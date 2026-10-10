#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep one complete cross-problem paper in every reading edition."""

import io
import importlib.util
import json
from pathlib import Path
import re
import shutil
import tempfile
import unittest
from contextlib import ExitStack, redirect_stderr, redirect_stdout
from unittest.mock import patch
from urllib.parse import quote, unquote

import build_reading_edition as edition

_RENDERER_SPEC = importlib.util.spec_from_file_location(
    "paper_corpus_renderer", edition.ROOT / "docs/papers/paper_corpus_renderer.py"
)
renderer = importlib.util.module_from_spec(_RENDERER_SPEC)
_RENDERER_SPEC.loader.exec_module(renderer)


class EquationReadingLinkTests(unittest.TestCase):
    BODY = (
        "\\begin{align}\n"
        " F(z)&=z^7-1\\tag{A}\\label{eq:ani-F}\\\\\n"
        " f(z)&=\\rho^7F(z/\\rho).\\label{eq:ani-f}\\\\\n"
        " g(z)&=f(z)+1\\tag{C}\\label{eq:third}\n"
        "\\end{align}"
    )

    def math(self):
        return {"t": "Math", "c": [{"t": "DisplayMath"}, self.BODY]}

    def test_equation_targets_are_outside_unchanged_display_math(self):
        blocks = [{"t": "Para", "c": [self.math()]}]
        walked = renderer._AstWalk().blocks(blocks)
        inlines = walked[0]["c"]
        self.assertEqual(inlines[-1], self.math())
        for label in ("eq:ani-F", "eq:ani-f", "eq:third"):
            self.assertIn(f'<a id="{label}"></a>', inlines[0]["c"][1])

    def test_each_explicit_tag_belongs_only_to_its_equation_row(self):
        self.assertEqual(renderer._tagged_equation_numbers(self.math()), {
            "eq:ani-F": "(A)", "eq:third": "(C)",
        })

    def test_nested_alignment_does_not_split_one_tagged_equation(self):
        body = (
            r"\begin{align}a&=\begin{aligned}b&=1\\c&=2\end{aligned}"
            r"\tag{A}\label{eq:a}\\d&=3\tag{D}\label{eq:d}\end{align}"
        )
        node = {"t": "Math", "c": [{"t": "DisplayMath"}, body]}
        self.assertEqual(renderer._tagged_equation_numbers(node), {
            "eq:a": "(A)", "eq:d": "(D)",
        })

    def test_equation_references_drop_only_pandoc_reference_metadata(self):
        def reference(label):
            return {"t": "Link", "c": [
                ["", [], [["reference-type", "eqref"], ["reference", label]]],
                [{"t": "Str", "c": f"[{label}]"}], [f"#{label}", ""],
            ]}
        unknown, tagged, section = (reference(label) for label in ("eq:unknown", "eq:tag", "sec:one"))
        renderer._render_numbered_references(
            [unknown, tagged, section], {"eq:tag": "(A)"}, {"eq:unknown", "eq:tag"}
        )
        self.assertEqual(unknown['c'][0], ["", [], []])
        self.assertEqual(unknown['c'][1], [{"t": "Str", "c": "[eq:unknown]"}])
        self.assertEqual(unknown['c'][2][0], '#eq%3Aunknown')
        self.assertEqual(tagged['c'][1], [{"t": "Str", "c": "(A)"}])
        self.assertEqual(section, reference("sec:one"))

    def test_equation_fragment_encodes_reserved_characters_once(self):
        label = "eq:a/b?#%"
        node = {"t": "Link", "c": [
            ["", [], [["reference-type", "eqref"], ["reference", label]]],
            [{"t": "Str", "c": f"[{label}]"}], [f"#{label}", ""],
        ]}
        renderer._render_numbered_references(node, {}, {label})
        self.assertEqual(node['c'][2][0], '#eq%3Aa%2Fb%3F%23%25')
        self.assertEqual(unquote(node['c'][2][0][1:]), label)

    def test_known_section_and_statement_targets_keep_existing_reference_text(self):
        def reference(label, text):
            return {"t": "Link", "c": [
                ["", [], [["reference-type", "ref"], ["reference", label]]],
                [{"t": "Str", "c": text}], [f"#{label}", ""],
            ]}
        blocks = [
            {"t": "Para", "c": [reference("sec:known", "6.1"), reference("thm:known", "2"),
                                   reference("fig:known", "1"),
                                   reference("sec:missing", "[sec:missing]")]},
            {"t": "Header", "c": [1, ["sec:known", [], []], [{"t": "Str", "c": "A section"}]]},
            {"t": "Div", "c": [["thm:known", ["theorem"], []],
                                   [{"t": "Para", "c": [{"t": "Str", "c": "A statement."}]}]]},
            {"t": "Figure", "c": [["fig:known", [], []], [None, []], []]},
        ]
        walk = renderer._AstWalk()
        converted = walk.blocks(blocks)
        renderer._render_numbered_references(converted, {}, walk.equation_labels | walk.reference_labels)
        section, theorem, figure, missing = converted[0]['c']
        self.assertEqual(section['c'], [["", [], []], [{"t": "Str", "c": "6.1"}], ['#sec%3Aknown', '']])
        self.assertEqual(theorem['c'], [["", [], []], [{"t": "Str", "c": "2"}], ['#thm%3Aknown', '']])
        self.assertEqual(figure['c'], [["", [], []], [{"t": "Str", "c": "1"}], ['#fig%3Aknown', '']])
        self.assertEqual(missing, reference("sec:missing", "[sec:missing]"))

    def test_prose_emphasis_is_split_around_unchanged_display_math(self):
        blocks = [{"t": "Para", "c": [{"t": "Emph", "c": [
            {"t": "Str", "c": "Before."}, {"t": "SoftBreak"},
            {"t": "Strong", "c": [self.math()]}, {"t": "SoftBreak"},
            {"t": "Str", "c": "After."},
        ]}]}]
        inlines = renderer._AstWalk().blocks(blocks)[0]['c']
        self.assertEqual([node['c'] for node in inlines if node['t'] == 'Math'], [self.math()['c']])
        self.assertEqual([node['c'] for node in inlines if node['t'] == 'Emph'], [
            [{"t": "Str", "c": "Before."}], [{"t": "Str", "c": "After."}],
        ])

    @unittest.skipUnless(shutil.which("pandoc"), "display conversion requires Pandoc")
    def test_theorem_displays_close_fences_before_following_section_navigation(self):
        source = r'''\documentclass{article}
\usepackage{amsmath}
\newtheorem{theorem}{Theorem}
\begin{document}
\begin{theorem}\label{thm:display}
Before the display.
\begin{equation}x=1\label{eq:first}\end{equation}
After the display.
\begin{equation}y=2\label{eq:last}\end{equation}
\end{theorem}
See Section~\ref{sec:open}.
\section{Open}\label{sec:open}
\end{document}
'''
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "fixture.tex"
            path.write_text(source)
            text = renderer._convert(path, "fixture")['markdown']
        self.assertNotRegex(text, r'(?m)^ *```\*')
        self.assertIn('*Before the display.*', text)
        self.assertIn('*After the display.*', text)
        for formula in ('x=1\\label{eq:first}', 'y=2\\label{eq:last}'):
            self.assertIn(formula, text)
        scoped = edition.scope_anchors(text, "fixture")
        self.assertIn('[1](#fixture--sec%3Aopen)', scoped)
        self.assertIn('<a id="fixture--sec:open"></a>', scoped)

    @unittest.skipUnless(shutil.which("pandoc"), "reference conversion requires Pandoc")
    def test_section_and_theorem_conversion_retains_ids_and_native_numbered_links(self):
        source = r'''\documentclass{article}
\newtheorem{theorem}{Theorem}
\begin{document}
See Section~\ref{sec:known}, Theorem~\ref{thm:known}, and Figure~\ref{fig:known}.
\section{A fixture}\label{sec:known}
\begin{theorem}\label{thm:known}A fixture statement.\end{theorem}
\begin{figure}\caption{A fixture caption.}\label{fig:known}\end{figure}
\end{document}
'''
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "fixture.tex"
            path.write_text(source)
            text = renderer._convert(path, "fixture")['markdown']
        self.assertIn('[1](#sec%3Aknown)', text)
        self.assertIn('[1](#thm%3Aknown)', text)
        self.assertIn('[1](#fig%3Aknown)', text)
        self.assertIn('<a id="sec:known"></a>', text)
        self.assertIn('<div id="thm:known" class="theorem">', text)
        self.assertEqual(text.count('<a id="fig:known"></a>'), 1)
        self.assertIn('<figure>', text)
        self.assertIn('A fixture caption.', text)
        self.assertNotIn('data-reference-type="ref"', text)

    @unittest.skipUnless(shutil.which("pandoc"), "equation conversion requires Pandoc")
    def test_conversion_and_bundle_keep_native_equation_links_and_tags(self):
        source = (
            "\\documentclass{article}\n\\usepackage{amsmath}\n"
            "\\begin{document}\n"
            "See \\eqref{eq:ani-F}, \\eqref{eq:ani-f}, and \\eqref{eq:third}.\n\n"
            + self.BODY + "\n\n"
            "% paper-text-number: eq:declared=17\n"
            "\\begin{equation}h=4\\label{eq:declared}\\end{equation}\n"
            "See \\eqref{eq:declared}.\n\\end{document}\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "paper.tex"
            path.write_text(source)
            text = renderer._convert(path, "fixture")['markdown']
            numbered = renderer._convert(path, "optimal-sparse-perturbations")['markdown']
        self.assertIn(self.BODY, re.findall(r'``` math\n(.*?)\n```', text, re.DOTALL))
        for label in ("eq:ani-F", "eq:ani-f", "eq:third", "eq:declared"):
            self.assertEqual(text.count(f'<a id="{label}"></a>'), 1)
            self.assertIn(f"](#{quote(label, safe='')})", text)
        self.assertNotIn("[(A)](#eq%3Aani-F)", text)
        self.assertNotIn("[(C)](#eq%3Athird)", text)
        self.assertNotIn("[(17)](#eq%3Adeclared)", text)
        self.assertIn("[(A)](#eq%3Aani-F)", numbered)
        self.assertIn("[(C)](#eq%3Athird)", numbered)
        self.assertIn("[(17)](#eq%3Adeclared)", numbered)
        self.assertNotIn("[(A)](#eq%3Aani-f)", numbered)
        self.assertNotIn('data-reference-type="eqref"', text)
        self.assertNotIn('href="#eq:', text)
        combined = "\n".join(edition.scope_anchors(text, paper) for paper in ("one", "two"))
        for paper in ("one", "two"):
            self.assertIn(f'<a id="{paper}--eq:ani-f"></a>', combined)
            self.assertIn(f"](#{paper}--eq%3Aani-f)", combined)
            self.assertEqual(unquote(f"{paper}--eq%3Aani-f"), f"{paper}--eq:ani-f")
        self.assertEqual(combined.count(self.BODY), 2)


class SynthesisReadingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.corpus = self.root / "corpus.json"
        self.rows = [
            self.row(edition.SYNTHESIS_PAPER_ID, "synthesis_paper"),
        ]

    def row(self, paper_id, publication_class):
        path = self.root / f"{paper_id}.md"
        path.write_text(f"# {paper_id}\n\nA mathematical statement.\n")
        return {
            "paper_id": paper_id,
            "publication_class": publication_class,
            "subject_kind": "synthesis",
            "publication_state": "pending_source_publication",
            "local_full_text": path.name,
            "local_pdf": f"paper/synthesis/{paper_id}.pdf",
            "title": paper_id,
            "question_this_paper_answers": "Which values occur?",
        }

    def load(self, rows):
        self.corpus.write_text(json.dumps({"papers": rows}))
        with patch.object(edition, "ROOT", self.root), patch.object(edition, "CORPUS", self.corpus):
            return edition.synthesis_papers()

    def test_one_paper_contains_the_complete_record(self):
        rows = self.load(self.rows)
        self.assertEqual([r["paper_id"] for r in rows], [edition.SYNTHESIS_PAPER_ID])
        rendered = edition.synthesis_entry(rows)
        self.assertIn("A mathematical statement.", rendered)
        self.assertNotIn("Working record:", rendered)

    def test_second_synthesis_is_rejected(self):
        extra = self.row("duplicate-record", "reasoning_surface")
        with self.assertRaisesRegex(edition.ReadingEditionError, "exactly one"):
            self.load([*self.rows, extra])

    def test_missing_or_wrong_canonical_paper_is_rejected(self):
        for rows in ([], [self.row("other-paper", "synthesis_paper")]):
            with self.subTest(rows=rows), self.assertRaisesRegex(edition.ReadingEditionError, "exactly one"):
                self.load(rows)

    def test_retired_predecessor_is_not_reintroduced(self):
        retired = self.row("old-record", "reasoning_surface")
        retired["publication_state"] = "retired"
        self.assertEqual(len(self.load([retired, *self.rows])), 1)


class ReadingLinkTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.text_dir = self.root / "docs/papers/full-text"
        self.text_dir.mkdir(parents=True)

    def test_relocated_links_preserve_fragments_queries_and_external_urls(self):
        original = (
            "[PDF](../../../paper/257/a%20record.pdf?raw=1#nameddest=section.3) "
            "[section](#sec:result) [web](https://example.org/paper.pdf) "
            "[mail](mailto:reader@example.org) [cdn](//example.org/paper.pdf)"
        )
        with patch.object(edition, "ROOT", self.root):
            rendered = edition.public_links(original, self.text_dir / "paper.md")
        self.assertIn(f"]({edition.BLOB}paper/257/a%20record.pdf?raw=1#nameddest=section.3)", rendered)
        for link in ("#sec:result", "https://example.org/paper.pdf",
                     "mailto:reader@example.org", "//example.org/paper.pdf"):
            self.assertIn(f"]({link})", rendered)

    def test_link_cannot_escape_the_public_repository(self):
        with patch.object(edition, "ROOT", self.root):
            with self.assertRaisesRegex(edition.ReadingEditionError, "outside the repository"):
                edition.public_links("[bad](../../../../private.pdf)", self.text_dir / "paper.md")

    def test_math_and_code_are_not_reinterpreted_as_links(self):
        for literal in (
            "$`b_k=[z^k](z;q)_infty`$", "$b_k=[z^k](z;q)_infty$",
            "$$b_k=[z^k](z;q)_infty$$", "`[example](local.md)`",
            "```math\nb_k=[z^k](z;q)_infty\n```",
            "~~~text\n[example](local.md)\n~~~",
        ):
            with self.subTest(literal=literal), patch.object(edition, "ROOT", self.root):
                rendered = edition.public_links(literal, self.text_dir / "paper.md")
            self.assertEqual(rendered, literal)
        with patch.object(edition, "ROOT", self.root):
            self.assertEqual(
                edition.public_links("[a `code` label](../../../paper/note.pdf)", self.text_dir / "paper.md"),
                f"[a `code` label]({edition.BLOB}paper/note.pdf)",
            )

    def test_scoping_preserves_literal_equation_and_anchor_examples(self):
        for literal in (
            '`[equation](#eq:shared)`',
            '```math\n\\text{id="eq:shared"}\\tag{A}\\label{eq:shared}\n```',
            '~~~text\n<a id="eq:shared"></a> [equation](#eq:shared)\n~~~',
            '$`\\text{id="eq:shared"}`$',
            '$\\text{id="eq:shared"}$',
            '$$\\text{id="eq:shared"}$$',
            '$`\\text{\\$ id="eq:shared"}`$',
        ):
            with self.subTest(literal=literal):
                self.assertEqual(edition.scope_anchors(literal, "one"), literal)
        text = '<a id="eq:shared"></a> [(A)](#eq:shared)'
        self.assertEqual(edition.scope_anchors(text, "one"),
                         '<a id="one--eq:shared"></a> [(A)](#one--eq:shared)')
        encoded = '<a id="eq:shared"></a> [(A)](#eq%3Ashared)'
        self.assertEqual(edition.scope_anchors(encoded, "part:one"),
                         '<a id="part:one--eq:shared"></a> [(A)](#part%3Aone--eq%3Ashared)')

    def test_scoping_closes_fences_only_on_valid_fence_lines(self):
        for opening, embedded, closing in (
            ('```python', 'print("```")', '```'),
            ('```python', 'print("```")\n```suffix', '```'),
            ('~~~python', 'print("~~~")', '~~~'),
            ('~~~python', 'print("~~~")\n~~~suffix', '~~~'),
            ('````python', '```\nprint("````")', '   `````  '),
        ):
            literal = (f"{opening}\n{embedded}\n"
                       'literal = \'<a id="code-note"></a>\'\n'
                       f"{closing}\n")
            text = literal + '\n<a id="real-note"></a>\n'
            with self.subTest(opening=opening):
                self.assertEqual(edition.scope_anchors(text, "fixture"),
                                 literal + '\n<a id="fixture--real-note"></a>\n')
        literal = '``literal ` <a id="code-note"></a>``'
        self.assertEqual(edition.scope_anchors(literal + ' <a id="real-note"></a>', "fixture"),
                         literal + ' <a id="fixture--real-note"></a>')

    def test_all_editions_rebase_paper_links_and_scope_repeated_anchors(self):
        def row(paper_id, publication_class, problem=None):
            path = self.text_dir / f"{paper_id}.md"
            path.write_text(
                f'# {paper_id}\n\n<a id="sec:result"></a>\n'
                '[result](#sec:result) [PDF](../../../paper/257/record.pdf#nameddest=section.3)\n'
            )
            result = {
                "paper_id": paper_id, "publication_class": publication_class,
                "title": paper_id, "question_this_paper_answers": "Which values occur?",
                "local_full_text": path.relative_to(self.root).as_posix(),
                "local_pdf": "paper/257/record.pdf", "text_path": path,
            }
            if problem is not None:
                result["problem"] = problem
            return result

        papers = [row("short257", "problem_paper", 257),
                  row("long257", "reasoning_surface", 257)]
        synthesis = [row(edition.SYNTHESIS_PAPER_ID, "synthesis_paper")]
        out = self.root / "docs/reading-edition"
        out.mkdir()
        intro = out / "INTRODUCTION.md"
        intro.write_text("Read the mathematics.\n")
        complete_path = self.root / "downloaded-edition.md"
        with ExitStack() as stack:
            for name, value in (("ROOT", self.root), ("OUT", out),
                                ("INTRODUCTION", intro), ("WORKED_EXAMPLES", ())):
                stack.enter_context(patch.object(edition, name, value))
            stack.enter_context(patch.object(edition, "mathematical_papers", return_value=papers))
            stack.enter_context(patch.object(edition, "synthesis_papers", return_value=synthesis))
            stack.enter_context(patch.object(edition, "shared_instruction", return_value="Explore."))
            stack.enter_context(patch.object(edition, "fingerprint", return_value="fixture"))
            outputs = edition.build()
            edition.complete(complete_path)
        for text in (outputs[out / "plectis-reading-edition.md"],
                     outputs[out / "plectis-short-papers.md"], complete_path.read_text()):
            self.assertNotIn("](../../../", text)
            self.assertIn(f"]({edition.BLOB}paper/257/record.pdf#nameddest=section.3)", text)
            self.assertNotIn('id="sec:result"', text)
            self.assertIn('id="short257--sec:result"', text)
            self.assertIn("](#short257--sec:result)", text)


class ReadingCheckRepairCommandTests(unittest.TestCase):
    def check_stale_family(self, records):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            normal = root / "normal.md"
            record = root / "record.md"
            normal.write_text("old normal\n")
            record.write_text("old record\n")
            outputs = {normal: "new normal\n"}
            record_outputs = {record: "new record\n"}
            with patch.object(edition, "ROOT", root), \
                    patch.object(edition, "build_weighted_task", return_value={}), \
                    patch.object(edition, "build", return_value=outputs) as build, \
                    patch.object(edition, "build_records", return_value=record_outputs) as build_records:
                stderr = io.StringIO()
                with redirect_stderr(stderr), redirect_stdout(io.StringIO()):
                    status = edition.main(["--check", *(["--records"] if records else [])])
                self.assertEqual(status, 1)
                self.assertEqual(normal.read_text(), "old normal\n")
                self.assertEqual(record.read_text(), "old record\n")
                expected = "python3 scripts/build_reading_edition.py" + (" --records" if records else "")
                self.assertEqual(stderr.getvalue().splitlines(), [
                    "stale: " + ("record.md" if records else "normal.md"), "run: " + expected,
                ])
                command = stderr.getvalue().splitlines()[-1].removeprefix("run: ")
                with redirect_stdout(io.StringIO()):
                    self.assertEqual(edition.main(command.split()[2:]), 0)
                if records:
                    self.assertEqual(record.read_text(), "new record\n")
                    self.assertEqual(normal.read_text(), "old normal\n")
                    build.assert_not_called()
                    self.assertEqual(build_records.call_count, 2)
                else:
                    self.assertEqual(normal.read_text(), "new normal\n")
                    self.assertEqual(record.read_text(), "old record\n")
                    build_records.assert_not_called()
                    self.assertEqual(build.call_count, 2)

    def test_stale_record_repair_preserves_records_mode_and_other_family(self):
        self.check_stale_family(records=True)

    def test_stale_normal_repair_keeps_default_mode_and_other_family(self):
        self.check_stale_family(records=False)

    def test_current_records_do_not_emit_a_repair_command(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            record = root / "record.md"
            record.write_text("current record\n")
            with patch.object(edition, "ROOT", root), \
                    patch.object(edition, "build") as build, \
                    patch.object(edition, "build_records", return_value={record: "current record\n"}):
                stderr = io.StringIO()
                with redirect_stderr(stderr), redirect_stdout(io.StringIO()):
                    self.assertEqual(edition.main(["--records", "--check"]), 0)
                self.assertEqual(stderr.getvalue(), "")
                self.assertEqual(record.read_text(), "current record\n")
                build.assert_not_called()


if __name__ == "__main__":
    unittest.main()
