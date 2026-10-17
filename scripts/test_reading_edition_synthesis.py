#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep one complete cross-problem paper in every reading edition."""

import copy
import hashlib
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
import check_markdown_table_render as table_render

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

    def test_span_targets_preserve_unnumbered_text_and_ignore_literal_lookalikes(self):
        def reference(label):
            return {"t": "Link", "c": [
                ["", [], [["reference-type", "ref"], ["reference", label]]],
                [{"t": "Str", "c": f"[{label}]"}], [f"#{label}", ""],
            ]}
        label = "res:constant-factor-path"
        span = {"t": "Span", "c": [[label, [], [["label", label]]], []]}
        literals = [
            {"t": "Code", "c": [["", [], []], '<span id="res:inline-code"></span>']},
            {"t": "Math", "c": [{"t": "InlineMath"}, r'\text{<span id="res:inline-math"></span>}']},
            {"t": "Math", "c": [{"t": "DisplayMath"}, r'\text{<span id="res:display-math"></span>}']},
        ]
        code_block = {"t": "CodeBlock", "c": [["", [], []], '<span id="res:block-code"></span>']}
        missing_labels = ("res:inline-code", "res:inline-math", "res:display-math", "res:block-code")
        blocks = [
            {"t": "Para", "c": [reference(label), *(reference(missing) for missing in missing_labels)]},
            {"t": "Para", "c": [span, *literals]},
            code_block,
        ]
        walk = renderer._AstWalk()
        converted = walk.blocks(blocks)
        renderer._render_numbered_references(converted, {}, walk.equation_labels | walk.reference_labels)
        self.assertEqual(walk.reference_labels, {label})
        self.assertEqual(converted[0]['c'][0]['c'], [
            ["", [], []], [{"t": "Str", "c": f"[{label}]"}], ['#res%3Aconstant-factor-path', ''],
        ])
        self.assertEqual(converted[0]['c'][1:], [reference(missing) for missing in missing_labels])
        self.assertEqual(converted[1]['c'], [span, *literals])
        self.assertEqual(converted[2], code_block)

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

    @unittest.skipUnless(shutil.which("pandoc"), "Span reference conversion requires Pandoc")
    def test_span_conversion_retains_unnumbered_remark_and_bundle_destination(self):
        source = r'''\documentclass{article}
\newtheorem*{remark}{Remark}
\let\remark\relax
\let\endremark\relax
\newtheorem{theorem}{Theorem}
\newtheorem{remark}[theorem]{Remark}
\begin{document}
See Remark~\ref{res:constant-factor-path}.
\begin{remark}\label{res:constant-factor-path}A fixture statement.\end{remark}
Literal code: \verb|<span id="res:code"></span>|.
\[\text{<span id="res:math"></span>}\]
\end{document}
'''
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "fixture.tex"
            path.write_text(source)
            text = renderer._convert(path, "fixture")['markdown']
        self.assertIn('<span id="res:constant-factor-path" label="res:constant-factor-path"></span>', text)
        self.assertIn(r'[\[res:constant-factor-path\]](#res%3Aconstant-factor-path)', text)
        self.assertNotIn('data-reference-type="ref"', text)
        self.assertNotIn('href="#res:constant-factor-path"', text)
        self.assertIn('`<span id="res:code"></span>`', text)
        self.assertIn(r'\text{<span id="res:math"></span>}',
                      re.findall(r'``` math\n(.*?)\n```', text, re.DOTALL))
        scoped = edition.scope_anchors(text, "fixture")
        self.assertIn('<span id="fixture--res:constant-factor-path"', scoped)
        self.assertIn(r'[\[res:constant-factor-path\]](#fixture--res%3Aconstant-factor-path)', scoped)
        self.assertIn('`<span id="res:code"></span>`', scoped)
        self.assertIn(r'\text{<span id="res:math"></span>}',
                      re.findall(r'``` math\n(.*?)\n```', scoped, re.DOTALL))

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
        renamed = renderer._case_safe_anchor_ids({"eq:ani-F", "eq:ani-f", "eq:third", "eq:declared"})
        target = lambda label: quote(renamed.get(label, label), safe='')
        self.assertIn(self.BODY, re.findall(r'``` math\n(.*?)\n```', text, re.DOTALL))
        for label in ("eq:ani-F", "eq:ani-f", "eq:third", "eq:declared"):
            self.assertEqual(text.count(f'<a id="{renamed.get(label, label)}"></a>'), 1)
            self.assertIn(f"](#{target(label)})", text)
        self.assertNotIn(f"[(A)](#{target('eq:ani-F')})", text)
        self.assertNotIn("[(C)](#eq%3Athird)", text)
        self.assertNotIn("[(17)](#eq%3Adeclared)", text)
        self.assertIn(f"[(A)](#{target('eq:ani-F')})", numbered)
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


class CaseCollisionReadingTests(unittest.TestCase):
    def test_allocator_reserves_authored_ids_and_changes_only_real_collisions(self):
        upper, lower = "prop:B7", "prop:b7"
        occupied = lower + "--case-" + hashlib.sha256(upper.encode()).hexdigest()[:8]
        labels = {upper, lower, occupied.upper(), "sec:Unchanged"}
        renamed = renderer._case_safe_anchor_ids(labels)
        self.assertEqual(renamed, {upper: occupied + "-2"})
        self.assertEqual(renamed, renderer._case_safe_anchor_ids(set(reversed(sorted(labels)))))
        self.assertEqual(len({renamed.get(label, label).lower() for label in labels}), len(labels))
        self.assertEqual(renderer._case_safe_anchor_ids({"eq:OnlyUpper"}), {})

    def test_all_emitted_target_paths_and_local_links_preserve_semantic_contents(self):
        def reference(label, text):
            return {"t": "Link", "c": [["", [], [["reference-type", "ref"], ["reference", label]]],
                    [{"t": "Str", "c": text}], ["#" + label, ""]]}
        math = {"t": "Math", "c": [{"t": "DisplayMath"}, EquationReadingLinkTests.BODY]}
        literals = [
            {"t": "Code", "c": [["", [], []], '<span id="ghost:A"></span><a href="#prop:B7">127</a>']},
            {"t": "CodeBlock", "c": [["", [], []], '<a id="ghost:a"></a>']},
            {"t": "Math", "c": [{"t": "InlineMath"}, r'\text{<span id="ghost:A"></span>}\label{ghost:a}']},
            {"t": "Math", "c": [{"t": "DisplayMath"}, r'\text{<a id="ghost:a"></a>}']},
        ]
        external = {"t": "Link", "c": [["", [], []], [{"t": "Str", "c": "External"}],
                                             ["https://example.org/paper#prop:B7", "title"]]}
        unknown = reference("ghost:A", "[ghost:A]")
        raw = ('<!-- <a id="ghost:A"></a> --><a title=\'literal id="ghost:A">\' '
               'data-id="ghost:a" href="https://example.org/#prop:B7"></a>')
        blocks = [
            {"t": "Header", "c": [1, ["sec:UP", [], []], [{"t": "Str", "c": "A section"}]]},
            {"t": "Header", "c": [1, ["sec:up", [], []], [{"t": "Str", "c": "Another section"}]]},
            {"t": "Div", "c": [["prop:b7", ["prop"], []],
                                    [{"t": "Para", "c": [{"t": "Str", "c": "Proposition 26"}]}]]},
            {"t": "Div", "c": [["prop:B7", ["prop"], []],
                                    [{"t": "Para", "c": [{"t": "Str", "c": "Proposition 127"}]}]]},
            {"t": "Figure", "c": [["fig:UP", [], []], [None, []], []]},
            {"t": "Figure", "c": [["fig:up", [], []], [None, []], []]},
            literals[1],
            {"t": "Para", "c": [
                {"t": "Span", "c": [["span:UP", [], [["label", "span:UP"]]], []]},
                {"t": "Span", "c": [["span:up", [], []], []]}, math,
                literals[0], *literals[2:], external, unknown,
                reference("prop:b7", "26"), reference("prop:B7", "127"),
                {"t": "RawInline", "c": ["html", '<a HREF = "#prop%3AB7">127</a>']},
                {"t": "RawInline", "c": ["html", raw]},
            ]},
        ]
        walk = renderer._AstWalk()
        walked = walk.blocks(copy.deepcopy(blocks))
        renderer._render_numbered_references(walked, {}, walk.reference_labels | walk.equation_labels)
        before = copy.deepcopy(walked)
        labels = renderer._rendered_anchor_labels(walked)
        self.assertNotIn("ghost:A", labels)
        self.assertNotIn("ghost:a", labels)
        renamed = renderer._case_safe_anchor_ids(labels)
        self.assertEqual(set(renamed), {"sec:UP", "prop:B7", "fig:UP", "span:UP", "eq:ani-F"})
        renderer._remap_delivery_anchors(walked, renamed)
        delivered = renderer._rendered_anchor_labels(walked)
        self.assertEqual(len({label.lower() for label in delivered}), len(labels))
        self.assertIn(math, walked[-1]['c'])
        for literal in literals:
            self.assertIn(literal, walked if literal['t'] == 'CodeBlock' else walked[-1]['c'])
        self.assertIn(external, walked[-1]['c'])
        self.assertIn(unknown, walked[-1]['c'])
        self.assertIn({"t": "RawInline", "c": ["html", raw]}, walked[-1]['c'])
        refs = [node for node in walked[-1]['c'] if node.get('t') == 'Link']
        self.assertEqual(refs[-2]['c'][1:], [[{"t": "Str", "c": "26"}], ['#prop%3Ab7', '']])
        self.assertEqual(refs[-1]['c'][1:], [[{"t": "Str", "c": "127"}],
                         ['#' + quote(renamed['prop:B7'], safe=''), '']])
        span = next(node for node in walked[-1]['c'] if node.get('t') == 'Span')
        self.assertEqual(span['c'][0][2], [["label", "span:UP"]])
        renderer._remap_delivery_anchors(before, {})
        self.assertNotEqual(before, walked)

    @unittest.skipUnless(shutil.which("pandoc"), "case collision conversion requires Pandoc")
    def test_real_separated_249_and_adjacent_1041_targets_keep_bodies_and_bundle_routes(self):
        # Actual #249 statement excerpts (source labels prop:b7 / prop:B7),
        # followed by the actual #1041 case-distinct alignment shape.
        source = (
            "\\documentclass{article}\n\\usepackage{amsmath}\n"
            "\\newtheorem{prop}{Proposition}\n\\begin{document}\n"
            "\\section{Unchanged}\\label{sec:Unchanged}\n"
            "See Proposition~\\ref{prop:B7} and \\eqref{eq:ani-F}, \\eqref{eq:ani-f}.\n"
            "\\begin{prop}[The coefficient properties of the rational example]\\label{prop:b7}\n"
            "The rational sequence in Proposition~\\ref{prop:parity} satisfies uniform\n"
            "boundedness, $c(n)\\le n$, agreement with $\\varphi(n)$ modulo $2$ at every\n"
            "index, and the stated separated-carry form of aperiodicity. Consequently,\n"
            "those properties alone cannot imply irrationality of a dyadic series.\n"
            "The example does not exclude arguments using further totient identities,\n"
            "including its multiplicative relations.\n\\end{prop}\n\n"
            "A separate part of the argument follows.\n\n"
            "\\begin{prop}[A sufficient condition on the LCM grid]\\label{prop:B7}\n"
            "\\[\n"
            "\\big(\\forall t_0,\\ \\exists t\\ge t_0,\\ \\exists q\\,m\\,L,\\ 0<q \\wedge \\mathcal{C}(m\\cdot{H}\\,t)(q\\cdot{H}\\,t)\\ L\\big)\n"
            "\\implies S\\notin\\mathbb Q.\n\\]\n"
            "One residue certificate \\emph{anywhere} on the two-multiplier LCM cone, at arbitrarily large $t$,\n"
            "suffices; the diagonal choice $q=m=1$ recovers Proposition~\\ref{prop:B3}.\n"
            "\\end{prop}\n\n" + EquationReadingLinkTests.BODY + "\n\\end{document}\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "paper.tex"
            path.write_text(source)
            marks = {
                'prop:b7': ('Lean', 'https://example.org/evidence#prop-b7', ''),
                'prop:B7': ('Lean', 'https://example.org/evidence#prop-b7-60c3ed',
                            'https://example.org/comparator#prop-b7-60c3ed'),
            }
            with patch.object(renderer, '_evidence_marks', return_value=(marks, {})):
                with patch.object(renderer, '_case_safe_anchor_ids', return_value={}):
                    before = renderer._convert(path, "fixture")
                after = renderer._convert(path, "fixture")
        renamed = renderer._case_safe_anchor_ids({"prop:b7", "prop:B7", "eq:ani-F", "eq:ani-f"})
        expected = before['markdown']
        for original, target in renamed.items():
            expected = expected.replace(f'id="{original}"', f'id="{target}"')
            expected = expected.replace(f'](#{quote(original, safe="")})', f'](#{quote(target, safe="")})')
        self.assertEqual(after['markdown'], expected)
        self.assertEqual({k: v for k, v in after.items() if k != 'markdown'},
                         {k: v for k, v in before.items() if k != 'markdown'})
        self.assertIn(EquationReadingLinkTests.BODY, after['markdown'])
        self.assertIn('<a id="eq:ani-f"></a>', after['markdown'])
        self.assertIn(f'<a id="{renamed["eq:ani-F"]}"></a>\n<a id="eq:ani-f"></a>', after['markdown'])
        self.assertIn(f'](#{quote(renamed["prop:B7"], safe="")})', after['markdown'])
        self.assertIn('<a id="sec:Unchanged"></a>', after['markdown'])
        self.assertIn(f'<div id="{renamed["prop:B7"]}" class="prop">\n<p class="evidence-marks">',
                      after['markdown'])
        for mark in marks.values():
            for url in mark[1:]:
                if url:
                    self.assertIn(url, after['markdown'])
        combined = '\n'.join(edition.scope_anchors(after['markdown'], paper) for paper in ('one', 'two'))
        for paper in ('one', 'two'):
            for original, target in renamed.items():
                self.assertIn(f'id="{paper}--{target}"', combined)
                self.assertIn(f'](#{paper}--{quote(target, safe="")})', combined)
        self.assertEqual(combined.count(EquationReadingLinkTests.BODY), 2)

    @unittest.skipUnless(shutil.which("pandoc"), "section collision conversion requires Pandoc")
    def test_real_section_coordinates_and_span_targets_follow_delivery_ids(self):
        source = (
            "\\documentclass{article}\n\\begin{document}\n"
            "\\section{First}\\label{sec:UP}\n"
            "\\hypertarget{span:UP}{First named point}.\n"
            "\\section{Second}\\label{sec:up}\n"
            "\\hypertarget{span:up}{Second named point}.\n"
            "See \\ref{sec:UP} and \\hyperlink{span:UP}{the first point}.\n\n"
            "\\verb|<span id=\"ghost:A\"></span>|\n"
            "$\\text{<a id=\"ghost:a\">}$\n"
            "\\end{document}\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'paper.tex'
            path.write_text(source)
            converted = renderer._convert(path, 'fixture')
        renamed = renderer._case_safe_anchor_ids({'sec:UP', 'sec:up', 'span:UP', 'span:up'})
        sections = {section['title']: section for section in converted['sections']}
        self.assertEqual(sections['First']['id'], renamed['sec:UP'])
        self.assertEqual(sections['Second']['id'], 'sec:up')
        lines = converted['markdown'].splitlines()
        for section in sections.values():
            self.assertEqual(lines[section['line'] - 1], f'<a id="{section["id"]}"></a>')
        for target in renamed.values():
            self.assertIn(f'id="{target}"', converted['markdown'])
            self.assertIn(f'](#{quote(target, safe="")})', converted['markdown'])
        self.assertIn('`<span id="ghost:A"></span>`', converted['markdown'])
        self.assertIn(r'\text{<a id="ghost:a">}', converted['markdown'])
        self.assertNotIn('ghost:a--case-', converted['markdown'])


class DisplayLayoutReadingTests(unittest.TestCase):
    PAYLOADS = (
        "\\displaystyle\n"
        " \\operatorname{ev}_e:\\mathbb Z^{I_e}\\longrightarrow L_e,\n"
        " \\qquad (c_i)\\longmapsto\\sum_{i\\in I_e}c_iF_i.\n",
        "\\displaystyle\n"
        " \\ker(\\operatorname{ev}_e)\n"
        "   =\\bigoplus_{i\\in I_e\\mathbin{\\backslash} J_e}\\mathbb Z R_i,\n"
        " \\qquad\n"
        " \\operatorname{rank}_{\\mathbb Z}\\ker(\\operatorname{ev}_e)=2^e-2.\n",
        "\\begin{array}{c|rrrrrrrrrrrrrrr}\n"
        "h&4&5&6&7&8&9&10&11&12&13&14&15&16&17&18\\\\ \\hline\n"
        "\\#&1&104&812&5437&51409&237423&735450&1431226&1132756&236752&34910&3076&521&49&8\n"
        "\\end{array}",
    )

    @staticmethod
    def wrappers(payloads):
        return [r"\adjustbox{max width=\linewidth}{$" + payload + "$}"
                for payload in payloads[:2]] + [r"\resizebox{\linewidth}{!}{$" + payloads[2] + "$}"]

    def test_whole_display_wrappers_keep_commands_comments_newlines_and_labels(self):
        payload = "\n\\displaystyle\\frac{a_{i+1}}{b\\{i\\}}\n% ignored } $ \\label{eq:fake}\n\\tag{A}\\label{eq:real}\n"
        for wrapper in (r"\adjustbox{max width=\linewidth}{$" + payload + "$}",
                        r"\resizebox{\linewidth}{!}{$" + payload + "$}"):
            walk = renderer._AstWalk()
            blocks = [{"t": "Para", "c": [{"t": "Math", "c": [{"t": "DisplayMath"}, wrapper]}]}]
            with self.subTest(wrapper=wrapper):
                inlines = walk.blocks(blocks)[0]['c']
                self.assertEqual(inlines[-1], {"t": "Math", "c": [{"t": "DisplayMath"}, payload]})
                self.assertEqual(walk.equation_labels, {"eq:real"})
                self.assertIn('<a id="eq:real"></a>', inlines[0]['c'][1])

    def test_unknown_partial_starred_and_mixed_display_wrappers_are_unchanged(self):
        known = r"\adjustbox{max width=\linewidth}{$x+y$}"
        for body in (
            r"\adjustbox*{max width=\linewidth}{$x+y$}",
            r"\adjustbox{max width=\linewidth,angle=90}{$x+y$}",
            r"\resizebox*{\linewidth}{!}{$x+y$}",
            r"\resizebox{\textwidth}{!}{$x+y$}",
            r"\resizebox{\linewidth}{\linewidth}{$x+y$}",
            r"\adjustbox{max width=\linewidth}{$x+y$",
            r"\resizebox{\linewidth}{!}{$x+y$",
            r"\adjustbox{max width=\linewidth}{text $x+y$}",
            r"\adjustbox{max width=\linewidth}{$x+y$ text}",
            r"\adjustbox{max width=\linewidth}{$x$ and $y$}",
            r"\adjustbox{max width=\linewidth}{$$x+y$$}",
            r"\adjustbox{max width=\linewidth}{$$}",
            r"\resizebox{\linewidth}{!}{$ $}",
            "x+" + known,
            known + "+y",
        ):
            math = {"t": "Math", "c": [{"t": "DisplayMath"}, body]}
            with self.subTest(body=body):
                self.assertEqual(renderer._AstWalk().blocks([{"t": "Para", "c": [math]}]),
                                 [{"t": "Para", "c": [math]}])

    def test_inline_math_and_code_lookalikes_remain_exact(self):
        wrapper = r"\resizebox{\linewidth}{!}{$\frac{x}{y}$}"
        inline = {"t": "Math", "c": [{"t": "InlineMath"}, wrapper]}
        code = {"t": "Code", "c": [["", [], []], wrapper]}
        code_block = {"t": "CodeBlock", "c": [["", [], []], wrapper]}
        blocks = [{"t": "Para", "c": [inline, code]}, code_block]
        self.assertEqual(renderer._AstWalk().blocks(blocks), blocks)

    def test_three_source_payloads_retain_their_exact_ast_interiors(self):
        for wrapper, payload in zip(self.wrappers(self.PAYLOADS), self.PAYLOADS):
            math = {"t": "Math", "c": [{"t": "DisplayMath"}, wrapper]}
            with self.subTest(wrapper=wrapper):
                converted = renderer._AstWalk().blocks([{"t": "Para", "c": [math]}])
                self.assertEqual(converted, [{"t": "Para", "c": [
                    {"t": "Math", "c": [{"t": "DisplayMath"}, payload]},
                ]}])

    @unittest.skipUnless(shutil.which("pandoc"), "display layout conversion requires Pandoc")
    def test_pandoc_conversion_removes_only_three_complete_display_wrappers(self):
        wrappers = self.wrappers(self.PAYLOADS)
        inline = r"\resizebox{\linewidth}{!}{$x+y$}"
        unknown = r"\resizebox{\textwidth}{!}{$x+y$}"
        source = (r"\documentclass{article}\begin{document}" + "\n"
                  + "\n".join(r"\[" + wrapper + r"\]" for wrapper in wrappers)
                  + "\n" + r"\[" + unknown + r"\]" + "\n"
                  + r"Inline: \(" + inline + r"\)." + "\n"
                  + r"Literal: \verb|" + inline + "|.\n"
                  + r"\begin{Verbatim}" + "\n" + wrappers[0] + "\n" + r"\end{Verbatim}" + "\n"
                  + r"\end{document}")
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "fixture.tex"
            path.write_text(source)
            text = renderer._convert(path, "fixture")['markdown']
        displays = re.findall(r'``` math\n(.*?)\n```', text, re.DOTALL)
        # Pandoc normalizes fence-boundary whitespace; the AST test above
        # retains the exact interiors before that ordinary writer behavior.
        self.assertEqual(displays, [*(payload.strip() for payload in self.PAYLOADS), unknown])
        self.assertIn("$`" + inline + "`$", text)
        self.assertIn("`" + inline + "`", text)
        code_block = "\n".join(line[4:] for line in text.splitlines() if line.startswith("    "))
        self.assertIn(wrappers[0], code_block)


class LayoutAdjustboxReadingTests(unittest.TestCase):
    INEQUALITIES = (
        r"0<q\le Q_0=79\,639\,646\,646\,701\,375\,323\,355\,774\,875\,831\,053",
        r"0<d\le Q_1=39\,819\,823\,323\,350\,687\,661\,677\,887\,437\,915\,526",
    )

    def test_layout_only_wrapper_keeps_nested_body_bytes_and_comments(self):
        body = "$" + r"\frac{q+\{1\}}{\mathbb{N}}" + "\n% ignored }\n$"
        wrapped = "Before \\adjustbox{% ignored }\n max width = \\linewidth}{" + body + "} after."
        self.assertEqual(renderer._preserve_layout_adjustbox(wrapped), "Before " + body + " after.")

    def test_other_options_and_starred_commands_are_retained(self):
        for command in (
            r"\adjustbox{width=\linewidth}{$q=1$}",
            r"\adjustbox{max width=\linewidth,trim=1 2 3 4}{$q=1$}",
            r"\adjustbox{max width=\textwidth}{$q=1$}",
            r"\adjustbox*{max width=\linewidth}{$q=1$}",
        ):
            with self.subTest(command=command):
                self.assertEqual(renderer._preserve_layout_adjustbox(command), command)

    def test_percent_encoded_url_stays_literal_before_layout_conversion(self):
        url = r"\url{https://example.org/paper%20name}"
        source = url + r" and \adjustbox{max width=\linewidth}{$q=1$}"
        self.assertEqual(renderer._preserve_layout_adjustbox(source), url + " and $q=1$")

    def test_comments_code_math_and_escaped_lookalikes_are_unchanged(self):
        command = r"\adjustbox{max width=\linewidth}{$q=1$}"
        literals = (
            "% " + command + "\n",
            r"\verb|" + command + "|",
            r"\verb*%" + command + "%",
            r"\texttt{" + command + "}",
            r"\begin{Verbatim}" + "\n" + command + "\n" + r"\end{Verbatim}",
            "$" + command + "$",
            "$$" + command + "$$",
            r"\(" + command + r"\)",
            r"\[" + command + r"\]",
            r"\begin{equation}" + command + r"\end{equation}",
            "\\" + command,
        )
        for literal in literals:
            with self.subTest(literal=literal):
                self.assertEqual(renderer._preserve_layout_adjustbox(literal), literal)
        self.assertEqual(renderer._preserve_layout_adjustbox("\\% " + command), "\\% $q=1$")

    def test_incomplete_wrapper_is_rejected_without_a_partial_rewrite(self):
        for source in (r"\adjustbox{max width=\linewidth}",
                       r"\adjustbox{max width=\linewidth}{$q=1$"):
            with self.subTest(source=source), self.assertRaises(ValueError):
                renderer._preserve_layout_adjustbox(source)

    @unittest.skipUnless(shutil.which("pandoc"), "layout conversion requires Pandoc")
    def test_conversion_restores_both_exact_farey_inequality_cells(self):
        first, second = self.INEQUALITIES
        command = r"\adjustbox{max width=\linewidth}{" + "$" + first + "$}"
        source = (
            r"\documentclass{article}\begin{document}\begin{tabular}{ll}" + "\n"
            r"Computation & Exact statement \\ \hline" + "\n"
            "Farey & Every $q\\in\\mathbb{N}$ with " + command + r" satisfies the gap certificate. \\" + "\n"
            "Coprimality & Every $d\\in\\mathbb{N}$ with \\adjustbox{max width=\\linewidth}{$" + second
            + r"$} (exactly $\lfloor Q_0/2\rfloor$) is excluded. \\" + "\n"
            r"\end{tabular}" + "\n"
            + r"Literal code: \verb|" + command + "|.\n"
            + r"Nested braces: \adjustbox{max width=\linewidth}{$\frac{q+1}{\mathbb{N}}$}."
            + r"\end{document}"
        )
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "fixture.tex"
            path.write_text(source)
            text = renderer._convert(path, "fixture")['markdown']
        for formula in (*self.INEQUALITIES, r"\frac{q+1}{\mathbb{N}}"):
            self.assertIn("$`" + formula + "`$", text)
        self.assertNotIn("with satisfies", text)
        self.assertNotIn("with (exactly", text)
        self.assertIn("`" + command + "`", text)
        tables = list(table_render.find_tables(text.splitlines()))
        self.assertEqual(len(tables), 1)
        self.assertEqual(len(tables[0][2]), 2)
        self.assertEqual(table_render.analyse(tables[0][1], tables[0][2])['overflow_px'], 0)


class GfmTableReadingTests(unittest.TestCase):
    def test_multiline_cell_moves_intact_after_all_complete_rows(self):
        cell = "Before $`1/2 <\n\\sum_{d\\in N}1/(2^d-1)`$ after [8](#sec%3Aknown)."
        link = "[`half_lt_tsum_negativeMobius`](https://example.org/source.lean#L164)"
        source = (
            "| Result | Source |\n|:---|:---|\n"
            + "| " + cell + " | " + link + " |\n"
            + "| Second row remains | [2](#sec%3Asecond) |\n\nFollowing prose.\n"
        )
        projected = renderer._externalize_long_gfm_table_source_notes(source)
        tables = list(table_render.find_tables(projected.splitlines()))
        self.assertEqual(len(tables), 1)
        self.assertEqual(len(tables[0][2]), 2)
        self.assertEqual(table_render.analyse(tables[0][1], tables[0][2])['overflow_px'], 0)
        self.assertIn("**Detail note 1.** " + cell, projected)
        self.assertEqual(projected.count(cell), 1)
        self.assertEqual(projected.count(link), 1)
        self.assertLess(projected.index("Second row remains"), projected.index("**Detail note 1.**"))
        self.assertIn("\n\nFollowing prose.\n", projected)

    def test_incomplete_rows_remain_exact_and_do_not_absorb_following_rows(self):
        for broken in (
            "| broken | $`unterminated\ncontinuation with no close\n",
            "| broken | still incomplete\n(source: `a_very_long_exact_source_coordinate_that_must_stay_here.lean`)\n",
            "| broken | wrong | column count |\n",
        ):
            source = "| Result | Source |\n|:---|:---|\n" + broken + "| valid | untouched |\n\n"
            with self.subTest(broken=broken):
                self.assertEqual(renderer._externalize_long_gfm_table_source_notes(source), source)

    @unittest.skipUnless(shutil.which("pandoc"), "multiline table conversion requires Pandoc")
    def test_pandoc_multiline_rows_keep_every_formula_and_link_in_notes(self):
        formulas = (
            "1/2 <\n\\sum_{d\\in N}1/(2^d-1)",
            "\\{19,\\allowbreak23,\\allowbreak25,\n\\allowbreak27,\\allowbreak29\\}",
        )
        source = (
            r"\documentclass{article}\begin{document}\section{Known}\label{sec:known}" + "\n"
            + r"\begin{tabular}{ll}Result & Scope \\ \hline" + "\n"
            + "Overshoots: $" + formulas[0] + r"$; Section~\ref{sec:known}. & One support \\" + "\n"
            + "Finite set: $" + formulas[1] + r"$. & Exact computation \\" + "\n"
            + r"\end{tabular}\end{document}"
        )
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "fixture.tex"
            path.write_text(source)
            with patch.object(renderer, "_externalize_long_gfm_table_source_notes", side_effect=lambda text: text):
                unprojected = renderer._convert(path, "fixture")['markdown']
            text = renderer._convert(path, "fixture")['markdown']
        # Pandoc may pad a small pipe table before this owner sees it. Preserve
        # those emitted formula bytes too, including every physical newline.
        emitted_formulas = re.findall(r'\$`(.*?)`\$', unprojected, re.DOTALL)
        self.assertEqual(len(emitted_formulas), 2)
        self.assertCountEqual(re.findall(r'\$`(.*?)`\$', text, re.DOTALL), emitted_formulas)
        self.assertCountEqual([re.sub(r'\s+', '', formula) for formula in emitted_formulas],
                              [re.sub(r'\s+', '', formula) for formula in formulas])
        self.assertIn('[1](#sec%3Aknown)', text)
        self.assertIn('<a id="sec:known"></a>', text)
        tables = list(table_render.find_tables(text.splitlines()))
        self.assertEqual(len(tables), 1)
        self.assertEqual(len(tables[0][2]), 2)
        self.assertEqual(table_render.analyse(tables[0][1], tables[0][2])['overflow_px'], 0)
        self.assertEqual(text.count("**Detail note "), 2)


class CatalogueSignalLinkTests(unittest.TestCase):
    def test_source_relative_links_relocate_without_changing_literals_or_url_suffixes(self):
        prose = (
            '[replay](verification/replay.md?run=one%20two#record%3Aone) '
            '[root guide](../README.md) [paper](papers/full-text/fixture.md) '
            '[web](https://example.org/verification/replay.md#record) '
            '[mail](mailto:review@example.org) [local](#record) '
            '[absolute](/verification/replay.md) '
            '`[code](verification/replay.md)` '
            '$[z^k](z;q)$ $`[math](verification/replay.md)`$'
        )
        expected = (
            '[replay](../verification/replay.md?run=one%20two#record%3Aone) '
            '[root guide](../../README.md) [paper](full-text/fixture.md) '
            '[web](https://example.org/verification/replay.md#record) '
            '[mail](mailto:review@example.org) [local](#record) '
            '[absolute](/verification/replay.md) '
            '`[code](verification/replay.md)` '
            '$[z^k](z;q)$ $`[math](verification/replay.md)`$'
        )
        self.assertEqual(renderer._signal_text(prose, field="evidence_certainty"), expected)

    def test_relocated_catalogue_fixture_resolves_same_authored_destinations(self):
        records = json.loads((edition.ROOT / 'docs/papers/corpus.json').read_text())['papers']
        showcase = json.loads((edition.ROOT / 'docs/PALOMAR_RESULT_SHOWCASE.json').read_text())
        claims = json.loads((edition.ROOT / 'docs/claims.json').read_text())
        evidence = 'Replay [record](verification/replay.md#record) and [guide](../README.md).'
        showcase['candidate_ranking'][0]['evidence_certainty'] = evidence
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'docs/verification').mkdir(parents=True)
            (root / 'docs/papers').mkdir()
            (root / 'docs/PALOMAR_RESULT_SHOWCASE.json').write_text(json.dumps(showcase))
            (root / 'docs/claims.json').write_text(json.dumps(claims))
            (root / 'docs/RELATED_PROBLEMS.md').write_text('# Problems\n')
            (root / 'docs/verification/replay.md').write_text('# Record\n')
            (root / 'README.md').write_text('# Guide\n')
            rendered = renderer._readme(records, 'plectis-erdos', root)
            evidence_line = next(line for line in rendered.splitlines() if '**Evidence:** Replay' in line)
            self.assertIn('Replay [record](../verification/replay.md#record) and [guide](../../README.md).', evidence_line)
            for authored, delivered in (('verification/replay.md', '../verification/replay.md'),
                                        ('../README.md', '../../README.md')):
                source_target = (root / 'docs' / authored).resolve()
                reader_target = (root / 'docs/papers' / delivered).resolve()
                self.assertEqual(reader_target, source_target)
                self.assertTrue(reader_target.is_file())
            retained = json.loads((root / 'docs/PALOMAR_RESULT_SHOWCASE.json').read_text())
            self.assertEqual(retained['candidate_ranking'][0]['evidence_certainty'], evidence)

    def test_actual_catalogue_evidence_link_reaches_repository_replay_guide(self):
        records = json.loads((edition.ROOT / 'docs/papers/corpus.json').read_text())['papers']
        rendered = renderer._readme(records, 'plectis-erdos', edition.ROOT)
        target = '../verification/EXTERNAL_VERIFICATION_REPLAY.md#pull-request-merge-gate'
        evidence_line = next(line for line in rendered.splitlines() if "replay guide's repository CI record" in line)
        self.assertIn('](' + target + ')', evidence_line)
        destination = (edition.ROOT / 'docs/papers' / target.split('#')[0]).resolve()
        self.assertEqual(destination, edition.ROOT / 'docs/verification/EXTERNAL_VERIFICATION_REPLAY.md')
        self.assertIn('## Pull-request merge gate', destination.read_text())
        showcase = json.loads((edition.ROOT / 'docs/PALOMAR_RESULT_SHOWCASE.json').read_text())
        self.assertIn('](verification/EXTERNAL_VERIFICATION_REPLAY.md#pull-request-merge-gate)',
                      showcase['candidate_ranking'][0]['evidence_certainty'])


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


class ExpositoryPaperTests(unittest.TestCase):
    """A problem's optional expository paper reads after its short and long papers."""

    def test_an_expository_paper_follows_its_problems_pair(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            corpus = root / "docs/papers/corpus.json"
            text_dir = root / "docs/papers/full-text"
            text_dir.mkdir(parents=True)
            rows = []
            # The expository id sorts first; its class still reads last.
            for paper_id, publication_class in (("a-explain", "expository_paper"),
                                                ("c-long", "reasoning_surface"),
                                                ("b-short", "problem_paper")):
                path = text_dir / f"{paper_id}.md"
                path.write_text(f"# {paper_id}\n")
                rows.append({"paper_id": paper_id, "publication_class": publication_class,
                             "publication_state": "active", "subject_kind": "problem",
                             "subject": "Erdős #257", "local_full_text": path.relative_to(root).as_posix()})
            corpus.write_text(json.dumps({"papers": rows}))
            with patch.object(edition, "ROOT", root), patch.object(edition, "CORPUS", corpus):
                papers = edition.mathematical_papers()
        self.assertEqual([row["paper_id"] for row in papers], ["b-short", "c-long", "a-explain"])

if __name__ == "__main__":
    unittest.main()
