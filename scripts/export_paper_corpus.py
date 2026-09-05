#!/usr/bin/env python3
"""Regenerate this public repository's clone-local paper corpus.

The builder is intentionally self-contained in the public release. Registered
manuscripts and their metadata come from this checkout, so no sibling checkout
or external registry is needed to reproduce the generated Markdown, catalogue,
or source hashes.

So each repository receives a generated corpus: every paper as navigable text,
every paper's PDF, and one orientation file small enough to read on contact.

Two bands, because the two readers want different things.

The *orientation band* -- ``README.md`` and ``corpus.json`` -- is small. It says
which papers exist, which are active or retired, which question each answers,
where a first-time reader should start, what each paper is not authority for,
and where every artefact is. An agent reads this and knows the shape of the
world without loading every PDF.

The *full-text band* is the papers themselves, addressable. Each paper becomes
GitHub-flavoured Markdown with its section labels preserved as HTML anchors, so
``sec:unresolved`` is a thing an agent can jump to rather than a thing it must
find. The index in ``corpus.json`` carries every section's label, title, and line
number in the generated file.

Why Markdown and not the exact LaTeX. The corpus that ships to the site embeds
exact ``.tex``, and it is right to: byte-exact source is the fidelity floor and
the thing a hash can bind. But exact LaTeX is a bad *navigation* surface --
macros hide the content, ``\\ref`` is a dangling token, and a reader cannot tell
which theorem number is meant. Conversion here is not lossy compression; it
resolves things the source only implies. ``\\lref{Foo.lean}{386}{name}`` becomes
an absolute commit-pinned GitHub URL. ``Section~\\ref{sec:ladder}`` becomes
"Section 3" with a working anchor. ``\\cite[p.~63]{erdos1948}`` becomes a visible
citation rather than the silent nothing pandoc emits by default. So both bands
ship: ``.tex`` is authority, ``.md`` is the route, and each says so.

Repository ownership remains explicit in every row. The current corpus is
native to this repository; the schema retains a labelled mirror relation for a
future deliberately vendored manuscript without making it the default.

Freshness is checkable without this tool. Every record carries the SHA-256 of
the source it was built from, so a repository's own CI can hash its manuscript
and compare, with no pandoc and no sibling checkout. ``--check`` does exactly
that and exits non-zero on drift.

Usage::

    python3 scripts/export_paper_corpus.py --write
    python3 scripts/export_paper_corpus.py --check
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import posixpath
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import validation_singleflight as singleflight

CORPUS_SCHEMA = "plectis_paper_corpus_v0"
REGISTRY_SCHEMA = "plectis_public_paper_registry_v0"
THIS_REPOSITORY = "plectis-erdos"
CORPUS_DIR_REL = "docs/papers"
PAPER_LICENCE = "CC-BY-4.0"
COPYRIGHT = "2026 Will Cook"

# The authority order is quoted from the shipped scholarly corpus rather than
# paraphrased, so the two surfaces cannot drift into saying different things
# about what proves what.
AUTHORITY_ORDER = (
    "checked Lean source is proof authority; the claims registry owns public "
    "status and coordinates; methodology owns transition rules; the paper owns "
    "exposition"
)

FULL_TEXT_DIR = "full-text"

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "docs" / "papers" / "paper_registry.json"
# The publication taxonomy -- document class, manuscript status, review state,
# citation, and the explicit absence of any DOI -- is projected from the records
# below rather than authored. The local projector is imported so it and the
# corpus exporter continue to serialize the same object byte for byte.
_TAXONOMY_BUILDER = (
    ROOT / "docs" / "papers" / "build_publication_taxonomy.py"
)
TRUSTED_PANDOC_PATHS = (
    Path("/opt/homebrew/bin/pandoc"),
    Path("/usr/local/bin/pandoc"),
    Path("/usr/bin/pandoc"),
)
_PANDOC_EXECUTABLE: str | None = None


@dataclass(frozen=True)
class Paper:
    paper_id: str
    source: str
    pdf: str
    canonical_repository: str
    canonical_source_path: str
    canonical_source_commit: str | None
    home_repository: str
    relation_to_this_repository: str
    fallback_title: str
    question: str
    subject: str
    subject_kind: str
    form: str
    owns: str
    not_authority_for: str
    publication_state: str
    first_pass: tuple[str, ...]
    first_pass_stated_by_paper: bool
    reading_route_label: str | None

    @property
    def tex_rel(self) -> str:
        return self.source

    @property
    def pdf_rel(self) -> str:
        return self.pdf

    @property
    def home_repo(self) -> str:
        return self.home_repository

    @property
    def stem(self) -> str:
        return Path(self.pdf).stem

    @property
    def is_native(self) -> bool:
        return self.relation_to_this_repository == "native"


def papers_for_exported_corpus() -> tuple[Paper, ...]:
    """Load and validate the authored public paper inventory."""
    payload = json.loads(REGISTRY.read_text(encoding="utf-8"))
    if payload.get("schema") != REGISTRY_SCHEMA:
        raise ValueError(f"{REGISTRY.relative_to(ROOT)} must use {REGISTRY_SCHEMA}")
    if payload.get("this_repository") != THIS_REPOSITORY:
        raise ValueError("paper registry names the wrong repository")
    rows = payload.get("papers")
    if not isinstance(rows, list) or not rows:
        raise ValueError("paper registry must contain a non-empty papers list")
    papers: list[Paper] = []
    seen: set[str] = set()
    registered_sources: set[str] = set()
    registered_native_sources: set[str] = set()
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("paper registry rows must be objects")
        paper_id = row.get("paper_id")
        if not isinstance(paper_id, str) or not paper_id or paper_id in seen:
            raise ValueError(f"invalid or duplicate paper id: {paper_id!r}")
        seen.add(paper_id)
        if row.get("relation_to_this_repository") not in {"native", "mirror"}:
            raise ValueError(f"{paper_id}: invalid repository relation")
        source = row.get("source")
        pdf = row.get("pdf")
        if not isinstance(source, str) or not isinstance(pdf, str):
            raise ValueError(f"{paper_id}: source and pdf must be local paths")
        for field, value in (("source", source), ("pdf", pdf)):
            candidate = Path(value)
            if candidate.is_absolute() or ".." in candidate.parts:
                raise ValueError(f"{paper_id}: {field} must stay inside the repository")
        if source in registered_sources:
            raise ValueError(f"multiple paper rows use source {source}")
        registered_sources.add(source)
        if row.get("relation_to_this_repository") == "native":
            registered_native_sources.add(source)
        papers.append(
            Paper(
                **{
                    **row,
                    "first_pass": tuple(row.get("first_pass") or ()),
                }
            )
        )
    support_sources = payload.get("support_sources")
    if not isinstance(support_sources, list) or not all(
        isinstance(value, str) for value in support_sources
    ):
        raise ValueError("paper registry must declare support_sources")
    discovered = {
        str(path.relative_to(ROOT)) for path in (ROOT / "paper").glob("*.tex")
    }
    covered = registered_native_sources | set(support_sources)
    if discovered != covered:
        raise ValueError(
            "paper registry does not cover local paper/*.tex inputs: "
            f"missing={sorted(discovered - covered)}, "
            f"stale={sorted(covered - discovered)}"
        )
    return tuple(papers)


def _canonical_url(paper: Paper, *, raw: bool = False) -> str:
    ref = paper.canonical_source_commit or "main"
    if raw:
        return (
            f"https://raw.githubusercontent.com/{paper.canonical_repository}/"
            f"{ref}/{paper.canonical_source_path}"
        )
    return (
        f"https://github.com/{paper.canonical_repository}/blob/"
        f"{ref}/{paper.canonical_source_path}"
    )


def _load_taxonomy_builder() -> Any:
    """Load the local projector so one copy of the rules serves both lanes.

    Its ``_serialise`` deliberately matches the ``json.dumps(corpus, indent=2)``
    form used below, so the two agree byte for byte and neither reports drift
    against the other.
    """
    spec = importlib.util.spec_from_file_location(
        "_plectis_publication_taxonomy", _TAXONOMY_BUILDER
    )
    if spec is None or spec.loader is None:  # pragma: no cover - packaging fault
        raise RuntimeError(f"cannot load taxonomy projector at {_TAXONOMY_BUILDER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# --------------------------------------------------------------------------
# pandoc AST handling
# --------------------------------------------------------------------------


def resolve_pandoc(explicit: str | None = None) -> str | None:
    """Resolve Pandoc without consulting the caller's ambient ``PATH``."""
    if explicit is not None:
        requested = Path(explicit)
        if not requested.is_absolute():
            raise ValueError("--pandoc must name an absolute executable path")
        candidates = (requested,)
    else:
        system = shutil.which("pandoc", path=os.defpath)
        candidates = TRUSTED_PANDOC_PATHS + ((Path(system),) if system else ())
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate.resolve())
    return None


def _pandoc_environment(executable: str) -> dict[str, str]:
    """Give Pandoc only the canonical child environment plus its trusted bin."""
    environment = singleflight.command_environment()
    executable_directory = str(Path(executable).resolve().parent)
    environment["PATH"] = os.pathsep.join(
        (executable_directory, environment["PATH"])
    )
    return environment

# Inline nodes whose content is a bare list of inlines.
_PLAIN_INLINE_CONTAINERS = {
    "Emph", "Strong", "Strikeout", "Superscript", "Subscript", "SmallCaps", "Para", "Plain",
}
# Inline nodes shaped [attr, [inline]] or [attr, [inline], target].
_ATTR_INLINE_CONTAINERS = {"Span", "Link", "Image"}


def _stringify(node: Any) -> str:
    """Plain text of a pandoc inline tree.

    Written out by node shape rather than by guessing, because pandoc's content
    field means different things per node: ``Code`` is ``[attr, str]`` while
    ``Emph`` is ``[inline]``, and a generic "recurse into lists of dicts" walk
    silently drops the former. That bug produced section titles with holes.
    """
    if isinstance(node, list):
        return "".join(_stringify(n) for n in node)
    if not isinstance(node, dict):
        return ""
    tag = node.get("t")
    content = node.get("c")
    if tag == "Str":
        return content if isinstance(content, str) else ""
    if tag in ("Space", "SoftBreak", "LineBreak"):
        return " "
    if tag in _PLAIN_INLINE_CONTAINERS:
        return _stringify(content)
    if tag in _ATTR_INLINE_CONTAINERS:
        return _stringify(content[1]) if isinstance(content, list) and len(content) > 1 else ""
    if tag in ("Code", "Math", "RawInline"):
        # [attr_or_type, string]
        return content[1] if isinstance(content, list) and len(content) > 1 else ""
    if tag == "Quoted":
        return _stringify(content[1]) if isinstance(content, list) and len(content) > 1 else ""
    if tag == "Cite":
        return _stringify(content[1]) if isinstance(content, list) and len(content) > 1 else ""
    if tag == "Note":
        return ""
    if isinstance(content, list):
        return "".join(_stringify(n) for n in content if isinstance(n, (dict, list)))
    return ""


def _render_citation(node: dict[str, Any]) -> dict[str, Any]:
    """``Cite`` -> visible bracketed key, because GFM otherwise emits nothing.

    These papers declare their bibliography inline with ``thebibliography``
    rather than a ``.bib``, so pandoc has citation *data* in the AST but no
    citeproc database to format against, and its Markdown writer drops the node
    entirely -- turning "Erdos's 1948 theorem~\\cite{erdos1948}." into
    "Erdos's 1948 theorem ." with a dangling space. The keys are stable and
    resolvable against the bibliography section that does survive, so emitting
    the key is both honest and useful.
    """
    citations = node["c"][0]
    parts: list[str] = []
    for citation in citations:
        key = citation.get("citationId", "")
        prefix = _stringify(citation.get("citationPrefix")).strip()
        suffix = _stringify(citation.get("citationSuffix")).strip()
        text = f"{prefix} {key}".strip() if prefix else key
        if suffix:
            text = f"{text}, {suffix}"
        parts.append(text)
    return {"t": "Str", "c": "[" + "; ".join(parts) + "]"}


class _AstWalk:
    """One pass that fixes citations, anchors headers, and indexes sections."""

    def __init__(self) -> None:
        self.sections: list[dict[str, Any]] = []
        self.citations_rendered = 0

    def blocks(self, blocks: list[Any]) -> list[Any]:
        out: list[Any] = []
        for block in blocks:
            if isinstance(block, dict) and block.get("t") == "Header":
                level, attr, inlines = block["c"]
                anchor = attr[0]
                title = _stringify(inlines).strip()
                if anchor:
                    # A raw HTML anchor survives into GFM, where pandoc's header
                    # attributes do not. Without it the paper's own \label ids --
                    # the stable names everything else refers to -- would not
                    # exist in the generated file at all.
                    out.append({"t": "RawBlock", "c": ["html", f'<a id="{anchor}"></a>']})
                self.sections.append({"level": level, "id": anchor, "title": title})
            out.append(self.node(block))
        return out

    def node(self, node: Any) -> Any:
        if isinstance(node, list):
            return [self.node(x) for x in node]
        if not isinstance(node, dict):
            return node
        if node.get("t") == "Cite":
            self.citations_rendered += 1
            return _render_citation(node)
        return {k: (self.node(v) if k == "c" else v) for k, v in node.items()}


def _pandoc(args: list[str], stdin: str | None = None, cwd: Path | None = None) -> str:
    """Run pandoc, and treat every potentially lossy warning as fatal.

    Both halves of this matter. ``cwd`` must be the manuscript's own directory,
    because these papers ``\\input`` a macro file by relative name; handing
    pandoc an absolute path from elsewhere makes that include unresolvable.

    Pandoc reports that failure as a *warning* on stderr while still exiting
    0. Every macro the missing file defined then expands to nothing, so whole
    passages disappear from the output with no error anywhere -- which is
    exactly what happened here, silently dropping the half-value subsections
    while the build reported success. A conversion that loses text is not a
    successful conversion, so warnings are escalated rather than printed.

    One warning class is explicitly non-lossy in the JSON-to-GFM pass:
    ``Could not convert TeX math ..., rendering as TeX``. In that case pandoc
    preserves the complete formula as a TeX math node in Markdown. The full
    reasoning papers use valid formula fragments that the GFM math writer does
    not simplify, so rejecting this fallback would make those real manuscripts
    impossible to export. No other warning is admitted.
    """
    executable = _PANDOC_EXECUTABLE or resolve_pandoc()
    if executable is None:
        raise RuntimeError("pandoc is required to build the paper corpus")
    result = subprocess.run(
        [executable, *args],
        input=stdin,
        capture_output=True,
        text=True,
        check=False,
        cwd=str(cwd) if cwd else None,
        env=_pandoc_environment(executable),
    )
    if result.returncode != 0:
        raise RuntimeError(f"pandoc failed ({result.returncode}): {result.stderr.strip()}")
    warnings = [
        line.strip()
        for line in result.stderr.splitlines()
        if line.strip()
    ]
    json_to_gfm = "-f" in args and args[args.index("-f") + 1] == "json"
    nonlossy_math_warning = re.compile(
        r"^\[WARNING\] Could not convert TeX math .+, rendering as TeX$"
    )
    fatal_warnings = [
        warning
        for warning in warnings
        if not (json_to_gfm and nonlossy_math_warning.fullmatch(warning))
    ]
    if fatal_warnings:
        raise RuntimeError(
            "pandoc emitted warnings; refusing to ship a possibly lossy conversion:\n"
            + "\n".join(fatal_warnings)
        )
    return result.stdout


def _meta_blocks(meta: dict[str, Any], stem: str) -> tuple[list[Any], str, str | None]:
    """Title, subtitle, and abstract as leading blocks, plus the plain title.

    Pandoc parks ``\\title``, ``\\subtitle`` and ``\\abstract`` in document
    metadata, and its Markdown writer emits none of them without a template. The
    result was a 64-page paper whose generated text began at "Introduction" --
    no title, no abstract. For a reader deciding whether this is the paper they
    want, that is the worst possible thing to drop.
    """
    title = _stringify(meta.get("title", {}).get("c")) if "title" in meta else ""
    subtitle = _stringify(meta.get("subtitle", {}).get("c")) if "subtitle" in meta else ""
    # Headers only -- the anchor for each is emitted by the walk that indexes
    # them, so adding one here too would double it.
    blocks: list[Any] = []
    if title:
        blocks.append({"t": "Header", "c": [1, [stem, [], []], [{"t": "Str", "c": title}]]})
    if subtitle:
        blocks.append({"t": "Para", "c": [{"t": "Emph", "c": [{"t": "Str", "c": subtitle}]}]})
    abstract = meta.get("abstract")
    if abstract is not None:
        blocks.append({"t": "Header", "c": [2, ["abstract", [], []], [{"t": "Str", "c": "Abstract"}]]})
        body = abstract.get("c")
        blocks.extend(body if isinstance(body, list) else [body])
    return blocks, title, subtitle or None


_DEF_RE = re.compile(r"\\long\\def\\([A-Za-z]+)\{")
_PATH_RE = re.compile(r"\\path\{")
_PDECL_RE = re.compile(r"\\pdecl\{([A-Za-z0-9_']+)\}")


def _matching_brace(text: str, open_index: int) -> int:
    """Index of the brace closing the one at ``open_index``.

    TeX-aware enough for these manuscripts: a backslash escapes the next
    character, and a percent starts a comment that runs to end of line. Both
    would otherwise let a stray brace unbalance the scan.
    """
    depth = 0
    i = open_index
    while i < len(text):
        char = text[i]
        if char == "\\":
            i += 2
            continue
        if char == "%":
            newline = text.find("\n", i)
            if newline == -1:
                break
            i = newline + 1
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise ValueError("unbalanced brace while expanding a \\long\\def macro")


def _path_argument_end(text: str, open_index: int) -> int:
    """Return the close brace for a ``\\path`` argument.

    ``url``-package path arguments give characters such as ``%`` their literal
    meaning, so the ordinary TeX scanner above is deliberately not reused.
    Backslash escapes and nested braces are still honoured.
    """
    depth = 0
    index = open_index
    while index < len(text):
        char = text[index]
        if char == "\\":
            index += 2
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return index
        index += 1
    raise ValueError("unbalanced brace in \\path argument")


def _preserve_path_macros(tex: str) -> str:
    """Translate ``\\path{...}`` to Pandoc-readable literal code.

    Pandoc's LaTeX reader silently removes ``\\path`` and its argument before
    producing an AST.  That left exported sentences with missing filenames and
    tool names even though conversion exited successfully.  ``\\verb`` has the
    same literal-text semantics needed by the Markdown projection and Pandoc
    emits it as inline code.
    """
    chunks: list[str] = []
    cursor = 0
    while True:
        match = _PATH_RE.search(tex, cursor)
        if match is None:
            chunks.append(tex[cursor:])
            return "".join(chunks)
        open_index = match.end() - 1
        close_index = _path_argument_end(tex, open_index)
        literal = tex[open_index + 1 : close_index]
        delimiter = next(
            (candidate for candidate in "|!+;:@?" if candidate not in literal),
            None,
        )
        if delimiter is None:
            raise ValueError(
                "\\path argument uses every supported literal delimiter"
            )
        chunks.extend(
            (
                tex[cursor : match.start()],
                f"\\verb{delimiter}{literal}{delimiter}",
            )
        )
        cursor = close_index + 1


def _readable_lean_label(identifier: str) -> str:
    """Reproduce the paper preamble's human-readable declaration label.

    The ``\\pdecl`` helper is intentionally presentation-only: unlike
    ``\\lword`` it carries no source coordinate. Pandoc silently drops an
    unknown one-argument macro and its argument, which previously turned lists
    of declarations into runs of empty commas. Preserve the manuscript's
    lower-case, spaced label rather than promoting it to a source link.
    """
    spaced = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", identifier)
    spaced = re.sub(r"_+", " ", spaced)
    return " ".join(spaced.split()).lower()


def _preserve_declaration_macros(tex: str) -> str:
    """Expand presentation-only ``\\pdecl`` uses before Pandoc sees them."""

    return _PDECL_RE.sub(
        lambda match: rf"\emph{{{_readable_lean_label(match.group(1))}}}",
        tex,
    )


def _remove_immediate_duplicate_gfm_table_headers(markdown: str) -> str:
    """Remove the repeated header row emitted for a LaTeX ``longtable``.

    Pandoc correctly selects the first ``longtable`` header as the GFM table
    header, but it can also emit the identical ``\\endhead`` row as the first
    body row. The only row removed here is an exact duplicate immediately after
    the GFM alignment delimiter, so ordinary repeated data rows are untouched.
    """

    lines = markdown.splitlines(keepends=True)
    out: list[str] = []
    index = 0
    delimiter = re.compile(r"^\s*\|(?:\s*:?-+:?\s*\|)+\s*$")
    while index < len(lines):
        if (
            index + 2 < len(lines)
            and lines[index].lstrip().startswith("|")
            and delimiter.fullmatch(lines[index + 1].rstrip("\r\n"))
            and lines[index].strip() == lines[index + 2].strip()
        ):
            out.extend((lines[index], lines[index + 1]))
            index += 3
            continue
        out.append(lines[index])
        index += 1
    return "".join(out)


_LOCAL_PDF_LINK = re.compile(
    r"(?P<open>\]\()(?P<target>[^)\s]+\.pdf)(?P<fragment>#[^)]*)?(?P<close>\))"
)


def _pdf_link_targets() -> dict[str, str]:
    """Map manuscript PDF basenames to their exported full-text-relative path."""

    full_text_dir = f"{CORPUS_DIR_REL}/{FULL_TEXT_DIR}"
    targets: dict[str, str] = {}
    for paper in papers_for_exported_corpus():
        if paper.is_native:
            destination = paper.pdf_rel
        else:
            destination = paper.pdf_rel
        targets[Path(paper.pdf_rel).name] = posixpath.relpath(
            destination, start=full_text_dir
        )
    return targets


def _rewrite_exported_pdf_links(markdown: str, targets: dict[str, str]) -> str:
    """Make local PDF crosslinks resolve from ``docs/papers/full-text``."""

    def replace(match: re.Match[str]) -> str:
        raw_target = match.group("target")
        if "://" in raw_target:
            return match.group(0)
        basename = Path(raw_target).name
        destination = targets.get(basename)
        if destination is None:
            return match.group(0)
        return (
            f"{match.group('open')}{destination}"
            f"{match.group('fragment') or ''}{match.group('close')}"
        )

    return _LOCAL_PDF_LINK.sub(replace, markdown)


def _inline_long_defs(tex: str) -> tuple[str, list[str]]:
    """Inline ``\\long\\def\\Name{...}`` bodies at the point they are invoked.

    The mathematics paper defines three technical appendices as no-argument TeX
    macros near the material they extend, then places them at the back of the
    document by invoking the macro. TeX expands that; pandoc does not, and it
    does not warn -- it reads the definition, keeps nothing, and silently emits
    a document missing three appendices and roughly a fifth of its text.

    Rewriting the definition to its use site is a faithful transformation for
    argument-free macros: it is what TeX itself does. The count is reported so a
    caller can assert something was expanded rather than assume it.
    """
    expanded: list[str] = []
    while True:
        match = _DEF_RE.search(tex)
        if match is None:
            return tex, expanded
        name = match.group(1)
        open_index = match.end() - 1
        close_index = _matching_brace(tex, open_index)
        body = tex[open_index + 1 : close_index]
        tex = tex[: match.start()] + tex[close_index + 1 :]
        # Replace the single invocation. \Name must not match \NameOther.
        tex, count = re.subn(rf"\\{name}(?![A-Za-z])", lambda _m: body, tex, count=1)
        if count == 0:
            raise RuntimeError(f"\\long\\def\\{name} is defined but never invoked")
        expanded.append(name)


def _sectioning_titles(tex: str) -> int:
    """How many sectioning commands the manuscript will actually typeset."""
    body = tex
    start = body.find("\\iffalse")
    if start != -1:
        end = body.find("\\fi", start)
        body = body[:start] + body[end:] if end != -1 else body[:start]
    return len(re.findall(r"\\(?:sub)*section\*?\{", body))


def _header_block_count(blocks: list[dict[str, Any]]) -> int:
    """Count only injected headings, not title-page prose such as authors."""
    return sum(block.get("t") == "Header" for block in blocks)


def _convert(tex_path: Path, stem: str) -> dict[str, Any]:
    """LaTeX -> markdown, section index with line numbers, and front matter."""
    source = _preserve_path_macros(tex_path.read_text())
    source = _preserve_declaration_macros(source)
    source, inlined = _inline_long_defs(source)
    ast = json.loads(
        _pandoc(["-f", "latex", "-t", "json"], stdin=source, cwd=tex_path.parent)
    )
    front, title, subtitle = _meta_blocks(ast.get("meta") or {}, stem)
    walk = _AstWalk()
    ast["blocks"] = walk.blocks(front + ast["blocks"])
    markdown = _pandoc(["-f", "json", "-t", "gfm", "--wrap=none"], stdin=json.dumps(ast))
    markdown = _remove_immediate_duplicate_gfm_table_headers(markdown)

    # Bind each section to a line in the file it actually landed in. An index
    # that only names sections makes an agent scan; one that names lines lets it
    # seek.
    line_of: dict[str, int] = {}
    for number, line in enumerate(markdown.splitlines(), start=1):
        stripped = line.strip()
        if stripped.startswith('<a id="') and stripped.endswith('"></a>'):
            line_of.setdefault(stripped[7:-6], number)
    for section in walk.sections:
        section["line"] = line_of.get(section["id"])
    # Every sectioning command the manuscript typesets must survive into the
    # output. This is the check that was missing when three \long\def appendices
    # silently vanished: pandoc exited 0, the file looked plausible, and a fifth
    # of the paper was gone. Counting is enough to catch a whole block dropping,
    # and is far cheaper than comparing rendered text.
    expected = _sectioning_titles(source)
    # Remove only emitted headers added by _meta_blocks.  Some manuscripts also
    # receive an author Para in ``front``; subtracting every injected block made
    # a complete 131-section conversion look one section short.
    produced = len(walk.sections) - _header_block_count(front)
    if produced < expected:
        raise RuntimeError(
            f"{tex_path.name}: conversion lost content -- the manuscript typesets "
            f"{expected} sections but the output has {produced}. "
            "Check for macro-wrapped or conditionally-included blocks that pandoc "
            "does not expand."
        )
    return {
        "markdown": markdown,
        "sections": walk.sections,
        "citations_rendered": walk.citations_rendered,
        "title": title,
        "subtitle": subtitle,
        "macros_inlined": inlined,
        "sections_expected": expected,
    }


# --------------------------------------------------------------------------
# corpus assembly
# --------------------------------------------------------------------------


def _sha256(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def _first_pass(sections: list[dict[str, Any]], paper: Paper) -> dict[str, Any]:
    """The declared entry route, resolved against the real section index.

    Declared-but-absent is reported rather than silently dropped: a route
    pointing at a section that no longer exists is worse than no route, because
    it looks authoritative. The provenance travels with it -- whether the paper
    said this or we chose it -- so a reader can weigh the advice.
    """
    by_id = {s["id"]: s for s in sections}
    entries: list[dict[str, Any]] = []
    for label in paper.first_pass:
        section = by_id.get(label)
        entries.append(
            {"id": label, "title": section["title"], "line": section["line"]}
            if section
            else {
                "id": label,
                "resolved": False,
                "reason": "label not present in the current manuscript",
            }
        )
    route: dict[str, Any] = {
        "stated_by_the_paper": paper.first_pass_stated_by_paper,
        "provenance": (
            "the paper's own stated reading route"
            if paper.first_pass_stated_by_paper
            else "editorial selection; this paper states no reading route of its own"
        ),
        "sections": entries,
        "unresolved_count": sum(1 for e in entries if e.get("resolved") is False),
    }
    if paper.reading_route_label:
        stated_at = by_id.get(paper.reading_route_label)
        route["stated_at"] = (
            {"id": paper.reading_route_label, "line": stated_at["line"]}
            if stated_at
            else {"id": paper.reading_route_label, "resolved": False}
        )
    return route


def _paper_record(
    paper: Paper,
    is_native: bool,
    converted: dict[str, Any],
    markdown_rel: str,
    tex_bytes: bytes,
    pdf_bytes: bytes | None,
    source_rel_in_target: str,
    pdf_rel_in_target: str | None,
    source_commit: str | None = None,
) -> dict[str, Any]:
    sections = converted["sections"]
    # The manuscript's own \title, not a second editorial copy of it. The
    # registry string is a fallback for a manuscript that cannot be read.
    title = converted.get("title") or paper.fallback_title
    record: dict[str, Any] = {
        "paper_id": paper.paper_id,
        "title": title,
        "title_source": "manuscript" if converted.get("title") else "registry_fallback",
        "question_this_paper_answers": paper.question,
        # These fields let generated reader routes group papers by the problem
        # they serve instead of accidentally foregrounding a historical joint
        # manuscript just because it appears first in registry order.
        "subject": paper.subject,
        "subject_kind": paper.subject_kind,
        "form": paper.form,
        "owns": paper.owns,
        "not_authority_for": paper.not_authority_for,
        "publication_state": paper.publication_state,
        "relation_to_this_repository": "native" if is_native else "mirror",
        "home_repository": paper.home_repo,
        "licence": PAPER_LICENCE,
        "copyright": COPYRIGHT,
        "local_full_text": markdown_rel,
        "local_source": source_rel_in_target,
        # `source_sha256` hashes the bytes this export just copied. On its own
        # that is a self-certifying record: it can only ever agree with the
        # local mirror, so it cannot detect that the manuscript upstream has
        # moved. `canonical_source_commit` is what makes it checkable — it names
        # the exact upstream commit the bytes came from, and the URLs below
        # resolve against that commit rather than a branch tip. Keep the
        # companion status explicit: a null commit still produces a useful
        # moving URL for readers, but it is not immutable source evidence.
        "source_sha256": _sha256(tex_bytes),
        "canonical_source_commit": source_commit,
        "canonical_source_pin_status": (
            "immutable_commit" if source_commit else "moving_default_ref"
        ),
        "canonical_source_url": _canonical_url(paper),
        "canonical_source_raw_url": _canonical_url(paper, raw=True),
        "section_count": len(sections),
        "sections": sections,
        "citations_rendered": converted["citations_rendered"],
    }
    if converted.get("subtitle"):
        record["subtitle"] = converted["subtitle"]
    if converted.get("title") and converted["title"] != paper.fallback_title:
        # The registry's fallback is only ever used when a manuscript cannot be
        # read, so a mismatch is harmless here and load-bearing elsewhere: it
        # means the label other surfaces show has drifted from the real title.
        # Reported rather than silently corrected -- all three of these were
        # wrong before the registry existed, and nothing noticed.
        record["fallback_title_drift"] = {
            "registry_fallback": paper.fallback_title,
            "manuscript_title": converted["title"],
        }
    if not is_native:
        record["mirror_note"] = (
            f"generated copy; the manuscript is owned by {paper.home_repo} and "
            "authority does not move with the copy"
        )
    if pdf_bytes is not None and pdf_rel_in_target:
        record["local_pdf"] = pdf_rel_in_target
        record["pdf_sha256"] = _sha256(pdf_bytes)
        record["pdf_byte_count"] = len(pdf_bytes)
    if paper.first_pass:
        record["first_pass"] = _first_pass(sections, paper)
    return record


def _relative_to_corpus(repo_rel: str) -> str:
    """Repository-relative path -> link that works from inside the corpus dir.

    The corpus README lives at ``docs/papers/``; a native PDF lives at the
    repository root. Both appear in the same list, so the depth is resolved here
    once rather than guessed per link.
    """
    if repo_rel.startswith(f"{CORPUS_DIR_REL}/"):
        return repo_rel.removeprefix(f"{CORPUS_DIR_REL}/")
    return "../../" + repo_rel


def _section_link(record: dict[str, Any], entry: dict[str, Any]) -> str:
    return f"{_relative_to_corpus(record['local_full_text'])}#{entry['id']}"


def _signal_text(value: Any, *, field: str) -> str:
    """Keep source-owned signal prose on one Markdown line."""
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"Palomar signal field {field} must be non-empty text")
    return " ".join(value.split())


def _signal_paper_record(
    records: list[dict[str, Any]], problem: int
) -> dict[str, Any]:
    """Choose the dedicated problem note for a ranked mathematical family."""
    subject_token = f"#{problem}"
    matches = [
        record
        for record in records
        if subject_token in str(record.get("subject") or "")
        and record.get("publication_state") == "active"
        and record.get("local_full_text")
    ]
    if not matches:
        raise ValueError(
            f"Palomar signal family for Erdős #{problem} lacks an active paper route"
        )
    # Prefer the dedicated note to a longer reasoning surface. The registry
    # remains the authority for the full inventory; this only chooses the first
    # useful route for a signal item.
    matches.sort(
        key=lambda record: (
            0 if str(record.get("paper_id", "")).startswith(f"erdos-{problem}-") else 1,
            str(record.get("paper_id", "")),
        )
    )
    return matches[0]


def _signal_source_link(source: str) -> str:
    """Make a repository-root source path reachable from ``docs/papers``."""
    return f"[Lean source](../../{source})"


def _signal_hierarchy_lines(
    records: list[dict[str, Any]], target_repo: str, repo_root: Path
) -> list[str]:
    """Project Palomar's mathematical judgement before the paper inventory.

    ``docs/PALOMAR_RESULT_SHOWCASE.json`` is the source of the rank and
    disposition judgement. ``docs/claims.json`` supplies the exact checked
    interface, source declaration, problem, and boundary. Paper records only
    supply navigational links. Keeping these joins here makes the generated
    README useful without creating a second mathematical ranking authority.
    """
    showcase_path = repo_root / "docs" / "PALOMAR_RESULT_SHOWCASE.json"
    if not showcase_path.is_file():
        return []
    claims_path = repo_root / "docs" / "claims.json"
    if not claims_path.is_file():
        raise FileNotFoundError(
            f"Palomar signal projection requires {claims_path.relative_to(repo_root)}"
        )
    showcase = json.loads(showcase_path.read_text(encoding="utf-8"))
    claims = json.loads(claims_path.read_text(encoding="utf-8"))
    ranking = showcase.get("candidate_ranking")
    screening = showcase.get("candidate_screening")
    contract = showcase.get("selection_contract")
    disposition_source = showcase.get("candidate_value_dispositions")
    universe = showcase.get("candidate_universe")
    packet = claims.get("external_verification_packet")
    main_results = packet.get("main_results") if isinstance(packet, dict) else None
    if not isinstance(ranking, list) or not ranking:
        raise ValueError("Palomar showcase lacks candidate_ranking")
    ranks = [row.get("rank") for row in ranking]
    if sorted(ranks) != list(range(1, len(ranking) + 1)):
        raise ValueError("Palomar candidate_ranking must use contiguous ranks")
    if len({row.get("family_id") for row in ranking}) != len(ranking):
        raise ValueError("Palomar candidate_ranking must use unique family ids")
    if not isinstance(screening, list):
        raise ValueError("Palomar showcase lacks candidate_screening")
    if not isinstance(contract, dict) or not contract.get("ranking_axes"):
        raise ValueError("Palomar showcase lacks selection_contract.ranking_axes")
    if not isinstance(disposition_source, dict) or not isinstance(universe, dict):
        raise ValueError("Palomar showcase lacks candidate-value disposition authority")
    if not isinstance(main_results, list) or not main_results:
        raise ValueError("claims external_verification_packet lacks main_results")

    by_wrapper: dict[str, dict[str, Any]] = {}
    for result in main_results:
        wrapper = result.get("wrapper_declaration")
        if not isinstance(wrapper, str) or wrapper in by_wrapper:
            raise ValueError("main_results wrapper declarations must be unique")
        by_wrapper[wrapper] = result

    review_by_family: dict[str, dict[str, Any]] = {}
    for problem_row in packet.get("review_matrix", []) if isinstance(packet, dict) else []:
        if not isinstance(problem_row, dict):
            continue
        problem = problem_row.get("problem")
        for family in problem_row.get("families", []):
            if isinstance(family, dict) and isinstance(family.get("id"), str):
                review_by_family[family["id"]] = {
                    "problem": problem,
                    **family,
                }

    dispositions = universe.get("source_family_dispositions")
    if not isinstance(dispositions, dict):
        dispositions = disposition_source.get("source_family_dispositions")
    if not isinstance(dispositions, dict):
        raise ValueError("Palomar showcase lacks source_family_dispositions")

    def checked_result(wrapper: str) -> dict[str, Any]:
        result = by_wrapper.get(wrapper)
        if result is None:
            raise ValueError(
                "Palomar signal declaration lacks a claims main_results row: "
                f"{wrapper}"
            )
        if not isinstance(result.get("problem"), int):
            raise ValueError(f"claims result lacks integer problem for {wrapper}")
        if result.get("review_family") is None:
            raise ValueError(f"claims result lacks review_family for {wrapper}")
        return result

    def screening_identity(
        declaration: str, family_id: str
    ) -> tuple[int, dict[str, Any] | None]:
        result = by_wrapper.get(declaration)
        if result is not None:
            if not isinstance(result.get("problem"), int):
                raise ValueError(f"claims result lacks integer problem for {declaration}")
            return int(result["problem"]), result
        review = review_by_family.get(family_id)
        if review is None or not isinstance(review.get("problem"), int):
            raise ValueError(
                "Palomar screening declaration lacks claims/review-family identity: "
                f"{declaration}"
            )
        # A source-current review family can predate its ExternalVerification
        # wrapper by one projection turn. It is still safe to display as
        # represented natural friction, but not to invent a checked wrapper row.
        return int(review["problem"]), None

    def disposition_family(declaration: str) -> str:
        """Resolve a disposition row without requiring claims to lead Palomar.

        Ranked checked interfaces still require ``main_results``.  The lower
        disposition roster makes no source, statement, or boundary claim, so a
        source-current Palomar screening row is sufficient identity while the
        slower claims projection catches up.
        """
        result = by_wrapper.get(declaration)
        if result is not None:
            family_id = result.get("review_family")
            if not isinstance(family_id, str) or not family_id:
                raise ValueError(
                    f"claims result lacks review_family for {declaration}"
                )
            return family_id
        families = {
            row.get("family_id")
            for row in screening
            if isinstance(row, dict) and row.get("declaration") == declaration
        }
        if len(families) != 1 or not all(
            isinstance(family_id, str) and family_id for family_id in families
        ):
            raise ValueError(
                "Palomar disposition declaration lacks unique screening-family "
                f"identity: {declaration}"
            )
        return next(iter(families))

    lines = [
        "## Mathematical signal first",
        "",
        "This reader order is the existing Palomar `candidate_ranking`, joined",
        "to exact source/current claims and their paper routes. It is a value",
        "judgement about consequence, endpoint proximity, mechanism depth,",
        "distinctness, usefulness, digestion value, evidence certainty, natural",
        "friction, and overclaim risk—not a proof, novelty, or closure claim.",
        "The complete paper inventory follows only after this ranked and",
        "disposition-aware spine.",
        "",
        "### Ranked frontier",
        "",
    ]
    ranked_families: set[str] = set()
    for candidate in sorted(ranking, key=lambda row: row["rank"]):
        wrapper = candidate.get("declaration")
        result = checked_result(wrapper)
        family_id = candidate.get("family_id")
        if result.get("review_family") != family_id:
            raise ValueError(
                "Palomar candidate family does not match claims review_family: "
                f"{family_id}"
            )
        ranked_families.add(family_id)
        paper = _signal_paper_record(records, int(result["problem"]))
        source = result.get("original_source")
        source_declaration = result.get("original_declaration")
        if not isinstance(source, str) or not isinstance(source_declaration, str):
            raise ValueError(f"claims result lacks source identity for {wrapper}")
        route = _relative_to_corpus(str(paper["local_full_text"]))
        lines.extend(
            [
                f"#### {candidate['rank']}. Erdős #{result['problem']} — `{family_id}`",
                "",
                f"**Paper route:** [{paper['paper_id']}]({route})",
                f"  **Checked interface:** `{wrapper}`",
                f"  **Source declaration:** `{source_declaration}` via {_signal_source_link(source)}",
                f"  **Result:** {_signal_text(candidate.get('consequence_and_endpoint_proximity'), field='consequence_and_endpoint_proximity')}",
                f"  **Hard mechanism:** {_signal_text(candidate.get('mechanism_depth_and_natural_friction'), field='mechanism_depth_and_natural_friction')}",
                f"  **Evidence:** {_signal_text(candidate.get('evidence_certainty'), field='evidence_certainty')}",
                f"  **Boundary:** {_signal_text(result.get('boundary'), field='boundary')}",
                "",
            ]
        )

    lines.extend(
        [
            "### Represented natural friction",
            "",
            "These source-current families are represented because they expose",
            "the obstruction, missing producer, or reusable mechanism that a",
            "reader needs to understand the frontier. They are not silently",
            "promoted to endpoint results.",
            "",
        ]
    )
    represented: dict[str, dict[str, Any]] = {}
    for row in screening:
        family_id = row.get("family_id")
        if dispositions.get(family_id) != "represented" or family_id in ranked_families:
            continue
        declaration = row.get("declaration")
        if not isinstance(family_id, str) or not isinstance(declaration, str):
            raise ValueError("Palomar candidate_screening row lacks family/declaration")
        problem, result = screening_identity(declaration, family_id)
        slot = represented.setdefault(
            family_id,
            {
                "declarations": [],
                "reasons": [],
                "problem": problem,
                "paper": _signal_paper_record(records, problem),
            },
        )
        if declaration not in slot["declarations"]:
            slot["declarations"].append(declaration)
        reason = row.get("reason")
        if isinstance(reason, str) and reason not in slot["reasons"]:
            slot["reasons"].append(reason)
    for family_id, row in represented.items():
        declarations = ", ".join(f"`{value}`" for value in row["declarations"])
        reasons = " ".join(_signal_text(value, field="screening.reason") for value in row["reasons"])
        route = _relative_to_corpus(str(row["paper"]["local_full_text"]))
        lines.append(
            f"- `{family_id}` (Erdős #{row['problem']}; [{row['paper']['paper_id']}]({route})): "
            f"{declarations}. {reasons}"
        )
    lines.append("")

    lines.extend(
        [
            "### Explicitly subordinate, rejected, and long tail",
            "",
            "The remaining families stay discoverable in the exhaustive roster",
            "with their disposition visible. Subordinate and rejected entries",
            "are useful boundaries or reductions; long-tail entries are exact",
            "support, identities, finite instances, or auxiliary routes that do",
            "not currently earn scarce first-contact attention.",
            "",
        ]
    )
    eligible_groups = disposition_source.get("eligible_groups")
    if not isinstance(eligible_groups, list):
        raise ValueError("Palomar candidate_value_dispositions lacks eligible_groups")
    for group in eligible_groups:
        disposition = group.get("disposition")
        if disposition not in {"subordinate", "rejected", "long_tail"}:
            continue
        declarations = group.get("declarations")
        if not isinstance(declarations, list):
            raise ValueError(f"Palomar disposition group lacks declarations: {disposition}")
        lines.append(f"#### {disposition.replace('_', ' ').title()}")
        lines.append("")
        reason = _signal_text(group.get("reason"), field=f"{disposition}.reason")
        by_family: dict[str, list[str]] = {}
        for declaration in declarations:
            if not isinstance(declaration, str) or not declaration:
                raise ValueError(
                    f"Palomar {disposition} group contains an invalid declaration"
                )
            family_id = disposition_family(declaration)
            by_family.setdefault(family_id, []).append(declaration)
        for family_id, family_declarations in by_family.items():
            joined = ", ".join(f"`{value}`" for value in family_declarations)
            lines.append(f"- `{family_id}`: {joined}. {reason}")
        lines.append("")
    return lines


def _readme(
    records: list[dict[str, Any]], target_repo: str, repo_root: Path
) -> str:
    """The orientation band as prose. Deliberately short.

    A cold reader should finish this file knowing which paper answers their
    question and where it is. Everything else is a link.
    """
    active_count = sum(
        record.get("publication_state") == "active" for record in records
    )
    retired_count = sum(
        record.get("publication_state") == "retired" for record in records
    )
    pending_count = sum(
        record.get("publication_state") == "pending_source_publication"
        for record in records
    )
    active_problem_subjects: list[str] = []
    for record in records:
        subject = str(record.get("subject") or "").strip()
        if (
            record.get("publication_state") == "active"
            and record.get("subject_kind") == "problem"
            and subject
            and subject not in active_problem_subjects
        ):
            active_problem_subjects.append(subject)

    active_records = [
        record for record in records if record.get("publication_state") == "active"
    ]
    non_active_records = [
        record for record in records if record.get("publication_state") != "active"
    ]
    ordered_records = active_records + non_active_records
    lines: list[str] = [
        "# The papers",
        "",
        "<!-- Generated by scripts/export_paper_corpus.py in this public repository.",
        "     Do not edit by hand: edits are overwritten",
        "     on the next export, and the manuscripts are the source of truth. -->",
        "",
        "This directory carries every active and locally present pending manuscript",
        "as navigable text. Pending rows remain visibly pending and are not promoted",
        "into the active reader ranking. A retired manuscript that remains shipped",
        "as a root PDF is carried for provenance, not restored to an active route.",
        "",
        (
            f"This checkout carries {active_count} active "
            f"{'paper' if active_count == 1 else 'papers'}"
            + (
                f", {pending_count} pending source-publication "
                f"{'paper' if pending_count == 1 else 'papers'},"
                if pending_count
                else ""
            )
            + (
                f" and {retired_count} retired provenance "
                f"{'paper' if retired_count == 1 else 'papers'}"
                if retired_count
                else ""
            )
            + ". Pick the question you are actually asking:"
        ),
        "",
    ]
    lines.extend(_signal_hierarchy_lines(records, target_repo, repo_root))
    if active_problem_subjects:
        lines += [
            f"## Problem portfolio (complete {len(records)}-paper inventory)",
            "",
            "The active mathematical notes form a growing problem-by-problem "
            f"portfolio: {', '.join(active_problem_subjects)}. Start with the "
            "named problem, then use its note for the exact checked results and "
            "remaining obligation. Retired combined manuscripts are provenance, "
            "not the portfolio's front door.",
            "",
        ]
        if target_repo == THIS_REPOSITORY:
            portfolio_path = repo_root / "docs" / "RELATED_PROBLEMS.md"
            if not portfolio_path.is_file():
                raise FileNotFoundError(
                    "Lean paper portfolio route requires "
                    f"{portfolio_path.relative_to(repo_root)}"
                )
            lines += [
                "**Lean portfolio entry:** start with the "
                "[human problem portfolio](../RELATED_PROBLEMS.md). Its "
                "machine-owned `docs/problems.json` index carries exact route "
                "data; this paper mirror is a full-text shelf, not the selector.",
                "",
            ]
    for record in ordered_records:
        lines.append(f"### {record['question_this_paper_answers']}")
        lines.append("")
        subtitle = f" — *{record['subtitle']}*" if record.get("subtitle") else ""
        state = record.get("publication_state", "active")
        state_label = (
            " · **retired provenance manuscript**"
            if state == "retired"
            else (
                " · **pending source publication**"
                if state == "pending_source_publication"
                else ""
            )
        )
        lines.append(f"**{record['title']}**{subtitle}{state_label}")
        lines.append("")
        links = [f"[full text]({_relative_to_corpus(record['local_full_text'])})"]
        if record.get("local_pdf"):
            links.append(f"[PDF]({_relative_to_corpus(record['local_pdf'])})")
        links.append(f"[LaTeX source]({record['canonical_source_url']})")
        lines.append(
            f"{' · '.join(links)} · {record['section_count']} sections · "
            f"`{record['paper_id']}` · {record['relation_to_this_repository']} to this repository"
        )
        lines.append("")
        route = record.get("first_pass")
        if route:
            entries = [e for e in route["sections"] if e.get("resolved") is not False]
            named = ", ".join(f"[{e['title']}]({_section_link(record, e)})" for e in entries)
            lead = (
                "The paper's own reading map sends a first pass to"
                if route["stated_by_the_paper"]
                else "This paper states no reading route. Its evidence boundary is in"
            )
            lines.append(f"{lead} {named}.")
            lines.append("")

    lines += [
        "## What each paper is not",
        "",
        "Reading a paper is not checking it. Each paper is exposition; none of them",
        "is proof authority. In order:",
        "",
        f"> {AUTHORITY_ORDER}.",
        "",
    ]
    for record in records:
        lines.append(
            f"- `{record['paper_id']}` is not authority for {record['not_authority_for']}."
        )
    lines += [
        "",
        "## For agents",
        "",
        f"`corpus.json` is the machine view: every paper, every section with its",
        "`\\label` id and its line number in the generated Markdown, every source",
        "hash, and the authority boundaries above. Read it first; it is small.",
        "",
        "Each generated Markdown file keeps the manuscript's own section labels as",
        "HTML anchors, so a section can be reached by name rather than by scanning:",
        "",
        "```",
        f'grep -n \'<a id="sec:intro">\' {FULL_TEXT_DIR}/*.md',
        "```",
        "",
        "The Markdown is a generated projection. It resolves what the LaTeX only",
        "implies -- theorem numbers, cross-references, and Lean source links become",
        "absolute commit-pinned URLs -- but the `.tex` remains the manuscript and",
        "the hash of record. Where the two disagree, the `.tex` wins.",
        "",
    ]
    return "\n".join(lines)


def _export_repo(write: bool) -> dict[str, Any]:
    target_repo = THIS_REPOSITORY
    repo_root = ROOT
    corpus_dir = repo_root / CORPUS_DIR_REL
    records: list[dict[str, Any]] = []
    planned: list[tuple[Path, bytes]] = []
    drift: list[dict[str, Any]] = []

    pdf_link_targets = _pdf_link_targets()

    for paper in papers_for_exported_corpus():
        is_native = paper.is_native
        source_commit = paper.canonical_source_commit
        tex_path = repo_root / paper.tex_rel
        pdf_path = repo_root / paper.pdf_rel
        if not tex_path.is_file():
            raise FileNotFoundError(f"{paper.paper_id}: manuscript missing at {paper.tex_rel}")
        if not pdf_path.is_file():
            raise FileNotFoundError(f"{paper.paper_id}: shipped PDF missing at {paper.pdf_rel}")

        tex_bytes = tex_path.read_bytes()
        pdf_bytes = pdf_path.read_bytes()
        converted = _convert(tex_path, paper.stem)
        converted["markdown"] = _rewrite_exported_pdf_links(
            converted["markdown"], pdf_link_targets
        )

        md_name = f"{paper.stem}.md"
        md_rel = f"{CORPUS_DIR_REL}/{FULL_TEXT_DIR}/{md_name}"
        planned.append((corpus_dir / FULL_TEXT_DIR / md_name, converted["markdown"].encode()))

        source_rel = paper.tex_rel
        pdf_rel = paper.pdf_rel if pdf_bytes is not None else None

        records.append(
            _paper_record(
                paper, is_native, converted, md_rel,
                tex_bytes, pdf_bytes, source_rel, pdf_rel,
                source_commit,
            )
        )

    corpus = {
        "schema": CORPUS_SCHEMA,
        "role": "clone_local_scholarly_corpus",
        "this_repository": target_repo,
        "why_this_exists": (
            "This corpus carries every active paper and every locally present "
            "pending paper as navigable text, plus the still-shipped retired "
            "manuscript, so an agent with no network can read, cite, and "
            "cross-check the public evidence without changing publication status."
        ),
        "generated_by": "scripts/export_paper_corpus.py",
        "generated_from": (
            "the local authored paper registry and its repository-resident "
            "manuscripts; do not hand-edit generated corpus files"
        ),
        "authority_order": AUTHORITY_ORDER,
        "reading_the_generated_markdown": (
            "The Markdown is a projection of the .tex, not a replacement. It resolves "
            "theorem numbers, cross-references, and Lean source links that the source "
            "only implies. The .tex is the manuscript and the hash of record; where "
            "they disagree, the .tex wins."
        ),
        "verification_boundary": {
            "proof_recheck_performed": False,
            "note": (
                "No Lean kernel ran during this export. Reading a paper, or its "
                "generated text, is not checking a proof."
            ),
        },
        "licences": {
            PAPER_LICENCE: "all carried manuscripts and every view generated from them",
        },
        # This makes the public, dependency-free freshness checker able to
        # distinguish a complete but old catalogue from one that merely hashes
        # the papers it happened to carry. It deliberately records the export
        # selection rather than importing the private registry at check time.
        "expected_paper_ids": [
            paper.paper_id
            for paper in papers_for_exported_corpus()
        ],
        "paper_count": len(records),
        "papers": records,
    }
    corpus = _load_taxonomy_builder().build(corpus, repo_root)
    planned.append((corpus_dir / "corpus.json", (json.dumps(corpus, indent=2) + "\n").encode()))
    planned.append(
        (
            corpus_dir / "README.md",
            _readme(
                [r for r in records if r.get("title")], target_repo, repo_root
            ).encode(),
        )
    )

    written = 0
    for path, payload in planned:
        current = path.read_bytes() if path.is_file() else None
        if current == payload:
            continue
        drift.append(
            {
                "path": str(path.relative_to(repo_root)),
                "state": "missing" if current is None else "stale",
            }
        )
        if write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
            written += 1

    return {
        "repository": target_repo,
        "checkout_path": str(repo_root),
        "status": "written" if write else ("clean" if not drift else "drift"),
        "corpus_dir": CORPUS_DIR_REL,
        "artifact_count": len(planned),
        "papers_carried": sum(1 for r in records if r.get("title")),
        "files_changed": written if write else len(drift),
        "drift": drift,
        "total_bytes": sum(len(p) for _, p in planned),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true", help="write the corpus into each repository")
    mode.add_argument("--check", action="store_true", help="report drift, write nothing, exit 1 if stale")
    parser.add_argument(
        "--pandoc",
        metavar="ABSOLUTE_PATH",
        help="use this absolute Pandoc executable instead of trusted install paths",
    )
    parser.add_argument("--json", action="store_true", help="emit the report as JSON")
    args = parser.parse_args(argv)

    try:
        pandoc = resolve_pandoc(args.pandoc)
    except ValueError as error:
        print(str(error), file=sys.stderr)
        return 2
    if pandoc is None:
        print("pandoc is required to build the paper corpus (brew install pandoc)", file=sys.stderr)
        return 2
    global _PANDOC_EXECUTABLE
    _PANDOC_EXECUTABLE = pandoc

    reports = [_export_repo(write=args.write)]
    report = {"schema": CORPUS_SCHEMA, "mode": "write" if args.write else "check", "repositories": reports}

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        for entry in reports:
            print(f"{entry['repository']}: {entry['status']}", end="")
            if entry["status"] == "absent":
                print(f" ({entry['path']})")
                continue
            print(
                f" — {entry['papers_carried']} papers, {entry['artifact_count']} artifacts, "
                f"{entry['total_bytes'] // 1024} KiB, {entry['files_changed']} changed"
            )
            for row in entry["drift"][:10]:
                print(f"    {row['state']}: {row['path']}")

    stale = [e for e in reports if e["status"] == "drift"]
    if args.check and stale:
        print("\npaper corpus is stale; run with --write", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
