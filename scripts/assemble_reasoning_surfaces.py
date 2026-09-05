#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Assemble the eight long reasoning papers from their public source owners.

The public manuscripts are deliberately flat: Pandoc and TeX must see every
section without following a private include tree.  The #249/#257 records use
reviewable authored parts.  The other six reuse their problem note's complete
mathematical body and bibliography, then add a long-only preamble and generated
family catalogue.  The builder inlines every source with visible part markers;
``--check`` is the freshness gate.

The --bootstrap mode is a one-time migration aid. It splits an existing flat
manuscript at its part markers and refuses to overwrite an existing parts
directory. Normal authoring uses --write after editing a part.
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
PARTS_ROOT = ROOT / "paper" / "reasoning-parts"
MARKER_RE = re.compile(r"^% ---- part ([a-z0-9_]+) ----\n", re.MULTILINE)

PAPERS = {
    "68": {
        "output": ROOT / "paper" / "erdos68-factorial-reasoning-surface.tex",
        "directory": PARTS_ROOT / "erdos68",
        "note_source": ROOT / "paper" / "erdos-68-factorial-denominator-irrationality.tex",
        "title": "The Factorial-Denominator Series: Complete Reasoning Record",
        "subtitle": "Erd\\H{o}s Problem~\\#68",
        "runninghead": "Erd\\H{o}s \\#68: complete reasoning record",
        "pdf_title": "The Factorial-Denominator Series: complete reasoning record for Erdős Problem 68",
        "parts": ("family_catalogue",),
    },
    "243": {
        "output": ROOT / "paper" / "erdos243-reciprocal-tail-reasoning-surface.tex",
        "directory": PARTS_ROOT / "erdos243",
        "note_source": ROOT / "paper" / "erdos-243-reciprocal-tail-rigidity.tex",
        "title": "Reciprocal-Tail Rigidity: Complete Reasoning Record",
        "subtitle": "Erd\\H{o}s Problem~\\#243",
        "runninghead": "Erd\\H{o}s \\#243: complete reasoning record",
        "pdf_title": "Reciprocal-tail rigidity: complete reasoning record for Erdős Problem 243",
        "parts": ("family_catalogue",),
    },
    "249": {
        "output": ROOT / "paper" / "erdos249-totient-reasoning-surface.tex",
        "directory": PARTS_ROOT / "erdos249",
        "parts": (
            "a249_front",
            "a249_p0",
            "a249_p1a",
            "a249_p1b",
            "a249_newdecls",
            "a249_p2",
            "a249_p3",
            "a249_p4",
            "a249_invent",
            "a249_family_catalogue",
            "a249_p5",
        ),
    },
    "251": {
        "output": ROOT / "paper" / "erdos251-prime-gap-reasoning-surface.tex",
        "directory": PARTS_ROOT / "erdos251",
        "note_source": ROOT / "paper" / "erdos-251-prime-gap-dyadic-series.tex",
        "title": "Prime Gaps and Dyadic Tails: Complete Reasoning Record",
        "subtitle": "Erd\\H{o}s Problem~\\#251",
        "runninghead": "Erd\\H{o}s \\#251: complete reasoning record",
        "pdf_title": "Prime gaps and dyadic tails: complete reasoning record for Erdős Problem 251",
        "parts": ("family_catalogue",),
        "trim_note_core_terminal_newline": True,
    },
    "257": {
        "output": ROOT / "paper" / "erdos257-mersenne-reasoning-surface.tex",
        "directory": PARTS_ROOT / "erdos257",
        "parts": (
            "a257_front",
            "a257_p0",
            "a257_p1a",
            "a257_p1b",
            "a257_newdecls",
            "a257_p2",
            "a257_p3",
            "a257_p4",
            "a257_invent",
            "a257_family_catalogue",
            "a257_p5",
        ),
    },
    "269": {
        "output": ROOT / "paper" / "erdos269-running-lcm-reasoning-surface.tex",
        "directory": PARTS_ROOT / "erdos269",
        "note_source": ROOT / "paper" / "erdos-269-three-prime-running-lcm.tex",
        "title": "The Three-Prime Running LCM: Complete Reasoning Record",
        "subtitle": "Erd\\H{o}s Problem~\\#269",
        "runninghead": "Erd\\H{o}s \\#269: complete reasoning record",
        "pdf_title": "The three-prime running least common multiple: complete reasoning record for Erdős Problem 269",
        "parts": ("family_catalogue",),
    },
    "1041": {
        "output": ROOT / "paper" / "erdos1041-lemniscate-reasoning-surface.tex",
        "directory": PARTS_ROOT / "erdos1041",
        "note_source": ROOT / "paper" / "erdos-1041-lemniscate-newton-flow.tex",
        "title": "Lemniscates and Newton Flow: Complete Reasoning Record",
        "subtitle": "Erd\\H{o}s Problem~\\#1041",
        "runninghead": "Erd\\H{o}s \\#1041: complete reasoning record",
        "pdf_title": "Lemniscates and Newton flow: complete reasoning record for Erdős Problem 1041",
        "parts": ("family_catalogue",),
        "trim_note_core_terminal_newline": True,
    },
    "1049": {
        "output": ROOT / "paper" / "erdos1049-rational-base-lambert-reasoning-surface.tex",
        "directory": PARTS_ROOT / "erdos1049",
        "note_source": ROOT / "paper" / "erdos-1049-rational-base-lambert.tex",
        "title": "Rational-Base Lambert Series: Complete Reasoning Record",
        "subtitle": "Erd\\H{o}s Problem~\\#1049",
        "runninghead": "Erd\\H{o}s \\#1049: complete reasoning record",
        "pdf_title": "Rational-base Lambert series: complete reasoning record for Erdős Problem 1049",
        "parts": ("family_catalogue",),
    },
}

NOTE_DOCUMENT_RE = re.compile(
    r"(?P<preamble>.*?\\begin\{document\}\n)"
    r"(?P<core>.*?)"
    r"(?P<back>\\begin\{thebibliography\}.*)",
    re.DOTALL,
)


def split_flat(text: str, expected: tuple[str, ...]) -> tuple[str, dict[str, str]]:
    matches = list(MARKER_RE.finditer(text))
    names = tuple(match.group(1) for match in matches)
    if names != expected:
        raise ValueError(f"part markers {names!r} do not match manifest {expected!r}")
    preamble = text[: matches[0].start()]
    parts: dict[str, str] = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        parts[match.group(1)] = text[match.end() : end]
    return preamble, parts


def bootstrap(key: str) -> None:
    row = PAPERS[key]
    if row.get("note_source") is not None:
        raise ValueError(
            f"paper {key} derives its mathematical body from its problem note; "
            "use --bootstrap-from-note"
        )
    directory: Path = row["directory"]
    if directory.exists():
        raise ValueError(f"refusing to overwrite existing authored parts: {directory}")
    output: Path = row["output"]
    preamble, parts = split_flat(output.read_text(encoding="utf-8"), row["parts"])
    directory.mkdir(parents=True)
    (directory / "preamble.tex").write_text(preamble, encoding="utf-8")
    for name, text in parts.items():
        (directory / f"{name}.tex").write_text(text, encoding="utf-8")


def _replace_single(text: str, pattern: str, replacement: str, label: str) -> str:
    updated, count = re.subn(
        pattern, lambda _match: replacement, text, count=1, flags=re.DOTALL
    )
    if count != 1:
        raise ValueError(f"could not replace {label} exactly once")
    return updated


def _replace_document_role_header(text: str) -> str:
    replacement = (
        "% Long-form reasoning record seeded from the complete problem note.\n"
        "% The short note and this record are now independent publication units.\n"
        "% This flat manuscript is generated from reviewable parts below.\n"
    )
    patterns = (
        r"% Standalone Erd.*?% Build from the public paper directory with `make`\.\n",
        r"% One of the Erd.*?% `tectonic .*?` or `make`\.\n",
    )
    for pattern in patterns:
        updated, count = re.subn(
            pattern, lambda _match: replacement, text, count=1, flags=re.DOTALL
        )
        if count == 1:
            return updated
    raise ValueError("could not replace document-role header exactly once")


def bootstrap_from_note(key: str) -> None:
    """Seed a missing long record from the complete current problem note.

    The operation is deliberately one-shot.  It creates only the long-form
    preamble and generated-family placeholder; the mathematical core and
    bibliography continue to come from the problem note on every assembly.
    """

    row = PAPERS[key]
    note_source: Path | None = row.get("note_source")
    if note_source is None:
        raise ValueError(f"paper {key} is not bootstrapped from a problem note")
    directory: Path = row["directory"]
    output: Path = row["output"]
    if directory.exists() or output.exists():
        raise ValueError(
            f"refusing to overwrite existing long-form source: {directory} or {output}"
        )
    match = NOTE_DOCUMENT_RE.fullmatch(note_source.read_text(encoding="utf-8"))
    if not match:
        raise ValueError(
            f"cannot split note at document/bibliography boundaries: {note_source}"
        )

    preamble = match.group("preamble")
    preamble = _replace_document_role_header(preamble)
    preamble = _replace_single(
        preamble,
        r"\\runninghead\{[^\n]*\}",
        f"\\runninghead{{{row['runninghead']}}}",
        "running head",
    )
    preamble = _replace_single(
        preamble,
        r"\\title\{[^\n]*\}",
        f"\\title{{{row['title']}}}",
        "title",
    )
    preamble = _replace_single(
        preamble,
        r"\\subtitle\{[^\n]*\}",
        f"\\subtitle{{{row['subtitle']}}}",
        "subtitle",
    )
    preamble = _replace_single(
        preamble,
        r"pdftitle=\{[^\n]*\}",
        f"pdftitle={{{row['pdf_title']}}}",
        "PDF title",
    )

    directory.mkdir(parents=True)
    (directory / "preamble.tex").write_text(preamble, encoding="utf-8")
    (directory / "family_catalogue.tex").write_text(
        "% Generated by scripts/build_paper_result_integration.py.\n",
        encoding="utf-8",
    )
    write_one(key)


def note_document_parts(row: dict[str, object]) -> tuple[str, str]:
    """Read the note-owned core and bibliography for one derived long paper."""
    note_source = row.get("note_source")
    if not isinstance(note_source, Path):
        raise ValueError("note-derived paper lacks a problem-note source")
    match = NOTE_DOCUMENT_RE.fullmatch(note_source.read_text(encoding="utf-8"))
    if not match:
        raise ValueError(
            f"cannot split note at document/bibliography boundaries: {note_source}"
        )
    core = match.group("core")
    if row.get("trim_note_core_terminal_newline") is True:
        if not core.endswith("\n\n"):
            raise ValueError(
                f"note core lost its byte-compatibility seam: {note_source}"
            )
        # The first generated long outputs for #251 and #1041 omitted exactly
        # one otherwise inert blank-line byte at this seam. Preserve their
        # committed flat-manuscript identity without retaining a body copy.
        core = core[:-1]
    return core, match.group("back")


def assemble(key: str) -> str:
    row = PAPERS[key]
    directory: Path = row["directory"]
    chunks = [(directory / "preamble.tex").read_text(encoding="utf-8")]
    if row.get("note_source") is not None:
        core, back = note_document_parts(row)
        chunks.extend(
            (
                "% ---- part core ----\n",
                core,
                "% ---- part family_catalogue ----\n",
                (directory / "family_catalogue.tex").read_text(encoding="utf-8"),
                "% ---- part back ----\n",
                back,
            )
        )
        return "".join(chunks)
    for name in row["parts"]:
        chunks.append(f"% ---- part {name} ----\n")
        chunks.append((directory / f"{name}.tex").read_text(encoding="utf-8"))
    return "".join(chunks)


def check_one(key: str) -> bool:
    row = PAPERS[key]
    output: Path = row["output"]
    actual = output.read_text(encoding="utf-8")
    expected = assemble(key)
    if actual == expected:
        return True
    relative = output.relative_to(ROOT)
    print(f"{relative}: assembled output is stale", file=sys.stderr)
    diff = difflib.unified_diff(
        actual.splitlines(),
        expected.splitlines(),
        fromfile=str(relative),
        tofile=f"assembled:{relative}",
        lineterm="",
        n=2,
    )
    for line in list(diff)[:80]:
        print(line, file=sys.stderr)
    return False


def write_one(key: str) -> None:
    row = PAPERS[key]
    output: Path = row["output"]
    expected = assemble(key)
    if not output.exists() or output.read_text(encoding="utf-8") != expected:
        output.write_text(expected, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--bootstrap", action="store_true")
    action.add_argument("--bootstrap-from-note", action="store_true")
    action.add_argument("--write", action="store_true")
    action.add_argument("--check", action="store_true")
    parser.add_argument("--paper", choices=("all", *PAPERS), default="all")
    args = parser.parse_args()
    keys = tuple(PAPERS) if args.paper == "all" else (args.paper,)

    try:
        if args.bootstrap:
            for key in keys:
                bootstrap(key)
            for key in keys:
                if not check_one(key):
                    return 1
            return 0
        if args.bootstrap_from_note:
            for key in keys:
                bootstrap_from_note(key)
            return 0
        if args.write:
            for key in keys:
                write_one(key)
            return 0
        return 0 if all(check_one(key) for key in keys) else 1
    except (OSError, ValueError) as exc:
        print(f"assemble_reasoning_surfaces: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
