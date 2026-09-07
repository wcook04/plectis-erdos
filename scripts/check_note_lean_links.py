#!/usr/bin/env python3
"""Verify that every Lean hyperlink in a problem note points at a real declaration.

WHY
---
The problem notes cite Lean with ``\\lref{File.lean}{LINE}{decl}``,
``\\lword{File.lean}{LINE}{decl}{words}``, ``\\lloc{File.lean}{LINE}``,
``\\lrefx{...}``, and the sibling-library forms ``\\mref``/``\\mword``/``\\mloc``
whose first argument is repository-relative. Each link is pinned to ``\\commit``
on the public repository, so a wrong line number is a dead reader affordance
that no LaTeX build catches. This checker resolves every link against the
working tree (``--root``) and reports links whose target line does not carry the
named declaration, and links into files that do not exist.

It checks organisation only: it never reads theorem bodies or changes claim
status. A declaration is "at" a line when the ``theorem``/``lemma``/``def``/
``abbrev``/``structure``/``instance``/``noncomputable def`` keyword and the
declaration's last dotted component appear within ``--slack`` lines of it.

USAGE
-----
    ./repo-python formal_math/erdos257_period_noncollapse/scripts/check_note_lean_links.py \
        [--root formal_math/erdos257_period_noncollapse] [--slack 2] [--json] [NOTE.tex ...]

Exit 0 when every link resolves, 1 otherwise, 2 on usage error.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve()
DEFAULT_ROOT = HERE.parents[1]
DEFAULT_NOTES = sorted((DEFAULT_ROOT / "ErdosProblems" / "papers").glob("erdos-*.tex"))

# \lref{file}{line}{decl}  \lword{file}{line}{decl}{words}  \lloc{file}{line}
# \lrefx{file}{line}{decl} (251 local variant)  and the m-forms with repo-relative file.
LINK_RE = re.compile(
    r"\\(?P<macro>lref|lrefx|lword|lloc|mref|mword|mloc)\{(?P<file>[^}]*)\}\{(?P<line>[^}]*)\}(?:\{(?P<decl>[^}]*)\})?"
)
DECL_KW_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|instance|inductive|class|opaque|axiom)\b"
)


def resolve_file(root: Path, macro: str, rel: str) -> Path:
    if macro.startswith("m"):
        return root / rel
    return root / "ErdosProblems" / rel


def resolve_first(roots: list[Path], macro: str, rel: str) -> Path | None:
    """First root (private tree, then any fallback such as a public checkout) holding the file."""
    for root in roots:
        cand = resolve_file(root, macro, rel)
        if cand.is_file():
            return cand
    return None


def check_note(note: Path, root: Path, slack: int, fallback_roots: list[Path] | None = None) -> list[dict]:
    findings: list[dict] = []
    roots = [root, *(fallback_roots or [])]
    text = note.read_text(encoding="utf-8")
    for m in LINK_RE.finditer(text):
        macro, rel, line_s, decl = m.group("macro"), m.group("file"), m.group("line"), m.group("decl")
        note_line = text.count("\n", 0, m.start()) + 1
        row = {"note": note.name, "note_line": note_line, "macro": macro, "file": rel, "line": line_s, "decl": decl}
        target = resolve_first(roots, macro, rel)
        if target is None:
            findings.append({**row, "status": "missing_file"})
            continue
        try:
            ln = int(line_s)
        except ValueError:
            findings.append({**row, "status": "non_integer_line"})
            continue
        lines = target.read_text(encoding="utf-8").splitlines()
        if not (1 <= ln <= len(lines)):
            findings.append({**row, "status": "line_out_of_range", "file_lines": len(lines)})
            continue
        lo, hi = max(1, ln - slack), min(len(lines), ln + slack)
        window = lines[lo - 1 : hi]
        has_kw = any(DECL_KW_RE.match(x) for x in window)
        short = (decl or "").split(".")[-1]
        has_name = (not decl) or any(re.search(rf"\b{re.escape(short)}\b", x) for x in window)
        if has_kw and has_name:
            continue
        findings.append({
            **row,
            "status": "declaration_not_at_line" if has_kw else "no_declaration_keyword_near_line",
            "window": [f"{lo + i}: {x.rstrip()}" for i, x in enumerate(window)],
        })
    return findings


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("notes", nargs="*", type=Path, default=None)
    ap.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    ap.add_argument("--fallback-root", type=Path, action="append", default=[],
                    help="extra checkout to resolve links the private tree lacks (e.g. a public plectis-erdos worktree holding Erdos249257/)")
    ap.add_argument("--slack", type=int, default=2)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    notes = [Path(p) for p in args.notes] if args.notes else DEFAULT_NOTES
    if not notes:
        print("no notes selected", file=sys.stderr)
        return 2
    total = 0
    bad: list[dict] = []
    for note in notes:
        text = note.read_text(encoding="utf-8")
        n_links = len(LINK_RE.findall(text))
        total += n_links
        bad.extend(check_note(note, args.root, args.slack, args.fallback_root))
    if args.json:
        print(json.dumps({"links": total, "failures": bad}, indent=1, ensure_ascii=False))
    else:
        print(f"links checked: {total}; failures: {len(bad)}")
        for b in bad:
            print(f"  {b['note']}:{b['note_line']} \\{b['macro']} {b['file']}:{b['line']} {b.get('decl') or ''} -> {b['status']}")
            for w in b.get("window", []):
                print(f"      {w}")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
