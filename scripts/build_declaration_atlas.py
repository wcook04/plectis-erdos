#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the exhaustive machine-readable declaration atlas.

The atlas is a navigation projection over the public Lean source. It does not
replace Lean proof authority or the authored claim/argument map in
``docs/claims.json``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "docs" / "declaration_atlas.json"

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?:(?:noncomputable|private|protected|scoped|local|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+"
    r"([A-Za-z0-9_'.]+)\b"
)
LIBRARY_ROOTS = ("Erdos249257", "ErdosProblems")
ROOT_FILES = tuple(f"{root}.lean" for root in LIBRARY_ROOTS)
IMPORT_RE = re.compile(
    rf"^import ((?:{'|'.join(LIBRARY_ROOTS)})(?:\.[A-Za-z0-9_]+)+)\s*$",
    re.M,
)


def source_paths() -> list[Path]:
    return [
        path
        for library_root, root_file in zip(LIBRARY_ROOTS, ROOT_FILES, strict=True)
        for path in (
            ROOT / root_file,
            *sorted((ROOT / library_root).rglob("*.lean")),
        )
    ]


def module_id(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def compact_signature(lines: list[str], start: int) -> str:
    pieces: list[str] = []
    for raw in lines[start : start + 14]:
        line = raw.strip()
        if not line or line.startswith("--"):
            continue
        pieces.append(line)
        joined = " ".join(pieces)
        for marker in (":=", " where", " := by", " by"):
            pos = joined.find(marker)
            if pos >= 0:
                joined = joined[:pos]
                return re.sub(r"\s+", " ", joined).strip()[:800]
    return re.sub(r"\s+", " ", " ".join(pieces)).strip()[:800]


def preceding_docstring(lines: list[str], start: int) -> str | None:
    cursor = start - 1
    while cursor >= 0 and (not lines[cursor].strip() or lines[cursor].lstrip().startswith("@[")):
        cursor -= 1
    if cursor < 0 or "-/" not in lines[cursor]:
        return None
    end = cursor
    lower = max(-1, cursor - 40)
    while cursor > lower and "/--" not in lines[cursor]:
        cursor -= 1
    if cursor <= lower or "/--" not in lines[cursor]:
        return None
    text = " ".join(line.strip() for line in lines[cursor : end + 1])
    text = text.replace("/--", "", 1).rsplit("-/", 1)[0]
    text = re.sub(r"\s+", " ", text).strip()
    return text[:1000] or None


def build() -> dict[str, object]:
    claims = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    claim_refs: dict[tuple[str, str], list[str]] = {}
    for claim in claims["claims"]:
        for decl in claim["declarations"]:
            claim_refs.setdefault((decl["module"], decl["name"]), []).append(claim["id"])

    paths = source_paths()
    digest = hashlib.sha256()
    modules: list[dict[str, object]] = []
    declarations: list[dict[str, object]] = []
    kind_counts: Counter[str] = Counter()
    generated_count = 0

    for path in paths:
        rel = path.relative_to(ROOT).as_posix()
        text = path.read_text(encoding="utf-8")
        digest.update(rel.encode("utf-8") + b"\0" + text.encode("utf-8") + b"\0")
        lines = text.splitlines()
        module_decls: list[dict[str, object]] = []
        for index, line in enumerate(lines):
            match = DECL_RE.match(line)
            if not match:
                continue
            kind, name = match.groups()
            generated = (
                "/GeneratedCertificates" in rel
                or "/DiagonalPincerPrimeCertificates/" in rel
            )
            row: dict[str, object] = {
                "id": f"{rel}:{index + 1}:{name}",
                "name": name,
                "kind": kind,
                "module": rel,
                "line": index + 1,
                "signature": compact_signature(lines, index),
                "generated_certificate": generated,
                "claim_ids": claim_refs.get((rel, name), []),
            }
            docstring = preceding_docstring(lines, index)
            if docstring:
                row["docstring"] = docstring
            module_decls.append(row)
            declarations.append(row)
            kind_counts[kind] += 1
            generated_count += int(generated)

        local_counts = Counter(str(row["kind"]) for row in module_decls)
        modules.append(
            {
                "id": module_id(path),
                "path": rel,
                "imports": IMPORT_RE.findall(text),
                "declaration_count": len(module_decls),
                "kind_counts": dict(sorted(local_counts.items())),
            }
        )

    return {
        "schema": "erdos249257-declaration-atlas/1",
        "artifact_role": "generated_exhaustive_navigation_projection",
        "projection_not_authority": True,
        "proof_authority": "Lean source checked by the pinned Lean kernel",
        "argument_authority": "docs/claims.json::machine_readable_paper.argument_graph",
        "source_fingerprint": f"sha256:{digest.hexdigest()}",
        "summary": {
            "module_count": len(modules),
            "declaration_count": len(declarations),
            "theorem_like_count": kind_counts["theorem"] + kind_counts["lemma"],
            "generated_certificate_declaration_count": generated_count,
            "principal_claim_link_count": sum(bool(row["claim_ids"]) for row in declarations),
            "kind_counts": dict(sorted(kind_counts.items())),
        },
        "modules": modules,
        "declarations": declarations,
        "drilldown": {
            "principal_argument_map": "docs/claims.json",
            "human_exposition": "paper/erdos249-257-main-paper.tex",
            "root_import": "Erdos249257.lean",
            "root_imports": list(ROOT_FILES),
            "check": "python3 scripts/build_declaration_atlas.py --check",
        },
    }


def render() -> str:
    return json.dumps(build(), ensure_ascii=False, indent=2) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the tracked atlas is stale")
    args = parser.parse_args()
    expected = render()
    if args.check:
        actual = OUTPUT.read_text(encoding="utf-8") if OUTPUT.is_file() else ""
        if actual != expected:
            print("declaration atlas is stale; run python3 scripts/build_declaration_atlas.py")
            return 1
        atlas = json.loads(actual)
        print(
            "declaration atlas current: "
            f"{atlas['summary']['declaration_count']} declarations across "
            f"{atlas['summary']['module_count']} modules"
        )
        return 0
    OUTPUT.write_text(expected, encoding="utf-8")
    atlas = json.loads(expected)
    print(
        f"wrote {OUTPUT.relative_to(ROOT)}: "
        f"{atlas['summary']['declaration_count']} declarations across "
        f"{atlas['summary']['module_count']} modules"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
