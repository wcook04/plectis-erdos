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
import os
import re
import stat
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "docs" / "declaration_atlas.json"
GENERATED_MANIFEST = ROOT / "docs" / "generated_certificate_manifest.json"

# A Lean identifier may end in a prime or contain `?`/`!`.  The previous
# pattern closed the name with `\b`, so `half_pow_term'` was recorded as
# `half_pow_term` and `integerGreedyRemainder_lt_of_get?_eq_false` as
# `integerGreedyRemainder_lt_of_get`.  Every citation of the real name then
# failed to resolve against the atlas.  The name now runs to the first
# character that cannot appear in an identifier.
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?:(?:noncomputable|private|protected|scoped|local|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+"
    r"([A-Za-z_\u00c0-\u024f\u0370-\u03ff][^\s(){}\[\]:,]*)(?=$|[\s({:\[])"
)
KEYWORD_ONLY_RE = re.compile(
    r"^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?:(?:noncomputable|private|protected|scoped|local|partial|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s*$"
)
# How far past a keyword-only line to look for the name it introduces.  Only
# blank and line-comment lines are skipped, so the window stops at the first
# line carrying content whatever that content turns out to be.
HEAD_LOOKAHEAD = 3
LIBRARY_ROOTS = ("Erdos249257", "ErdosProblems")
ROOT_FILES = tuple(f"{root}.lean" for root in LIBRARY_ROOTS)
IMPORT_RE = re.compile(
    rf"^import ((?:{'|'.join(LIBRARY_ROOTS)})(?:\.[A-Za-z0-9_]+)+)\s*$",
    re.M,
)


class UnsafeAtlasPath(ValueError):
    """A declaration-atlas input or output is outside the safe file boundary."""


def safe_atlas_input_path(path: Path, root: Path = ROOT) -> Path:
    """Resolve an atlas input without following checkout links or special files."""
    candidate = Path(os.path.abspath(path))
    root = Path(os.path.abspath(root))
    if candidate != root and root not in candidate.parents:
        raise UnsafeAtlasPath(f"atlas input escaped checkout: {candidate}")
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeAtlasPath(f"symlinked atlas input: {candidate}")
        if current == root:
            break
        if current.parent == current:
            raise UnsafeAtlasPath(f"atlas input escaped checkout: {candidate}")
        current = current.parent
    if not candidate.is_file():
        raise UnsafeAtlasPath(f"atlas input is not a regular file: {candidate}")
    return candidate


def safe_atlas_text(path: Path, root: Path = ROOT) -> str:
    """Read an atlas input through a no-follow regular-file descriptor."""
    candidate = safe_atlas_input_path(path, root=root)
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeAtlasPath(f"atlas input could not be opened safely: {candidate}") from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeAtlasPath(f"atlas input is not a regular file: {candidate}")
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
    except OSError as exc:
        raise UnsafeAtlasPath(f"atlas input could not be read safely: {candidate}") from exc
    finally:
        os.close(descriptor)
    try:
        return b"".join(chunks).decode("utf-8")
    except UnicodeDecodeError as exc:
        raise UnsafeAtlasPath(f"atlas input is not UTF-8: {candidate}") from exc


def safe_atlas_output_path(path: Path, root: Path = ROOT) -> Path:
    """Resolve a generated atlas output without following parent symlinks."""
    candidate = Path(os.path.abspath(path))
    root = Path(os.path.abspath(root))
    if candidate != root and root not in candidate.parents:
        raise UnsafeAtlasPath(f"atlas output escaped checkout: {candidate}")
    current = candidate.parent
    while True:
        if current.is_symlink():
            raise UnsafeAtlasPath(f"symlinked atlas output parent: {candidate}")
        if current == root:
            break
        if current.parent == current:
            raise UnsafeAtlasPath(f"atlas output escaped checkout: {candidate}")
        current = current.parent
    return candidate


def safe_atlas_output_text(path: Path, content: str, root: Path = ROOT) -> None:
    """Write generated atlas content through a no-follow regular-file descriptor."""
    candidate = safe_atlas_output_path(path, root=root)
    flags = (
        os.O_WRONLY
        | os.O_CREAT
        | os.O_TRUNC
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_NONBLOCK", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )
    try:
        descriptor = os.open(candidate, flags, 0o644)
    except OSError as exc:
        raise UnsafeAtlasPath(
            f"atlas output could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeAtlasPath(f"atlas output is not a regular file: {candidate}")
        payload = content.encode("utf-8")
        offset = 0
        while offset < len(payload):
            written = os.write(descriptor, payload[offset:])
            if written <= 0:
                raise UnsafeAtlasPath(f"atlas output write made no progress: {candidate}")
            offset += written
        os.fsync(descriptor)
    except OSError as exc:
        raise UnsafeAtlasPath(f"atlas output could not be written safely: {candidate}") from exc
    finally:
        os.close(descriptor)


def source_paths() -> list[Path]:
    return [
        path
        for library_root, root_file in zip(LIBRARY_ROOTS, ROOT_FILES, strict=True)
        for path in (
            ROOT / root_file,
            *sorted((ROOT / library_root).rglob("*.lean")),
        )
    ]


def code_lines(lines: list[str]) -> list[bool]:
    """Mark which lines carry Lean code rather than comment prose.

    ``DECL_RE`` matched anywhere, including inside docstrings, so a sentence
    that wrapped onto a line beginning ``theorem says that`` or ``lemma used
    by`` was extracted as a declaration named ``says`` or ``used``.  Those
    phantoms inflated the declaration count and could never be owned by any
    semantic node, because there is nothing there to own.

    Lean block comments nest, so depth is tracked rather than toggled.
    """
    marks: list[bool] = []
    depth = 0
    for raw in lines:
        start_depth = depth
        index = 0
        # Generated certificate lines can be hundreds of kilobytes long.  A
        # character-at-a-time Python loop made this comment filter dominate
        # the exhaustive atlas build.  ``str.find`` performs the same token
        # walk in C and jumps directly between the only three delimiters that
        # can change the state.
        while index < len(raw) - 1:
            opener = raw.find("/-", index)
            closer = raw.find("-/", index) if depth else -1
            line_comment = raw.find("--", index) if depth == 0 else -1
            candidates = [position for position in (opener, closer) if position >= 0]
            next_block = min(candidates) if candidates else -1
            if line_comment >= 0 and (next_block < 0 or line_comment < next_block):
                break
            if next_block < 0:
                break
            if next_block == opener:
                depth += 1
                index = opener + 2
                continue
            depth -= 1
            index = closer + 2
        marks.append(start_depth == 0)
    return marks


def declaration_head(lines: list[str], index: int) -> tuple[str, str] | None:
    """Return the ``(kind, name)`` the declaration head at ``index`` opens.

    A head may wrap: the keyword on one line and the name on the next.  The
    builder matched a single line at a time, so ``DECL_RE`` could never span
    the newline its own pattern allows, and every wrapped declaration was
    dropped from the atlas -- which made correct citations of it look
    fabricated.  A keyword-only line therefore grows the window forward to the
    first line that carries content.

    An anonymous ``instance``, whose head is followed by binders rather than a
    name, has nothing to record and yields ``None``.
    """
    match = DECL_RE.match(lines[index])
    if match:
        return match.group(1), match.group(2)
    if not KEYWORD_ONLY_RE.match(lines[index]):
        return None
    for follow in lines[index + 1 : index + 1 + HEAD_LOOKAHEAD]:
        stripped = follow.strip()
        if not stripped or stripped.startswith("--"):
            continue
        match = DECL_RE.match(f"{lines[index].rstrip()} {stripped}")
        return (match.group(1), match.group(2)) if match else None
    return None


def generated_modules() -> dict[str, str]:
    """Map generated module path to the family that owns it.

    Provenance is a contract, not a filename pattern.  The earlier heuristic
    matched only ``/GeneratedCertificates`` and ``/DiagonalPincerPrimeCertificates/``
    and therefore reported the eighteen emitted ``DiagonalPincerCertificates``
    window modules -- 5,246 declarations -- as authored mathematics.
    """
    manifest = json.loads(safe_atlas_text(GENERATED_MANIFEST))
    return {
        path: family["id"]
        for family in manifest["families"]
        for path in family["module_paths"]
    }


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

    # Walk backwards to the opener that matches the immediately preceding
    # block-comment close.  The previous implementation searched up to forty
    # lines for *any* `/--`; if the preceding block was a section comment
    # (`/-! ... -/`), it crossed intervening Lean code and attached an older
    # theorem's docstring and body to the next declaration.
    depth = 0
    opener_line: int | None = None
    opener_column: int | None = None
    for line_index in range(end, -1, -1):
        tokens = list(re.finditer(r"/-|-/", lines[line_index]))
        for token in reversed(tokens):
            if token.group(0) == "-/":
                depth += 1
            else:
                depth -= 1
                if depth == 0:
                    opener_line = line_index
                    opener_column = token.start()
                    break
        if opener_line is not None:
            break
    if opener_line is None or opener_column is None:
        return None
    if not lines[opener_line].startswith("/--", opener_column):
        return None

    text = " ".join(line.strip() for line in lines[opener_line : end + 1])
    text = text.replace("/--", "", 1).rsplit("-/", 1)[0]
    text = re.sub(r"\s+", " ", text).strip()
    return text[:1000] or None


def _update_source_digest(
    digest,
    relative_path: str,
    text: str,
) -> None:
    """Apply the declaration-atlas source-fingerprint framing exactly once."""
    digest.update(
        relative_path.encode("utf-8")
        + b"\0"
        + text.encode("utf-8")
        + b"\0"
    )


def source_fingerprint(paths: list[Path] | None = None) -> str:
    """Hash current Lean inputs without paying the full declaration parse cost."""
    digest = hashlib.sha256()
    for path in source_paths() if paths is None else paths:
        relative_path = path.relative_to(ROOT).as_posix()
        _update_source_digest(digest, relative_path, safe_atlas_text(path))
    return f"sha256:{digest.hexdigest()}"


def build() -> dict[str, object]:
    claims = json.loads(safe_atlas_text(ROOT / "docs" / "claims.json"))
    claim_refs: dict[tuple[str, str], list[str]] = {}
    for claim in claims["claims"]:
        for decl in claim["declarations"]:
            claim_refs.setdefault((decl["module"], decl["name"]), []).append(claim["id"])

    paths = source_paths()
    generated_index = generated_modules()
    digest = hashlib.sha256()
    modules: list[dict[str, object]] = []
    declarations: list[dict[str, object]] = []
    kind_counts: Counter[str] = Counter()
    generated_count = 0

    for path in paths:
        rel = path.relative_to(ROOT).as_posix()
        text = safe_atlas_text(path)
        _update_source_digest(digest, rel, text)
        lines = text.splitlines()
        module_decls: list[dict[str, object]] = []
        is_code = code_lines(lines)
        for index in range(len(lines)):
            if not is_code[index]:
                continue
            head = declaration_head(lines, index)
            if head is None:
                continue
            kind, name = head
            generated_family = generated_index.get(rel)
            generated = generated_family is not None
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
            if generated:
                row["generated_family"] = generated_family
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
        actual = safe_atlas_text(OUTPUT) if OUTPUT.is_file() else ""
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
    safe_atlas_output_text(OUTPUT, expected)
    atlas = json.loads(expected)
    print(
        f"wrote {OUTPUT.relative_to(ROOT)}: "
        f"{atlas['summary']['declaration_count']} declarations across "
        f"{atlas['summary']['module_count']} modules"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
