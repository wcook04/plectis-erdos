#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Re-anchor the source-attribution registry after edits to anchored files.

docs/research-commons/source-attributions.json pins every bibliography entry,
citation usage, closure-note locator and Lean review to a line range plus the
SHA-256 of that excerpt. An edit above an anchor moves every later anchor in
the file, and scripts/build_source_attributions.py then rejects the registry.

    python3 scripts/reanchor_source_attributions.py [--root .] [--base origin/main] [--write] [--patch rows.json]

Each anchored file with a row that no longer matches the working tree is
aligned line by line (difflib) against its --base version. Rules, in order:

  current   the recorded digest and expected_text already match; untouched.
  moved     the recorded lines survive unchanged elsewhere; the digest is kept
            and re-verified.
  bibitem   a span from a \\bibitem line through the next \\bibitem or
            \\end{thebibliography} line is re-derived from the same key (and
            expected_text) nearest the mapped position, so it ends on the new
            following item.
  expected  an edited range carrying expected_text is re-found nearest the
            mapped position.
  cite      an edited one-line citation anchor moves to the nearest line
            within 12 lines that carries the same citation keys.
  mapped    any other edited range takes its aligned boundaries; review it.

A row that an earlier --write already re-anchored is found again by its digest,
or re-derived from the base registry row with the same label. Lean reviews and
their context ranges only move: an edited reviewed comment needs a fresh
review, so it is reported as unresolved. The default is a dry run that prints a
summary and every recomputed row. Exit status 1 means some anchor could not be
resolved, and nothing is written. --write saves the registry only when every
anchor resolved and the registry round-trips byte-identically through
json.dumps(indent=2, ensure_ascii=False).

--patch takes a JSON list of source rows. A row whose id exists extends that
source (artifact_links appended, list fields unioned, relation replaced when
given); a new id is appended. Artifact links in a patch may be written as
{"path", "find", "span": "bibitem"|"line", "expected_text"} and are resolved
against the working tree to exact line ranges and digests.
"""

from __future__ import annotations

import argparse
import bisect
import difflib
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterator

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = "docs/research-commons/source-attributions.json"
CITE_WINDOW = 12
CITE_RE = re.compile(
    r"\\(?:cite|citep|citet|citealp|citealt|citeauthor|citeyear|nocite)\s*(?:\[[^\]]*\]\s*){0,2}\{([^}]*)\}",
    re.S,
)
BIBITEM_RE = re.compile(r"\s*\\bibitem(?![A-Za-z@])")
BIBITEM_KEY_RE = re.compile(r"\\bibitem(?![A-Za-z@])(?:\s*\[[^\]]*\])?\s*\{([^}]+)\}")
BIB_END_RE = re.compile(r"\s*\\end\{thebibliography\}")
COMMENT_RE = re.compile(r"(?<!\\)%.*")
ANCHOR_FIELDS = (("artifact_links", "path"), ("paper_reported_locators", "path"), ("source_locators", "evidence_path"))
LEAN_KINDS = {"lean_review", "lean_context"}
FIELD_ORDER = [
    "id", "kind", "title", "authors", "publication_years", "year", "urls", "problems",
    "source_locators", "artifact_links", "relation", "verification_state",
    "bibliography_keys", "verification_scope", "mapping_status", "mapping_note",
    "paper_reported_locators", "identity_disclosure", "confirmation_status",
]
PATCH_LIST_FIELDS = ("urls", "problems", "source_locators", "bibliography_keys", "publication_years")


class ReanchorError(ValueError):
    """An input the tool refuses to act on."""


@dataclass
class Anchor:
    label: str
    row: dict[str, Any]
    path: str
    kind: str


@dataclass
class Change:
    label: str
    path: str
    old: tuple[int, int]
    new: tuple[int, int]
    rule: str
    first_line: str


@dataclass
class Report:
    current: int = 0
    moved: list[Change] = field(default_factory=list)
    recomputed: list[Change] = field(default_factory=list)
    unresolved: list[str] = field(default_factory=list)


def serialise(value: Any) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False) + "\n"


def excerpt(lines: list[str], start: int, end: int) -> str:
    return "\n".join(lines[start - 1:end]) + "\n"


def sha(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode()).hexdigest()


def valid_range(row: dict[str, Any]) -> bool:
    start, end = row.get("line_start"), row.get("line_end")
    return (
        isinstance(start, int) and not isinstance(start, bool)
        and isinstance(end, int) and not isinstance(end, bool)
        and 1 <= start <= end
    )


def matches(lines: list[str], row: dict[str, Any]) -> bool:
    if not valid_range(row) or row["line_end"] > len(lines):
        return False
    text = excerpt(lines, row["line_start"], row["line_end"])
    if "excerpt_sha256" in row and row["excerpt_sha256"] != sha(text):
        return False
    return "expected_text" not in row or (isinstance(row["expected_text"], str) and row["expected_text"] in text)


def set_range(row: dict[str, Any], span: tuple[int, int], digest: str) -> None:
    row["line_start"], row["line_end"] = span
    if "excerpt_sha256" in row:
        row["excerpt_sha256"] = digest


def unsafe_path(value: str) -> bool:
    path = Path(value)
    return not value or path.is_absolute() or ".." in path.parts


def is_boundary(line: str) -> bool:
    return bool(BIBITEM_RE.match(line) or BIB_END_RE.match(line))


def bibitem_key(line: str) -> str | None:
    match = BIBITEM_KEY_RE.search(COMMENT_RE.sub("", line))
    return match.group(1).strip() if match else None


def next_boundary(lines: list[str], start: int) -> int | None:
    for number in range(start + 1, len(lines) + 1):
        if is_boundary(lines[number - 1]):
            return number
    return None


def is_bibitem_span(lines: list[str], start: int, end: int) -> bool:
    return end > start and bool(BIBITEM_RE.match(lines[start - 1])) and next_boundary(lines, start) == end


def cite_keys(line: str) -> set[str]:
    masked = COMMENT_RE.sub("", line)
    return {key.strip() for match in CITE_RE.finditer(masked) for key in match.group(1).split(",") if key.strip()}


def occurrences(lines: list[str], needle: str) -> list[tuple[int, int]]:
    """Return (first_line, last_line) for every occurrence of needle."""
    if not needle or not lines:
        return []
    text = excerpt(lines, 1, len(lines))
    starts = [0]
    for line in lines:
        starts.append(starts[-1] + len(line) + 1)
    hits = []
    position = text.find(needle)
    while position >= 0:
        first = bisect.bisect_right(starts, position)
        last = bisect.bisect_right(starts, position + len(needle) - 1)
        hits.append((first, min(last, len(lines))))
        position = text.find(needle, position + 1)
    return hits


class Alignment:
    """Line correspondence between a base file and its working-tree version."""

    def __init__(self, old: list[str], new: list[str]):
        self.old, self.new = old, new
        self.opcodes = difflib.SequenceMatcher(None, old, new, autojunk=False).get_opcodes()
        self.equal: dict[int, int] = {}
        for tag, i1, i2, j1, _j2 in self.opcodes:
            if tag == "equal":
                for offset in range(i2 - i1):
                    self.equal[i1 + offset + 1] = j1 + offset + 1

    def _opcode(self, line: int) -> tuple[str, int, int, int, int]:
        for opcode in self.opcodes:
            if opcode[1] < line <= opcode[2]:
                return opcode
        raise ReanchorError(f"line {line} lies outside the base file")

    def start(self, line: int) -> int:
        if line in self.equal:
            return self.equal[line]
        _tag, i1, i2, j1, j2 = self._opcode(line)
        return j1 + (line - i1) if j2 - j1 == i2 - i1 else j1 + 1

    def end(self, line: int) -> int:
        if line in self.equal:
            return self.equal[line]
        _tag, i1, i2, j1, j2 = self._opcode(line)
        return j1 + (line - i1) if j2 - j1 == i2 - i1 else j2

    def position(self, line: int) -> int:
        if line in self.equal:
            return self.equal[line]
        _tag, i1, _i2, j1, j2 = self._opcode(line)
        if j2 > j1:
            return j1 + 1 + min(line - i1 - 1, j2 - j1 - 1)
        return min(max(j1, 1), max(len(self.new), 1))

    def contiguous(self, start: int, end: int) -> tuple[int, int] | None:
        first = self.equal.get(start)
        if first is None or any(self.equal.get(start + k) != first + k for k in range(end - start + 1)):
            return None
        return first, first + end - start


def relocate(new: list[str], block: list[str], hint: int) -> tuple[int, int] | None:
    """Find the verbatim base block nearest the hint."""
    best = None
    for index, line in enumerate(new):
        if line == block[0] and new[index:index + len(block)] == block:
            candidate = index + 1
            if best is None or abs(candidate - hint) < abs(best - hint):
                best = candidate
    return None if best is None else (best, best + len(block) - 1)


def relocate_by_digest(new: list[str], row: dict[str, Any]) -> tuple[int, int] | None:
    """Find a window of the recorded length whose excerpt matches the row, nearest its recorded start."""
    if not isinstance(row.get("excerpt_sha256"), str):
        return None
    length = row["line_end"] - row["line_start"] + 1
    last = len(new) - length + 1
    if last < 1:
        return None
    hint = min(row["line_start"], last)
    for distance in range(max(hint - 1, last - hint) + 1):
        for start in dict.fromkeys((hint - distance, hint + distance)):
            if 1 <= start <= last and matches(new, {**row, "line_start": start, "line_end": start + length - 1}):
                return start, start + length - 1
    return None


def resolve_bibitem(old: list[str], new: list[str], align: Alignment, start: int, expected: str | None):
    key = bibitem_key(old[start - 1])
    if key is None and expected is None:
        return None, "the \\bibitem has no key on its first line and no expected_text"
    hint = align.position(start)
    best = None
    for number, line in enumerate(new, 1):
        if not BIBITEM_RE.match(line) or (key is not None and bibitem_key(line) != key):
            continue
        stop = next_boundary(new, number)
        if stop is None or (expected is not None and expected not in excerpt(new, number, stop)):
            continue
        rank = (abs(number - hint), number)
        if best is None or rank < best[0]:
            best = (rank, (number, stop))
    if best is None:
        item = f"\\bibitem{{{key}}}" if key else "\\bibitem"
        return None, f"no {item} span" + (" carrying expected_text" if expected is not None else "") + " remains"
    return best[1], None


def resolve_expected(old: list[str], new: list[str], align: Alignment, start: int, end: int, expected: str):
    hits = occurrences(old[start - 1:end], expected)
    if not hits:
        return None, "expected_text was already absent at base"
    old_first, old_last = start - 1 + hits[0][0], start - 1 + hits[0][1]
    if end > start:
        mapped = (align.start(start), align.end(end))
        if mapped[0] <= mapped[1] and expected in excerpt(new, *mapped):
            return mapped, None
    found = occurrences(new, expected)
    if not found:
        return None, "expected_text is gone from the edited file"
    hint = align.position(old_first)
    new_first, new_last = min(found, key=lambda hit: (abs(hit[0] - hint), hit[0]))
    return (max(1, new_first - (old_first - start)), min(len(new), new_last + (end - old_last))), None


def resolve_cite(new: list[str], align: Alignment, start: int, keys: set[str]):
    hint = align.position(start)
    best = None
    for number in range(max(1, hint - CITE_WINDOW), min(len(new), hint + CITE_WINDOW) + 1):
        found = cite_keys(new[number - 1])
        if found and keys <= found:
            rank = (abs(number - hint), found != keys, number)
            if best is None or rank < best:
                best = rank
    if best is None:
        return None, f"no line within {CITE_WINDOW} lines of new line {hint} cites {', '.join(sorted(keys))}"
    return (best[2], best[2]), None


def iter_anchors(registry: dict[str, Any]) -> Iterator[Anchor]:
    sources = registry.get("sources")
    for source in sources if isinstance(sources, list) else []:
        if not isinstance(source, dict):
            continue
        for field_name, key in ANCHOR_FIELDS:
            rows = source.get(field_name)
            for index, row in enumerate(rows if isinstance(rows, list) else []):
                if isinstance(row, dict) and isinstance(row.get(key), str) and "line_start" in row:
                    yield Anchor(f"{source.get('id')}.{field_name}[{index}]", row, row[key], "source")
    reviews = registry.get("lean_reviews")
    for index, review in enumerate(reviews if isinstance(reviews, list) else []):
        if isinstance(review, dict) and isinstance(review.get("path"), str) and "line_start" in review:
            yield Anchor(f"lean_reviews[{index}]", review, review["path"], "lean_review")
            context = review.get("context")
            if isinstance(context, dict) and "line_start" in context:
                yield Anchor(f"lean_reviews[{index}].context", context, review["path"], "lean_context")


def git(root: Path, *args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(["git", "-C", str(root), *args], capture_output=True, check=False)


def resolve_base(root: Path, base: str) -> str:
    run = git(root, "rev-parse", "--verify", "--quiet", f"{base}^{{commit}}")
    if run.returncode != 0:
        raise ReanchorError(f"base ref {base!r} does not name a commit in {root}")
    return run.stdout.decode().strip()


def base_lines(root: Path, commit: str, path: str) -> list[str] | None:
    run = git(root, "show", f"{commit}:{path}")
    return run.stdout.decode("utf-8").splitlines() if run.returncode == 0 else None


def base_registry_anchors(root: Path, commit: str) -> dict[str, Anchor]:
    run = git(root, "show", f"{commit}:{REGISTRY}")
    try:
        data = json.loads(run.stdout.decode("utf-8")) if run.returncode == 0 else None
    except (UnicodeDecodeError, json.JSONDecodeError):
        data = None
    return {anchor.label: anchor for anchor in iter_anchors(data)} if isinstance(data, dict) else {}


def resolve_anchor(
    anchor: Anchor, base_row: dict[str, Any], old: list[str], new: list[str], align: Alignment, report: Report
) -> bool:
    """Map one row through the alignment from its base coordinates; return whether it changed."""
    row = anchor.row
    recorded = (row["line_start"], row["line_end"])
    start, end = base_row["line_start"], base_row["line_end"]
    where = f"{anchor.label} {anchor.path}:{recorded[0]}-{recorded[1]}"
    old_text = excerpt(old, start, end)
    old_digest = base_row.get("excerpt_sha256", sha(old_text))
    span, rule = align.contiguous(start, end), "moved"
    if span is None:
        span, rule = relocate(new, old[start - 1:end], align.position(start)), "relocated"
    if span is not None:
        new_text = excerpt(new, *span)
        if new_text != old_text or sha(new_text) != old_digest:
            raise AssertionError(f"{where}: an unchanged excerpt changed its digest while moving to {span}")
        set_range(row, span, old_digest)
        report.moved.append(Change(anchor.label, anchor.path, recorded, span, rule, new[span[0] - 1]))
        return True
    if anchor.kind in LEAN_KINDS:
        report.unresolved.append(f"{where}: the reviewed Lean comment was edited; re-read it and restamp the review")
        return False
    expected = base_row.get("expected_text")
    keys = cite_keys(old[start - 1]) if start == end else set()
    if is_bibitem_span(old, start, end):
        rule = "bibitem"
        span, why = resolve_bibitem(old, new, align, start, expected)
    elif expected is not None:
        rule = "expected"
        span, why = resolve_expected(old, new, align, start, end, expected)
    elif keys:
        rule = "cite"
        span, why = resolve_cite(new, align, start, keys)
    else:
        rule = "mapped"
        mapped = (align.start(start), align.end(end))
        span, why = (mapped, None) if mapped[0] <= mapped[1] else (None, "the anchored lines were deleted")
    if span is None:
        report.unresolved.append(f"{where}: {why}")
        return False
    new_text = excerpt(new, *span)
    if expected is not None and expected not in new_text:
        report.unresolved.append(f"{where}: expected_text is absent from new lines {span[0]}-{span[1]}")
        return False
    set_range(row, span, sha(new_text))
    report.recomputed.append(Change(anchor.label, anchor.path, recorded, span, rule, new[span[0] - 1]))
    return True


def reanchor(root: Path, commit: str, registry: dict[str, Any]) -> Report:
    report = Report()
    by_path: dict[str, list[Anchor]] = {}
    for anchor in iter_anchors(registry):
        by_path.setdefault(anchor.path, []).append(anchor)
    prior_rows: dict[str, Anchor] | None = None
    changed: set[int] = set()
    for path, anchors in by_path.items():
        if unsafe_path(path):
            report.unresolved.extend(f"{a.label} {path}: unsafe repository-relative path" for a in anchors)
            continue
        target = root / path
        try:
            new = target.read_text(encoding="utf-8").splitlines() if target.is_file() else None
        except (OSError, UnicodeDecodeError) as exc:
            report.unresolved.extend(f"{a.label} {path}: unreadable: {exc}" for a in anchors)
            continue
        pending = []
        for anchor in anchors:
            if not valid_range(anchor.row):
                report.unresolved.append(f"{anchor.label} {path}: malformed line range")
            elif new is not None and matches(new, anchor.row):
                report.current += 1
            else:
                pending.append(anchor)
        if not pending:
            continue
        if new is None:
            report.unresolved.extend(
                f"{a.label} {path}:{a.row['line_start']}-{a.row['line_end']}: file is missing from the working tree"
                for a in pending
            )
            continue
        try:
            old = base_lines(root, commit, path)
        except UnicodeDecodeError:
            old = None
        align = Alignment(old, new) if old is not None else None
        for anchor in pending:
            row = anchor.row
            recorded = (row["line_start"], row["line_end"])
            if old is not None and align is not None and matches(old, row):
                base_row = row
            else:
                span = relocate_by_digest(new, row)
                if span is not None:
                    row["line_start"], row["line_end"] = span
                    report.moved.append(Change(anchor.label, path, recorded, span, "relocated", new[span[0] - 1]))
                    changed.add(id(row))
                    continue
                if prior_rows is None:
                    prior_rows = base_registry_anchors(root, commit)
                prior = prior_rows.get(anchor.label)
                if (
                    old is None or align is None or prior is None or prior.path != path
                    or prior.row.get("expected_text") != row.get("expected_text") or not matches(old, prior.row)
                ):
                    where = "is absent at base" if old is None else "matches neither base nor the working tree"
                    report.unresolved.append(
                        f"{anchor.label} {path}:{recorded[0]}-{recorded[1]}: the file {where}, "
                        "and the recorded excerpt was found neither by digest nor through the base registry row"
                        if old is None else
                        f"{anchor.label} {path}:{recorded[0]}-{recorded[1]}: the recorded excerpt {where}, "
                        "and neither its digest nor a base registry row with this label resolves it"
                    )
                    continue
                base_row = prior.row
            if resolve_anchor(anchor, base_row, old, new, align, report):
                changed.add(id(row))
    reviews = registry.get("lean_reviews")
    for index, review in enumerate(reviews if isinstance(reviews, list) else []):
        context = review.get("context") if isinstance(review, dict) else None
        if not isinstance(context, dict) or not (id(review) in changed or id(context) in changed):
            continue
        if valid_range(review) and valid_range(context) and (
            context["line_start"] > review["line_start"] or context["line_end"] < review["line_end"]
        ):
            report.unresolved.append(f"lean_reviews[{index}] {review['path']}: context no longer contains the reviewed line")
    return report


def resolve_link(root: Path, link: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(link, dict) or not isinstance(link.get("path"), str) or unsafe_path(link["path"]):
        raise ReanchorError(f"patch artifact link needs a safe repository-relative path: {link!r}")
    if "find" not in link:
        return dict(link)
    lines = (root / link["path"]).read_text(encoding="utf-8").splitlines()
    hits = [number for number, text in enumerate(lines, 1) if link["find"] in text]
    if len(hits) != 1:
        raise ReanchorError(f"{link['path']}: find {link['find']!r} matched {len(hits)} lines")
    start = end = hits[0]
    span = link.get("span", "line")
    if span == "bibitem":
        end = next_boundary(lines, start) or len(lines)
    elif span != "line":
        raise ReanchorError(f"{link['path']}: unknown span {span!r}")
    row: dict[str, Any] = {"path": link["path"], "line_start": start, "line_end": end}
    if "expected_text" in link:
        if link["expected_text"] not in excerpt(lines, start, end):
            raise ReanchorError(f"{link['path']}:{start}-{end}: expected_text is absent from the resolved lines")
        row["expected_text"] = link["expected_text"]
    row["excerpt_sha256"] = sha(excerpt(lines, start, end))
    return row


def apply_patch(root: Path, registry: dict[str, Any], patches: Any) -> list[str]:
    if not isinstance(patches, list) or not all(isinstance(p, dict) and isinstance(p.get("id"), str) for p in patches):
        raise ReanchorError("--patch must be a JSON list of source rows with string ids")
    notes = []
    by_id = {source["id"]: source for source in registry["sources"] if isinstance(source, dict) and "id" in source}
    for patch in patches:
        links = [resolve_link(root, link) for link in patch.get("artifact_links", [])]
        if patch["id"] in by_id:
            target = by_id[patch["id"]]
            existing = {(l.get("path"), l.get("line_start"), l.get("line_end")) for l in target.get("artifact_links", [])}
            fresh = [l for l in links if (l["path"], l.get("line_start"), l.get("line_end")) not in existing]
            target.setdefault("artifact_links", []).extend(fresh)
            for name in PATCH_LIST_FIELDS:
                for item in patch.get(name, []):
                    if item not in target.setdefault(name, []):
                        target[name].append(item)
            if "relation" in patch:
                target["relation"] = patch["relation"]
            notes.append(f"extended {patch['id']} with {len(fresh)} new artifact links")
        else:
            row = {k: v for k, v in patch.items() if k != "artifact_links"}
            row["artifact_links"] = links
            ordered = {k: row[k] for k in FIELD_ORDER if k in row}
            ordered.update({k: v for k, v in row.items() if k not in ordered})
            registry["sources"].append(ordered)
            by_id[patch["id"]] = ordered
            notes.append(f"added {patch['id']} with {len(links)} artifact links")
    return notes


def write_registry(path: Path, text: str) -> None:
    if path.is_symlink():
        raise ReanchorError(f"refusing to write through a symbolic link: {path}")
    handle, temporary = tempfile.mkstemp(dir=path.parent, prefix=".source-attributions.", suffix=".tmp")
    try:
        with os.fdopen(handle, "w", encoding="utf-8", newline="") as stream:
            stream.write(text)
        os.chmod(temporary, stat.S_IMODE(path.stat().st_mode))
        os.replace(temporary, path)
    except BaseException:
        Path(temporary).unlink(missing_ok=True)
        raise


def describe(change: Change) -> str:
    (a, b), (c, d) = change.old, change.new
    return f"{change.label} {change.path}: {a}-{b} -> {c}-{d} [{change.rule}] {change.first_line.strip()[:80]}"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=ROOT, help="repository checkout (default: this clone)")
    parser.add_argument("--base", default="origin/main", help="git ref the recorded anchors were digested against")
    parser.add_argument("--write", action="store_true", help="save the registry when every anchor resolves")
    parser.add_argument("--patch", type=Path, help="JSON list of source rows to add or extend")
    parser.add_argument("--verbose", action="store_true", help="also list rows that only moved")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    registry_path = root / REGISTRY
    try:
        raw = registry_path.read_text(encoding="utf-8")
        registry = json.loads(raw)
        if not isinstance(registry, dict) or not isinstance(registry.get("sources"), list):
            raise ReanchorError(f"{REGISTRY} must be an object with a sources list")
        commit = resolve_base(root, args.base)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, ReanchorError) as exc:
        print(f"reanchor_source_attributions: {exc}", file=sys.stderr)
        return 2
    if serialise(registry) != raw:
        message = "registry does not round-trip byte-identically through json.dumps(indent=2, ensure_ascii=False)"
        if args.write:
            print(f"reanchor_source_attributions: {message}; refusing to write", file=sys.stderr)
            return 2
        print(f"warning: {message}; --write will refuse", file=sys.stderr)
    report = reanchor(root, commit, registry)
    try:
        notes = apply_patch(root, registry, json.loads(args.patch.read_text(encoding="utf-8"))) if args.patch else []
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, ReanchorError) as exc:
        print(f"reanchor_source_attributions: {exc}", file=sys.stderr)
        return 2
    print(f"base {args.base} ({commit[:12]}); registry {REGISTRY}")
    if args.verbose:
        for change in report.moved:
            print("moved", describe(change))
    for change in report.recomputed:
        print("recomputed", describe(change))
    for note in notes:
        print(note)
    for problem in report.unresolved:
        print("UNRESOLVED", problem)
    output = serialise(registry)
    print(
        f"current {report.current}, moved {len(report.moved)}, recomputed {len(report.recomputed)}, "
        f"unresolved {len(report.unresolved)}; registry {'changed' if output != raw else 'unchanged'}"
    )
    if report.unresolved:
        if args.write:
            print("not written: resolve the anchors above, then rerun")
        return 1
    if args.write and output != raw:
        try:
            write_registry(registry_path, output)
        except (OSError, ReanchorError) as exc:
            print(f"reanchor_source_attributions: {exc}", file=sys.stderr)
            return 2
        print("wrote", REGISTRY)
    elif output != raw:
        print("dry run; pass --write to save")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
