#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""The contrast ledger: distinctions this programme has read wrongly, each with
the evidence that exposes it and the places it must be applied.

The ledger lives at ``docs/research-commons/record/contrasts.json`` (schema
``plectis-contrast-ledger/1``). Each row names a distinction in one sentence,
the wrong and right readings, an evidence bundle, its provenance, the triggers
that make it relevant, and four uses: a packet obligation, a return gate, a
regression and an experiment.

``check`` confirms that the cited evidence is present:

* a ``source_span`` must exist in the file at the git ref (``HEAD`` by
  default), its lines must be in range, and every ``must_contain`` literal must
  lie inside the span;
* a ``declaration`` must appear in ``docs/declaration_atlas.json``
  (evidence class ``declaration_atlas_at_pin``) or in the Lean source of its
  module (``lean_source_at_ref``, or ``lean_source_worktree_uncommitted`` with a
  warning when the file is not yet committed);
* a ``relation`` id must appear in ``docs/research-commons/record/relations.json``
  when that file exists (evidence class ``recorded_relation``); a missing file
  is a warning.

The check reads bytes and names. It judges no mathematics. The atlas is a
navigation projection of the Lean source at the formal-source pin
(``projection_not_authority``): ``declaration_atlas_at_pin`` shows the name is
listed there and does not show that any CI job compiled its module. Kernel
acceptance comes from the pinned Lean build, and no field in this ledger
confers it.

``triggered`` and ``gate`` select the rows whose triggers match a problem, a
text or a declaration. The gate returns the sentences a return touching those
triggers must address. It flags; it never issues a verdict.

Standard library only.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]

SCHEMA = "plectis-contrast-ledger/1"
CHECK_SCHEMA = "plectis-contrast-ledger-check/1"
GATE_SCHEMA = "plectis-contrast-gate/1"
LEDGER_PATH = "docs/research-commons/record/contrasts.json"
ATLAS_PATH = "docs/declaration_atlas.json"
RELATIONS_PATH = "docs/research-commons/record/relations.json"

EVIDENCE_KINDS = ("source_span", "declaration", "relation")
PROVENANCE_KINDS = ("round", "return", "claim", "commit", "pull_request", "note")
ROW_FIELDS = ("id", "title", "distinction", "wrong_reading", "right_reading",
              "evidence", "provenance", "triggers", "uses")
TRIGGER_FIELDS = ("problems", "declarations", "phrases")
USE_FIELDS = ("packet_obligation", "return_gate", "regression", "experiment")
ROW_ID = re.compile(r"^[a-z0-9][a-z0-9-]*$")

EVIDENCE_BOUNDARY = (
    "This check reads bytes, declaration names and relation ids. It judges no "
    "mathematical reading. declaration_atlas_at_pin means the name is listed in "
    "the declaration atlas, a navigation projection of the Lean source at the "
    "formal-source pin; it does not show that any CI job compiled the module. "
    "Kernel acceptance comes from the pinned Lean build. No field of the ledger "
    "confers kernel authority.")
GATE_BOUNDARY = (
    "The gate flags the distinctions a return touching these triggers must "
    "address. It issues no verdict; a reviewer decides whether the return "
    "respects each one.")

# A Lean declaration header. Leading attributes and modifiers are optional.
DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped)[ \t]+)*"
    r"(?P<kw>theorem|lemma|def|abbrev|structure|inductive|instance|class|axiom|opaque)"
    r"[ \t]+(?P<name>[^\s:({\[]+)")
# Lines at or left of a declaration's indent that continue the same item.
CONTINUATION = ("|", "where", "termination_by", "decreasing_by", "deriving")


class LedgerError(ValueError):
    """The ledger or a source it cites cannot be read as required."""


class SourceError(LedgerError):
    """A cited file is missing at the requested ref or escapes the root."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, ensure_ascii=False,
                      separators=(",", ":"), allow_nan=False).encode("utf-8")


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_relative(path: str) -> str:
    """Return a normalised repository-relative POSIX path or raise."""
    if not isinstance(path, str) or not path.strip():
        raise SourceError("path must be a nonempty string")
    pure = PurePosixPath(path)
    if pure.is_absolute() or ".." in pure.parts or "\\" in path:
        raise SourceError(f"path must be relative and contained: {path}")
    return pure.as_posix()


@dataclass(frozen=True)
class Blob:
    path: str
    data: bytes
    binding: str  # git_ref | worktree | worktree_uncommitted

    @property
    def sha256(self) -> str:
        return sha256_hex(self.data)

    def lines(self) -> list[str]:
        return self.data.decode("utf-8").splitlines(keepends=True)


class SourceTree:
    """Read repository files at a git ref, or from the working tree.

    With ``ref`` set, a file absent at the ref raises unless
    ``allow_uncommitted`` is true, in which case the working-tree bytes are
    returned with binding ``worktree_uncommitted``. With ``ref=None`` every read
    comes from the working tree (binding ``worktree``).
    """

    def __init__(self, root: Path | str, ref: str | None = "HEAD",
                 allow_uncommitted: bool = False) -> None:
        self.root = Path(root).resolve()
        self.ref = ref
        self.allow_uncommitted = allow_uncommitted
        self.commit: str | None = None
        self._cache: dict[str, Blob | None] = {}
        if ref is not None:
            result = self._git("rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}")
            if result.returncode != 0:
                raise SourceError(f"cannot resolve git ref {ref!r} under {self.root}")
            self.commit = result.stdout.decode("ascii").strip()

    def _git(self, *args: str) -> subprocess.CompletedProcess:
        try:
            return subprocess.run(["git", "-C", str(self.root), *args],
                                  capture_output=True, check=False)
        except OSError as exc:
            raise SourceError(f"git is unavailable: {exc}") from exc

    def _worktree(self, rel: str) -> bytes | None:
        path = (self.root / rel).resolve()
        if not path.is_relative_to(self.root):
            raise SourceError(f"path escapes the root through a link: {rel}")
        if not path.is_file():
            return None
        return path.read_bytes()

    def find(self, path: str) -> Blob | None:
        rel = safe_relative(path)
        if rel in self._cache:
            return self._cache[rel]
        blob: Blob | None = None
        if self.ref is None:
            data = self._worktree(rel)
            blob = None if data is None else Blob(rel, data, "worktree")
        else:
            result = self._git("cat-file", "blob", f"{self.commit}:{rel}")
            if result.returncode == 0:
                blob = Blob(rel, result.stdout, "git_ref")
            elif self.allow_uncommitted:
                data = self._worktree(rel)
                blob = None if data is None else Blob(rel, data, "worktree_uncommitted")
        self._cache[rel] = blob
        return blob

    def find_or_uncommitted(self, path: str) -> Blob | None:
        """Like ``find``, falling back to working-tree bytes labelled ``worktree_uncommitted``.

        Used where presence in the working tree is a weaker, still reportable
        class of evidence (declaration names, the atlas, the relations record).
        """
        blob = self.find(path)
        if blob is None and self.ref is not None:
            data = self._worktree(safe_relative(path))
            blob = None if data is None else Blob(safe_relative(path), data, "worktree_uncommitted")
        return blob

    def read(self, path: str) -> Blob:
        blob = self.find(path)
        if blob is None:
            where = "the working tree" if self.ref is None else f"git ref {self.ref}"
            raise SourceError(f"{path} is absent at {where}")
        return blob

    def describe(self) -> dict[str, Any]:
        return {"ref": self.ref, "commit": self.commit,
                "allow_uncommitted": self.allow_uncommitted}


def span_text(blob: Blob, start: int, end: int) -> str:
    lines = blob.lines()
    if not isinstance(start, int) or not isinstance(end, int) or isinstance(start, bool) \
            or isinstance(end, bool):
        raise LedgerError("start_line and end_line must be integers")
    if start < 1 or end < start or end > len(lines):
        raise LedgerError(f"invalid line range {start}-{end} for {blob.path} "
                          f"({len(lines)} lines)")
    return "".join(lines[start - 1:end])


def missing_literals(text: str, literals: Sequence[str]) -> list[str]:
    return [literal for literal in literals if literal not in text]


def short_name(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def names_agree(declared: str, wanted: str) -> bool:
    """A declared token and a cited name agree up to a namespace prefix."""
    if declared == wanted:
        return True
    return declared.endswith("." + wanted) or wanted.endswith("." + declared)


def declaration_lines(lines: Sequence[str], name: str) -> list[int]:
    """1-based lines whose declaration header declares ``name``."""
    found = []
    for index, line in enumerate(lines, start=1):
        match = DECL_RE.match(line)
        if match and names_agree(match.group("name"), name):
            found.append(index)
    return found


def declaration_span(lines: Sequence[str], line: int, max_lines: int = 80) -> tuple[int, int, bool]:
    """Span of the declaration whose header is at ``line`` (1-based).

    The span starts at an attached docstring or attribute block and ends before
    the next item at the same or a lesser indent. It is capped at ``max_lines``
    lines from the header; the third value reports whether the cap applied.
    """
    if line < 1 or line > len(lines):
        raise LedgerError(f"declaration line {line} is out of range")
    header = lines[line - 1]
    indent = len(header) - len(header.lstrip(" \t"))
    start = line
    probe = line - 1
    while probe >= 1:
        text = lines[probe - 1].strip()
        if text.startswith("@["):
            start = probe
            probe -= 1
            continue
        if text.endswith("-/"):
            opener = probe
            while opener >= 1 and not lines[opener - 1].lstrip().startswith("/-"):
                opener -= 1
            if opener >= 1 and lines[opener - 1].lstrip().startswith("/--") \
                    and line - opener <= 200:
                start = opener
                probe = opener - 1
                continue
        break
    end = len(lines)
    for index in range(line + 1, len(lines) + 1):
        raw = lines[index - 1]
        text = raw.strip()
        if not text:
            continue
        this_indent = len(raw) - len(raw.lstrip(" \t"))
        if this_indent <= indent and not text.startswith(CONTINUATION):
            end = index - 1
            break
    while end > line and not lines[end - 1].strip():
        end -= 1
    capped = end - line + 1 > max_lines
    if capped:
        end = line + max_lines - 1
    return start, end, capped


class DeclarationIndex:
    """Resolve declaration names through the atlas, then the Lean source."""

    def __init__(self, tree: SourceTree, atlas_path: str = ATLAS_PATH) -> None:
        self.tree = tree
        self.atlas_path = atlas_path
        self._loaded = False
        self._by_short: dict[str, list[dict[str, Any]]] = {}
        self.atlas_info: dict[str, Any] = {"path": atlas_path, "present": False}

    def _load(self) -> None:
        if self._loaded:
            return
        self._loaded = True
        blob = self.tree.find_or_uncommitted(self.atlas_path)
        if blob is None:
            return
        document = json.loads(blob.data.decode("utf-8"))
        self.atlas_info = {"path": self.atlas_path, "present": True, "binding": blob.binding,
                           "sha256": blob.sha256,
                           "source_fingerprint": document.get("source_fingerprint")}
        for row in document.get("declarations", []):
            name = row.get("name")
            if isinstance(name, str):
                self._by_short.setdefault(short_name(name), []).append(row)

    def atlas_rows(self, name: str, module: str | None = None) -> list[dict[str, Any]]:
        self._load()
        rows = [row for row in self._by_short.get(short_name(name), [])
                if names_agree(row["name"], name)]
        if module is not None:
            rows = [row for row in rows if row.get("module") == module]
        return sorted(rows, key=lambda row: (row.get("module", ""), row.get("line", 0)))

    def resolve(self, name: str, module: str | None) -> dict[str, Any]:
        """Locate a declaration. Returns a result dict; ``found`` says whether it exists."""
        if not isinstance(name, str) or not name:
            return {"found": False, "errors": ["declaration name must be a nonempty string"]}
        result: dict[str, Any] = {"name": name, "module": module, "found": False,
                                  "errors": [], "warnings": []}
        atlas = self.atlas_rows(name, module)
        elsewhere = [] if atlas or module is None else self.atlas_rows(name)
        source_line = None
        blob = None
        if module is not None:
            try:
                blob = self.tree.find_or_uncommitted(module)
            except SourceError as exc:
                result["errors"].append(str(exc))
            if blob is not None:
                lines = blob.lines()
                hits = declaration_lines(lines, name)
                if atlas:
                    wanted = atlas[0].get("line")
                    if wanted in hits:
                        source_line = wanted
                    elif hits:
                        source_line = hits[0]
                        result["warnings"].append(
                            f"atlas line {wanted} for {name} differs from the source at the ref; "
                            f"using line {source_line}")
                elif hits:
                    source_line = hits[0]
                result["binding"] = blob.binding
                result["file_sha256"] = blob.sha256
        if atlas:
            result.update(found=True, evidence_class="declaration_atlas_at_pin",
                          module=atlas[0].get("module"), atlas_line=atlas[0].get("line"),
                          claim_ids=atlas[0].get("claim_ids", []))
        elif source_line is not None:
            uncommitted = result.get("binding") == "worktree_uncommitted"
            result.update(found=True, evidence_class=(
                "lean_source_worktree_uncommitted" if uncommitted else
                "lean_source_worktree" if result.get("binding") == "worktree" else
                "lean_source_at_ref"))
            if uncommitted:
                result["warnings"].append(
                    f"{name} is found only in the uncommitted working tree of {module}")
        else:
            if elsewhere:
                result["errors"].append(
                    f"{name} is listed in the atlas only under "
                    f"{sorted({row.get('module') for row in elsewhere})}; the ledger cites {module}")
            else:
                result["errors"].append(f"declaration {name} is absent from the atlas and from "
                                        f"the Lean source of {module}")
        if source_line is not None:
            result["line"] = source_line
        elif atlas:
            result["line"] = atlas[0].get("line")
        return result


def load_relation_ids(tree: SourceTree, path: str = RELATIONS_PATH) -> tuple[set[str] | None, dict[str, Any], dict[str, dict]]:
    """Relation ids from the relations record, or ``None`` when the file is absent.

    Accepts a top-level list or an object with ``relations`` or ``rows``.
    """
    blob = tree.find_or_uncommitted(path)
    if blob is None:
        return None, {"path": path, "present": False}, {}
    document = json.loads(blob.data.decode("utf-8"))
    rows = document if isinstance(document, list) else (
        document.get("relations") or document.get("rows") or [])
    by_id = {row["id"]: row for row in rows
             if isinstance(row, Mapping) and isinstance(row.get("id"), str)}
    info = {"path": path, "present": True, "binding": blob.binding, "sha256": blob.sha256,
            "schema": document.get("schema") if isinstance(document, Mapping) else None}
    return set(by_id), info, by_id


def load_ledger(path: Path | str) -> dict[str, Any]:
    try:
        document = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise LedgerError(f"cannot read ledger {path}: {exc}") from exc
    if not isinstance(document, Mapping):
        raise LedgerError("ledger must be a JSON object")
    return dict(document)


def _nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def shape_errors(document: Mapping[str, Any]) -> list[str]:
    """Structural errors in a ledger document, without reading any source."""
    errors: list[str] = []
    if document.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA!r}")
    rows = document.get("rows")
    if not isinstance(rows, list) or not rows:
        return errors + ["rows must be a nonempty list"]
    seen: set[str] = set()
    for index, row in enumerate(rows):
        where = f"rows[{index}]"
        if not isinstance(row, Mapping):
            errors.append(f"{where} must be an object")
            continue
        row_id = row.get("id")
        if not isinstance(row_id, str) or not ROW_ID.match(row_id):
            errors.append(f"{where}.id must match {ROW_ID.pattern}")
        elif row_id in seen:
            errors.append(f"duplicate row id {row_id}")
        else:
            seen.add(row_id)
            where = row_id
        extra = sorted(set(row) - set(ROW_FIELDS))
        if extra:
            errors.append(f"{where} has unknown fields {extra}")
        for field in ("title", "distinction", "wrong_reading", "right_reading"):
            if not _nonempty_string(row.get(field)):
                errors.append(f"{where}.{field} must be a nonempty string")
        evidence = row.get("evidence")
        if not isinstance(evidence, list) or not evidence:
            errors.append(f"{where}.evidence must be a nonempty list")
            evidence = []
        for position, item in enumerate(evidence):
            errors.extend(_evidence_shape_errors(f"{where}.evidence[{position}]", item))
        provenance = row.get("provenance")
        if not isinstance(provenance, list) or not provenance:
            errors.append(f"{where}.provenance must be a nonempty list")
            provenance = []
        for position, item in enumerate(provenance):
            if not isinstance(item, Mapping) or item.get("kind") not in PROVENANCE_KINDS \
                    or not _nonempty_string(item.get("ref")) \
                    or not _nonempty_string(item.get("detail")):
                errors.append(f"{where}.provenance[{position}] needs kind in {PROVENANCE_KINDS}, "
                              "ref and detail")
        triggers = row.get("triggers")
        if not isinstance(triggers, Mapping) or set(triggers) != set(TRIGGER_FIELDS):
            errors.append(f"{where}.triggers must have exactly {TRIGGER_FIELDS}")
        else:
            problems = triggers["problems"]
            if not isinstance(problems, list) or any(
                    not isinstance(p, int) or isinstance(p, bool) or p <= 0 for p in problems):
                errors.append(f"{where}.triggers.problems must be positive integers")
            for field in ("declarations", "phrases"):
                values = triggers[field]
                if not isinstance(values, list) or any(not _nonempty_string(v) for v in values):
                    errors.append(f"{where}.triggers.{field} must be nonempty strings")
            if not any(isinstance(triggers[f], list) and triggers[f] for f in TRIGGER_FIELDS):
                errors.append(f"{where}.triggers must name at least one problem, declaration or phrase")
        uses = row.get("uses")
        if not isinstance(uses, Mapping) or set(uses) != set(USE_FIELDS):
            errors.append(f"{where}.uses must have exactly {USE_FIELDS}")
        else:
            if not isinstance(uses["packet_obligation"], bool):
                errors.append(f"{where}.uses.packet_obligation must be true or false")
            if not _nonempty_string(uses["return_gate"]):
                errors.append(f"{where}.uses.return_gate must be a nonempty sentence")
            for field in ("regression", "experiment"):
                if uses[field] is not None and not _nonempty_string(uses[field]):
                    errors.append(f"{where}.uses.{field} must be a nonempty string or null")
    return errors


def _evidence_shape_errors(where: str, item: Any) -> list[str]:
    if not isinstance(item, Mapping):
        return [f"{where} must be an object"]
    kind = item.get("kind")
    if kind == "source_span":
        errors = []
        if set(item) != {"kind", "path", "start_line", "end_line", "must_contain"}:
            errors.append(f"{where} source_span needs exactly kind, path, start_line, end_line, "
                          "must_contain")
        literals = item.get("must_contain")
        if not isinstance(literals, list) or not literals or any(
                not _nonempty_string(v) for v in literals):
            errors.append(f"{where}.must_contain must be a nonempty list of nonempty strings")
        return errors
    if kind == "declaration":
        if set(item) != {"kind", "name", "module"} or not _nonempty_string(item.get("name")) \
                or not _nonempty_string(item.get("module")):
            return [f"{where} declaration needs exactly kind, name and module"]
        return []
    if kind == "relation":
        if set(item) != {"kind", "id"} or not _nonempty_string(item.get("id")):
            return [f"{where} relation needs exactly kind and id"]
        return []
    return [f"{where}.kind must be one of {EVIDENCE_KINDS}"]


def check_evidence(item: Mapping[str, Any], tree: SourceTree, index: DeclarationIndex,
                   relation_ids: set[str] | None) -> dict[str, Any]:
    """Check one evidence item. The result carries ``status`` and ``evidence_class``."""
    kind = item.get("kind")
    out: dict[str, Any] = {"kind": kind, "errors": [], "warnings": []}
    if kind == "source_span":
        out.update(path=item.get("path"), start_line=item.get("start_line"),
                   end_line=item.get("end_line"))
        try:
            blob = tree.read(item["path"])
            text = span_text(blob, item["start_line"], item["end_line"])
        except (LedgerError, UnicodeDecodeError) as exc:
            out["errors"].append(str(exc))
        else:
            out.update(file_sha256=blob.sha256, binding=blob.binding,
                       evidence_class="source_span_bound_to_file_hash")
            if blob.binding == "worktree_uncommitted":
                out["warnings"].append(f"{blob.path} is not committed at {tree.ref}")
            missing = missing_literals(text, item.get("must_contain", []))
            if missing:
                out["errors"].append(f"literals outside the span {item['path']}:"
                                     f"{item['start_line']}-{item['end_line']}: {missing}")
    elif kind == "declaration":
        found = index.resolve(item.get("name"), item.get("module"))
        out.update(name=item.get("name"), module=found.get("module", item.get("module")))
        for key in ("evidence_class", "line", "binding", "file_sha256", "claim_ids"):
            if key in found:
                out[key] = found[key]
        out["errors"].extend(found.get("errors", []))
        out["warnings"].extend(found.get("warnings", []))
    elif kind == "relation":
        out["id"] = item.get("id")
        if relation_ids is None:
            out["warnings"].append(f"{RELATIONS_PATH} is absent; relation {item.get('id')} "
                                   "was not checked")
            out["evidence_class"] = "relation_unchecked"
        elif item.get("id") in relation_ids:
            out["evidence_class"] = "recorded_relation"
        else:
            out["errors"].append(f"relation id {item.get('id')} is absent from {RELATIONS_PATH}")
    else:
        out["errors"].append(f"unknown evidence kind {kind!r}")
    out["status"] = "error" if out["errors"] else "ok"
    return out


def check(root: Path | str = ROOT, ledger_path: str = LEDGER_PATH, ref: str | None = "HEAD",
          allow_uncommitted: bool = False, tree: SourceTree | None = None,
          index: DeclarationIndex | None = None) -> dict[str, Any]:
    """Check the ledger against the repository. ``ok`` is false on any error."""
    root = Path(root).resolve()
    tree = tree or SourceTree(root, ref=ref, allow_uncommitted=allow_uncommitted)
    index = index or DeclarationIndex(tree)
    ledger_file = root / ledger_path
    document = load_ledger(ledger_file)
    errors = shape_errors(document)
    warnings: list[str] = []
    relation_ids, relations_info, _ = load_relation_ids(tree)
    if relation_ids is None:
        warnings.append(f"{RELATIONS_PATH} is absent; relation evidence was not checked")
    elif relations_info.get("binding") == "worktree_uncommitted":
        warnings.append(f"{RELATIONS_PATH} is read from the uncommitted working tree")
    rows_out = []
    if not errors:
        for row in document["rows"]:
            results = [check_evidence(item, tree, index, relation_ids) for item in row["evidence"]]
            for result in results:
                errors.extend(f"{row['id']}: {message}" for message in result["errors"])
                warnings.extend(f"{row['id']}: {message}" for message in result["warnings"])
            rows_out.append({"id": row["id"], "evidence": results})
    return {
        "schema": CHECK_SCHEMA,
        "ledger": ledger_path,
        "ledger_sha256": sha256_hex(ledger_file.read_bytes()),
        "source": tree.describe(),
        "atlas": index.atlas_info,
        "relations": relations_info,
        "ok": not errors,
        "errors": sorted(set(errors)),
        "warnings": sorted(set(warnings)),
        "rows": rows_out,
        "evidence_boundary": EVIDENCE_BOUNDARY,
    }


def _normalise(text: str) -> str:
    return " ".join(text.casefold().split())


def _mentions(text: str, name: str) -> bool:
    pattern = r"(?<![\w.'])(?:[\w']+\.)*" + re.escape(short_name(name)) + r"(?![\w'])"
    for match in re.finditer(pattern, text):
        if names_agree(match.group(0), name):
            return True
    return False


def triggered(rows: Iterable[Mapping[str, Any]], problem: int | None = None,
              text: str | None = None, declarations: Sequence[str] = ()) -> list[dict[str, Any]]:
    """Rows whose triggers match, each with the matches that selected it.

    A row matches on its problem number, on a declaration named in
    ``declarations`` or mentioned in ``text``, or on a phrase found in ``text``
    (case and spacing ignored). Nothing supplied matches nothing.
    """
    normalised = _normalise(text) if text else ""
    out = []
    for row in rows:
        trig = row.get("triggers", {})
        matched: list[dict[str, Any]] = []
        if problem is not None and problem in trig.get("problems", []):
            matched.append({"on": "problem", "value": problem})
        for name in trig.get("declarations", []):
            if any(names_agree(given, name) for given in declarations):
                matched.append({"on": "declaration", "value": name})
            elif text and _mentions(text, name):
                matched.append({"on": "declaration_in_text", "value": name})
        if normalised:
            for phrase in trig.get("phrases", []):
                if _normalise(phrase) in normalised:
                    matched.append({"on": "phrase", "value": phrase})
        if matched:
            out.append({"id": row["id"], "title": row["title"],
                        "packet_obligation": row["uses"]["packet_obligation"],
                        "return_gate": row["uses"]["return_gate"], "matched_on": matched})
    return sorted(out, key=lambda entry: entry["id"])


def gate(rows: Iterable[Mapping[str, Any]], text: str, problems: Sequence[int] = ()) -> dict[str, Any]:
    """The distinctions a return touching these triggers must address. Flags only."""
    rows = list(rows)
    found: dict[str, dict[str, Any]] = {}
    for problem in list(problems) or [None]:
        for entry in triggered(rows, problem=problem, text=text):
            previous = found.get(entry["id"])
            if previous is None:
                found[entry["id"]] = entry
            else:
                seen = {json.dumps(m, sort_keys=True) for m in previous["matched_on"]}
                previous["matched_on"].extend(
                    m for m in entry["matched_on"] if json.dumps(m, sort_keys=True) not in seen)
    flags = [{"id": key, "title": value["title"], "must_address": value["return_gate"],
              "matched_on": value["matched_on"]} for key, value in sorted(found.items())]
    return {"schema": GATE_SCHEMA, "evidence_class": "authored_review", "verdict": None,
            "flags": flags, "evidence_boundary": GATE_BOUNDARY}


def _print(value: Any) -> None:
    sys.stdout.write(json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check and query the contrast ledger of distinctions this programme has read "
                    "wrongly. Output states its evidence class; nothing here is a proof.")
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root")
    parser.add_argument("--ledger", default=LEDGER_PATH, help="ledger path relative to the root")
    sub = parser.add_subparsers(dest="command", required=True)
    check_parser = sub.add_parser("check", help="confirm every cited span, declaration and relation")
    check_parser.add_argument("--ref", default="HEAD",
                              help="git ref whose bytes are checked (default HEAD)")
    check_parser.add_argument("--worktree", action="store_true",
                              help="read the working tree instead of a git ref")
    check_parser.add_argument("--allow-uncommitted", action="store_true",
                              help="accept files absent at the ref from the working tree, with a warning")
    sub.add_parser("list", help="list rows with their triggers and uses")
    trig = sub.add_parser("triggered", help="rows whose triggers match, with their return gates")
    trig.add_argument("--problem", type=int)
    trig.add_argument("--text", type=Path, help="file whose text is matched against phrases")
    trig.add_argument("--declaration", action="append", default=[])
    args = parser.parse_args(argv)
    try:
        if args.command == "check":
            report = check(args.root, args.ledger, ref=None if args.worktree else args.ref,
                           allow_uncommitted=args.allow_uncommitted)
            _print(report)
            return 0 if report["ok"] else 1
        document = load_ledger(Path(args.root) / args.ledger)
        errors = shape_errors(document)
        if errors:
            _print({"ok": False, "errors": errors})
            return 1
        rows = document["rows"]
        if args.command == "list":
            _print({"schema": SCHEMA, "evidence_class": "authored_review",
                    "rows": [{"id": row["id"], "title": row["title"],
                              "distinction": row["distinction"], "triggers": row["triggers"],
                              "uses": row["uses"]} for row in rows]})
            return 0
        text = args.text.read_text(encoding="utf-8") if args.text else None
        matches = triggered(rows, problem=args.problem, text=text, declarations=args.declaration)
        _print({"schema": GATE_SCHEMA, "evidence_class": "authored_review", "verdict": None,
                "matches": matches, "evidence_boundary": GATE_BOUNDARY})
        return 0
    except (LedgerError, OSError, json.JSONDecodeError) as exc:
        sys.stderr.write(f"contrast_ledger: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
