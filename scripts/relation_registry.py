#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Relation rows between statements, attested against the declaration atlas.

``docs/research-commons/record/relations.json`` records how two statements
compare inside one context: equivalent, an endpoint route, a slot replacement,
strictly stronger, a separator, or a single statement refuted, feasible or
supplied. The vocabulary is the one fixed in
``lean/ErdosProblems/ArgumentGraph/Contracts.lean``; the left and right fields
follow the argument order of the Lean structure after the context ``Γ``:

* ``equivalent``: ``Equivalent Γ left right``, entailment both ways.
* ``endpoint_route``: ``EndpointRoute Γ left right``, ``left`` gives the endpoint ``right``.
* ``slot_replacement``: ``SlotReplacement Γ left right``, the replacement ``right``
  reconstructs the hypothesis ``left``. It never counts as weakening ``left``.
* ``strictly_stronger``: ``StrictlyStronger Γ left right``, ``left`` gives ``right``
  and a separator shows ``right`` does not give ``left``.
* ``separates``: ``Separates Γ left right``, some context value satisfies ``left``
  and fails ``right``.
* ``refuted``, ``feasible``, ``supplied``: one statement ``left``; ``right`` is null.

Each row names a certificate declaration. A row is ``attested`` when that
declaration is listed in ``docs/declaration_atlas.json`` in the named module,
the sha256 of the atlas signature equals the recorded ``signature_sha256``, the
head of the signature's type is the Contracts structure for the relation, and
the module is a compiled target: ``research_record.compiled_modules`` reaches it
from the default build roots or the coverage-build targets. The atlas is a
navigation projection of the Lean source at the formal-source pin
(``projection_not_authority``); a listing shows the name exists in that source
and does not show that CI compiled the module. The evidence class of an
attested row is ``declaration_atlas_at_pin``, and every atlas-listed row
reports ``compiled_target``. A row whose listing and hash match but whose
module no CI job compiles is ``listed_not_compiled`` and fails the check. The
reading of ``left`` and ``right`` stays the registry author's transcription,
bound to the declaration by the signature hash. A declaration absent from the
atlas is ``pending_pin`` (it may exist in ``lean/`` ahead of the pin; the check
reports whether its source is present); anything else is ``mismatch`` and
fails the check. No field of a row confers kernel authority by itself.

Kernel-probe verdicts from ``docs/residualbench_report.json`` can be loaded as
computed rows with evidence class ``kernel_probe_verdict``; they are never
written into the registry.

Accounting works over usable rows only: equivalence classes by union-find over
equivalent rows, and transport, in which supply moves forward along an
entailment and refutation moves backward. Outcomes, costs and failed attempts
never transport; a failed or timed-out search is ``unknown``.

Standard library only.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import tempfile
from collections import defaultdict, deque
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
REGISTRY_PATH = "docs/research-commons/record/relations.json"
ATLAS_PATH = "docs/declaration_atlas.json"
RESIDUALBENCH_PATH = "docs/residualbench_report.json"
SCHEMA = "plectis-relation-registry/1"

EVIDENCE_ATTESTED = "declaration_atlas_at_pin"
EVIDENCE_PROBE = "kernel_probe_verdict"
EVIDENCE_REPORTED = "reported"
EVIDENCE_BOUNDARY = (
    "attested rows carry declaration_atlas_at_pin and a compiled target. The atlas is a navigation "
    "projection of the Lean source at the formal-source pin: a listing shows the name exists there and "
    "does not show that CI compiled the module, so a listed row whose module no default build root or "
    "coverage-build target reaches is listed_not_compiled and fails. pending_pin rows are reported "
    "transcriptions whose certificate is not yet in the pinned atlas.")
FAILING_STATES = frozenset({"mismatch", "listed_not_compiled"})

# Relation name -> the Contracts structure its certificate type must be headed by.
RELATIONS: dict[str, str] = {
    "equivalent": "Equivalent",
    "endpoint_route": "EndpointRoute",
    "slot_replacement": "SlotReplacement",
    "strictly_stronger": "StrictlyStronger",
    "separates": "Separates",
    "refuted": "Refuted",
    "feasible": "Feasible",
    "supplied": "Supplied",
}
UNARY = frozenset({"refuted", "feasible", "supplied"})
ROW_FIELDS = frozenset({"id", "relation", "problem", "left", "right", "context",
                        "certificate", "sources", "note"})
CERTIFICATE_FIELDS = frozenset({"declaration", "module", "signature_sha256"})
SOURCE_FIELDS = frozenset({"declaration", "module"})
TOP_FIELDS = frozenset({"schema", "boundary", "rows"})
ROW_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.:-]*\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
TRANSPORT_MODES = ("supplied", "refuted")

DIRECTION = {
    "equivalent": "left <-> right in context",
    "endpoint_route": "left -> right (right is the endpoint)",
    "slot_replacement": "right -> left (the replacement reconstructs the hypothesis; never a weakening)",
    "strictly_stronger": "left -> right, and a separator shows right does not give left",
    "separates": "left does not give right (a context value satisfies left and fails right)",
    "refuted": "left is refuted in context",
    "feasible": "left is satisfiable in context",
    "supplied": "left holds throughout context",
    "unknown": "no relation decided (a failed or timed-out search reads unknown)",
}


class RegistryError(ValueError):
    """A schema or consistency error in the registry."""


class TransportRefused(ValueError):
    """Raised when a caller asks to move anything other than supply or refutation."""


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


# --------------------------------------------------------------------------
# Lean source reading: namespaces and declarations, comments removed.
# --------------------------------------------------------------------------

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+"
    r"([^\s:({\[⦃]+)")
NAMESPACE_RE = re.compile(r"^\s*namespace\s+(\S+)\s*$")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+(\S+))?\s*$")


def strip_lean_comments(text: str) -> str:
    """Remove line comments and (nested) block comments, keeping line breaks."""
    out: list[str] = []
    depth = 0
    i, n = 0, len(text)
    in_string = False
    while i < n:
        ch = text[i]
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            if ch == "\n":
                out.append("\n")
            i += 1
            continue
        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if ch == '"':
            in_string = True
        out.append(ch)
        i += 1
    return "".join(out)


def lean_declarations(text: str) -> list[dict[str, Any]]:
    """Every declaration in a Lean file with its full name, kind and line."""
    stack: list[tuple[str, str]] = []  # (kind, name)
    found: list[dict[str, Any]] = []
    for number, line in enumerate(strip_lean_comments(text).splitlines(), 1):
        m = NAMESPACE_RE.match(line)
        if m:
            stack.append(("namespace", m.group(1)))
            continue
        m = SECTION_RE.match(line)
        if m:
            stack.append(("section", m.group(1) or ""))
            continue
        m = END_RE.match(line)
        if m:
            name = m.group(1) or ""
            for index in range(len(stack) - 1, -1, -1):
                if stack[index][1] == name:
                    del stack[index:]
                    break
            continue
        m = DECL_RE.match(line)
        if m:
            short = m.group(2)
            if short.startswith("_root_."):
                full = short[len("_root_."):]
            else:
                prefix = ".".join(name for kind, name in stack if kind == "namespace")
                full = f"{prefix}.{short}" if prefix else short
            found.append({"kind": m.group(1), "short": short, "full": full, "line": number})
    return found


def normalise_module(module: str | None) -> str | None:
    """Accept ``A.B.C``, ``A/B/C.lean`` or ``lean/A/B/C.lean``; return ``lean/A/B/C.lean``."""
    if not module:
        return None
    module = module.strip()
    if module.endswith(".lean"):
        path = module
    else:
        path = module.replace(".", "/") + ".lean"
    if not path.startswith("lean/"):
        path = "lean/" + path
    return path


class LeanSource:
    """Read-only view of the Lean tree under ``root/lean``; caches parsed files."""

    def __init__(self, root: Path):
        self.root = Path(root)
        self._files: dict[str, list[dict[str, Any]] | None] = {}

    def declarations(self, module_path: str) -> list[dict[str, Any]] | None:
        if module_path not in self._files:
            path = self.root / module_path
            if not path.is_file():
                self._files[module_path] = None
            else:
                self._files[module_path] = lean_declarations(path.read_text(encoding="utf-8"))
        return self._files[module_path]

    def full_names(self, module_path: str) -> set[str] | None:
        decls = self.declarations(module_path)
        return None if decls is None else {d["full"] for d in decls}

    def find_theorem(self, short: str) -> list[str]:
        """Files under lean/ that contain ``theorem <short>`` as text."""
        pattern = re.compile(r"\btheorem\s+" + re.escape(short) + r"(?![\w'.])")
        hits = []
        base = self.root / "lean"
        if not base.is_dir():
            return hits
        for path in sorted(base.rglob("*.lean")):
            if ".lake" in path.parts:
                continue
            try:
                if pattern.search(path.read_text(encoding="utf-8")):
                    hits.append(path.relative_to(self.root).as_posix())
            except (OSError, UnicodeDecodeError):
                continue
        return hits


# --------------------------------------------------------------------------
# Declaration atlas lookup.
# --------------------------------------------------------------------------

class Atlas:
    """Index over ``docs/declaration_atlas.json`` (names there are namespace-relative)."""

    def __init__(self, payload: dict[str, Any] | None, source: LeanSource | None = None):
        self.present = payload is not None
        self.fingerprint = (payload or {}).get("source_fingerprint")
        self.by_tail: dict[str, list[dict[str, Any]]] = defaultdict(list)
        self.source = source
        for row in (payload or {}).get("declarations", []):
            name = row.get("name")
            if isinstance(name, str):
                self.by_tail[name.split(".")[-1]].append(row)

    @classmethod
    def load(cls, root: Path, source: LeanSource | None = None) -> "Atlas":
        path = Path(root) / ATLAS_PATH
        if not path.is_file():
            return cls(None, source)
        return cls(json.loads(path.read_text(encoding="utf-8")), source)

    def resolve(self, declaration: str, module: str | None = None) -> dict[str, Any]:
        """Find the atlas row for a full or short name, optionally within a module.

        Returns ``{"state": "found"|"absent"|"ambiguous"|"no_atlas", ...}``.
        When the Lean source of a candidate module is present its namespaces are
        read so a full name must match exactly; otherwise the match is by suffix.
        """
        if not self.present:
            return {"state": "no_atlas", "candidates": []}
        module_path = normalise_module(module)
        tail = declaration.split(".")[-1]
        candidates = []
        for row in self.by_tail.get(tail, []):
            name = row["name"]
            if not (declaration == name or declaration.endswith("." + name) or name.endswith("." + declaration)):
                continue
            if module_path and row.get("module") != module_path:
                continue
            candidates.append(row)
        exact = []
        namespace_checked = False
        if "." in declaration and self.source is not None:
            for row in candidates:
                names = self.source.full_names(row["module"])
                if names is None:
                    continue
                namespace_checked = True
                if declaration in names:
                    exact.append(row)
            if namespace_checked:
                # An exact namespace match wins; otherwise rows whose file could not
                # be read remain as suffix matches.
                unread = [r for r in candidates if self.source.full_names(r["module"]) is None]
                candidates = exact or unread
        if not candidates:
            return {"state": "absent", "candidates": [], "namespace_checked": namespace_checked}
        if len(candidates) > 1:
            return {"state": "ambiguous", "candidates": [c["id"] for c in candidates],
                    "namespace_checked": namespace_checked}
        return {"state": "found", "row": candidates[0], "namespace_checked": namespace_checked,
                "candidates": [candidates[0]["id"]]}


def type_head(signature: str) -> str | None:
    """The last component of the head identifier of a signature's type, or None."""
    depth = 0
    openers, closers = "([{⦃⟨", ")]}⦄⟩"
    colon = None
    for index, ch in enumerate(signature):
        if ch in openers:
            depth += 1
        elif ch in closers:
            depth -= 1
        elif ch == ":" and depth == 0:
            if signature[index + 1:index + 2] == "=" or signature[index - 1:index] == ":":
                continue
            colon = index
            break
    if colon is None:
        return None
    body = signature[colon + 1:].strip()
    m = re.match(r"([^\s()\[\]{}⦃⦄⟨⟩,]+)", body)
    if not m:
        return None
    token = m.group(1)
    if token in {"∀", "∃", "fun", "λ", "¬"}:
        return None
    return token.split(".")[-1]


# --------------------------------------------------------------------------
# Registry loading, schema and attestation.
# --------------------------------------------------------------------------

def _string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def schema_errors(document: Any) -> list[str]:
    errors: list[str] = []
    if not isinstance(document, dict):
        return ["registry must be a JSON object"]
    extra = set(document) - TOP_FIELDS
    if extra:
        errors.append(f"unknown top-level fields: {sorted(extra)}")
    if document.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA!r}")
    rows = document.get("rows")
    if not isinstance(rows, list):
        return errors + ["rows must be a list"]
    seen: set[str] = set()
    for index, row in enumerate(rows):
        where = f"rows[{index}]"
        if not isinstance(row, dict):
            errors.append(f"{where}: must be an object")
            continue
        rid = row.get("id")
        where = f"row {rid!r}" if isinstance(rid, str) else where
        missing = ROW_FIELDS - set(row)
        extra = set(row) - ROW_FIELDS
        if missing:
            errors.append(f"{where}: missing fields {sorted(missing)}")
        if extra:
            errors.append(f"{where}: unknown fields {sorted(extra)} (no row field confers authority)")
        if not isinstance(rid, str) or not ROW_ID.match(rid):
            errors.append(f"{where}: id must match {ROW_ID.pattern}")
        elif rid in seen:
            errors.append(f"{where}: duplicate id")
        else:
            seen.add(rid)
        relation = row.get("relation")
        if relation not in RELATIONS:
            errors.append(f"{where}: relation must be one of {sorted(RELATIONS)}")
        problem = row.get("problem")
        if problem is not None and (isinstance(problem, bool) or not isinstance(problem, int) or problem <= 0):
            errors.append(f"{where}: problem must be a positive integer or null")
        if not _string(row.get("left")):
            errors.append(f"{where}: left must be a non-empty string")
        if relation in UNARY:
            if row.get("right") is not None:
                errors.append(f"{where}: right must be null for {relation}")
        elif not _string(row.get("right")):
            errors.append(f"{where}: right must be a non-empty string for {relation}")
        if not _string(row.get("context")):
            errors.append(f"{where}: context must be a non-empty string")
        if not isinstance(row.get("note"), str):
            errors.append(f"{where}: note must be a string")
        cert = row.get("certificate")
        if not isinstance(cert, dict):
            errors.append(f"{where}: certificate must be an object")
        else:
            if set(cert) != CERTIFICATE_FIELDS:
                errors.append(f"{where}: certificate fields must be {sorted(CERTIFICATE_FIELDS)}")
            if not _string(cert.get("declaration")):
                errors.append(f"{where}: certificate.declaration must be a non-empty string")
            if not _string(cert.get("module")):
                errors.append(f"{where}: certificate.module must be a non-empty string")
            digest = cert.get("signature_sha256")
            if digest is not None and not (isinstance(digest, str) and SHA256.match(digest)):
                errors.append(f"{where}: certificate.signature_sha256 must be 64 hex digits or null")
        sources = row.get("sources")
        if not isinstance(sources, list) or not sources:
            errors.append(f"{where}: sources must be a non-empty list")
        else:
            for s_index, source in enumerate(sources):
                if not isinstance(source, dict) or set(source) != SOURCE_FIELDS or \
                        not _string(source.get("declaration")) or not _string(source.get("module")):
                    errors.append(f"{where}: sources[{s_index}] must be {{declaration, module}}")
    return errors


def load_registry(root: Path, path: str | Path | None = None) -> dict[str, Any]:
    target = Path(root) / (path or REGISTRY_PATH)
    try:
        document = json.loads(target.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise RegistryError(f"registry not found: {target}") from exc
    except json.JSONDecodeError as exc:
        raise RegistryError(f"registry is not valid JSON: {exc}") from exc
    errors = schema_errors(document)
    if errors:
        raise RegistryError("; ".join(errors))
    return document


def compiled_modules(root: Path) -> frozenset[str] | None:
    """The compiled module set; the one helper lives in ``research_record``."""
    import research_record  # deferred: research_record imports this module

    return research_record.compiled_modules(root)


def module_id(module_path: str | None) -> str | None:
    path = normalise_module(module_path)
    return None if path is None else path[len("lean/"):-len(".lean")].replace("/", ".")


def attest(row: dict[str, Any], atlas: Atlas, source: LeanSource,
           compiled: frozenset[str] | None = None) -> dict[str, Any]:
    """Attestation state of one registry row against the atlas, the Lean source and the build.

    ``compiled`` is the compiled module set (``compiled_modules``); None means it
    could not be read, and then no row can be attested.
    """
    cert = row["certificate"]
    module_path = normalise_module(cert["module"])
    expected_head = RELATIONS[row["relation"]]
    result: dict[str, Any] = {"id": row["id"], "declaration": cert["declaration"], "module": module_path}
    if not atlas.present:
        result.update(state="mismatch", reasons=["declaration atlas is absent"],
                      evidence_class=EVIDENCE_REPORTED)
        return result
    found = atlas.resolve(cert["declaration"], module_path)
    if found["state"] == "found":
        atlas_row = found["row"]
        signature = atlas_row.get("signature", "")
        digest = sha256_text(signature)
        head = type_head(signature)
        reasons = []
        if cert["signature_sha256"] is None:
            reasons.append("signature_sha256 is null while the declaration is in the atlas (run fill-hashes)")
        elif cert["signature_sha256"] != digest:
            reasons.append("atlas signature hash differs from the recorded signature_sha256 (the statement changed)")
        if head != expected_head:
            reasons.append(f"type head is {head!r}; relation {row['relation']!r} needs {expected_head!r}")
        compiled_target = None if compiled is None else module_id(atlas_row.get("module")) in compiled
        result.update(atlas_id=atlas_row.get("id"), atlas_signature_sha256=digest, type_head=head,
                      compiled_target=compiled_target)
        if compiled is None:
            reasons.append("the compiled module set could not be read (docs/claims.json module_graph or "
                           "the coverage-build workflow)")
        if reasons:
            result.update(state="mismatch", reasons=reasons, evidence_class=EVIDENCE_REPORTED)
        elif not compiled_target:
            result.update(state="listed_not_compiled", evidence_class=EVIDENCE_REPORTED,
                          reasons=[f"{module_id(atlas_row.get('module'))} is listed in the atlas, but no "
                                   "default build root or coverage-build target reaches it"])
        else:
            result.update(state="attested", evidence_class=EVIDENCE_ATTESTED)
        return result
    if found["state"] == "ambiguous":
        result.update(state="mismatch", reasons=[f"ambiguous atlas match: {found['candidates']}"],
                      evidence_class=EVIDENCE_REPORTED)
        return result
    # Not in this module at the pin. A same-named declaration in another module is a mismatch.
    elsewhere = atlas.resolve(cert["declaration"], None)
    if elsewhere["state"] in {"found", "ambiguous"}:
        result.update(state="mismatch", evidence_class=EVIDENCE_REPORTED,
                      reasons=[f"declaration is in the atlas under another module: {elsewhere['candidates']}"])
        return result
    names = source.full_names(module_path)
    if names is not None and cert["declaration"] in names:
        present, where = True, [module_path]
    else:
        where = source.find_theorem(cert["declaration"].split(".")[-1])
        present = bool(where)
    result.update(state="pending_pin", source_present=present, source_paths=where,
                  compiled_target=None if compiled is None else module_id(module_path) in compiled,
                  evidence_class=EVIDENCE_REPORTED)
    return result


def check(root: Path, registry_path: str | Path | None = None) -> dict[str, Any]:
    """Validate schema, attest every row and check row consistency."""
    root = Path(root)
    try:
        document = load_registry(root, registry_path)
    except RegistryError as exc:
        return {"ok": False, "errors": [str(exc)], "rows": [], "counts": {}}
    source = LeanSource(root)
    atlas = Atlas.load(root, source)
    compiled = compiled_modules(root)
    results = [attest(row, atlas, source, compiled) for row in document["rows"]]
    counts: dict[str, int] = defaultdict(int)
    for r in results:
        counts[r["state"]] += 1
    errors = [f"{r['id']}: " + "; ".join(r["reasons"]) for r in results if r["state"] in FAILING_STATES]
    errors.extend(consistency_errors(document["rows"]))
    # Sources are provenance, so an unresolved source is a warning rather than a failure.
    warnings = []
    if atlas.present:
        for row in document["rows"]:
            for s in row["sources"]:
                state = atlas.resolve(s["declaration"], normalise_module(s["module"]))["state"]
                if state != "found":
                    warnings.append(f"{row['id']}: source {s['declaration']} is {state} in the atlas")
    return {"ok": not errors, "errors": errors, "warnings": warnings, "rows": results,
            "counts": dict(sorted(counts.items())),
            "atlas_fingerprint": atlas.fingerprint,
            "evidence_boundary": EVIDENCE_BOUNDARY}


def fill_hashes(root: Path, registry_path: str | Path | None = None) -> dict[str, Any]:
    """Write signature_sha256 for rows whose certificate is now in the atlas.

    A row is filled only when its declaration resolves in the named module and
    the type head matches the relation. An existing hash that differs is left
    alone and reported: the statement changed and the row needs review.
    """
    root = Path(root)
    target = root / (registry_path or REGISTRY_PATH)
    document = load_registry(root, registry_path)
    source = LeanSource(root)
    atlas = Atlas.load(root, source)
    filled, refused, unchanged = [], [], []
    for row in document["rows"]:
        cert = row["certificate"]
        found = atlas.resolve(cert["declaration"], normalise_module(cert["module"]))
        if found["state"] != "found":
            unchanged.append({"id": row["id"], "reason": found["state"]})
            continue
        signature = found["row"].get("signature", "")
        digest = sha256_text(signature)
        head = type_head(signature)
        if head != RELATIONS[row["relation"]]:
            refused.append({"id": row["id"], "reason": f"type head {head!r} does not match {row['relation']!r}"})
        elif cert["signature_sha256"] is None:
            cert["signature_sha256"] = digest
            filled.append(row["id"])
        elif cert["signature_sha256"] != digest:
            refused.append({"id": row["id"], "reason": "recorded hash differs from the atlas; review the row"})
        else:
            unchanged.append({"id": row["id"], "reason": "already bound"})
    if filled:
        write_registry(target, document)
    return {"filled": filled, "refused": refused, "unchanged": unchanged}


def render_registry(document: dict[str, Any]) -> str:
    return json.dumps(document, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def write_registry(target: Path, document: dict[str, Any]) -> None:
    errors = schema_errors(document)
    if errors:
        raise RegistryError("; ".join(errors))
    data = render_registry(document).encode("utf-8")
    fd, tmp = tempfile.mkstemp(prefix=".relations-", dir=target.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.chmod(tmp, 0o644)
        os.replace(tmp, target)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


# --------------------------------------------------------------------------
# Kernel-probe verdicts as computed rows.
# --------------------------------------------------------------------------

PROBE_RELATION = {
    "endpoint_equivalent": "equivalent",
    "strict_decomposition_candidate": "slot_replacement",
    "residual_refuted": "refuted",
    "unknown_relation": "unknown",
}


def residualbench_rows(root: Path) -> list[dict[str, Any]]:
    """Rows computed from ``docs/residualbench_report.json`` verdicts (never stored)."""
    path = Path(root) / RESIDUALBENCH_PATH
    if not path.is_file():
        return []
    report = json.loads(path.read_text(encoding="utf-8"))
    if report.get("schema") != "residual_evaluator/1":
        raise RegistryError("unsupported residualbench report schema")
    module = report.get("module", "ResidualBench")
    budget = (report.get("tactic_budget") or {}).get("id")
    rows = []
    for verdict in report.get("verdicts", []):
        relation = PROBE_RELATION.get(verdict.get("verdict"))
        if relation is None:
            raise RegistryError(f"unrecognised residualbench verdict {verdict.get('verdict')!r}")
        residuals = verdict.get("residuals") or []
        conjunction = " ∧ ".join(residuals)
        target = verdict["target"]
        if relation == "refuted":
            left, right = conjunction, None
        else:
            left, right = target, conjunction
        note = {
            "equivalent": "soundness and laundering probes both elaborated: the residuals restate the target",
            "slot_replacement": "the residuals reconstruct the target; the converse is unknown within the budget",
            "refuted": "the refutation probe elaborated: the residual conjunction is refuted",
            "unknown": "no probe decided a relation within the budget; this is not evidence against any relation",
        }[relation]
        rows.append({
            "id": f"residualbench:{verdict['sketch_id']}",
            "relation": relation, "problem": None, "left": left, "right": right,
            "context": f"{module} (tactic budget {budget})",
            "certificate": None,
            "sources": [{"report": RESIDUALBENCH_PATH, "sketch_id": verdict["sketch_id"],
                         "receipts": verdict.get("receipts", {})}],
            "note": note,
            "converse": "unknown" if relation == "slot_replacement" else None,
            "state": "kernel_probe_verdict",
            "evidence_class": EVIDENCE_PROBE,
        })
    return rows


# --------------------------------------------------------------------------
# Accounting: usable rows, classes, explanation, comparison and transport.
# --------------------------------------------------------------------------

class Ledger:
    """Entailment edges and facts from usable rows, keyed by (context, statement)."""

    def __init__(self, rows: Iterable[dict[str, Any]]):
        self.rows = list(rows)
        self.forward: dict[tuple[str, str], list[tuple[tuple[str, str], dict]]] = defaultdict(list)
        self.backward: dict[tuple[str, str], list[tuple[tuple[str, str], dict]]] = defaultdict(list)
        self.separators: list[tuple[tuple[str, str], tuple[str, str], dict]] = []
        self.facts: dict[str, dict[tuple[str, str], list[dict]]] = {
            "refuted": defaultdict(list), "feasible": defaultdict(list), "supplied": defaultdict(list)}
        for row in self.rows:
            relation, ctx = row["relation"], row["context"]
            left = (ctx, row["left"])
            right = (ctx, row["right"]) if row.get("right") is not None else None
            if relation == "equivalent":
                self._edge(left, right, row)
                self._edge(right, left, row)
            elif relation == "endpoint_route":
                self._edge(left, right, row)
            elif relation == "slot_replacement":
                self._edge(right, left, row)
            elif relation == "strictly_stronger":
                self._edge(left, right, row)
                self.separators.append((right, left, row))
            elif relation == "separates":
                self.separators.append((left, right, row))
            elif relation in self.facts:
                self.facts[relation][left].append(row)

    def _edge(self, src: tuple[str, str], dst: tuple[str, str], row: dict) -> None:
        self.forward[src].append((dst, row))
        self.backward[dst].append((src, row))

    def reach(self, start: tuple[str, str], forward: bool = True) -> dict[tuple[str, str], list[dict]]:
        """Breadth-first paths (row lists) from ``start`` within its context."""
        graph = self.forward if forward else self.backward
        paths: dict[tuple[str, str], list[dict]] = {start: []}
        queue = deque([start])
        while queue:
            node = queue.popleft()
            for nxt, row in sorted(graph.get(node, []), key=lambda item: (item[0], item[1]["id"])):
                if nxt not in paths:
                    paths[nxt] = paths[node] + [row]
                    queue.append(nxt)
        return paths

    def compare(self, context: str, a: str, b: str) -> dict[str, Any]:
        """Relation of ``a`` to ``b`` from usable rows; absence of a path is unknown."""
        na, nb = (context, a), (context, b)
        forward = nb in self.reach(na, True)
        backward = na in self.reach(nb, True)
        separated = self._separated(nb, na)
        if forward and backward:
            relation = "equivalent"
        elif forward and separated:
            relation = "strictly_stronger"
        elif forward:
            relation = "sufficient_converse_unknown"
        elif backward:
            relation = "necessary_converse_unknown"
        else:
            relation = "unknown"
        return {"left": a, "right": b, "context": context, "relation": relation,
                "left_gives_right": forward, "right_gives_left": backward,
                "separator_right_not_giving_left": separated}

    def _separated(self, p: tuple[str, str], q: tuple[str, str]) -> bool:
        """Some separator (P0 not giving Q0) transports to (p, q): P0 -> p and q -> Q0."""
        for p0, q0, _ in self.separators:
            if p in self.reach(p0, True) and q0 in self.reach(q, True):
                return True
        return False

    def inconsistencies(self) -> list[str]:
        """Entailments contradicted by separators, and feasibility against refutation."""
        problems = []
        for p0, q0, row in self.separators:
            if q0 in self.reach(p0, True):
                problems.append(f"{row['id']}: separator contradicts a recorded entailment "
                                f"{p0[1]!r} -> {q0[1]!r} in context {p0[0]!r}")
        for node, rows in sorted(self.facts["feasible"].items()):
            for refuted_node in self.facts["refuted"]:
                if refuted_node[0] == node[0] and node in self.reach(refuted_node, False):
                    problems.append(f"{rows[0]['id']}: {node[1]!r} is feasible yet refuted by transport "
                                    f"in context {node[0]!r}")
        return problems


def consistency_errors(rows: list[dict[str, Any]]) -> list[str]:
    """Contradictions among all registry rows, whatever their attestation state.

    The principal case is a slot replacement reported as weakening: a row that
    separates the replacement from the hypothesis it reconstructs, or that calls
    the hypothesis strictly stronger than its replacement.
    """
    return Ledger(rows).inconsistencies()


def usable_rows(root: Path, include_residualbench: bool = False, include_pending: bool = False,
                registry_path: str | Path | None = None) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    root = Path(root)
    report = check(root, registry_path)
    if report["errors"] and not report["rows"]:
        raise RegistryError("; ".join(report["errors"]))
    document = load_registry(root, registry_path)
    states = {r["id"]: r for r in report["rows"]}
    rows = []
    for row in document["rows"]:
        state = states[row["id"]]
        if state["state"] == "attested" or (include_pending and state["state"] == "pending_pin"):
            rows.append(dict(row, state=state["state"], evidence_class=state["evidence_class"]))
    if include_residualbench:
        rows.extend(r for r in residualbench_rows(root) if r["relation"] != "unknown")
    return rows, report


def classes(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Equivalence classes by union-find over equivalent rows, per context."""
    parent: dict[tuple[str, str], tuple[str, str]] = {}

    def find(x):
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    used: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for row in rows:
        if row["relation"] != "equivalent":
            continue
        a, b = (row["context"], row["left"]), (row["context"], row["right"])
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[max(ra, rb)] = min(ra, rb)
    groups: dict[tuple[str, str], list[tuple[str, str]]] = defaultdict(list)
    for node in list(parent):
        groups[find(node)].append(node)
    for row in rows:
        if row["relation"] == "equivalent":
            used[find((row["context"], row["left"]))].append(row)
    out = []
    for rep, members in groups.items():
        if len(members) < 2:
            continue
        evidence = sorted({r["evidence_class"] for r in used[rep]})
        out.append({"context": rep[0], "members": sorted(m[1] for m in members),
                    "rows": sorted(r["id"] for r in used[rep]), "evidence_classes": evidence,
                    "meaning": "one question for credit; separate formulations for search"})
    return sorted(out, key=lambda c: (c["context"], c["members"]))


def explain(rows: list[dict[str, Any]], text: str) -> list[dict[str, Any]]:
    needle = text.casefold()
    out = []
    for row in rows:
        haystack = [row["left"], row.get("right") or "", row["id"]]
        if any(needle in h.casefold() for h in haystack):
            out.append({"id": row["id"], "relation": row["relation"], "problem": row.get("problem"),
                        "left": row["left"], "right": row.get("right"), "context": row["context"],
                        "direction": DIRECTION[row["relation"]],
                        "weakening": "excluded" if row["relation"] == "slot_replacement" else None,
                        "state": row.get("state"), "evidence_class": row.get("evidence_class"),
                        "note": row.get("note")})
    return sorted(out, key=lambda r: r["id"])


def transport(rows: list[dict[str, Any]], statement: str, mode: str,
              context: str | None = None) -> dict[str, Any]:
    """What a supplied or refuted ``statement`` implies along usable rows.

    Supply moves forward along an entailment; refutation moves backward. Any
    other mode (an outcome, a cost, a failed attempt) is refused: those never
    transport.
    """
    if mode not in TRANSPORT_MODES:
        raise TransportRefused(
            f"mode {mode!r} refused: only supply (forward) and refutation (backward) move along "
            "entailments; outcomes, costs and failed attempts never transport")
    ledger = Ledger(rows)
    contexts = sorted({r["context"] for r in rows
                       if statement in (r["left"], r.get("right"))
                       and (context is None or r["context"] == context)})
    results = []
    for ctx in contexts:
        paths = ledger.reach((ctx, statement), forward=(mode == "supplied"))
        moved = []
        for node, path in sorted(paths.items()):
            if not path:
                continue
            classes_on_path = sorted({r["evidence_class"] for r in path})
            conflict = []
            opposite = "refuted" if mode == "supplied" else "feasible"
            if node in ledger.facts[opposite]:
                conflict = [r["id"] for r in ledger.facts[opposite][node]]
            moved.append({"statement": node[1], "becomes": mode, "path": [r["id"] for r in path],
                          "evidence_classes": classes_on_path, "conflicts_with": conflict})
        results.append({"context": ctx, "moved": moved})
    return {"statement": statement, "mode": mode,
            "assumption": f"the caller takes {statement!r} as {mode}; this call does not establish it",
            "direction": "forward along entailments" if mode == "supplied" else "backward along entailments",
            "contexts": results,
            "boundary": ("derivation over registry rows; each step inherits its row's evidence class. "
                         "Nothing about attempts, costs or outcomes moves.")}


# --------------------------------------------------------------------------
# CLI.
# --------------------------------------------------------------------------

def _print(value: Any) -> None:
    sys.stdout.write(json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Relation rows between statements, attested against the declaration atlas. "
                    "Attested rows carry evidence class declaration_atlas_at_pin and a compiled target; "
                    "listed_not_compiled rows fail the check; pending_pin rows are reported transcriptions.")
    parser.add_argument("--root", type=Path, default=ROOT, help="checkout root (default: this repository)")
    parser.add_argument("--registry", default=None, help=f"registry path relative to the root (default {REGISTRY_PATH})")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("check", help="validate and attest every row; exit 1 on a mismatch, a listed_not_compiled "
                                 "row or a schema error")
    for name, help_text in (("classes", "equivalence classes over usable equivalent rows"),
                            ("explain", "rows whose left or right mention TEXT"),
                            ("transport", "what a supplied or refuted statement implies")):
        p = sub.add_parser(name, help=help_text)
        p.add_argument("--include-residualbench", action="store_true",
                       help="also use kernel-probe verdicts from docs/residualbench_report.json")
        p.add_argument("--include-pending", action="store_true",
                       help="also use pending_pin rows (evidence class reported)")
        if name == "explain":
            p.add_argument("text")
        if name == "transport":
            p.add_argument("statement")
            p.add_argument("mode", help="supplied or refuted")
            p.add_argument("--context", default=None)
    sub.add_parser("fill-hashes", help="write signature_sha256 for rows now in the atlas")
    args = parser.parse_args(argv)
    try:
        if args.command == "check":
            report = check(args.root, args.registry)
            _print(report)
            return 0 if report["ok"] else 1
        if args.command == "fill-hashes":
            _print(fill_hashes(args.root, args.registry))
            return 0
        rows, report = usable_rows(args.root, args.include_residualbench, args.include_pending, args.registry)
        if args.command == "classes":
            _print({"classes": classes(rows), "usable_rows": len(rows), "registry_counts": report["counts"]})
        elif args.command == "explain":
            # Explanation lists every registry row labelled with its state, whatever
            # that state is, and every probe verdict (unknown included) when asked.
            document = load_registry(args.root, args.registry)
            states = {r["id"]: r for r in report["rows"]}
            pool = [dict(r, state=states[r["id"]]["state"], evidence_class=states[r["id"]]["evidence_class"])
                    for r in document["rows"]]
            if args.include_residualbench:
                pool.extend(residualbench_rows(args.root))
            _print({"text": args.text, "rows": explain(pool, args.text)})
        else:
            _print(transport(rows, args.statement, args.mode, args.context))
        return 0
    except TransportRefused as exc:
        sys.stderr.write(f"refused: {exc}\n")
        return 2
    except RegistryError as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
