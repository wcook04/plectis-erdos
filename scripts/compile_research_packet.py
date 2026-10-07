#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Compile a research packet from the record under a byte budget, so that every
registered distinction survives, and emit it as a ``type_b_handoff_manifest_v1``.

Inputs are a spec (target, byte budget, mandatory resources, resources,
obligations, withholding) and the contrast ledger
(``docs/research-commons/record/contrasts.json``).

* Every resource is bound to bytes. A span is read at the git ref (``HEAD`` by
  default), bound to the SHA-256 of the whole file there, and every
  ``must_contain`` literal must lie inside the span. A declaration resolves
  through the declaration atlas (or the Lean source) to its header line and
  runs to the next item or a line window.
* Each obligation is an OR of AND alternatives over resource ids. Authored
  obligations come from the spec. With ``include_triggered_contrasts``, each
  contrast whose triggers match the target adds one obligation whose single
  alternative is the whole evidence bundle of that contrast, so both sides of
  the distinction reach the reader. An authored obligation with origin
  ``contrast:<id>`` replaces the derived one only in the legacy mode. The
  dispatch profile sets ``protect_contrasts=true`` and refuses such overrides;
  extra authored views must be additive, not substitutes for a guard.
* Withheld resources, resources after the cutoff (or with no availability date
  when a cutoff is set), resources in an excluded family, resources whose span
  overlaps blocked bytes, and everything depending on them are blocked.
* Selection is exact branch and bound over the alternatives with shared costs
  (identical excerpts are paid once) and dependency closure. The mandatory
  closure comes first. A search that meets its state budget is labelled
  incomplete and never called optimal. When the budget cannot hold the
  mandatory set plus one alternative per obligation, the compiler refuses and
  returns the unmet obligations and a deletion-minimal infeasible core.

Outputs in ``--out``: ``excerpts/<sha256>.md`` (header naming path, lines and
file SHA-256, then the exact lines), ``handoff_manifest.json`` for
``type_b_handoff_bundle.py build --repo-root <out>`` (the compiler never writes
a packet directory itself), and ``owner_receipt.json`` with the selection,
blocked items, witnesses, byte totals and search record. The receipt stays out
of the manifest. The byte budget counts the distinct excerpt files; the
builder's guide and index files are extra.

Evidence boundary: the compiler certifies source integrity and structural
coverage of the declared obligations. It certifies no mathematics, no reader's
understanding, and no completeness of the obligation catalogue.

Standard library only.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import sys
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

import contrast_ledger as ledger  # noqa: E402

ROOT = ledger.ROOT
MANIFEST_SCHEMA = "type_b_handoff_manifest_v1"
RECEIPT_SCHEMA = "plectis-research-packet-receipt/1"
MANIFEST_NAME = "handoff_manifest.json"
RECEIPT_NAME = "owner_receipt.json"
EXCERPT_DIR = "excerpts"
DEFAULT_STATE_BUDGET = 200_000
DEFAULT_DECLARATION_WINDOW = 80
MANAGED_NAMES = {MANIFEST_NAME, RECEIPT_NAME, EXCERPT_DIR}
ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.:-]*$")
CONTRAST_PREFIX = "contrast-"
RESOURCE_KINDS = ("source_span", "file", "declaration")
SPEC_FIELDS = {"schema", "packet_id", "title", "question", "target", "byte_budget", "mandatory",
               "resources", "obligations", "withheld", "excluded_families", "cutoff",
               "include_triggered_contrasts", "contrasts", "state_budget", "declaration_window",
               "protect_contrasts"}
RESOURCE_FIELDS = {"id", "kind", "path", "name", "start_line", "end_line", "must_contain",
                   "depends_on", "family", "available_at", "role"}
EVIDENCE_BOUNDARY = (
    "Selection certifies source integrity (each excerpt is bound to the SHA-256 of its whole "
    "file at the recorded commit, with its required literals inside the span) and structural "
    "coverage of the declared obligations. It certifies no mathematical claim, no reader's "
    "understanding and no completeness of the obligation catalogue. Declaration evidence "
    "classes name where a declaration was found; kernel acceptance comes from the pinned Lean "
    "build.")
LANGUAGES = {".lean": "lean", ".md": "markdown", ".py": "python", ".json": "json",
             ".tex": "latex", ".txt": "text", ".yml": "yaml", ".yaml": "yaml"}


class SpecError(ValueError):
    """The spec is malformed or cites evidence that does not hold."""


def canonical_bytes(value: Any) -> bytes:
    return ledger.canonical_bytes(value) + b"\n"


def instant(value: str, where: str) -> datetime:
    try:
        moment = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except (AttributeError, ValueError) as exc:
        raise SpecError(f"{where} must be an ISO timestamp: {value!r}") from exc
    if moment.tzinfo is None:
        raise SpecError(f"{where} must carry a timezone: {value!r}")
    return moment


# ---------------------------------------------------------------------------
# Resources


@dataclass(frozen=True)
class Resource:
    id: str
    kind: str
    path: str
    start_line: int
    end_line: int
    excerpt: bytes
    file_sha256: str
    binding: str
    evidence_class: str
    origin: str = "spec"
    name: str | None = None
    must_contain: tuple[str, ...] = ()
    depends_on: tuple[str, ...] = ()
    family: str | None = None
    available_at: str | None = None
    role: str | None = None
    window_capped: bool = False
    # Hash only the exact selected source text, never its provenance header.
    payload_sha256: str | None = None

    @property
    def excerpt_sha256(self) -> str:
        return ledger.sha256_hex(self.excerpt)

    @property
    def cost(self) -> int:
        return len(self.excerpt)

    def record(self) -> dict[str, Any]:
        row = {"id": self.id, "kind": self.kind, "origin": self.origin, "path": self.path,
               "start_line": self.start_line, "end_line": self.end_line,
               "file_sha256": self.file_sha256, "binding": self.binding,
               "excerpt_sha256": self.excerpt_sha256, "payload_sha256": self.payload_sha256,
               "bytes": self.cost,
               "evidence_class": self.evidence_class, "must_contain": list(self.must_contain),
               "depends_on": list(self.depends_on)}
        if self.name:
            row["name"] = self.name
        if self.family:
            row["family"] = self.family
        if self.available_at:
            row["available_at"] = self.available_at
        if self.window_capped:
            row["window_capped"] = True
        return row


def _fence(text: str) -> str:
    longest = max((len(run) for run in re.findall(r"~+", text)), default=0)
    return "~" * max(3, longest + 1)


def render_excerpt(path: str, start: int, end: int, file_sha256: str, text: str, binding: str,
                   declaration: str | None = None, evidence_class: str | None = None,
                   window_capped: bool = False) -> bytes:
    """Excerpt file bytes: a header naming the source, then the exact lines."""
    header = ["# Source excerpt", "", f"- Path: `{path}`", f"- Lines: {start}-{end}",
              f"- File SHA-256: {file_sha256}"]
    if declaration:
        header.append(f"- Declaration: `{declaration}` ({evidence_class})")
    if binding == "worktree_uncommitted":
        header.append("- Binding: working-tree bytes of a file absent at the recorded commit")
    elif binding == "worktree":
        header.append("- Binding: working-tree bytes")
    if window_capped:
        header.append(f"- Window: the declaration continues past line {end}")
    body = text if text.endswith("\n") else text + "\n"
    fence = _fence(body)
    language = LANGUAGES.get(PurePosixPath(path).suffix.lower(), "text")
    return ("\n".join(header) + "\n\n" + f"{fence}{language}\n" + body + fence + "\n").encode("utf-8")


def _require_list_of_strings(value: Any, where: str) -> tuple[str, ...]:
    if value is None:
        return ()
    if not isinstance(value, list) or any(not isinstance(v, str) or not v for v in value):
        raise SpecError(f"{where} must be a list of nonempty strings")
    return tuple(value)


def resolve_resource(row: Mapping[str, Any], tree: ledger.SourceTree,
                     index: ledger.DeclarationIndex, window: int = DEFAULT_DECLARATION_WINDOW,
                     origin: str = "spec") -> Resource:
    """Bind one resource spec to bytes at the tree's ref."""
    if not isinstance(row, Mapping):
        raise SpecError("each resource must be an object")
    rid = row.get("id")
    if not isinstance(rid, str) or not ID_RE.match(rid):
        raise SpecError(f"resource id {rid!r} must match {ID_RE.pattern}")
    extra = sorted(set(row) - RESOURCE_FIELDS)
    if extra:
        raise SpecError(f"resource {rid} has unknown fields {extra}")
    kind = row.get("kind")
    if kind not in RESOURCE_KINDS:
        raise SpecError(f"resource {rid} kind must be one of {RESOURCE_KINDS}")
    must_contain = _require_list_of_strings(row.get("must_contain"), f"{rid}.must_contain")
    depends_on = _require_list_of_strings(row.get("depends_on"), f"{rid}.depends_on")
    family = row.get("family")
    if family is not None and (not isinstance(family, str) or not family):
        raise SpecError(f"resource {rid} family must be a nonempty string")
    available_at = row.get("available_at")
    if available_at is not None:
        instant(available_at, f"{rid}.available_at")
    declaration = None
    evidence_class = "source_span_bound_to_file_hash"
    capped = False
    try:
        if kind == "declaration":
            name = row.get("name")
            if not isinstance(name, str) or not name:
                raise SpecError(f"resource {rid} of kind declaration needs a name")
            found = index.resolve(name, row.get("path"))
            if not found.get("found"):
                raise SpecError(f"resource {rid}: " + "; ".join(found.get("errors", [])))
            module = found.get("module") or row.get("path")
            if not module:
                raise SpecError(f"resource {rid}: declaration {name} has no module")
            blob = (tree.read(module) if found.get("binding") != "worktree_uncommitted"
                    or tree.allow_uncommitted else None)
            if blob is None:
                raise SpecError(f"resource {rid}: {module} is absent at {tree.ref}; "
                                "pass --allow-uncommitted to bind working-tree bytes")
            lines = blob.lines()
            hits = ledger.declaration_lines(lines, name)
            if not hits:
                raise SpecError(f"resource {rid}: no header for {name} in {module}")
            wanted = found.get("line")
            line = wanted if wanted in hits else hits[0]
            start, end, capped = ledger.declaration_span(lines, line, window)
            declaration = name
            evidence_class = found["evidence_class"]
            must_contain = tuple(dict.fromkeys((ledger.short_name(name),) + must_contain))
            path = module
        else:
            path = row.get("path")
            blob = tree.read(path)
            if kind == "file":
                start, end = 1, len(blob.lines())
                if end == 0:
                    raise SpecError(f"resource {rid}: {path} is empty")
            else:
                start, end = row.get("start_line"), row.get("end_line")
        text = ledger.span_text(blob, start, end)
    except ledger.LedgerError as exc:
        raise SpecError(f"resource {rid}: {exc}") from exc
    except UnicodeDecodeError as exc:
        raise SpecError(f"resource {rid}: source is not UTF-8") from exc
    missing = ledger.missing_literals(text, must_contain)
    if missing:
        raise SpecError(f"resource {rid}: literals outside {blob.path}:{start}-{end}: {missing}")
    excerpt = render_excerpt(blob.path, start, end, blob.sha256, text, blob.binding,
                             declaration, evidence_class if declaration else None, capped)
    return Resource(id=rid, kind=kind, path=blob.path, start_line=start, end_line=end,
                    excerpt=excerpt, file_sha256=blob.sha256, binding=blob.binding,
                    evidence_class=evidence_class, origin=origin, name=declaration,
                    must_contain=must_contain, depends_on=depends_on, family=family,
                    available_at=available_at, role=row.get("role"), window_capped=capped,
                    payload_sha256=ledger.sha256_hex(text.encode("utf-8")))


# ---------------------------------------------------------------------------
# Dependencies and blocking


def dependency_closure(ids: Iterable[str], deps: Mapping[str, Sequence[str]]) -> frozenset[str]:
    seen: set[str] = set()
    stack = list(ids)
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        if node not in deps:
            raise SpecError(f"unknown resource {node}")
        seen.add(node)
        stack.extend(deps[node])
    return frozenset(seen)


def check_acyclic(deps: Mapping[str, Sequence[str]]) -> None:
    state: dict[str, int] = {}
    for root in sorted(deps):
        if state.get(root):
            continue
        stack = [(root, iter(deps[root]))]
        state[root] = 1
        while stack:
            node, children = stack[-1]
            child = next(children, None)
            if child is None:
                state[node] = 2
                stack.pop()
                continue
            if child not in deps:
                raise SpecError(f"{node} depends on unknown resource {child}")
            if state.get(child) == 1:
                raise SpecError(f"dependency cycle through {child}")
            if not state.get(child):
                state[child] = 1
                stack.append((child, iter(deps[child])))


def blocked_resources(resources: Mapping[str, Resource], withheld: Sequence[str],
                      excluded_families: Sequence[str], cutoff: str | None) -> dict[str, str]:
    """Blocked resource ids with reasons; taint moves through overlap and ``depends_on``."""
    paths = {r.path for r in resources.values()}
    unknown = sorted(set(withheld) - set(resources) - paths)
    if unknown:
        raise SpecError(f"withheld names no resource id or path: {unknown}")
    moment = instant(cutoff, "cutoff") if cutoff else None
    blocked: dict[str, str] = {}
    for rid, res in sorted(resources.items()):
        if rid in withheld or res.path in withheld:
            blocked[rid] = "withheld"
        elif moment is not None and res.available_at is None:
            blocked[rid] = "availability_unknown_before_cutoff"
        elif moment is not None and instant(res.available_at, rid) > moment:
            blocked[rid] = "after_cutoff"
        elif res.family is not None and res.family in excluded_families:
            blocked[rid] = "held_out_family"
    changed = True
    while changed:
        changed = False
        for rid, res in sorted(resources.items()):
            if rid in blocked:
                continue
            for other in sorted(blocked):
                source = resources[other]
                # An exact copy changes its rendered hash when its path changes.
                # Equality is a conservative custody taint, not semantic equality.
                if source.payload_sha256 and source.payload_sha256 == res.payload_sha256:
                    blocked[rid] = f"same_bytes_as_blocked:{other}"
                    changed = True
                    break
                # Mere interval overlap does not expand the original tainted span.
                # An exact alias, however, carries its whole copied payload.
                if blocked[other].startswith("overlaps_"):
                    continue
                if source.path == res.path and source.start_line <= res.end_line \
                        and res.start_line <= source.end_line:
                    blocked[rid] = f"overlaps_blocked_material:{other}"
                    changed = True
                    break
                if source.excerpt_sha256 == res.excerpt_sha256:
                    blocked[rid] = f"same_bytes_as_blocked:{other}"
                    changed = True
                    break
            if rid in blocked:
                continue
            tainted = sorted(d for d in res.depends_on if d in blocked)
            if tainted:
                blocked[rid] = f"depends_on_blocked_material:{tainted[0]}"
                changed = True
    return blocked


# ---------------------------------------------------------------------------
# The cover model


@dataclass(frozen=True)
class Requirement:
    id: str
    alternatives: tuple[frozenset[str], ...]


@dataclass
class CoverResult:
    selected: frozenset[str] | None
    cost: int | None
    states: int
    complete: bool


def set_cost(units: Mapping[str, tuple[str, int]], ids: Iterable[str]) -> int:
    """Cost of a set: identical content (same key) is paid once."""
    paid: dict[str, int] = {}
    for rid in ids:
        key, size = units[rid]
        paid[key] = size
    return sum(paid.values())


def minimum_cover(units: Mapping[str, tuple[str, int]], requirements: Sequence[Requirement],
                  base: frozenset[str] = frozenset(), budget: int | None = None,
                  state_budget: int = DEFAULT_STATE_BUDGET) -> CoverResult:
    """Least-cost superset of ``base`` meeting every requirement, by branch and bound.

    Each requirement is met when one of its alternatives lies inside the set.
    The search branches on the pending requirement with fewest alternatives and
    prunes with the admissible bound "the largest cheapest marginal cost over
    the pending requirements". When it runs to completion the result is the
    exact optimum of the finite model (ties broken by the sorted ids). When the
    state budget stops it, ``complete`` is false and any incumbent is only
    feasible.
    """
    if state_budget < 1:
        raise SpecError("state budget must be positive")
    reqs = tuple(requirements)
    if len({r.id for r in reqs}) != len(reqs):
        raise SpecError("duplicate requirement id")
    for req in reqs:
        for alternative in req.alternatives:
            if not alternative <= units.keys():
                raise SpecError(f"requirement {req.id} names unknown resources")
    if not base <= units.keys():
        raise SpecError("mandatory set names unknown resources")
    best: frozenset[str] | None = None
    best_cost: int | None = None
    states = 0
    complete = True
    seen: set[frozenset[str]] = set()
    todo = [frozenset(base)]
    while todo:
        selected = todo.pop()
        if selected in seen:
            continue
        if states >= state_budget:
            complete = False
            break
        states += 1
        seen.add(selected)
        cost = set_cost(units, selected)
        if budget is not None and cost > budget:
            continue
        if best_cost is not None and cost > best_cost:
            continue
        pending = [r for r in reqs if not any(a <= selected for a in r.alternatives)]
        if not pending:
            if best is None or (cost, tuple(sorted(selected))) < (best_cost, tuple(sorted(best))):
                best, best_cost = selected, cost
            continue
        if any(not r.alternatives for r in pending):
            continue
        lower = max(min(set_cost(units, selected | a) - cost for a in r.alternatives)
                    for r in pending)
        if budget is not None and cost + lower > budget:
            continue
        if best_cost is not None and cost + lower > best_cost:
            continue
        chosen = min(pending, key=lambda r: (len(r.alternatives), r.id))
        extensions = {selected | a for a in chosen.alternatives}
        todo.extend(sorted(extensions, key=lambda s: (set_cost(units, s), tuple(sorted(s))),
                           reverse=True))
    return CoverResult(best, best_cost, states, complete)


def irreducible_budget_core(units: Mapping[str, tuple[str, int]],
                            requirements: Sequence[Requirement], base: frozenset[str],
                            budget: int, state_budget: int = DEFAULT_STATE_BUDGET) -> dict[str, Any]:
    """A deletion-minimal set of requirements that no cover within the budget meets.

    The mandatory base is fixed in every trial. An incomplete search is never
    read as infeasibility, so the result can be ``not_established``.
    """
    def impossible(reqs: Sequence[Requirement]) -> bool:
        result = minimum_cover(units, reqs, base, budget, state_budget)
        return result.complete and result.selected is None

    core = list(requirements)
    if not impossible(core):
        return {"status": "not_established", "obligations": []}
    for req in list(core):
        candidate = [r for r in core if r.id != req.id]
        if impossible(candidate):
            core = candidate
    minimal = True
    for req in core:
        reduced = minimum_cover(units, [r for r in core if r.id != req.id], base, budget,
                                state_budget)
        if not (reduced.complete and reduced.selected is not None):
            minimal = False
    return {"status": "deletion_minimal" if minimal else "infeasible_core",
            "obligations": [r.id for r in core], "budget": budget,
            "scope": "declared resources, obligations and budget"}


# ---------------------------------------------------------------------------
# Spec, contrasts and obligations


@dataclass
class Obligation:
    id: str
    origin: str
    alternatives: list[tuple[str, ...]]
    description: str
    contrast: Mapping[str, Any] | None = None
    notes: list[str] = field(default_factory=list)
    dropped: list[dict[str, Any]] = field(default_factory=list)


def load_spec(path: Path) -> dict[str, Any]:
    try:
        spec = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SpecError(f"cannot read spec {path}: {exc}") from exc
    if not isinstance(spec, Mapping):
        raise SpecError("spec must be a JSON object")
    return dict(spec)


def validate_spec(spec: Mapping[str, Any]) -> None:
    extra = sorted(set(spec) - SPEC_FIELDS)
    if extra:
        raise SpecError(f"spec has unknown fields {extra}")
    packet_id = spec.get("packet_id")
    if not isinstance(packet_id, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", packet_id):
        raise SpecError("packet_id must be a filename-safe identifier")
    if not isinstance(spec.get("title"), str) or not spec["title"].strip():
        raise SpecError("title must be a nonempty string")
    target = spec.get("target")
    if not isinstance(target, Mapping) or not isinstance(target.get("anchor"), str) \
            or not target["anchor"].strip():
        raise SpecError("target must be an object with a nonempty anchor")
    problem = target.get("problem")
    if problem is not None and (not isinstance(problem, int) or isinstance(problem, bool)):
        raise SpecError("target.problem must be an integer or null")
    _require_list_of_strings(target.get("declarations"), "target.declarations")
    budget = spec.get("byte_budget")
    if not isinstance(budget, int) or isinstance(budget, bool) or budget <= 0:
        raise SpecError("byte_budget must be a positive integer")
    for key in ("mandatory", "withheld", "excluded_families", "contrasts"):
        _require_list_of_strings(spec.get(key), key)
    if not isinstance(spec.get("resources", []), list):
        raise SpecError("resources must be a list")
    if not isinstance(spec.get("obligations", []), list):
        raise SpecError("obligations must be a list")
    if not isinstance(spec.get("include_triggered_contrasts", False), bool):
        raise SpecError("include_triggered_contrasts must be true or false")
    if not isinstance(spec.get("protect_contrasts", False), bool):
        raise SpecError("protect_contrasts must be true or false")
    if spec.get("cutoff") is not None:
        instant(spec["cutoff"], "cutoff")


def contrast_resource_rows(row: Mapping[str, Any], relations: Mapping[str, Mapping[str, Any]],
                           ) -> tuple[list[dict[str, Any]], list[str]]:
    """Resource specs for a contrast's evidence, and notes for evidence without bytes."""
    specs: list[dict[str, Any]] = []
    notes: list[str] = []
    for position, item in enumerate(row["evidence"], start=1):
        rid = f"{CONTRAST_PREFIX}{row['id']}-e{position}"
        if item["kind"] == "source_span":
            specs.append({"id": rid, "kind": "source_span", "path": item["path"],
                          "start_line": item["start_line"], "end_line": item["end_line"],
                          "must_contain": list(item["must_contain"])})
        elif item["kind"] == "declaration":
            specs.append({"id": rid, "kind": "declaration", "name": item["name"],
                          "path": item["module"]})
        else:
            relation = relations.get(item["id"])
            certificate = relation.get("certificate") if isinstance(relation, Mapping) else None
            if isinstance(certificate, Mapping) and isinstance(certificate.get("declaration"), str):
                specs.append({"id": rid, "kind": "declaration",
                              "name": certificate["declaration"],
                              "path": certificate.get("module")})
                notes.append(f"relation {item['id']} is cited through its certificate "
                             f"declaration {certificate['declaration']} (recorded_relation)")
            else:
                notes.append(f"relation {item['id']} is cited by id only; the relations record "
                             "names no certificate declaration for it")
    return specs, notes


def select_contrasts(spec: Mapping[str, Any], rows: Sequence[Mapping[str, Any]],
                     ) -> tuple[list[Mapping[str, Any]], list[dict[str, Any]]]:
    """Contrast rows that become obligations, and a log of how each was chosen."""
    by_id = {row["id"]: row for row in rows}
    chosen: dict[str, str] = {}
    log: list[dict[str, Any]] = []
    for cid in spec.get("contrasts", []) or []:
        if cid not in by_id:
            raise SpecError(f"contrast {cid} is absent from the ledger")
        chosen.setdefault(cid, "listed_in_spec")
    if spec.get("include_triggered_contrasts"):
        target = spec["target"]
        for entry in ledger.triggered(rows, problem=target.get("problem"),
                                      text=target.get("anchor"),
                                      declarations=target.get("declarations") or []):
            if not entry["packet_obligation"]:
                log.append({"id": entry["id"], "selection": "triggered_without_packet_obligation",
                            "matched_on": entry["matched_on"]})
                continue
            chosen.setdefault(entry["id"], "triggered_by_target")
            log.append({"id": entry["id"], "selection": "triggered_by_target",
                        "matched_on": entry["matched_on"]})
    for cid in sorted(set(spec.get("contrasts", []) or [])):
        log.append({"id": cid, "selection": "listed_in_spec"})
    log.sort(key=lambda entry: (entry["id"], entry["selection"]))
    return [by_id[cid] for cid in sorted(chosen)], log


# ---------------------------------------------------------------------------
# Compilation


def _ledger_rows(tree: ledger.SourceTree, ledger_path: str) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    blob = tree.find_or_uncommitted(ledger_path)
    if blob is None:
        raise SpecError(f"contrast ledger {ledger_path} is absent")
    document = json.loads(blob.data.decode("utf-8"))
    errors = ledger.shape_errors(document)
    if errors:
        raise SpecError("contrast ledger is malformed: " + "; ".join(errors))
    return document["rows"], {"path": ledger_path, "sha256": blob.sha256, "binding": blob.binding}


def compile_packet(spec: Mapping[str, Any], root: Path | str = ROOT, ref: str | None = "HEAD",
                   allow_uncommitted: bool = False, ledger_path: str = ledger.LEDGER_PATH,
                   budget: int | None = None, tree: ledger.SourceTree | None = None,
                   index: ledger.DeclarationIndex | None = None) -> dict[str, Any]:
    """Compile in memory. Returns ``{status, receipt, manifest, excerpts}``.

    ``manifest`` and ``excerpts`` are ``None`` when the compiler refuses.
    """
    validate_spec(spec)
    tree = tree or ledger.SourceTree(root, ref=ref, allow_uncommitted=allow_uncommitted)
    index = index or ledger.DeclarationIndex(tree)
    byte_budget = spec["byte_budget"] if budget is None else budget
    if not isinstance(byte_budget, int) or byte_budget <= 0:
        raise SpecError("budget must be a positive integer")
    state_budget = spec.get("state_budget", DEFAULT_STATE_BUDGET)
    window = spec.get("declaration_window", DEFAULT_DECLARATION_WINDOW)

    resources: dict[str, Resource] = {}
    for row in spec.get("resources", []):
        res = resolve_resource(row, tree, index, window)
        if res.id.startswith(CONTRAST_PREFIX):
            raise SpecError(f"resource id prefix {CONTRAST_PREFIX!r} is reserved for contrast evidence")
        if res.id in resources:
            raise SpecError(f"duplicate resource id {res.id}")
        resources[res.id] = res

    ledger_info: dict[str, Any] | None = None
    contrast_log: list[dict[str, Any]] = []
    contrast_rows: list[Mapping[str, Any]] = []
    if spec.get("include_triggered_contrasts") or spec.get("contrasts"):
        rows, ledger_info = _ledger_rows(tree, ledger_path)
        contrast_rows, contrast_log = select_contrasts(spec, rows)
    _, relations_info, relations = ledger.load_relation_ids(tree)

    obligations: list[Obligation] = []
    overridden: set[str] = set()
    for row in spec.get("obligations", []):
        if not isinstance(row, Mapping):
            raise SpecError("each obligation must be an object")
        oid = row.get("id")
        if not isinstance(oid, str) or not ID_RE.match(oid):
            raise SpecError(f"obligation id {oid!r} must match {ID_RE.pattern}")
        origin = row.get("origin", "authored")
        if origin != "authored" and not (isinstance(origin, str) and origin.startswith("contrast:")):
            raise SpecError(f"obligation {oid} origin must be 'authored' or 'contrast:<id>'")
        if origin.startswith("contrast:"):
            if spec.get("protect_contrasts", False):
                raise SpecError(f"obligation {oid}: protected contrast cannot be replaced; "
                                "use origin=authored for an additional view")
            overridden.add(origin.split(":", 1)[1])
        alternatives = row.get("alternatives")
        if not isinstance(alternatives, list) or not alternatives or any(
                not isinstance(a, list) or not a or any(not isinstance(i, str) for i in a)
                for a in alternatives):
            raise SpecError(f"obligation {oid} needs a nonempty list of nonempty id lists")
        obligations.append(Obligation(oid, origin, [tuple(a) for a in alternatives],
                                      str(row.get("description") or row.get("covers") or
                                          f"Authored obligation {oid}.")))

    for row in contrast_rows:
        if row["id"] in overridden:
            contrast_log.append({"id": row["id"], "selection": "replaced_by_authored_obligation"})
            continue
        specs, notes = contrast_resource_rows(row, relations)
        ids: list[str] = []
        for resource_spec in specs:
            res = resolve_resource(resource_spec, tree, index, window, origin=f"contrast:{row['id']}")
            resources[res.id] = res
            ids.append(res.id)
        description = (f"Distinction {row['id']}: {row['distinction']} "
                       f"Right reading: {row['right_reading']}")
        obligations.append(Obligation(f"{CONTRAST_PREFIX}{row['id']}", f"contrast:{row['id']}",
                                      [tuple(ids)] if ids else [], description, row, notes))
    if len({o.id for o in obligations}) != len(obligations):
        raise SpecError("duplicate obligation id")

    deps = {rid: res.depends_on for rid, res in resources.items()}
    check_acyclic(deps)
    for name in spec.get("mandatory", []) or []:
        if name not in resources:
            raise SpecError(f"mandatory names unknown resource {name}")
    for ob in obligations:
        for alternative in ob.alternatives:
            for rid in alternative:
                if rid not in resources:
                    raise SpecError(f"obligation {ob.id} names unknown resource {rid}")

    blocked = blocked_resources(resources, spec.get("withheld", []) or [],
                                spec.get("excluded_families", []) or [], spec.get("cutoff"))
    eligible = {rid: res for rid, res in resources.items() if rid not in blocked}
    units = {rid: (res.excerpt_sha256, res.cost) for rid, res in eligible.items()}
    mandatory = dependency_closure(spec.get("mandatory", []) or [], deps)

    requirements: list[Requirement] = []
    for ob in obligations:
        kept: list[frozenset[str]] = []
        for alternative in ob.alternatives:
            closed = dependency_closure(alternative, deps)
            hit = sorted(closed & blocked.keys())
            if hit:
                ob.dropped.append({"alternative": list(alternative), "blocked": hit})
            elif closed not in kept:
                kept.append(closed)
        requirements.append(Requirement(ob.id, tuple(sorted(kept, key=lambda s: tuple(sorted(s))))))

    receipt: dict[str, Any] = {
        "schema": RECEIPT_SCHEMA,
        "packet_id": spec["packet_id"],
        "spec_sha256": ledger.sha256_hex(ledger.canonical_bytes(dict(spec))),
        "source": tree.describe(),
        "contrast_ledger": ledger_info,
        "relations": relations_info,
        "atlas": index.atlas_info,
        "byte_budget": byte_budget,
        "budget_unit": "bytes of distinct excerpt files; builder guide and index files are extra",
        "state_budget": state_budget,
        "resources": [resources[rid].record() for rid in sorted(resources)],
        "blocked": {rid: blocked[rid] for rid in sorted(blocked)},
        "mandatory_closure": sorted(mandatory),
        "contrast_selection": contrast_log,
        "protect_contrasts": spec.get("protect_contrasts", False),
        "evidence_boundary": EVIDENCE_BOUNDARY,
    }

    def obligation_rows(witnesses: Mapping[str, list[str]] | None = None) -> list[dict[str, Any]]:
        out = []
        for ob, req in zip(obligations, requirements):
            row = {"id": ob.id, "origin": ob.origin,
                   "alternatives": [sorted(a) for a in req.alternatives],
                   "dropped_alternatives": ob.dropped, "notes": ob.notes}
            if witnesses is not None:
                row["witness"] = witnesses.get(ob.id)
            out.append(row)
        return out

    def refuse(status: str, unmet: list[dict[str, Any]], core: dict[str, Any] | None,
               search: CoverResult | None) -> dict[str, Any]:
        receipt.update(status=status, optimality="not_applicable", obligations=obligation_rows(),
                       unmet_obligations=unmet, infeasible_core=core,
                       search=None if search is None else {"states": search.states,
                                                           "complete": search.complete})
        return {"status": status, "receipt": receipt, "manifest": None, "excerpts": None}

    blocked_mandatory = sorted(mandatory & blocked.keys())
    if blocked_mandatory:
        return refuse("refused_mandatory_blocked",
                      [{"id": "mandatory", "reason": "mandatory context is blocked",
                        "blocked": {rid: blocked[rid] for rid in blocked_mandatory}}], None, None)
    mandatory_bytes = set_cost(units, mandatory)
    receipt["mandatory_bytes"] = mandatory_bytes
    if mandatory_bytes > byte_budget:
        return refuse("refused_mandatory_over_budget",
                      [{"id": "mandatory", "reason": "mandatory context exceeds the budget",
                        "bytes": mandatory_bytes}],
                      {"status": "mandatory_alone", "obligations": [], "budget": byte_budget},
                      None)
    result = minimum_cover(units, requirements, mandatory, byte_budget, state_budget)
    if result.selected is None:
        if not result.complete:
            return refuse("refused_search_incomplete", [], None, result)
        core = irreducible_budget_core(units, requirements, mandatory, byte_budget, state_budget)
        unmet = []
        for ob, req in zip(obligations, requirements):
            if req.id not in core.get("obligations", []):
                continue
            if not ob.alternatives:
                reason = "no_evidence_with_bytes"
            elif not req.alternatives:
                reason = "all_alternatives_blocked"
            else:
                reason = "budget_cannot_hold_an_alternative_with_the_rest_of_the_core"
            unmet.append({"id": req.id, "reason": reason})
        return refuse("refused_infeasible_in_declared_model", unmet, core, result)

    witnesses: dict[str, list[str]] = {}
    for req in requirements:
        inside = [a for a in req.alternatives if a <= result.selected]
        best = min(inside, key=lambda a: (set_cost(units, a), len(a), tuple(sorted(a))))
        witnesses[req.id] = sorted(best)
    selected = frozenset(mandatory).union(*[frozenset(w) for w in witnesses.values()])
    total = set_cost(units, selected)
    receipt.update(
        status="compiled",
        optimality="optimal_in_declared_model" if result.complete else "feasible_search_incomplete",
        selected=sorted(selected),
        obligations=obligation_rows(witnesses),
        bytes={"mandatory": mandatory_bytes, "total": total,
               "distinct_excerpts": len({units[r][0] for r in selected})},
        search={"states": result.states, "complete": result.complete},
    )
    manifest, excerpts, placements = build_manifest(spec, obligations, witnesses, mandatory,
                                                    eligible, tree)
    receipt["placements"] = placements
    receipt["manifest_sha256"] = ledger.sha256_hex(canonical_bytes(manifest))
    receipt["build_command"] = ("python3 tools/meta/bridge/type_b_handoff_bundle.py build "
                                f"--manifest <out>/{MANIFEST_NAME} --repo-root <out>")
    return {"status": "compiled", "receipt": receipt, "manifest": manifest, "excerpts": excerpts}


def _excerpt_path(res: Resource) -> str:
    return f"{EXCERPT_DIR}/{res.excerpt_sha256}.md"


def _output_name(res: Resource) -> str:
    stem = re.sub(r"[^A-Za-z0-9_.-]+", "_", PurePosixPath(res.path).stem)
    return f"{res.excerpt_sha256[:12]}_{stem}_L{res.start_line}-{res.end_line}.md"


def _file_spec(res_group: Sequence[Resource], role: str, covers: Sequence[str]) -> dict[str, Any]:
    head = res_group[0]
    ids = ", ".join(r.id for r in res_group)
    classes = ", ".join(sorted({r.evidence_class for r in res_group}))
    notes = (f"Resources: {ids}. Covers: {', '.join(covers) or 'mandatory context'}. "
             f"Source {head.path}:{head.start_line}-{head.end_line}, file SHA-256 "
             f"{head.file_sha256}. Evidence class: {classes}.")
    return {"path": _excerpt_path(head), "output_name": _output_name(head), "role": role,
            "notes": notes, "entry_id": head.excerpt_sha256, "content_mode": "inline"}


def build_manifest(spec: Mapping[str, Any], obligations: Sequence[Obligation],
                   witnesses: Mapping[str, Sequence[str]], mandatory: frozenset[str],
                   resources: Mapping[str, Resource], tree: ledger.SourceTree,
                   ) -> tuple[dict[str, Any], dict[str, bytes], dict[str, str]]:
    """The handoff manifest. Each distinct excerpt is placed once: top level when
    mandatory, otherwise in the first obligation bundle whose witness uses it."""
    by_sha: dict[str, list[Resource]] = {}
    for rid in sorted(mandatory | {r for w in witnesses.values() for r in w}):
        by_sha.setdefault(resources[rid].excerpt_sha256, []).append(resources[rid])
    excerpts = {_excerpt_path(group[0]): group[0].excerpt for group in by_sha.values()}
    covers: dict[str, list[str]] = {}
    for ob in obligations:
        for rid in witnesses[ob.id]:
            covers.setdefault(resources[rid].excerpt_sha256, []).append(ob.id)
    placements: dict[str, str] = {}
    top_files = []
    for sha in sorted({resources[r].excerpt_sha256 for r in mandatory},
                      key=lambda s: min(r.id for r in by_sha[s])):
        placements[sha] = "top_level"
        top_files.append(_file_spec(by_sha[sha], "mandatory target context",
                                    sorted(set(covers.get(sha, [])))))
    bundles = []
    for ob in obligations:
        files = []
        shared = []
        for sha in sorted({resources[r].excerpt_sha256 for r in witnesses[ob.id]},
                          key=lambda s: min(r.id for r in by_sha[s])):
            if sha in placements:
                shared.append(f"{_output_name(by_sha[sha][0])} ({placements[sha]})")
                continue
            placements[sha] = ob.id
            files.append(_file_spec(by_sha[sha], f"evidence for obligation {ob.id}",
                                    sorted(set(covers.get(sha, [])))))
        guidance = ob.description
        if shared:
            guidance += " Also uses excerpts placed elsewhere: " + "; ".join(shared) + "."
        if ob.notes:
            guidance += " " + " ".join(note[0].upper() + note[1:] + "." for note in ob.notes)
        bundle = {"bundle_id": ob.id, "title": _bundle_title(ob), "rank": "support",
                  "file_type_group": "source_excerpts", "guidance": guidance, "files": files,
                  "content_mode": "inline"}
        if ob.contrast is not None:
            trig = ob.contrast["triggers"]
            bundle["query_terms"] = list(trig["declarations"]) + list(trig["phrases"])
        bundles.append(bundle)
    target = spec["target"]
    commit = tree.commit or "the working tree"
    gates = [f"[{ob.contrast['id']}] {ob.contrast['uses']['return_gate']}"
             for ob in obligations if ob.contrast is not None]
    manifest = {
        "schema": MANIFEST_SCHEMA,
        "packet_id": spec["packet_id"],
        "title": spec["title"],
        "current_telos": f"Work on {target['anchor']} using the compiled evidence.",
        "authority_boundary": (
            f"Excerpts are bytes of the plectis-erdos repository at {commit}, each bound to the "
            "SHA-256 of its whole file. They carry no kernel authority by themselves; kernel "
            "acceptance comes from the pinned Lean build."),
        "receiver_instruction": (
            "Open 00_ASK_TYPE_B.md, execute it now, and return substantive work in the current "
            "response. Address every distinction listed under the disconfirming checks."),
        "output_dir": f"~/Downloads/{spec['packet_id']}",
        "bundle_formats": ["markdown", "jsonl_index"],
        "content_mode": "inline",
        "max_bundle_part_bytes": 700_000,
        "ask_type_b": {
            "decision_or_question": spec.get("question") or target["anchor"],
            "private_evidence_floor": [
                "Each excerpt names its source path, line range and the SHA-256 of its whole file.",
                "Declaration names carry the evidence class under which they were found.",
                "Each obligation bundle holds one full evidence alternative; the obligation list "
                "is authored and may be incomplete.",
            ],
            "public_research_needed": [
                "Search published literature only where the question depends on it.",
            ],
            "disconfirming_check": gates or [
                "Name any supplied excerpt whose reading the answer relies on beyond its text.",
            ],
            "output_shape_requested": [
                "For each obligation bundle, what it establishes and its evidence class.",
                "For each listed distinction, how the answer respects it.",
            ],
        },
        "readme": {
            "problem": target["anchor"],
            "what_type_b_owns": "Reasoning over the supplied excerpts and any public literature.",
            "one_line": spec["title"],
        },
        "top_level": {"files": top_files},
        "bundles": bundles,
    }
    return manifest, excerpts, {sha: place for sha, place in sorted(placements.items())}


def _bundle_title(ob: Obligation) -> str:
    if ob.contrast is not None:
        return str(ob.contrast["title"])
    return f"Obligation {ob.id}"


def write_outputs(result: Mapping[str, Any], out: Path, replace: bool = False) -> None:
    """Write excerpts, manifest and receipt. Refuses a directory holding other files."""
    out = Path(out)
    if out.exists():
        present = {p.name for p in out.iterdir()}
        foreign = sorted(present - MANAGED_NAMES)
        if foreign:
            raise SpecError(f"output directory holds unmanaged files: {foreign}")
        if present and not replace:
            raise SpecError("output directory is not empty; pass --replace to overwrite "
                            "a previous compile")
        for name in present:
            target = out / name
            if target.is_dir():
                shutil.rmtree(target)
            else:
                target.unlink()
    out.mkdir(parents=True, exist_ok=True)
    if result.get("excerpts") is not None:
        for rel, data in sorted(result["excerpts"].items()):
            path = out / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        (out / MANIFEST_NAME).write_bytes(canonical_bytes(result["manifest"]))
    (out / RECEIPT_NAME).write_bytes(canonical_bytes(result["receipt"]))


# ---------------------------------------------------------------------------
# Pre-digestion. This is a second output mode of the native packet compiler.
# Source owners remain claims, coverage, evidence, atlas, relations and journal.

DOSSIER_SCHEMA = "dossier/1"
DOSSIER_AUDIT_PROFILE = "dossier-audit/1"
DOSSIER_PROBLEMS = (68, 243, 249, 251, 257, 269, 1041, 1049)
DOSSIER_PATHS = {
    "claims": "docs/claims.json",
    "coverage": "docs/paper_lean_coverage.json",
    "atlas": "docs/declaration_atlas.json",
    "dependencies": "docs/lean_dependency_index.json",
    "evidence": "evidence/paper_evidence.json",
    "relations": "docs/research-commons/record/relations.json",
    "contrasts": "docs/research-commons/record/contrasts.json",
    "journal": "docs/research-commons/record/journal.jsonl",
    "routes": "docs/research-commons/route-memory/route_memory.json",
}
DOSSIER_BOUNDARY = (
    "A dossier inventories registered assertions and source-bound writing material. "
    "It does not prove their mathematics, completeness over all possible results, novelty, "
    "or reader benefit. 'lean' means every registered supporting declaration resolves in "
    "both the pinned source and its dependency export; the Lean build is NOT rerun here. "
    "'cited' with documentary_only=true means the source asserts the statement, not that "
    "this compiler has verified a proof. Recorded reviews and Comparator receipts retain "
    "their original scope. Null writing fields are named gaps, never invented explanations."
)


def dossier_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n").encode("utf-8")


def json_pointer(value: Any, pointer: str) -> Any:
    """Resolve an RFC 6901 pointer, with no fuzzy or basename matching."""
    if pointer == "":
        return value
    if not isinstance(pointer, str) or not pointer.startswith("/"):
        raise SpecError("JSON pointer must be empty or start with /")
    for part in pointer[1:].split("/"):
        part = part.replace("~1", "/").replace("~0", "~")
        if isinstance(value, list):
            if not re.fullmatch(r"0|[1-9][0-9]*", part):
                raise SpecError(f"invalid array pointer component: {part}")
            value = value[int(part)]
        else:
            value = value[part]
    return value


class DossierTree(ledger.SourceTree):
    """Strict immutable reads; disable the native index's worktree fallback."""

    def __init__(self, root: Path | str, ref: str = "HEAD") -> None:
        if not ref:
            raise SpecError("a dossier requires an immutable source commit")
        super().__init__(root, ref=ref, allow_uncommitted=False)

    def find_or_uncommitted(self, path: str) -> ledger.Blob | None:
        return self.find(path)


def verify_dossier_locators(value: Any, tree: DossierTree) -> int:
    """Re-resolve every structured source locator; cache parsing, never trust it."""
    documents: dict[str, Any] = {}
    file_digests: dict[str, str] = {}
    verified: set[tuple] = set()
    def visit(part: Any) -> int:
        count = 0
        if isinstance(part, dict):
            if part.get("kind") == "source_locator":
                blob = tree.read(part["path"])
                if part["path"] not in file_digests:
                    file_digests[part["path"]] = blob.sha256
                if part["commit"] != tree.commit or part["sha256"] != file_digests[part["path"]]:
                    raise SpecError("stale source locator: " + part["path"])
                key = (part["path"], part.get("json_pointer"), part.get("start_line"),
                       part.get("end_line"), part.get("selection"), part["selection_sha256"])
                if key not in verified:
                    if part.get("selection") == "file":
                        digest = file_digests[part["path"]]
                    elif "json_pointer" in part:
                        if part["path"] not in documents:
                            documents[part["path"]] = json.loads(blob.data)
                        selected = json_pointer(documents[part["path"]], part["json_pointer"])
                        digest = ledger.sha256_hex(dossier_bytes(selected))
                    else:
                        text = ledger.span_text(blob, part["start_line"], part["end_line"])
                        digest = ledger.sha256_hex(text.encode("utf-8"))
                    if digest != part["selection_sha256"]:
                        raise SpecError("source selection changed: " + part["path"])
                    verified.add(key)
                count += 1
            for child in part.values():
                count += visit(child)
        elif isinstance(part, list):
            for child in part:
                count += visit(child)
        return count
    return visit(value)


class DossierCompiler:
    """Join existing source owners without changing their claims or decisions.

    The inventory counts source records, not distinct mathematical discoveries.
    Dependency edges are read only at the resolved Git cut. They are never used
    to rank 'importance', and authored argument edges remain separately typed.
    """

    def __init__(self, root: Path | str, ref: str = "HEAD", annotations: dict | None = None):
        import hashlib
        import build_declaration_atlas as atlas_owner
        import check_lean_paper_propagation as coverage_owner
        import research_record as record_owner

        self.tree = DossierTree(root, ref)
        self.docs: dict[str, Any] = {}
        for key, path in DOSSIER_PATHS.items():
            blob = self.tree.read(path)  # Missing owners are a refusal, not an empty corpus.
            if key != "journal":
                self.docs[key] = json.loads(blob.data)
        events = record_owner.read_events_bytes(self.tree.read(DOSSIER_PATHS["journal"]).data)
        replay = record_owner.Replay()
        for event in events:
            replay.apply(event)
        if replay.errors:
            raise SpecError("pinned research journal: " + "; ".join(replay.errors))
        self.events, self.replay = events, replay
        self.json_cache = {DOSSIER_PATHS[k]: v for k, v in self.docs.items()}
        self.locator_cache: dict[tuple, dict] = {}
        self.digest_cache: dict[str, str] = {}
        self.index = ledger.DeclarationIndex(self.tree)
        self.coverage = self.docs["coverage"]
        self.claims = self.docs["claims"]["claims"]
        self.opens = self.docs["claims"].get("remaining_open_propositions", [])
        self.argument_edges = self.docs["claims"].get("machine_readable_paper", {}).get(
            "argument_graph", {}).get("edges", [])
        self.currency, self.paper_texts = coverage_owner.locate_rows(
            self.coverage, lambda path: self.tree.read(path).data.decode("utf-8"))
        self.rows = self.coverage["rows"]
        if len({r["id"] for r in self.rows}) != len(self.rows):
            raise SpecError("duplicate paper-coverage ids")
        if len({r["id"] for r in self.claims}) != len(self.claims):
            raise SpecError("duplicate claim ids")
        self.coverage_pos = {r["id"]: i for i, r in enumerate(self.rows)}
        self.claim_pos = {r["id"]: i for i, r in enumerate(self.claims)}
        self.evidence_rows: dict[str, tuple[dict, str]] = {}
        for pi, paper in enumerate(self.docs["evidence"]["papers"]):
            for ri, row in enumerate(paper["results"]):
                if row["id"] in self.evidence_rows:
                    raise SpecError("duplicate evidence row: " + row["id"])
                self.evidence_rows[row["id"]] = (row, f"/papers/{pi}/results/{ri}")
        self.dep_nodes = self.docs["dependencies"]["nodes"]
        self.by_handle = {n["handle"]: n for n in self.dep_nodes}
        if len(self.by_handle) != len(self.dep_nodes):
            raise SpecError("duplicate dependency handles")
        self.dep_pos = {n["handle"]: i for i, n in enumerate(self.dep_nodes)}
        self.by_short: dict[tuple[str, str], list[dict]] = {}
        self.by_node = {n["node_id"]: n for n in self.dep_nodes}
        self.reverse_deps: dict[int, list[tuple[int, int]]] = {}
        for node in self.dep_nodes:
            self.by_short.setdefault((node["module"], node["handle"].split(".")[-1]), []).append(node)
        for edge in self.docs["dependencies"]["edges"]:
            source, target, relation = edge
            if source not in self.by_node or target not in self.by_node:
                raise SpecError("dependency edge has an absent endpoint")
            self.reverse_deps.setdefault(target, []).append((source, relation))
        self.atlas_at = {(r["module"], r["line"]): r for r in self.docs["atlas"]["declarations"]}
        # Use the atlas owner's exact byte framing; read the source paths at the cut.
        inventory = self.tree._git("ls-tree", "-r", "--name-only", self.tree.commit, "--", "lean")
        if inventory.returncode:
            raise SpecError("cannot inventory the pinned Lean tree")
        tracked = inventory.stdout.decode("utf-8").splitlines()
        paths = []
        # Match the native inventory: each root file, then Path-sorted descendants.
        for library in ("Erdos249257", "ErdosProblems"):
            root_path = f"lean/{library}.lean"
            if root_path in tracked:
                paths.append(root_path)
            paths.extend(sorted((p for p in tracked if p.startswith(f"lean/{library}/") and p.endswith(".lean")),
                                key=PurePosixPath))
        self.atlas_inventory_matches = set(paths) == {r["path"] for r in self.docs["atlas"]["modules"]}
        digest = hashlib.sha256()
        for path in paths:
            atlas_owner._update_source_digest(digest, path, self.tree.read(path).data.decode("utf-8"))
        self.measured_fingerprint = "sha256:" + digest.hexdigest()
        self.fingerprint_matches = self.atlas_inventory_matches and (
            self.measured_fingerprint == self.docs["atlas"].get("source_fingerprint")
            == self.docs["dependencies"].get("source_fingerprint"))
        self.declaration_cache: dict[tuple[str, str | None], dict] = {}
        self.lean_files: dict[str, Any] = {}
        self.claim_problems = self._claim_problem_map()
        self.annotations = annotations
        self.annotation_rows: dict[str, dict] = {}
        if annotations is not None:
            if annotations.get("schema") != "dossier-annotations/1":
                raise SpecError("unsupported dossier annotation schema")
            if annotations.get("source_commit") != self.tree.commit:
                raise SpecError("annotation source commit differs from dossier cut")
            for row in annotations.get("rows", []):
                rid = row["id"]
                if rid not in self.coverage_pos and not (
                    rid.startswith("registry:") and rid[9:] in self.claim_pos):
                    raise SpecError("annotation names unknown result: " + rid)
                if rid in self.annotation_rows:
                    raise SpecError("duplicate annotation: " + rid)
                if row.get("review_state") not in ("candidate_editorial_synthesis", "reviewed_editorial"):
                    raise SpecError("annotation needs an explicit editorial review state")
                unknown = set(row) - {"id", "review_state", "generality", "mechanism_sentence",
                                      "hard_step", "attribution", "open_questions"}
                if unknown:
                    raise SpecError("unknown annotation fields: " + str(sorted(unknown)))
                for field, entry in row.items():
                    if field in ("id", "review_state"):
                        continue
                    if not isinstance(entry, dict) or not isinstance(entry.get("text"), str) \
                            or not entry["text"].strip() or not entry.get("sources"):
                        raise SpecError(f"{rid}.{field}: text and nonempty sources required")
                    for source in entry["sources"]:
                        self.annotation_source(source)  # Validate every field, even unused ones.
                self.annotation_rows[rid] = row

    def locator(self, path: str, start: int | None = None, end: int | None = None,
                pointer: str | None = None) -> dict:
        key = (path, start, end, pointer)
        if key in self.locator_cache:
            return self.locator_cache[key]
        blob = self.tree.read(path)
        if path not in self.digest_cache:
            self.digest_cache[path] = blob.sha256
        file_digest = self.digest_cache[path]
        result = {"kind": "source_locator", "commit": self.tree.commit,
                  "path": path, "sha256": file_digest}
        if pointer is not None:
            if path not in self.json_cache:
                self.json_cache[path] = json.loads(blob.data)
            selected = json_pointer(self.json_cache[path], pointer)
            result.update(json_pointer=pointer, selection_sha256=ledger.sha256_hex(dossier_bytes(selected)))
        elif start is None and end is None:
            result.update(selection="file", selection_sha256=file_digest)
        else:
            start = 1 if start is None else start
            end = len(blob.lines()) if end is None else end
            text = ledger.span_text(blob, start, end)
            result.update(start_line=start, end_line=end,
                          selection_sha256=ledger.sha256_hex(text.encode("utf-8")))
        self.locator_cache[key] = result
        return result

    def annotation_source(self, source: dict) -> dict:
        if not isinstance(source, dict) or set(source) - {"path", "start_line", "end_line", "must_contain"}:
            raise SpecError("invalid annotation source")
        spec = {"id": "annotation", "kind": "source_span", **source}
        if not spec.get("must_contain"):
            raise SpecError("annotation source needs a required literal")
        resource = resolve_resource(spec, self.tree, self.index)
        return self.locator(resource.path, resource.start_line, resource.end_line)

    @staticmethod
    def module_path(path: str | None) -> str | None:
        if path is None:
            return None
        if path.startswith(("lean/", "verification/", "research/")):
            return path
        if path.endswith(".lean"):
            return "lean/" + path
        return "lean/" + path.replace(".", "/") + ".lean"

    def declaration(self, name: str, path: str | None) -> dict:
        import paper_evidence as evidence_owner

        path = self.module_path(path)
        key = name, path
        if key in self.declaration_cache:
            return self.declaration_cache[key]
        node = self.by_handle.get(name)
        # Unqualified native claim names require a unique module-local match.
        if node is None and path:
            choices = [candidate for candidate in self.by_short.get((path, name.split(".")[-1]), [])
                       if candidate["handle"].endswith("." + name)]
            if len(choices) == 1:
                node = choices[0]
        result = {"requested_name": name, "requested_module": path, "locators": [],
                  "source_present": False, "dependency_index_present": False,
                  "eligible_lean": False, "gaps": [], "kernel_replay": "UNRUN"}
        if node and path and node["module"] != path:
            result["gaps"].append("dependency_module_mismatch")
            node = None
        if path is None and node:
            path = node["module"]
        if node:
            result.update(handle=node["handle"], dependency_index_present=True)
            result["locators"].append(self.locator(DOSSIER_PATHS["dependencies"],
                                                 pointer=f"/nodes/{self.dep_pos[node['handle']]}"))
        else:
            result["gaps"].append("not_in_compact_dependency_export")
        if path is not None:
            blob = self.tree.find(path)
            if blob is None:
                result["gaps"].append("source_file_missing_at_cut")
            else:
                if path not in self.lean_files:
                    self.lean_files[path] = evidence_owner.LeanFile(blob.data.decode("utf-8"))
                try:
                    resolved_name = node["handle"] if node else name
                    source_index = self.lean_files[path].index
                    if resolved_name not in source_index:
                        choices = [key for key in source_index if key.endswith("." + resolved_name)]
                        if len(choices) == 1:
                            resolved_name = choices[0]
                    # Resolve a unique suffix in this module only; never strip a fake prefix.
                    decl = evidence_owner.lean_declaration(
                        self.lean_files[path], path, resolved_name, allow_suffix=False)
                    result["resolved_source_name"] = resolved_name
                    result.update(source_present=True, source_statement=decl.statement,
                                  source_docstring=decl.docstring, line=decl.line, module=path,
                                  source_statement_sha256=ledger.sha256_hex(decl.normalised.encode("utf-8")))
                    end = min(len(blob.lines()), decl.line + max(1, len(decl.statement.splitlines())) - 1)
                    result["locators"].append(self.locator(path, decl.line, end))
                    if node and node["line"] != decl.line:
                        result["gaps"].append("dependency_coordinate_drift")
                    result["eligible_lean"] = bool(node and node["line"] == decl.line and self.fingerprint_matches)
                except (evidence_owner.EvidenceError, ValueError) as exc:
                    result["gaps"].append("source_declaration_unresolved: " + str(exc))
        else:
            result["gaps"].append("no_source_module")
        if not self.fingerprint_matches:
            result["gaps"].append("source_atlas_dependency_fingerprint_mismatch")
        self.declaration_cache[key] = result
        return result

    def _claim_problem_map(self) -> dict[str, list[int]]:
        labels: dict[str, set[int]] = {}
        for row in self.rows:
            labels.setdefault(row.get("label", ""), set()).add(row["problem"])
        declared_in_papers: dict[tuple[str, str], set[int]] = {}
        for row in self.rows:
            for declaration in row.get("lean", {}).get("declarations", []):
                key = (self.module_path(declaration.get("file")), declaration["name"].split(".")[-1])
                declared_in_papers.setdefault(key, set()).add(row["problem"])
        direct = {}
        for claim in self.claims:
            found = set(labels.get(claim.get("paper_label"), ()))
            for declaration in claim["declarations"]:
                key = (self.module_path(declaration.get("module")), declaration["name"].split(".")[-1])
                found.update(declared_in_papers.get(key, ()))
            texts = [claim["id"], claim["label"], claim["statement"], *claim.get("remaining_open_proposition_ids", [])]
            texts.extend(d.get("module", "") for d in claim["declarations"])
            for text in texts:
                for match in re.finditer(r"(?:erdos[_:/-]?|Erdos|#|erdosproblems\.com/|Erdős\s*#?)(1049|1041|269|257|251|249|243|68)(?!\d)", text, re.I):
                    found.add(int(match.group(1)))
            direct[claim["id"]] = found
        # Only one-hop explicit authored edges, not arbitrary graph transitive closure.
        seeds = {key: set(value) for key, value in direct.items()}
        for claim in self.claims:
            if not direct[claim["id"]]:
                found = set()
                for edge in self.argument_edges:
                    if edge.get("from") == claim["id"]:
                        found.update(seeds.get(edge.get("to"), ()))
                if found:
                    direct[claim["id"]] = found
        return {key: sorted(value) for key, value in direct.items()}

    def comparator(self, evidence: dict) -> list[dict]:
        """Check receipt identity fields. No transport or kernel replay is claimed."""
        answer = []
        comparator = evidence.get("comparator", {})
        for item in comparator.get("checks", []):
            path = item.get("receipt")
            row = {"entry": item.get("entry"), "declaration": item.get("declaration"),
                   "reported_status": comparator.get("status"), "locators": [],
                   "validation": "unresolved", "kernel_replay": "UNRUN",
                   "external_corpus_bytes_verified": False}
            if not path or self.tree.find(path) is None:
                row["gap"] = "receipt_missing_at_cut"
            else:
                value = json.loads(self.tree.read(path).data)
                row["locators"].append(self.locator(path, pointer=""))
                checks = {
                    "schema": value.get("schema") == "palomar_replay_receipt_v1",
                    "entry": value.get("entry") == item.get("entry"),
                    "commit": value.get("github", {}).get("sha") == comparator.get("commit"),
                    "run_id": str(value.get("github", {}).get("run_id")) == str(comparator.get("run_id")),
                    "challenge_theorem": item.get("challenge", {}).get("declaration") in value.get("theorem_names", []),
                    "recorded_outcome": value.get("verification", {}).get("outcome") == "passed",
                    "recorded_exit": value.get("exit") == 0 and value.get("process_exit") == 0,
                }
                row["identity_checks"] = checks
                row["validation"] = "receipt_fields_match" if all(checks.values()) else "receipt_fields_mismatch"
                row["scope"] = "historical recorded check; not a new verification of source-to-challenge correspondence"
            answer.append(row)
        return answer

    def _annotations(self, row: dict) -> None:
        for field in ("generality", "mechanism_sentence", "hard_step", "attribution"):
            row[field] = None
        annotation = self.annotation_rows.get(row["id"])
        if annotation:
            bindings = {}
            for field in ("generality", "mechanism_sentence", "hard_step", "attribution", "open_questions"):
                if field not in annotation:
                    continue
                value = annotation[field]
                bindings[field] = [self.annotation_source(x) for x in value["sources"]]
                if field == "open_questions":
                    row[field].append({"statement": value["text"], "basis": "editorial_annotation"})
                else:
                    row[field] = value["text"]
            row["annotation"] = {"review_state": annotation["review_state"], "field_sources": bindings,
                                 "boundary": "source-bound editorial synthesis; not generated or verified mathematics"}
        for field in ("generality", "mechanism_sentence", "hard_step", "attribution"):
            if row[field] is None:
                row["gaps"].append({"code": "writing_field_unannotated", "field": field})

    def _paper_row(self, item: dict) -> dict:
        rid = item["id"]
        locs = [self.locator(DOSSIER_PATHS["coverage"], pointer=f"/rows/{self.coverage_pos[rid]}")]
        resolved = self.currency.located.get(rid)
        row = {"id": rid, "kind": "paper_assertion", "problem": item["problem"],
               "statement": None, "statement_format": "source_tex", "gaps": [],
               "open_questions": [], "consumers": [], "source_status": item["lean"]["status"],
               "source_statement_sha256": item["statement_sha256"]}
        if resolved is None:
            row["gaps"].append({"code": "current_paper_statement_not_resolved_by_digest"})
        else:
            source = self.locator(resolved.path, resolved.line, resolved.end_line)
            locs.append(source)
            row["statement"] = ledger.span_text(self.tree.read(resolved.path), resolved.line, resolved.end_line)
            row["consumers"].append({"kind": item["side"] + "_paper", "paper_id": item["paper_id"],
                                     "locator": source})
            # Bounded adjacent text is evidence for a writer to inspect, not an inferred mechanism.
            lines = self.tree.read(resolved.path).lines()
            end = min(len(lines), resolved.end_line + 24)
            row["adjacent_context"] = {"text": ledger.span_text(self.tree.read(resolved.path), resolved.line, end),
                                       "locator": self.locator(resolved.path, resolved.line, end),
                                       "interpretation": "exact adjacent excerpt; may belong to another result"}
        evid, pointer = self.evidence_rows.get(rid, ({}, None))
        if pointer is not None:
            locs.append(self.locator(DOSSIER_PATHS["evidence"], pointer=pointer))
        evidence_current = bool(evid and evid.get("statement_sha256") == item.get("statement_sha256")
                                and resolved is not None)
        if evid and not evidence_current:
            row["gaps"].append({"code": "evidence_projection_statement_mismatch"})
        row["formal_sources"] = [self.declaration(x["name"], x.get("file"))
                                  for x in item.get("lean", {}).get("declarations", [])]
        all_lean = bool(row["formal_sources"]) and all(x["eligible_lean"] for x in row["formal_sources"])
        # A modulo-input result is never silently promoted to a proved endpoint.
        all_lean = all_lean and item["lean"]["status"] in ("exact", "exact_or_stronger", "modulo_named_input")
        all_lean = all_lean and resolved is not None and evidence_current
        expected = {d["name"]: d for d in evid.get("lean", {}).get("declarations", [])}
        for formal in row["formal_sources"]:
            old = expected.get(formal["requested_name"])
            if not old or old.get("statement_sha256") != formal.get("source_statement_sha256"):
                row["gaps"].append({"code": "recorded_formal_statement_identity_unconfirmed",
                                    "name": formal["requested_name"]})
                all_lean = False
        for formal in row["formal_sources"]:
            locs.extend(formal["locators"])
            if formal["gaps"]:
                row["gaps"].append({"code": "formal_support_gap", "name": formal["requested_name"],
                                    "details": formal["gaps"]})
        row["evidence"] = {
            "class": "lean" if all_lean else "cited", "documentary_only": not all_lean,
            "locators": locs, "kernel_replay": "UNRUN",
            "support_relation": item["lean"]["status"],
            "named_inputs": item["lean"].get("named_inputs"),
            "registered_lean_metadata": item["lean"],
            "recorded_ordinary_proof_note": evid.get("lean", {}).get("reason") if evidence_current else None,
            "recorded_comparator_checks": self.comparator(evid) if evidence_current else [],
            "scope": "recorded evidence class with source binding, not a new proof or semantic review",
        }
        if item["lean"]["status"] == "modulo_named_input":
            row["gaps"].append({"code": "named_input_remains", "detail": item["lean"]})
        row["related_claim_ids"] = [c["id"] for c in self.claims
                                    if c.get("paper_label") == item.get("label")
                                    and item["problem"] in self.claim_problems[c["id"]]]
        for claim_id in row["related_claim_ids"]:
            claim = self.claims[self.claim_pos[claim_id]]
            row["open_questions"].extend({"id": x} for x in claim.get("remaining_open_proposition_ids", []))
        self._annotations(row)
        return row

    def _claim_row(self, claim: dict, problem: int) -> dict:
        row = {"id": "registry:" + claim["id"], "kind": "registry_assertion", "problem": problem,
               "statement": claim["statement"], "statement_format": "registered_prose",
               "source_status": claim["status"], "gaps": [],
               "open_questions": [{"id": x} for x in claim.get("remaining_open_proposition_ids", [])],
               "consumers": [], "formal_sources": [self.declaration(x["name"], x.get("module"))
                                                    for x in claim["declarations"]]}
        # Registry prose often combines proved facts, limitations and open targets.
        # Declaration existence never establishes that the entire prose is proved.
        row["evidence"] = {"class": "cited", "documentary_only": True,
                           "locators": [self.locator(DOSSIER_PATHS["claims"], pointer=f"/claims/{self.claim_pos[claim['id']]}")],
                           "scope": "verbatim status-owner assertion; formal links do not verify the whole prose"}
        for i, edge in enumerate(self.argument_edges):
            if edge.get("to") == claim["id"] or edge.get("from") == claim["id"]:
                row["consumers"].append({"kind": "authored_argument_edge", "edge": edge,
                                         "locator": self.locator(DOSSIER_PATHS["claims"],
                                             pointer=f"/machine_readable_paper/argument_graph/edges/{i}")})
        self._annotations(row)
        return row

    def build(self, problem: int) -> dict:
        if problem not in DOSSIER_PROBLEMS:
            raise SpecError("unsupported dossier problem: " + str(problem))
        selected_claims = [c for c in self.claims if problem in self.claim_problems[c["id"]]]
        results = [self._paper_row(row) for row in self.rows if row["problem"] == problem]
        results.extend(self._claim_row(claim, problem) for claim in selected_claims)
        results.sort(key=lambda x: x["id"])
        own_ids = {c["id"] for c in selected_claims}
        handles = {s["handle"] for r in results for s in r["formal_sources"] if s.get("handle")}
        relationships = []
        for i, rel in enumerate(self.docs["relations"].get("rows", [])):
            if rel.get("problem") == problem:
                relationships.append({"record": rel,
                    "locator": self.locator(DOSSIER_PATHS["relations"], pointer=f"/rows/{i}"),
                    "certificate": self.declaration(rel["certificate"]["declaration"], rel["certificate"]["module"]),
                    "interpretation": "registered contextual relation; equivalence supplies neither endpoint"})
        contrasts = []
        text = "\n".join((r["statement"] or "") for r in results)
        fired = {x["id"]: x for x in ledger.triggered(self.docs["contrasts"]["rows"],
                                                    problem, text, sorted(handles))}
        for i, contrast in enumerate(self.docs["contrasts"]["rows"]):
            if contrast["id"] in fired:
                contrasts.append({"record": contrast, "matches": fired[contrast["id"]]["matched_on"],
                    "locator": self.locator(DOSSIER_PATHS["contrasts"], pointer=f"/rows/{i}"),
                    "boundary": "keep wrong and corrected readings with their stated scope; not a no-go theorem",
                    "nested_record_pointers": "reported native metadata; only structured source_locator objects are re-resolved here"})
        routes = []
        for i, route in enumerate(self.docs["routes"].get("records", [])):
            if route.get("problem") == problem:
                routes.append({"record": route,
                               "locator": self.locator(DOSSIER_PATHS["routes"], pointer=f"/records/{i}")})
        failed = [route for route in routes if route["record"].get("status") in ("failed", "refuted", "blocked", "refuted_local")]
        formal_consumers = []
        for handle in sorted(handles):
            node = self.by_handle[handle]
            for source_id, relation in sorted(self.reverse_deps.get(node["node_id"], [])):
                source = self.by_node[source_id]
                formal_consumers.append({"supplier": handle, "consumer": source["handle"],
                    "relation_bits": relation, "boundary": "recorded direct reference at the source cut; not importance or novelty",
                    "locator": self.locator(DOSSIER_PATHS["dependencies"], pointer=f"/nodes/{self.dep_pos[source['handle']]}"),
                    "edge": [source_id, node["node_id"], relation]})
        events = []
        for event in self.events:
            detail = event["detail"]
            matched = detail.get("problem") == problem or any(
                c in json.dumps(detail, ensure_ascii=False) for c in own_ids if len(c) > 8)
            if matched:
                line = event["sequence"] + 1
                events.append({"event": event, "locator": self.locator(DOSSIER_PATHS["journal"], line, line),
                               "boundary": "journal decision, not proof authority"})
        inventory = []
        for ai, a in enumerate(self.docs["atlas"]["declarations"]):
            if a.get("kind") not in ("theorem", "lemma"):
                continue
            explicit = bool(re.search(r"/Erdos" + str(problem) + r"(?:/|\.)", a["module"]))
            claimed = bool(own_ids.intersection(a.get("claim_ids", [])))
            if explicit or claimed:
                inventory.append({"id": a["id"], "name": a["name"], "module": a["module"],
                                  "line": a["line"], "generated_certificate": a.get("generated_certificate", False),
                                  "route_basis": "problem_module" if explicit else "atlas_claim_link",
                                  "atlas_pointer": f"/declarations/{ai}",
                                  "boundary": "navigation candidate; not individually admitted as a paper result"})
        opens = []
        for i, item in enumerate(self.opens):
            if item.get("open_target_claim") in own_ids or re.search(r"erdos_" + str(problem) + r"(?:_|$)", item["id"]):
                opens.append({"record": item,
                              "locator": self.locator(DOSSIER_PATHS["claims"], pointer=f"/remaining_open_propositions/{i}")})
        import collections
        gap_counts = collections.Counter(g["code"] for r in results for g in r["gaps"])
        dossier = {
            "schema": DOSSIER_SCHEMA, "audit_profile": DOSSIER_AUDIT_PROFILE,
            "problem": problem, "source_commit": self.tree.commit,
            "status": "dossier_with_named_gaps", "evidence_boundary": DOSSIER_BOUNDARY,
            "results": results,
            "landscape": {"routes": routes, "failed_routes_with_scope": failed,
                          "generalisations": [r for r in relationships if r["record"].get("relation") in ("strictly_stronger", "generalises")],
                          "relations": relationships, "contrast_guards": contrasts,
                          "open_questions": opens, "journal_events": events,
                          "formal_consumers": formal_consumers,
                          "dependency_relation_legend": self.docs["dependencies"].get("edge_relation_bit_legend", {}),
                          "failed_route_scope": "registered failed/refuted/blocked route records only; contrast corrections remain separate"},
            "declaration_inventory": inventory,
            "sources": [self.locator(path) for key, path in DOSSIER_PATHS.items() if key != "journal"],
            "coverage": {
                "paper_rows": sum(r["kind"] == "paper_assertion" for r in results),
                "registry_rows": len(selected_claims), "source_rows_not_distinct_theorems": len(results),
                "annotated_rows": sum("annotation" in r for r in results),
                "lean_index_eligible_paper_rows": sum(r["kind"] == "paper_assertion" and r["evidence"]["class"] == "lean" for r in results),
                "declaration_candidates": len(inventory), "gap_counts": dict(sorted(gap_counts.items())),
                "scope": "all registered paper rows and explicitly routed claims; declaration candidates remain uncurated",
                "unassigned_registry_claim_ids": sorted(c for c, ps in self.claim_problems.items() if not ps),
                "paper_inventory_scope": "whole registered sixteen-paper portfolio; these diagnostics are global",
                "paper_inventory_missing": self.currency.missing,
                "paper_inventory_unrowed": self.currency.unrowed,
                "paper_inventory_coordinate_drift": self.currency.drift,
                "completeness_over_all_possible_results": False,
                "global_shared_declaration_assignment": "unassigned shared declarations retained in global_inventory.json",
            },
            "annotation_input_sha256": ledger.sha256_hex(dossier_bytes(self.annotations)) if self.annotations is not None else None,
            "annotation_boundary": "optional candidate editorial input, produced after the corpus cut; not historical corpus evidence",
            "validation": {"source_atlas_dependency_fingerprints_match": self.fingerprint_matches,
                           "atlas_source_inventory_matches": self.atlas_inventory_matches,
                           "measured_source_fingerprint": self.measured_fingerprint,
                           "recorded_atlas_fingerprint": self.docs["atlas"].get("source_fingerprint"),
                           "recorded_dependency_fingerprint": self.docs["dependencies"].get("source_fingerprint"),
                           "journal_chain_valid": True, "kernel_build": "UNRUN",
                           "comparator_replay": "UNRUN", "reader_measurement": "UNRUN"},
        }
        dossier["validation"]["verified_locator_occurrences"] = verify_dossier_locators(dossier, self.tree)
        return dossier

    def global_inventory(self) -> dict:
        """Account for shared declarations without assigning mathematical scope by guess."""
        shared = [dict(id=a["id"], name=a["name"], module=a["module"], line=a["line"],
                       claim_ids=a.get("claim_ids", []), generated_certificate=a.get("generated_certificate", False))
                  for a in self.docs["atlas"]["declarations"]
                  if a.get("kind") in ("theorem", "lemma") and not any(
                      re.search(r"/Erdos" + str(p) + r"(?:/|\.)", a["module"]) for p in DOSSIER_PROBLEMS)]
        return {"schema": "dossier-global-inventory/1", "source_commit": self.tree.commit,
                "shared_theorem_candidates": shared,
                "unassigned_registry_claims": [c for c in self.claims if not self.claim_problems[c["id"]]],
                "boundary": "shared source candidates remain visible; no exhaustive semantic assignment is claimed"}


def render_dossier(dossier: dict) -> str:
    """A bounded writer's entry point; full assertions and gaps remain in JSON."""
    lines = [f"# Problem {dossier['problem']}: writer dossier", "",
             f"Source cut: `{dossier['source_commit']}`", "", DOSSIER_BOUNDARY, "",
             "## Coverage", "", json.dumps(dossier["coverage"], ensure_ascii=False, indent=2), "",
             "## Source-bound editorial cards", ""]
    for row in dossier["results"]:
        if "annotation" not in row:
            continue
        lines.extend([f"### {row['id']}", "", f"Status: {row['source_status']}; evidence: {row['evidence']['class']}.", ""])
        for field in ("generality", "mechanism_sentence", "hard_step", "attribution"):
            lines.extend([f"**{field.replace('_', ' ').capitalize()}:** {row.get(field) or 'UNANNOTATED'}", ""])
        lines.extend(["Exact statements, source hashes, declaration checks and scoped limitations are in the same JSON row.", ""])
    lines.extend(["## Results index", "", "Each entry names a source row, not an independent new result.", ""])
    for row in dossier["results"]:
        lines.append(f"- `{row['id']}` | {row['source_status']} | {row['evidence']['class']} | {len(row['gaps'])} named gaps")
    lines.extend(["", "## Open questions", ""])
    for entry in dossier["landscape"]["open_questions"]:
        lines.extend([entry["record"]["statement"], ""])
    lines.extend(["## Distinctions to retain", ""])
    for entry in dossier["landscape"]["contrast_guards"]:
        lines.extend([f"### {entry['record']['title']}", "", entry["record"]["right_reading"], ""])
    return "\n".join(lines) + "\n"


def compile_dossiers(root: Path | str, ref: str = "HEAD", problems: Sequence[int] = DOSSIER_PROBLEMS,
                     annotations: dict | None = None) -> dict[str, bytes]:
    if not problems or len(set(problems)) != len(problems) or any(type(p) is not int or p not in DOSSIER_PROBLEMS for p in problems):
        raise SpecError("dossier problems must be a nonempty distinct subset of the eight supported problems")
    compiler = DossierCompiler(root, ref, annotations)
    outputs: dict[str, bytes] = {}
    summaries = []
    for problem in sorted(problems):
        d = compiler.build(problem)
        outputs[f"{problem}.json"] = dossier_bytes(d)
        outputs[f"{problem}.md"] = render_dossier(d).encode("utf-8")
        summaries.append({"problem": problem, **d["coverage"], "validation": d["validation"]})
    outputs["global_inventory.json"] = dossier_bytes(compiler.global_inventory())
    outputs["source_manifest.json"] = dossier_bytes({
        "source_commit": compiler.tree.commit,
        "files": [{"path": path, "sha256": blob.sha256, "bytes": len(blob.data)}
                  for path, blob in sorted(compiler.tree._cache.items()) if blob is not None]})
    receipt = {"schema": "dossier-build-receipt/1", "source_commit": compiler.tree.commit,
               "compiler_sha256": ledger.sha256_hex(Path(__file__).read_bytes()),
               "record_owner_sha256": ledger.sha256_hex(Path(__file__).with_name("research_record.py").read_bytes()),
               "annotation_input_sha256": ledger.sha256_hex(dossier_bytes(annotations)) if annotations is not None else None,
               "reproducibility": "same source commit, compiler bytes and explicit annotation bytes; no time or absolute paths",
               "problems": summaries, "evidence_boundary": DOSSIER_BOUNDARY,
               "output_sha256": {name: ledger.sha256_hex(data) for name, data in sorted(outputs.items())}}
    outputs["receipt.json"] = dossier_bytes(receipt)
    return outputs


def write_dossiers(outputs: Mapping[str, bytes], out: Path, check: bool = False) -> None:
    """Refuse existing destinations; check mode is read-only and rejects extra files."""
    if out.is_symlink():
        raise SpecError("dossier destination must not be a symlink")
    if check:
        if not out.is_dir() or {p.name for p in out.iterdir()} != set(outputs):
            raise SpecError("dossier output inventory differs")
        for name, data in outputs.items():
            path = out / name
            if path.is_symlink() or not path.is_file() or path.read_bytes() != data:
                raise SpecError("dossier output differs: " + name)
        return
    if out.exists():
        raise SpecError("dossier destination already exists; use a fresh directory or --check")
    out.parent.mkdir(parents=True, exist_ok=True)
    import tempfile
    import os
    staging = Path(tempfile.mkdtemp(prefix=".dossier-", dir=out.parent))
    try:
        for name, data in outputs.items():
            if PurePosixPath(name).name != name:
                raise SpecError("unsafe dossier output name")
            (staging / name).write_bytes(data)
        # Avoid overwriting an output created while generation was in flight.
        if out.exists():
            raise SpecError("dossier destination appeared during build")
        os.rename(staging, out)
    finally:
        if staging.exists():
            shutil.rmtree(staging)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Compile a research packet under a byte budget so that every registered "
                    "distinction survives, and emit a type_b_handoff_manifest_v1. Certifies "
                    "source integrity and structural coverage only.")
    sub = parser.add_subparsers(dest="command", required=True)
    comp = sub.add_parser("compile", help="compile SPEC into --out")
    comp.add_argument("spec", type=Path)
    comp.add_argument("--out", type=Path, required=True)
    comp.add_argument("--budget", type=int, help="override the spec byte budget")
    comp.add_argument("--root", type=Path, default=ROOT, help="repository root")
    comp.add_argument("--ref", default="HEAD", help="git ref whose bytes are bound (default HEAD)")
    comp.add_argument("--worktree", action="store_true",
                      help="bind working-tree bytes instead of a git ref")
    comp.add_argument("--allow-uncommitted", action="store_true",
                      help="bind working-tree bytes for files absent at the ref, labelled as such")
    comp.add_argument("--ledger", default=ledger.LEDGER_PATH)
    comp.add_argument("--replace", action="store_true",
                      help="overwrite a previous compile in --out")
    dossier = sub.add_parser("dossier", help="compile source-pinned writer dossiers without model calls")
    dossier.add_argument("--root", type=Path, default=ROOT)
    dossier.add_argument("--ref", default="HEAD")
    dossier.add_argument("--problem", type=int, action="append", help="repeat to select; defaults to all eight")
    dossier.add_argument("--out", type=Path, required=True)
    dossier.add_argument("--annotations", type=Path, help="explicit, source-bound editorial candidate input")
    dossier.add_argument("--check", action="store_true", help="regenerate and compare without writing")
    args = parser.parse_args(argv)
    if args.command == "dossier":
        try:
            annotations = json.loads(args.annotations.read_bytes()) if args.annotations else None
            outputs = compile_dossiers(args.root, args.ref, args.problem or DOSSIER_PROBLEMS, annotations)
            write_dossiers(outputs, args.out, check=args.check)
            receipt = json.loads(outputs["receipt.json"])
            print(json.dumps({"source_commit": receipt["source_commit"], "files": len(outputs),
                              "mode": "checked" if args.check else "written",
                              "problems": [{"problem": x["problem"], "paper_rows": x["paper_rows"],
                                            "registry_rows": x["registry_rows"], "annotated_rows": x["annotated_rows"],
                                            "lean_index_eligible_paper_rows": x["lean_index_eligible_paper_rows"]}
                                           for x in receipt["problems"]]}, indent=2))
            return 0
        except (SpecError, ledger.LedgerError, OSError, ValueError, KeyError, IndexError) as exc:
            sys.stderr.write(f"compile_research_packet dossier: {exc}\n")
            return 2
    try:
        spec = load_spec(args.spec)
        result = compile_packet(spec, args.root, ref=None if args.worktree else args.ref,
                                allow_uncommitted=args.allow_uncommitted,
                                ledger_path=args.ledger, budget=args.budget)
        write_outputs(result, args.out, replace=args.replace)
    except (SpecError, ledger.LedgerError, OSError, json.JSONDecodeError) as exc:
        sys.stderr.write(f"compile_research_packet: {exc}\n")
        return 2
    receipt = result["receipt"]
    summary = {key: receipt.get(key) for key in (
        "status", "optimality", "byte_budget", "bytes", "search", "unmet_obligations",
        "infeasible_core", "blocked")}
    summary["witnesses"] = {row["id"]: row.get("witness") for row in receipt.get("obligations", [])}
    summary["evidence_boundary"] = EVIDENCE_BOUNDARY
    sys.stdout.write(json.dumps(summary, indent=2, ensure_ascii=False, sort_keys=True) + "\n")
    return 0 if result["status"] == "compiled" else 3


if __name__ == "__main__":
    raise SystemExit(main())
