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
  ``contrast:<id>`` replaces the derived one.
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
               "include_triggered_contrasts", "contrasts", "state_budget", "declaration_window"}
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
               "excerpt_sha256": self.excerpt_sha256, "bytes": self.cost,
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
                    available_at=available_at, role=row.get("role"), window_capped=capped)


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
                if blocked[other].startswith(("overlaps_", "same_bytes_")):
                    continue
                source = resources[other]
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
    args = parser.parse_args(argv)
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
