#!/usr/bin/env python3
"""Build the argument-continuation projection from the kernel export.

Input: the JSON Lines stream written by ``scripts/export_argument_continuations.lean``
(the CI artifact ``argument-continuations-<sha>``, gzip or plain).

Output:

* ``docs/argument_continuations.json``: the bounded projection a reader or a
  research agent opens first (per-problem open statements, disguise classes,
  reduction frontier, leverage), with every row carrying its kernel producers;
* ``docs/argument_continuations_graph.json.gz``: the full graph.

Semantics. Everything below is computed from ``match`` rows (kernel
unification) and from theorem telescopes, never from declaration names.

* A *reduction* of a closed statement ``S`` is a corpus theorem ``T`` that
  supplies ``S`` once its residual hypotheses ``R₁ … Rₖ`` are supplied. A
  theorem with closed hypotheses and a closed conclusion is itself a
  reduction of its conclusion; an unconditional theorem is a reduction with
  no residual.
* ``S`` is *supplied* when some reduction has every residual supplied (least
  fixpoint). The witness reduction is recorded, so every supplied statement
  has a kernel proof tree.
* After supplied residuals are removed, a reduction with one residual ``A``
  is an implication ``A ⇒ S``. A strongly connected component of that graph
  with two or more open statements is a *disguise class*: its members are
  proved equivalent, so moving between them is a change of coordinates, not
  progress.
* The *bundles* of an open statement are the minimal sets of open statements
  whose supply supplies it (AND over residuals, OR over reductions, subset
  absorption, explicit budget). A member of a bundle of size two or more is
  strictly weaker than the statement it serves unless the kernel also proves
  the converse.
* The *leverage* of an open statement ``A`` is the set of open statements that
  become supplied when ``A`` is added and the fixpoint is recomputed.

The producer relation is a lower bound (see the exporter's docstring); a
statement reported open may be supplied by an argument the export did not
try. Leverage and bundles inherit that bound. Nothing here is proof
authority: the kernel theorems each row cites are.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "erdos249257-argument-continuations/1"
GRAPH_SCHEMA = "erdos249257-argument-continuation-graph/1"
DEFAULT_OUTPUT = ROOT / "docs" / "argument_continuations.json"
DEFAULT_GRAPH_OUTPUT = ROOT / "docs" / "argument_continuations_graph.json.gz"
PROBLEMS = ("68", "243", "249", "251", "257", "269", "1041", "1049")
BUNDLE_LIMIT = 24
BUNDLE_SIZE_LIMIT = 4
BUNDLE_DEPTH_LIMIT = 6
LIST_LIMIT = 40

# Declaration-name tokens used only to attribute shared-library theorems
# (namespace Erdos249257) to one of its two problems when no paper row
# attributes them. Attribution is navigation; it never changes the graph.
PROBLEM_257_TOKENS = ("Mersenne", "Half", "Greedy", "TwentyOne", "Achievement", "Seam", "Skip", "Erdos257")
PROBLEM_249_TOKENS = ("Totient", "Phi", "totient", "phi", "Erdos249")


# --------------------------------------------------------------------------
# Loading


def read_export(path: Path) -> list[dict[str, Any]]:
    opener = gzip.open if path.suffix == ".gz" else open
    rows: list[dict[str, Any]] = []
    with opener(path, "rt", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.strip():
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError as error:
                raise SystemExit(f"{path}:{line_number}: invalid JSON line: {error}") from error
    if not rows or rows[0].get("record") != "meta":
        raise SystemExit(f"{path}: export does not start with a meta record")
    if rows[0].get("schema") != "plectis-argument-continuation-export/1":
        raise SystemExit(f"{path}: unexpected export schema {rows[0].get('schema')!r}")
    if not any(row.get("record") == "summary" for row in rows):
        raise SystemExit(f"{path}: export has no summary record (truncated file?)")
    return rows


def file_digest(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> Any:
    if not path.is_file():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


# --------------------------------------------------------------------------
# Joins


def source_refs(root: Path) -> dict[str, str]:
    index = load_json(root / "docs" / "lean_dependency_index.json")
    out: dict[str, str] = {}
    if not index:
        return out
    for node in index.get("nodes", []):
        handle = node.get("handle")
        ref = node.get("source_ref")
        if handle and ref:
            out[handle] = ref
    return out


def paper_rows(root: Path) -> dict[str, list[dict[str, Any]]]:
    coverage = load_json(root / "docs" / "paper_lean_coverage.json")
    out: dict[str, list[dict[str, Any]]] = defaultdict(list)
    if not coverage:
        return out
    for row in coverage.get("rows", []):
        lean = row.get("lean") or {}
        comparator = row.get("comparator") or {}
        for declaration in lean.get("declarations", []) or []:
            name = declaration.get("name")
            if not name:
                continue
            out[name].append({
                "row": row.get("id"),
                "problem": str(row.get("problem")),
                "paper": row.get("paper_id"),
                "side": row.get("side"),
                "label": row.get("label"),
                "source": row.get("source"),
                "lean_status": lean.get("status"),
                "comparator": comparator.get("status"),
            })
    return out


def comparator_results(root: Path) -> dict[str, dict[str, Any]]:
    packet = load_json(root / "docs" / "external_verification_packet.json")
    out: dict[str, dict[str, Any]] = {}
    if not packet:
        return out
    for result in packet.get("main_results", []) or []:
        name = result.get("original_declaration")
        if name:
            out[name] = {
                "id": result.get("id"),
                "wrapper": result.get("wrapper_declaration"),
                "boundary": result.get("boundary"),
            }
    return out


def module_problem(module: str, name: str) -> str | None:
    match = re.search(r"\.Erdos(\d+)(?:\.|$)", "." + module)
    if match and match.group(1) in PROBLEMS:
        return match.group(1)
    if module.startswith("Erdos249257"):
        text = module + "." + name
        hits_257 = any(token in text for token in PROBLEM_257_TOKENS)
        hits_249 = any(token in text for token in PROBLEM_249_TOKENS)
        if hits_257 and not hits_249:
            return "257"
        if hits_249 and not hits_257:
            return "249"
        return "249_257"
    return None


# --------------------------------------------------------------------------
# Graph


class Graph:
    def __init__(self, rows: list[dict[str, Any]]):
        self.meta = rows[0] if rows else {}
        self.summary = next((row for row in rows if row.get("record") == "summary"), {})
        self.theorems: dict[str, dict[str, Any]] = {}
        self.statements: dict[str, dict[str, Any]] = {}
        # reduction: (head, producer, reading, residual keys tuple)
        self.reductions: list[tuple[str, str, str, tuple[str, ...]]] = []
        self.existential: list[dict[str, Any]] = []
        self.budget_exhausted: list[dict[str, Any]] = []
        self.caps: list[dict[str, Any]] = []
        self.errors: list[dict[str, Any]] = []
        self.alias: dict[str, str] = {}
        self._ingest(rows)

    def canon(self, key: str) -> str:
        """Representative of a statement's definitional-alias class."""
        root = key
        while self.alias.get(root, root) != root:
            root = self.alias[root]
        while self.alias.get(key, key) != root:
            self.alias[key], key = root, self.alias[key]
        return root

    @classmethod
    def from_payload(cls, payload: dict[str, Any]) -> "Graph":
        """Rebuild the graph from ``argument_continuations_graph.json.gz``."""
        graph = cls([])
        graph.meta = {"schema": payload.get("schema")}
        graph.summary = (payload.get("source") or {}).get("export_summary", {})
        for row in payload.get("statements", []):
            graph.statements[row["key"]] = {
                "key": row["key"], "type": row.get("type"), "origins": set(row.get("origins", [])),
                "consumers": set(row.get("consumers", [])), "conclusion_of": set(row.get("conclusion_of", [])),
                "constants": set(row.get("constants", [])),
                "aliases": set(row.get("aliases", [])),
            }
        for row in payload.get("reductions", []):
            graph.reductions.append((row["statement"], row["producer"], row.get("reading", "conclusion"),
                                     tuple(row.get("residuals", []))))
        for row in payload.get("theorems", []):
            graph.theorems[row["name"]] = {
                "name": row["name"], "module": row.get("module", ""),
                "hypotheses": row.get("hypotheses", []),
                "schematic_hypotheses": row.get("schematic_hypotheses", []),
                "conclusion_key": row.get("conclusion"), "conclusion_type": row.get("conclusion_type"),
                "conclusion_closed": row.get("conclusion") is not None, "data_binders": [],
                "card": {k: row[k] for k in ("source", "papers", "comparator_result", "problem") if k in row},
            }
        graph.existential = payload.get("existential_reductions", [])
        graph.budget_exhausted = payload.get("budget_exhausted", [])
        return graph

    def _statement(self, key: str, type_text: str | None, origin: str,
                   constants: Iterable[str] = ()) -> dict[str, Any]:
        representative = self.canon(key)
        if representative != key:
            node = self._statement(representative, None, origin, constants)
            if type_text:
                node["aliases"].add(type_text)
            return node
        node = self.statements.get(key)
        if node is None:
            node = {"key": key, "type": type_text, "origins": set(), "consumers": set(),
                    "conclusion_of": set(), "constants": set(), "aliases": set()}
            self.statements[key] = node
        if type_text and not node.get("type"):
            node["type"] = type_text
        node["origins"].add(origin)
        node["constants"].update(constants)
        return node

    def _ingest(self, rows: list[dict[str, Any]]) -> None:
        seen_reductions: set[tuple[str, str, str, tuple[str, ...]]] = set()
        # Definitional aliases first: a named proposition and its one-step
        # unfolding are one statement. The named side represents the class.
        unfold_types: dict[str, str] = {}
        for row in rows:
            if row.get("record") == "unfold":
                named, unfolded = self.canon(row["statement"]), self.canon(row["unfolded"])
                if named != unfolded:
                    self.alias[unfolded] = named
                unfold_types[row["unfolded"]] = row.get("type")
        canon = self.canon

        def add_reduction(head: str, producer: str, reading: str, residuals: Iterable[str]) -> None:
            head = canon(head)
            residual_tuple = tuple(sorted({canon(r) for r in residuals}))
            if head in residual_tuple:
                return  # tautological: the statement reduces to itself
            item = (head, producer, reading, residual_tuple)
            if item not in seen_reductions:
                seen_reductions.add(item)
                self.reductions.append(item)

        for row in rows:
            record = row.get("record")
            if record == "theorem":
                name = row["name"]
                binders = row.get("binders", [])
                hypotheses = [b for b in binders if b.get("kind") == "hypothesis"]
                closed = [b for b in hypotheses if b.get("closed")]
                schematic = [b for b in hypotheses if not b.get("closed")]
                conclusion = row.get("conclusion", {})
                self.theorems[name] = {
                    "name": name,
                    "module": row.get("module", ""),
                    "hypotheses": [canon(b.get("key")) for b in closed if b.get("key")],
                    "schematic_hypotheses": [b.get("type") for b in schematic],
                    "conclusion_key": canon(conclusion["key"]) if conclusion.get("key") else None,
                    "conclusion_type": conclusion.get("type"),
                    "conclusion_closed": bool(conclusion.get("closed")),
                    "data_binders": [b.get("name") for b in binders if b.get("kind") == "data"],
                }
                for binder in closed:
                    node = self._statement(binder["key"], binder.get("type"), "hypothesis")
                    node["consumers"].add(name)
                if conclusion.get("closed") and conclusion.get("key"):
                    node = self._statement(conclusion["key"], conclusion.get("type"), "conclusion",
                                           conclusion.get("constants", ()))
                    node["conclusion_of"].add(name)
                    if schematic:
                        self.existential.append({
                            "statement": canon(conclusion["key"]), "producer": name,
                            "reason": "hypothesis depends on a data binder absent from the conclusion",
                        })
                    else:
                        add_reduction(conclusion["key"], name, "theorem",
                                      [binder["key"] for binder in closed])
            elif record == "statement":
                self._statement(row["key"], row.get("type"), row.get("origin", "statement"),
                                row.get("constants", ()))
            elif record == "unfold":
                self._statement(row["unfolded"], row.get("type"), "unfolding", row.get("constants", ()))
            elif record == "match":
                status = row.get("status")
                if status != "matched":
                    self.budget_exhausted.append({
                        "statement": row.get("statement"), "producer": row.get("producer"),
                        "status": status,
                    })
                    continue
                residuals = row.get("residuals", [])
                for residual in residuals:
                    self._statement(residual["key"], residual.get("type"), "residual")
                if row.get("open_data") or any(r.get("has_open_data") for r in residuals):
                    self.existential.append({
                        "statement": canon(row["statement"]), "producer": row["producer"],
                        "reason": "producer data not determined by unification",
                        "residual_types": [r.get("type") for r in residuals],
                    })
                    continue
                add_reduction(row["statement"], row["producer"], row.get("reading", "conclusion"),
                              [r["key"] for r in residuals])
            elif record == "candidate_cap":
                self.caps.append(row)
            elif record in ("theorem_error", "statement_error"):
                self.errors.append(row)

    # ------------------------------------------------------------------
    # Supply fixpoint with witnesses

    def supply(self, extra: Iterable[str] = (), *, exclude_heads: frozenset[str] = frozenset(),
               exclude_producers: frozenset[str] = frozenset()) -> tuple[set[str], dict[str, int]]:
        def usable(index: int) -> bool:
            head, producer, _, _ = self.reductions[index]
            return head not in exclude_heads and producer not in exclude_producers

        remaining = [len(residuals) for (_, _, _, residuals) in self.reductions]
        by_residual: dict[str, list[int]] = defaultdict(list)
        for index, (_, _, _, residuals) in enumerate(self.reductions):
            if not usable(index):
                continue
            for residual in residuals:
                by_residual[residual].append(index)
        supplied: set[str] = set()
        witness: dict[str, int] = {}
        queue: list[str] = []
        for index, (head, _, _, residuals) in enumerate(self.reductions):
            if not usable(index):
                continue
            if not residuals and head not in supplied:
                supplied.add(head)
                witness[head] = index
                queue.append(head)
        for key in extra:
            if key not in supplied:
                supplied.add(key)
                witness[key] = -1
                queue.append(key)
        while queue:
            key = queue.pop()
            for index in by_residual.get(key, ()):
                remaining[index] -= 1
                if remaining[index] == 0:
                    head = self.reductions[index][0]
                    if head not in supplied:
                        supplied.add(head)
                        witness[head] = index
                        queue.append(head)
        return supplied, witness

    def analyse(self) -> None:
        self.supplied, self.witness = self.supply()
        self.open = {key for key in self.statements if key not in self.supplied}
        # Reduced reductions of open heads: residuals minus supplied.
        self.reduced: list[tuple[str, str, str, tuple[str, ...]]] = []
        for head, producer, reading, residuals in self.reductions:
            if head in self.supplied:
                continue
            left = tuple(r for r in residuals if r not in self.supplied)
            self.reduced.append((head, producer, reading, left))
        self.implies: dict[str, set[str]] = defaultdict(set)   # A -> {S}: A ⇒ S
        self.implied_by: dict[str, set[str]] = defaultdict(set)
        self.implication_producers: dict[tuple[str, str], set[str]] = defaultdict(set)
        for head, producer, _, left in self.reduced:
            if len(left) == 1:
                a = left[0]
                self.implies[a].add(head)
                self.implied_by[head].add(a)
                self.implication_producers[(a, head)].add(producer)
        self._components()
        self._by_residual_open: dict[str, list[int]] = defaultdict(list)
        for index, (_, _, _, left) in enumerate(self.reduced):
            for r in left:
                self._by_residual_open[r].append(index)

    def _components(self) -> None:
        """Tarjan's algorithm, iterative, over the implication graph."""
        index_of: dict[str, int] = {}
        low: dict[str, int] = {}
        on_stack: set[str] = set()
        stack: list[str] = []
        counter = 0
        self.component: dict[str, int] = {}
        components: list[list[str]] = []
        nodes = sorted(self.open)
        for start in nodes:
            if start in index_of:
                continue
            work = [(start, iter(sorted(self.implies.get(start, ()))))]
            index_of[start] = low[start] = counter
            counter += 1
            stack.append(start)
            on_stack.add(start)
            while work:
                node, successors = work[-1]
                advanced = False
                for successor in successors:
                    if successor not in self.open:
                        continue
                    if successor not in index_of:
                        index_of[successor] = low[successor] = counter
                        counter += 1
                        stack.append(successor)
                        on_stack.add(successor)
                        work.append((successor, iter(sorted(self.implies.get(successor, ())))))
                        advanced = True
                        break
                    if successor in on_stack:
                        low[node] = min(low[node], index_of[successor])
                if advanced:
                    continue
                work.pop()
                if work:
                    parent = work[-1][0]
                    low[parent] = min(low[parent], low[node])
                if low[node] == index_of[node]:
                    members = []
                    while True:
                        member = stack.pop()
                        on_stack.discard(member)
                        members.append(member)
                        if member == node:
                            break
                    component_id = len(components)
                    for member in members:
                        self.component[member] = component_id
                    components.append(sorted(members))
        self.components = components

    def disguise_classes(self) -> list[list[str]]:
        return [members for members in self.components if len(members) >= 2]

    # ------------------------------------------------------------------
    # Bundles and leverage

    def bundles(self, key: str) -> tuple[list[list[str]], bool]:
        """Minimal sets of open statements whose supply supplies ``key``."""
        truncated = False
        memo: dict[str, list[frozenset[str]]] = {}

        def minimise(sets: Iterable[frozenset[str]]) -> list[frozenset[str]]:
            ordered = sorted(set(sets), key=lambda s: (len(s), sorted(s)))
            kept: list[frozenset[str]] = []
            for candidate in ordered:
                if not any(existing <= candidate for existing in kept):
                    kept.append(candidate)
            return kept

        def expand(node: str, depth: int, path: frozenset[str]) -> list[frozenset[str]]:
            nonlocal truncated
            if node in self.supplied:
                return [frozenset()]
            if node in memo:
                return memo[node]
            options: list[frozenset[str]] = [frozenset([node])]
            if depth < BUNDLE_DEPTH_LIMIT:
                for head, _, _, left in self.reduced_by_head.get(node, ()):
                    if any(r in path for r in left):
                        continue  # a cycle back through the current path
                    partial: list[frozenset[str]] = [frozenset()]
                    for residual in left:
                        choices = expand(residual, depth + 1, path | {node})
                        partial = minimise(a | b for a in partial for b in choices
                                           if len(a | b) <= BUNDLE_SIZE_LIMIT)
                        if len(partial) > BUNDLE_LIMIT:
                            partial = partial[:BUNDLE_LIMIT]
                            truncated = True
                        if not partial:
                            break
                    options.extend(partial)
                    if len(options) > 4 * BUNDLE_LIMIT:
                        truncated = True
                        break
            result = minimise(options)
            if len(result) > BUNDLE_LIMIT:
                result = result[:BUNDLE_LIMIT]
                truncated = True
            if depth == 0 or not truncated:
                memo[node] = result
            return result

        found = expand(key, 0, frozenset())
        out = [sorted(bundle) for bundle in found if bundle != frozenset([key])]
        return out, truncated

    @property
    def reduced_by_head(self) -> dict[str, list[tuple[str, str, str, tuple[str, ...]]]]:
        cached = getattr(self, "_reduced_by_head", None)
        if cached is None:
            cached = defaultdict(list)
            for item in self.reduced:
                cached[item[0]].append(item)
            self._reduced_by_head = cached
        return cached

    def leverage(self, key: str, limit: int = 100000) -> set[str]:
        """Open statements supplied once ``key`` is supplied."""
        if key in self.supplied:
            return set()
        remaining: dict[int, int] = {}
        gained = {key}
        queue = [key]
        steps = 0
        while queue and steps < limit:
            node = queue.pop()
            steps += 1
            for index in self._by_residual_open.get(node, ()):
                count = remaining.get(index)
                if count is None:
                    count = len(self.reduced[index][3])
                count -= 1
                remaining[index] = count
                if count == 0:
                    head = self.reduced[index][0]
                    if head not in gained:
                        gained.add(head)
                        queue.append(head)
        gained.discard(key)
        return gained

    def criticality(self, *, statement: str | None = None, producer: str | None = None) -> set[str]:
        """Supplied statements that lose every kernel witness chain when the
        given statement is no longer supplied, or the given theorem is
        withdrawn: the answer to "what fails without it"."""
        supplied, _ = self.supply(
            exclude_heads=frozenset([statement]) if statement else frozenset(),
            exclude_producers=frozenset([producer]) if producer else frozenset())
        lost = self.supplied - supplied
        if statement:
            lost.discard(statement)
        return lost

    def proof_tree(self, key: str, depth: int = 0, limit: int = 6) -> dict[str, Any]:
        index = self.witness.get(key)
        node: dict[str, Any] = {"statement": key, "type": self.statements.get(key, {}).get("type")}
        if index is None:
            node["status"] = "open"
            return node
        if index < 0:
            node["status"] = "assumed"
            return node
        head, producer, reading, residuals = self.reductions[index]
        node["producer"] = producer
        node["reading"] = reading
        if depth < limit:
            node["from"] = [self.proof_tree(r, depth + 1, limit) for r in residuals]
        elif residuals:
            node["from_truncated"] = list(residuals)
        return node


def dependency_handles(root: Path) -> dict[str, str]:
    """source_ref (lean/<module>:<line>) -> fully qualified declaration name."""
    index = load_json(root / "docs" / "lean_dependency_index.json")
    out: dict[str, str] = {}
    if not index:
        return out
    for node in index.get("nodes", []):
        if node.get("source_ref") and node.get("handle"):
            out[node["source_ref"]] = node["handle"]
    return out


def semantic_nodes(root: Path) -> list[dict[str, Any]]:
    path = root / "docs" / "semantic_corpus.json.gz"
    if not path.is_file():
        return []
    with gzip.open(path, "rt", encoding="utf-8") as handle:
        return json.load(handle).get("statement_nodes", [])


def kernel_status(graph: "Graph", name: str) -> str | None:
    theorem = graph.theorems.get(name)
    if theorem is None:
        return None
    closed = theorem.get("hypotheses", [])
    if not closed:
        return "unconditional"
    if any(k not in graph.supplied for k in closed):
        return "conditional_on_open"
    return "conditional_on_supplied"


def compositions(graph: "Graph", papers: dict[str, list[dict[str, Any]]]) -> list[dict[str, Any]]:
    """Statements the graph supplies only by chaining a conditional theorem
    with hypotheses that other theorems prove: the corpus holds every piece,
    and no single declaration states the composed result."""
    direct = {head for (head, _, _, residuals) in graph.reductions if not residuals}
    out = []
    for key in sorted(graph.supplied):
        if key in direct:
            continue
        index = graph.witness.get(key, -1)
        if index < 0:
            continue
        head, producer, reading, residuals = graph.reductions[index]
        suppliers = []
        for residual in residuals:
            w = graph.witness.get(residual, -1)
            suppliers.append({"statement": residual, "type": graph.statements.get(residual, {}).get("type"),
                              "supplied_by": graph.reductions[w][1] if w >= 0 else None})
        out.append({
            "statement": key,
            "type": graph.statements[key].get("type"),
            "via": producer,
            "reading": reading,
            "hypotheses_supplied_by": suppliers,
            "paper_rows_of_conditional_theorem": papers.get(producer, []),
        })
    out.sort(key=lambda row: (not row["paper_rows_of_conditional_theorem"], row["via"]))
    return out


def audit_authored_layers(graph: "Graph", root: Path) -> dict[str, Any]:
    """Check the authored navigation layers against the kernel graph."""
    handles = dependency_handles(root)
    rows = []
    counts: dict[str, int] = defaultdict(int)
    for node in semantic_nodes(root):
        label = node.get("logical_class")
        if label in (None, "infrastructure", "finite_instance", "generated_certificate_instance"):
            continue
        statuses = []
        for evidence in node.get("evidence", []) or []:
            handle = handles.get(f"lean/{evidence.get('module')}:{evidence.get('line')}")
            status = kernel_status(graph, handle) if handle else None
            if status:
                statuses.append((handle, status))
        if not statuses:
            counts["unresolved_evidence"] += 1
            continue
        if label == "conditional_implication":
            if all(status != "conditional_on_open" for _, status in statuses):
                verdict = "conditional_label_but_no_open_kernel_hypothesis"
            else:
                verdict = "consistent"
        elif label == "unconditional_object_theorem":
            if any(status == "conditional_on_open" for _, status in statuses):
                verdict = "unconditional_label_but_open_kernel_hypothesis"
            else:
                verdict = "consistent"
        else:
            verdict = "not_audited_class"
        counts[f"{label}:{verdict}"] += 1
        if verdict not in ("consistent", "not_audited_class"):
            rows.append({"node": node.get("id"), "logical_class": label, "verdict": verdict,
                         "declarations": [{"name": h, "kernel_status": st} for h, st in statuses]})
    frontier = load_json(root / "docs" / "semantic" / "frontier.json") or {}
    antecedent_rows = []
    for antecedent in frontier.get("open_antecedents", []) or []:
        constants = set(antecedent.get("lean_constants") or [])
        if not constants:
            continue
        hits = [k for k, n in graph.statements.items()
                if any(c in constants or any(c.endswith("." + x) for x in constants) for c in n.get("constants", ()))]
        statuses = sorted({"supplied" if k in graph.supplied else "open" for k in hits})
        antecedent_rows.append({"id": antecedent.get("id"), "lean_constants": sorted(constants),
                                "kernel_statements": len(hits), "kernel_statuses": statuses,
                                "verdict": ("authored_open_but_kernel_supplied" if statuses == ["supplied"]
                                            else "consistent" if "open" in statuses else "not_found_in_graph")})
    return {"semantic_logical_class": {"counts": dict(sorted(counts.items())), "disagreements": rows[:200],
                                       "disagreement_count": len(rows)},
            "frontier_open_antecedents": antecedent_rows}


# --------------------------------------------------------------------------
# Projection


def build(export_path: Path, root: Path = ROOT) -> tuple[dict[str, Any], dict[str, Any]]:
    rows = read_export(export_path)
    graph = Graph(rows)
    graph.analyse()
    refs = source_refs(root)
    papers = paper_rows(root)
    comparator = comparator_results(root)

    def theorem_problem(name: str) -> str | None:
        rows_for = papers.get(name) or []
        problems = sorted({row["problem"] for row in rows_for if row.get("problem")})
        if problems:
            return problems[0] if len(problems) == 1 else "cross"
        theorem = graph.theorems.get(name)
        return module_problem(theorem["module"] if theorem else "", name)

    theorem_problems = {name: theorem_problem(name) for name in graph.theorems}
    statement_problems: dict[str, set[str]] = defaultdict(set)
    for key, node in graph.statements.items():
        for name in node["consumers"] | node["conclusion_of"]:
            problem = theorem_problems.get(name)
            if problem:
                statement_problems[key].add(problem)
    for head, producer, _, residuals in graph.reductions:
        problem = theorem_problems.get(producer)
        if problem:
            statement_problems[head].add(problem)
            for residual in residuals:
                statement_problems[residual].add(problem)

    def theorem_card(name: str) -> dict[str, Any]:
        card: dict[str, Any] = {"name": name, "source": refs.get(name)}
        if papers.get(name):
            card["papers"] = papers[name]
        if comparator.get(name):
            card["comparator_result"] = comparator[name]
        return card

    def statement_card(key: str, *, with_bundles: bool = False) -> dict[str, Any]:
        node = graph.statements[key]
        card: dict[str, Any] = {
            "key": key,
            "type": node.get("type"),
            "status": "supplied" if key in graph.supplied else "open",
            "problems": sorted(statement_problems.get(key, ())),
            "consumed_by": sorted(node["consumers"])[:12],
            "consumer_count": len(node["consumers"]),
        }
        if key in graph.supplied:
            index = graph.witness.get(key, -1)
            if index >= 0:
                card["supplied_by"] = graph.reductions[index][1]
        else:
            reductions = graph.reduced_by_head.get(key, [])
            card["reductions"] = [
                {"producer": producer, "reading": reading, "open_residuals": list(left)}
                for (_, producer, reading, left) in reductions[:12]
            ]
            card["reduction_count"] = len(reductions)
            component = graph.component.get(key)
            if component is not None and len(graph.components[component]) >= 2:
                card["disguise_class"] = component
            gained = graph.leverage(key)
            card["leverage"] = len(gained)
            if with_bundles:
                bundles, truncated = graph.bundles(key)
                card["bundles"] = bundles
                card["bundles_truncated"] = truncated
        return card

    # Per-problem open sinks: open statements with at least one reduction into
    # them and no open statement they imply outside their own class.
    per_problem: dict[str, Any] = {}
    for problem in PROBLEMS + ("249_257", "cross"):
        keys = [k for k in graph.open if problem in statement_problems.get(k, ())]
        if not keys:
            continue
        sinks = []
        for key in keys:
            if not graph.reduced_by_head.get(key):
                continue
            component = graph.component.get(key)
            escapes = [s for s in graph.implies.get(key, ()) if graph.component.get(s) != component]
            if not escapes:
                sinks.append(key)
        sinks.sort(key=lambda k: (-len(graph.reduced_by_head.get(k, [])), graph.statements[k].get("type") or ""))
        levered = sorted(keys, key=lambda k: (-len(graph.leverage(k)), k))
        classes = sorted({graph.component[k] for k in keys
                          if graph.component.get(k) is not None
                          and len(graph.components[graph.component[k]]) >= 2})
        per_problem[problem] = {
            "open_statements": len(keys),
            "supplied_statements": sum(1 for k in graph.supplied if problem in statement_problems.get(k, ())),
            "sinks": [statement_card(k, with_bundles=True) for k in sinks[:LIST_LIMIT]],
            "sink_count": len(sinks),
            "highest_leverage": [statement_card(k) for k in levered[:LIST_LIMIT]],
            "disguise_classes": [
                {"class": c, "size": len(graph.components[c]),
                 "members": [{"key": m, "type": graph.statements[m].get("type")}
                             for m in graph.components[c][:LIST_LIMIT]]}
                for c in classes[:LIST_LIMIT]
            ],
        }

    conditional = [name for name, t in graph.theorems.items() if t["hypotheses"]]
    composed = compositions(graph, papers)
    audit = audit_authored_layers(graph, root)
    summary = {
        "theorems": len(graph.theorems),
        "conditional_arguments": len(conditional),
        "closed_statements": len(graph.statements),
        "supplied_statements": len(graph.supplied),
        "open_statements": len(graph.open),
        "reductions": len(graph.reductions),
        "implications_between_open_statements": sum(len(v) for v in graph.implies.values()),
        "disguise_classes": len(graph.disguise_classes()),
        "largest_disguise_class": max((len(c) for c in graph.disguise_classes()), default=0),
        "existential_reductions": len(graph.existential),
        "budget_exhausted_attempts": len(graph.budget_exhausted),
        "candidate_caps": len(graph.caps),
        "export_errors": len(graph.errors),
        "export_truncated": bool(graph.summary.get("truncated")),
        "compositions": len(composed),
        "compositions_of_paper_cited_conditional_theorems": sum(
            1 for row in composed if row["paper_rows_of_conditional_theorem"]),
        "semantic_label_disagreements": audit["semantic_logical_class"]["disagreement_count"],
    }
    source = {
        "export_digest": file_digest(export_path),
        "export_schema": graph.meta.get("schema"),
        "lean_version": graph.meta.get("lean_version"),
        "export_summary": {k: v for k, v in graph.summary.items() if k != "record"},
        "export_config": {k: graph.meta.get(k) for k in
                          ("roots", "name_prefixes", "match_heartbeats_thousands",
                           "max_candidates", "max_statements", "time_budget_ms")},
    }
    projection = {
        "schema": SCHEMA,
        "artifact_role": "generated_argument_graph_projection",
        "authority_posture": (
            "kernel-unification producer relation (a lower bound) joined to papers and Comparator "
            "results; navigation and planning evidence, not proof authority: the cited kernel "
            "theorems are"),
        "semantics": {
            "reduction": "a corpus theorem that supplies the statement once its residual hypotheses are supplied",
            "supplied": "least fixpoint over reductions; every supplied statement has a kernel witness chain",
            "implication": "a reduction left with exactly one open residual",
            "disguise_class": "strongly connected component of implications with two or more open statements: provably equivalent statements",
            "bundle": "a minimal set of open statements whose supply supplies the statement",
            "leverage": "number of open statements supplied once the statement is supplied",
            "sink": "an open statement with a reduction into it that implies nothing outside its own class",
            "composition": "a statement supplied only by chaining a conditional theorem with hypotheses other theorems prove",
            "audit": "authored logical classes and open antecedents checked against the kernel graph",
        },
        "source": source,
        "summary": summary,
        "problems": per_problem,
        "compositions": composed[:LIST_LIMIT * 3],
        "audit": audit,
    }
    graph_payload = {
        "schema": GRAPH_SCHEMA,
        "source": source,
        "statements": [
            {
                "key": key,
                "type": node.get("type"),
                "origins": sorted(node["origins"]),
                "status": "supplied" if key in graph.supplied else "open",
                "problems": sorted(statement_problems.get(key, ())),
                "consumers": sorted(node["consumers"]),
                "conclusion_of": sorted(node["conclusion_of"]),
                "constants": sorted(node.get("constants", ())),
                "aliases": sorted(node.get("aliases", ())),
                "component": graph.component.get(key),
                "witness": (graph.reductions[graph.witness[key]][1]
                            if graph.witness.get(key, -1) >= 0 else None),
            }
            for key, node in sorted(graph.statements.items())
        ],
        "reductions": [
            {"statement": head, "producer": producer, "reading": reading, "residuals": list(residuals)}
            for head, producer, reading, residuals in graph.reductions
        ],
        "existential_reductions": graph.existential,
        "budget_exhausted": graph.budget_exhausted,
        "theorems": [
            {**theorem_card(name), "module": t["module"], "problem": theorem_problems.get(name),
             "hypotheses": t["hypotheses"], "schematic_hypotheses": t["schematic_hypotheses"],
             "conclusion": t["conclusion_key"], "conclusion_type": t["conclusion_type"]}
            for name, t in sorted(graph.theorems.items())
        ],
    }
    return projection, graph_payload


def write_outputs(projection: dict[str, Any], graph_payload: dict[str, Any],
                  output: Path, graph_output: Path) -> None:
    output.write_text(json.dumps(projection, indent=1, ensure_ascii=False, sort_keys=False) + "\n",
                      encoding="utf-8")
    data = json.dumps(graph_payload, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    with graph_output.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as handle:
        handle.write(data)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--export", type=Path, required=True,
                        help="export stream (.jsonl or .jsonl.gz) from export_argument_continuations.lean")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--graph-output", type=Path, default=DEFAULT_GRAPH_OUTPUT)
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root for the joins")
    args = parser.parse_args(argv)
    projection, graph_payload = build(args.export, args.root)
    write_outputs(projection, graph_payload, args.output, args.graph_output)
    summary = projection["summary"]
    print(json.dumps({"output": str(args.output), "graph_output": str(args.graph_output), **summary}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
