#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Joint questions over the argument graph's recorded edges.

The pairwise views of the graph (implications, disguise classes, leverage)
look at one statement at a time. Some questions only have an answer for a set
of statements assumed together:

* **Joint conflict.** From ``A ⇒ ¬B`` and ``A ∧ B ⇒ G`` neither ``A`` nor ``B``
  is refuted, yet the bundle ``{A, B}`` for ``G`` can never be supplied. The
  closure of an assumed set follows the recorded reductions forward from what
  the graph supplies, fires every recorded refutation whose residuals it
  reaches, and reports a conflict when it supplies a refuted statement or
  ``False``, with both derivations and the assumptions they use.
* **Joint endpoint equivalence.** From ``A ∧ B ⇒ G``, ``G ⇒ A`` and ``G ⇒ B``
  the bundle ``{A, B}`` is ``G`` restated, although no single member is
  equivalent to ``G``. The check tests the forward route and every reverse
  direction.
* **Cheapest cut.** Within a caller-chosen pool of statements with costs, the
  cheapest set that supplies a target without a recorded conflict, paying for
  a statement shared by several routes once.

Every answer is a derivation over recorded edges (elaborator matches and
kernel-checked rows), labelled ``derivation_over_recorded_edges``; it is not a
Lean proof, and "no recorded conflict" never says the set is satisfiable.
Closures start from the graph's own fixpoint and propagate only what the
assumptions add, so their cost is the size of that difference. Budgets are
work units, never wall-clock time, so a result does not depend on the machine
that computed it; an exhausted budget reads ``unknown_budget``, never a
verdict. Costs are priorities chosen by the caller, not measured difficulty.
"""

from __future__ import annotations

import heapq
from collections import defaultdict, deque
from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Iterable

EVIDENCE = "derivation_over_recorded_edges"
CHECK_WORK_LIMIT = 200_000
CUT_POOL_LIMIT = 32


@dataclass(frozen=True)
class Rule:
    head: str
    producer: str
    reading: str
    residuals: tuple[str, ...]   # every residual of the recorded reduction or refutation
    pending: tuple[str, ...]     # the residuals the graph does not supply
    negative: bool


class Closure:
    """What an assumed set adds to the graph's fixpoint. ``positive`` and
    ``negative`` hold only the statements the assumptions add (each with the
    index of the rule that fired, ``-1`` for an assumption)."""

    def __init__(self, assumptions: frozenset[str], positive: dict[str, int], negative: dict[str, int],
                 conflicts: list[str], complete: bool, work: int):
        self.assumptions = assumptions
        self.positive = positive
        self.negative = negative
        self.conflicts = conflicts
        self.complete = complete
        self.work = work


class Frontier:
    """An index over one analysed graph. Build it again after the graph changes.
    ``supplied`` and ``refuted`` default to the graph's own; the builder passes
    others (and ``exclude_readings``) to ask the same questions of a variant of
    the graph, such as the graph without its idle reductions."""

    def __init__(self, graph: Any, *, supplied: set[str] | None = None,
                 refuted: dict[str, dict[str, Any]] | None = None,
                 exclude_readings: frozenset[str] = frozenset()):
        self.graph = graph
        supplied = graph.supplied if supplied is None else supplied
        refuted = graph.refuted if refuted is None else refuted
        self.base_positive: set[str] = supplied
        self.base_negative: dict[str, dict[str, Any]] = refuted
        self.base_conflicts: list[str] = sorted(set(refuted) & supplied)
        self.rules: list[Rule] = []
        self.watch: dict[str, list[int]] = defaultdict(list)
        for head, producer, reading, residuals in graph.reductions:
            if head in supplied or reading in exclude_readings:
                continue
            pending = tuple(sorted({r for r in residuals if r not in supplied}))
            if pending:
                self._add(Rule(head, producer, reading, tuple(residuals), pending, False))
        for statement, producer, reading, residuals in graph.refutations:
            pending = tuple(sorted({r for r in residuals if r not in supplied}))
            if pending:  # a refutation whose residuals the graph supplies has fired already
                self._add(Rule(statement, producer, reading, tuple(residuals), pending, True))
        # Exports may flag the proposition False itself; older ones render it.
        self.false_keys = {key for key, node in graph.statements.items()
                           if node.get("is_false") is True or node.get("type") == "False"
                           or "False" in node.get("aliases", ())}
        self._reverse: dict[str, Closure] = {}

    def _add(self, rule: Rule) -> None:
        index = len(self.rules)
        self.rules.append(rule)
        for residual in rule.pending:
            self.watch[residual].append(index)

    # ------------------------------------------------------------------
    # Closure and witnesses

    def is_positive(self, state: Closure, key: str) -> bool:
        return key in self.base_positive or key in state.positive

    def closure(self, assumptions: Iterable[str] = (), *, max_work: int = CHECK_WORK_LIMIT) -> Closure:
        canon = self.graph.canon
        assumed = frozenset(canon(k) for k in assumptions)
        unknown = sorted(k for k in assumed if k not in self.graph.statements)
        if unknown:
            raise ValueError(f"unknown statement keys: {unknown}")
        positive: dict[str, int] = {}
        negative: dict[str, int] = {}
        queue: deque[str] = deque()
        for key in sorted(assumed):
            if key not in self.base_positive:
                positive[key] = -1
                queue.append(key)
        remaining: dict[int, int] = {}
        work = 0
        complete = True
        while queue:
            if work >= max_work:
                complete = False
                break
            key = queue.popleft()
            work += 1
            for index in self.watch.get(key, ()):
                work += 1
                count = remaining.get(index, len(self.rules[index].pending)) - 1
                remaining[index] = count
                if count:
                    continue
                rule = self.rules[index]
                if rule.negative:
                    negative.setdefault(rule.head, index)
                elif rule.head not in positive and rule.head not in self.base_positive:
                    positive[rule.head] = index
                    queue.append(rule.head)
        conflicts = {k for k in positive
                     if k in self.base_negative or k in negative or k in self.false_keys}
        conflicts |= {k for k in negative if k in self.base_positive}
        return Closure(assumed, positive, negative, sorted(conflicts), complete, work)

    def witness(self, state: Closure, key: str, *, negative: bool = False, max_nodes: int = 32) -> dict[str, Any]:
        """The derivation of ``key`` (or of its refutation) in ``state``: a DAG
        whose leaves are assumptions and statements the graph settles by
        itself (with the graph's own witness). Truncation is reported."""
        graph = self.graph
        nodes: dict[str, Any] = {}
        truncated = False

        def visit(k: str, neg: bool) -> str:
            nonlocal truncated
            token = ("refuted:" if neg else "supplied:") + k
            if token in nodes:
                return token
            if len(nodes) >= max_nodes:
                truncated = True
                return token
            row: dict[str, Any] = {"statement": k, "type": graph.statements.get(k, {}).get("type")}
            nodes[token] = row
            if neg:
                index = state.negative.get(k)
                if index is not None:
                    rule = self.rules[index]
                    row.update({"status": "refuted_under_assumptions", "producer": rule.producer,
                                "reading": rule.reading})
                    row["from"] = [visit(r, False) for r in rule.residuals]
                elif k in self.base_negative:
                    row.update({"status": "refuted_in_graph", "refutation": self.base_negative[k]})
                elif k in self.false_keys:
                    row["status"] = "false"
                else:
                    row["status"] = "not_refuted"
                return token
            index = state.positive.get(k)
            if index == -1:
                row["status"] = "assumed"
            elif index is not None:
                rule = self.rules[index]
                row.update({"status": "supplied_under_assumptions", "producer": rule.producer,
                            "reading": rule.reading})
                row["from"] = [visit(r, False) for r in rule.residuals]
            elif k in self.base_positive:
                at = graph.witness.get(k, -1)
                row["status"] = "supplied_in_graph"
                if at >= 0:
                    row["producer"] = graph.reductions[at][1]
            else:
                row["status"] = "not_supplied"
            return token

        root = visit(key, negative)
        return {"root": root, "nodes": nodes, "truncated": truncated, "evidence_class": EVIDENCE}

    def conflict_support(self, state: Closure, key: str) -> list[str]:
        """The assumptions the two derivations of a conflict use: a set of
        assumptions that the recorded edges already make jointly impossible,
        not a claim of a smallest such set. A truncated derivation falls back
        to every assumption."""
        proofs = [self.witness(state, key, max_nodes=256)]
        if key in state.negative or key in self.base_negative:
            proofs.append(self.witness(state, key, negative=True, max_nodes=256))
        if any(proof["truncated"] for proof in proofs):
            return sorted(state.assumptions)
        return sorted({node["statement"] for proof in proofs for node in proof["nodes"].values()
                       if node.get("status") == "assumed"})

    def reverse(self, target: str, *, max_work: int = CHECK_WORK_LIMIT) -> Closure:
        """The closure of the target alone (what the target supplies), cached."""
        target = self.graph.canon(target)
        cached = self._reverse.get(target)
        if cached is None or (not cached.complete and cached.work < max_work):
            cached = self.closure([target], max_work=max_work)
            self._reverse[target] = cached
        return cached

    # ------------------------------------------------------------------
    # Questions

    def refuted_alone(self, candidates: Iterable[str], *, max_work: int = CHECK_WORK_LIMIT
                      ) -> tuple[dict[str, dict[str, Any]], dict[str, int]]:
        """The candidates whose closure alone conflicts: supplying one would
        supply a statement together with a recorded refutation of it (a
        refutation whose residuals the candidate supplies), a refuted
        statement, or False. Only candidates from which a recorded route leads
        to such a source are closed. Returns ``{key: record}`` (a refutation
        of kind ``derived_conflict``) and the closures run, their work, and
        the number the budget cut short (which say nothing)."""
        seeds = set(self.false_keys) | set(self.base_negative)
        by_head: dict[str, list[int]] = defaultdict(list)
        for index, rule in enumerate(self.rules):
            if rule.negative:
                seeds.update(rule.pending)
            else:
                by_head[rule.head].append(index)
        cone: set[str] = set()
        stack = list(seeds)
        while stack:
            node = stack.pop()
            if node in cone:
                continue
            cone.add(node)
            for index in by_head.get(node, ()):
                stack.extend(self.rules[index].pending)
        found: dict[str, dict[str, Any]] = {}
        stats = {"closures": 0, "work": 0, "incomplete": 0}
        for key in sorted(candidates):
            if key not in cone or key in self.base_positive or key in self.base_negative:
                continue
            state = self.closure([key], max_work=max_work)
            stats["closures"] += 1
            stats["work"] += state.work
            if not state.complete:
                stats["incomplete"] += 1
            if not state.conflicts:
                continue
            conflict = state.conflicts[0]
            producers: list[str] = []
            for dag in (self.witness(state, conflict), self.witness(state, conflict, negative=True)):
                for node in dag["nodes"].values():
                    producer = node.get("producer") or (node.get("refutation") or {}).get("producer")
                    if producer and producer not in producers:
                        producers.append(producer)
            refuted_by = None
            if conflict in state.negative:
                refuted_by = self.rules[state.negative[conflict]].producer
            elif conflict in self.base_negative:
                refuted_by = (self.base_negative[conflict].get("producer")
                              or self.base_negative[conflict].get("kind"))
            found[key] = {"kind": "derived_conflict", "reaches": conflict, "refuted_by": refuted_by,
                          "producers": producers[:8], "evidence_class": EVIDENCE}
        return found, stats

    def check(self, assumptions: Iterable[str], *, target: str | None = None,
              max_work: int = CHECK_WORK_LIMIT, witnesses: bool = True) -> dict[str, Any]:
        """Whether an assumed set is jointly impossible over the recorded
        edges, and, given a target, whether it supplies the target and whether
        it is the target restated (``joint_endpoint_equivalence``)."""
        if self.base_conflicts:
            return {"assumptions": sorted({self.graph.canon(k) for k in assumptions}),
                    "status": "base_graph_inconsistent", "base_conflicts": self.base_conflicts[:8],
                    "evidence_class": EVIDENCE, "satisfiability": "not_established"}
        state = self.closure(assumptions, max_work=max_work)
        status = ("refuted_jointly" if state.conflicts else
                  "no_recorded_conflict" if state.complete else "unknown_budget")
        result: dict[str, Any] = {
            "assumptions": sorted(state.assumptions), "status": status,
            "complete_for_recorded_edges": state.complete, "work": state.work,
            "evidence_class": EVIDENCE, "satisfiability": "not_established",
        }
        if state.conflicts:
            result["conflicts"] = []
            for key in state.conflicts[:4]:
                conflict: dict[str, Any] = {"statement": key,
                                            "type": self.graph.statements.get(key, {}).get("type"),
                                            "assumption_support": self.conflict_support(state, key)}
                if witnesses:
                    conflict["supplied"] = self.witness(state, key)
                    conflict["refuted"] = self.witness(state, key, negative=True)
                result["conflicts"].append(conflict)
            result["conflicts_truncated"] = len(state.conflicts) > 4
        if target is not None:
            target = self.graph.canon(target)
            if target not in self.graph.statements:
                raise ValueError(f"unknown target key {target!r}")
            supplies = self.is_positive(state, target)
            result["supplies_target"] = supplies
            if supplies and witnesses:
                result["target_witness"] = self.witness(state, target)
            reverse = self.reverse(target, max_work=max_work)
            implied = [a for a in sorted(state.assumptions) if self.is_positive(reverse, a)]
            all_implied = len(implied) == len(state.assumptions)
            result["implied_by_target"] = implied
            if supplies and all_implied:
                relation = "joint_endpoint_equivalence"
            elif (not supplies and state.complete) or (not all_implied and reverse.complete):
                # One direction is settled negatively over the recorded edges.
                relation = "not_established_by_recorded_edges"
            else:
                relation = "unknown_budget"
            result["endpoint_relation"] = relation
            if relation == "joint_endpoint_equivalence" and witnesses:
                result["reverse_witnesses"] = {a: self.witness(reverse, a) for a in implied[:4]}
        return result

    def cheapest_cut(self, target: str, costs: dict[str, Any], *, max_states: int = 10_000,
                     max_work: int = 5_000_000, exclude_equivalent: bool = False) -> dict[str, Any]:
        """The cheapest subset of a caller-chosen pool (at most 32 statements
        with nonnegative integer or rational-string costs) that supplies the
        target without a recorded conflict. A statement shared by several
        routes is paid for once; supersets of a conflicting or already
        sufficient set are pruned. Exponential in the pool in the worst case,
        with every budget exit explicit. Optimal only over this pool, these
        costs and the recorded edges."""
        graph = self.graph
        target = graph.canon(target)
        if target not in graph.statements:
            raise ValueError(f"unknown target key {target!r}")
        parsed: dict[str, Fraction] = {}
        for raw, value in costs.items():
            key = graph.canon(raw)
            if key not in graph.statements:
                raise ValueError(f"unknown candidate key {raw!r}")
            if key == target:
                raise ValueError("the target itself is not a candidate")
            if isinstance(value, (bool, float)) or not isinstance(value, (int, str)):
                raise ValueError("costs must be integers or exact rational strings")
            cost = Fraction(value)
            if cost < 0:
                raise ValueError("costs must be nonnegative")
            if key in parsed and parsed[key] != cost:
                raise ValueError(f"aliases of {key!r} have different costs")
            parsed[key] = cost
        keys = sorted(parsed)
        if len(keys) > CUT_POOL_LIMIT:
            raise ValueError(f"the pool has {len(keys)} statements; choose at most {CUT_POOL_LIMIT}")
        if self.base_conflicts:
            return {"status": "base_graph_inconsistent", "base_conflicts": self.base_conflicts[:8],
                    "evidence_class": EVIDENCE}
        weights = [parsed[k] for k in keys]
        heap: list[tuple[Fraction, tuple[int, ...]]] = [(Fraction(0), ())]
        nogoods: list[frozenset[str]] = []
        sufficient: list[frozenset[str]] = []
        states = 0
        work = 0
        excluded_equivalent = 0
        reverse = self.closure([target], max_work=max_work)
        work += reverse.work

        def answer(status: str, bound: Fraction | None, **extra: Any) -> dict[str, Any]:
            return {"status": status, "target": target, "states": states, "work": work,
                    "lower_bound": str(bound) if bound is not None else None,
                    "candidate_pool": {k: str(parsed[k]) for k in keys},
                    "optimality_scope": "finite_candidate_pool_and_recorded_edges",
                    "satisfiability": "not_established", "evidence_class": EVIDENCE,
                    "nogoods": [sorted(n) for n in nogoods[:16]],
                    "equivalent_cuts_excluded": excluded_equivalent, **extra}

        while heap:
            cost, indices = heapq.heappop(heap)
            if states >= max_states or work >= max_work:
                return answer("unknown_budget", cost, optimal=False)
            chosen = frozenset(keys[i] for i in indices)
            if any(n <= chosen for n in nogoods) or any(s <= chosen for s in sufficient):
                continue
            states += 1
            state = self.closure(chosen, max_work=max_work - work)
            work += state.work
            if state.conflicts:
                # A conflict found in a partial closure stands: closures only grow.
                nogoods.append(frozenset(self.conflict_support(state, state.conflicts[0])))
                continue
            if not state.complete:
                return answer("unknown_budget", cost, optimal=False)
            if self.is_positive(state, target):
                equivalent = all(self.is_positive(reverse, a) for a in chosen)
                if exclude_equivalent and not equivalent and not reverse.complete:
                    return answer("unknown_budget", cost, optimal=False, budget_reason="equivalence")
                sufficient.append(chosen)
                if exclude_equivalent and equivalent:
                    excluded_equivalent += 1
                    continue
                relation = ("joint_endpoint_equivalence" if equivalent else
                            "not_established_by_recorded_edges" if reverse.complete else "unknown_budget")
                return answer("optimal_recorded_cut", cost, optimal=True, cost=str(cost),
                              assumptions=sorted(chosen), endpoint_relation=relation,
                              witness=self.witness(state, target))
            start = indices[-1] + 1 if indices else 0
            for i in range(start, len(keys)):
                heapq.heappush(heap, (cost + weights[i], indices + (i,)))
        return answer("no_admissible_recorded_cut", None, optimal=False, exhaustive_within_declared_pool=True)
