#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Interface chains: what a theorem needs of a hypothesis, level by level.

A kernel-checked weakening row says that the proof of a theorem ``T`` uses its
closed hypothesis ``h : H`` only through use sites proving the consequences
``C₁ … Cₖ``: the kernel checked ``H → Cᵢ`` for each, and ``T`` with ``H``
replaced by the ``Cᵢ``. Each ``Cᵢ`` records the lemmas applied at its use
sites (``via``). When such a lemma ``V`` has a kernel-checked weakening of its
own, and the export matched ``V``'s weakened theorem against ``Cᵢ`` (a
recorded reduction ``Cᵢ ← D₁ … Dₘ``), then ``T`` needs of ``H`` only what ``V``
needs of it at that site: the ``Dⱼ``. The chain follows these refinements down
through the lemmas.

Levels. Level 0 is ``{H}``, level 1 the consequences of the weakening row.
Level ``k + 1`` replaces every member of level ``k`` that has a recorded
refinement by the refinement's statements (the weakened lemma's consequences,
and any other obligation the match left), keeps the members without one, and
then lists as *implied* (and drops) a member whose own refinement lies inside
the rest of the level. By induction each level is a set of statements from
which ``T``'s conclusion follows, given ``T``'s other obligations: a candidate
cut point. The levels depend only on the recorded refinements, so they stay
put when a member is proved; statuses (supplied, refuted, open) lie over them.
Every level is kept, not only the deepest, because the useful cut is often in
the middle: the deepest level can be the hypothesis itself in other words. The
chain stops when no member refines, when a level repeats (a cycle through
statement keys), or at the depth limit (``truncated``).

Every refinement is a reduction the export recorded (the elaborator's unifier
matched a kernel-checked weakened theorem); a lemma in ``via`` whose weakened
theorem the export did not match against the member is listed under
``unmatched`` and never used. Each level also carries its joint check over the
recorded edges (``argument_graph_frontier.py``): whether its open members are
jointly impossible (then ``H``, which implies each member where the kernel
checked it, is refuted along with them), and whether the level implies ``H``
back (the level restates the hypothesis rather than weakening it). The
evidence class is ``derivation_over_recorded_edges``: navigation, not a proof;
the kernel theorems each step cites are.
"""

from __future__ import annotations

from collections import defaultdict
from typing import Any

EVIDENCE = "derivation_over_recorded_edges"
DEPTH_LIMIT = 8
NODE_LIMIT = 96
CLOSURE_WORK_LIMIT = 50_000


class Interfaces:
    """Interface chains over one analysed graph (build it again after the
    graph changes). ``chain(entry)`` takes an entry of ``graph.weakenings``."""

    def __init__(self, graph: Any):
        self.graph = graph
        self.rows_by_theorem: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for entry in graph.weakenings:
            if entry.get("weakened") and entry.get("consequences"):
                self.rows_by_theorem[entry["theorem"]].append(entry)
        for rows in self.rows_by_theorem.values():
            rows.sort(key=lambda e: (e.get("i") if isinstance(e.get("i"), int) else -1, e.get("weakened") or ""))
        weakened_names = {e["weakened"] for rows in self.rows_by_theorem.values() for e in rows}
        # (statement, weakened theorem) -> residual sets of the recorded matches
        self.matches: dict[tuple[str, str], list[tuple[str, ...]]] = defaultdict(list)
        for head, producer, _, residuals in graph.reductions:
            if producer in weakened_names:
                self.matches[(head, producer)].append(residuals)
        self._chains: dict[tuple[str, Any, str], dict[str, Any]] = {}
        self._needed_by: dict[str, list[dict[str, Any]]] | None = None

    # ------------------------------------------------------------------
    # Refinement of one member

    def refinements(self, key: str, record: dict[str, Any], hypothesis: str) -> tuple[list[dict], list[dict]]:
        """The recorded refinements of ``key`` (a consequence with ``record``,
        derived from ``hypothesis``), and the lemmas in ``via`` that give
        none, with the reason."""
        options: list[dict[str, Any]] = []
        unmatched: list[dict[str, Any]] = []
        for lemma in sorted(set(record.get("via") or [])):
            rows = self.rows_by_theorem.get(lemma, ())
            for row in rows:
                name = row["weakened"]
                matched = self.matches.get((key, name))
                if not matched:
                    unmatched.append({"lemma": lemma, "i": row.get("i"), "weakened": name,
                                      "reason": "no recorded match of the weakened lemma against this statement"})
                    continue
                own = {c["key"]: c for c in row["consequences"]}
                for residuals in matched:
                    if hypothesis in residuals or row.get("hypothesis") in residuals:
                        unmatched.append({"lemma": lemma, "i": row.get("i"), "weakened": name,
                                          "reason": "the match still needs the hypothesis"})
                        continue
                    into = [r for r in residuals if r in own]
                    side = [r for r in residuals if r not in own]
                    option = {"lemma": lemma, "i": row.get("i"), "weakened": name,
                              "lemma_hypothesis": row.get("hypothesis"), "into": into, "side": side,
                              "records": {r: {**own[r], "row_theorem": lemma,
                                              "row_hypothesis": row.get("hypothesis")} for r in into}}
                    if not any(o["into"] == into and o["side"] == side for o in options):
                        options.append(option)
        return options, unmatched

    # ------------------------------------------------------------------
    # Chains

    def chain(self, entry: dict[str, Any]) -> dict[str, Any]:
        token = (entry.get("theorem"), entry.get("i"), entry.get("weakened") or "")
        cached = self._chains.get(token)
        if cached is None:
            cached = self._chains[token] = self._chain(entry)
        return cached

    def chains(self) -> list[dict[str, Any]]:
        return [self.chain(entry) for rows in (self.rows_by_theorem[t] for t in sorted(self.rows_by_theorem))
                for entry in rows]

    def chains_of(self, theorem: str) -> list[dict[str, Any]]:
        return [self.chain(entry) for entry in self.rows_by_theorem.get(theorem, ())]

    def _chain(self, entry: dict[str, Any]) -> dict[str, Any]:
        graph = self.graph
        frontier = graph.frontier()
        hypothesis = entry.get("hypothesis")
        records: dict[str, dict[str, Any]] = {}
        for c in entry["consequences"]:
            records.setdefault(c["key"], {**c, "row_theorem": entry["theorem"], "row_hypothesis": hypothesis})
        chosen: dict[str, dict[str, Any] | None] = {}
        alternatives: dict[str, int] = {}
        unmatched_of: dict[str, list[dict[str, Any]]] = {}
        levels: list[dict[str, Any]] = [{
            "level": 0, "members": [self._member(hypothesis, None, None)] if hypothesis else [],
            "implied": [], **self._level_status([hypothesis] if hypothesis else [])}]
        current = sorted({c["key"] for c in entry["consequences"]})
        entered_by: dict[str, dict[str, Any] | None] = {k: None for k in current}
        seen = {frozenset([hypothesis])} if hypothesis else set()
        truncated = cycle = False
        depth = 1
        conclusion = entry.get("conclusion")
        conclusion_closure = frontier.closure([conclusion], max_work=CLOSURE_WORK_LIMIT) \
            if conclusion in graph.statements else None
        while True:
            for key in current:
                if key not in chosen:
                    record = records.get(key)
                    options, unmatched = self.refinements(key, record, hypothesis) if record else ([], [])
                    chosen[key] = options[0] if options else None
                    alternatives[key] = len(options)
                    unmatched_of[key] = unmatched
                    for option in options:
                        for child, child_record in option["records"].items():
                            records.setdefault(child, child_record)
            essential, implied = self._minimise(current, chosen)
            signature = frozenset(essential)
            if signature in seen:
                cycle = True  # a level repeats through statement keys: stop before listing it again
                break
            seen.add(signature)
            level = {"level": depth,
                     "members": [self._member(k, records.get(k), entered_by.get(k)) for k in essential],
                     "implied": implied, **self._level_status(essential)}
            level["joint"] = self._joint(essential, hypothesis, conclusion_closure)
            levels.append(level)
            if depth >= DEPTH_LIMIT:
                truncated = any(chosen.get(k) for k in essential)
                break
            following: set[str] = set()
            changed = False
            for key in essential:
                option = chosen[key]
                if option is None:
                    following.add(key)
                    continue
                changed = True
                for child in option["into"] + option["side"]:
                    following.add(child)
                    entered_by.setdefault(child, {"lemma": option["lemma"], "weakened": option["weakened"],
                                                  "refines": key})
            if not changed:
                break
            if len(records) > NODE_LIMIT:
                truncated = True
                break
            current = sorted(following)
            depth += 1
        for level in levels:
            for member in level["members"]:
                key = member["key"]
                if key in chosen and chosen[key] is not None:
                    option = chosen[key]
                    member["refined_by"] = {"lemma": option["lemma"], "weakened": option["weakened"],
                                            "into": option["into"], "side_obligations": option["side"]}
                    if alternatives.get(key, 0) > 1:
                        member["other_refinements"] = alternatives[key] - 1
                if unmatched_of.get(key):
                    member["unmatched"] = unmatched_of[key][:4]
        theorem = graph.theorems.get(entry["theorem"], {})
        return {
            "theorem": entry["theorem"], "i": entry.get("i"), "weakened": entry.get("weakened"),
            "hypothesis": self._member(hypothesis, None, None) if hypothesis else None,
            "conclusion": ({"key": conclusion, "type": graph.statements.get(conclusion, {}).get("type"),
                            "status": graph.status(conclusion)}
                           if conclusion in graph.statements else
                           {"key": None, "type": theorem.get("conclusion_type"), "status": "schematic"}),
            "other_obligations": [{"key": k, "type": graph.statements.get(k, {}).get("type"),
                                   "status": graph.status(k)} for k in entry.get("other_obligations", [])],
            "schematic_obligations": bool(entry.get("schematic_obligations")),
            "levels": levels, "depth": len(levels) - 1, "truncated": truncated, "cycle": cycle,
            "evidence_class": EVIDENCE,
        }

    def _member(self, key: str, record: dict[str, Any] | None, entered: dict[str, Any] | None) -> dict[str, Any]:
        graph = self.graph
        node = graph.statements.get(key, {})
        status = graph.status(key) if key in graph.statements else "unknown"
        member: dict[str, Any] = {"key": key, "type": node.get("type"), "status": status}
        if record is not None:
            member["via"] = list(record.get("via") or [])
            member["kernel_checked_from"] = (record.get("row_hypothesis")
                                             if record.get("implication_kernel_checked") else None)
        if entered:
            member["entered_by"] = entered
        if status == "supplied":
            at = graph.witness.get(key, -1)
            if at >= 0:
                member["supplied_by"] = graph.reductions[at][1]
        elif status == "refuted":
            member["refutation"] = graph.refuted.get(key)
        else:
            producers = []
            for _, producer, reading, left in graph.reduced_by_head.get(key, [])[:6]:
                producers.append({"producer": producer, "reading": reading, "open_residuals": list(left)})
            member["producers"] = producers
            member["producer_count"] = len(graph.reduced_by_head.get(key, []))
        return member

    def _level_status(self, keys: list[str]) -> dict[str, Any]:
        graph = self.graph
        refuted = [k for k in keys if k in graph.refuted]
        open_ = [k for k in keys if k not in graph.supplied and k not in graph.refuted]
        status = "blocked" if refuted else "open" if open_ else "satisfied"
        return {"status": status, "open": open_, "refuted": refuted}

    def _minimise(self, keys: list[str], chosen: dict[str, dict[str, Any] | None]
                  ) -> tuple[list[str], list[dict[str, Any]]]:
        """Drop a member whose own refinement lies inside the rest of the
        level: the weakened lemma at its use site supplies it from the other
        members, so the level without it still suffices. Levels depend only on
        the recorded refinements, never on what the graph supplies, so they do
        not move when a member is proved; the statuses lie over them."""
        graph = self.graph
        essential = list(keys)
        implied: list[dict[str, Any]] = []
        for key in sorted(keys):
            option = chosen.get(key)
            if option is None:
                continue
            rest = set(essential) - {key}
            needs = option["into"] + option["side"]
            if set(needs) <= rest:
                essential.remove(key)
                implied.append({"key": key, "type": graph.statements.get(key, {}).get("type"),
                                "status": graph.status(key) if key in graph.statements else "unknown",
                                "supplied_by": option["weakened"], "from_members": needs})
        return essential, implied

    def _joint(self, keys: list[str], hypothesis: str | None,
               conclusion_closure: Any) -> dict[str, Any]:
        """The level's joint check over the recorded edges: its open members
        jointly impossible, and whether the level implies the hypothesis back
        (restates it) or follows from the theorem's own conclusion."""
        graph = self.graph
        frontier = graph.frontier()
        open_members = [k for k in keys if k not in graph.supplied and k not in graph.refuted]
        if not open_members:
            return {"status": "no_open_member", "evidence_class": EVIDENCE}
        target = hypothesis if hypothesis in graph.statements else None
        check = frontier.check(open_members, target=target, max_work=CLOSURE_WORK_LIMIT)
        row: dict[str, Any] = {"status": check["status"], "evidence_class": EVIDENCE,
                               "satisfiability": "not_established"}
        if check.get("conflicts"):
            row["conflicts"] = check["conflicts"]
        if check["status"] == "base_graph_inconsistent":
            return row  # the graph contradicts itself: no joint answer means anything
        if target is not None:
            # None: the closure ran out of work before it could tell.
            supplies = bool(check.get("supplies_target"))
            row["implies_hypothesis"] = True if supplies else (None if check["status"] == "unknown_budget" else False)
            relation = check.get("endpoint_relation")
            row["restates_hypothesis"] = (None if relation == "unknown_budget"
                                          else relation == "joint_endpoint_equivalence")
            if supplies and check.get("target_witness"):
                row["hypothesis_witness"] = check["target_witness"]
        if conclusion_closure is not None:
            follows = [k for k in open_members if frontier.is_positive(conclusion_closure, k)]
            row["follows_from_conclusion"] = len(follows) == len(open_members)
            if not conclusion_closure.complete and not row["follows_from_conclusion"]:
                row["follows_from_conclusion"] = None  # the conclusion's closure ran out of work
        return row

    # ------------------------------------------------------------------
    # Reverse index

    def needed_by(self) -> dict[str, list[dict[str, Any]]]:
        """For every statement at level 1 or below of some chain (a member or
        an implied member), the chains that need it, with the level."""
        if self._needed_by is None:
            index: dict[str, list[dict[str, Any]]] = defaultdict(list)
            for chain in self.chains():
                seen: set[str] = set()
                for level in chain["levels"][1:]:
                    for member in level["members"] + level["implied"]:
                        key = member["key"]
                        if key in seen:
                            continue
                        seen.add(key)
                        index[key].append({"theorem": chain["theorem"], "i": chain["i"],
                                           "hypothesis": (chain["hypothesis"] or {}).get("key"),
                                           "level": level["level"]})
            self._needed_by = dict(index)
        return self._needed_by

    def open_targets(self) -> dict[str, list[dict[str, Any]]]:
        """Open members at level 1 or below of chains whose hypothesis is not
        supplied: attack targets, each with the chains that need it."""
        graph = self.graph
        out: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for chain in self.chains():
            hypothesis = (chain["hypothesis"] or {}).get("key")
            if hypothesis in graph.supplied:
                continue
            for level in chain["levels"][1:]:
                for member in level["members"]:
                    if member["status"] == "open":
                        out[member["key"]].append({"theorem": chain["theorem"], "i": chain["i"],
                                                   "hypothesis": hypothesis, "level": level["level"],
                                                   "restates_hypothesis": level["joint"].get("restates_hypothesis"),
                                                   "jointly_impossible": level["joint"]["status"]
                                                   == "refuted_jointly"})
        return dict(out)
