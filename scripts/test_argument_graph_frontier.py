#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tests for ``argument_graph_frontier.py``: joint questions over the graph's
recorded edges, and the builder surfaces that use them (bundles checked as a
whole, refutation by conflict). Every row is hand-made; a statement's key
doubles as its rendered type."""

from __future__ import annotations

import itertools
import random
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import build_argument_continuations as builder  # noqa: E402
from argument_graph_frontier import Frontier  # noqa: E402
from test_build_argument_continuations import graph_of, match, statement  # noqa: E402


def refutation(head: str, residuals: tuple[str, ...] = (), producer: str = "T.not") -> dict:
    return {"record": "refutation", "statement": head, "producer": producer, "reading": "conclusion",
            "status": "matched", "open_data": False,
            "residuals": [{"key": r, "type": r, "has_open_data": False} for r in residuals]}


def rows_for(keys, positive=(), negative=()) -> list[dict]:
    return ([statement(k) for k in keys]
            + [match(head, f"T.r{i}", tuple(premises)) for i, (head, premises) in enumerate(positive)]
            + [refutation(head, tuple(premises), f"T.n{i}") for i, (head, premises) in enumerate(negative)])


class JointChecks(unittest.TestCase):
    def test_jointly_impossible_bundle_is_dropped_with_witnesses(self) -> None:
        # A ⇒ ¬B and A ∧ B ⇒ G: neither A nor B is refuted, the pair is impossible.
        graph = graph_of(rows_for("ABG", [("G", "AB")], [("B", "A")]))
        self.assertEqual(graph.open, set("ABG"))
        self.assertEqual(graph._candidate_bundles("G"), ([["A", "B"]], False))
        kept, truncated, checks = graph.bundle_report("G")
        self.assertEqual((kept, truncated), ([], False))
        self.assertEqual(graph.bundles("G"), ([], False))
        check = checks[0]
        self.assertEqual((check["status"], check["evidence_class"]), ("refuted_jointly",
                                                                      "derivation_over_recorded_edges"))
        conflict = check["conflicts"][0]
        self.assertEqual((conflict["statement"], conflict["assumption_support"]), ("B", ["A", "B"]))
        refuted = conflict["refuted"]["nodes"][conflict["refuted"]["root"]]
        self.assertEqual((refuted["status"], refuted["producer"]), ("refuted_under_assumptions", "T.n0"))

    def test_joint_endpoint_equivalence_without_a_pairwise_class(self) -> None:
        # A ∧ B ⇒ G, G ⇒ A, G ⇒ B: no pairwise class, but {A, B} is G restated.
        graph = graph_of(rows_for("ABG", [("G", "AB"), ("A", "G"), ("B", "G")]))
        self.assertEqual(graph.disguise_classes(), [])
        result = graph.frontier().check("AB", target="G")
        self.assertEqual((result["status"], result["endpoint_relation"], result["satisfiability"]),
                         ("no_recorded_conflict", "joint_endpoint_equivalence", "not_established"))
        self.assertEqual(sorted(result["reverse_witnesses"]), ["A", "B"])
        kept, _, checks = graph.bundle_report("G")
        self.assertEqual(kept, [["A", "B"]])  # a restatement is kept, labelled
        self.assertEqual(checks[0]["endpoint_relation"], "joint_endpoint_equivalence")

    def test_one_direction_is_not_an_equivalence(self) -> None:
        graph = graph_of(rows_for("ABG", [("G", "AB"), ("A", "G")]))
        result = graph.frontier().check("AB", target="G")
        self.assertEqual((result["endpoint_relation"], result["implied_by_target"]),
                         ("not_established_by_recorded_edges", ["A"]))

    def test_false_is_a_conflict_without_a_refutation(self) -> None:
        graph = graph_of(rows_for(["A", "B", "False"], [("False", ["A", "B"])]))
        self.assertEqual(graph.frontier().check(["A", "B"])["status"], "refuted_jointly")

    def test_no_conflict_does_not_establish_consistency(self) -> None:
        graph = graph_of(rows_for("AG", [("G", "A")]))
        result = graph.frontier().check(["A"])
        self.assertEqual((result["status"], result["satisfiability"]), ("no_recorded_conflict", "not_established"))

    def test_support_leaves_out_an_unused_assumption(self) -> None:
        graph = graph_of(rows_for("ABC", [("B", "A")], [("B", "A")]))
        # A alone supplies B and refutes it: the graph itself refutes A (conflict).
        self.assertEqual(graph.refuted["A"]["kind"], "derived_conflict")
        frontier = Frontier(graph, supplied=graph.supplied, refuted={})
        conflict = frontier.check(["A", "C"])["conflicts"][0]
        self.assertEqual(conflict["assumption_support"], ["A"])

    def test_a_refutation_needs_all_its_residuals(self) -> None:
        frontier = graph_of(rows_for("ABG", [("G", "A")], [("A", "B")])).frontier()
        self.assertFalse(frontier.closure(["A"]).conflicts)
        self.assertEqual(frontier.closure(["A", "B"]).conflicts, ["A"])

    def test_cycles_do_not_supply_themselves(self) -> None:
        frontier = graph_of(rows_for("ABG", [("A", "B"), ("B", "A"), ("G", "B")])).frontier()
        self.assertNotIn("G", frontier.closure().positive)
        self.assertIn("G", frontier.closure(["A"]).positive)

    def test_work_budget_reads_unknown_never_a_verdict(self) -> None:
        graph = graph_of(rows_for("ABCG", [("B", "A"), ("C", "B"), ("G", "C")]))
        result = graph.frontier().check(["A"], target="G", max_work=1)
        self.assertEqual(result["status"], "unknown_budget")
        self.assertFalse(result["complete_for_recorded_edges"])
        # The reverse direction is settled (G implies nothing), so G is not A
        # restated whatever the cut-short forward closure would have found.
        self.assertEqual(result["endpoint_relation"], "not_established_by_recorded_edges")
        both_short = graph_of(rows_for("ABCG", [("B", "A"), ("C", "B"), ("G", "C"), ("A", "G"), ("A", "C")]))
        self.assertEqual(both_short.frontier().check(["A"], target="G", max_work=1)["endpoint_relation"],
                         "unknown_budget")
        # A conflict found before the budget runs out stands: closures only grow.
        conflicting = graph_of(rows_for("ABCD", [("B", "A"), ("C", "B"), ("D", "C")], [("B", "A")]))
        self.assertEqual(conflicting.refuted["A"]["kind"], "derived_conflict")

    def test_the_graph_budget_for_bundle_checks_is_shared_and_deterministic(self) -> None:
        graph = graph_of(rows_for("ABG", [("G", "AB")]))
        graph._bundle_check_work = builder.BUNDLE_CHECK_TOTAL_WORK
        kept, truncated, checks = graph.bundle_report("G")
        self.assertEqual((kept, truncated), ([["A", "B"]], False))  # unknown is kept, never dropped
        self.assertEqual((checks[0]["status"], checks[0]["endpoint_relation"]), ("unknown_budget", "unknown_budget"))

    def test_witnesses_stop_at_what_the_graph_supplies(self) -> None:
        graph = graph_of(rows_for("ABSG", [("S", ()), ("B", "AS"), ("G", "B")]))
        frontier = graph.frontier()
        dag = frontier.witness(frontier.closure(["A"]), "G")
        statuses = {node["statement"]: node["status"] for node in dag["nodes"].values()}
        self.assertEqual(statuses, {"G": "supplied_under_assumptions", "B": "supplied_under_assumptions",
                                    "A": "assumed", "S": "supplied_in_graph"})
        self.assertTrue(frontier.witness(frontier.closure(["A"]), "G", max_nodes=1)["truncated"])

    def test_unknown_keys_are_refused(self) -> None:
        with self.assertRaises(ValueError):
            graph_of(rows_for("AG", [("G", "A")])).frontier().check(["absent"])

    def test_an_inconsistent_graph_answers_nothing(self) -> None:
        graph = graph_of(rows_for("AG", [("A", ()), ("G", "A")], [("A", ())]))
        self.assertEqual(graph.inconsistent, ["A"])
        self.assertEqual(graph.frontier().check(["G"])["status"], "base_graph_inconsistent")
        self.assertEqual(graph.frontier().cheapest_cut("G", {"A": 1})["status"], "base_graph_inconsistent")


class RefutationByConflict(unittest.TestCase):
    def test_a_statement_that_supplies_both_sides_is_refuted(self) -> None:
        # X is supplied; a recorded refutation of X needs Y (supplied) and L
        # (open): supplying L would supply ¬X next to X, so L is refuted. The
        # propagation of refutations alone left L open (the shape of the real
        # graph's `2 < 2` refuted through `auxPrime_not_dvd_self`).
        rows = rows_for("XYLG", [("X", ()), ("Y", ()), ("G", "L")], [("X", "YL")])
        graph = graph_of(rows)
        record = graph.refuted["L"]
        self.assertEqual((record["kind"], record["reaches"], record["refuted_by"]),
                         ("derived_conflict", "X", "T.n0"))
        self.assertNotIn("L", graph.open)
        self.assertEqual(graph.inconsistent, [])
        # G's only route runs through L: no bundle is offered for it.
        self.assertEqual(graph.bundles("G"), ([], False))
        self.assertEqual(builder.sentinel_alarms(graph), [])

    def test_a_statement_is_refuted_when_it_reaches_one_that_is(self) -> None:
        rows = rows_for("XYLMG", [("X", ()), ("Y", ()), ("L", "M"), ("G", "M")], [("X", "YL")])
        graph = graph_of(rows)
        self.assertEqual(graph.refuted["M"]["kind"], "derived_conflict")
        self.assertEqual(graph.status("G"), "open")

    def test_a_registered_open_target_refuted_by_conflict_raises_an_alarm(self) -> None:
        half = "1 / 2 ∈ Erdos249257.mersenneAchievementSet"
        graph = graph_of(rows_for(["X", "Y", half], [("X", ()), ("Y", ())], [("X", ("Y", half))]))
        self.assertEqual(graph.refuted[half]["kind"], "derived_conflict")
        alarms = builder.sentinel_alarms(graph)
        self.assertEqual([(a["status"], a["overridable"]) for a in alarms], [("refuted", True)])


class CheapestCut(unittest.TestCase):
    def test_a_shared_statement_is_paid_once(self) -> None:
        graph = graph_of(rows_for("ABCDEG", [("A", "C"), ("B", "C"), ("G", "AB"), ("G", "DE")]))
        result = graph.frontier().cheapest_cut("G", {"C": 5, "D": 3, "E": 3})
        self.assertEqual((result["status"], result["assumptions"], result["cost"]),
                         ("optimal_recorded_cut", ["C"], "5"))
        self.assertEqual(result["optimality_scope"], "finite_candidate_pool_and_recorded_edges")

    def test_restatements_can_be_excluded_and_cannot_hide_behind_a_spare_member(self) -> None:
        frontier = graph_of(rows_for("ABCG", [("G", "AB"), ("A", "G"), ("B", "G"), ("G", "C")])).frontier()
        result = frontier.cheapest_cut("G", {"A": 1, "B": 1, "C": 7}, exclude_equivalent=True)
        self.assertEqual(result["assumptions"], ["C"])
        self.assertGreater(result["equivalent_cuts_excluded"], 0)
        spare = graph_of(rows_for("ABCG", [("G", "AB"), ("A", "G"), ("B", "G")])).frontier()
        self.assertEqual(spare.cheapest_cut("G", {"A": 1, "B": 1, "C": 1}, exclude_equivalent=True)["status"],
                         "no_admissible_recorded_cut")

    def test_conflicting_sets_are_skipped(self) -> None:
        graph = graph_of(rows_for("ABCG", [("G", "AB"), ("G", "C")], [("B", "A")]))
        result = graph.frontier().cheapest_cut("G", {"A": 1, "B": 1, "C": 5})
        self.assertEqual((result["assumptions"], result["nogoods"]), (["C"], [["A", "B"]]))

    def test_costs_are_validated(self) -> None:
        frontier = graph_of(rows_for("AG", [("G", "A")])).frontier()
        for costs in ({"A": -1}, {"G": 1}, {"missing": 1}, {"A": 0.5}, {"A": True}, {"A": [1]}):
            with self.subTest(costs=costs), self.assertRaises(ValueError):
                frontier.cheapest_cut("G", costs)
        self.assertEqual(frontier.cheapest_cut("G", {"A": "1/3"})["cost"], "1/3")

    def test_budgets_read_unknown(self) -> None:
        frontier = graph_of(rows_for("AG", [("G", "A")])).frontier()
        self.assertEqual(frontier.cheapest_cut("G", {"A": 1}, max_states=0)["status"], "unknown_budget")

    def test_the_pool_is_bounded(self) -> None:
        keys = [f"K{i}" for i in range(33)]
        frontier = graph_of(rows_for(keys + ["G"], [("G", ("K0",))])).frontier()
        with self.assertRaises(ValueError):
            frontier.cheapest_cut("G", {k: 1 for k in keys})

    def test_against_an_exhaustive_oracle_on_random_graphs(self) -> None:
        rng = random.Random(27381)
        checked = 0
        for trial in range(360):
            keys = ["A", "B", "C", "D", "X", "G"]
            positive = [(rng.choice(keys), rng.sample(keys, rng.randrange(3))) for _ in range(9)]
            negative = [(rng.choice(keys), rng.sample(keys, rng.randrange(3))) for _ in range(3)]

            def oracle(seed):
                # Scan to a fixpoint from scratch: no Frontier, no Graph.supply.
                known = set(seed)
                while True:
                    grown = known | {head for head, premises in positive if set(premises) <= known}
                    if grown == known:
                        break
                    known = grown
                refuted = {head for head, premises in negative if set(premises) <= known}
                return known, known & refuted

            if oracle([])[1]:
                continue  # an inconsistent base graph answers nothing
            graph = graph_of(rows_for(keys, positive, negative))
            costs = {k: rng.randrange(1, 6) for k in "ABCD"}
            feasible = [sum(costs[k] for k in seed) for n in range(5) for seed in itertools.combinations(costs, n)
                        if "G" in oracle(seed)[0] and not oracle(seed)[1]]
            result = graph.frontier().cheapest_cut("G", costs)
            with self.subTest(trial=trial):
                if feasible:
                    self.assertEqual(result["status"], "optimal_recorded_cut")
                    self.assertEqual(int(result["cost"]), min(feasible))
                else:
                    self.assertEqual(result["status"], "no_admissible_recorded_cut")
                for n in range(3):
                    for seed in itertools.combinations("ABCD", n):
                        known, conflicts = oracle(seed)
                        state = graph.frontier().closure(seed)
                        self.assertEqual(known, graph.supplied | set(state.positive))
                        self.assertEqual(bool(conflicts), bool(state.conflicts))
            checked += 1
        self.assertGreater(checked, 100)


if __name__ == "__main__":
    unittest.main()
