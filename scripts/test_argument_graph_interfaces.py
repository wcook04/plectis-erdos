#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tests for ``argument_graph_interfaces.py`` (interface chains) and the query
surfaces that use them (``needs``, ``next``, ``packet``).

``erdos249_rows`` reproduces, as export rows, the four-level chain a kernel
probe found in the #249 module ``ExcludedCofactorEstimate``: ``prop_badcof``
uses its prime-number-theorem input only through
``eventually_card_excluded_le`` and ``eventually_excluded_budget``; those only
through ``eventually_card_excluded_le_of_upper`` and
``eventually_excluded_budget_of_upper``; those only through
``eventually_card_primes_dyadic_le`` (the dyadic prime count with constant
``1 + ε``), which uses it only through ``nthPrime_two_sided``. The rows are the
ones the exporter writes for that module: theorem telescopes, one weakening row
per theorem (each lemma takes the input first, and each use site is the lemma
applied to it), and the matches of each lemma and of its weakened theorem
against the statement its use site proves. The kernel verdicts in them are
synthetic data.
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import build_argument_continuations as builder  # noqa: E402
import query_continuations as query  # noqa: E402
from test_build_argument_continuations import (FIXTURE, META, SUMMARY, data, graph_of, hyp, match,  # noqa: E402
                                               statement, theorem)

NS = "ErdosProblems.Erdos249.PaperCompleteR21"
MODULE = f"{NS}.ExcludedCofactorEstimate"
PNT = "PrimeNumberTheorem"
# The statements the use sites prove: each lemma applied to the input.
C_CARD = "∀ (h s : ℕ) {η D : ℝ}, HasNaturalDensity (excludedCofactorSet η) D → ∀ {ε : ℝ}, 0 < ε → count ≤ (D + ε) X"
C_BUDGET = "∀ (h s : ℕ) {η D : ℝ}, HasNaturalDensity (excludedCofactorSet η) D → D < 1 / 100 → budget"
C_CARD_UPPER = "∀ (h s : ℕ) {η D : ℝ}, 0 ≤ D → D ≤ 1 → UpperDensityLE (excludedCofactorSet η) D → count ≤ (D + ε) X"
C_BUDGET_UPPER = "∀ (h s : ℕ) {η D : ℝ}, 0 ≤ D → D ≤ 1 → UpperDensityLE (excludedCofactorSet η) D → D < 1 / 100 → budget"
C_DYADIC = "∀ {ε : ℝ}, 0 < ε → ∀ᶠ (a : ℕ) in atTop, #{p prime : a < p ≤ 2a + 1} * log a ≤ (1 + ε) * a"
C_TWO_SIDED = "∀ {δ : ℝ}, 0 < δ → ∃ K, 2 ≤ K ∧ ∀ n ≥ K, (1 - δ) n log n ≤ p_n ∧ p_n ≤ (1 + δ) n log n"

# lemma -> (the statement its use site proves, the lemma its own proof applies to the input)
CHAIN = {
    "eventually_card_excluded_le": (C_CARD, "eventually_card_excluded_le_of_upper"),
    "eventually_card_excluded_le_of_upper": (C_CARD_UPPER, "eventually_card_primes_dyadic_le"),
    "eventually_card_primes_dyadic_le": (C_DYADIC, "nthPrime_two_sided"),
    "nthPrime_two_sided": (C_TWO_SIDED, None),
    "eventually_excluded_budget": (C_BUDGET, "eventually_excluded_budget_of_upper"),
    "eventually_excluded_budget_of_upper": (C_BUDGET_UPPER, "eventually_card_excluded_le_of_upper"),
}
# theorem -> the lemmas its proof applies to the input
USES = {
    "prop_badcof": ["eventually_card_excluded_le", "eventually_excluded_budget"],
    "excluded_budget_one_thousandth": ["eventually_excluded_budget_of_upper"],
    **{lemma: [below] for lemma, (_, below) in CHAIN.items() if below},
}


def full(name: str) -> str:
    return f"{NS}.{name}"


def weakening(name: str, lemmas: list[str], *, hypothesis: str = PNT, i: int = 0) -> dict:
    return {"record": "weakening", "theorem": full(name), "i": i, "hypothesis": hypothesis,
            "hypothesis_type": hypothesis, "weakened": f"{full(name)}._argument_weakening_{i}",
            "type": f"weakened {name}", "kernel_checked": True, "kernel_error": "",
            "consequences": [{"key": CHAIN[lemma][0], "type": CHAIN[lemma][0], "via": [full(lemma)],
                              "sites": [f"{lemma} hPNT"], "implication_kernel_checked": True} for lemma in lemmas]}


def erdos249_rows(*, weakened_matches: bool = True) -> list[dict]:
    rows = [statement(PNT)]
    names = ["prop_badcof", "excluded_budget_one_thousandth", *CHAIN]
    for name in names:
        # The input first, then data and schematic side conditions: every
        # conclusion mentions a binder, as in the module.
        rows.append(theorem(full(name), [hyp(0, PNT), data(1, "ℕ"), hyp(2, "0 < ε", closed=False)], None,
                            module=MODULE))
    for name, lemmas in USES.items():
        rows.append(weakening(name, lemmas))
    for lemma, (proves, below) in CHAIN.items():
        rows.append(statement(proves, "consequence"))
        rows.append(match(proves, full(lemma), (PNT,)))
        if below and weakened_matches:
            rows.append(match(proves, f"{full(lemma)}._argument_weakening_0", (CHAIN[below][0],)))
    return rows


def ledger(root: Path, rows: list[dict]) -> None:
    (root / "docs").mkdir(exist_ok=True)
    (root / "docs" / "paper_lean_coverage.json").write_text(json.dumps({"rows": rows}), encoding="utf-8")


def ledger_row(row_id: str, label: str, name: str, problem: str = "249") -> dict:
    return {"id": row_id, "problem": problem, "paper_id": f"erdos{problem}-long", "side": "long", "label": label,
            "source": f"paper.tex:{len(label)}", "lean": {"status": "exact", "declarations": [{"name": name}]},
            "comparator": {"status": "compared"}}


def load(rows: list[dict], ledger_rows: list[dict]) -> tuple[builder.Graph, dict]:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        ledger(root, ledger_rows)
        export = root / "export.jsonl"
        export.write_text("\n".join(json.dumps(r, ensure_ascii=False) for r in [META, *rows, SUMMARY]) + "\n",
                          encoding="utf-8")
        projection, payload = builder.build(export, root)
        builder.write_outputs(projection, payload, root / "p.json", root / "g.json.gz")
        graph, loaded = query.load(root / "g.json.gz")
        loaded["_projection"] = projection
        return graph, loaded


LEDGER_249 = [ledger_row("r249-badcof", "prop:badcof", full("prop_badcof")),
              ledger_row("r249-thousandth", "rem:eta-thousandth", full("excluded_budget_one_thousandth"))]


def levels(chain: dict) -> list[list[str]]:
    return [[m["key"] for m in level["members"]] for level in chain["levels"]]


class Erdos249Chain(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.graph, cls.payload = load(erdos249_rows(), LEDGER_249)
        cls.chain = cls.graph.interfaces().chains_of(full("prop_badcof"))[0]

    def test_every_level_of_the_four_level_chain(self) -> None:
        self.assertEqual(levels(self.chain), [[PNT], sorted([C_CARD, C_BUDGET]), [C_CARD_UPPER], [C_DYADIC],
                                              [C_TWO_SIDED]])
        self.assertEqual((self.chain["depth"], self.chain["truncated"], self.chain["cycle"]), (4, False, False))
        # Level 2 is both _of_upper lemmas; the budget one follows from the
        # other through its own weakened theorem, so it is listed as implied.
        implied = self.chain["levels"][2]["implied"]
        self.assertEqual([m["key"] for m in implied], [C_BUDGET_UPPER])
        self.assertEqual(implied[0]["supplied_by"], full("eventually_excluded_budget_of_upper._argument_weakening_0"))
        for level in self.chain["levels"]:
            self.assertEqual(level["status"], "open")

    def test_each_level_records_how_it_refines(self) -> None:
        level1 = {m["key"]: m for m in self.chain["levels"][1]["members"]}
        card = level1[C_CARD]
        self.assertEqual((card["via"], card["kernel_checked_from"]), ([full("eventually_card_excluded_le")], PNT))
        self.assertEqual(card["refined_by"]["weakened"], full("eventually_card_excluded_le._argument_weakening_0"))
        self.assertEqual(card["refined_by"]["into"], [C_CARD_UPPER])
        dyadic = self.chain["levels"][3]["members"][0]
        self.assertEqual(dyadic["entered_by"]["lemma"], full("eventually_card_excluded_le_of_upper"))
        self.assertEqual(dyadic["refined_by"]["into"], [C_TWO_SIDED])
        self.assertNotIn("refined_by", self.chain["levels"][4]["members"][0])  # nthPrime_two_sided: no weakening
        for level in self.chain["levels"][1:]:
            self.assertEqual(level["joint"]["status"], "no_recorded_conflict")
            self.assertFalse(level["joint"]["restates_hypothesis"])

    def test_the_other_paper_result_shares_the_lower_levels(self) -> None:
        chain = self.graph.interfaces().chains_of(full("excluded_budget_one_thousandth"))[0]
        self.assertEqual(levels(chain), [[PNT], [C_BUDGET_UPPER], [C_CARD_UPPER], [C_DYADIC], [C_TWO_SIDED]])

    def test_reverse_index(self) -> None:
        users = self.graph.interfaces().needed_by()[C_DYADIC]
        self.assertEqual({(u["theorem"].split(".")[-1], u["level"]) for u in users},
                         {("prop_badcof", 3), ("excluded_budget_one_thousandth", 3),
                          ("eventually_card_excluded_le", 2), ("eventually_card_excluded_le_of_upper", 1),
                          ("eventually_excluded_budget", 3), ("eventually_excluded_budget_of_upper", 2)})
        projection = self.payload["_projection"]
        row = next(r for r in projection["interfaces"]["needed_by"] if r["key"] == C_DYADIC)
        self.assertEqual(row["paper_results"], 2)
        self.assertEqual(projection["summary"]["interface_chains"], 7)
        self.assertEqual(projection["summary"]["interface_chains_deeper_than_one_level"], 6)
        cited = projection["interfaces"]["by_problem"]["249"][:2]
        self.assertEqual({(c["theorem"], tuple(p["label"] for p in c["papers"])) for c in cited},
                         {(full("prop_badcof"), ("prop:badcof",)),
                          (full("excluded_budget_one_thousandth"), ("rem:eta-thousandth",))})

    def test_query_needs_by_label_and_by_name(self) -> None:
        by_label = query.cmd_needs(self.graph, self.payload, argparse.Namespace(target="prop:badcof"))
        self.assertEqual((by_label["resolved_as"], [t["name"] for t in by_label["theorems"]]),
                         ("paper result", [full("prop_badcof")]))
        chain = by_label["theorems"][0]["interfaces"][0]
        dyadic = chain["levels"][3]["members"][0]
        self.assertEqual(dyadic["key"], C_DYADIC)
        self.assertEqual(len(dyadic["paper_results_above"]), 2)
        by_name = query.cmd_needs(self.graph, self.payload, argparse.Namespace(target="prop_badcof"))
        self.assertEqual(by_name["resolved_as"], "theorem")
        plain = query.cmd_needs(self.graph, self.payload, argparse.Namespace(target="nthPrime_two_sided"))
        self.assertIn("no kernel-checked weakening", plain["theorems"][0]["note"])
        with self.assertRaises(SystemExit):
            query.cmd_needs(self.graph, self.payload, argparse.Namespace(target="no-such-label"))

    def test_next_and_packet_surface_the_levels(self) -> None:
        shortlist = query.cmd_next(self.graph, self.payload, argparse.Namespace(problem="249", limit=20, sinks=12))
        rows = {row["key"]: row for row in shortlist["shortlist"]}
        self.assertEqual(rows[PNT]["tier"], "paper input or interface level")
        self.assertTrue(any("assumed by 2 paper result(s)" in r for r in rows[PNT]["reasons"]))
        for key, level in ((C_CARD, 1), (C_CARD_UPPER, 2), (C_DYADIC, 3), (C_TWO_SIDED, 4)):
            self.assertTrue(any(f"level {level} of what `prop_badcof` needs of" in r for r in rows[key]["reasons"]),
                            (key, rows[key]["reasons"]))
        packet = query.packet_markdown(self.graph, self.payload, "249", 12)
        section = packet.split("## 2.")[0]
        self.assertIn(f"### `{query.short(PNT)}` {PNT}", section)
        self.assertIn("level 3 (open)", section)
        self.assertIn(C_DYADIC, section)
        self.assertIn("implied by the others", section)

    def test_supplying_the_dyadic_level_removes_the_input(self) -> None:
        # A theorem with no hypothesis proving the level-3 statement (the
        # constant stays 1 + ε here) settles every level above it.
        rows = [*erdos249_rows(), theorem(full("dyadic_elementary"), [], C_DYADIC, module=MODULE)]
        graph, _ = load(rows, LEDGER_249)
        chain = graph.interfaces().chains_of(full("prop_badcof"))[0]
        self.assertEqual([level["status"] for level in chain["levels"]],
                         ["open", "satisfied", "satisfied", "satisfied", "open"])
        self.assertIn(C_CARD, graph.supplied)
        self.assertEqual(graph.status(PNT), "open")

    def test_without_the_weakened_matches_no_level_is_claimed(self) -> None:
        graph, _ = load(erdos249_rows(weakened_matches=False), LEDGER_249)
        chain = graph.interfaces().chains_of(full("prop_badcof"))[0]
        self.assertEqual(levels(chain), [[PNT], sorted([C_CARD, C_BUDGET])])
        card = next(m for m in chain["levels"][1]["members"] if m["key"] == C_CARD)
        self.assertEqual(card["unmatched"][0]["reason"],
                         "no recorded match of the weakened lemma against this statement")


class ChainEdges(unittest.TestCase):
    def test_a_jointly_impossible_level_refutes_its_hypothesis(self) -> None:
        # T uses H only through C1 and C2, and a refutation of C2 needs C1.
        rows = [statement("H"), theorem("T.t", [hyp(0, "H")], "G"),
                {**weakening_row("T.t", "H", [("C1", "L1"), ("C2", "L2")])},
                {"record": "refutation", "statement": "C2", "producer": "T.not_c2", "reading": "conclusion",
                 "status": "matched", "open_data": False,
                 "residuals": [{"key": "C1", "type": "C1", "has_open_data": False}]}]
        graph = graph_of(rows)
        self.assertEqual(graph.refuted["H"]["kind"], "derived_conflict")
        chain = graph.interfaces().chains_of("T.t")[0]
        self.assertEqual(chain["levels"][0]["status"], "blocked")
        level = chain["levels"][1]
        self.assertEqual((level["status"], level["joint"]["status"]), ("open", "refuted_jointly"))
        self.assertEqual(level["joint"]["conflicts"][0]["assumption_support"], ["C1", "C2"])

    def test_a_level_that_implies_the_hypothesis_back_restates_it(self) -> None:
        rows = [statement("H"), theorem("T.t", [hyp(0, "H")], "G"), weakening_row("T.t", "H", [("C", "L")]),
                theorem("T.back", [hyp(0, "C")], "H")]
        chain = graph_of(rows).interfaces().chains_of("T.t")[0]
        joint = chain["levels"][1]["joint"]
        self.assertTrue(joint["implies_hypothesis"] and joint["restates_hypothesis"])
        self.assertEqual(joint["evidence_class"], "derivation_over_recorded_edges")

    def test_a_cycle_through_statement_keys_stops(self) -> None:
        rows = [statement("H"), theorem("T.t", [hyp(0, "H")], "G"),
                weakening_row("T.t", "H", [("C", "V")]),
                theorem("V", [hyp(0, "H")], None), weakening_row("V", "H", [("D", "W")]),
                theorem("W", [hyp(0, "H")], None), weakening_row("W", "H", [("C", "V")]),
                match("C", "V._argument_weakening_0", ("D",)), match("D", "W._argument_weakening_0", ("C",))]
        chain = graph_of(rows).interfaces().chains_of("T.t")[0]
        self.assertEqual(levels(chain), [["H"], ["C"], ["D"]])
        self.assertTrue(chain["cycle"])

    def test_a_match_that_still_needs_the_hypothesis_is_no_refinement(self) -> None:
        rows = [statement("H"), theorem("T.t", [hyp(0, "H")], "G"), weakening_row("T.t", "H", [("C", "V")]),
                theorem("V", [hyp(0, "H"), hyp(1, "H")], None), weakening_row("V", "H", [("D", "W")]),
                match("C", "V._argument_weakening_0", ("D", "H"))]
        chain = graph_of(rows).interfaces().chains_of("T.t")[0]
        self.assertEqual(levels(chain), [["H"], ["C"]])
        self.assertEqual(chain["levels"][1]["members"][0]["unmatched"][0]["reason"],
                         "the match still needs the hypothesis")

    def test_depth_is_bounded(self) -> None:
        rows = [statement("H"), theorem("T.t", [hyp(0, "H")], "G"), weakening_row("T.t", "H", [("C0", "V0")])]
        for i in range(12):
            rows += [theorem(f"V{i}", [hyp(0, "H")], None),
                     weakening_row(f"V{i}", "H", [(f"C{i + 1}", f"V{i + 1}")]),
                     match(f"C{i}", f"V{i}._argument_weakening_0", (f"C{i + 1}",))]
        chain = graph_of(rows).interfaces().chains_of("T.t")[0]
        self.assertTrue(chain["truncated"])
        self.assertEqual(chain["depth"], 8)


def weakening_row(name: str, hypothesis: str, uses: list[tuple[str, str]], i: int = 0) -> dict:
    return {"record": "weakening", "theorem": name, "i": i, "hypothesis": hypothesis, "hypothesis_type": hypothesis,
            "weakened": f"{name}._argument_weakening_{i}", "type": f"weakened {name}", "kernel_checked": True,
            "consequences": [{"key": key, "type": key, "via": [lemma], "sites": [f"{lemma} h"],
                              "implication_kernel_checked": True} for key, lemma in uses]}


class ToyChains(unittest.TestCase):
    """The UseToy weakenings of the toy corpus are one level deep: the lemmas
    at their use sites have no weakening of their own."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.graph = builder.Graph(builder.read_export(FIXTURE))
        cls.graph.analyse()
        cls.key = {}
        for key, node in cls.graph.statements.items():
            for text in [node["type"], *node.get("aliases", ())]:
                cls.key[text] = key

    def chain(self, name: str) -> dict:
        chains = self.graph.interfaces().chains_of(f"UseToy.{name}")
        self.assertEqual(len(chains), 1)
        return chains[0]

    def test_goal_of_strong(self) -> None:
        chain = self.chain("goal_of_strong")
        self.assertEqual(levels(chain), [[self.key["UseToy.Strong"]], [self.key["UseToy.Weak"]]])
        self.assertEqual([level["status"] for level in chain["levels"]], ["open", "satisfied"])
        self.assertEqual(chain["conclusion"]["status"], "supplied")
        self.assertEqual(chain["levels"][1]["joint"]["status"], "no_open_member")

    def test_odd_of_bad_is_blocked(self) -> None:
        chain = self.chain("odd_of_bad")
        self.assertEqual([level["status"] for level in chain["levels"]], ["blocked", "blocked"])

    def test_fam_three_and_mixed(self) -> None:
        # The toy proves ∀ n, Fam n outright, so both levels are satisfied;
        # h 3 applies the hypothesis itself, so nothing refines further.
        fam = self.chain("fam_three")
        self.assertEqual(levels(fam), [[self.key["∀ (n : Nat), UseToy.Fam n"]], [self.key["UseToy.Fam 3"]]])
        self.assertEqual([level["status"] for level in fam["levels"]], ["satisfied", "satisfied"])
        self.assertEqual(fam["levels"][1]["members"][0]["via"], ["hypothesis"])
        mixed = self.chain("mixed")
        self.assertEqual((mixed["conclusion"]["status"], mixed["depth"]), ("schematic", 1))


class Anchoring(unittest.TestCase):
    """next and packet start from the paper results; another problem's
    statements are listed apart, and literal arithmetic ranks last."""

    def test_cross_problem_statements_and_artifacts(self) -> None:
        rows = [*erdos249_rows(),
                # A #257 theorem states S257; a general #249 lemma, matched by
                # the unifier, reduces it (its own conclusion is another statement).
                theorem("ErdosProblems.Erdos257.Use.consumer", [hyp(0, "S257")], "C257",
                        module="ErdosProblems.Erdos257.Use"),
                theorem(f"{NS}.lemma249", [data(0, "ℕ"), hyp(1, "Q249")], None, module=MODULE),
                match("S257", f"{NS}.lemma249", ("Q249",)),
                # No attributed theorem states W257, which mentions only #257
                # objects; a general #249 lemma happens to match it.
                {"record": "statement", "key": "W257", "origin": "residual", "type": "mersenneWeight w ≤ r",
                 "constants": ["Erdos249257.mersenneWeight", "Erdos249257.greedyMersenneRemainder"]},
                match("W257", f"{NS}.lemma249", ("Q249",)),
                theorem("DemandLedger.edge", [hyp(0, "W257")], "Z", module="ErdosProblems.DemandLedger.edges"),
                theorem(f"{NS}.degenerate", [hyp(0, "2 ≤ 2 - 1")], "Z249", module=MODULE),
                theorem(f"{NS}.plain", [hyp(0, "P249")], "Z249", module=MODULE),
                statement("Q249"), statement("2 ≤ 2 - 1"), statement("P249")]
        graph, payload = load(rows, LEDGER_249)
        shortlist = query.cmd_next(graph, payload, argparse.Namespace(problem="249", limit=40, sinks=12))
        main = [row["key"] for row in shortlist["shortlist"]]
        cross = [row["key"] for row in shortlist["cross_problem"]]
        self.assertNotIn("S257", main)
        self.assertIn("S257", cross)
        self.assertNotIn("W257", main)
        self.assertIn("W257", cross)
        w257 = next(row for row in shortlist["cross_problem"] if row["key"] == "W257")
        self.assertEqual(w257["belongs_to_problems"], ["257"])
        self.assertEqual(main[0], PNT)
        artifact = next(row for row in shortlist["shortlist"] if row["key"] == "2 ≤ 2 - 1")
        plain = next(row for row in shortlist["shortlist"] if row["key"] == "P249")
        self.assertTrue(artifact["artifact"])
        self.assertLess(main.index("P249"), main.index("2 ≤ 2 - 1"))
        self.assertFalse(plain["artifact"])
        packet = query.packet_markdown(graph, payload, "249", 12)
        cross_section = packet.split("## 6. Cross-problem statements")[1]
        self.assertIn("S257", cross_section)
        self.assertNotIn("`S257`", packet.split("## 6.")[0])
        self.assertIn("likely an instantiation artifact", packet)

    def test_literal_arithmetic(self) -> None:
        for text in ("2 ≤ 2 - 1", "binaryCoeffTail x (0 - 1 - 1)", "f (n - 1 + 1 - 1)", "↑(Nat.factorial 2 - 1) = 0",
                     "0 / (0 + 0) ≤ 1 / 2", "lam (0 / (0 + 1 / 2)) ≤ 1", "x + 0 = x", "a * 0 = 0"):
            self.assertTrue(builder.instantiation_artifact(text), text)
        for text in ("2 ^ 3 - 1 ∣ n", "(1 - δ) * x", "1 - 1 / 2 ^ n < 1", "x.1 - 1 = 0", "2 ^ 13 - 1 = 8191",
                     "Irrational (∑' (n : ℕ), ↑n.totient / 2 ^ n)", "1 / 2 ∈ S", "0 ≤ x", "10 / 3 < x", "2 ^ 0 = 1",
                     None):
            self.assertFalse(builder.instantiation_artifact(text), text)


if __name__ == "__main__":
    unittest.main()
