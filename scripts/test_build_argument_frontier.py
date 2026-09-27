#!/usr/bin/env python3
"""Tests for scripts/build_argument_frontier.py on a synthetic graph.

The weakening chain is the one a CI kernel probe found in the #249
excluded-cofactor module (run 36277692173): `prop_badcof` uses its input only
through `eventually_card_excluded_le` and `eventually_excluded_budget`, those only
through their `_of_upper` forms, which reach the dyadic prime count, which uses
the input only through `nthPrime_two_sided`.
"""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build_argument_frontier as frontier  # noqa: E402

P = "ErdosProblems.Erdos249.PaperCompleteR21"
E = f"{P}.ExcludedCofactor"


PNT = "kPNT"


def weakening(theorem: str, *vias: str) -> dict:
    # A use site `v h` proves the statement of `v` applied to the input, the
    # same statement whichever theorem's proof contains it.
    return {"theorem": theorem, "i": 0, "hypothesis": PNT, "hypothesis_type": "PrimeNumberTheorem",
            "consequences": [{"key": f"k:{v}", "type": f"C({v})", "via": [v]} for v in vias]}


def graph() -> dict:
    names = [f"{P}.prop_badcof", f"{E}.eventually_card_excluded_le", f"{E}.eventually_excluded_budget",
             f"{E}.eventually_card_excluded_le_of_upper", f"{E}.eventually_excluded_budget_of_upper",
             f"{E}.eventually_card_primes_dyadic_le", f"{E}.nthPrime_two_sided", "Toy.idle_thm"]
    return {
        "source": {"source_revision": "abc", "lean_tree": "def"},
        "theorems": [{"name": n, "module": f"{P}.ExcludedCofactorEstimate" if n != "Toy.idle_thm" else "Toy.M",
                      "problem": "249", "source": "x.lean:1",
                      "hypotheses": [PNT] if n != "Toy.idle_thm" else []} for n in names],
        "statements": [{"key": PNT, "type": "PrimeNumberTheorem", "status": "open"}]
                      + [{"key": f"k:{n}", "type": f"C({n})", "status": "open"} for n in names],
        "idle": [{"theorem": "Toy.idle_thm", "type": "∀ a, a ≤ a", "dropped": [{"i": 1, "type": "0 < a"}]}],
        "weakenings": [
            weakening(f"{P}.prop_badcof", f"{E}.eventually_card_excluded_le", f"{E}.eventually_excluded_budget"),
            weakening(f"{E}.eventually_card_excluded_le", f"{E}.eventually_card_excluded_le_of_upper"),
            weakening(f"{E}.eventually_excluded_budget", f"{E}.eventually_excluded_budget_of_upper"),
            weakening(f"{E}.eventually_excluded_budget_of_upper", f"{E}.eventually_card_excluded_le_of_upper"),
            weakening(f"{E}.eventually_card_excluded_le_of_upper", f"{E}.eventually_card_primes_dyadic_le"),
            weakening(f"{E}.eventually_card_primes_dyadic_le", f"{E}.nthPrime_two_sided"),
        ],
    }


class ChainCuts(unittest.TestCase):
    def test_cuts_are_the_levels_every_branch_reaches(self):
        index = frontier.weakening_index(graph())
        cuts = frontier.chain_cuts(f"{P}.prop_badcof", index)
        self.assertEqual(cuts, [f"{E}.eventually_card_excluded_le_of_upper",
                                f"{E}.eventually_card_primes_dyadic_le"])

    def test_unchecked_rows_are_skipped(self):
        g = graph()
        g["weakenings"][0]["kernel_checked"] = False
        self.assertNotIn(f"{P}.prop_badcof", frontier.weakening_index(g))


class Modules(unittest.TestCase):
    def test_modules_and_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "docs").mkdir()
            ledger = {"rows": [
                {"id": "p#res:badcof", "label": "res:badcof", "paper_id": "p", "side": "long", "problem": 249,
                 "lean": {"status": "modulo_named_input", "declarations": [{"name": f"{P}.prop_badcof"}]}},
                {"id": "p#res:idle", "label": "res:idle", "paper_id": "p", "side": "short", "problem": 249,
                 "lean": {"status": "exact", "declarations": [{"name": "Toy.idle_thm"}]}}]}
            (root / "docs" / "paper_lean_coverage.json").write_text(json.dumps(ledger))
            path = root / "g.json"
            path.write_text(json.dumps(graph()))
            self.assertEqual(frontier.main(["--graph", str(path), "--root", str(root)]), 0)
            text = (root / frontier.DERIVED / "Erdos249.lean").read_text()
            self.assertIn("import ErdosProblems.ArgumentGraph.Derive", text)
            self.assertIn("set_option argumentGraph.strict true", text)
            self.assertIn("derive_idle Toy.idle_thm", text)
            self.assertIn(f"derive_weakening {P}.prop_badcof", text)
            self.assertIn(f"derive_frontier {P}.prop_badcof\n", text)
            self.assertIn(f"derive_frontier {P}.prop_badcof at {E}.eventually_card_primes_dyadic_le", text)
            # only paper-cited theorems get commands
            self.assertNotIn(f"derive_weakening {E}.eventually_card_excluded_le\n", text)
            manifest = json.loads((root / "docs" / "argument_frontier.json").read_text())
            ops = sorted(r["operation"] for r in manifest["rows"]["Erdos249"])
            self.assertEqual(ops, ["idle", "weakening"])
            self.assertEqual(frontier.main(["--graph", str(path), "--root", str(root), "--check"]), 0)

    def test_named_input_levels(self):
        g = graph()
        papers = {f"{P}.prop_badcof": [{"row": "p#res:badcof", "label": "res:badcof",
                                          "lean_status": "modulo_named_input"}]}
        inputs = frontier.named_inputs(g, papers, frontier.weakening_index(g))
        self.assertEqual([i["statement"] for i in inputs], ["PrimeNumberTheorem"])
        levels = [[c["type"] for c in level] for level in inputs[0]["consumers"][0]["levels"]]
        self.assertEqual(levels, [
            [f"C({E}.eventually_card_excluded_le)", f"C({E}.eventually_excluded_budget)"],
            [f"C({E}.eventually_card_excluded_le_of_upper)", f"C({E}.eventually_excluded_budget_of_upper)"],
            [f"C({E}.eventually_card_primes_dyadic_le)"],
            [f"C({E}.nthPrime_two_sided)"]])

    def test_supplied_consequence_gives_a_using_command(self):
        g = graph()
        g["theorems"].append({"name": "Toy.chebyshev", "module": "Toy.Cheb", "problem": "249", "hypotheses": []})
        for st in g["statements"]:
            if st["key"] == f"k:{E}.eventually_card_primes_dyadic_le":
                st["status"], st["witness"] = "supplied", "Toy.chebyshev"
        index = frontier.weakening_index(g)
        theorems = {t["name"]: t for t in g["theorems"]}
        statements = {st["key"]: st for st in g["statements"]}
        self.assertEqual(frontier.chain_suppliers(f"{P}.prop_badcof", index, statements, theorems),
                         ["Toy.chebyshev"])
        papers = {f"{P}.prop_badcof": [{"row": "r", "label": "l", "lean_status": "modulo_named_input"}]}
        slot = frontier.plan(g, papers)["Erdos249"]
        self.assertIn(f"derive_frontier {P}.prop_badcof using Toy.chebyshev", slot["supplied_commands"])
        self.assertIn("Toy.Cheb", slot["imports"])
        text = frontier.render_module("Erdos249", slot, g["source"])
        self.assertIn(f"set_option argumentGraph.strict false in derive_frontier {P}.prop_badcof using Toy.chebyshev", text)

    def test_lean_ident_escapes(self):
        self.assertEqual(frontier.lean_ident("A.b_c.d'"), "A.b_c.d'")
        self.assertEqual(frontier.lean_ident("A.1x"), "A.«1x»")


if __name__ == "__main__":
    unittest.main()
