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
            self.assertIn("import ErdosProblems.ArgumentGraph.Factor", text)
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

    def test_paper_macros(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "docs").mkdir()
            ledger = {"rows": [{"id": "p#r", "label": "r", "paper_id": "p", "side": "long", "problem": 249,
                                "lean": {"status": "modulo_named_input",
                                         "declarations": [{"name": f"{P}.prop_badcof"}]}}]}
            (root / "docs" / "paper_lean_coverage.json").write_text(json.dumps(ledger))
            path = root / "g.json"
            path.write_text(json.dumps(graph()))
            paper = root / "paper.tex"
            paper.write_text("x\n% BEGIN generated_argument_frontier_macros\nold\n"
                             "% END generated_argument_frontier_macros\ny\n")
            self.assertEqual(frontier.main(["--graph", str(path), "--root", str(root), "--paper", str(paper)]), 0)
            text = paper.read_text()
            self.assertIn(r"\newcommand{\AFWeakened}{1}", text)
            self.assertIn(r"\newcommand{\AFCuts}{2}", text)
            self.assertIn(r"\newcommand{\AFNamedInputs}{1}", text)
            self.assertNotIn("old", text)

    def test_probe_verdicts_prune_and_promote(self):
        # A strict command the probe shows added nothing is dropped with its row; a
        # candidate that added theorems becomes strict and its row a `conjuncts` row;
        # a command the probe did not reach stays where it was.
        g = graph()
        g["theorems"].append({"name": f"{P}.bundle", "module": f"{P}.M", "problem": "249",
                              "hypotheses": [PNT], "conclusion_type": "A ∧ B"})
        papers = {f"{P}.prop_badcof": [{"row": "r", "label": "l", "lean_status": "modulo_named_input"}],
                  "Toy.idle_thm": [{"row": "s", "label": "m", "lean_status": "exact"}],
                  f"{P}.bundle": [{"row": "t", "label": "n", "lean_status": "modulo_named_input"}]}
        per_problem = frontier.plan(g, papers)
        verdicts = {"probe_run": "1", "commands": {
            "derive_idle Toy.idle_thm": {"added": False, "message": "its proof uses every hypothesis"},
            f"derive_conjuncts {P}.bundle": {"added": True, "message": ""}}}
        dropped, lost = frontier.apply_verdicts(per_problem, verdicts)
        self.assertEqual(lost, [])
        slot = per_problem["Erdos249"]
        self.assertEqual([d["command"] for d in dropped], ["derive_idle Toy.idle_thm"])
        self.assertIn(f"derive_conjuncts {P}.bundle", slot["commands"])
        self.assertNotIn(f"derive_conjuncts {P}.bundle", slot["supplied_commands"])
        self.assertIn(f"derive_weakening {P}.prop_badcof", slot["commands"])
        ops = sorted(r["operation"] for r in slot["rows"])
        # the bundle is also a factoring candidate, which this probe did not reach
        self.assertEqual(ops, ["conjuncts", "factor_candidate", "weakening"])

    def test_structured_paper_theorems_are_factoring_candidates(self):
        g = graph()
        g["theorems"].append({"name": f"{P}.construction", "module": f"{P}.C", "problem": "249",
                              "hypotheses": [], "schematic_hypotheses": ["0 < ε"],
                              "conclusion_type": "∃ w, A w ∧ B w"})
        g["theorems"].append({"name": f"{P}.plain", "module": f"{P}.C", "problem": "249",
                              "hypotheses": [PNT], "conclusion_type": "A"})
        papers = {f"{P}.construction": [{"row": "r", "label": "l", "lean_status": "exact"}],
                  f"{P}.plain": [{"row": "s", "label": "m", "lean_status": "exact"}]}
        slot = frontier.plan(g, papers)["Erdos249"]
        self.assertIn(f"derive_factor {P}.construction", slot["supplied_commands"])
        self.assertNotIn(f"derive_factor {P}.plain", slot["supplied_commands"])
        verdicts = {"probe_run": "2", "commands": {f"derive_factor {P}.construction": {
            "added": True, "names": [f"{P}.lemma.factored", f"{P}.construction.factored"],
            "statements": {f"{P}.construction.factored": "∃ w, A w ∧ (H → B w)"}, "message": ""}}}
        frontier.apply_verdicts({"Erdos249": slot}, verdicts)
        self.assertIn(f"derive_factor {P}.construction", slot["commands"])
        row = next(r for r in slot["rows"] if r["theorem"] == f"{P}.construction")
        self.assertEqual(row["operation"], "factored")
        self.assertEqual(row["derived"], [f"{P}.lemma.factored", f"{P}.construction.factored"])

    def test_a_published_command_is_retained_and_its_loss_stops_the_build(self):
        # The new graph proposes nothing for `Toy.gone`, but the published module ran
        # `derive_idle Toy.gone`: the plan carries it, and a probe verdict that it adds
        # nothing is a loss unless the command is retired.
        g = graph()
        papers = {f"{P}.prop_badcof": [{"row": "r", "label": "l", "lean_status": "modulo_named_input"}]}
        published = frontier.parse_module(
            "import ErdosProblems.ArgumentGraph.Factor\nimport Toy.Old\n\nderive_idle Toy.gone\n"
            f"derive_weakening {P}.prop_badcof\n"
            f"{frontier.NONSTRICT}derive_conjuncts Toy.maybe\n")
        self.assertEqual(published["imports"], {"Toy.Old"})
        per_problem = frontier.plan(g, papers, {"Erdos249": published})
        slot = per_problem["Erdos249"]
        self.assertEqual(slot["commands"].count(f"derive_weakening {P}.prop_badcof"), 1)
        self.assertIn("derive_idle Toy.gone", slot["commands"])
        self.assertEqual(slot["retained"], ["derive_idle Toy.gone"])
        self.assertIn("Toy.Old", slot["imports"])
        self.assertIn("derive_conjuncts Toy.maybe", slot["supplied_commands"])
        verdicts = {"probe_run": "3", "commands": {"derive_idle Toy.gone": {"added": False, "message": "gone"}}}
        dropped, lost = frontier.apply_verdicts(per_problem, verdicts)
        self.assertEqual([e["command"] for e in lost], ["derive_idle Toy.gone"])
        self.assertIn("derive_idle Toy.gone", slot["commands"])
        per_problem = frontier.plan(g, papers, {"Erdos249": published})
        dropped, lost = frontier.apply_verdicts(per_problem, verdicts, {"derive_idle Toy.gone"})
        self.assertEqual(lost, [])
        self.assertEqual([e["command"] for e in dropped], ["derive_idle Toy.gone"])

    def test_main_stops_on_a_loss_and_on_a_restated_name(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "docs").mkdir()
            ledger = {"rows": [{"id": "p#r", "label": "r", "paper_id": "p", "side": "long", "problem": 249,
                                "lean": {"status": "modulo_named_input",
                                         "declarations": [{"name": f"{P}.prop_badcof"}]}}]}
            (root / "docs" / "paper_lean_coverage.json").write_text(json.dumps(ledger))
            path = root / "g.json"
            path.write_text(json.dumps(graph()))
            module = root / frontier.DERIVED / "Erdos249.lean"
            module.parent.mkdir(parents=True)
            module.write_text("import ErdosProblems.ArgumentGraph.Factor\n\nderive_idle Toy.gone\n")
            verified = root / "v.json"
            verified.write_text(json.dumps({"probe_run": "4", "commands": {
                "derive_idle Toy.gone": {"added": False, "message": "no"}}}))
            self.assertEqual(frontier.main(["--graph", str(path), "--root", str(root),
                                            "--verified", str(verified)]), 4)
            self.assertEqual(frontier.main(["--graph", str(path), "--root", str(root), "--verified",
                                            str(verified), "--retire", "derive_idle Toy.gone"]), 0)
            # the manifest now records the weakening's statement and hash; a later probe
            # reporting another hash for the same name stops the regeneration
            (root / "docs" / "argument_frontier.json").write_text(json.dumps({"derived": {
                f"{P}.prop_badcof.weakened_0": {"statement": "S", "hash": "aa", "command": "c"}}}))
            verified.write_text(json.dumps({"probe_run": "5", "commands": {},
                                            "statement_hashes": {f"{P}.prop_badcof.weakened_0": "bb"}}))
            module.write_text("import ErdosProblems.ArgumentGraph.Factor\n")
            self.assertEqual(frontier.main(["--graph", str(path), "--root", str(root),
                                            "--verified", str(verified)]), 4)

    def test_a_name_two_modules_would_declare_is_found(self):
        per_problem = {"Erdos249": {"commands": ["derive_factor A.x"], "rows": []},
                       "Erdos257": {"commands": ["derive_factor B.y"], "rows": []}}
        verified = {"commands": {
            "derive_factor A.x": {"added": True, "names": ["A.x.factored", "Shared.lemma.factored"]},
            "derive_factor B.y": {"added": True, "names": ["B.y.factored", "Shared.lemma.factored"]}}}
        self.assertEqual(frontier.duplicate_declarations(per_problem, verified),
                         {"Shared.lemma.factored": ["Erdos249", "Erdos257"]})

    def test_probes_inline_the_library(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lib = root / "lean" / "ErdosProblems" / "ArgumentGraph"
            lib.mkdir(parents=True)
            (lib / "Derive.lean").write_text("import Lean\nregister_option argumentGraph.strict : Bool := {\n"
                                             "  defValue := false\n}\ndef derivePart := 1\n")
            (lib / "Factor.lean").write_text("import ErdosProblems.ArgumentGraph.Derive\ndef factorPart := 2\n")
            slot = {"imports": {"Toy.M"}, "commands": ["derive_idle Toy.a"], "supplied_commands": ["derive_factor Toy.b"]}
            text = frontier.probe_text(root, "Erdos249", slot)
            self.assertTrue(text.startswith("import Lean\nimport Toy.M\n"))
            self.assertNotIn("register_option", text)
            self.assertNotIn("import ErdosProblems.ArgumentGraph", text)
            self.assertLess(text.index("derivePart"), text.index("factorPart"))
            self.assertLess(text.index("derive_idle Toy.a"), text.index("derive_factor Toy.b"))
            self.assertIn("DERIVED", text)
            lines = text.splitlines()
            for i, line in enumerate(lines):
                if "@@COMMAND" in line and line.startswith("run_cmd"):
                    number = int(line.split("@@COMMAND ")[1].rstrip('"'))
                    self.assertEqual(number, i + 2)
                    self.assertTrue(lines[i + 1].startswith("derive_"))

    def test_lean_ident_escapes(self):
        self.assertEqual(frontier.lean_ident("A.b_c.d'"), "A.b_c.d'")
        self.assertEqual(frontier.lean_ident("A.1x"), "A.«1x»")


if __name__ == "__main__":
    unittest.main()
