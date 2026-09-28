#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tests for ``relation_registry.py``: attestation against a declaration atlas,
the Lean namespace reader, the authority invariants of relation accounting
(slot replacements never weaken, equivalence needs both directions, strictness
needs a separator, only supply and refutation transport), kernel-probe import,
and the committed registry. Fixtures are small and built in temporary
directories; one class reads the real registry and is skipped when absent."""

from __future__ import annotations

import contextlib
import copy
import io
import json
import re
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import relation_registry as rr  # noqa: E402

MODULE = "lean/Toy/Certs.lean"
LEAN_SOURCE = """\
-- SPDX-License-Identifier: Apache-2.0
/-! A module docstring that mentions namespace Fake and end Fake. -/
namespace Toy.Certs

/-- An equivalence. -/
theorem eq_view : Equivalent (fun _ : Unit => True) (fun _ => A) (fun _ => B) := sorry_free

theorem route_view : EndpointRoute (fun _ : Unit => True) (fun _ => R) (fun _ => G) := x

section Inner
theorem inner_thm : True := trivial
end Inner

namespace Deep
theorem deep_thm : True := trivial
end Deep

theorem _root_.rootLevel : True := trivial

end Toy.Certs

theorem pending_view : Refuted (fun _ : Unit => True) (fun _ => C) := x
"""
SIGNATURES = {
    "eq_view": "theorem eq_view : Equivalent (fun _ : Unit => True) (fun _ => A) (fun _ => B)",
    "route_view": "theorem route_view : EndpointRoute (fun _ : Unit => True) (fun _ => R) (fun _ => G)",
}


def atlas_payload(signatures: dict[str, str]) -> dict:
    return {"schema": "erdos249257-declaration-atlas/1", "source_fingerprint": "sha256:" + "a" * 64,
            "declarations": [{"id": f"{MODULE}:{i}:{name}", "name": name, "kind": "theorem",
                              "module": MODULE, "line": i, "signature": sig}
                             for i, (name, sig) in enumerate(sorted(signatures.items()), 1)]}


def reg_row(rid: str, relation: str, left: str, right: str | None, declaration: str,
            digest: str | None = None, context: str = "U", module: str = MODULE) -> dict:
    return {"id": rid, "relation": relation, "problem": None, "left": left, "right": right,
            "context": context, "certificate": {"declaration": declaration, "module": module,
                                                "signature_sha256": digest},
            "sources": [{"declaration": "Toy.src", "module": module}], "note": ""}


def plain_row(rid: str, relation: str, left: str, right: str | None = None, context: str = "U",
              evidence: str = rr.EVIDENCE_ATTESTED) -> dict:
    row = reg_row(rid, relation, left, right, "Toy.Certs." + rid, context=context)
    row.update(state="attested", evidence_class=evidence)
    return row


COVERAGE_WORKFLOW = """\
jobs:
  coverage:
    steps:
      - name: Memory-bounded coverage build
        id: coverage-build
        run: >-
          python3 scripts/lean_fast_build.py --jobs 2 --lake-staleness
          {targets}

      - name: Save
"""


def write_build(root: Path, reach: str | None) -> None:
    """Write the module graph and coverage workflow that ``compiled_modules`` reads.

    ``reach`` says how ``Toy.Certs`` is compiled: ``"root"`` (the default build
    root imports it), ``"coverage"`` (a coverage-build target imports it),
    ``"none"`` (nothing reaches it) or None (no build inputs at all).
    """
    if reach is None:
        return
    root_path = root / "lean/ErdosProblems.lean"
    root_path.parent.mkdir(parents=True, exist_ok=True)
    root_path.write_text("import ErdosProblems.Core\n" + ("import Toy.Certs\n" if reach == "root" else ""),
                         encoding="utf-8")
    nodes = [{"id": "ErdosProblems.Core", "path": "lean/ErdosProblems/Core.lean", "imports": []},
             {"id": "ErdosProblems.CoverageAgg", "path": "lean/ErdosProblems/CoverageAgg.lean",
              "imports": ["Toy.Certs"] if reach == "coverage" else []},
             {"id": "Toy.Certs", "path": MODULE, "imports": []}]
    graph = {"root": "lean/ErdosProblems.lean", "additional_roots": [], "auxiliary_roots": [], "nodes": nodes}
    (root / "docs").mkdir(exist_ok=True)
    (root / "docs/claims.json").write_text(json.dumps({"machine_readable_paper": {"module_graph": graph}}),
                                           encoding="utf-8")
    workflow = root / ".github/workflows/lean-coverage-build.yml"
    workflow.parent.mkdir(parents=True, exist_ok=True)
    workflow.write_text(COVERAGE_WORKFLOW.format(targets="ErdosProblems.CoverageAgg"), encoding="utf-8")


class Fixture:
    def __init__(self, rows: list[dict], signatures: dict[str, str] | None = None, lean: bool = True,
                 reach: str | None = "root"):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "docs/research-commons/record").mkdir(parents=True)
        write_build(self.root, reach)
        if signatures is not None:
            (self.root / rr.ATLAS_PATH).write_text(json.dumps(atlas_payload(signatures)), encoding="utf-8")
        if lean:
            path = self.root / MODULE
            path.parent.mkdir(parents=True)
            path.write_text(LEAN_SOURCE, encoding="utf-8")
        self.write({"schema": rr.SCHEMA, "rows": rows})

    def write(self, document: dict) -> None:
        (self.root / rr.REGISTRY_PATH).write_text(json.dumps(document, ensure_ascii=False), encoding="utf-8")

    def read(self) -> dict:
        return json.loads((self.root / rr.REGISTRY_PATH).read_text(encoding="utf-8"))

    def close(self) -> None:
        self.tmp.cleanup()


def sha(name: str) -> str:
    return rr.sha256_text(SIGNATURES[name])


class LeanReading(unittest.TestCase):
    def test_namespaces_sections_root_and_comments(self) -> None:
        names = {d["full"] for d in rr.lean_declarations(LEAN_SOURCE)}
        self.assertEqual(names, {"Toy.Certs.eq_view", "Toy.Certs.route_view", "Toy.Certs.inner_thm",
                                 "Toy.Certs.Deep.deep_thm", "rootLevel", "pending_view"})

    def test_type_head(self) -> None:
        self.assertEqual(rr.type_head(SIGNATURES["eq_view"]), "Equivalent")
        self.assertEqual(rr.type_head("theorem t {α : Type} (h : P) : Contracts.Refuted Γ P"), "Refuted")
        self.assertIsNone(rr.type_head("theorem t : ∀ x, Equivalent Γ P Q"))
        self.assertIsNone(rr.type_head("theorem t (h : P)"))

    def test_normalise_module(self) -> None:
        for form in ("Toy.Certs", "Toy/Certs.lean", "lean/Toy/Certs.lean"):
            self.assertEqual(rr.normalise_module(form), MODULE)


class Attestation(unittest.TestCase):
    def run_check(self, rows, signatures=SIGNATURES, lean=True, reach="root"):
        fixture = Fixture(rows, signatures, lean, reach)
        self.addCleanup(fixture.close)
        return fixture, rr.check(fixture.root)

    def test_attested_row(self) -> None:
        _, report = self.run_check([reg_row("e", "equivalent", "A", "B", "Toy.Certs.eq_view", sha("eq_view"))])
        self.assertTrue(report["ok"], report["errors"])
        self.assertEqual(report["rows"][0]["state"], "attested")
        self.assertEqual(report["rows"][0]["evidence_class"], "declaration_atlas_at_pin")
        self.assertIs(report["rows"][0]["compiled_target"], True)
        self.assertIn("navigation projection", report["evidence_boundary"])

    def test_attested_through_a_coverage_build_target(self) -> None:
        _, report = self.run_check([reg_row("e", "equivalent", "A", "B", "Toy.Certs.eq_view", sha("eq_view"))],
                                   reach="coverage")
        self.assertTrue(report["ok"], report["errors"])
        self.assertEqual(report["rows"][0]["state"], "attested")
        self.assertIs(report["rows"][0]["compiled_target"], True)

    def test_listed_but_not_compiled_fails(self) -> None:
        # Atlas listing with the right hash and head is not enough: no CI job compiles the module.
        fixture, report = self.run_check(
            [reg_row("e", "equivalent", "A", "B", "Toy.Certs.eq_view", sha("eq_view"))], reach="none")
        self.assertFalse(report["ok"])
        row = report["rows"][0]
        self.assertEqual(row["state"], "listed_not_compiled")
        self.assertIs(row["compiled_target"], False)
        self.assertEqual(row["evidence_class"], "reported")
        self.assertEqual(report["counts"], {"listed_not_compiled": 1})
        self.assertIn("Toy.Certs is listed in the atlas", report["errors"][0])
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(rr.main(["--root", str(fixture.root), "check"]), 1)
        rows, _ = rr.usable_rows(fixture.root, include_pending=True)
        self.assertEqual(rows, [])

    def test_unreadable_build_inputs_attest_nothing(self) -> None:
        _, report = self.run_check([reg_row("e", "equivalent", "A", "B", "Toy.Certs.eq_view", sha("eq_view"))],
                                   reach=None)
        self.assertFalse(report["ok"])
        self.assertEqual(report["rows"][0]["state"], "mismatch")
        self.assertIsNone(report["rows"][0]["compiled_target"])
        self.assertIn("compiled module set could not be read", report["errors"][0])

    def test_pending_rows_report_compiled_target(self) -> None:
        _, report = self.run_check([reg_row("p", "refuted", "C", None, "pending_view")], reach="none")
        self.assertTrue(report["ok"], report["errors"])
        self.assertEqual(report["rows"][0]["state"], "pending_pin")
        self.assertIs(report["rows"][0]["compiled_target"], False)

    def test_hash_mismatch_fails(self) -> None:
        _, report = self.run_check([reg_row("e", "equivalent", "A", "B", "Toy.Certs.eq_view", "0" * 64)])
        self.assertFalse(report["ok"])
        self.assertEqual(report["rows"][0]["state"], "mismatch")

    def test_head_must_match_relation(self) -> None:
        # A route certificate cannot attest an equivalence, even with the right hash.
        _, report = self.run_check([reg_row("r", "equivalent", "R", "G", "Toy.Certs.route_view", sha("route_view"))])
        self.assertFalse(report["ok"])
        self.assertIn("type head", report["errors"][0])

    def test_unfilled_hash_is_a_mismatch_with_a_route(self) -> None:
        _, report = self.run_check([reg_row("e", "equivalent", "A", "B", "Toy.Certs.eq_view")])
        self.assertFalse(report["ok"])
        self.assertIn("fill-hashes", report["errors"][0])

    def test_pending_pin_with_and_without_source(self) -> None:
        rows = [reg_row("p", "refuted", "C", None, "pending_view"),
                reg_row("q", "refuted", "C", None, "Toy.Certs.no_such_theorem")]
        _, report = self.run_check(rows)
        self.assertTrue(report["ok"], report["errors"])
        states = {r["id"]: r for r in report["rows"]}
        self.assertEqual(states["p"]["state"], "pending_pin")
        self.assertTrue(states["p"]["source_present"])
        self.assertEqual(states["q"]["state"], "pending_pin")
        self.assertFalse(states["q"]["source_present"])
        self.assertEqual(states["p"]["evidence_class"], "reported")

    def test_wrong_module_is_a_mismatch(self) -> None:
        _, report = self.run_check([reg_row("e", "equivalent", "A", "B", "Toy.Certs.eq_view", sha("eq_view"),
                                            module="lean/Toy/Other.lean")])
        self.assertFalse(report["ok"])
        self.assertIn("another module", report["errors"][0])

    def test_absent_atlas_fails(self) -> None:
        _, report = self.run_check([reg_row("e", "equivalent", "A", "B", "Toy.Certs.eq_view")], signatures=None)
        self.assertFalse(report["ok"])

    def test_cli_exit_codes(self) -> None:
        fixture, _ = self.run_check([reg_row("e", "equivalent", "A", "B", "Toy.Certs.eq_view", "0" * 64)])
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(rr.main(["--root", str(fixture.root), "check"]), 1)
        fixture.write({"schema": rr.SCHEMA, "rows": [reg_row("p", "refuted", "C", None, "pending_view")]})
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(rr.main(["--root", str(fixture.root), "check"]), 0)


class Schema(unittest.TestCase):
    def base(self) -> dict:
        return {"schema": rr.SCHEMA, "rows": [reg_row("e", "equivalent", "A", "B", "Toy.Certs.eq_view")]}

    def test_valid(self) -> None:
        self.assertEqual(rr.schema_errors(self.base()), [])

    def test_rejections(self) -> None:
        cases = []
        doc = self.base(); doc["rows"][0]["attested"] = True; cases.append(("authority field", doc))
        doc = self.base(); doc["rows"][0]["relation"] = "weaker"; cases.append(("relation", doc))
        doc = self.base(); doc["rows"].append(copy.deepcopy(doc["rows"][0])); cases.append(("duplicate", doc))
        doc = self.base(); doc["rows"][0]["relation"] = "refuted"; cases.append(("unary right", doc))
        doc = self.base(); doc["rows"][0]["right"] = None; cases.append(("binary right", doc))
        doc = self.base(); doc["rows"][0]["sources"] = []; cases.append(("sources", doc))
        doc = self.base(); doc["rows"][0]["certificate"]["signature_sha256"] = "xyz"; cases.append(("hash", doc))
        doc = self.base(); doc["schema"] = "other"; cases.append(("schema", doc))
        for label, document in cases:
            with self.subTest(label):
                self.assertTrue(rr.schema_errors(document))


class Invariants(unittest.TestCase):
    def test_slot_replacement_never_weakens(self) -> None:
        slot = plain_row("s", "slot_replacement", "H", "R")
        explained = rr.explain([slot], "H")[0]
        self.assertEqual(explained["weakening"], "excluded")
        self.assertIn("never a weakening", explained["direction"])
        # R reconstructs H: the replacement gives the hypothesis, so R is at least as strong.
        ledger = rr.Ledger([slot])
        self.assertTrue(ledger.compare("U", "R", "H")["left_gives_right"])
        self.assertEqual(ledger.compare("U", "H", "R")["relation"], "necessary_converse_unknown")
        # Recording H as strictly stronger than R, or a separator of R from H, contradicts the slot.
        for bad in (plain_row("x", "strictly_stronger", "H", "R"), plain_row("y", "separates", "R", "H")):
            with self.subTest(bad["id"]):
                self.assertTrue(rr.consistency_errors([slot, bad]))

    def test_equivalence_requires_both_directions(self) -> None:
        one_way = rr.Ledger([plain_row("r", "endpoint_route", "P", "Q")])
        self.assertEqual(one_way.compare("U", "P", "Q")["relation"], "sufficient_converse_unknown")
        both = rr.Ledger([plain_row("r", "endpoint_route", "P", "Q"), plain_row("b", "endpoint_route", "Q", "P")])
        self.assertEqual(both.compare("U", "P", "Q")["relation"], "equivalent")
        self.assertEqual(rr.classes([plain_row("r", "endpoint_route", "P", "Q")]), [])

    def test_strictness_requires_a_separator(self) -> None:
        route = plain_row("r", "endpoint_route", "P", "Q")
        self.assertNotEqual(rr.Ledger([route]).compare("U", "P", "Q")["relation"], "strictly_stronger")
        separator = plain_row("s", "separates", "Q", "P")
        self.assertEqual(rr.Ledger([route, separator]).compare("U", "P", "Q")["relation"], "strictly_stronger")
        # Separates.transport: a separator of Q0 from P moves to Q when Q0 gives Q.
        transported = [route, plain_row("s0", "separates", "Q0", "P"), plain_row("q", "endpoint_route", "Q0", "Q")]
        self.assertEqual(rr.Ledger(transported).compare("U", "P", "Q")["relation"], "strictly_stronger")

    def test_unknown_stays_unknown(self) -> None:
        self.assertEqual(rr.Ledger([]).compare("U", "P", "Q")["relation"], "unknown")

    def test_transport_directions_and_refusal(self) -> None:
        rows = [plain_row("r1", "endpoint_route", "A", "B"), plain_row("r2", "endpoint_route", "B", "C"),
                plain_row("other", "endpoint_route", "A", "Z", context="V")]
        supplied = rr.transport(rows, "A", "supplied", context="U")
        moved = {m["statement"]: m["path"] for m in supplied["contexts"][0]["moved"]}
        self.assertEqual(moved, {"B": ["r1"], "C": ["r1", "r2"]})
        refuted = rr.transport(rows, "C", "refuted")
        moved = {m["statement"] for m in refuted["contexts"][0]["moved"]}
        self.assertEqual(moved, {"A", "B"})
        # Refuting A says nothing about B; supplying C says nothing about A.
        self.assertEqual(rr.transport(rows, "A", "refuted", context="U")["contexts"][0]["moved"], [])
        self.assertEqual(rr.transport(rows, "C", "supplied")["contexts"][0]["moved"], [])
        for mode in ("cost", "attempt_failed", "outcome", "timeout"):
            with self.subTest(mode):
                with self.assertRaises(rr.TransportRefused):
                    rr.transport(rows, "A", mode)

    def test_transport_respects_context(self) -> None:
        rows = [plain_row("r1", "endpoint_route", "A", "B", context="U"),
                plain_row("r2", "endpoint_route", "B", "C", context="V")]
        result = rr.transport(rows, "A", "supplied")
        moved = [m["statement"] for c in result["contexts"] for m in c["moved"]]
        self.assertEqual(moved, ["B"])

    def test_transport_flags_conflicts(self) -> None:
        rows = [plain_row("r", "endpoint_route", "A", "B"), plain_row("f", "feasible", "A")]
        refuted = rr.transport(rows, "B", "refuted")
        self.assertEqual(refuted["contexts"][0]["moved"][0]["conflicts_with"], ["f"])
        self.assertTrue(rr.consistency_errors(rows + [plain_row("x", "refuted", "B")]))

    def test_classes_union_find(self) -> None:
        rows = [plain_row("e1", "equivalent", "A", "B"), plain_row("e2", "equivalent", "B", "C"),
                plain_row("e3", "equivalent", "C", "D", context="V"),
                plain_row("p", "equivalent", "X", "Y", evidence=rr.EVIDENCE_PROBE)]
        found = rr.classes(rows)
        self.assertEqual([(c["context"], c["members"]) for c in found],
                         [("U", ["A", "B", "C"]), ("U", ["X", "Y"]), ("V", ["C", "D"])])
        self.assertEqual(found[1]["evidence_classes"], ["kernel_probe_verdict"])

    def test_deterministic(self) -> None:
        rows = [plain_row("e1", "equivalent", "A", "B"), plain_row("e2", "equivalent", "B", "C")]
        self.assertEqual(rr.canonical(rr.classes(rows)), rr.canonical(rr.classes(list(reversed(rows)))))


class FillHashes(unittest.TestCase):
    def test_fill_refuse_and_keep(self) -> None:
        rows = [reg_row("e", "equivalent", "A", "B", "Toy.Certs.eq_view"),
                reg_row("wrong", "equivalent", "R", "G", "Toy.Certs.route_view"),
                reg_row("changed", "endpoint_route", "R", "G", "Toy.Certs.route_view", "1" * 64),
                reg_row("p", "refuted", "C", None, "pending_view")]
        fixture = Fixture(rows, SIGNATURES)
        self.addCleanup(fixture.close)
        result = rr.fill_hashes(fixture.root)
        self.assertEqual(result["filled"], ["e"])
        self.assertEqual(sorted(r["id"] for r in result["refused"]), ["changed", "wrong"])
        after = {r["id"]: r["certificate"]["signature_sha256"] for r in fixture.read()["rows"]}
        self.assertEqual(after["e"], sha("eq_view"))
        self.assertIsNone(after["wrong"])
        self.assertEqual(after["changed"], "1" * 64)
        self.assertIsNone(after["p"])
        states = {r["id"]: r["state"] for r in rr.check(fixture.root)["rows"]}
        self.assertEqual(states["e"], "attested")


class ResidualBench(unittest.TestCase):
    REPORT = {"schema": "residual_evaluator/1", "module": "Bench", "tactic_budget": {"id": "b1"},
              "verdicts": [
                  {"sketch_id": "eq", "target": "T", "residuals": ["R1"], "verdict": "endpoint_equivalent",
                   "receipts": {"soundness": True, "laundering": True, "refutation": False}},
                  {"sketch_id": "strict", "target": "T", "residuals": ["R2", "R3"],
                   "verdict": "strict_decomposition_candidate",
                   "receipts": {"soundness": True, "laundering": False, "refutation": False}},
                  {"sketch_id": "ref", "target": "T", "residuals": ["R4"], "verdict": "residual_refuted",
                   "receipts": {"soundness": True, "laundering": False, "refutation": True}},
                  {"sketch_id": "unk", "target": "T", "residuals": ["R5"], "verdict": "unknown_relation",
                   "receipts": {"soundness": False, "laundering": False, "refutation": False}}]}

    def setUp(self) -> None:
        self.fixture = Fixture([reg_row("p", "refuted", "C", None, "pending_view")], SIGNATURES)
        self.addCleanup(self.fixture.close)
        (self.fixture.root / rr.RESIDUALBENCH_PATH).write_text(json.dumps(self.REPORT), encoding="utf-8")

    def test_mapping(self) -> None:
        rows = {r["id"]: r for r in rr.residualbench_rows(self.fixture.root)}
        self.assertEqual(rows["residualbench:eq"]["relation"], "equivalent")
        self.assertEqual(rows["residualbench:strict"]["relation"], "slot_replacement")
        self.assertEqual(rows["residualbench:strict"]["converse"], "unknown")
        self.assertEqual(rows["residualbench:strict"]["right"], "R2 ∧ R3")
        self.assertEqual(rows["residualbench:ref"]["relation"], "refuted")
        self.assertEqual(rows["residualbench:unk"]["relation"], "unknown")
        self.assertTrue(all(r["evidence_class"] == "kernel_probe_verdict" for r in rows.values()))

    def test_loaded_on_demand_and_never_written(self) -> None:
        before = (self.fixture.root / rr.REGISTRY_PATH).read_bytes()
        rows, _ = rr.usable_rows(self.fixture.root, include_residualbench=True)
        ids = {r["id"] for r in rows}
        self.assertIn("residualbench:eq", ids)
        self.assertNotIn("residualbench:unk", ids)  # an unknown verdict carries no edge
        self.assertEqual((self.fixture.root / rr.REGISTRY_PATH).read_bytes(), before)
        rows, _ = rr.usable_rows(self.fixture.root)
        self.assertEqual(rows, [])  # pending rows are unusable without --include-pending

    def test_explain_cli_includes_unknown_verdicts(self) -> None:
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = rr.main(["--root", str(self.fixture.root), "explain", "R5", "--include-residualbench"])
        self.assertEqual(code, 0)
        rows = json.loads(out.getvalue())["rows"]
        self.assertEqual([(r["id"], r["relation"]) for r in rows], [("residualbench:unk", "unknown")])


REAL_REGISTRY = ROOT / rr.REGISTRY_PATH
REAL_CERTS = ROOT / "lean/ErdosProblems/ArgumentGraph/Results/RelationCertificates.lean"


@unittest.skipUnless(REAL_REGISTRY.is_file() and REAL_CERTS.is_file(), "committed registry or certificates absent")
class CommittedRegistry(unittest.TestCase):
    EXPECTED = {"prime_gap_view": 251, "contour_view": 1049, "square_view": 257, "demand_G102_view": 249,
                "support_gap_route": 249, "good_base_gap_route": 249,
                "maximality_clause_refuted_off_switch": 1041, "off_switch_region_feasible": 1041}

    def test_rows_match_the_lean_certificates(self) -> None:
        document = rr.load_registry(ROOT)
        rows = {r["id"]: r for r in document["rows"]}
        self.assertEqual({k: r["problem"] for k, r in rows.items()}, self.EXPECTED)
        text = rr.strip_lean_comments(REAL_CERTS.read_text(encoding="utf-8"))
        for rid, row in rows.items():
            with self.subTest(rid):
                m = re.search(r"theorem\s+" + re.escape(rid) + r"\s*:\s*(\w+)", text)
                self.assertIsNotNone(m)
                self.assertEqual(m.group(1), rr.RELATIONS[row["relation"]])
                self.assertEqual(row["certificate"]["declaration"],
                                 "ErdosProblems.ArgumentGraph.RelationCertificates." + rid)

    def test_check_passes_and_reports_pin_state(self) -> None:
        if not (ROOT / rr.ATLAS_PATH).is_file():
            self.skipTest("declaration atlas absent")
        report = rr.check(ROOT)
        self.assertTrue(report["ok"], report["errors"])
        self.assertEqual(report["warnings"], [])  # every cited source declaration is on main
        for row in report["rows"]:
            self.assertIn(row["state"], {"attested", "pending_pin"})
            # The certificate module is a coverage-build target, so every row can reach attested.
            self.assertIs(row["compiled_target"], True)
            if row["state"] == "pending_pin":
                self.assertTrue(row["source_present"])

    def test_file_is_in_canonical_rendering(self) -> None:
        document = rr.load_registry(ROOT)
        self.assertEqual(REAL_REGISTRY.read_text(encoding="utf-8"), rr.render_registry(document))


if __name__ == "__main__":
    unittest.main()
