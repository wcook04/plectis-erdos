#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Tests for ``compile_research_packet.py``: exact selection against brute force,
AND groups kept whole, refusal with an infeasible core, withholding and its
taint, cutoff and family exclusion, span binding with required literals,
contrast obligations, deterministic output, and the handoff manifest shape.
Every repository is a small fixture in a temporary directory. When the private
handoff builder is present the manifest is also run through its own
normaliser in dry-run mode; that test is skipped elsewhere."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import itertools
import json
import os
import random
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import compile_research_packet as crp  # noqa: E402
import contrast_ledger as cl  # noqa: E402

BUILDER = Path(os.environ.get(
    "PLECTIS_HANDOFF_BUILDER",
    str(Path.home() / "src/ai_workflow/tools/meta/bridge/type_b_handoff_bundle.py")))

LEAN = """namespace Demo

/-- The definition. -/
def term (n : Nat) : Nat := n + 1

/-- A fact with a telescope. -/
theorem fact_hn {k n : Nat} (hk : k < n) (hn : 0 < n) : 0 < n := by
  exact hn

theorem relation_view : True := trivial

end Demo
"""


def write(root: Path, rel: str, text: str) -> None:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def numbered(prefix: str, count: int, width: int = 40) -> str:
    return "".join(f"{prefix} {i:03d} ".ljust(width, "x") + "\n" for i in range(1, count + 1))


def contrast_row(row_id: str = "c-demo", problems: tuple[int, ...] = (7,)) -> dict:
    return {
        "id": row_id, "title": "Demo distinction",
        "distinction": "A hypothesis redundant in a telescope can fail on its own.",
        "wrong_reading": "Dropped everywhere.", "right_reading": "Judged in its telescope.",
        "evidence": [
            {"kind": "source_span", "path": "notes/A.md", "start_line": 2, "end_line": 3,
             "must_contain": ["alpha 002"]},
            {"kind": "declaration", "name": "fact_hn", "module": "lean/Demo.lean"},
            {"kind": "relation", "id": "rel-demo"},
        ],
        "provenance": [{"kind": "note", "ref": "fixture", "detail": "Made for the test."}],
        "triggers": {"problems": list(problems), "declarations": ["fact_hn"], "phrases": []},
        "uses": {"packet_obligation": True, "return_gate": "Name the telescope.",
                 "regression": None, "experiment": None},
    }


class Repo:
    """A fixture repository read from the working tree (ref=None)."""

    def __init__(self, test: unittest.TestCase) -> None:
        self.tmp = tempfile.mkdtemp(prefix="research-packet-")
        test.addCleanup(shutil.rmtree, self.tmp, True)
        self.root = Path(self.tmp) / "repo"
        write(self.root, "notes/A.md", numbered("alpha", 20))
        write(self.root, "notes/B.md", numbered("beta", 20))
        write(self.root, "notes/C.md", numbered("gamma", 20))
        write(self.root, "lean/Demo.lean", LEAN)
        write(self.root, cl.ATLAS_PATH, json.dumps({"declarations": [
            {"name": "term", "module": "lean/Demo.lean", "line": 4},
            {"name": "fact_hn", "module": "lean/Demo.lean", "line": 7}]}))
        write(self.root, cl.RELATIONS_PATH, json.dumps({"rows": [
            {"id": "rel-demo", "certificate": {"declaration": "Demo.relation_view",
                                               "module": "lean/Demo.lean"}}]}))
        write(self.root, cl.LEDGER_PATH, json.dumps({"schema": cl.SCHEMA,
                                                     "rows": [contrast_row()]}))

    def out(self, name: str = "out") -> Path:
        return Path(self.tmp) / name

    def compile(self, spec: dict, **kwargs) -> dict:
        kwargs.setdefault("ref", None)
        return crp.compile_packet(spec, self.root, **kwargs)


def span(rid: str, path: str, start: int, end: int, **extra) -> dict:
    must = extra.pop("must_contain", [])
    return {"id": rid, "kind": "source_span", "path": path, "start_line": start,
            "end_line": end, "must_contain": must, **extra}


def base_spec(**overrides) -> dict:
    spec = {
        "packet_id": "demo_packet", "title": "Demo packet",
        "target": {"problem": 99, "anchor": "Demo target", "declarations": []},
        "byte_budget": 100_000, "mandatory": ["target"],
        "resources": [
            span("target", "notes/A.md", 1, 1, must_contain=["alpha 001"]),
            span("b-short", "notes/B.md", 1, 2),
            span("b-long", "notes/B.md", 5, 15),
            span("c-part", "notes/C.md", 1, 3),
        ],
        "obligations": [
            {"id": "ob-1", "origin": "authored", "alternatives": [["b-long"], ["b-short", "c-part"]]},
        ],
        "withheld": [], "excluded_families": [], "include_triggered_contrasts": False,
    }
    spec.update(overrides)
    return spec


def satisfied(selected: frozenset, requirement: crp.Requirement) -> bool:
    return any(a <= selected for a in requirement.alternatives)


class CoverModelTests(unittest.TestCase):
    def brute_force(self, units, requirements, base, budget):
        ids = sorted(units)
        best = None
        for size in range(len(ids) + 1):
            for combo in itertools.combinations(ids, size):
                chosen = frozenset(combo)
                if not base <= chosen or not all(satisfied(chosen, r) for r in requirements):
                    continue
                cost = crp.set_cost(units, chosen)
                if budget is not None and cost > budget:
                    continue
                if best is None or cost < best:
                    best = cost
        return best

    def test_exhaustive_small_models_match_brute_force(self) -> None:
        rng = random.Random(20260928)
        for trial in range(300):
            count = rng.randint(3, 7)
            ids = [f"r{i}" for i in range(count)]
            # Some resources share content, so their bytes are paid once.
            units = {rid: (f"k{rng.randint(0, count - 2)}", 0) for rid in ids}
            sizes = {key: rng.randint(1, 30) for key, _ in units.values()}
            units = {rid: (key, sizes[key]) for rid, (key, _) in units.items()}
            requirements = []
            for n in range(rng.randint(1, 4)):
                alternatives = {frozenset(rng.sample(ids, rng.randint(1, 3)))
                                for _ in range(rng.randint(0, 3))}
                requirements.append(crp.Requirement(f"o{n}", tuple(sorted(
                    alternatives, key=lambda s: tuple(sorted(s))))))
            base = frozenset(rng.sample(ids, rng.randint(0, 1)))
            budget = rng.choice([None, rng.randint(5, 80)])
            result = crp.minimum_cover(units, requirements, base, budget)
            expected = self.brute_force(units, requirements, base, budget)
            with self.subTest(trial=trial):
                self.assertTrue(result.complete)
                self.assertEqual(result.cost, expected)
                if result.selected is not None:
                    self.assertTrue(base <= result.selected)
                    self.assertTrue(all(satisfied(result.selected, r) for r in requirements))

    def test_state_budget_marks_the_search_incomplete(self) -> None:
        units = {f"r{i}": (f"k{i}", i + 1) for i in range(8)}
        requirements = [crp.Requirement(f"o{i}", (frozenset({f"r{i}"}), frozenset({f"r{i + 4}"})))
                        for i in range(4)]
        result = crp.minimum_cover(units, requirements, state_budget=2)
        self.assertFalse(result.complete)

    def test_core_is_deletion_minimal(self) -> None:
        units = {"a": ("a", 6), "b": ("b", 6), "c": ("c", 1)}
        requirements = [crp.Requirement("need-a", (frozenset({"a"}),)),
                        crp.Requirement("need-b", (frozenset({"b"}),)),
                        crp.Requirement("need-c", (frozenset({"c"}),))]
        core = crp.irreducible_budget_core(units, requirements, frozenset(), budget=10)
        self.assertEqual(core["status"], "deletion_minimal")
        self.assertEqual(core["obligations"], ["need-a", "need-b"])


class SelectionTests(unittest.TestCase):
    def test_cheapest_alternative_and_and_groups_kept_whole(self) -> None:
        repo = Repo(self)
        result = repo.compile(base_spec())
        receipt = result["receipt"]
        self.assertEqual(result["status"], "compiled")
        self.assertEqual(receipt["optimality"], "optimal_in_declared_model")
        # b-short alone is cheapest but only covers with c-part; the pair beats b-long.
        self.assertEqual(receipt["selected"], ["b-short", "c-part", "target"])
        witness = receipt["obligations"][0]["witness"]
        self.assertEqual(witness, ["b-short", "c-part"])
        bundle = result["manifest"]["bundles"][0]
        self.assertEqual(bundle["bundle_id"], "ob-1")
        self.assertEqual(len(bundle["files"]), 2)

    def test_and_group_is_never_split_under_a_tight_budget(self) -> None:
        repo = Repo(self)
        spec = base_spec()
        pair_cost = repo.compile(spec)["receipt"]["bytes"]["total"]
        # One byte short of the pair: b-short alone would fit but never covers ob-1.
        result = repo.compile(spec, budget=pair_cost - 1)
        receipt = result["receipt"]
        if result["status"] == "compiled":
            self.assertIn("b-long", receipt["selected"])
        else:
            self.assertEqual(result["status"], "refused_infeasible_in_declared_model")
        self.assertNotEqual(receipt.get("selected"), ["b-short", "target"])

    def test_mandatory_over_budget_refuses_with_its_obligation(self) -> None:
        repo = Repo(self)
        result = repo.compile(base_spec(), budget=10)
        self.assertEqual(result["status"], "refused_mandatory_over_budget")
        self.assertIsNone(result["manifest"])
        self.assertEqual(result["receipt"]["unmet_obligations"][0]["id"], "mandatory")

    def test_budget_refusal_returns_unmet_obligations_and_core(self) -> None:
        repo = Repo(self)
        spec = base_spec(obligations=[
            {"id": "need-b", "origin": "authored", "alternatives": [["b-long"]]},
            {"id": "need-c", "origin": "authored", "alternatives": [["c-part"]]},
        ])
        full = repo.compile(spec)["receipt"]["bytes"]["total"]
        result = repo.compile(spec, budget=full - 1)
        self.assertEqual(result["status"], "refused_infeasible_in_declared_model")
        receipt = result["receipt"]
        self.assertEqual(receipt["infeasible_core"]["status"], "deletion_minimal")
        self.assertEqual(sorted(u["id"] for u in receipt["unmet_obligations"]),
                         receipt["infeasible_core"]["obligations"])
        self.assertTrue(receipt["infeasible_core"]["obligations"])

    def test_small_state_budget_is_never_called_optimal(self) -> None:
        repo = Repo(self)
        result = repo.compile(base_spec(state_budget=1))
        self.assertIn(result["status"], {"compiled", "refused_search_incomplete"})
        self.assertNotEqual(result["receipt"].get("optimality"), "optimal_in_declared_model")


class WithholdingTests(unittest.TestCase):
    def test_withheld_taint_moves_through_dependencies_and_overlap(self) -> None:
        repo = Repo(self)
        resources = base_spec()["resources"] + [
            span("b-over", "notes/B.md", 14, 18),
            span("dep-on-long", "notes/C.md", 10, 10, depends_on=["b-long"]),
        ]
        spec = base_spec(resources=resources, withheld=["b-long"], obligations=[
            {"id": "ob-1", "origin": "authored",
             "alternatives": [["dep-on-long"], ["b-over"], ["b-short", "c-part"]]}])
        result = repo.compile(spec)
        blocked = result["receipt"]["blocked"]
        self.assertEqual(blocked["b-long"], "withheld")
        self.assertTrue(blocked["dep-on-long"].startswith("depends_on_blocked_material"))
        self.assertTrue(blocked["b-over"].startswith("overlaps_blocked_material"))
        self.assertEqual(result["receipt"]["obligations"][0]["witness"], ["b-short", "c-part"])
        self.assertEqual(len(result["receipt"]["obligations"][0]["dropped_alternatives"]), 2)

    def test_withheld_path_blocks_every_span_of_the_file(self) -> None:
        repo = Repo(self)
        result = repo.compile(base_spec(withheld=["notes/B.md"]))
        self.assertEqual(result["status"], "refused_infeasible_in_declared_model")
        self.assertEqual(result["receipt"]["unmet_obligations"],
                         [{"id": "ob-1", "reason": "all_alternatives_blocked"}])

    def test_blocked_mandatory_refuses(self) -> None:
        repo = Repo(self)
        result = repo.compile(base_spec(withheld=["target"]))
        self.assertEqual(result["status"], "refused_mandatory_blocked")

    def test_cutoff_blocks_late_and_undated_material(self) -> None:
        repo = Repo(self)
        resources = [dict(r, available_at="2026-01-01T00:00:00Z") for r in base_spec()["resources"]]
        resources[1]["available_at"] = "2026-12-01T00:00:00Z"  # b-short arrives late
        del resources[3]["available_at"]  # c-part has no date
        result = repo.compile(base_spec(resources=resources, cutoff="2026-06-01T00:00:00+00:00"))
        blocked = result["receipt"]["blocked"]
        self.assertEqual(blocked["b-short"], "after_cutoff")
        self.assertEqual(blocked["c-part"], "availability_unknown_before_cutoff")
        self.assertEqual(result["receipt"]["obligations"][0]["witness"], ["b-long"])

    def test_excluded_family_is_blocked(self) -> None:
        repo = Repo(self)
        resources = base_spec()["resources"]
        resources[2] = dict(resources[2], family="held")
        result = repo.compile(base_spec(resources=resources, excluded_families=["held"]))
        self.assertEqual(result["receipt"]["blocked"]["b-long"], "held_out_family")

    def test_unknown_withheld_name_is_a_spec_error(self) -> None:
        with self.assertRaises(crp.SpecError):
            Repo(self).compile(base_spec(withheld=["nothing"]))


class BindingTests(unittest.TestCase):
    def test_hash_valid_wrong_window_is_rejected_by_must_contain(self) -> None:
        repo = Repo(self)
        resources = base_spec()["resources"]
        # The literal is in the file, on line 1, outside the cited window.
        resources[1] = span("b-short", "notes/B.md", 2, 3, must_contain=["beta 001"])
        with self.assertRaises(crp.SpecError) as raised:
            repo.compile(base_spec(resources=resources))
        self.assertIn("literals outside", str(raised.exception))

    def test_excerpt_header_names_path_lines_and_file_hash(self) -> None:
        repo = Repo(self)
        result = repo.compile(base_spec())
        target = next(r for r in result["receipt"]["resources"] if r["id"] == "target")
        body = result["excerpts"][f"excerpts/{target['excerpt_sha256']}.md"].decode("utf-8")
        file_sha = cl.sha256_hex((repo.root / "notes/A.md").read_bytes())
        self.assertIn("- Path: `notes/A.md`", body)
        self.assertIn("- Lines: 1-1", body)
        self.assertIn(f"- File SHA-256: {file_sha}", body)
        self.assertIn("alpha 001", body)
        self.assertEqual(target["file_sha256"], file_sha)
        self.assertEqual(cl.sha256_hex(body.encode("utf-8")), target["excerpt_sha256"])

    def test_declaration_resource_resolves_to_its_span(self) -> None:
        repo = Repo(self)
        spec = base_spec(resources=base_spec()["resources"] + [
            {"id": "decl", "kind": "declaration", "name": "fact_hn", "path": "lean/Demo.lean"}],
            mandatory=["target", "decl"])
        record = next(r for r in repo.compile(spec)["receipt"]["resources"] if r["id"] == "decl")
        self.assertEqual((record["start_line"], record["end_line"]), (6, 8))
        self.assertEqual(record["evidence_class"], "declaration_atlas_at_pin")

    @unittest.skipUnless(shutil.which("git"), "git is unavailable")
    def test_spans_bind_to_head_bytes(self) -> None:
        repo = Repo(self)
        for args in (("init", "-q"), ("add", "-A"), ("commit", "-q", "-m", "fixture")):
            subprocess.run(["git", "-C", str(repo.root), "-c", "user.name=f",
                            "-c", "user.email=f@example.invalid", "-c", "commit.gpgsign=false",
                            *args], check=True, capture_output=True)
        write(repo.root, "notes/A.md", "rewritten\n" * 20)
        result = repo.compile(base_spec(), ref="HEAD")
        target = next(r for r in result["receipt"]["resources"] if r["id"] == "target")
        self.assertEqual(target["binding"], "git_ref")
        self.assertIn(b"alpha 001", result["excerpts"][f"excerpts/{target['excerpt_sha256']}.md"])
        self.assertEqual(len(result["receipt"]["source"]["commit"]), 40)


class ContrastTests(unittest.TestCase):
    def spec(self, **overrides) -> dict:
        return base_spec(target={"problem": 7, "anchor": "Demo target", "declarations": []},
                         include_triggered_contrasts=True, **overrides)

    def test_triggered_contrast_becomes_one_and_group(self) -> None:
        repo = Repo(self)
        result = repo.compile(self.spec())
        receipt = result["receipt"]
        contrast = next(o for o in receipt["obligations"] if o["id"] == "contrast-c-demo")
        self.assertEqual(contrast["origin"], "contrast:c-demo")
        self.assertEqual(contrast["alternatives"], [["contrast-c-demo-e1", "contrast-c-demo-e2",
                                                     "contrast-c-demo-e3"]])
        self.assertEqual(contrast["witness"], contrast["alternatives"][0])
        relation = next(r for r in receipt["resources"] if r["id"] == "contrast-c-demo-e3")
        self.assertEqual(relation["name"], "Demo.relation_view")
        gates = result["manifest"]["ask_type_b"]["disconfirming_check"]
        self.assertEqual(gates, ["[c-demo] Name the telescope."])

    def test_untriggered_contrast_is_absent(self) -> None:
        receipt = Repo(self).compile(base_spec(include_triggered_contrasts=True))["receipt"]
        self.assertEqual([o["id"] for o in receipt["obligations"]], ["ob-1"])

    def test_authored_obligation_replaces_the_derived_one(self) -> None:
        repo = Repo(self)
        obligations = base_spec()["obligations"] + [
            {"id": "my-view", "origin": "contrast:c-demo", "alternatives": [["c-part"]]}]
        receipt = repo.compile(self.spec(obligations=obligations))["receipt"]
        self.assertEqual([o["id"] for o in receipt["obligations"]], ["ob-1", "my-view"])
        self.assertIn({"id": "c-demo", "selection": "replaced_by_authored_obligation"},
                      receipt["contrast_selection"])

    def test_contrast_evidence_cannot_be_dropped_by_the_budget(self) -> None:
        repo = Repo(self)
        without = repo.compile(base_spec())["receipt"]["bytes"]["total"]
        result = repo.compile(self.spec(), budget=without)
        self.assertEqual(result["status"], "refused_infeasible_in_declared_model")
        self.assertIn("contrast-c-demo", result["receipt"]["infeasible_core"]["obligations"])


class OutputTests(unittest.TestCase):
    def test_two_runs_are_byte_identical(self) -> None:
        repo = Repo(self)
        spec = base_spec(include_triggered_contrasts=True,
                         target={"problem": 7, "anchor": "Demo", "declarations": []})
        outputs = []
        for name in ("one", "two"):
            out = repo.out(name)
            crp.write_outputs(repo.compile(spec), out)
            outputs.append({p.relative_to(out).as_posix(): p.read_bytes()
                            for p in sorted(out.rglob("*")) if p.is_file()})
        self.assertEqual(outputs[0], outputs[1])
        self.assertIn(crp.MANIFEST_NAME, outputs[0])
        self.assertIn(crp.RECEIPT_NAME, outputs[0])

    def test_manifest_shape_places_each_excerpt_once(self) -> None:
        repo = Repo(self)
        spec = base_spec(include_triggered_contrasts=True,
                         target={"problem": 7, "anchor": "Demo", "declarations": []})
        result = repo.compile(spec)
        manifest = result["manifest"]
        self.assertEqual(manifest["schema"], "type_b_handoff_manifest_v1")
        self.assertNotIn(crp.RECEIPT_NAME, json.dumps(manifest))
        self.assertEqual([b["bundle_id"] for b in manifest["bundles"]], ["ob-1", "contrast-c-demo"])
        paths = [f["path"] for f in manifest["top_level"]["files"]]
        paths += [f["path"] for b in manifest["bundles"] for f in b["files"]]
        self.assertEqual(len(paths), len(set(paths)))
        self.assertEqual(sorted(paths), sorted(result["excerpts"]))
        for bundle in manifest["bundles"]:
            for spec_row in bundle["files"]:
                self.assertEqual(spec_row["path"], f"excerpts/{spec_row['entry_id']}.md")

    def test_write_refuses_foreign_files_and_needs_replace(self) -> None:
        repo = Repo(self)
        result = repo.compile(base_spec())
        out = repo.out()
        crp.write_outputs(result, out)
        with self.assertRaises(crp.SpecError):
            crp.write_outputs(result, out)
        crp.write_outputs(result, out, replace=True)
        write(out, "stray.txt", "x")
        with self.assertRaises(crp.SpecError):
            crp.write_outputs(result, out, replace=True)

    def test_cli_exit_codes(self) -> None:
        repo = Repo(self)
        spec_path = Path(repo.tmp) / "spec.json"
        spec_path.write_text(json.dumps(base_spec()), encoding="utf-8")
        common = ["compile", str(spec_path), "--root", str(repo.root), "--worktree"]
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(crp.main(common + ["--out", str(repo.out("a"))]), 0)
        self.assertEqual(json.loads(out.getvalue())["status"], "compiled")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(crp.main(common + ["--out", str(repo.out("b")), "--budget", "5"]), 3)
        self.assertTrue((repo.out("b") / crp.RECEIPT_NAME).exists())
        self.assertFalse((repo.out("b") / crp.MANIFEST_NAME).exists())
        spec_path.write_text(json.dumps(base_spec(mandatory=["missing"])), encoding="utf-8")
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(crp.main(common + ["--out", str(repo.out("c"))]), 2)


@unittest.skipUnless(BUILDER.is_file(), "the private handoff builder is not present")
class HandoffBuilderTests(unittest.TestCase):
    def test_manifest_passes_the_builder_normaliser_in_dry_run(self) -> None:
        loader = importlib.util.spec_from_file_location("type_b_handoff_bundle_under_test", BUILDER)
        builder = importlib.util.module_from_spec(loader)
        loader.loader.exec_module(builder)
        repo = Repo(self)
        spec = base_spec(include_triggered_contrasts=True,
                         target={"problem": 7, "anchor": "Demo", "declarations": []})
        out = repo.out()
        crp.write_outputs(repo.compile(spec), out)
        manifest = json.loads((out / crp.MANIFEST_NAME).read_text(encoding="utf-8"))
        for row in builder.top_level_file_specs(manifest):
            self.assertIn("path", builder.normalize_file_spec(row))
        receipt = builder.build_packet(manifest, repo_root=out, output_dir=Path(repo.tmp) / "pkt",
                                       dry_run=True)
        self.assertEqual([b["bundle_id"] for b in receipt["bundles"]], ["ob-1", "contrast-c-demo"])
        self.assertFalse((Path(repo.tmp) / "pkt").exists())


if __name__ == "__main__":
    unittest.main()
