#!/usr/bin/env python3
"""Exact replay and lineage checks for the #1041 successor nonet revision 4."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[5]
PACKET_DIR = ROOT / "docs/formal_math/type_b_packets/erdos1041_frontier_coevolution_nonet_r4_2026_08_26"
OUT_ROOT = Path("public-source-redacted://erdos1041_frontier_coevolution_nonet_r4_20260826")
PREDECESSOR_DIR = ROOT / "docs/formal_math/type_b_packets/erdos1041_frontier_coevolution_nonet_r3_2026_08_26"
RETURN_INTAKE = ROOT / "state/formal_math/type_b_return_batches/erdos1041_20260826_return_stream_01/intake.json"
PREDECESSOR_PORTFOLIO_SHA256 = "60a65b85e4d78d1180d37d45b8f4761a19b20af01464ed8396f101d15e7d91aa"
PREDECESSOR_VALIDATION_SHA256 = "b307903bc6363660c258726c0810734247ba9d51c9af00ebaf29b385e84cd42c"
RETURN_INTAKE_SHA256 = "7c10bb581cdc820121501273cb2e212b90f264daac494efef396602f78c792f0"
MERGE_DISCRIMINANT_CHECKER = ROOT / (
    "research_corpus/Erdos1041/scripts/"
    "check_erdos1041_merge_tree_discriminant_dichotomy.py"
)
FIRST_TWO_CHECKER = ROOT / (
    "research_corpus/Erdos1041/scripts/"
    "check_erdos1041_first_two_critical_optimized_bergman.py"
)
JOINT_CHECKER = ROOT / (
    "research_corpus/Erdos1041/scripts/"
    "check_erdos1041_six_return_joint_assimilation.py"
)
CHARGED_ALLOCATION_CHECKER = ROOT / (
    "research_corpus/Erdos1041/scripts/"
    "check_erdos1041_charged_lifetime_allocation_no_go.py"
)
LEAF_ENTRANCE_CHECKER = ROOT / (
    "research_corpus/Erdos1041/scripts/"
    "check_erdos1041_leaf_entrance_product_identity.py"
)
ROOT_ANCESTRY_CHECKER = ROOT / (
    "research_corpus/Erdos1041/scripts/"
    "check_erdos1041_root_indexed_entrance_ancestry.py"
)
SEVENTH_SEXTIC_CHECKER = ROOT / (
    "research_corpus/Erdos1041/scripts/"
    "check_erdos1041_seventh_return_sextic_assimilation.py"
)


@dataclass(frozen=True)
class GQ:
    re: Fraction
    im: Fraction = Fraction(0)

    def __add__(self, other: "GQ") -> "GQ":
        return GQ(self.re + other.re, self.im + other.im)

    def __sub__(self, other: "GQ") -> "GQ":
        return GQ(self.re - other.re, self.im - other.im)

    def __mul__(self, other: "GQ") -> "GQ":
        return GQ(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    def conj(self) -> "GQ":
        return GQ(self.re, -self.im)

    def scale(self, q: Fraction) -> "GQ":
        return GQ(q * self.re, q * self.im)

    def norm_sq(self) -> Fraction:
        return self.re * self.re + self.im * self.im


ZERO = GQ(Fraction(0))
ONE = GQ(Fraction(1))


def poly_mul(p: list[GQ], q: list[GQ]) -> list[GQ]:
    out = [ZERO for _ in range(len(p) + len(q) - 1)]
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] = out[i + j] + a * b
    while len(out) > 1 and out[-1] == ZERO:
        out.pop()
    return out


def poly_eval(p: list[GQ], t: Fraction) -> GQ:
    acc = ZERO
    for coefficient in reversed(p):
        acc = acc.scale(t) + coefficient
    return acc


def ray_polynomial(roots: list[GQ], i: int) -> list[GQ]:
    out = [ONE]
    for root in roots:
        out = poly_mul(out, [GQ(-root.re, -root.im), roots[i]])
    return out


def modulus_square_polynomial(p: list[GQ]) -> list[GQ]:
    out = poly_mul(p, [z.conj() for z in p])
    out[0] = out[0] - ONE
    assert all(z.im == 0 for z in out)
    return out


def check_radial_switching() -> dict[str, object]:
    fixtures = [
        [
            GQ(Fraction(1, 2)),
            GQ(Fraction(-1, 3), Fraction(1, 4)),
            GQ(Fraction(1, 5), Fraction(-2, 5)),
            GQ(Fraction(-2, 7), Fraction(-1, 6)),
        ],
        [
            GQ(Fraction(3, 5), Fraction(1, 10)),
            GQ(Fraction(-2, 5), Fraction(1, 3)),
            GQ(Fraction(-1, 4), Fraction(-1, 2)),
            GQ(Fraction(1, 6), Fraction(3, 7)),
            GQ(Fraction(1, 8), Fraction(-1, 9)),
        ],
    ]
    sample_t = [Fraction(0), Fraction(1, 10), Fraction(1, 3), Fraction(2, 3), Fraction(9, 10)]
    checked_pair_identities = 0
    checked_radii = 0
    max_degree = 0

    for roots in fixtures:
        assert all(root.norm_sq() < 1 for root in roots)
        n = len(roots)
        ray_polys = [ray_polynomial(roots, i) for i in range(n)]
        for p in ray_polys:
            modulus_poly = modulus_square_polynomial(p)
            degree = len(modulus_poly) - 1
            max_degree = max(max_degree, degree)
            assert degree <= 2 * n

        for t in sample_t:
            direct_product_sq = Fraction(1)
            reciprocal_product_sq = Fraction(1)
            safe_count = 0
            for i, ai in enumerate(roots):
                value_sq = poly_eval(ray_polys[i], t).norm_sq()
                direct_product_sq *= value_sq
                safe_count += int(value_sq <= 1)
                for aj in roots:
                    lhs = (ONE - (ai * aj.conj()).scale(t)).norm_sq()
                    rhs = (ai.scale(t) - aj).norm_sq()
                    expected = (1 - aj.norm_sq()) * (1 - t * t * ai.norm_sq())
                    assert lhs - rhs == expected
                    reciprocal_product_sq *= lhs
                    checked_pair_identities += 1
            assert direct_product_sq <= reciprocal_product_sq
            assert reciprocal_product_sq <= 1
            assert safe_count >= 1
            checked_radii += 1

    return {
        "fixture_count": len(fixtures),
        "checked_pair_identities": checked_pair_identities,
        "checked_radii": checked_radii,
        "max_ray_safe_polynomial_degree": max_degree,
    }


def polynomial_value_sq(z: GQ, roots: list[GQ]) -> Fraction:
    value = ONE
    for root in roots:
        value = value * (z - root)
    return value.norm_sq()


def check_safe_endpoint_chord_nogo() -> dict[str, object]:
    r = Fraction(99, 100)
    roots = [
        GQ(Fraction(3, 5), Fraction(4, 5)).scale(r),
        GQ(Fraction(3, 5), Fraction(-4, 5)).scale(r),
        GQ(Fraction(-4, 5), Fraction(3, 5)).scale(r),
    ]
    assert all(root.norm_sq() == r * r < 1 for root in roots)
    x = roots[1].scale(Fraction(1, 2))
    y = roots[2].scale(Fraction(1, 2))
    midpoint = (x + y).scale(Fraction(1, 2))
    x_sq = polynomial_value_sq(x, roots)
    y_sq = polynomial_value_sq(y, roots)
    midpoint_sq = polynomial_value_sq(midpoint, roots)
    assert x_sq == Fraction(31834268291696013, 40000000000000000)
    assert y_sq == Fraction(208067113017621, 320000000000000)
    assert midpoint_sq == Fraction(8367179814045680661, 8000000000000000000)
    assert x_sq < 1 and y_sq < 1 < midpoint_sq
    return {
        "root_modulus": "99/100",
        "ray_parameter": "1/2",
        "endpoint_squares": [str(x_sq), str(y_sq)],
        "midpoint_square": str(midpoint_sq),
        "conclusion": "two_strictly_safe_common_radius_endpoints_do_not_force_safe_chord",
    }


def check_fibre_capacity_improvement() -> dict[str, object]:
    checked = 0
    strict = 0
    for n in range(2, 121):
        for k in range(1, n):
            new = Fraction(k, 2 * n - k)
            old = Fraction(n - 1, n + 1) ** (n - k)
            assert 0 < new <= old < 1
            assert (new == old) == (n - k == 1)
            checked += 1
            strict += int(new < old)
    return {
        "checked_component_constants": checked,
        "strict_multi_exterior_improvements": strict,
    }


def check_merge_discriminant_dichotomy() -> dict[str, object]:
    run = subprocess.run(
        [str(ROOT / "repo-python"), str(MERGE_DISCRIMINANT_CHECKER)],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    receipt = json.loads(run.stdout)
    assert receipt["passed"] is True
    assert receipt["exact_ordered_binary_trees"]["ordered_tree_count"] == 2055
    return {
        "exact_ordered_binary_trees": 2055,
        "terminal_threshold_max_error": receipt["terminal_threshold_max_error"],
        "actual_merge_tree_row_count": len(receipt["actual_merge_tree_rows"]),
    }


def check_successor_frontier() -> dict[str, object]:
    receipts: dict[str, object] = {}
    for label, checker in {
        "optimized_first_two_critical": FIRST_TWO_CHECKER,
        "six_return_joint_assimilation": JOINT_CHECKER,
        "charged_lifetime_allocation_no_go": CHARGED_ALLOCATION_CHECKER,
        "leaf_entrance_product_identity": LEAF_ENTRANCE_CHECKER,
        "root_indexed_entrance_ancestry": ROOT_ANCESTRY_CHECKER,
        "seventh_return_sextic_assimilation": SEVENTH_SEXTIC_CHECKER,
    }.items():
        run = subprocess.run(
            [str(ROOT / "repo-python"), str(checker)],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
        try:
            receipt = json.loads(run.stdout)
        except json.JSONDecodeError:
            receipt = {"stdout": run.stdout.strip()}
        receipts[label] = receipt
    return receipts


def check_lineage() -> dict[str, object]:
    rows = {
        "predecessor_portfolio": (
            PREDECESSOR_DIR / "portfolio_receipt.json",
            PREDECESSOR_PORTFOLIO_SHA256,
        ),
        "predecessor_validation": (
            PREDECESSOR_DIR / "validation_receipt.json",
            PREDECESSOR_VALIDATION_SHA256,
        ),
        "assimilated_return_intake": (RETURN_INTAKE, RETURN_INTAKE_SHA256),
    }
    checked: dict[str, str] = {}
    for label, (path, expected) in rows.items():
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        assert actual == expected, (label, actual, expected)
        checked[label] = actual
    return {
        "lifecycle": "refine_validated_unsent_predecessor",
        "predecessor_dispatch_state": "unsent",
        "sha256": checked,
    }


def check_manifests(require_built: bool) -> dict[str, object]:
    manifests = sorted(PACKET_DIR.glob("manifest_*.json"))
    assert len(manifests) == 9, [path.name for path in manifests]
    predecessor_hashes = json.loads(
        (PREDECESSOR_DIR / "portfolio_receipt.json").read_text(encoding="utf-8")
    )["manifest_sha256"]
    packet_ids: set[str] = set()
    central_objects: set[str] = set()
    for path in manifests:
        data = json.loads(path.read_text(encoding="utf-8"))
        assert data["schema"] == "type_b_handoff_manifest_v1"
        assert data["handoff_profile"] == "research_bundle"
        assert data["proof_campaign"]["enabled"] is True
        packet_id = data["packet_id"]
        assert packet_id not in packet_ids
        packet_ids.add(packet_id)
        central = data["design_notes"]["attack_card"]["central_object"]
        central_objects.add(central)
        assert data["top_level"]["files"] == []
        dossiers = data["bundles"]
        assert len(dossiers) == 17
        assert len({row["bundle_id"] for row in dossiers}) == len(dossiers)
        embedded_paths = [
            source["path"] for dossier in dossiers for source in dossier["files"]
        ]
        assert len(embedded_paths) == len(set(embedded_paths))
        assert all((ROOT / source_path).is_file() for source_path in embedded_paths)
        if packet_id in {"02_forest_metric_consumer", "09_sparse_defect_pair_allocation"}:
            assert any(path.endswith("LeafEntranceProductIdentity.md") for path in embedded_paths)
        if packet_id in {
            "01_unrestricted_fanin",
            "02_forest_metric_consumer",
            "03_forest_combined_charge",
            "09_sparse_defect_pair_allocation",
        }:
            assert any(path.endswith("RootIndexedEntranceAncestry.md") for path in embedded_paths)
            ask_text = data["ask_type_b"]["decision_or_question"]
            assert "subtree" in ask_text.lower()
            assert "cut" in ask_text.lower()
        if packet_id == "07_tied_face_complement_cover":
            assert any(path.endswith("SeventhReturnSexticAssimilation20260826.md") for path in embedded_paths)
            ask_text = data["ask_type_b"]["decision_or_question"]
            assert "4sqrt(3)" in ask_text
            assert "low/paired splice" in ask_text
        assert all(dossier["slot_class"] == "proof_source" for dossier in dossiers)
        assert all(dossier["query_terms"] for dossier in dossiers)
        assert all(len(dossier["relations"]) == len(dossier["files"]) for dossier in dossiers)
        assert data["packing_policy"]["compiled_dossier_mode"] is True
        assert data["packing_policy"]["relation_aware_bin_packing"] is True
        assert data["packing_policy"]["terminal_native_dossier_mode"] is True
        assert data["return_contract"]["max_downloadable_artifacts"] == 0
        lineage = data["design_notes"]["lineage"]
        assert lineage["lifecycle"] == "refine_validated_unsent_predecessor"
        assert lineage["predecessor_dispatch_state"] == "unsent"
        assert lineage["predecessor_portfolio_sha256"] == PREDECESSOR_PORTFOLIO_SHA256
        assert lineage["predecessor_validation_sha256"] == PREDECESSOR_VALIDATION_SHA256
        assert lineage["assimilated_return_intake_sha256"] == RETURN_INTAKE_SHA256
        assert lineage["predecessor_manifest_sha256"] == predecessor_hashes[packet_id]
        ask = data["ask_type_b"]
        assert "FULL SOLUTION" in " ".join(ask["depth_floor"])
        assert "Claim exactly what you prove" in ask["claim_scope"]
        if require_built:
            out_dir = Path(data["output_dir"])
            built_files = [p for p in out_dir.iterdir() if p.is_file()]
            assert (out_dir / "00_ASK_TYPE_B.md").is_file()
            assert len(built_files) == data["max_output_file_count"]
            proof_files = [path for path in built_files if path.name.endswith("_PROOF_DOSSIER.dossier.zip")]
            assert len(proof_files) == 17
            assert min(path.stat().st_size for path in proof_files) >= 80_000
    assert len(central_objects) >= 8
    return {
        "packet_count": len(manifests),
        "central_object_count": len(central_objects),
        "built_required": require_built,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-built", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    result = {
        "schema": "erdos1041_frontier_coevolution_nonet_r4_check_v1",
        "status": "pass",
        "lineage": check_lineage(),
        "successor_frontier": check_successor_frontier(),
        "radial_switching": check_radial_switching(),
        "safe_endpoint_chord_nogo": check_safe_endpoint_chord_nogo(),
        "fibre_capacity_improvement": check_fibre_capacity_improvement(),
        "merge_tree_discriminant_dichotomy": check_merge_discriminant_dichotomy(),
        "portfolio": check_manifests(args.require_built),
    }
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print("PASS: exact radial factor identities and degree bounds")
        print("PASS: exact open-disk safe-endpoints/unsafe-chord no-go")
        print("PASS: exterior-fibre capacity constant improves the independent-factor gap")
        print("PASS: exact merge-tree discriminant dichotomy replay")
        print("PASS: nine governed successor packet manifests and source combinations")
        if args.require_built:
            print("PASS: nine flat built packet folders at declared file ceilings")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
