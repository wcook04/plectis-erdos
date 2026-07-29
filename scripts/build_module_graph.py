#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Refresh the exact Lean import graph embedded in ``docs/claims.json``.

Roles are authored navigation metadata and are therefore preserved when a
module already has one.  Paths and import edges are derived mechanically from
the public Lean source; this script does not alter claims or argument edges.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIMS = ROOT / "docs" / "claims.json"
LIBRARY_ROOTS = ("Erdos249257", "ErdosProblems")
ROOT_FILES = tuple(f"{root}.lean" for root in LIBRARY_ROOTS)
IMPORT_RE = re.compile(
    rf"^import ((?:{'|'.join(LIBRARY_ROOTS)})(?:\.[A-Za-z0-9_]+)+)\s*$",
    re.M,
)

NEW_ROLES = {
    "Erdos249257.ActualForeignResidueProjection": "Finite foreign-residue projection consumer",
    "Erdos249257.SquareCRTCube": "Finite square-CRT correction-suppression mechanism",
    "Erdos249257.SignedQMomentObstruction": "Finite signed-moment determinant and dyadic-parity substrate",
    "Erdos249257.TotientMahlerDefect": "Finite dyadic-totient rank and certificate interface",
    "Erdos249257.ResidualGaugeObstruction": "Residual-gauge obstruction for monomial minor criteria",
    "Erdos249257.BinaryTailWindowTransfer": "Binary tail-window transfer interfaces",
    "Erdos249257.CyclicTensorMobiusShadow": "Cyclic tensor identities for the Mobius shadow",
    "Erdos249257.CompositeDilationDefect": "Composite support-dilation defect identity",
    "Erdos249257.CyclotomicProjectionOfShadow": "Cyclotomic projections of the Mobius shadow",
    "Erdos249257.DiagonalFreshLossBridge": "Fresh-loss projection and suffix-supply reduction",
    "Erdos249257.DiagonalPincerCertificates": "Finite diagonal-pincer certificate base",
    "Erdos249257.DiagonalPincerDecomposition": "Exact diagonal-pincer target decomposition",
    "Erdos249257.DyadicPrefixCompression": "Dyadic prefix compression identities",
    "Erdos249257.FullTargetPrimeAdjunctionNoGo": "Prime-adjunction obstruction for the full target",
    "Erdos249257.HalfCarryReachability": "Half-carry reachability and compactness",
    "Erdos249257.HalfCarryCeilParentContraction": "Fixed-coefficient rewind contraction",
    "Erdos249257.CampbellShiftSynchronization": "Campbell shift synchronization for the half target",
    "Erdos249257.HalfCarrySelectedWindow": "Selected protected half-carry windows",
    "Erdos249257.HalfCutLocator": "Fatal-gap locator for the half target",
    "Erdos249257.HalfCarryRewindPhase": "Realized fixed-coefficient rewind phase",
    "Erdos249257.HalfCarryProtectedSeamConsumer": "Localized protected one-hole seam consumer",
    "Erdos249257.HalfCarryCofinalWindowOrSeamConsumer": "Mixed cofinal half-carry fan-in",
    "Erdos249257.HalfCylinderIntegerGreedy": "Integer-greedy first-wrap seam reduction",
    "Erdos249257.HalfCylinderConcreteSeamAdapter": "Concrete finite seam adapter",
    "Erdos249257.HalfCylinderFiniteShadow": "Finite shadows of the half cylinder",
    "Erdos249257.HalfCylinderFullShellSeamBridge": "Full-shell seam bridge for the half target",
    "Erdos249257.HalfCylinderFloorErrorReset": "Floor-error reset for the half seam",
    "Erdos249257.HalfCylinderSkippedEndpointClassifier": "Skipped-endpoint classifier for the half seam",
    "Erdos249257.HalfCylinderSeamLimit": "Seam-limit reduction for the half target",
    "Erdos249257.HalfCylinderSkippedRankLimit": "Skipped-rank limit for the half seam",
    "Erdos249257.HalfCylinderFalseBitSupply": "False-bit supply for the half seam",
    "Erdos249257.HalfCylinderFatalGapRightTail": "Fatal-gap and eventual-right seam classification for the half target",
    "Erdos249257.HalfCylinderFinalMiddleTailSocket": "Analytic tail socket for the final middle seam cells",
    "Erdos249257.HalfCylinderHalfMembershipClassification": "Positive half-membership classification in seam coordinates",
    "Erdos249257.HalfCylinderLargestSkipGap": "Largest skipped-rank gap and successor propagation for the half seam",
    "Erdos249257.HalfCylinderBoundaryPulse": "Boundary-pulse normalization at the largest-skip crossing",
    "Erdos249257.HalfCylinderLargestSkipInduction": "Largest-skip induction from a first-crossing producer socket",
    "Erdos249257.HalfCylinderFixedTailSocket": "Fixed-tail survival classification for half-cylinder skips",
    "Erdos249257.HalfCylinderProducerCarrySocket": "Producer-carry and future-tail comparison socket",
    "Erdos249257.HalfCylinderQuarterBandEndpoints": "Quarter-band endpoint cells for adjacent half-cylinder cuts",
    "Erdos249257.HalfCylinderResetDeficitEscape": "Reset-deficit escape geometry for the largest-skip crossing",
    "Erdos249257.HalfCylinderSeamProducerAlignment": "Seam-to-producer carry alignment identity",
    "Erdos249257.HalfFinalMiddlePhaseSieve": "Rank-21 final-middle phase sieve for the half seam",
    "Erdos249257.HalfCarrySelectedWindowBase": "Computed depth-18 selected half-carry window base",
    "Erdos249257.RewindSeamOperationalBridge": "Operational bridge from rewind seams to protected next-row seams",
    "Erdos249257.SelectedSuffixCylinder": "Terminally indexed selected suffix-cylinder propagation",
    "Erdos249257.SelectedSuffixCylinderPreFeedback": "Selected suffix-cylinder run through the first feedback row",
    "Erdos249257.HalfDivisorUnitDrop": "Half-divisor unit coefficient drop at the feedback row",
    "Erdos249257.HalfTrappingReturnCarry": "Half-trapping reverse-carry interface",
    "Erdos249257.LambertDiagonalEnclosure": "Lambert diagonal enclosure reduction",
    "Erdos249257.LcmFactorIdealPulseObstruction": "LCM factor-ideal anchor-pulse obstruction",
    "Erdos249257.MersenneShadowCyclotomicNoncollapse": "Cyclotomic noncollapse in the Mersenne shadow",
    "Erdos249257.MaximalOmegaLayer": "Mixed prime-power support-layer identities",
    "Erdos249257.MersenneShadowDenominatorGrowth": "Exact denominator growth in the Mersenne shadow",
    "Erdos249257.PrimePowerJumpDynamics": "Prime-power jump dynamics",
    "Erdos249257.PrimitiveRationalGapSupply": "Conditional primitive rational-gap supply interface",
    "Erdos249257.PrimitiveSupportBridge": "Conditional primitive-support bridge",
    "Erdos249257.RadicalMobiusShadow": "Radical structure of the Mobius shadow",
    "Erdos249257.RationalDenominatorSurvival": "Rational denominator-survival identities",
    "Erdos249257.RepunitMobiusNumerator": "Repunit and Mobius-numerator identities",
    "Erdos249257.SquaredMersenneDiagonalEnclosure": "Sharp squared-Mersenne diagonal enclosure",
    "Erdos249257.SternBrocotRunGeometry": "Stern-Brocot run geometry",
    "Erdos249257.SupportDilationDifferences": "Finite support-dilation difference identities",
    "Erdos249257.SupportSunflowerDichotomy": "Conditional orthogonal-petal support reduction",
}


def module_id(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def default_role(module: str) -> str:
    if ".DiagonalPincerPrimeCertificates." in module:
        return "Finite diagonal prime-certificate shard"
    if module.startswith("Erdos249257.DiagonalPincerCertificatesT"):
        return "Finite diagonal-pincer certificate extension"
    if ".GeneratedCertificates." in module:
        return "Generated finite certificate shard"
    return NEW_ROLES.get(module, "Lean proof module")


def build_graph(data: dict[str, object]) -> dict[str, object]:
    machine = data["machine_readable_paper"]
    current = machine["module_graph"]
    roles = {row["id"]: row["role"] for row in current["nodes"]}
    nodes = []
    source_paths = [
        path
        for library_root in LIBRARY_ROOTS
        for path in sorted((ROOT / library_root).rglob("*.lean"))
    ]
    for path in source_paths:
        module = module_id(path)
        nodes.append(
            {
                "id": module,
                "path": path.relative_to(ROOT).as_posix(),
                "role": roles.get(module, default_role(module)),
                "imports": IMPORT_RE.findall(path.read_text(encoding="utf-8")),
            }
        )
    return {
        "root": ROOT_FILES[0],
        "additional_roots": list(ROOT_FILES[1:]),
        "nodes": nodes,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = json.loads(CLAIMS.read_text(encoding="utf-8"))
    expected = build_graph(data)
    actual = data["machine_readable_paper"]["module_graph"]
    if args.check:
        if actual != expected:
            print("module graph is stale; run python3 scripts/build_module_graph.py")
            return 1
        print(f"module graph current: {len(expected['nodes'])} modules")
        return 0
    data["machine_readable_paper"]["module_graph"] = expected
    CLAIMS.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"wrote docs/claims.json module graph: {len(expected['nodes'])} modules")
    return 0


if __name__ == "__main__":
    sys.exit(main())
