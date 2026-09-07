#!/usr/bin/env python3
"""Verify the exact infinite polynomial-gap countermodel for Erdős 251.

This is a symbolic coefficient checker, not a finite-horizon experiment.  It
verifies the recurrence and adjacent-difference identities in ``Z[n]`` and
emits an exact geometric domination certificate for the terminal tail.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Iterable


problem_id = "erdos_251"


REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT_REL = Path(
    "formal_math/erdos257_period_noncollapse/scripts/"
    "erdos251_polynomial_gap_countermodel.py"
)
LEAN_REL = Path(
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/"
    "PrimeGapDyadicTail.lean"
)
ANALYSIS_REL = Path(
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/"
    "PolynomialGapTailCountermodel.md"
)
PACKET_REL = Path(
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/"
    "research_packet.json"
)
RECEIPT_REL = Path(
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos251_polynomial_gap_countermodel_receipt.json"
)
LEAN_VALIDATION_REL = Path(
    "state/command_runs/runs/"
    "cmdrun_20260822T232202Z_76530_bc0c7e5b6f5b.json"
)


def _trim(poly: list[int]) -> list[int]:
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def _add(left: Iterable[int], right: Iterable[int]) -> list[int]:
    left_rows = list(left)
    right_rows = list(right)
    size = max(len(left_rows), len(right_rows))
    return _trim(
        [
            (left_rows[index] if index < len(left_rows) else 0)
            + (right_rows[index] if index < len(right_rows) else 0)
            for index in range(size)
        ]
    )


def _scale(poly: Iterable[int], scalar: int) -> list[int]:
    return _trim([scalar * coefficient for coefficient in poly])


def _sub(left: Iterable[int], right: Iterable[int]) -> list[int]:
    return _add(left, _scale(right, -1))


def _shift_one(poly: Iterable[int]) -> list[int]:
    """Return coefficients of p(n+1), from low to high degree."""
    rows = list(poly)
    result = [0] * len(rows)
    for degree, coefficient in enumerate(rows):
        choose = 1
        for power in range(degree + 1):
            result[power] += coefficient * choose
            if power < degree:
                choose = choose * (degree - power) // (power + 1)
    return _trim(result)


def _sha256(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_digest(payload: dict[str, object]) -> str:
    encoded = json.dumps(
        payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def build_receipt(repo_root: Path) -> dict[str, object]:
    lean_validation = json.loads((repo_root / LEAN_VALIDATION_REL).read_text())
    expected_target = "ErdosProblems.Erdos251.PrimeGapDyadicTail"
    if not (
        lean_validation.get("status") == "completed"
        and lean_validation.get("exit_code") == 0
        and expected_target in lean_validation.get("argv", [])
    ):
        raise AssertionError("focused Lean validation receipt is not a PASS for the target")

    # Coefficients are stored from constant term upward.
    gap = [4, 8, 2]  # 2(n^2 + 4n + 2)
    tail = [32, 16, 2]  # 2(n + 4)^2
    gap_succ = _shift_one(gap)
    tail_succ = _shift_one(tail)
    recurrence_residual = _sub(tail_succ, _sub(_scale(tail, 2), gap_succ))
    adjacent_difference = _sub(gap_succ, gap)
    adjacent_difference_expected = [10, 4]

    # For a_n = 2(n+4)^2/2^n, the exact ratio bound
    # a_(n+1) / a_n <= 25/32 is equivalent to
    # 25(n+4)^2 - 16(n+5)^2 = n(9n+40) >= 0.
    ratio_domination_residual = _sub(
        _scale([16, 8, 1], 25),
        _scale([25, 10, 1], 16),
    )

    assertions = {
        "tail_recurrence_polynomial_identity": recurrence_residual == [0],
        "adjacent_difference_polynomial_identity": (
            adjacent_difference == adjacent_difference_expected
        ),
        "adjacent_difference_ne_plus_or_minus_two_for_all_naturals": (
            adjacent_difference_expected[0] >= 10
            and adjacent_difference_expected[1] >= 0
        ),
        "tail_orbit_positive_integral_for_all_naturals": (
            all(coefficient >= 0 for coefficient in tail) and tail[0] > 0
        ),
        "terminal_geometric_domination_for_all_naturals": (
            ratio_domination_residual == [0, 40, 9]
        ),
        "geometric_ratio_strictly_below_one": 25 < 32,
        "series_value_is_rational_32": tail[0] == 32,
    }
    if not all(assertions.values()):
        raise AssertionError(assertions)

    payload: dict[str, object] = {
        "schema": "erdos251_polynomial_gap_countermodel_receipt_v1",
        "status": "exact_symbolic_infinite_countermodel_verified",
        "problem_id": "erdos_251",
        "proof_scope": "symbolic_all_indices_not_finite_horizon",
        "links": {
            "checker": str(SCRIPT_REL),
            "lean_source": str(LEAN_REL),
            "analysis": str(ANALYSIS_REL),
            "research_packet": str(PACKET_REL),
            "lean_validation_receipt": str(LEAN_VALIDATION_REL),
            "receipt": str(RECEIPT_REL),
        },
        "source_digests": {
            "checker": _sha256(repo_root / SCRIPT_REL),
            "lean_source": _sha256(repo_root / LEAN_REL),
            "analysis": _sha256(repo_root / ANALYSIS_REL),
            "research_packet": _sha256(repo_root / PACKET_REL),
            "lean_validation_receipt": _sha256(repo_root / LEAN_VALIDATION_REL),
        },
        "lean_validation": {
            "status": "focused_lake_pass",
            "target": expected_target,
            "run_id": lean_validation["run_id"],
            "exit_code": lean_validation["exit_code"],
            "duration_s": lean_validation["duration_s"],
            "finished_at": lean_validation["finished_at"],
            "source_status_sha256": lean_validation["key"]["dirty_relevant_paths"][
                "status_sha256"
            ],
            "source_unstaged_diff_sha256": lean_validation["key"][
                "dirty_relevant_paths"
            ]["unstaged_full_diff_sha256"],
            "authority_scope": "focused module plus final serialized Lake authority check",
        },
        "polynomials_low_to_high": {
            "gap_g_n": gap,
            "tail_T_n": tail,
            "gap_g_n_plus_1": gap_succ,
            "tail_T_n_plus_1": tail_succ,
            "adjacent_difference": adjacent_difference,
        },
        "exact_identities": {
            "tail_recurrence": "T_(n+1) = 2*T_n - g_(n+1)",
            "tail_recurrence_residual_coefficients": recurrence_residual,
            "adjacent_difference": "g_(n+1) - g_n = 4*n + 10",
            "adjacent_difference_residual_coefficients": _sub(
                adjacent_difference, adjacent_difference_expected
            ),
        },
        "infinite_series_certificate": {
            "finite_telescope": (
                "T_0 = sum_(1<=j<=N) g_j/2^j + T_N/2^N"
            ),
            "terminal_sequence": "a_n = T_n/2^n = 2(n+4)^2/2^n",
            "ratio_bound": "a_(n+1)/a_n <= 25/32 < 1",
            "ratio_bound_residual_identity": (
                "25(n+4)^2 - 16(n+5)^2 = n(9n+40)"
            ),
            "ratio_bound_residual_coefficients": ratio_domination_residual,
            "terminal_limit": "T_N/2^N -> 0",
            "series_value": 32,
        },
        "mechanism_consequence": {
            "eliminated": (
                "positivity + parity + polynomial growth + unboundedness + "
                "nonperiodicity + dyadic recurrence force the h=1 adjacent-small-mismatch producer"
            ),
            "surviving_requirement": (
                "finer consecutive-prime arithmetic or an external fractional-tail theorem"
            ),
            "does_not_prove": "irrationality or rationality of the actual prime-gap series",
        },
        "assertions": assertions,
        "authority_boundary": (
            "The checker proves polynomial identities and geometric domination by exact integer "
            "coefficient arithmetic. The linked completed command-run receipt records a focused "
            "Lean/Lake PASS for the source module; no full-project integration claim is made."
        ),
    }
    payload["canonical_payload_sha256"] = _canonical_digest(payload)
    return payload


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=REPO_ROOT / RECEIPT_REL)
    args = parser.parse_args()
    if args.write and args.check:
        parser.error("choose at most one of --write and --check")

    receipt = build_receipt(REPO_ROOT)
    rendered = json.dumps(receipt, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text(encoding="utf-8") != rendered:
            print(json.dumps({"ok": False, "status": "receipt_drift"}))
            return 1
        print(
            json.dumps(
                {
                    "ok": True,
                    "status": receipt["status"],
                    "receipt": str(args.output.relative_to(REPO_ROOT)),
                    "canonical_payload_sha256": receipt["canonical_payload_sha256"],
                },
                sort_keys=True,
            )
        )
        return 0
    if args.write:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
