#!/usr/bin/env python3
"""Joint prime-pole/gap census for the surviving Erdős #68 prime route.

For a prime ``p`` put

    Delta_p = ceil((p-1)! P_(p-1)) - (p-1)! P_(p-1) = u/(p^e w),
    h = p^(e-1) w,  t = u-h.

When the principal pole residue ``C_p`` is nonzero, the checked transport law
prescribes one residue class for ``t`` modulo ``p``.  A lower-cylinder hit can
only occur in

    epsilon_p h < t <= (epsilon_p + R_p) h,

where ``epsilon_p=1/(p!-1)`` and
``R_p=p! * sum_(n>p) 1/(n!-1)``.  This probe tests whether the residue class is
actually selective at that Archimedean scale.  It uses the rigorous bounds

    p!/((p+1)!-1) < R_p < 2/p.

Thus ``h*p!/((p+1)!-1) >= p`` is already a falsifier: the known subinterval
has length greater than one full residue spacing, so every class modulo ``p``
occurs in the dangerous interval.  The computation stops at a stated finite
prime horizon and does not promote finite escape to irrationality.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from formal_math.probes.erdos68_prime_pole_scan import (  # noqa: E402
    endpoint_prime_pole,
    primes_through,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)


SOURCE_REF = "formal_math/probes/erdos68_prime_pole_gap_joint_census.py"
SCANNER_REF = "formal_math/probes/erdos68_prime_pole_scan.py"
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "PrimePoleCriterion.lean"
)
LAB_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "PrimePoleCriterionLab.md"
)
TAIL_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/"
    "PrimeZeroBranch.lean"
)
DEFAULT_OUTPUT = REPO_ROOT / (
    "state/formal_math/probes/"
    "erdos68_prime_pole_gap_joint_census_receipt.json"
)


def ceil_fraction(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def valuation(value: int, p: int) -> tuple[int, int]:
    exponent = 0
    cofactor = value
    while cofactor % p == 0:
        exponent += 1
        cofactor //= p
    return exponent, cofactor


def decimal_digits_from_bits(bits: int) -> int:
    if bits <= 1:
        return 1
    return int((bits - 1) * math.log10(2)) + 1


def count_scale_record(value: int) -> dict[str, int | bool]:
    """Record the exact positivity and size of a huge count without serialising it."""
    bits = value.bit_length() if value > 0 else 0
    return {
        "positive": value > 0,
        "bit_length": bits,
        "decimal_digits": decimal_digits_from_bits(bits) if bits else 1,
    }


def lower_interval_candidate_count(
    *, p: int, residue: int, left: Fraction, right: Fraction
) -> int:
    """Count integers congruent to residue mod p in the interval (left,right]."""
    k_min = ((left - residue) // p) + 1
    k_max = (right - residue) // p
    return max(0, k_max - k_min + 1)


def classify_offset(offset: Fraction, epsilon: Fraction, p: int) -> str:
    """Classify using only exact bounds epsilon < offset <= epsilon + R_p."""
    if offset <= epsilon:
        return "certified_below_lower_cylinder"
    if offset >= epsilon + Fraction(2, p):
        return "certified_above_lower_cylinder_using_Rp_lt_2_over_p"
    return "unresolved_inside_rigorous_tail_envelope"


def census(max_prime: int) -> dict[str, Any]:
    if max_prime < 7:
        raise ValueError("max_prime must be at least 7")

    prime_set = set(primes_through(max_prime))
    delta = Fraction(1)  # Delta_3 in the lab's endpoint notation is A_2=1.
    pred_factorial = 2  # (p-1)! at p=3.
    rows: list[dict[str, Any]] = []

    for p in range(3, max_prime + 1):
        if p in prime_set and p >= 5:
            pole = endpoint_prime_pole(p)
            reduced_e, w = valuation(delta.denominator, p)
            principal = pole["principal_residue_mod_q"]
            pole_e = pole["maximum_exponent"]
            epsilon = Fraction(1, p * pred_factorial - 1)
            offset = p * delta - 1
            row: dict[str, Any] = {
                "p": p,
                "literal_pole_exponent": pole_e,
                "reduced_gap_pole_exponent": reduced_e,
                "principal_residue_mod_p": principal,
                "maximal_hits": pole["maximal_hits"],
                "pole_survives": principal != 0,
                "offset_location": classify_offset(offset, epsilon, p),
                "offset_positive": offset > 0,
            }

            if principal == 0:
                if reduced_e >= pole_e:
                    raise AssertionError(
                        f"p={p}: cancelled principal pole did not lose p-adic order"
                    )
                row["transport_status"] = "principal_pole_cancelled"
            else:
                if reduced_e != pole_e or reduced_e <= 0:
                    raise AssertionError(
                        f"p={p}: pole survival exponent mismatch "
                        f"literal={pole_e}, reduced={reduced_e}"
                    )
                u = delta.numerator
                h = p ** (reduced_e - 1) * w
                t = u - h
                transported = (u * pow(w, -1, p)) % p
                if transported != principal:
                    raise AssertionError(
                        f"p={p}: gap transport {transported} != C_p {principal}"
                    )
                target_scaled = principal - 1 if reduced_e == 1 else principal
                target_t_residue = (target_scaled * w) % p
                actual_t_residue = t % p
                if actual_t_residue != target_t_residue:
                    raise AssertionError(
                        f"p={p}: t residue {actual_t_residue} != prescribed "
                        f"{target_t_residue}"
                    )

                p_factorial = p * pred_factorial
                tail_lower = Fraction(p_factorial, (p + 1) * p_factorial - 1)
                known_left = epsilon * h
                known_right = (epsilon + tail_lower) * h
                candidate_count = lower_interval_candidate_count(
                    p=p,
                    residue=target_t_residue,
                    left=known_left,
                    right=known_right,
                )
                full_lattice_saturation = tail_lower * h >= p

                row.update(
                    {
                        "transport_status": "verified",
                        "prescribed_t_residue_mod_p": target_t_residue,
                        "least_positive_t_residue": (
                            target_t_residue if target_t_residue else p
                        ),
                        "actual_t_matches_prescribed_residue": True,
                        "h_bit_length": h.bit_length(),
                        "h_decimal_digits": decimal_digits_from_bits(h.bit_length()),
                        "known_tail_subinterval_length_at_least_one_spacing": (
                            full_lattice_saturation
                        ),
                        "prescribed_class_candidates_in_known_subinterval_scale": (
                            count_scale_record(candidate_count)
                        ),
                    }
                )
            rows.append(row)

        if p < max_prime:
            pred_factorial *= p
            y = p * delta - Fraction(1, pred_factorial - 1)
            carry = ceil_fraction(y) - 1
            delta = y - carry
            if not 0 < delta <= 1:
                raise AssertionError(f"gap left (0,1] after p={p}: {delta}")

    surviving = [row for row in rows if row["pole_survives"]]
    saturated = [
        row
        for row in surviving
        if row["known_tail_subinterval_length_at_least_one_spacing"]
    ]
    escapes = [
        row for row in rows if row["offset_location"].startswith("certified_")
    ]
    unresolved = [
        row
        for row in rows
        if row["offset_location"] == "unresolved_inside_rigorous_tail_envelope"
    ]
    first_saturated = saturated[0]["p"] if saturated else None

    falsifiers = {
        "p=7 is already residue-lattice saturated": first_saturated == 7,
        "p=139 principal pole cancellation reproduced": any(
            row["p"] == 139
            and row["transport_status"] == "principal_pole_cancelled"
            for row in rows
        ),
        "all surviving poles from p=7 are saturated through horizon": all(
            row["p"] < 7
            or row["known_tail_subinterval_length_at_least_one_spacing"]
            for row in surviving
        ),
        "every reported transport congruence checks": all(
            row["transport_status"] != "verified"
            or row["actual_t_matches_prescribed_residue"]
            for row in rows
        ),
    }
    return {
        "range": {"minimum_prime": 5, "maximum_prime": max_prime},
        "prime_count": len(rows),
        "surviving_principal_pole_count": len(surviving),
        "cancelled_principal_poles": [
            row["p"] for row in rows if not row["pole_survives"]
        ],
        "first_full_residue_lattice_saturation_prime": first_saturated,
        "saturated_surviving_pole_count": len(saturated),
        "certified_lower_cylinder_escape_count": len(escapes),
        "unresolved_tail_envelope_primes": [row["p"] for row in unresolved],
        "rows": rows,
        "falsifiers": falsifiers,
        "all_falsifiers_pass": all(falsifiers.values()),
        "pivot_decision": (
            "Principal-residue nonvanishing is nonselective at the lower-cylinder "
            "scale from p=7 throughout the exact horizon: the rigorous first-tail "
            "subinterval already contains the prescribed class. Any viable prime "
            "route must control the quotient (t-r)/p or another Archimedean "
            "localizer, not merely C_p modulo p. Do not extend this residue-only "
            "scan as an endpoint attack."
        ),
        "claim_boundary": (
            "Exact finite rational and modular computation plus rigorous tail "
            "bounds. It falsifies residue-only selectivity on the checked horizon; "
            "it proves neither eventual saturation nor cofinal prime escape nor "
            "irrationality."
        ),
    }


def build_receipt(max_prime: int) -> dict[str, Any]:
    result = census(max_prime)
    contract = build_experiment_contract(
        problem_id="erdos_68",
        target_statement="Prove irrationality of sum_(n>=2) 1/(n!-1).",
        claim_ceiling=(
            "Finite exact elimination of principal-residue nonvanishing as a "
            "standalone lower-cylinder exclusion mechanism; no cofinal theorem."
        ),
        hypothesis_id="prime_pole_residue_alone_selects_against_lower_cylinder",
        hypothesis_statement=(
            "For surviving endpoint prime poles, the prescribed class of t modulo "
            "p is sparse enough in the dangerous Archimedean interval to force "
            "lower-cylinder misses."
        ),
        probe_id="joint_prime_pole_gap_lattice_saturation",
        probe_question=(
            "Does the rigorous lower tail width R_p h remain below one residue "
            "spacing p, and does the transported actual t satisfy its predicted class?"
        ),
        computation=(
            "Iterate the exact predecessor-gap Fraction recurrence; at each prime "
            "factor the reduced denominator, reproduce C_p, verify the transported "
            "t congruence, and count its class in the subinterval supplied by the "
            "first omitted tail term."
        ),
        falsifier=(
            "At one surviving pole, the rigorous subinterval length is at least p, "
            "so every residue class occurs before any unknown tail contribution."
        ),
        stop_condition=(
            "Stop after reproducing the first saturation witness and a bounded joint "
            "census; pivot if all later surviving poles remain saturated."
        ),
        survival_consequence=(
            "A genuinely sub-spacing interval would leave open a residue-exclusion theorem."
        ),
        falsification_consequence=(
            "Residue nonvanishing must be coupled to a bound on the lift quotient "
            "(t-r)/p or a different Archimedean localization mechanism."
        ),
        consumer_ref=LEAN_REF,
        analysis_refs=[LAB_REF, TAIL_REF, SCANNER_REF],
        source_refs=[SOURCE_REF, SCANNER_REF, LEAN_REF, LAB_REF, TAIL_REF],
        result_status="finite_counterexample",
        result_summary=result["pivot_decision"],
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos68-prime-pole-gap-joint-census/1",
        "status": "verified_residue_only_lower_cylinder_route_nonselective",
        "experiment_contract": contract,
        "census": result,
        "source_records": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, SCANNER_REF),
            source_record(REPO_ROOT, LEAN_REF),
            source_record(REPO_ROOT, LAB_REF),
            source_record(REPO_ROOT, TAIL_REF),
        ],
    }


def emit(payload: dict[str, Any], output: Path, check: bool) -> int:
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-prime", type=int, default=211)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    payload = build_receipt(args.max_prime)
    if not payload["census"]["all_falsifiers_pass"]:
        print(json.dumps(payload["census"]["falsifiers"], indent=2), file=sys.stderr)
        return 1
    return emit(payload, args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
