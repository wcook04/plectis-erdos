#!/usr/bin/env python3
"""Breadth gate for affine index actions in the Erdős-257 Lambert series.

The Lambert atom is K_n(x)=x^n/(1-x^n).  Mahler substitution intertwines it
exactly with multiplication of the index: K_n(x^a)=K_{an}(x).  This audit
checks that translated affine actions n -> an+b have new cyclotomic pole
orders and therefore are not the same functional-equation mechanism.

It also records the elementary reciprocal-summability bound for every finite
union of forward affine orbits.  Such sparse supports are already covered by
the repository's reciprocal-summable irrationality theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path


problem_id = "erdos_257"


REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT = Path("formal_math/erdos257_period_noncollapse/scripts/affine_lambert_adaptation_probe.py")
NOTE = Path("formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/AffineAdaptationBreadthGate.md")
RECEIPT = Path("state/formal_math/erdos257_period_noncollapse/affine_lambert_adaptation_receipt.json")


def atom(n: int, x: Fraction) -> Fraction:
    return x**n / (1 - x**n)


def pole_witness(a: int, b: int, max_mahler_power: int) -> dict:
    """Find n for which an+b divides none of a^j n, 0 <= j <= J.

    A primitive (an+b)-th root is then a pole of K_{an+b}; it is not a pole
    of any K_n(x^(a^j)).  Polynomial coefficients cannot create that pole.
    """
    if b == 0:
        return {
            "status": "multiplicative_control",
            "n": 1,
            "image_index": a,
            "matching_mahler_power": 1,
            "identity": "K_(a*n)(x) = K_n(x^a)",
        }
    for n in range(2, 100000):
        if math.gcd(n, b) != 1:
            continue
        image = a * n + b
        divisibilities = [pow(a, j) * n % image == 0 for j in range(max_mahler_power + 1)]
        if image > pow(a, max_mahler_power) and not any(divisibilities):
            return {
                "status": "translated_pole_order_escapes",
                "n": n,
                "image_index": image,
                "mahler_powers_tested": list(range(max_mahler_power + 1)),
                "image_divides_a_pow_j_n": divisibilities,
                "gcd_n_image": math.gcd(n, image),
            }
    raise RuntimeError(f"no pole witness for a={a}, b={b}")


def affine_orbit(a: int, b: int, seed: int, terms: int) -> list[int]:
    result = []
    value = seed
    for _ in range(terms):
        result.append(value)
        value = a * value + b
    return result


def build_receipt(max_a: int, max_mahler_power: int, orbit_terms: int) -> dict:
    x = Fraction(1, 2)
    multiplicative_controls = []
    translated_rows = []
    orbit_rows = []

    for a in range(2, max_a + 1):
        exact = all(atom(a * n, x) == atom(n, x**a) for n in range(1, 65))
        multiplicative_controls.append({
            "a": a,
            "n_grid": [1, 64],
            "exact_at_x_one_half": exact,
            "identity": "K_(a*n)(x)=K_n(x^a)",
        })
        for b in range(1, a):
            row = {"a": a, "b": b, **pole_witness(a, b, max_mahler_power)}
            translated_rows.append(row)

        for b in (0, 1, a - 1):
            values = affine_orbit(a, b, 1, orbit_terms)
            reciprocal_partial = sum((Fraction(1, value) for value in values), Fraction(0))
            geometric_bound = Fraction(a, a - 1)  # seed=1 and u_t >= a^t
            orbit_rows.append({
                "a": a,
                "b": b,
                "seed": 1,
                "terms": orbit_terms,
                "last_index_digits": len(str(values[-1])),
                "reciprocal_partial": f"{reciprocal_partial.numerator}/{reciprocal_partial.denominator}",
                "geometric_upper_bound": f"{geometric_bound.numerator}/{geometric_bound.denominator}",
                "below_geometric_bound": reciprocal_partial <= geometric_bound,
            })

    status = (
        "ok"
        if all(row["exact_at_x_one_half"] for row in multiplicative_controls)
        and all(row["status"] == "translated_pole_order_escapes" for row in translated_rows)
        and all(row["below_geometric_bound"] for row in orbit_rows)
        else "FAIL"
    )
    return {
        "schema": "erdos257.affine_lambert_adaptation_breadth_gate.v1",
        "script": str(SCRIPT),
        "note": str(NOTE),
        "parameters": {
            "max_a": max_a,
            "translations_b": "1 <= b < a",
            "max_mahler_power": max_mahler_power,
            "orbit_terms": orbit_terms,
        },
        "exact_kernel_identity": "K_n(x^a)=K_(a*n)(x)",
        "multiplicative_controls": multiplicative_controls,
        "translated_affine_pole_witnesses": translated_rows,
        "forward_affine_orbit_reciprocal_bounds": orbit_rows,
        "mechanism_decision": {
            "status": "specific_affine_and_k_adic_examples_do_not_open_a_third_adaptation",
            "translated_action": (
                "n -> a*n+b with b nonzero does not intertwine the Lambert atom with "
                "a fixed finite Mahler tower: K_(a*n+b) has new cyclotomic pole orders."
            ),
            "finite_forward_orbits": (
                "Every finite union of forward affine orbits is reciprocal-summable and "
                "is already settled by the reciprocal-summable irrationality theorem."
            ),
            "finite_k_adic_substitution": (
                "A finite substitution on k-adic chains uses the existing x -> x^k action; "
                "if it yields a Mahler equation, that is base-k adaptation, not a third action."
            ),
        },
        "nonclaims": [
            "This does not classify all semigroup actions or all functional equations of Lambert series.",
            "The pole argument eliminates fixed finite Mahler-tower intertwining for the translated atom; it does not forbid a more elaborate identity with n-dependent coefficients.",
            "This does not solve Erdős 257 or prove anything about survival of a rational greedy orbit.",
        ],
        "status": status,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-a", type=int, default=12)
    parser.add_argument("--max-mahler-power", type=int, default=4)
    parser.add_argument("--orbit-terms", type=int, default=24)
    parser.add_argument("--output", type=Path, default=REPO_ROOT / RECEIPT)
    args = parser.parse_args()
    payload = build_receipt(args.max_a, args.max_mahler_power, args.orbit_terms)
    payload["script_sha256"] = hashlib.sha256((REPO_ROOT / SCRIPT).read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": payload["status"],
        "multiplicative_controls": len(payload["multiplicative_controls"]),
        "translated_pole_witnesses": len(payload["translated_affine_pole_witnesses"]),
        "orbit_bounds": len(payload["forward_affine_orbit_reciprocal_bounds"]),
        "mechanism_decision": payload["mechanism_decision"],
    }, indent=2, sort_keys=True))
    return 0 if payload["status"] == "ok" else 1


if __name__ == "__main__":
    raise SystemExit(main())
