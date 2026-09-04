#!/usr/bin/env python3
"""Exact source-content probe for Zudilin's #1049 Hankel forms.

At x=z=1 let P_n=prod_{j<=n}(p^j-1) and
L_n=prod_{d<=n} Phi_d(p).  The source formula immediately gives the common
factor

    p^(n+1) P_n^3 / L_n

in every cleared linear form v_n.  This checker reconstructs the source forms,
regression-tests exactness of that content at the first discriminating ranks,
forms the first Hankel determinants, and records the all-rank scalar-factor
degree bound.  The all-rank proof is in ZudilinScalarContentLab.md.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
import json
from pathlib import Path
import sys

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "scripts/check_zudilin_scalar_content.py"
)
PRIMARY_SOURCE_REF = "annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/extracted.md"
ANALYSIS_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "ZudilinScalarContentLab.md"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/"
    "AdelicHeightBridge.lean"
)
CONSUMER_DECLARATIONS = [
    "zudilinScalarContent_ceiling_lt_required",
    "zudilinScalarContent_cannot_meet_required_charge",
]

p, mu = sp.symbols("p mu")


@lru_cache(None)
def pochhammer(n: int) -> sp.Expr:
    return sp.prod(1 - p**j for j in range(1, n + 1))


def gaussian(n: int, k: int) -> sp.Expr:
    return sp.cancel(pochhammer(n) / (pochhammer(k) * pochhammer(n - k)))


@lru_cache(None)
def cyclotomic_lcm(n: int) -> sp.Expr:
    return sp.prod(sp.cyclotomic_poly(d, p) for d in range(1, n + 1))


def predicted_content(n: int) -> sp.Expr:
    numerator = p ** (n + 1) * pochhammer(n) ** 3
    return sp.Poly(sp.cancel(numerator / cyclotomic_lcm(n)), p).as_expr()


@lru_cache(None)
def cleared_row(n: int) -> tuple[sp.Poly, sp.Poly, sp.Poly]:
    """Return the primary-source (A~,B~,C~) at x=z=1."""

    exponent = (n + 1) * (3 * n + 2) // 2
    clearing = sp.prod((p**j - 1) ** 3 for j in range(1, n + 1))
    clearing /= p ** (3 * n * (n + 1) // 2)
    a_sum = 0
    b_sum = 0
    for k in range(n + 1):
        core = (
            (-1) ** k
            * p ** (k * (k + 1) // 2)
            * sp.prod(p ** (k + j) - 1 for j in range(1, n + 1))
            / (pochhammer(k) * pochhammer(n - k))
        )
        a_sum += core
        b_sum += core * sum(1 / (p**ell - 1) for ell in range(1, k + 1))
    c_sum = 0
    for ell in range(n):
        inner = sum(
            (-1) ** k
            * gaussian(n, k)
            * gaussian(n + ell - k, n)
            * p ** ((n - k) * (n - k + 1) // 2)
            for k in range(ell + 1)
        )
        c_sum += inner / (p ** (n - ell) - 1)
    result = []
    for expression in (p**exponent * a_sum, p**exponent * b_sum, p**exponent * c_sum):
        numerator, denominator = sp.fraction(sp.cancel(clearing * expression))
        if sp.expand(denominator) != 1:
            raise AssertionError((n, denominator))
        result.append(sp.Poly(sp.expand(numerator), p))
    return tuple(result)  # type: ignore[return-value]


def polynomial_gcd(polynomials: list[sp.Poly]) -> sp.Poly:
    nonzero = [poly for poly in polynomials if not poly.is_zero]
    result = nonzero[0]
    for poly in nonzero[1:]:
        result = sp.gcd(result, poly)
    return result.monic()


def content_signature(poly: sp.Poly, max_cyclotomic: int) -> dict[str, object]:
    p_order = 0
    quotient = poly
    p_poly = sp.Poly(p, p)
    while quotient.rem(p_poly).is_zero:
        quotient = quotient.exquo(p_poly)
        p_order += 1
    cyclotomic_orders: dict[str, int] = {}
    for d in range(1, max_cyclotomic + 1):
        factor = sp.Poly(sp.cyclotomic_poly(d, p), p)
        order = 0
        while quotient.rem(factor).is_zero:
            quotient = quotient.exquo(factor)
            order += 1
        if order:
            cyclotomic_orders[str(d)] = order
    return {
        "p_order": p_order,
        "cyclotomic_orders": cyclotomic_orders,
        "unaccounted_quotient": str(sp.factor(quotient.as_expr())),
    }


def scalar_factor_degree(rank: int) -> int:
    # deg H_n, H_n=P_n^3/L_n, is 3n(n+1)/2-sum_{d<=n} phi(d).
    return 2 * sum(
        3 * n * (n + 1) // 2 - sum(int(sp.totient(d)) for d in range(1, n + 1))
        for n in range(rank)
    )


def compute(max_rank: int, degree_table_max: int) -> dict[str, object]:
    rows = [cleared_row(n) for n in range(2 * max_rank - 1)]
    row_checks = []
    for n, row in enumerate(rows):
        gcd = polynomial_gcd(list(row))
        predicted = sp.Poly(predicted_content(n), p).monic()
        quotients = [poly.exquo(predicted) for poly in row]
        row_checks.append(
            {
                "index": n,
                "coefficient_degrees": [(-1 if poly.is_zero else poly.degree()) for poly in row],
                "gcd_degree": gcd.degree(),
                "predicted_content_degree": predicted.degree(),
                "exact_gcd_equals_predicted_content": gcd == predicted,
                "primitive_quotient_gcd_is_one": polynomial_gcd(quotients).degree() == 0,
                "content_signature": content_signature(gcd, n),
            }
        )

    moments = [a.as_expr() * mu - b.as_expr() - c.as_expr() for a, b, c in rows]
    determinant_checks = []
    for rank in range(1, max_rank + 1):
        determinant = sp.expand(
            sp.Matrix(rank, rank, lambda i, j: moments[i + j]).det()
        )
        coefficients = [sp.Poly(coefficient, p) for coefficient in sp.Poly(determinant, mu).all_coeffs()]
        gcd = polynomial_gcd(coefficients)
        determinant_checks.append(
            {
                "rank": rank,
                "mu_degree": sp.Poly(determinant, mu).degree(),
                "p_degree": int(sp.degree(determinant, p)),
                "content_degree": gcd.degree(),
                "content_signature": content_signature(gcd, 2 * rank - 2),
            }
        )

    degree_table = []
    for rank in range(1, degree_table_max + 1):
        degree = scalar_factor_degree(rank)
        ceiling = rank**3 - rank
        raw = 4 * rank**3 - 3 * rank**2
        degree_table.append(
            {
                "rank": rank,
                "guaranteed_scalar_factor_degree": degree,
                "simple_cubic_ceiling": ceiling,
                "raw_charge": raw,
                "required_charge_numerator_39_over_41": 39 * raw,
                "ceiling_scaled_by_41": 41 * ceiling,
                "ceiling_is_below_required_charge": 41 * ceiling < 39 * raw,
            }
        )
    return {
        "row_checks": row_checks,
        "all_reconstructed_row_gcds_match": all(
            row["exact_gcd_equals_predicted_content"] for row in row_checks
        ),
        "all_reconstructed_quotients_are_primitive": all(
            row["primitive_quotient_gcd_is_one"] for row in row_checks
        ),
        "determinant_checks": determinant_checks,
        "degree_table": degree_table,
        "all_degree_ceilings_below_required_charge": all(
            row["ceiling_is_below_required_charge"] for row in degree_table
        ),
        "all_rank_factor": "(prod_{i=0}^{N-1} (P_i^3/L_i))^2 divides V_N(mu;p,1,1)",
        "factor_degree": "2 sum_{i<N} (3i(i+1)/2 - sum_{d<=i} phi(d))",
        "factor_degree_ceiling": "N^3-N",
        "required_extraction": ">(39/41)(4N^3-3N^2)",
    }


def emit(result: dict[str, object], output: Path | None, check: bool) -> int:
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if output is None:
        print(rendered, end="")
        return 0
    resolved = output.resolve()
    if check:
        if not resolved.exists() or resolved.read_text(encoding="utf-8") != rendered:
            print(f"stale receipt: {resolved}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(resolved)}))
        return 0
    resolved.parent.mkdir(parents=True, exist_ok=True)
    resolved.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(resolved)}))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-rank", type=int, default=3)
    parser.add_argument("--degree-table-max", type=int, default=24)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.max_rank <= 3:
        parser.error("--max-rank must lie in [1,3]")
    if args.degree_table_max < 1:
        parser.error("--degree-table-max must be positive")
    if args.check and args.output is None:
        parser.error("--check requires --output")

    scan = compute(args.max_rank, args.degree_table_max)
    result = {
        "schema": "erdos1049-zudilin-scalar-content/1",
        "claim_ceiling": (
            "The all-rank source algebra proves a genuine scalar factor, but its "
            "degree is at most N^3-N and therefore cannot alone meet the required "
            "Hankel charge extraction. Erdos #1049 remains open."
        ),
        "parameters": {
            "max_rank": args.max_rank,
            "degree_table_max": args.degree_table_max,
        },
        "scan": scan,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_1049",
            target_statement="Prove irrationality of the rational-base Lambert value at p=3/2.",
            claim_ceiling=(
                "The checker regression-tests exact source contents and the finite "
                "degree table. The authored algebra proves the all-rank factor and "
                "Lean proves its ceiling is insufficient; no irrationality follows."
            ),
            hypothesis_id="zudilin_source_scalar_content_supplies_required_charge",
            hypothesis_statement=(
                "The common scalar content already present in Zudilin's cleared "
                "rows removes enough of the raw cubic Hankel charge at p=3/2."
            ),
            probe_id="exact_source_row_content_and_charge_ceiling",
            probe_question=(
                "What is the exact common content of the specialized source rows, "
                "what determinant factor does it force at every rank, and can its "
                "degree meet the explicit 39/41 extraction requirement?"
            ),
            computation=(
                "Reconstruct A~, B~, C~ from the primary-source formulas over Z[p], "
                "take coefficient gcds and Hankel determinant contents exactly, and "
                "evaluate the closed totient-sum factor degree."
            ),
            falsifier=(
                "An all-rank upper bound below the explicit required extraction "
                "eliminates scalar row/column content as a sufficient mechanism."
            ),
            stop_condition=(
                "Once the universal factor and its strict charge ceiling are proved, "
                "retain the factor but move to residual border-rank or jet divisibility."
            ),
            survival_consequence=(
                "Sufficient cubic degree would close the missing arithmetic side of "
                "the normalized Hankel route."
            ),
            falsification_consequence=(
                "Scalar content alone is decisively insufficient; any successful "
                "Hankel route must extract additional residual determinant factors."
            ),
            consumer_ref=CONSUMER_REF,
            consumer_declarations=CONSUMER_DECLARATIONS,
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF, PRIMARY_SOURCE_REF],
            result_status="exact_one_way_result",
            result_summary=(
                "At x=z=1 every cleared source row contains "
                "p^(n+1)P_n^3/L_n. Hence (prod_{i<N} P_i^3/L_i)^2 divides "
                "the rank-N Hankel determinant. Its degree is at most N^3-N, "
                "strictly below (39/41)(4N^3-3N^2); scalar content alone is "
                "eliminated, while residual border-rank extraction remains open."
            ),
            resource_bounds={
                "maximum_exact_hankel_rank": args.max_rank,
                "maximum_reconstructed_row_index": 2 * args.max_rank - 2,
                "degree_table_max_rank": args.degree_table_max,
            },
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, PRIMARY_SOURCE_REF),
            source_record(REPO_ROOT, CONSUMER_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
        ],
    }
    return emit(result, args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
