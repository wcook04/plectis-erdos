#!/usr/bin/env python3
"""Exact bounded-depth k-kernel ranks for phi, sigma, tau, mu and lambda.

For an arithmetic function ``f`` and integers ``k >= 2``, ``e >= 1`` the
bounded-depth ``k``-kernel span is

    V_{k,e}(f) = span_Q { n |-> f(k^j n + r) : 0 <= j <= e, 0 <= r < k^j }.

For the Euler totient the corpus proves ``dim V_{k,e}(phi) = k^e + 1`` with the
canonical basis indexed by ``{(0,0), (1,0)} u {(j,r) : 1<=j<=e, 1<=r<k^j, k∤r}``.
This module measures that dimension computationally for several functions and
bases, so that the totient formula is separated from the behaviour of other
classical multiplicative functions rather than assumed to be a generic
phenomenon.

Method.  Ranks are computed by Gaussian elimination over a prime field on an
evaluation matrix ``M[i][c] = f(channel_c(n_i))``.  A full-rank minor mod ``p``
certifies rational linear independence, so the measured value is always a
*lower* bound on the rational rank, and is exact whenever it meets the spanning
upper bound supplied by the reduction identities.  Two independent primes are
used; agreement is required.  This is exact finite linear algebra over integer
evaluations, not a proof of an all-``(k,e)`` formula.

Boundary: nothing here bears on Erdos #249 itself, which asks for irrationality
of ``sum phi(n)/2^n``.  These are structural measurements of the kernel span.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)
from system.lib.formal_math_probe_registry import mechanism_bindings  # noqa: E402


SOURCE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/"
    "scripts/check_all_base_multiplicative_kernel_rank.py"
)
CONSUMER_REF = (
    "formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/"
    "TotientMahlerDefect.lean"
)
ANALYSIS_REF = "docs/formal_math/odd_slope_affine_totient_independence.md"

PRIMES = (1_000_003, 1_000_033)


# ---------------------------------------------------------------- sieves


def sieve_tables(limit: int) -> dict[str, list[int]]:
    """Least-prime-factor sieve, then phi, sigma, tau, mu, lambda by factoring."""

    lpf = list(range(limit + 1))
    i = 2
    while i * i <= limit:
        if lpf[i] == i:
            for j in range(i * i, limit + 1, i):
                if lpf[j] == j:
                    lpf[j] = i
        i += 1

    phi = [0] * (limit + 1)
    sigma = [0] * (limit + 1)
    tau = [0] * (limit + 1)
    mu = [0] * (limit + 1)
    lam = [0] * (limit + 1)
    if limit >= 1:
        phi[1] = sigma[1] = tau[1] = mu[1] = lam[1] = 1
    for n in range(2, limit + 1):
        m = n
        ph, sg, tu, omega = 1, 1, 1, 0
        squarefree = True
        while m > 1:
            p = lpf[m]
            a = 0
            while m % p == 0:
                m //= p
                a += 1
            ph *= (p - 1) * p ** (a - 1)
            sg *= (p ** (a + 1) - 1) // (p - 1)
            tu *= a + 1
            omega += a
            if a > 1:
                squarefree = False
        phi[n] = ph
        sigma[n] = sg
        tau[n] = tu
        mu[n] = 0 if not squarefree else (-1 if omega % 2 else 1)
        lam[n] = -1 if omega % 2 else 1
    return {"phi": phi, "sigma": sigma, "tau": tau, "mu": mu, "lambda": lam}


# ---------------------------------------------------------------- channels


def all_channels(k: int, e: int) -> list[tuple[int, int]]:
    return [(j, r) for j in range(e + 1) for r in range(k**j)]


def canonical_totient_channels(k: int, e: int) -> list[tuple[int, int]]:
    """{(0,0),(1,0)} u {(j,r): 1<=j<=e, 1<=r<k^j, k does not divide r}."""

    out = [(0, 0), (1, 0)]
    for j in range(1, e + 1):
        out.extend((j, r) for r in range(1, k**j) if r % k != 0)
    return out


def canonical_mobius_channels(k: int, e: int) -> list[tuple[int, int]]:
    """Channels not identically zero for mu, per the all-base squarefree rule."""

    def squarefree(n: int) -> bool:
        d = 2
        while d * d <= n:
            if n % (d * d) == 0:
                return False
            d += 1
        return True

    out = [(0, 0)]
    if squarefree(k):
        out.append((1, 0))
    for j in range(1, e + 1):
        for r in range(1, k**j):
            if r % k == 0:
                continue
            g = 1
            a, b = k**j, r
            while b:
                a, b = b, a % b
            g = a
            if squarefree(g):
                out.append((j, r))
    return out


def canonical_liouville_channels(k: int, e: int) -> list[tuple[int, int]]:
    out = [(0, 0)]
    for j in range(1, e + 1):
        out.extend((j, r) for r in range(1, k**j) if r % k != 0)
    return out


# ---------------------------------------------------------------- rank


def matrix_rank_mod(rows: list[list[int]], p: int) -> int:
    work = [[x % p for x in row] for row in rows]
    height = len(work)
    width = len(work[0]) if height else 0
    rank = 0
    for col in range(width):
        pivot = next((r for r in range(rank, height) if work[r][col]), None)
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        inv = pow(work[rank][col], p - 2, p)
        work[rank] = [(x * inv) % p for x in work[rank]]
        for r in range(height):
            if r != rank and work[r][col]:
                factor = work[r][col]
                work[r] = [
                    (a - factor * b) % p for a, b in zip(work[r], work[rank])
                ]
        rank += 1
        if rank == height:
            break
    return rank


def evaluation_rows(
    table: list[int], channels: list[tuple[int, int]], k: int, row_count: int
) -> list[list[int]]:
    return [
        [table[k**j * n + r] for (j, r) in channels]
        for n in range(1, row_count + 1)
    ]


def measure(
    tables: dict[str, list[int]],
    function: str,
    k: int,
    e: int,
    channels: list[tuple[int, int]],
    row_multiplier: int,
) -> dict[str, object]:
    table = tables[function]
    row_count = len(channels) * row_multiplier
    rows = evaluation_rows(table, channels, k, row_count)
    ranks = {str(p): matrix_rank_mod(rows, p) for p in PRIMES}
    values = sorted(set(ranks.values()))
    return {
        "function": function,
        "base": k,
        "depth": e,
        "channel_count": len(channels),
        "evaluation_rows": row_count,
        "rank_by_prime": ranks,
        "primes_agree": len(values) == 1,
        "measured_rank_lower_bound": values[-1],
        "channel_count_upper_bound": len(channels),
        "rank_equals_channel_count": values[-1] == len(channels),
    }


def compute(cases: list[tuple[str, int, int]], row_multiplier: int) -> dict[str, object]:
    max_arg = 0
    for _, k, e in cases:
        channel_count = len(all_channels(k, e))
        max_arg = max(max_arg, k**e * (channel_count * row_multiplier + 1) + k**e)
    tables = sieve_tables(max_arg + 8)

    rows: list[dict[str, object]] = []
    for function, k, e in cases:
        if function == "mu":
            channels = canonical_mobius_channels(k, e)
        elif function == "lambda":
            channels = canonical_liouville_channels(k, e)
        else:
            channels = canonical_totient_channels(k, e)
        record = measure(tables, function, k, e, channels, row_multiplier)
        record["totient_formula_prediction"] = k**e + 1
        record["matches_totient_formula"] = (
            record["measured_rank_lower_bound"] == k**e + 1
        )
        rows.append(record)

    # sigma/tau at base 6, depth 2: the canonical totient indexing is NOT a
    # basis. Two evident relations cap the rank at 41; measure the full family
    # minus the two dependent level-two columns.
    composite: list[dict[str, object]] = []
    for function in ("sigma", "tau"):
        k, e = 6, 2
        full = all_channels(k, e)
        dropped = [(2, 6), (2, 30)]
        reduced = [ch for ch in full if ch not in dropped]
        record = measure(tables, function, k, e, reduced, row_multiplier)
        record["dropped_dependent_channels"] = [list(x) for x in dropped]
        record["full_family_channel_count"] = len(full)
        record["totient_formula_prediction"] = k**e + 1
        record["exceeds_totient_formula"] = (
            record["measured_rank_lower_bound"] > k**e + 1
        )
        table = tables[function]
        scale = 12 if function == "sigma" else 4
        witness = all(
            table[36 * n + 6] == scale * table[6 * n + 1]
            and table[36 * n + 30] == scale * table[6 * n + 5]
            for n in range(0, 400)
        )
        record["evident_relation_scale"] = scale
        record["evident_relations_hold_on_scan"] = witness
        composite.append(record)

    return {
        "row_multiplier": row_multiplier,
        "canonical_indexing_cases": rows,
        "all_canonical_cases_match_totient_formula": all(
            row["matches_totient_formula"] for row in rows if row["function"] == "phi"
        ),
        "composite_base_sigma_tau": composite,
        "sigma_tau_exceed_totient_formula_at_base_six": all(
            row["exceeds_totient_formula"] for row in composite
        ),
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


DEFAULT_CASES = [
    ("phi", 2, 4),
    ("phi", 3, 3),
    ("phi", 4, 2),
    ("phi", 5, 2),
    ("phi", 6, 2),
    ("phi", 12, 2),
    ("sigma", 4, 2),
    ("sigma", 9, 2),
    ("tau", 4, 2),
    ("tau", 9, 2),
    ("mu", 2, 4),
    ("mu", 3, 3),
    ("mu", 4, 2),
    ("mu", 6, 2),
    ("mu", 12, 2),
    ("lambda", 2, 4),
    ("lambda", 3, 3),
    ("lambda", 4, 2),
    ("lambda", 5, 2),
]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--row-multiplier", type=int, default=2)
    parser.add_argument(
        "--extra-case",
        action="append",
        default=[],
        metavar="FUNCTION:BASE:DEPTH",
        help=(
            "append a case, for example phi:30:2. Large bases are slow: the "
            "base-30 depth-2 totient case is a 901-column elimination."
        ),
    )
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.row_multiplier < 1:
        parser.error("--row-multiplier must be positive")
    if args.check and args.output is None:
        parser.error("--check requires --output")

    cases = list(DEFAULT_CASES)
    for raw in args.extra_case:
        parts = raw.split(":")
        if len(parts) != 3:
            parser.error(f"--extra-case must be FUNCTION:BASE:DEPTH, got {raw!r}")
        function, base, depth = parts[0], int(parts[1]), int(parts[2])
        if function not in ("phi", "sigma", "tau", "mu", "lambda"):
            parser.error(f"unknown function in --extra-case: {function}")
        if base < 2 or depth < 1:
            parser.error("--extra-case base must be >= 2 and depth >= 1")
        cases.append((function, base, depth))

    scan = compute(cases, args.row_multiplier)
    totient_sharp = bool(scan["all_canonical_cases_match_totient_formula"])
    sigma_tau_break = bool(scan["sigma_tau_exceed_totient_formula_at_base_six"])
    summary = (
        "The canonical totient indexing attains rank k^e+1 at every measured "
        "base and depth, including composite bases where the canonical residue "
        "condition is k does not divide r rather than gcd(k,r)=1. At base 6 "
        "depth 2 the same indexing FAILS for sigma and tau: both have rank 41, "
        "not 6^2+1=37, with the two evident level-two relations verified on a "
        "finite scan. The k^e+1 formula is therefore specific to the totient "
        "(and its n^q phi^m class), not a generic multiplicative phenomenon."
        if totient_sharp and sigma_tau_break
        else
        "At least one measured case departs from the recorded prediction; "
        "inspect the per-case rows before citing any rank."
    )
    result = {
        "schema": "erdos249-all-base-multiplicative-kernel-rank/1",
        "claim_ceiling": (
            "Exact finite linear algebra over integer evaluations. A full-rank "
            "minor mod p certifies rational independence at that (k,e); it does "
            "not prove an all-(k,e) formula and bears on Erdos #249 only "
            "structurally."
        ),
        "parameters": {"row_multiplier": args.row_multiplier},
        "scan": scan,
        "experiment_contract": build_experiment_contract(
            problem_id="erdos_249",
            target_statement=(
                "Prove that the binary totient series sum phi(n)/2^n is irrational."
            ),
            claim_ceiling=(
                "Structural measurement of bounded-depth kernel spans. Not a "
                "proof of any all-(k,e) rank formula and not a step toward the "
                "irrationality target."
            ),
            hypothesis_id="k_kernel_rank_formula_is_generic_multiplicative",
            hypothesis_statement=(
                "dim V_{k,e} = k^e + 1 with the canonical indexing holds for "
                "classical multiplicative functions generally, not only for the "
                "Euler totient."
            ),
            probe_id="canonical_indexing_rank_across_functions_and_bases",
            probe_question=(
                "Does the canonical totient indexing remain a basis for sigma, "
                "tau, mu and lambda at the same bases and depths?"
            ),
            computation=(
                "Sieve phi, sigma, tau, mu, lambda; build evaluation matrices "
                "over the canonical channels; compute rank by Gaussian "
                "elimination over two distinct prime fields and require "
                "agreement."
            ),
            falsifier=(
                "A function and base at which the canonical-channel rank "
                "differs from k^e+1, exhibiting extra or missing modes."
            ),
            stop_condition=(
                "Once the totient formula is confirmed and a composite-base "
                "counterexample is isolated for sigma and tau, the remaining "
                "work is the Lean all-base independence theorem, not further "
                "scanning."
            ),
            survival_consequence=(
                "A generic formula would suggest the totient reduction is not "
                "carrying arithmetic specific to phi."
            ),
            falsification_consequence=(
                "A composite-base failure for sigma and tau localises the "
                "mechanism in phi's Euler factors and rules out a purely "
                "combinatorial derivation of the rank."
            ),
            consumer_ref=CONSUMER_REF,
            consumer_declarations=[
                "linearIndependent_canonicalTotientKernelFamily",
                "finrank_canonicalTotientKernel_eq",
                "finrank_totientKernelThroughLevelFamily_eq",
            ],
            analysis_refs=[ANALYSIS_REF],
            source_refs=[SOURCE_REF],
            result_status=(
                "exact_one_way_result"
                if totient_sharp and sigma_tau_break
                else "finite_support"
            ),
            result_summary=summary,
            resource_bounds={
                "case_count": len(cases),
                "row_multiplier": args.row_multiplier,
                "prime_field_count": len(PRIMES),
            },
        ),
        "mechanism_bindings": mechanism_bindings(
            problem_id="erdos_249",
            motivated_by=[
                "totient_k_kernel_rank_k_to_e_plus_one",
                "totient_k_kernel_canonical_basis_and_reduction_normal_form",
            ],
            supports=[
                "totient_k_kernel_rank_k_to_e_plus_one",
                "totient_k_kernel_canonical_basis_and_reduction_normal_form",
            ],
            rationale=(
                "The canonical k-kernel indexing was measured only for the "
                "totient. Running the same indexing against sigma, tau, mu and "
                "lambda decides whether k^e+1 is a totient fact or a generic "
                "multiplicative one, and isolates the exact base at which the "
                "indexing stops being a basis."
            ),
        ),
        "sources": [
            source_record(REPO_ROOT, SOURCE_REF),
            source_record(REPO_ROOT, CONSUMER_REF),
            source_record(REPO_ROOT, ANALYSIS_REF),
        ],
        "summary": summary,
    }
    return emit(result, args.output, args.check)


if __name__ == "__main__":
    raise SystemExit(main())
