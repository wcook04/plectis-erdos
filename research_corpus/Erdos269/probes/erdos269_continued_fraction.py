#!/usr/bin/env python3
"""Diophantine type of the Erdos #269 {2,3,5} normalized tail.

Why this probe exists
---------------------
The denominator-exclusion certificate showed that the largest certified
exclusion at window depth L is Theta(sqrt(B_L)) with fitted exponent 0.4974.
That is exactly the bound a *badly approximable* real would give, and it says
the whole escape mechanism is controlled by one classical quantity: how well
X_a is approximated by rationals.

A denominator q survives the escape test at depth L precisely when q*X_a is
abnormally close to an integer.  The convergent denominators of the continued
fraction of X_a are, by definition, exactly the q that make |q X_a - p|
smallest.  So the partial quotients ARE the near-conspiracies: a partial
quotient a_(n+1) of size A means the denominator q_n survives roughly
log_8(A) extra depths.

Probe
-----
Compute X_a to certified precision from the exact truncation X_a = (F_K + X_(a+K))/B_K
with 0 < X_(a+K) <= kappa_K, take the continued fraction of F_K/B_K, and keep
only the partial quotients that are provably those of X_a.

Predeclared falsifier
---------------------
An unbounded or rapidly growing family of partial quotients (say a_n exceeding
exp(c n)) would mean X_a is a Liouville-type target, the escape depths are not
uniformly controlled, and the equidistribution reading is wrong.  Bounded-type
or generic Gauss-Kuzmin behaviour instead says the analytic producer must be an
effective irrationality-measure statement, not a Lyapunov or coboundary
argument.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal_math.probes.erdos269_blocks import build_blocks  # noqa: E402


def truncation(start: int, depth: int, blocks) -> tuple[int, int, int]:
    base, forcing, ending = 1, 0, 0
    for index in range(start - 1, start - 1 + depth):
        block_base, block_digit, ending = blocks[index]
        base *= block_base
        forcing = block_base * forcing + block_digit
    return base, forcing, ending


def _cf_terms(num: int, den: int, limit: int) -> list[int]:
    terms: list[int] = []
    while den and len(terms) < limit:
        a = num // den
        terms.append(a)
        num, den = den, num - a * den
    return terms


def certified_partial_quotients(forcing: int, base: int, kappa: int, limit: int):
    """Partial quotients provably shared by every X in (F/B, (F+kappa)/B].

    Continued-fraction prefixes are exactly cylinder memberships, and cylinders
    are intervals, so any prefix common to the two endpoints is common to the
    whole interval.  Taking the common prefix of the endpoint expansions (and
    discarding the last shared term, which the [.., a] = [.., a-1, 1] ambiguity
    can make unstable) is therefore an airtight certification.
    """
    left = _cf_terms(forcing, base, limit)
    right = _cf_terms(forcing + kappa, base, limit)
    shared: list[int] = []
    for x, y in zip(left, right):
        if x != y:
            break
        shared.append(x)
    if shared:
        shared.pop()                      # drop the boundary-ambiguous term
    denoms: list[int] = []
    q_prev, q_cur = 0, 1
    for a in shared:
        q_prev, q_cur = q_cur, a * q_cur + q_prev
        denoms.append(q_cur)
    return shared, denoms


def run(start: int, depth: int) -> dict:
    blocks = build_blocks(start + depth + 8)
    base, forcing, ending = truncation(start, depth, blocks)
    kappa = (ending * ending + 10 * ending + 27) // 9 + 1
    quotients, denoms = certified_partial_quotients(forcing, base, kappa, 200000)
    # drop the integer part
    tail = quotients[1:]
    if not tail:
        return {"probe_id": "erdos269_continued_fraction", "status": "no_certified_terms"}
    biggest = sorted(((a, i + 1) for i, a in enumerate(tail)), reverse=True)[:12]
    # Gauss-Kuzmin reference: P(a = k) = log2(1 + 1/(k(k+2)))
    counts = {k: sum(1 for a in tail if a == k) for k in range(1, 6)}
    n = len(tail)
    gk = {k: round(math.log2(1 + 1.0 / (k * (k + 2))), 4) for k in range(1, 6)}
    observed = {k: round(counts[k] / n, 4) for k in range(1, 6)}
    # Levy constant: (1/n) log q_n -> pi^2 / (12 ln 2) = 1.18657
    levy = math.log(denoms[-1]) / len(denoms)
    # Irrationality-exponent proxy: max over n of log q_(n+1) / log q_n
    exps = []
    for i in range(2, len(denoms)):
        if denoms[i - 1] > 1:
            exps.append(math.log(denoms[i]) / math.log(denoms[i - 1]))
    return {
        "probe_id": "erdos269_continued_fraction",
        "start": start,
        "truncation_depth": depth,
        "base_bits": base.bit_length(),
        "certified_partial_quotients": n,
        "largest_denominator_bits": denoms[-1].bit_length(),
        "max_partial_quotient": max(tail),
        "largest_partial_quotients_with_index": biggest,
        "mean_partial_quotient": round(sum(tail) / n, 4),
        "gauss_kuzmin_reference": gk,
        "observed_frequencies": observed,
        "levy_constant_observed": round(levy, 5),
        "levy_constant_reference": 1.18657,
        "irrationality_exponent_proxy_max": round(max(exps), 5) if exps else None,
        "irrationality_exponent_proxy_tail_max": (
            round(max(exps[len(exps) // 2:]), 5) if exps else None
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--start", type=int, default=1)
    ap.add_argument("--depth", type=int, default=3000)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.start, args.depth)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps(payload, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
