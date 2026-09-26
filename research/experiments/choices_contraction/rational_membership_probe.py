#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact rational-membership probe for reciprocal Mersenne subseries at base 2.

For a host set B of positive integers put w_n = 1/(2^n - 1) and

    A_B = { sum_{n in S} w_n : S a subset of B }.

Every weight exceeds the sum of all later weights, so a represented value has
exactly one selector and the greedy rule recovers it (short paper for Erdos
#257, sections "Unique coding and arithmetic membership" and "Greedy membership
and an integer recurrence").  The probe runs that greedy rule in exact rational
arithmetic on every reduced fraction p/q in (0, sum of B] with 2 <= q <= Q, through
depth N, and sorts each fraction into exactly one of three outcomes.

  excluded            At some index n <= N the remainder r satisfies
                      tail_upper(n) < r < w_n, where tail_upper(n) is a rigorous
                      upper bound for the sum of all later weights of B.  The
                      fraction is then outside A_B.  The triple
                      (n, r, tail_upper(n)) is a finite certificate.
  finite_representation
                      The remainder reached 0 at some index n <= N, so the
                      fraction is an explicit finite subseries sum.
  not_excluded        Neither event happened through depth N.  This outcome
                      says nothing about larger depths and is not a membership
                      claim.

The probe proves nothing about infinite representations.  See README.md.
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from math import gcd
from typing import Callable

OUTCOMES = ("excluded", "finite_representation", "not_excluded")


def squarefree(n: int) -> bool:
    p = 2
    while p * p <= n:
        if n % (p * p) == 0:
            return False
        p += 1
    return True


HOSTS: dict[str, Callable[[int], bool]] = {
    "all": lambda n: True,
    "not_divisible_by_3": lambda n: n % 3 != 0,
    "squarefree": squarefree,
    "odd": lambda n: n % 2 == 1,
}


def host_weights(member: Callable[[int], bool], horizon: int):
    """Exact weights and rigorous tail upper bounds for B within [1, horizon].

    For n > horizon, w_n < 2^(1-n), so the omitted tail is below 2^(1-horizon).
    """
    indices = [n for n in range(1, horizon + 1) if member(n)]
    weight = {n: Fraction(1, 2**n - 1) for n in indices}
    beyond = Fraction(2, 2**horizon)
    tail_upper: dict[int, Fraction] = {}
    acc = Fraction(0)
    for n in reversed(indices):
        tail_upper[n] = acc + beyond
        acc += weight[n]
    return indices, weight, tail_upper, acc, acc + beyond


def universal_tail_upper(n: int) -> Fraction:
    """A short bound for every host: sum_{k>n} w_k <= 2^-n + (2/3)4^-n."""
    return Fraction(1, 2**n) + Fraction(2, 3 * 4**n)


def classify(x: Fraction, indices, weight, tail_upper, depth: int,
             selected: list[int] | None = None):
    """Return (outcome, index), optionally recording the greedy selector prefix."""
    r = x
    for n in indices:
        if n > depth:
            break
        if r >= weight[n]:
            r -= weight[n]
            if selected is not None:
                selected.append(n)
            if r == 0:
                return "finite_representation", n
        elif r > tail_upper[n]:
            return "excluded", n
    return "not_excluded", None


def single_target(x: Fraction, host: str, depth: int, horizon: int) -> dict:
    """Expose one exact finite decision using the batch probe's classifier."""
    if depth < 1 or horizon < depth + 64:
        raise ValueError("depth must be positive and horizon at least depth + 64")
    indices, weight, tail_upper, total_lower, _ = host_weights(HOSTS[host], horizon)
    if not 0 < x <= total_lower:
        raise ValueError("target must be positive and at most the computed host-sum lower bound")
    selected: list[int] = []
    outcome, index = classify(x, indices, weight, tail_upper, depth, selected)
    remainder = x - sum((weight[n] for n in selected), Fraction(0))
    row = {
        "target": str(x),
        "host": host,
        "depth": depth,
        "horizon": horizon,
        "outcome": outcome,
        "selected_indices": selected,
        "remainder": str(remainder),
        "first_rejection": index if outcome == "excluded" else None,
        "finite_representation_end": index if outcome == "finite_representation" else None,
    }
    if outcome == "excluded":
        assert index is not None and tail_upper[index] < remainder < weight[index]
        next_host_index = next((n for n in indices if n > index), horizon + 1)
        short_bound = universal_tail_upper(next_host_index - 1)
        if short_bound < remainder:
            row["tail_upper"] = str(short_bound)
            row["tail_bound_kind"] = "universal_analytic"
            row["tail_bound_from"] = next_host_index
        else:
            row["tail_upper"] = str(tail_upper[index])
            row["tail_bound_kind"] = "computed_horizon"
        row["weight"] = str(weight[index])
    return row


def run(host: str, q_max: int, depth: int, horizon: int) -> dict:
    if horizon < depth + 64:
        raise SystemExit("horizon must exceed depth by at least 64 indices")
    indices, weight, tail_upper, total_lower, total_upper = host_weights(HOSTS[host], horizon)
    counts = {name: 0 for name in OUTCOMES}
    excluded_at: dict[int, int] = {}
    candidates = 0
    for q in range(2, q_max + 1):
        p = 1
        while Fraction(p, q) <= total_lower:
            if gcd(p, q) == 1:
                candidates += 1
                outcome, index = classify(Fraction(p, q), indices, weight, tail_upper, depth)
                counts[outcome] += 1
                if outcome == "excluded":
                    excluded_at[index] = excluded_at.get(index, 0) + 1
            p += 1
    return {
        "host": host,
        "q_max": q_max,
        "depth": depth,
        "horizon": horizon,
        "host_indices_through_depth": sum(1 for n in indices if n <= depth),
        "host_sum_lower": float(total_lower),
        "candidates": candidates,
        "counts": counts,
        "latest_exclusion_index": max(excluded_at) if excluded_at else None,
        "exclusions_by_index": {str(k): excluded_at[k] for k in sorted(excluded_at)},
    }


def grid(hosts, q_values, depths, horizon) -> dict:
    rows = [run(h, q, d, horizon) for h in hosts for q in q_values for d in depths]
    return {
        "schema": "plectis-choices-contraction-probe/1",
        "outcome_vocabulary": {
            "excluded": "outside the achievement set, with a finite certificate",
            "finite_representation": "an explicit finite subseries sum",
            "not_excluded": "no exclusion and no finite sum through the stated depth; no claim beyond it",
        },
        "rows": rows,
    }


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--target", help="one rational, such as 189/388, for an exact finite decision")
    ap.add_argument("--host", choices=list(HOSTS),
                    help="host for --target (default: all)")
    ap.add_argument("--hosts", nargs="+", choices=list(HOSTS))
    ap.add_argument("--q", nargs="+", type=int)
    ap.add_argument("--depth", nargs="+", type=int)
    ap.add_argument("--horizon", type=int, default=260)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)
    if args.target is not None:
        if args.hosts is not None or args.q is not None:
            ap.error("--hosts and --q belong to the batch mode; use --host with --target")
        try:
            target = Fraction(args.target)
            rows = [single_target(target, args.host or "all", depth, args.horizon)
                    for depth in (args.depth or [20])]
        except (ValueError, ZeroDivisionError) as exc:
            ap.error(str(exc))
        packet = {"schema": "plectis-single-target-probe/1", "rows": rows}
        if args.json:
            json.dump(packet, sys.stdout, indent=2, ensure_ascii=False)
            sys.stdout.write("\n")
        else:
            for row in rows:
                print(f"target={row['target']} host={row['host']} depth={row['depth']} "
                      f"outcome={row['outcome']} selected={row['selected_indices']}")
                if row["outcome"] == "excluded":
                    print(f"  exact certificate at n={row['first_rejection']}: "
                          f"{row['tail_upper']} < {row['remainder']} < {row['weight']}")
                elif row["outcome"] == "finite_representation":
                    print(f"  exact finite sum at n={row['finite_representation_end']}")
                else:
                    print("  no exclusion or finite sum through this depth; "
                          "no infinite-membership conclusion")
        return 0
    if args.host is not None:
        ap.error("--host belongs to --target; use --hosts for batch mode")
    packet = grid(args.hosts or list(HOSTS), args.q or [12, 24, 36],
                  args.depth or [10, 20, 40, 80, 160], args.horizon)
    if args.json:
        json.dump(packet, sys.stdout, indent=2, ensure_ascii=False)
        sys.stdout.write("\n")
        return 0
    for row in packet["rows"]:
        c = row["counts"]
        print(
            f"host={row['host']:<20} Q={row['q_max']:<3} N={row['depth']:<4} "
            f"candidates={row['candidates']:<5} excluded={c['excluded']:<5} "
            f"finite={c['finite_representation']:<3} not_excluded={c['not_excluded']:<5} "
            f"latest_exclusion_index={row['latest_exclusion_index']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
