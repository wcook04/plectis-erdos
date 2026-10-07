#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Independently check terminal rows from rational_membership_probe.py.

This standard-library checker reconstructs the greedy prefix and tail bound
from a JSON row. It does not import the producer. A finite survivor is not a
membership certificate and is deliberately refused. This is an ordinary exact
arithmetic check, not a Lean proof of the weighted-support theorem.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from pathlib import Path

MAX_HORIZON = 512
HOSTS = {"all", "odd", "not_divisible_by_3", "squarefree"}


def require(condition: bool, message: str) -> None:
    """Keep checks enabled under ``python -O``."""
    if not condition:
        raise ValueError(message)


def positive_integer(value: object, label: str) -> int:
    require(type(value) is int and value > 0, f"invalid {label}")
    return value


def rational(value: object, label: str) -> Fraction:
    require(type(value) is str, f"invalid {label}")
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError(f"invalid {label}") from exc


def member(host: str, n: int) -> bool:
    if host == "all":
        return True
    if host == "odd":
        return n % 2 == 1
    if host == "not_divisible_by_3":
        return n % 3 != 0
    require(host == "squarefree", "unknown host")
    p = 2
    while p * p <= n:
        if n % (p * p) == 0:
            return False
        p += 1
    return True


def weight(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def universal_tail_upper(n: int) -> Fraction:
    return Fraction(1, 1 << n) + Fraction(2, 3 * (1 << (2 * n)))


def verify(row: dict) -> str:
    require(type(row) is dict, "terminal witness must be an object")
    host = row["host"]
    require(type(host) is str and host in HOSTS, "unknown host")
    target = rational(row["target"], "target")
    require(target > 0, "target must be positive")
    depth = positive_integer(row["depth"], "depth")
    horizon = positive_integer(row["horizon"], "horizon")
    require(horizon >= depth + 64, "horizon outside producer contract")
    require(horizon <= MAX_HORIZON, "checker resource limit exceeded")
    indices = row["selected_indices"]
    require(type(indices) is list, "selected_indices must be a list")
    for n in indices:
        positive_integer(n, "selected index")
    require(indices == sorted(set(indices)), "selector must be strictly increasing")

    outcome = row["outcome"]
    require(outcome in ("excluded", "finite_representation"),
            "finite survival is not a terminal witness")
    if outcome == "excluded":
        end = positive_integer(row["first_rejection"], "first_rejection")
        require(row["finite_representation_end"] is None,
                "conflicting terminal outcomes")
        stop = end - 1
    else:
        end = positive_integer(row["finite_representation_end"],
                               "finite_representation_end")
        require(row["first_rejection"] is None, "conflicting terminal outcomes")
        stop = end
    require(end <= depth and member(host, end), "endpoint outside depth or host")

    # For k > n, 1/(2^k-1) <= 2^-k + 2*4^-k. The resulting universal
    # tail bound is below w_n, so each greedy choice is forced. Beyond the
    # horizon, w_k < 2^(1-k), giving the strict omitted-tail bound 2^(1-H).
    # The horizon suffix also checks that no earlier skip was a rejection.
    allowed = [n for n in range(1, horizon + 1) if member(host, n)]
    suffix: dict[int, Fraction] = {}
    remaining = Fraction(2, 1 << horizon)
    for n in reversed(allowed):
        suffix[n] = remaining
        remaining += weight(n)

    remainder = target
    actual: list[int] = []
    for n in allowed:
        if n > stop:
            break
        current_weight = weight(n)
        require(universal_tail_upper(n) < current_weight,
                "greedy dominance failed")
        if remainder >= current_weight:
            remainder -= current_weight
            actual.append(n)
            require(remainder != 0 or
                    (outcome == "finite_representation" and n == end),
                    "earlier finite termination")
        else:
            require(remainder <= suffix[n], "earlier rejection was skipped")
    require(actual == indices, "selector differs from forced greedy prefix")
    require(remainder == rational(row["remainder"], "remainder"),
            "remainder does not bind target and prefix")

    if outcome == "finite_representation":
        require(remainder == 0 and actual and actual[-1] == end,
                "finite selector does not sum to target")
        return "verified_finite_representation"

    require(remainder > 0, "nonpositive exclusion remainder")
    kind = row["tail_bound_kind"]
    if kind == "universal_analytic":
        start = positive_integer(row["tail_bound_from"], "tail_bound_from")
        require(end < start <= horizon + 1, "tail start outside horizon")
        require(all(not member(host, n) for n in range(end + 1, start)),
                "tail bound skips an allowed host index")
        bound = universal_tail_upper(start - 1)
    elif kind == "computed_horizon":
        bound = suffix[end]
    else:
        raise ValueError("unknown tail-bound derivation")
    require(rational(row["tail_upper"], "tail_upper") == bound,
            "tail bound disagrees with independent derivation")
    require(rational(row["weight"], "weight") == weight(end),
            "endpoint weight is wrong")
    require(bound < remainder < weight(end), "strict exclusion gap not established")
    return "verified_exclusion"


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if len(args) != 1:
        print("usage: verify_terminal_witness.py <probe-json-file>", file=sys.stderr)
        return 2
    try:
        data = json.loads(Path(args[0]).read_text(encoding="utf-8"))
        require(type(data) is dict, "probe JSON must be an object")
        rows = data.get("rows", [data])
        require(type(rows) is list, "rows must be a list")
        require(bool(rows), "no terminal witness rows supplied")
        print(json.dumps([verify(row) for row in rows]))
    except (OSError, json.JSONDecodeError, KeyError, TypeError, ValueError) as exc:
        print(f"witness rejected: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
