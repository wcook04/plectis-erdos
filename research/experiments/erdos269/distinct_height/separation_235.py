#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact checks behind the irrationality proof for the {2,3,5} distinct-height sum.

The number is

    D = 1 + sum over t in {2^n, 3^n, 5^n : n >= 1} of 1/H(t),
    H(t) = 2^floor(log_2 t) * 3^floor(log_3 t) * 5^floor(log_5 t),

the sum of the reciprocals of the distinct running least common multiples of
the 5-smooth integers.  Group the prime powers into the dyadic blocks
(2^a, 2^(a+1)] and put P_a = H(2^a) and Y_a = P_a * sum_{t > 2^a} 1/H(t).
If block a has type tau, then Y_a = G_tau(Y_(a+1)) with G_tau(y) = (mu + y)/b.

Proof constants (the paper proves these by hand; this program recomputes
them in exact rational arithmetic):
  * the five block types and their pairs (b, mu):
      ''  (2, 1),  '3' (6, 3),  '5' (10, 3),  '35' (30, 13),  '53' (30, 9);
  * every map sends [0, 1] into [0, 1], and G_''(y) >= G_3(y) for y >= 0;
  * the lower bound 3/10 = min mu/b;
  * the upper bound 13/15 = G_''(G_''(7/15)), where 7/15 is the largest value
    at y = 1 of a map whose block contains a power of 5;
  * the images of [3/10, 13/15] under the five maps are pairwise disjoint,
    with consecutive gaps 1/900, 17/300, 79/900 and 1/180.

Finite observations over the first N blocks (default 3000).  They are sanity
checks, and the proof does not use them:
  * the pair (b, mu) derived directly from the heights agrees with the table;
  * the blocks containing a power of 5 start at block 2 and are 2 or 3 apart;
  * the number of powers of 3 in block a equals
    floor((a+1) log_3 2) - floor(a log_3 2), decided with integer powers;
  * every tail Y_a lies in [3/10, 13/15] and in the image of its own type only;
  * D is enclosed between two rationals that agree to many digits.

The irrationality of D is an infinite statement.  No computation here proves
it; the proof is the argument in the paper, which uses only the constants in
the first list.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import time
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path

TABLE = {"": (2, 1), "3": (6, 3), "5": (10, 3), "35": (30, 13), "53": (30, 9)}
FIVE_TYPES = ("5", "35", "53")


def ilog(base: int, x: int) -> int:
    """The largest e >= 0 with base**e <= x, by integer comparison."""
    e, power = 0, 1
    while power * base <= x:
        power *= base
        e += 1
    return e


def height(t: int) -> int:
    return 2 ** ilog(2, t) * 3 ** ilog(3, t) * 5 ** ilog(5, t)


def G(tau: str, y: Fraction) -> Fraction:
    b, mu = TABLE[tau]
    return (mu + y) / b


def proof_constants() -> dict:
    """The exact constants the proof uses, with every comparison it makes."""
    lower = min(Fraction(mu, b) for b, mu in TABLE.values())
    five_top = max(G(tau, Fraction(1)) for tau in FIVE_TYPES)
    upper = G("", G("", five_top))
    images = {tau: (G(tau, lower), G(tau, upper)) for tau in TABLE}
    order = sorted(images, key=lambda tau: images[tau][0])
    gaps = [images[order[i + 1]][0] - images[order[i]][1] for i in range(len(order) - 1)]
    checks = {
        "maps_send_unit_interval_into_itself": all(
            0 <= G(tau, Fraction(0)) and G(tau, Fraction(1)) <= 1 for tau in TABLE),
        # G_''(y) - G_3(y) = y/3: equal intercepts 1/2 and slopes 1/2 > 1/6.
        "empty_block_map_dominates_power_of_3_map_on_nonnegative_y":
            G("", Fraction(0)) == G("3", Fraction(0))
            and G("", Fraction(1)) - G("", Fraction(0)) > G("3", Fraction(1)) - G("3", Fraction(0)),
        "lower_bound_is_3_10": lower == Fraction(3, 10),
        "five_top_is_7_15": five_top == Fraction(7, 15),
        "upper_bound_is_13_15": upper == Fraction(13, 15),
        "images_pairwise_disjoint": all(gap > 0 for gap in gaps),
        "gaps_are_1_900_17_300_79_900_1_180":
            gaps == [Fraction(1, 900), Fraction(17, 300), Fraction(79, 900), Fraction(1, 180)],
        "tight_comparison_is_upper_below_three_lower": upper < 3 * lower,
        "crude_upper_bound_one_would_fail": not (G("3", Fraction(1)) < G("", lower)),
    }
    return {
        "lower_bound": lower,
        "upper_bound": upper,
        "five_type_top": five_top,
        "images_in_increasing_order": [(tau, images[tau]) for tau in order],
        "gaps": gaps,
        "checks": checks,
    }


def block_data(count: int):
    """Block types and (b, mu) derived from the heights of the prime powers."""
    limit = 2 ** (count + 1)
    powers = sorted({r ** n for r in (2, 3, 5) for n in range(1, count + 2) if r ** n <= limit})
    blocks: list[list[int]] = [[] for _ in range(count + 1)]
    for t in powers:
        a = ilog(2, t - 1)  # 2^a < t <= 2^(a+1)
        if a < count:
            blocks[a].append(t)
    heights: dict[int, int] = {}

    def H(t: int) -> int:
        if t not in heights:
            heights[t] = height(t)
        return heights[t]

    types, pairs = [], []
    for a in range(count):
        jumps = blocks[a]
        assert jumps[-1] == 2 ** (a + 1)
        inner = jumps[:-1]
        assert all(t % 2 for t in inner)
        tau = "".join("3" if t % 3 == 0 else "5" for t in inner)
        low = H(2 ** a) if a else 1
        high = H(2 ** (a + 1))
        b = Fraction(high, low)
        mu = sum(Fraction(high, H(t)) for t in jumps)
        assert b.denominator == 1 and mu.denominator == 1
        types.append(tau)
        pairs.append((int(b), int(mu)))
    return types, pairs


def finite_observations(count: int, digits: int) -> dict:
    extra = 80
    types, pairs = block_data(count + extra)
    table_ok = all(TABLE[tau] == pair for tau, pair in zip(types, pairs))
    fives = [a for a, tau in enumerate(types) if "5" in tau]
    five_gaps = sorted({y - x for x, y in zip(fives, fives[1:])})
    three_count_ok = all(
        types[a].count("3") == ilog(3, 2 ** (a + 1)) - ilog(3, 2 ** a) for a in range(count))
    every_three_blocks = all(any("5" in types[a + i] for i in range(3)) for a in range(count))
    # Exact enclosures of the tails, from the crude bound [0, 1] far out.
    low, high = Fraction(0), Fraction(1)
    enclosure = [None] * (count + extra)
    for a in range(count + extra - 1, -1, -1):
        b, mu = pairs[a]
        low, high = (mu + low) / b, (mu + high) / b
        enclosure[a] = (low, high)
    constants = proof_constants()
    m, M = constants["lower_bound"], constants["upper_bound"]
    images = dict(constants["images_in_increasing_order"])
    inside = all(m <= enclosure[a][0] and enclosure[a][1] <= M for a in range(count))
    decoded = sum(
        1 for a in range(count)
        if [tau for tau, (x, y) in images.items()
            if x <= enclosure[a][0] and enclosure[a][1] <= y] == [types[a]])
    getcontext().prec = digits + 10
    d_low, d_high = 1 + enclosure[0][0], 1 + enclosure[0][1]
    as_decimal = lambda x: Decimal(x.numerator) / Decimal(x.denominator)
    lo_text, hi_text = str(as_decimal(d_low))[: digits + 2], str(as_decimal(d_high))[: digits + 2]
    return {
        "blocks": count,
        "first_types": types[:12],
        "first_pairs": [list(pair) for pair in pairs[:12]],
        "type_counts": {tau: types[:count].count(tau) for tau in TABLE},
        "table_matches_heights": table_ok,
        "first_block_with_power_of_5": fives[0],
        "gaps_between_blocks_with_power_of_5": five_gaps,
        "every_three_consecutive_blocks_contain_power_of_5": every_three_blocks,
        "power_of_3_count_matches_floor_formula": three_count_ok,
        "tails_inside_proof_interval": inside,
        "tails_decoded_by_own_type": decoded,
        "observed_tail_range": [f"{float(min(e[0] for e in enclosure[:count])):.6f}",
                                f"{float(max(e[1] for e in enclosure[:count])):.6f}"],
        "D_lower": lo_text,
        "D_upper": hi_text,
    }


def as_text(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--blocks", type=int, default=3000,
                        help="number of dyadic blocks for the finite observations")
    parser.add_argument("--digits", type=int, default=40, help="digits of D to print")
    parser.add_argument("--output", type=Path, help="write the JSON receipt here")
    args = parser.parse_args(argv)
    started = time.time()
    constants = proof_constants()
    observed = finite_observations(args.blocks, args.digits)
    report = {
        "number": "D = 1 + sum over t in {2^n, 3^n, 5^n : n >= 1} of 1/H(t)",
        "proof_constants": {
            "pairs_b_mu": {tau: list(pair) for tau, pair in TABLE.items()},
            "lower_bound": as_text(constants["lower_bound"]),
            "five_type_top": as_text(constants["five_type_top"]),
            "upper_bound": as_text(constants["upper_bound"]),
            "images_in_increasing_order": [
                {"type": tau, "image": [as_text(x), as_text(y)]}
                for tau, (x, y) in constants["images_in_increasing_order"]],
            "gaps": [as_text(g) for g in constants["gaps"]],
            "checks": constants["checks"],
        },
        "finite_observations": observed,
        "scope": ("Exact rational arithmetic. The constants are the ones the proof uses; the "
                  "finite observations are sanity checks over the stated range and prove "
                  "nothing about later blocks. Irrationality of D is proved in the paper."),
    }
    script = Path(__file__).resolve()
    report["run"] = {
        "program": script.name,
        "program_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
        "arguments": {"blocks": args.blocks, "digits": args.digits},
        "python": platform.python_version(),
        "seconds": round(time.time() - started, 2),
    }
    ok = all(constants["checks"].values()) and observed["table_matches_heights"] \
        and observed["tails_inside_proof_interval"] \
        and observed["tails_decoded_by_own_type"] == args.blocks
    if args.output:
        args.output.write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n",
                               encoding="utf-8")
    for tau, (x, y) in constants["images_in_increasing_order"]:
        print(f"type {tau!r:5}: image [{as_text(x)}, {as_text(y)}]")
    print("gaps:", ", ".join(as_text(g) for g in constants["gaps"]))
    print(f"{args.blocks} blocks: tails inside [3/10, 13/15] and decoded by their own type: "
          f"{observed['tails_decoded_by_own_type']}")
    print(f"D = {observed['D_lower']}...")
    print("all checks pass" if ok else "A CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
