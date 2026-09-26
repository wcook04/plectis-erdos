#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Decoding certificates for distinct-height running-LCM sums.

For a finite set P of at least two primes with least element p, write

    H_P(t) = prod_{r in P} r^floor(log_r t),
    D_P    = 1 + sum over the prime powers t = r^n (r in P, n >= 1) of 1/H_P(t).

H_P(t) is the least common multiple of the P-smooth integers up to t, and D_P
sums the reciprocal of each distinct value of that running least common
multiple once (Erdős, letter of 1 January 1973, Fibonacci Quarterly 12 (1974)
p. 335; Erdős Problem #269).

Blocks.  The block with index a is (p^a, p^(a+1)].  It ends with the jump at
p^(a+1) and contains at most one power of each other prime q in P, since
consecutive powers of q have ratio q > p.  The ordered block type
tau = (tau_1, ..., tau_v) lists the primes of those interior powers in
increasing order of the powers.  With P_a = H_P(p^a) and
Y_a = P_a * (sum of 1/H_P(t) over the prime powers t > p^a),

    Y_a = G_tau(Y_(a+1)),
    G_tau(y) = sum_{k=1..v} 1/(tau_1...tau_k) + (1 + y)/(p tau_1...tau_v),

where tau is the type of block a.

Superset automaton.  The power q^f lies in block floor(f log_p q), so
consecutive blocks containing a power of q are g_q or g_q + 1 apart, where
p^g_q < q < p^(g_q + 1).  A state records, for each q != p, the number d_q of
blocks since the last block containing a power of q (1 <= d_q <= g_q + 1).
A block must contain a power of q when d_q = g_q + 1, may contain one when
d_q = g_q, and cannot when d_q < g_q; every ordering of the chosen primes is
allowed.  Once every q has occurred, the actual sequence of block types is an
infinite path of this automaton, so every tail Y_a lies in the set V(s) of
values of infinite paths from the current state s.

Tail envelopes, two independent computations.
  outer: start from [0, 1/(p-1)] at every state and apply
         J(s) <- hull of the union of G_tau(J(t)) over the transitions (tau, t)
         from s, rounding every endpoint outwards to a multiple of 2^-96.
         By induction V(s) is contained in J(s) after any number of rounds.
         This is the certificate the paper describes.
  exact: the least and greatest values L(s), U(s) of infinite paths from s
         solve L(s) = min G_tau(L(t)) and U(s) = max G_tau(U(t)).  They are
         computed by policy iteration in exact rational arithmetic and then
         verified by substitution; the maps contract by at least 1/p, so the
         solutions are unique.  This is a cross-check with a different
         algorithm, and it gives the tightest envelopes of this automaton.

Depth-k test.  For each first type tau, form the union over all states s and
all automaton words of length k starting with tau of the images
G_word([envelope of the end state]).  The test passes when these unions are
pairwise disjoint (closed intervals; touching counts as a clash).

What is finite and what is proved.  Everything this program does is a
finite exact computation.  The implication "test passes => D_P irrational" is
proved in the paper (long record, the decoding criterion): a passing test
lets a tail determine its block type, rationality of D_P makes K*Y_a an
integer in [0, K/(p-1)] for some fixed K, so two tails coincide and the type
word is eventually periodic, which contradicts the irrationality of
log p / log q.  That argument is not executed here.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import sys
import time
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
from typing import Iterable

GRID_BITS = 96
DEFAULT_OUTER_ROUNDS = 80


# ---------------------------------------------------------------------------
# Arithmetic of one prime set
# ---------------------------------------------------------------------------

def is_prime(n: int) -> bool:
    if n < 2:
        return False
    return all(n % d for d in range(2, math.isqrt(n) + 1))


def ilog(base: int, x: int) -> int:
    """The largest e >= 0 with base**e <= x, by integer comparison."""
    e, power = 0, 1
    while power * base <= x:
        power *= base
        e += 1
    return e


def gap_exponent(p: int, q: int) -> int:
    """The g with p**g < q < p**(g+1); q > p are distinct primes."""
    g = ilog(p, q)
    assert p ** g < q < p ** (g + 1)
    return g


def type_map(p: int, tau: tuple[int, ...]) -> tuple[Fraction, Fraction]:
    """Coefficients (c, B) with G_tau(y) = c + B*y."""
    product_so_far = 1
    c = Fraction(0)
    for q in tau:
        product_so_far *= q
        c += Fraction(1, product_so_far)
    slope = Fraction(1, p * product_so_far)
    return c + slope, slope


@dataclass(frozen=True)
class Automaton:
    primes: tuple[int, ...]
    p: int
    others: tuple[int, ...]
    gaps: dict[int, int]
    states: tuple[tuple[int, ...], ...]
    transitions: dict[tuple[int, ...], tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]]
    maps: dict[tuple[int, ...], tuple[Fraction, Fraction]]


def build_automaton(primes: Iterable[int]) -> Automaton:
    ordered = tuple(sorted(set(primes)))
    if len(ordered) < 2 or not all(is_prime(r) for r in ordered):
        raise ValueError(f"need at least two distinct primes, got {ordered}")
    p, others = ordered[0], ordered[1:]
    gaps = {q: gap_exponent(p, q) for q in others}
    states = tuple(product(*[range(1, gaps[q] + 2) for q in others]))
    transitions = {}
    maps: dict[tuple[int, ...], tuple[Fraction, Fraction]] = {}
    for state in states:
        forced = [q for q, d in zip(others, state) if d == gaps[q] + 1]
        optional = [q for q, d in zip(others, state) if d == gaps[q]]
        out = []
        for size in range(len(optional) + 1):
            for extra in combinations(optional, size):
                chosen = set(forced) | set(extra)
                target = tuple(1 if q in chosen else d + 1 for q, d in zip(others, state))
                for tau in permutations(sorted(chosen)):
                    maps.setdefault(tau, type_map(p, tau))
                    out.append((tau, target))
        transitions[state] = tuple(out)
    return Automaton(ordered, p, others, gaps, states, transitions, maps)


# ---------------------------------------------------------------------------
# Tail envelopes
# ---------------------------------------------------------------------------

def _round_down(x: Fraction, bits: int) -> Fraction:
    return Fraction(math.floor(x * (1 << bits)), 1 << bits)


def _round_up(x: Fraction, bits: int) -> Fraction:
    return Fraction(math.ceil(x * (1 << bits)), 1 << bits)


def outer_envelopes(aut: Automaton, rounds: int = DEFAULT_OUTER_ROUNDS,
                    bits: int = GRID_BITS) -> dict[tuple[int, ...], tuple[Fraction, Fraction]]:
    """Interval iteration from [0, 1/(p-1)], rounded outwards: always an outer bound."""
    env = {s: (Fraction(0), Fraction(1, aut.p - 1)) for s in aut.states}
    for _ in range(rounds):
        new = {}
        for s in aut.states:
            lows, highs = [], []
            for tau, t in aut.transitions[s]:
                c, slope = aut.maps[tau]
                lows.append(c + slope * env[t][0])
                highs.append(c + slope * env[t][1])
            new[s] = (_round_down(min(lows), bits), _round_up(max(highs), bits))
        env = new
    return env


def _policy_values(aut: Automaton, policy) -> dict:
    """Solve V(s) = c + B*V(next) exactly on the functional graph of a policy."""
    values: dict = {}
    for start in aut.states:
        if start in values:
            continue
        path, index = [], {}
        s = start
        while s not in values and s not in index:
            index[s] = len(path)
            path.append(s)
            s = policy[s][1]
        if s in index:  # a new cycle path[index[s]:]
            cycle = path[index[s]:]
            acc_c, acc_slope = Fraction(0), Fraction(1)
            for u in cycle:
                c, slope = aut.maps[policy[u][0]]
                acc_c += acc_slope * c
                acc_slope *= slope
            values[cycle[0]] = acc_c / (1 - acc_slope)
            for u in reversed(cycle[1:]):
                c, slope = aut.maps[policy[u][0]]
                values[u] = c + slope * values[policy[u][1]]
            path = path[:index[s]]
        for u in reversed(path):
            c, slope = aut.maps[policy[u][0]]
            values[u] = c + slope * values[policy[u][1]]
    return values


def _extreme_values(aut: Automaton, pick) -> dict:
    policy = {s: aut.transitions[s][0] for s in aut.states}
    while True:
        values = _policy_values(aut, policy)
        changed = False
        for s in aut.states:
            best = policy[s]
            c, slope = aut.maps[best[0]]
            best_value = c + slope * values[best[1]]
            for tau, t in aut.transitions[s]:
                c, slope = aut.maps[tau]
                value = c + slope * values[t]
                if pick(value, best_value) and value != best_value:
                    best, best_value = (tau, t), value
            if best != policy[s]:
                policy[s] = best
                changed = True
        if not changed:
            return values


def exact_envelopes(aut: Automaton) -> dict[tuple[int, ...], tuple[Fraction, Fraction]]:
    """Exact least and greatest infinite-path values, verified by substitution."""
    low = _extreme_values(aut, lambda a, b: a < b)
    high = _extreme_values(aut, lambda a, b: a > b)
    for s in aut.states:
        images_low = [aut.maps[tau][0] + aut.maps[tau][1] * low[t] for tau, t in aut.transitions[s]]
        images_high = [aut.maps[tau][0] + aut.maps[tau][1] * high[t] for tau, t in aut.transitions[s]]
        if low[s] != min(images_low) or high[s] != max(images_high):
            raise AssertionError(f"Bellman equations fail at state {s}")
    return {s: (low[s], high[s]) for s in aut.states}


def envelopes(aut: Automaton, method: str):
    if method == "outer":
        return outer_envelopes(aut)
    if method == "exact":
        return exact_envelopes(aut)
    raise ValueError(method)


# ---------------------------------------------------------------------------
# The depth-k decoding test
# ---------------------------------------------------------------------------

def _merge(intervals):
    merged: list[tuple[Fraction, Fraction]] = []
    for low, high in sorted(intervals):
        if merged and low <= merged[-1][1]:
            if high > merged[-1][1]:
                merged[-1] = (merged[-1][0], high)
        else:
            merged.append((low, high))
    return merged


def first_type_images(aut: Automaton, env, depth: int):
    """Union, per first type, of G_word(envelope of the end state) over words of length depth."""
    if depth < 1:
        raise ValueError("depth must be at least 1")
    reach = {s: [env[s]] for s in aut.states}
    for _ in range(depth - 1):
        new = {}
        for s in aut.states:
            intervals = []
            for tau, t in aut.transitions[s]:
                c, slope = aut.maps[tau]
                intervals.extend((c + slope * lo, c + slope * hi) for lo, hi in reach[t])
            new[s] = _merge(intervals)
        reach = new
    images: dict[tuple[int, ...], list] = {}
    for s in aut.states:
        for tau, t in aut.transitions[s]:
            c, slope = aut.maps[tau]
            images.setdefault(tau, []).extend((c + slope * lo, c + slope * hi) for lo, hi in reach[t])
    return {tau: _merge(intervals) for tau, intervals in images.items()}


def decode(aut: Automaton, env, depth: int) -> dict:
    """Pairwise disjointness of the first-type unions, with the least gap or the overlaps."""
    images = first_type_images(aut, env, depth)
    tagged = sorted((lo, hi, tau) for tau, intervals in images.items() for lo, hi in intervals)
    overlaps: dict[tuple, Fraction] = {}
    least_gap = None
    # furthest right end reached so far by each type
    reach_by_type: dict[tuple[int, ...], Fraction] = {}
    for lo, hi, tau in tagged:
        for other, other_hi in reach_by_type.items():
            if other == tau:
                continue
            if lo <= other_hi:
                key = tuple(sorted((other, tau)))
                amount = min(hi, other_hi) - lo
                if key not in overlaps or amount > overlaps[key]:
                    overlaps[key] = amount
            else:
                gap = lo - other_hi
                if least_gap is None or gap < least_gap:
                    least_gap = gap
        if tau not in reach_by_type or hi > reach_by_type[tau]:
            reach_by_type[tau] = hi
    return {
        "depth": depth,
        "passed": not overlaps,
        "intervals": len(tagged),
        "least_gap": least_gap if not overlaps else None,
        "overlaps": sorted(overlaps.items(), key=lambda kv: -kv[1]),
    }


def first_passing_depth(aut: Automaton, env, max_depth: int):
    for depth in range(1, max_depth + 1):
        result = decode(aut, env, depth)
        if result["passed"]:
            return result
    return None


# ---------------------------------------------------------------------------
# Finite comparison with the actual block sequence (a sanity check only)
# ---------------------------------------------------------------------------

def actual_block_types(primes: Iterable[int], count: int) -> list[tuple[int, ...]]:
    ordered = tuple(sorted(set(primes)))
    p, others = ordered[0], ordered[1:]
    out = []
    for a in range(count):
        low, high = p ** a, p ** (a + 1)
        inside = []
        for q in others:
            power = q ** (ilog(q, low) + 1)  # least power of q above p^a
            if power < high:
                inside.append((power, q))
        out.append(tuple(q for _, q in sorted(inside)))
    return out


def check_actual_paths(aut: Automaton, env, blocks: int) -> dict:
    """Actual words are automaton paths and actual tails lie in their envelopes."""
    extra = 64
    types = actual_block_types(aut.primes, blocks + extra)
    low, high = Fraction(0), Fraction(1, aut.p - 1)
    enclosure = [None] * (blocks + extra)
    for a in range(blocks + extra - 1, -1, -1):
        c, slope = type_map(aut.p, types[a])
        low, high = c + slope * low, c + slope * high
        enclosure[a] = (low, high)
    last = {q: None for q in aut.others}
    checked = violations = 0
    for a in range(blocks):
        if all(last[q] is not None for q in aut.others):
            state = tuple(a - last[q] for q in aut.others)
            target = tuple(1 if q in types[a] else d + 1 for q, d in zip(aut.others, state))
            ok = state in env and (types[a], target) in aut.transitions[state]
            ok = ok and env[state][0] <= enclosure[a][0] and enclosure[a][1] <= env[state][1]
            checked += 1
            violations += not ok
        for q in types[a]:
            last[q] = a
    return {"blocks": blocks, "checked": checked, "violations": violations}


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def fraction_text(x: Fraction | None) -> str | None:
    return None if x is None else f"{x.numerator}/{x.denominator}"


def float_text(x: Fraction | None) -> str | None:
    return None if x is None else f"{float(x):.6g}"


def type_text(tau: tuple[int, ...]) -> str:
    return "(" + ",".join(map(str, tau)) + ")"


def run_record(script: Path, arguments: dict, started: float) -> dict:
    return {
        "program": script.name,
        "program_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
        "arguments": arguments,
        "python": platform.python_version(),
        "seconds": round(time.time() - started, 2),
    }


def certificate_report(primes: Iterable[int], max_depth: int, methods: Iterable[str],
                       validate_blocks: int = 0) -> dict:
    aut = build_automaton(primes)
    report = {
        "primes": list(aut.primes),
        "block_base": aut.p,
        "gap_exponents": {str(q): g for q, g in aut.gaps.items()},
        "states": len(aut.states),
        "block_types": len(aut.maps),
        "methods": {},
    }
    for method in methods:
        env = envelopes(aut, method)
        rows = []
        verdict = None
        for depth in range(1, max_depth + 1):
            result = decode(aut, env, depth)
            rows.append({
                "depth": depth,
                "passed": result["passed"],
                "intervals": result["intervals"],
                "least_gap": fraction_text(result["least_gap"]),
                "least_gap_float": float_text(result["least_gap"]),
                "largest_overlaps": [
                    {"types": [type_text(a), type_text(b)], "length": float_text(amount)}
                    for (a, b), amount in result["overlaps"][:4]
                ],
            })
            if result["passed"]:
                verdict = depth
                break
        report["methods"][method] = {
            "tail_range": [float_text(min(lo for lo, _ in env.values())),
                           float_text(max(hi for _, hi in env.values()))],
            "first_passing_depth": verdict,
            "depths": rows,
        }
        if validate_blocks:
            report["methods"][method]["actual_path_check"] = check_actual_paths(aut, env, validate_blocks)
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--primes", required=True,
                        help="comma-separated primes, for example 2,3,7")
    parser.add_argument("--max-depth", type=int, default=4)
    parser.add_argument("--method", choices=("outer", "exact", "both"), default="both")
    parser.add_argument("--validate-blocks", type=int, default=0,
                        help="also compare with the first N actual blocks (sanity check)")
    parser.add_argument("--output", type=Path, help="write the JSON receipt here")
    args = parser.parse_args(argv)
    started = time.time()
    primes = [int(x) for x in args.primes.split(",")]
    methods = ("outer", "exact") if args.method == "both" else (args.method,)
    report = certificate_report(primes, args.max_depth, methods, args.validate_blocks)
    verdicts = {m: report["methods"][m]["first_passing_depth"] for m in methods}
    report["run"] = run_record(Path(__file__).resolve(), {
        "primes": args.primes, "max_depth": args.max_depth, "method": args.method,
        "validate_blocks": args.validate_blocks}, started)
    text = json.dumps(report, indent=1, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    for method in methods:
        rows = report["methods"][method]["depths"]
        last = rows[-1]
        if last["passed"]:
            print(f"{report['primes']} [{method}]: passes at depth {last['depth']}, "
                  f"least gap {last['least_gap_float']}")
        else:
            worst = last["largest_overlaps"][0] if last["largest_overlaps"] else None
            print(f"{report['primes']} [{method}]: no pass through depth {last['depth']}; "
                  f"largest overlap {worst}")
    if len(set(verdicts.values())) > 1:
        print(f"methods disagree: {verdicts}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
