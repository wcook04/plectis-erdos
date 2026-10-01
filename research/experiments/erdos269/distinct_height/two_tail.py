#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact illustrations of the two-tail proof that D_P is irrational.

For a finite set P of at least two primes list the prime powers of P as
t_1 < t_2 < ..., let q_k be the prime of t_k, and put

    D_P = 1 + sum_k 1/(q_1 ... q_k).

The #269 papers prove that D_P is irrational for every such P.  For a finite
word s = s_1 ... s_n over P write Pi(s) = s_1 ... s_n and

    f(s) = sum_{t=1..n} s_{t+1} ... s_n,

so that the value V(u) = sum_i 1/(u_1 ... u_i) of an infinite word satisfies
V(s u) = (f(s) + V(u)) / Pi(s).  The proof compares the tail after t_k with the
tail after t_k p^n for a small return n.  The two future words differ only by
rearranging short chains of crossings, a rational D_P forces f to agree on
every chain and its rearrangement, and a chain that is one transposition gives
f(ab) - f(ba) = b - a != 0.

This program checks the finite facts the papers state about that argument.
The proof uses none of them.

  identity      V(s u) = (f(s) + V(u))/Pi(s) on random finite words, and the
                adjacent-swap formula f(s) - f(s') = (s_(i+1) - s_i) s_(i+2)...s_n.
  injectivity   f is injective on the orderings of two or three distinct primes,
                and not for four: f(5,7,3,2) = f(7,2,3,5) = 51.
  reversal      a chain and its reversal can collide:
                f(43,13,3,53) = f(53,3,13,43) = 2280.
  identity2357  the type words (5,7,3),() and (7),(3,5) of the dyadic blocks of
                {2,3,5,7} have the same affine map y -> (103 + y)/420, and both
                continue by (3),(5,7) to the same automaton state, so the
                finite-state decoding test of certificate.py fails at every depth.
  chains        for a return n the crossings after t_k and after t_k p^n
                correspond exactly, the chains keep their places, and no
                rearranged chain has equal f-values (simulation on four sets).
  close_pair    the exact difference x_k - x_m for a close pair of {2,3,5,7}
                and its predicted leading term.
  euler         random line arrangements on the torus R^2/Z^2 satisfy
                sum_v (k_v - 3) <= 0 and have a vertex on exactly two lines.
  ep_identities for the single-prime sub-sums E_p = sum_a 1/H_P(p^a) of the
                catalogue series: V_p(s u) = (f_p(s) + V_p(u))/Pi(s); f_p of an
                ordering of distinct primes is the product of the followers of
                p; R_{p,q} = E_p E_q term by term; the carries of the three-
                and four-prime product formula; D_P = sum_q E_q - (|P| - 1).
  ep_close_pair the exact difference of two E_2 tails for {2,3,5} at a return.

Every decision uses integers or Fractions.  Floating point selects the return
n; Decimal logarithms at 80 digits cut chains, with the smallest margin to the
cut reported.  The default run is the fast subset used by the test; --full
runs everything and writes the receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import heapq
import json
import math
import platform
import random
import sys
import time
from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import combinations, permutations
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from certificate import build_automaton, type_map  # noqa: E402

getcontext().prec = 80


# ---------------------------------------------------------------------------
# Words, values and f
# ---------------------------------------------------------------------------

def f(word) -> int:
    """sum_{t=1..n} word_{t+1} ... word_n."""
    total, product = 0, 1
    for letter in reversed(word):
        total += product
        product *= letter
    return total


def value(word) -> Fraction:
    """sum_i 1/(word_1 ... word_i) over a finite word."""
    total, product = Fraction(0), 1
    for letter in word:
        product *= letter
        total += Fraction(1, product)
    return total


def primes_upto(n: int) -> list[int]:
    return [q for q in range(2, n + 1) if all(q % d for d in range(2, math.isqrt(q) + 1))]


def check_identity(trials: int = 2000, swaps: int = 5000, seed: int = 1) -> dict:
    rng = random.Random(seed)
    letters = [2, 3, 5, 7, 11]
    for _ in range(trials):
        s = [rng.choice(letters) for _ in range(rng.randint(1, 6))]
        u = [rng.choice(letters) for _ in range(rng.randint(0, 8))]
        assert value(s + u) == (f(s) + value(u)) / math.prod(s)
    pool = primes_upto(47)
    for _ in range(swaps):
        s = rng.sample(pool, rng.randint(2, 7))
        i = rng.randrange(len(s) - 1)
        t = s[:]
        t[i], t[i + 1] = t[i + 1], t[i]
        assert f(s) - f(t) == (s[i + 1] - s[i]) * math.prod(s[i + 2:])
    return {"identity_checks": trials, "adjacent_swap_checks": swaps}


def injectivity(bound: int, size: int) -> dict:
    """Orderings of one set of distinct primes with a repeated f-value."""
    sets = collisions = 0
    examples = []
    for chosen in combinations(primes_upto(bound), size):
        sets += 1
        seen: dict[int, tuple[int, ...]] = {}
        for order in permutations(chosen):
            v = f(order)
            if v in seen:
                collisions += 1
                if len(examples) < 3:
                    examples.append([list(seen[v]), list(order), v])
            else:
                seen[v] = order
    return {"bound": bound, "size": size, "sets": sets, "collisions": collisions,
            "examples": examples}


def reversal_collisions(bound: int, size: int) -> dict:
    hits = []
    pairs = 0
    for chosen in combinations(primes_upto(bound), size):
        for order in permutations(chosen):
            if order[0] > order[-1]:
                continue  # each reversal pair once
            pairs += 1
            if f(order) == f(order[::-1]):
                hits.append([list(order), list(order[::-1]), f(order)])
    return {"bound": bound, "size": size, "pairs": pairs, "collisions": len(hits),
            "examples": hits[:5]}


# ---------------------------------------------------------------------------
# The block identity behind the {2,3,5,7} failure of the decoding test
# ---------------------------------------------------------------------------

def compose(p: int, words) -> tuple[Fraction, Fraction]:
    """(c, B) with G_w1 o G_w2 o ... (y) = c + B y."""
    c, slope = Fraction(0), Fraction(1)
    for tau in words:
        c0, s0 = type_map(p, tuple(tau))
        c, slope = c + slope * c0, slope * s0
    return c, slope


def run_path(aut, state, words):
    for tau in words:
        nxt = [t for w, t in aut.transitions[state] if w == tuple(tau)]
        if not nxt:
            return None
        state = nxt[0]
    return state


def block_types(primes, count: int) -> list[tuple[int, ...]]:
    """Types of the first `count` blocks (p^a, p^(a+1)], incrementally."""
    ordered = sorted(primes)
    p, others = ordered[0], ordered[1:]
    nxt = {q: q for q in others}
    out, high = [], p
    for _ in range(count):
        inside = []
        for q in others:
            if nxt[q] < high:
                inside.append((nxt[q], q))
                nxt[q] *= q
        out.append(tuple(q for _, q in sorted(inside)))
        high *= p
    return out


def identity_2357(blocks: int) -> dict:
    primes = (2, 3, 5, 7)
    aut = build_automaton(primes)
    w1 = [(5, 7, 3), (), (3,), (5, 7)]
    w2 = [(7,), (3, 5), (3,), (5, 7)]
    two1, two2 = compose(2, w1[:2]), compose(2, w2[:2])
    four1, four2 = compose(2, w1), compose(2, w2)
    starts = []
    for state in aut.states:
        e1, e2 = run_path(aut, state, w1), run_path(aut, state, w2)
        if e1 is not None and e2 is not None:
            starts.append({"start": list(state), "end_w1": list(e1), "end_w2": list(e2)})
    types = block_types(primes, blocks)
    count1 = sum(1 for a in range(blocks - 3) if [types[a + i] for i in range(4)] == w1)
    count2 = sum(1 for a in range(blocks - 3) if [types[a + i] for i in range(4)] == w2)
    return {
        "two_block_maps_equal": two1 == two2,
        "two_block_map": f"({two1[0] / two1[1]} + y)/{1 / two1[1]}",
        "four_block_maps_equal": four1 == four2,
        "common_start_states": starts,
        "same_end_state_everywhere": all(r["end_w1"] == r["end_w2"] for r in starts),
        "letter_collision": [f((5, 7, 3, 2)), f((7, 2, 3, 5))],
        "actual_blocks_scanned": blocks,
        "occurrences_w1": count1,
        "occurrences_w2": count2,
    }


# ---------------------------------------------------------------------------
# Two tails at a return: exact correspondence of crossings and chains
# ---------------------------------------------------------------------------

def future(start: int, primes, count: int) -> list[tuple[int, int]]:
    """The next `count` prime powers above `start`, as (power, prime)."""
    heap = []
    for q in primes:
        e = max(1, int(start.bit_length() / math.log2(q)) - 2)
        v = q ** e
        while v > start and e > 1:  # the estimate is below the target in practice
            e -= 1
            v //= q
        while v <= start:
            v *= q
        heap.append((v, q))
    heapq.heapify(heap)
    out = []
    while len(out) < count:
        v, q = heapq.heappop(heap)
        out.append((v, q))
        heapq.heappush(heap, (v * q, q))
    return out


def best_return(primes, p: int, limit: int) -> int:
    """The n < limit minimising max_q |n log p - round(n log p/log q) log q|."""
    logs = {q: math.log(q) for q in primes}
    best = None
    for n in range(1, limit):
        x = n * logs[p]
        e = max(abs(x - round(x / logs[q]) * logs[q]) for q in primes)
        if best is None or e < best[0]:
            best = (e, n)
    return best[1]


def chain_simulation(primes, p: int, a0: int, limit: int, length: int, n: int | None = None) -> dict:
    lg = {q: Decimal(q).ln() for q in primes}
    if n is None:
        n = best_return(primes, p, limit)
    m = {q: int((Decimal(n) * lg[p] / lg[q]).to_integral_value()) for q in primes}
    delta = {q: n * lg[p] - m[q] * lg[q] for q in primes}
    eps = max(abs(d) for d in delta.values())
    tk = p ** a0
    log_tk = Decimal(tk).ln()
    u = future(tk, primes, length)
    v = future(tk * p ** n, primes, length + 50)
    beta = min(min(log_tk % lg[q], lg[q] - log_tk % lg[q]) for q in primes if q != p)
    assert eps < beta and 2 * eps * len(primes) < Decimal(2).ln()
    # exact correspondence of crossings: q^j -> q^(j + m_q)
    image = [(power * q ** m[q], q) for power, q in u]
    assert sorted(image)[:length - 20] == v[:length - 20], "crossing correspondence fails"
    times = [Decimal(power).ln() - log_tk for power, _ in u]
    chains, current, margin = [], [0], Decimal(10)
    for i in range(1, length):
        gap = times[i] - times[i - 1]
        margin = min(margin, abs(gap - 2 * eps))
        if gap > 2 * eps:
            chains.append(current)
            current = [i]
        else:
            current.append(i)
    position = {power: i for i, (power, _) in enumerate(v)}
    sizes: dict[int, int] = {}
    rearranged = []
    for chain in chains:  # the last, possibly unfinished, chain is dropped
        places = sorted(position[image[i][0]] for i in chain)
        assert places == list(range(places[0], places[0] + len(chain))) and places[0] == chain[0]
        before = [u[i][1] for i in chain]
        after = [v[j][1] for j in places]
        assert len(set(before)) == len(before) <= len(primes)
        sizes[len(chain)] = sizes.get(len(chain), 0) + 1
        if before != after:
            rearranged.append([chain[0], before, after, f(before) - f(after)])
    return {
        "primes": list(primes), "p": p, "a0": a0, "n": n,
        "epsilon": f"{float(eps):.3e}", "beta": f"{float(beta):.3f}",
        "least_margin_to_cut": f"{float(margin):.1e}",
        "crossings": length, "chain_sizes": {str(k): sizes[k] for k in sorted(sizes)},
        "rearranged_chains": len(rearranged),
        "rearranged_transpositions": sum(1 for r in rearranged if len(r[1]) == 2),
        "f_collisions": sum(1 for r in rearranged if r[3] == 0),
        "first_rearranged": rearranged[:3],
    }


def close_pair_2357(n: int, a0: int, length: int) -> dict:
    """Exact x_k - x_m for t_k = 2^a0, t_m = 2^(a0+n) over {2,3,5,7}."""
    primes = (2, 3, 5, 7)
    u = [q for _, q in future(2 ** a0, primes, length)]
    v = [q for _, q in future(2 ** (a0 + n), primes, length)]
    # minimal segments on which the two words are rearrangements of each other
    segments, i = [], 0
    while i < length:
        count: dict[int, int] = {}
        j = i
        while j < length:
            count[u[j]] = count.get(u[j], 0) + 1
            count[v[j]] = count.get(v[j], 0) - 1
            j += 1
            if all(c == 0 for c in count.values()):
                break
        else:
            break
        segments.append((i, tuple(u[i:j]), tuple(v[i:j])))
        i = j
    moved = [(i, s, t) for i, s, t in segments if s != t]
    first, s, t = moved[0]
    cut = first + 60
    difference = value(u[:cut]) - value(v[:cut])
    error = Fraction(1, math.prod(u[:cut])) + Fraction(1, math.prod(v[:cut]))
    predicted = Fraction(abs(f(s) - f(t)), math.prod(u[:first]) * math.prod(s))

    def log10(x: Fraction) -> float:
        return math.log10(x.numerator) - math.log10(x.denominator)

    return {
        "n": n, "a0": a0, "letters": length,
        "rearranged_segments": len(moved),
        "segment_sizes": sorted({len(s) for _, s, _ in moved}),
        "f_collisions": sum(1 for _, s, t in moved if f(s) == f(t)),
        "first_rearranged": [first, list(s), list(t), f(s), f(t)],
        "difference_exceeds_truncation_error": abs(difference) > error,
        "log10_difference": round(log10(abs(difference)), 4),
        "log10_predicted_leading_term": round(log10(predicted), 4),
    }


# ---------------------------------------------------------------------------
# Line arrangements on the torus (Lemma 4)
# ---------------------------------------------------------------------------

def arrangement(vectors) -> tuple[int, int]:
    """(sum over vertices of k_v - 3, number of vertices with k_v = 2)."""
    points = set()
    for a, b in combinations(vectors, 2):
        det = a[0] * b[1] - a[1] * b[0]
        for z1 in range(abs(det)):
            for z2 in range(abs(det)):
                points.add((Fraction(z1 * b[1] - z2 * a[1], det) % 1,
                            Fraction(a[0] * z2 - b[0] * z1, det) % 1))
    ks = [sum((g[0] * x + g[1] * y).denominator == 1 for g in vectors) for x, y in points]
    return sum(k - 3 for k in ks), ks.count(2)


def euler_check(trials: int, bound: int, seed: int = 3) -> dict:
    rng = random.Random(seed)
    worst = None
    for _ in range(trials):
        r = rng.randint(4, 6)
        vectors: list[tuple[int, int]] = []
        while len(vectors) < r:
            g = (rng.randint(-bound, bound), rng.randint(-bound, bound))
            if g != (0, 0) and all(g[0] * h[1] - g[1] * h[0] for h in vectors):
                if rng.random() < 0.3:
                    g = (2 * g[0], 2 * g[1])  # non-primitive: parallel circles
                vectors.append(g)
        total, twos = arrangement(vectors)
        assert total <= 0 and twos >= 1, vectors
        worst = total if worst is None else max(worst, total)
    tight = arrangement([(1, 0), (0, 1), (1, 1), (1, -1)])
    return {"trials": trials, "entry_bound": bound, "max_sum_k_minus_3": worst,
            "square_with_diagonals": {"sum_k_minus_3": tight[0], "two_line_vertices": tight[1]}}


# ---------------------------------------------------------------------------
# The single-prime sub-sums E_p of the catalogue series
# ---------------------------------------------------------------------------

def height(primes, x: int) -> int:
    """H_P(x) = prod_q q^floor(log_q x), by integer comparison."""
    out = 1
    for q in primes:
        v = q
        while v <= x:
            v *= q
            out *= q
    return out


def value_p(word, p: int) -> Fraction:
    """V_p = sum over the positions i with word_i = p of 1/(word_1 ... word_i)."""
    total, product = Fraction(0), 1
    for letter in word:
        product *= letter
        if letter == p:
            total += Fraction(1, product)
    return total


def f_p(word, p: int) -> int:
    """sum over the positions t with word_t = p of word_(t+1) ... word_n."""
    total, product = 0, 1
    for letter in reversed(word):
        if letter == p:
            total += product
        product *= letter
    return total


def ep_identities(seed: int = 5, trials: int = 2000, box: int = 16) -> dict:
    rng = random.Random(seed)
    letters = [2, 3, 5, 7, 11]
    for _ in range(trials):  # V_p(s u) = (f_p(s) + V_p(u))/Pi(s)
        s = [rng.choice(letters) for _ in range(rng.randint(1, 6))]
        u = [rng.choice(letters) for _ in range(rng.randint(0, 8))]
        p = rng.choice(letters)
        assert value_p(s + u, p) == (f_p(s, p) + value_p(u, p)) / math.prod(s)
    followers = 0
    for chosen in combinations(primes_upto(23), 4):
        for p in chosen:
            seen: dict[int, frozenset] = {}
            for order in permutations(chosen):
                after = frozenset(order[order.index(p) + 1:])
                v = f_p(order, p)
                assert v == math.prod(after)
                assert seen.setdefault(v, after) == after
                followers += 1
    pairs = [(2, 3), (2, 5), (3, 5), (3, 7), (5, 7)]
    for p, q in pairs:  # R_{p,q} = E_p E_q term by term
        P = (p, q)
        for i in range(30):
            for j in range(30):
                assert height(P, p ** i * q ** j) == height(P, p ** i) * height(P, q ** j)
    carries: dict[str, list[int]] = {}
    for P in ((2, 3, 5), (2, 3, 7), (3, 5, 7)):
        seen = set()
        for e in [(i, j, k) for i in range(box) for j in range(box) for k in range(box)]:
            n = math.prod(q ** a for q, a in zip(P, e))
            split = math.prod(height(P, q ** a) for q, a in zip(P, e))
            ratio, rest = divmod(height(P, n), split)
            assert rest == 0
            for q in P:  # q^kappa_q with kappa_q in {0,1}
                kappa = 0
                while ratio % q == 0:
                    ratio //= q
                    kappa += 1
                seen.add(kappa)
            assert ratio == 1
        carries[",".join(map(str, P))] = sorted(seen)
    P4 = (2, 3, 5, 7)
    seen4 = set()
    for e in [(i, j, k, m) for i in range(8) for j in range(8) for k in range(8) for m in range(8)]:
        n = math.prod(q ** a for q, a in zip(P4, e))
        ratio = height(P4, n) // math.prod(height(P4, q ** a) for q, a in zip(P4, e))
        for q in P4:
            kappa = 0
            while ratio % q == 0:
                ratio //= q
                kappa += 1
            seen4.add(kappa)
    # D_P = sum_q E_q - (|P| - 1), truncated at the prime powers up to X
    X = 10 ** 12
    for P in ((2, 3), (2, 3, 5), (2, 3, 5, 7)):
        powers = sorted((q ** a, q) for q in P for a in range(1, 60) if q ** a <= X)
        D = 1 + sum(Fraction(1, height(P, t)) for t, _ in powers)
        E = {q: 1 + sum(Fraction(1, height(P, t)) for t, r in powers if r == q) for q in P}
        assert D == sum(E.values()) - (len(P) - 1)
    return {"shift_identity_checks": trials, "follower_orderings": followers,
            "two_prime_product_pairs": len(pairs), "three_prime_carry_values": carries,
            "four_prime_carry_values": sorted(seen4)}


def ep_close_pair(primes, p: int, a0: int, n: int, length: int) -> dict:
    """Exact y_k - y_m for t_k = p^a0 and t_m = p^(a0+n)."""
    u = [q for _, q in future(p ** a0, primes, length)]
    v = [q for _, q in future(p ** (a0 + n), primes, length)]
    first = next(i for i in range(length) if u[i] != v[i])
    j = first
    while sorted(u[first:j + 1]) != sorted(v[first:j + 1]):
        j += 1
    chain, image = u[first:j + 1], v[first:j + 1]
    difference = value_p(u, p) - value_p(v, p)
    error = Fraction(2, (p - 1) * min(math.prod(u), math.prod(v)))
    return {
        "primes": list(primes), "p": p, "a0": a0, "n": n, "letters": length,
        "first_rearranged": [first, chain, image, f_p(chain, p), f_p(image, p)],
        "difference_exceeds_truncation_error": abs(difference) > error,
        "log10_difference": round(math.log10(abs(difference.numerator))
                                  - math.log10(difference.denominator), 3),
    }


# ---------------------------------------------------------------------------

def fast_report() -> dict:
    return {
        "identity": check_identity(300, 500),
        "injectivity": [injectivity(60, 2), injectivity(60, 3), injectivity(60, 4)],
        "reversal": reversal_collisions(53, 4),
        "identity2357": identity_2357(20000),
        "chains": [chain_simulation((2, 3, 5), 3, 30, 20000, 1500)],
        "close_pair": close_pair_2357(2547450, 60, 1200),
        "euler": euler_check(40, 4),
        "ep_identities": ep_identities(trials=300, box=8),
        "ep_close_pair": ep_close_pair((2, 3, 5), 2, 20, 65, 300),
    }


def full_report() -> dict:
    return {
        "identity": check_identity(),
        "injectivity": [injectivity(200, 2), injectivity(200, 3), injectivity(60, 4)],
        "reversal": reversal_collisions(100, 4),
        "identity2357": identity_2357(20000),
        "chains": [
            chain_simulation((2, 3), 2, 40, 2000, 3000),
            chain_simulation((2, 3, 5), 3, 30, 20000, 3000),
            chain_simulation((2, 3, 5, 7), 2, 60, 300000, 4000),
            chain_simulation((3, 5, 7, 11), 5, 20, 300000, 4000),
        ],
        "close_pair": {**close_pair_2357(2547450, 60, 4000),
                       "return_scan_limit": 3000000,
                       "best_return_found": best_return((2, 3, 5, 7), 2, 3000000)},
        "euler": euler_check(400, 6),
        "ep_identities": ep_identities(),
        "ep_close_pair": ep_close_pair((2, 3, 5), 2, 20, 65, 300),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--full", action="store_true",
                        help="run every check at the sizes the papers state (a few minutes)")
    parser.add_argument("--output", type=Path, help="write the JSON receipt here")
    args = parser.parse_args(argv)
    started = time.time()
    report = full_report() if args.full else fast_report()
    report["run"] = {
        "program": Path(__file__).name,
        "program_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "library_sha256": hashlib.sha256((HERE / "certificate.py").read_bytes()).hexdigest(),
        "mode": "full" if args.full else "fast",
        "python": platform.python_version(),
        "seconds": round(time.time() - started, 2),
    }
    text = json.dumps(report, indent=1, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
