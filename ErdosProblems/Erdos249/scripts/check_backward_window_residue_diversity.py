#!/usr/bin/env python3
"""Backward-window residue diversity of the binary totient series (Erdos 249).

Objects (canonical coordinates):

    P_n = sum_{j=1}^n 2^(n-j) phi(j),   R_n = 2^n S - P_n,   R_n = 2 R_(n-1) - phi(n)

For N >= 16 put L_N = 2*ceil(log2 N), M_N = 2^(L_N) and, for N <= n < 2N,

    B_N(n) = P_n mod M_N = (sum_{j=0}^{L_N-1} 2^j phi(n-j)) mod 2^(L_N)

which is a function of a backward window of L_N consecutive totient values only.
D_N counts the distinct B_N(n) on [N,2N); E_N counts ordered coinciding pairs
(diagonal included).  This probe recomputes the (D_N, E_N) table independently,
extends it past the range reported in the batch, lists every actual collision
pair with its exact un-reduced window sums, and certifies the two exact
one-step doubling-defect values

    Delta_n = R_(2n) - 2 R_n = (4^n - 2^(n+1)) S - P_(2n) + 2 P_n .

Nothing here is promoted to a cofinal statement; these are finite exact
computations against explicitly bracketed S.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction


def totient_sieve(limit: int) -> list[int]:
    """phi(0..limit) by a linear-factor sieve using pure Python ints."""
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:  # p is prime
            for m in range(p, limit + 1, p):
                phi[m] -= phi[m] // p
    return phi


def prefix_blocks(phi: list[int], upto: int) -> list[int]:
    """P_0..P_upto as exact integers."""
    out = [0] * (upto + 1)
    acc = 0
    for n in range(1, upto + 1):
        acc = 2 * acc + phi[n]
        out[n] = acc
    return out


def window_sum(phi: list[int], n: int, length: int) -> int:
    """Un-reduced sum_{j=0}^{length-1} 2^j phi(n-j)."""
    total = 0
    for j in range(length):
        total += (1 << j) * phi[n - j]
    return total


def diversity_row(phi: list[int], j: int) -> dict:
    n_block = 1 << j
    width = 2 * j  # L_N = 2*ceil(log2 N) with N = 2^j
    modulus = 1 << width
    start = max(1, n_block - 2 * width)
    acc = 0
    for n in range(start, n_block):
        acc = (2 * acc + phi[n]) % modulus
    fibres: dict[int, list[int]] = {}
    for n in range(n_block, 2 * n_block):
        acc = (2 * acc + phi[n]) % modulus
        fibres.setdefault(acc, []).append(n)
    distinct = len(fibres)
    pairs = sum(len(g) * len(g) for g in fibres.values())
    collisions = sorted(g for g in fibres.values() if len(g) > 1)
    odd_distinct = len({r for r, g in fibres.items() if any(n % 2 for n in g)})
    odd_indices = sum(1 for n in range(n_block, 2 * n_block) if n % 2)
    odd_injective = all(
        sum(1 for n in g if n % 2) <= 1 for g in fibres.values()
    )
    cross_class_only = all(
        len({(n & -n).bit_length() for n in g}) == len(g) for g in collisions
    )
    return {
        "j": j,
        "N": n_block,
        "L_N": width,
        "D_N": distinct,
        "E_N": pairs,
        "N_minus_D_N": n_block - distinct,
        "D_N_over_N": float(Fraction(distinct, n_block)),
        "odd_index_count": odd_indices,
        "odd_restricted_distinct": odd_distinct,
        "odd_restriction_injective": odd_injective,
        "collisions_are_cross_v2_class_only": cross_class_only,
        "collision_index_groups": collisions,
        "collision_certificates": [
            {
                "indices": g,
                "window_sums": [window_sum(phi, n, width) for n in g],
                "common_residue": window_sum(phi, g[0], width) % modulus,
                "modulus": modulus,
            }
            for g in collisions
        ],
    }


def delta_certificates(phi: list[int], blocks: list[int], bits: int,
                       max_n: int) -> dict:
    """Delta_n = alpha_n S + beta_n with a rigorous rational bracket for S."""
    s_lo = Fraction(blocks[bits], 1 << bits)
    s_hi = s_lo + Fraction(bits + 2, 1 << bits)
    rows = []
    for n in range(1, max_n + 1):
        alpha = (1 << (2 * n)) - (1 << (n + 1))
        beta = -blocks[2 * n] + 2 * blocks[n]
        lo = alpha * s_lo + beta
        hi = alpha * s_hi + beta
        sign = "positive" if lo > 0 else ("negative" if hi < 0 else "undecided")
        rows.append(
            {
                "n": n,
                "alpha": alpha,
                "beta": beta,
                "lower_bound": str(lo),
                "upper_bound": str(hi),
                "sign": sign,
            }
        )
    coarse_lo = Fraction(blocks[13], 1 << 13)
    return {
        "bracket_bits": bits,
        "S_lower": str(s_lo),
        "S_upper": str(s_hi),
        "rows": rows,
        "delta_1_exact": rows[0]["beta"] if rows[0]["alpha"] == 0 else None,
        "delta_5_form": "960*S - 1312",
        "delta_5_coarse_bound_from_13_term_prefix": str(
            960 * coarse_lo - 1312
        ),
        "prefix_13_value": str(coarse_lo),
        "sign_change_present": any(r["sign"] == "negative" for r in rows)
        and any(r["sign"] == "positive" for r in rows),
    }


def entropy_profile(phi: list[int], j: int) -> dict:
    """Where the diversity of B_N actually lives.

    (a) window_injectivity: smallest t for which the exact backward word
        (phi(n-t+1), ..., phi(n)) already separates every n in [N,2N).
    (b) bit_budget: D_N at every truncated modulus 2^s, s = 1..L_N, i.e. how
        many low bits of P_n are needed before the residues separate.
    (c) doubling_classes: the same counts split by v_2(n), the class on which
        the exact doubling law phi(2m) = 2 phi(m) (m even) acts.
    """
    n_block = 1 << j
    width = 2 * j
    modulus = 1 << width
    idx = list(range(n_block, 2 * n_block))

    labels = {n: 0 for n in idx}
    injective_at = None
    inj_rows = []
    for t in range(1, width + 1):
        refined: dict[tuple[int, int], int] = {}
        new_labels = {}
        for n in idx:
            key = (labels[n], phi[n - t + 1])
            if key not in refined:
                refined[key] = len(refined)
            new_labels[n] = refined[key]
        labels = new_labels
        inj_rows.append({"t": t, "distinct_words": len(refined)})
        if injective_at is None and len(refined) == n_block:
            injective_at = t
    start = max(1, n_block - 2 * width)
    acc = 0
    for n in range(start, n_block):
        acc = (2 * acc + phi[n]) % modulus
    residues = []
    for n in idx:
        acc = (2 * acc + phi[n]) % modulus
        residues.append(acc)
    budget = []
    for s in range(1, width + 1):
        mask = (1 << s) - 1
        budget.append(
            {
                "s": s,
                "D_N_at_2^s": len({r & mask for r in residues}),
                "capacity_min(N, 2^s)": min(n_block, 1 << s),
            }
        )
    by_v2: dict[int, set] = {}
    for n, r in zip(idx, residues):
        v2 = (n & -n).bit_length() - 1
        by_v2.setdefault(v2, set()).add(r)
    counts = {}
    for n in idx:
        v2 = (n & -n).bit_length() - 1
        counts[v2] = counts.get(v2, 0) + 1
    return {
        "j": j,
        "N": n_block,
        "L_N": width,
        "exact_word_injective_at_length": injective_at,
        "word_distinct_counts": inj_rows,
        "bit_budget": budget,
        "doubling_class_diversity": [
            {"v2": v2, "indices": counts[v2], "distinct_residues": len(s_)}
            for v2, s_ in sorted(by_v2.items())
        ],
    }


def build_payload(max_j: int, bracket_bits: int, max_delta_n: int) -> dict:
    limit = (1 << (max_j + 1)) + 4
    limit = max(limit, 2 * max_delta_n + 4, bracket_bits + 4)
    phi = totient_sieve(limit)
    blocks = prefix_blocks(phi, max(bracket_bits, 2 * max_delta_n))
    rows = [diversity_row(phi, j) for j in range(4, max_j + 1)]
    return {
        "probe": "backward_window_residue_diversity",
        "definitions": {
            "L_N": "2*ceil(log2 N)",
            "B_N(n)": "P_n mod 2^(L_N)",
            "D_N": "#{B_N(n) : N <= n < 2N}",
            "E_N": "#{(m,n) in [N,2N)^2 : B_N(m) = B_N(n)} (ordered, diagonal in)",
        },
        "max_j": max_j,
        "rows": rows,
        "entropy_profile": entropy_profile(phi, min(max_j, 16)),
        "delta": delta_certificates(phi, blocks, bracket_bits, max_delta_n),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-j", type=int, default=20)
    parser.add_argument("--bracket-bits", type=int, default=400)
    parser.add_argument("--max-delta-n", type=int, default=40)
    parser.add_argument(
        "--quick",
        action="store_true",
        help="deterministic reduced range (max-j 16, 60 bracket bits)",
    )
    args = parser.parse_args()
    if args.quick:
        args.max_j = 16
        args.bracket_bits = 200
        args.max_delta_n = 20
    if args.max_j < 4:
        parser.error("max-j must be at least 4")
    print(json.dumps(build_payload(args.max_j, args.bracket_bits,
                                   args.max_delta_n), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
