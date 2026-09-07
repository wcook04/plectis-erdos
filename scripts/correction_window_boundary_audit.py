#!/usr/bin/env python3
"""Exact correction-window boundary audit for the 1/21 greedy orbit.

For I_K=[P_K+r_K-eta_K,P_K+r_K], the only possible integer in
4^K I_K is floor(4^K(P_K+r_K)).  The script uses Fraction for that candidate
and rational lower/upper enclosures for the non-rational correction tail.
No floating point decisions are made.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction


def w(n: int) -> Fraction:
    return Fraction(1, (1 << n) - 1)


def correction(n: int) -> Fraction:
    """w_n - 2^-n."""
    return Fraction(1, (1 << n) * ((1 << n) - 1))


def v2(n: int) -> int | None:
    if n == 0:
        return None
    return (abs(n) & -abs(n)).bit_length() - 1


def integer_receipt(n: int) -> object:
    if abs(n).bit_length() <= 512:
        return n
    raw = (b"-" if n < 0 else b"+") + abs(n).to_bytes(
        max(1, (abs(n).bit_length() + 7) // 8), "big"
    )
    return {"sha256": hashlib.sha256(raw).hexdigest(), "bits": abs(n).bit_length()}


def fraction_receipt(x: Fraction) -> object:
    if x.numerator.bit_length() <= 512 and x.denominator.bit_length() <= 512:
        return f"{x.numerator}/{x.denominator}"
    numerator = integer_receipt(x.numerator)
    denominator = integer_receipt(x.denominator)
    return {"numerator": numerator, "denominator": denominator}


def audit(depth: int, lookahead: int, modulus_bits: int) -> dict[str, object]:
    x = Fraction(1, 21)
    remainder = x
    prefix_numerator = 0
    crossed: list[dict[str, object]] = []
    undecided: list[int] = []
    max_valuation = -1
    max_rows: list[int] = []
    statuses = {"crossed": 0, "not_crossed": 0, "undecided": 0}

    for k in range(1, depth + 1):
        bit = remainder >= w(k)
        if bit:
            remainder -= w(k)
        prefix_numerator = 2 * prefix_numerator + int(bit)

        # U_K = 4^K(P_K+r_K) = 2^K B_K + 4^K r_K.
        upper = (1 << k) * prefix_numerator + (4**k) * remainder
        q = upper.numerator // upper.denominator
        gap = upper - q
        # In reduced form r_K=A_K/Q_K (Q_K odd), this is Euclidean division
        # of 4^K A_K by Q_K; prefix data contribute the integral 2^K B_K.
        a_k, q_k = remainder.numerator, remainder.denominator
        rho_k = ((4**k) * a_k) % q_k
        q_by_division = (1 << k) * prefix_numerator + ((4**k) * a_k - rho_k) // q_k
        assert q == q_by_division

        # eta_K is bracketed by its next `lookahead` corrections and
        # (2/3)*4^(-lookahead) after scaling by 4^K.
        eta_lower = sum((4**k) * correction(n)
                        for n in range(k + 1, k + lookahead + 1))
        eta_upper = eta_lower + Fraction(2, 3 * (4**lookahead))
        if gap <= eta_lower:
            status = "crossed"
        elif eta_upper < gap:
            status = "not_crossed"
        else:
            status = "undecided"
            undecided.append(k)
        statuses[status] += 1

        valuation = v2(q)
        if valuation is not None:
            if valuation > max_valuation:
                max_valuation, max_rows = valuation, [k]
            elif valuation == max_valuation:
                max_rows.append(k)
        if status == "crossed":
            modulus = 1 << modulus_bits
            residue_by_formula = (
                (1 << k) * prefix_numerator
                + (((4**k) * a_k - rho_k) * pow(q_k, -1, modulus))
            ) % modulus
            assert q % modulus == residue_by_formula
            crossed.append({
                "K": k,
                "selected_at_K": bit,
                "q": integer_receipt(q),
                "v2_q": valuation,
                "q_mod_2_pow_j": {"j": modulus_bits, "residue": q % modulus},
                "prefix_numerator_B_K": integer_receipt(prefix_numerator),
                "residual_A_K": integer_receipt(a_k),
                "residual_odd_Q_K": integer_receipt(q_k),
                "euclidean_remainder_rho_K": integer_receipt(rho_k),
                "scaled_gap": fraction_receipt(gap),
                "scaled_eta_lower": fraction_receipt(eta_lower),
                "scaled_eta_upper": fraction_receipt(eta_upper),
            })

    return {
        "method": "exact Fraction arithmetic; correction-tail lower sum plus rational geometric upper bound",
        "target": "1/21",
        "depth": depth,
        "lookahead": lookahead,
        "tail_bound": "4^K*(eta_K - partial_{K+1..K+L}) < 2/(3*4^L)",
        "status_counts": statuses,
        "undecided_K": undecided,
        "max_v2_q_over_all_candidates": {"valuation": max_valuation, "K": max_rows},
        "certified_crossings": crossed,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=192)
    parser.add_argument("--lookahead", type=int, default=96)
    parser.add_argument("--modulus-bits", type=int, default=32)
    args = parser.parse_args()
    if args.depth < 1 or args.lookahead < 1 or args.modulus_bits < 1:
        raise SystemExit("all arguments must be positive")
    print(json.dumps(audit(args.depth, args.lookahead, args.modulus_bits), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
