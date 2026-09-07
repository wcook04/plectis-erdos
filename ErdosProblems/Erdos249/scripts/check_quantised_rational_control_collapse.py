#!/usr/bin/env python3
"""Exact quantised rational control for Erdos 249: collapse and permanent trap.

Builds, with certified digits, a positive integral coefficient sequence c with

    c(n) = phi(n)                            (n odd, or n <= 2 m_0)
    c(2m) = phi(2m) + M_m d_m,  d_m in {-2,-1,0,1}   (m > m_0)
    sum_(n>=1) c(n) 2^(-n) = rho_D  (a dyadic rational strictly above S)

where M_m is a nondecreasing power of two of order m / log m satisfying
4 M_m <= phi(2m) and M_m <= m.  Consequences checked exactly on the built
prefix:

  * 0 < c(n) <= n-1, c = phi at every odd argument, c(2m) = phi(2m) mod M_m,
    |c(2m) - phi(2m)| <= 2 M_m = o(n), and 2-adic agreement 2^kappa(n) with
    kappa(n) = log2 n - log2 log2 n - O(1);
  * the integral carry R_n = 2^n rho_D - P_n^c is a positive integer bounded by
    n+2, which both certifies the series value and gives the rational instance;
  * the rational-collapse conclusion: V_N = #{R_n : N <= n < 2N} and
    D_N = #{P_n^c mod 2^(L_N)} both fall far below N, and the two equivalence
    relations R_m = R_n and P_m^c = P_n^c mod 2^(L_N) are literally identical
    on [N,2N) once N is large (the exact-identification step of the collapse
    theorem, tested on a genuine rational instance rather than assumed);
  * the permanent-trap conclusion for this control: with k = R_b, the signed
    endpoint error E_H = k - R_(b+H) obeys -b-H <= E_H <= b at every height and
    satisfies 4 E_H + p + phi(p+1) <= 4 + 3k at every prime p = b+H+1.

The totient row of the same collapse statistics is computed alongside for
contrast.  Nothing is promoted to a cofinal claim about phi.
"""

from __future__ import annotations

import argparse
import json


def totient_sieve(limit: int) -> list[int]:
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for m in range(p, limit + 1, p):
                phi[m] -= phi[m] // p
    return phi


def modulus(m: int) -> int:
    """Nondecreasing power of two with 4 M_m <= m / (2 + log2 m) <= phi(2m)."""
    t = m.bit_length() - 1              # floor(log2 m); 2^t <= m
    s = (2 + m.bit_length()).bit_length()  # 2^s > 2 + bit_length(m) > 2 + log2 m
    return 1 << max(0, t - 2 - s)


def build_control(phi: list[int], m0: int, m_max: int) -> dict:
    cut = m_max + 64
    bits = 2 * cut + 256
    scale_exp = bits

    blocks = [0] * (bits + 1)
    acc = 0
    for n in range(1, bits + 1):
        acc = 2 * acc + phi[n]
        blocks[n] = acc

    d_exp = 4 * m0 + 8
    rho_num_small = blocks[d_exp] + d_exp + 2      # rho_D = rho_num_small / 2^D
    rho_scaled = rho_num_small << (scale_exp - d_exp)

    s_lo = blocks[bits]
    s_hi = blocks[bits] + bits + 2

    mods = [0] * (cut + 2)
    for m in range(1, cut + 2):
        mods[m] = modulus(m)

    w = [0] * (cut + 2)
    for m in range(1, cut + 1):
        w[m] = mods[m] << (scale_exp - 2 * m)
    tail_bound = cut << (scale_exp - 2 * cut)
    w_lo = [0] * (cut + 2)
    run = 0
    for m in range(cut, m0 - 1, -1):
        w_lo[m] = run
        run += w[m] if m >= 1 else 0
    # w_lo[m] = sum_(j=m+1..cut) w_j
    x_lo = rho_scaled - s_hi
    x_hi = rho_scaled - s_lo

    digits = [0] * (cut + 2)
    certified = True
    first_uncertified = None
    start_ok = (x_lo >= -2 * (w_lo[m0] + tail_bound)) and (x_hi <= w_lo[m0])
    for m in range(m0 + 1, m_max + 1):
        wm = w[m]
        big_lo = w_lo[m]
        chosen = None
        for d in (1, 0, -1, -2):
            if x_lo - d * wm >= -2 * big_lo:
                chosen = d
                break
        if chosen is None or not (x_hi - chosen * wm <= big_lo):
            certified = False
            if first_uncertified is None:
                first_uncertified = m
            if chosen is None:
                chosen = -2
        digits[m] = chosen
        x_lo -= chosen * wm
        x_hi -= chosen * wm

    limit = 2 * m_max
    control = [0] * (limit + 1)
    for n in range(1, limit + 1):
        if n % 2 == 1 or n <= 2 * m0:
            control[n] = phi[n]
        else:
            m = n // 2
            control[n] = phi[n] + mods[m] * digits[m]
    return {
        "phi": phi,
        "c": control,
        "mods": mods,
        "digits": digits,
        "d_exp": d_exp,
        "rho_num_small": rho_num_small,
        "bits": bits,
        "certified_digits": certified,
        "first_uncertified_digit": first_uncertified,
        "start_residual_in_range": start_ok,
        "digit_histogram": {
            str(d): sum(1 for m in range(m0 + 1, m_max + 1) if digits[m] == d)
            for d in (-2, -1, 0, 1)
        },
        "limit": limit,
        "m0": m0,
        "m_max": m_max,
    }


def audit_control(built: dict) -> dict:
    phi, c, mods = built["phi"], built["c"], built["mods"]
    limit, m0 = built["limit"], built["m0"]
    fails = {
        "odd_agreement": [],
        "range_0_lt_c_le_n_minus_1": [],
        "congruence_mod_M": [],
        "abs_error_le_2M": [],
        "modulus_le_m": [],
        "four_M_le_phi_2m": [],
        "modulus_nondecreasing": [],
    }
    for n in range(1, limit + 1):
        if n % 2 == 1 and c[n] != phi[n]:
            fails["odd_agreement"].append(n)
        if not (0 < c[n] <= max(1, n - 1)):
            fails["range_0_lt_c_le_n_minus_1"].append(n)
    for m in range(m0 + 1, limit // 2 + 1):
        n = 2 * m
        if (c[n] - phi[n]) % mods[m] != 0:
            fails["congruence_mod_M"].append(m)
        if abs(c[n] - phi[n]) > 2 * mods[m]:
            fails["abs_error_le_2M"].append(m)
        if mods[m] > m:
            fails["modulus_le_m"].append(m)
        if 4 * mods[m] > phi[n]:
            fails["four_M_le_phi_2m"].append(m)
        if mods[m] < mods[m - 1]:
            fails["modulus_nondecreasing"].append(m)
    sample = [limit // 8, limit // 4, limit // 2, limit - 2]
    return {
        "failures": {k: v[:8] for k, v in fails.items()},
        "all_hold": all(not v for v in fails.values()),
        "modulus_samples": [
            {"m": s // 2, "M_m": mods[s // 2],
             "log2_M": mods[s // 2].bit_length() - 1,
             "n": s, "floor_log2_n": s.bit_length() - 1}
            for s in sample
        ],
        "max_abs_error": max(abs(c[n] - phi[n]) for n in range(1, limit + 1)),
    }


def carry_and_collapse(built: dict, seq_key: str, is_control: bool,
                       max_j: int) -> dict:
    seq = built[seq_key]
    limit = built["limit"]
    d_exp = built["d_exp"]
    rho_num_small = built["rho_num_small"]

    prefixes = [0] * (limit + 1)
    acc = 0
    for n in range(1, limit + 1):
        acc = 2 * acc + seq[n]
        prefixes[n] = acc

    carries = None
    carry_ok = None
    if is_control:
        carries = [None] * (limit + 1)
        carry_ok = True
        for n in range(d_exp, limit + 1):
            val = rho_num_small * (1 << (n - d_exp)) - prefixes[n]
            carries[n] = val
            if not (0 < val <= n + 2):
                carry_ok = False

    rows = []
    for j in range(6, max_j + 1):
        n_block = 1 << j
        if 2 * n_block > limit:
            break
        width = 2 * j
        mod = 1 << width
        res_fibres: dict[int, list[int]] = {}
        for n in range(n_block, 2 * n_block):
            res_fibres.setdefault(prefixes[n] % mod, []).append(n)
        row = {
            "j": j,
            "N": n_block,
            "L_N": width,
            "D_N": len(res_fibres),
            "D_N_over_N": len(res_fibres) / n_block,
        }
        if is_control:
            tail_fibres: dict[int, list[int]] = {}
            for n in range(n_block, 2 * n_block):
                tail_fibres.setdefault(carries[n], []).append(n)
            row["V_N"] = len(tail_fibres)
            row["V_N_over_N"] = len(tail_fibres) / n_block
            row["relations_identical"] = (
                sorted(map(sorted, res_fibres.values()))
                == sorted(map(sorted, tail_fibres.values()))
            )
            row["E_N"] = sum(len(g) ** 2 for g in res_fibres.values())
            row["E_N_over_N"] = row["E_N"] / n_block
        rows.append(row)
    out = {"rows": rows}
    if is_control:
        out["carry_positive_and_tempered"] = carry_ok
        out["series_value_error_bound"] = (
            "|rho_D - sum c(n)2^-n| <= (2*" + str(limit) + "+4) * 2^-" + str(limit)
        )
    return out


def proposition_four(built: dict, basepoints: list[int], max_height: int) -> dict:
    phi, c = built["phi"], built["c"]
    limit, d_exp = built["limit"], built["d_exp"]
    rho_num_small = built["rho_num_small"]
    prefixes = [0] * (limit + 1)
    acc = 0
    for n in range(1, limit + 1):
        acc = 2 * acc + c[n]
        prefixes[n] = acc

    def carry(n: int) -> int:
        return rho_num_small * (1 << (n - d_exp)) - prefixes[n]

    rows = []
    for b in basepoints:
        if b < d_exp or b + max_height + 2 > limit:
            continue
        k = carry(b)
        env_ok = True
        rec_ok = True
        lock_ok = True
        lock_count = 0
        worst_slack = None
        bottom_lock_ratio = None
        deepest = None
        e_prev = k - carry(b)
        for h in range(0, max_height + 1):
            e_h = k - carry(b + h)
            if not (-b - h <= e_h <= b):
                env_ok = False
            if h >= 1:
                if e_h != 2 * e_prev + c[b + h] - k:
                    rec_ok = False
            e_prev = e_h
            p = b + h + 1
            if p <= limit and phi[p] == p - 1 and p > 2:
                lock_count += 1
                slack = 4 + 3 * k - (4 * e_h + p + phi[p + 1])
                if slack < 0:
                    lock_ok = False
                if worst_slack is None or slack < worst_slack:
                    worst_slack = slack
                if deepest is None or e_h < deepest:
                    deepest = e_h
                    bottom_lock_ratio = e_h / (b + h + 1)
        rows.append(
            {
                "b": b,
                "k": k,
                "k_in_1_to_b_plus_1": 1 <= k <= b + 1,
                "max_height": max_height,
                "envelope_42_holds": env_ok,
                "recurrence_holds": rec_ok,
                "prime_successor_positions": lock_count,
                "lock_44_holds_at_every_prime": lock_ok,
                "minimum_lock_slack": worst_slack,
                "deepest_prime_position_error": deepest,
                "deepest_error_over_position": bottom_lock_ratio,
            }
        )
    return {"rows": rows}


def build_payload(m0: int, m_max: int, max_j: int, basepoints: list[int],
                  max_height: int) -> dict:
    cut = m_max + 64
    bits = 2 * cut + 256
    phi = totient_sieve(max(2 * m_max, bits) + 4)
    built = build_control(phi, m0, m_max)
    return {
        "probe": "quantised_rational_control_collapse",
        "parameters": {
            "m0": m0,
            "m_max": m_max,
            "D": built["d_exp"],
            "rho_D_numerator_over_2^D": built["rho_num_small"],
            "S_bracket_bits": built["bits"],
            "digits_certified": built["certified_digits"],
            "first_uncertified_digit": built["first_uncertified_digit"],
            "start_residual_in_range": built["start_residual_in_range"],
            "digit_histogram": built["digit_histogram"],
        },
        "control_audit": audit_control(built),
        "control_collapse": carry_and_collapse(built, "c", True, max_j),
        "totient_reference": carry_and_collapse(built, "phi", False, max_j),
        "proposition_four_on_control": proposition_four(
            built, basepoints, max_height
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--m0", type=int, default=4)
    parser.add_argument("--m-max", type=int, default=8192)
    parser.add_argument("--max-j", type=int, default=13)
    parser.add_argument("--max-height", type=int, default=2000)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    if args.quick:
        args.m_max = 2048
        args.max_j = 11
        args.max_height = 800
    basepoints = [24, 25, 40, 128, 1000]
    print(
        json.dumps(
            build_payload(args.m0, args.m_max, args.max_j, basepoints,
                          args.max_height),
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
