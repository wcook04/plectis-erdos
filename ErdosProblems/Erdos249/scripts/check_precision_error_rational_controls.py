#!/usr/bin/env python3
"""Finite instances of the two 2026-09-05 sparse rational controls for Erdős #249.

Both constructions perturb ``phi`` on a sparse even support, keep every odd
totient value, and have a *rational* binary series.  They sit at two different
points of the same precision--error frontier

        2^{k(n)} | delta(n)  and  delta(n) != 0   ==>   2^{k(n)} <= |delta(n)|,

which this checker verifies pointwise on the constructed prefixes.

``r01`` (Theorem 1).  Quantum ``D(n) = L(n) 2^{k_eps(n)}`` with
``t = floor(log2 n)``, ``b = ceil(log2(t+1))``, ``h = ceil(log2(b+1))``,
``k_eps = t - ceil((1+eps) h)``, ``L(n) = j(n)!`` where
``j(n) = max{j >= 2 : j! <= eps h(n)/4}``; support ``n_{i+1} =`` first multiple
of ``L(n_i)`` above ``n_i``; greedy digits ``d_i = ceil(x_{i-1}/w_i) - 1``.
High 2-adic precision, error ``O(n/(loglog n)^{1+eps/2})``.

``r02`` (Theorem 6).  Quantum ``b_j`` (smooth, growing), amplitude
``A_j = b_j 2^{Q_j}``, gap ``Q_j``, digits ``e_i`` with ``|e_i| <= 2^{Q_j}``,
covering condition ``T_{i+1} >= w_i``.  Tiny error, low 2-adic precision, and
eventual congruence modulo every fixed integer.

Effectivity note recorded in the payload: r01's threshold ``N_m`` for
"``m | delta(n)`` eventually" satisfies ``N_m >= 2^(2^(2^(4 m!/eps)))`` because
``j(n) >= m`` requires ``h(n) = ceil(log2(ceil(log2(floor(log2 n)+1))+1)) >=
4 m!/eps``.  r02's threshold is a single exponential in ``Q_m``.  Only the
``m = 2`` (r01) and ``m <= 4`` (r02, reduced gap) layers are computationally
reachable; the checker states which layer it actually certified.

The r02 instance is run with a REDUCED constant gap ``Q`` (support ``Q N``).  The faithful gap ``Q_j = 2 prod_{|s|<=j} ell_{j,s}`` forces
``n >~ 4^{Q_j}``, so density-zero support and near-prime agreement are not
computationally reachable; those two properties are proof-only here and the
payload says so.

Run: ``./repo-python <this file> --quick``
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction


# --------------------------------------------------------------------------


def totient_sieve(limit: int) -> list[int]:
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for k in range(p, limit + 1, p):
                phi[k] -= phi[k] // p
    return phi


def prefix_numerator(phi: list[int], upto: int, modulus: int | None = None) -> int:
    """Integer N with sum_{n<=upto} a(n) 2^-n = N / 2^upto."""
    acc = 0
    for n in range(1, upto + 1):
        v = phi[n] if modulus is None else phi[n] % modulus
        acc = acc * 2 + v
    return acc


def tail_bracket(phi: list[int], lo_index: int, hi_index: int) -> tuple[Fraction, Fraction]:
    """[lo, hi] containing sum_{n > lo_index} phi(n) 2^-n exactly.

    Uses 0 < sum_{n>N} phi(n) 2^-n <= sum_{n>N} (n-1) 2^-n = (N+1) 2^-N.
    """
    acc = 0
    for n in range(lo_index + 1, hi_index + 1):
        acc = acc * 2 + phi[n]
    lo = Fraction(acc, 1 << (hi_index - lo_index))
    lo = lo / (1 << lo_index)
    hi = lo + Fraction(hi_index + 1, 1 << hi_index)
    return lo, hi


def t_of(n: int) -> int:
    return n.bit_length() - 1


def ceil_log2(x: int) -> int:
    if x <= 1:
        return 0
    return (x - 1).bit_length()


def scale_functions(n: int) -> tuple[int, int, int]:
    t = t_of(n)
    b = ceil_log2(t + 1)
    h = ceil_log2(b + 1)
    return t, b, h


# --------------------------------------------------------------------------
# r01 Theorem 1
# --------------------------------------------------------------------------


def r01_parameters(n: int, eps: Fraction) -> dict:
    """t, b, h, k_eps(n) = t - ceil((1+eps)h), j(n) = max{j>=2 : j! <= eps h/4}."""
    t, b, h = scale_functions(n)
    val = (1 + eps) * h
    ceil_val = -((-val.numerator) // val.denominator)
    k = t - ceil_val
    cap = eps * Fraction(h) / 4
    j = 0
    jj = 2
    f = 2
    while Fraction(f) <= cap:
        j = jj
        jj += 1
        f *= jj
    L = math.factorial(j) if j >= 2 else 0
    return {"t": t, "b": b, "h": h, "k_eps": k, "j": j, "L": L}


def build_r01_instance(phi: list[int], eps: Fraction, n0: int, n_star: int,
                       steps: int, bracket_hi: int) -> dict:
    p0 = r01_parameters(n0, eps)
    if p0["L"] < 2 or p0["k_eps"] < 1:
        return {"status": "parameters_out_of_range", "params_at_n0": p0}

    # r = exact dyadic prefix of S; x = S - r, bracketed.
    D0 = p0["L"] * (1 << p0["k_eps"])
    w0 = Fraction(D0, 1 << n0)
    # smallest prefix N_r with (N_r+1) 2^-N_r < w0
    n_r = n0
    while Fraction(n_r + 1, 1 << n_r) >= w0:
        n_r += 1
    x_lo, x_hi = tail_bracket(phi, n_r, bracket_hi)
    assert x_hi < w0, "bracket must fit under w_0"

    support = []
    n = n0
    for _ in range(steps + 1):
        support.append(n)
        pr = r01_parameters(n, eps)
        if pr["L"] < 2:
            break
        L = pr["L"]
        n = L * (n // L + 1)
    rows = []
    lo, hi = x_lo, x_hi
    certified = 0
    prev_D = None
    prev_n = None
    for idx in range(1, len(support)):
        ni = support[idx]
        pr = r01_parameters(ni, eps)
        Di = pr["L"] * (1 << pr["k_eps"])
        wi = Fraction(Di, 1 << ni)
        d_lo = -((-(lo / wi).numerator) // (lo / wi).denominator) - 1
        r_hi = hi / wi
        d_hi = -((-r_hi.numerator) // r_hi.denominator) - 1
        if d_lo != d_hi:
            break
        d = d_lo
        certified += 1
        delta = d * Di
        a = phi[ni] - delta
        lo = lo - d * wi
        hi = hi - d * wi
        row = {
            "i": idx,
            "n": ni,
            "t": pr["t"], "b": pr["b"], "h": pr["h"],
            "k_eps": pr["k_eps"], "L": pr["L"], "D": Di,
            "d": d, "delta": delta, "phi": phi[ni], "a": a,
            "even": ni % 2 == 0,
            "quantum_divides_delta": delta % Di == 0,
            "two_adic_precision_ok": delta % (1 << pr["k_eps"]) == 0,
            "frontier_ok": (delta == 0) or ((1 << pr["k_eps"]) <= abs(delta)),
            "positivity_ok": 1 <= a <= phi[ni],
            "capacity_ok": (prev_D is None) or (delta < prev_D * (1 << (ni - prev_n))),
        }
        # (28): delta <= 2^{1+eps/2} n / (b+1)^{1+eps/2}
        bound28 = (Fraction(2) ** float(1 + eps / 2)) * ni / ((pr["b"] + 1) ** float(1 + eps / 2))
        row["bound_28"] = float(bound28)
        row["bound_28_ok"] = delta <= bound28
        rows.append(row)
        prev_D, prev_n = Di, ni

    residual_lo, residual_hi = lo, hi
    last = rows[-1] if rows else None
    tail_ok = (last is not None) and (0 < residual_lo) and (
        residual_hi <= Fraction(last["D"], 1 << last["n"])
    )
    nonzero = [r for r in rows if r["delta"] != 0]
    # effectivity: threshold for j(n) >= m
    thresholds = {}
    for m in (2, 3, 4):
        need_h = 4 * math.factorial(m) / float(eps)
        thresholds[str(m)] = {
            "required_h": need_h,
            "required_n_log2_log2_log2_at_least": need_h,
        }
    return {
        "status": "ok",
        "eps": [eps.numerator, eps.denominator],
        "n0": n0, "N_star": n_star, "r_prefix_length": n_r,
        "bracket_hi": bracket_hi,
        "certified_steps": certified,
        "support_head": support[:8],
        "support_tail": support[max(0, len(support) - 4):],
        "rows_head": rows[:6],
        "nonzero_delta_count": len(nonzero),
        "nonzero_delta_values": sorted({r["delta"] for r in nonzero}),
        "all_positivity_ok": all(r["positivity_ok"] for r in rows),
        "all_two_adic_ok": all(r["two_adic_precision_ok"] for r in rows),
        "all_frontier_ok": all(r["frontier_ok"] for r in rows),
        "all_capacity_ok": all(r["capacity_ok"] for r in rows),
        "all_bound28_ok": all(r["bound_28_ok"] for r in rows),
        "all_support_even": all(r["even"] for r in rows),
        "support_above_N_star": all(r["n"] > n_star for r in rows),
        "residual_within_last_weight": tail_ok,
        "congruence_layer_certified_m": [1, 2],
        "congruence_layer_reason": "j(n)=2 at this scale, so L(n)=2 and only m|2 is forced",
        "m_thresholds": thresholds,
    }


# --------------------------------------------------------------------------
# r02 Theorem 6 (reduced constant gap)
# --------------------------------------------------------------------------


def build_r02_instance(phi: list[int], gap: int, stage_quanta: list[int],
                       n_min: int, n_max: int, bracket_hi: int,
                       rho_prefix: int) -> dict:
    """Reduced r02 Theorem 6: constant gap ``gap``, stage quanta ``stage_quanta``."""
    amplitudes = [b * (1 << gap) for b in stage_quanta]
    if any(amplitudes[i] > amplitudes[i + 1] for i in range(len(amplitudes) - 1)):
        return {"status": "amplitudes_not_nondecreasing"}

    support_all = [n for n in range(gap, n_max + 1, gap) if n >= n_min]
    min_phi_from: dict[int, int] = {}
    running = None
    for n in reversed(support_all):
        running = phi[n] if running is None else min(running, phi[n])
        min_phi_from[n] = running

    thresholds: list[int] = []
    cursor = 0
    for A in amplitudes:
        while cursor < len(support_all) and min_phi_from[support_all[cursor]] < 2 * A:
            cursor += 1
        if cursor >= len(support_all):
            return {"status": "n_max_too_small_for_stage_amplitudes",
                    "amplitudes": amplitudes}
        thresholds.append(support_all[cursor])
        cursor += 1
    support = [n for n in support_all if n >= thresholds[0]]

    def stage_of(n: int) -> int:
        s = 0
        for idx, x in enumerate(thresholds):
            if n >= x:
                s = idx
        return s

    weights = [Fraction(stage_quanta[stage_of(n)], 1 << n) for n in support]
    caps = [Fraction(amplitudes[stage_of(n)], 1 << n) for n in support]
    tails = [Fraction(0)] * (len(support) + 1)
    for i in range(len(support) - 1, -1, -1):
        tails[i] = tails[i + 1] + caps[i]

    covering_failures = [i for i in range(len(support) - 1) if tails[i + 1] < weights[i]]

    # rho rational, non-dyadic offset, |rho - S| well inside [-T_1, T_1]
    s_lo, s_hi = tail_bracket(phi, 0, bracket_hi)
    n1 = support[0]
    rho = (Fraction(prefix_numerator(phi, rho_prefix), 1 << rho_prefix)
           + Fraction(amplitudes[0], 3 * (1 << n1)))
    y_lo = rho - s_hi
    y_hi = rho - s_lo
    if not (abs(y_lo) <= tails[0] and abs(y_hi) <= tails[0]):
        return {"status": "target_outside_representable_interval",
                "T1": str(tails[0]), "y_hi": str(y_hi)}

    rows = []
    lo, hi = y_lo, y_hi
    stop_reason = "support_exhausted"
    for i, n in enumerate(support):
        w = weights[i]
        Dcap = 1 << gap
        Tnext = tails[i + 1]
        if hi - lo > 2 * Tnext:
            stop_reason = "bracket_width_exceeds_remaining_capacity"
            break
        centre = (lo + hi) / 2 / w
        guess = round(centre)
        chosen = None
        for e in range(max(-Dcap, guess - 3), min(Dcap, guess + 3) + 1):
            if -Tnext <= lo - e * w and hi - e * w <= Tnext:
                chosen = e
                break
        if chosen is None:
            stop_reason = "no_admissible_digit"
            break
        s = stage_of(n)
        delta = stage_quanta[s] * chosen
        c = phi[n] + delta
        lo -= chosen * w
        hi -= chosen * w
        rows.append({
            "i": i, "n": n, "stage": s, "b": stage_quanta[s], "e": chosen,
            "delta": delta, "phi": phi[n], "c": c,
            "positivity_ok": 0 < c <= n,
            "amplitude_ok": abs(delta) <= amplitudes[s],
            "half_phi_ok": abs(delta) <= phi[n] // 2,
            "two_adic_valuation_of_delta": (delta & -delta).bit_length() - 1 if delta else None,
        })

    congruence = {}
    for m in (2, 3, 4, 6):
        first_stage = next((idx for idx, b in enumerate(stage_quanta) if b % m == 0), None)
        if first_stage is None:
            congruence[str(m)] = {"certified": False,
                                  "reason": "no stage quantum divisible by m"}
            continue
        n_from = thresholds[first_stage]
        tested = [r for r in rows if r["n"] >= n_from]
        bad = [r for r in tested if r["delta"] % m != 0]
        congruence[str(m)] = {
            "certified": bool(tested) and not bad,
            "eventually_from_index": n_from,
            "rows_tested": len(tested),
            "violations": len(bad),
        }

    max_stage_reached = max((r["stage"] for r in rows), default=-1)
    return {
        "status": "ok" if rows else "no_rows",
        "gap_Q": gap,
        "stage_quanta_b": stage_quanta,
        "stage_amplitudes_A": amplitudes,
        "stage_thresholds_X": thresholds,
        "max_stage_reached": max_stage_reached,
        "certified_support_points": len(rows),
        "certified_index_range": [rows[0]["n"], rows[-1]["n"]] if rows else None,
        "stop_reason": stop_reason,
        "support_head": support[:6],
        "covering_condition_T_next_ge_w": not covering_failures,
        "covering_failures": covering_failures[:5],
        "rows_head": rows[:6],
        "all_positivity_ok": all(r["positivity_ok"] for r in rows),
        "all_amplitude_ok": all(r["amplitude_ok"] for r in rows),
        "all_half_phi_ok": all(r["half_phi_ok"] for r in rows),
        "nonzero_delta_count": sum(1 for r in rows if r["delta"] != 0),
        "max_abs_delta": max((abs(r["delta"]) for r in rows), default=0),
        "eventual_congruence": congruence,
        "reduced_parameters_note": (
            "a constant gap Q replaces the CRT gaps Q_j; density-zero support and "
            "near-prime agreement are proof-only at this scale because the faithful "
            "construction needs n >~ 4^{Q_j}"
        ),
    }


# --------------------------------------------------------------------------


def build_payload(quick: bool) -> dict:
    if quick:
        eps = Fraction(8, 3)
        n0 = 4096
        n_star = 4000
        steps = 120
        bracket_hi = 4600
        r02_gap = 4
        r02_quanta = [2, 6, 24]
        r02_n_min = 100
        r02_n_max = 8000
        r02_bracket = 5000
        r02_rho_prefix = 4500
        sieve_limit = 8016
    else:
        eps = Fraction(8, 3)
        n0 = 4096
        n_star = 4000
        steps = 220
        bracket_hi = 5200
        r02_gap = 4
        r02_quanta = [2, 6, 24, 120, 840]
        r02_n_min = 100
        r02_n_max = 120000
        r02_bracket = 60000
        r02_rho_prefix = 58000
        sieve_limit = 120016

    phi = totient_sieve(max(sieve_limit, bracket_hi + 16))
    r01 = build_r01_instance(phi, eps, n0, n_star, steps, bracket_hi)
    r02 = build_r02_instance(phi, r02_gap, r02_quanta, r02_n_min, r02_n_max,
                             r02_bracket, r02_rho_prefix)

    ok = (
        r01.get("status") == "ok"
        and r01["all_positivity_ok"] and r01["all_two_adic_ok"]
        and r01["all_frontier_ok"] and r01["all_capacity_ok"]
        and r01["all_bound28_ok"] and r01["all_support_even"]
        and r01["support_above_N_star"] and r01["residual_within_last_weight"]
        and r01["nonzero_delta_count"] > 0
        and r02.get("status") == "ok"
        and r02["covering_condition_T_next_ge_w"]
        and r02["all_positivity_ok"] and r02["all_amplitude_ok"]
        and r02["nonzero_delta_count"] > 0
        and all(v["certified"] for v in r02["eventual_congruence"].values())
    )
    return {
        "checker": "check_precision_error_rational_controls",
        "problem": "erdos_249",
        "mode": "quick" if quick else "full",
        "r01_theorem1_instance": r01,
        "r02_theorem6_reduced_instance": r02,
        "frontier_identity": "2^{k(n)} | delta(n) and delta(n) != 0  =>  2^{k(n)} <= |delta(n)|",
        "all_checks_pass": ok,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    payload = build_payload(args.quick)
    print(json.dumps(payload, indent=2, sort_keys=True, default=str))
    return 0 if payload["all_checks_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
