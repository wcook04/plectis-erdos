#!/usr/bin/env python3
"""Exact finite discriminators for the eight-return assimilation.

Integer enclosures identify actual greedy decisions; they never guess a bit.
Prime progression conclusions require the separately stated Dirichlet input.
"""
from fractions import Fraction
from math import gcd, isqrt, lcm
import argparse
import json


def greedy(p, q, horizon):
    scale = 1 << (2 * horizon + 128)
    lo, remainder = divmod(p * scale, q)
    hi = lo + bool(remainder)
    selected = set()
    loads = [0] * (horizon + 1)
    defects = [p // q]
    prefix = 0
    for n in range(1, horizon + 1):
        den = (1 << n) - 1
        if lo * den >= scale:
            wlo, r = divmod(scale, den)
            lo -= wlo + bool(r)
            hi -= wlo
            selected.add(n)
            for m in range(n, horizon + 1, n):
                loads[m] += 1
        elif hi * den >= scale:
            raise ArithmeticError(f"ambiguous decision: {p}/{q}, rank {n}")
        assert 0 <= lo <= hi
        prefix = 2 * prefix + loads[n]
        defect = p * (1 << n) // q - prefix
        assert defect >= 0
        defects.append(defect)
    return selected, defects, hi - lo


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, default=4096)
    parser.add_argument("--output")
    args = parser.parse_args()
    assert args.horizon >= 1249
    A, Q, width = greedy(4, 9, args.horizon)
    anchors = sorted(a for a in A if a <= 727 and gcd(a, 420) == 1)
    assert len(anchors) == 80
    assert len([a for a in A if a <= 727]) == 356
    columns = {M: sorted(a for a in A if M % a == 0) for M in (120, 420)}
    assert columns[120] == [2, 4, 5, 8, 12, 20, 24, 30, 40, 60, 120]
    assert columns[420] == [2, 4, 5, 7, 12, 20, 21, 28, 30, 60, 105, 210, 420]
    modulus = lcm(*anchors)
    progressions = {}
    for M, divisor_count in ((120, 16), (420, 24)):
        residue = -pow(M, -1, modulus) % modulus
        assert gcd(residue, modulus) == 1 and (M * residue + 1) % modulus == 0
        load_bound = len(columns[M]) + divisor_count
        jump_bound = -(-(len(anchors) - 2 * load_bound) // 4)
        progressions[str(M)] = {
            "residue": str(residue), "modulus": str(modulus),
            "prime_lower_cutoff": 727, "load_upper_bound": load_bound,
            "defect_jump_lower_bound": jump_bound,
            "infinite_family_authority": "ordinary proof plus Dirichlet, not finite replay",
        }
    assert progressions["120"]["defect_jump_lower_bound"] == 7
    assert progressions["420"]["defect_jump_lower_bound"] == 2
    repairs = [n for n in range(args.horizon) if Q[n + 1] <= Q[n]]
    checked = 0
    max_wait = 0
    for k in range(args.horizon):
        end = k + 2 * isqrt(k) + 12
        if end > args.horizon:
            break
        witnesses = [n for n in range(k, end) if Q[n + 1] <= Q[n]]
        if not witnesses:
            raise AssertionError(f"target-excluding strict window found at {k}")
        max_wait = max(max_wait, witnesses[0] - k)
        checked += 1
    A21, Q21, _ = greedy(1, 21, 1024)
    assert 5 in A21 and 7 in A21
    assert (Q21[73], Q21[79]) == (1, 3)
    phases = []
    for r in range(15):
        delta = Fraction(2 ** ((2 * r) % 5), 31) - Fraction(pow(2, 2 * r, 21), 21)
        if delta > 0:
            phases.append((r, int(delta * 651)))
    assert phases == [(3, 11), (4, 44), (6, 53), (7, 212), (9, 137), (12, 305)]
    # A second immutable selected atom improves the phase obstruction.
    two_anchor_phases = [r for r in range(105) if
        sum((Fraction(2 ** ((2 * r) % d), (1 << d) - 1) for d in (5, 7)), Fraction())
        > Fraction(pow(2, 2 * r, 21), 21)]
    assert len(two_anchor_phases) == 60
    # Check the exact gcd-orbit finite-segment estimate used in r1 and r3.
    orbit_checks = 0
    for b in (2, 3, 5):
        for step in range(1, 13):
            for d in range(1, 20):
                g = gcd(step, d)
                for length in (1, 2, 3, 7, 19, 31):
                    mean = sum((Fraction(b ** ((t * step) % d), b ** d - 1)
                                for t in range(1, length + 1)), Fraction()) / length
                    bound = Fraction(g, d * (b ** g - 1)) + Fraction(1, length * (b ** g - 1))
                    assert mean <= bound
                    orbit_checks += 1
    receipt = {
        "schema_version": "erdos257_eight_return_exact_audit_v1",
        "arithmetic": "exact integers and fractions; outward enclosures for greedy bits",
        "horizon": args.horizon, "selected_count": len(A), "enclosure_width": width,
        "anchors": anchors, "prime_progressions": progressions,
        "repair_windows_checked": checked, "max_observed_wait": max_wait,
        "repair_count": len(repairs), "six_phase_certificate": phases,
        "two_anchor_phase_count": len(two_anchor_phases), "two_anchor_period": 105,
        "two_anchor_phases": two_anchor_phases, "orbit_inequalities_checked": orbit_checks,
        "twenty_one_six_step_counterexample": {"Q73": Q21[73], "Q79": Q21[79]},
        "endpoint_status": "open; finite windows do not establish all windows",
    }
    result = json.dumps(receipt, indent=2) + "\n"
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(result)
    print(result)


if __name__ == "__main__":
    main()
