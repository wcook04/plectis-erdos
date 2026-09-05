#!/usr/bin/env python3
"""Exact selected-anchor phase certificates; no membership inference."""
import argparse
import json
from fractions import Fraction
from math import gcd, lcm
from erdos257_eight_return_exact_audit import greedy


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--horizon', type=int, default=64)
    parser.add_argument('--period-cap', type=int, default=1260)
    args = parser.parse_args()
    selected, _, _ = greedy(1, 21, args.horizon)
    # Independently replay the short prefix with exact rational remainders.
    remainder = Fraction(1, 21)
    direct = set()
    for a in range(1, args.horizon + 1):
        weight = Fraction(1, (1 << a) - 1)
        if weight <= remainder:
            direct.add(a)
            remainder -= weight
    assert selected == direct
    anchors = []
    period = 3
    for a in sorted(selected):
        enlarged = lcm(period, a // gcd(a, 2))
        if enlarged <= args.period_cap:
            anchors.append(a)
            period = enlarged
    denominators = [(1 << a) - 1 for a in anchors]
    denominator = lcm(21, *denominators)
    columns = [(a, denominator // d) for a, d in zip(anchors, denominators)]
    favorable = []
    minimum_gap = None
    for r in range(period):
        gap = sum(c * (1 << ((2 * r) % a)) for a, c in columns)
        gap -= (denominator // 21) * pow(2, 2 * r, 21)
        if gap > 0:
            favorable.append(r)
            minimum_gap = gap if minimum_gap is None else min(gap, minimum_gap)
    density = Fraction(len(favorable), 2 * period)
    if args.horizon == 64 and args.period_cap == 1260:
        assert period == 1260 and len(favorable) == 1011
        assert density > Fraction(2, 5)
    print(json.dumps({
        'schema': 'erdos257_selected_phase_density_audit_v1',
        'arithmetic': 'integer enclosures for selected anchors; exact integer phase comparisons',
        'horizon': args.horizon, 'period_cap': args.period_cap,
        'anchors': anchors, 'period': period, 'favorable_count': len(favorable),
        'conditional_upper_density_lower_bound': str(density),
        'favorable_mask_hex': hex(sum(1 << r for r in favorable)),
        'anchor_prefix_checked_by_two_methods': True,
        'minimum_positive_gap': str(Fraction(minimum_gap, denominator)),
        'unfavorable_count': period - len(favorable),
        'boundary': 'Upper-density bound conditional on 1/21 membership; no lower-density or membership theorem.'
    }, indent=2))


if __name__ == '__main__':
    main()
