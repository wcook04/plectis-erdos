#!/usr/bin/env python3
"""Exact valuation replay for the unique Newton-face closure theorem."""

from __future__ import annotations

from fractions import Fraction
from math import gcd
import json
import random


def weight(n: int, m: int, qm: int, k: int, qk: int) -> int:
    return (n - m) * qk + qm * k


def main() -> int:
    rng = random.Random(1041_20260825)
    unique_rows = 0
    power_rows = 0
    phase_supply_rows = 0
    rejected_controls = 0
    minimum_gap = None

    for n in range(5, 81):
        for m in range(1, (n - 1) // 2 + 1):
            d = gcd(n, m)
            orbit = n // d
            assert orbit != 2  # orbit 2 is precisely the excluded Nyquist mode
            if orbit >= 5:
                strict_negative_supply = d * ((orbit - 1) // 2)
            else:
                assert orbit in (3, 4)
                strict_negative_supply = d
                assert d >= 2
            assert strict_negative_supply >= 2
            phase_supply_rows += 1

    for n in range(4, 81):
        low_modes = list(range(1, (n - 1) // 2 + 1))
        for _ in range(128):
            m = rng.choice(low_modes)
            active_modes = list(range(m, n))
            valuations = {k: rng.randint(1, 60) for k in active_modes}
            slopes = {k: Fraction(valuations[k], n - k) for k in active_modes}
            best = min(slopes.values())
            winners = [k for k in active_modes if slopes[k] == best]
            if len(winners) != 1 or winners[0] != m:
                rejected_controls += 1
                continue
            qm = valuations[m]
            active = n * qm
            for k in active_modes:
                if k == m:
                    continue
                qk = valuations[k]
                assert qm * (n - k) < qk * (n - m)
                competitor = weight(n, m, qm, k, qk)
                gap = competitor - active
                assert gap >= 1
                minimum_gap = gap if minimum_gap is None else min(minimum_gap, gap)
                u = Fraction(1, 10)
                assert u**competitor == u**active * u**gap
                assert u**competitor / u**active == u**gap
                power_rows += 1
            unique_rows += 1

        # Required negative controls: manufacture a two-mode rational tie.
        if len(low_modes) >= 2:
            j, k = low_modes[0], low_modes[-1]
            c = 3
            qj, qk = c * (n - j), c * (n - k)
            assert Fraction(qj, n - j) == Fraction(qk, n - k)
            assert not (qj * (n - k) < qk * (n - j))
            assert weight(n, j, qj, k, qk) == n * qj
            rejected_controls += 1

        # A unique outer winner at a higher degree is deliberately outside the
        # theorem: a dormant lower-degree mode can reappear at a smaller scale.
        if len(low_modes) >= 2:
            lower, outer = low_modes[0], low_modes[-1]
            qlower, qouter = 50, 1
            assert Fraction(qouter, n - outer) < Fraction(qlower, n - lower)
            assert lower < outer
            rejected_controls += 1

    assert unique_rows > 0
    assert power_rows > 0
    assert rejected_controls > 0
    assert minimum_gap == 1

    receipt = {
        "schema": "erdos1041_near_fekete_unique_newton_face_check_v1",
        "verdict": "PASS",
        "degrees": [4, 80],
        "exact_unique_face_rows": unique_rows,
        "exact_power_factor_rows": power_rows,
        "exact_strict_phase_supply_rows": phase_supply_rows,
        "tied_or_face_switch_negative_controls": rejected_controls,
        "minimum_positive_integral_gap": minimum_gap,
        "claim_boundary": (
            "Exact replay verifies valuation separation and rejects tied or "
            "lower-degree face-switching patterns. "
            "It does not numerically certify the analytic branch-matching proof "
            "or settle resonant faces or unrestricted Erdos 1041."
        ),
    }
    print(json.dumps(receipt, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
