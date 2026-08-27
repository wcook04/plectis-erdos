#!/usr/bin/env python3
"""Fail-closed audit for the first-nonzero-mode Form A-cut theorem.

This is evidence for, not the proof of, the closed-half-plane phase count.  It
checks every boundary event and every intervening phase cell for all modes
through degree 80, verifies the exact ray formula numerically, and requires the
sharp degree-three negative control to fire.
"""
from __future__ import annotations

import json
import math

import numpy as np


def event_phases(n: int, m: int) -> list[float]:
    two_pi = 2.0 * math.pi
    events = sorted(
        {(math.pi / 2.0 - two_pi * m * j / n) % two_pi for j in range(n)}
        | {(-math.pi / 2.0 - two_pi * m * j / n) % two_pi for j in range(n)}
    )
    probes = list(events)
    for a, b in zip(events, events[1:] + [events[0] + two_pi], strict=True):
        probes.append(((a + b) / 2.0) % two_pi)
    return probes


def count_nonpositive(n: int, m: int, phase: float) -> int:
    values = np.cos(phase + 2.0 * math.pi * m * np.arange(n) / n)
    return int(np.count_nonzero(values <= 2.0e-12))


def main() -> int:
    rows = []
    worst_identity = 0.0
    ok = True
    for n in range(4, 81):
        for m in range(1, n):
            d = math.gcd(n, m)
            q = n // d
            lower = d * (q // 2)
            counts = [count_nonpositive(n, m, phase) for phase in event_phases(n, m)]
            observed = min(counts)
            row_ok = lower >= 2 and observed >= lower
            ok &= row_ok
            rows.append(
                {
                    "n": n,
                    "m": m,
                    "gcd": d,
                    "orbit_size": q,
                    "proved_lower_bound": lower,
                    "observed_event_cell_minimum": observed,
                    "ok": row_ok,
                }
            )

            # Deterministic identity audit: H(t omega^j)=t^m p_j-t^n.
            A = np.exp(1j * (0.137 * n + 0.271 * m))
            omega = np.exp(2j * math.pi / n)
            for j in (0, n // 3, n - 1):
                u = omega**j
                p = float(np.real(A * u**m))
                for t in (0.0, 0.03125, 0.2, 0.73, 1.0):
                    lhs = float(np.real(A * (t * u) ** m - (t * u) ** n))
                    rhs = t**m * p - t**n
                    worst_identity = max(worst_identity, abs(lhs - rhs))

    # Sharp negative control: a generic half-plane through three roots can
    # contain only one of them.
    n3_counts = [count_nonpositive(3, 1, p) for p in event_phases(3, 1)]
    negative_control = min(n3_counts) == 1
    ok &= negative_control and worst_identity < 2.0e-11

    receipt = {
        "schema": "erdos1041_form_a_cut_first_nonzero_mode_check_v1",
        "verdict": "PASS" if ok else "FAIL",
        "degree_range": [4, 80],
        "mode_row_count": len(rows),
        "minimum_supply": min(row["proved_lower_bound"] for row in rows),
        "worst_ray_identity_residual": worst_identity,
        "degree_three_negative_control": negative_control,
        "failed_rows": [row for row in rows if not row["ok"]],
        "claim_boundary": (
            "Audits the exact homogeneous first-mode theorem and its sharp "
            "degree threshold. It does not absorb the polynomial remainder "
            "or prove unrestricted Erdos 1041."
        ),
    }
    print(json.dumps(receipt, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

