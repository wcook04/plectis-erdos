#!/usr/bin/env python3
"""Verify exact local falsifiers for Erdős #243 record-descent arguments.

The script checks two parametric reduced rational-tail constructions using
only Python integers:

* ``-m -> -t^2 m -> 0`` with a cancellation-free first step and arbitrarily
  small adjacent normalised errors;
* a clean-introduction, maximal-square-erasure, then landing-at-zero orbit.

These are finite exact regression fixtures.  They are not infinite
counterexamples and do not settle Erdős #243.
"""

from __future__ import annotations

import argparse
import json
import math


def reduced_step(u: int, v: int) -> dict[str, int]:
    """Apply the centred reduced pseudo-greedy step to ``u / v``."""
    if not (0 < u <= v) or math.gcd(u, v) != 1:
        raise ValueError("require a positive reduced rational u/v")

    nearest = (2 * v + u) // (2 * u)
    a = nearest + 1
    e = v - nearest * u
    raw_u = a * u - v
    raw_v = a * v
    h = math.gcd(raw_u, raw_v)

    assert raw_u == u - e
    assert h == math.gcd(a * a, raw_u)
    assert raw_u % h == 0 and raw_v % h == 0
    u_next = raw_u // h
    v_next = raw_v // h
    assert math.gcd(u_next, v_next) == 1
    return {
        "a": a,
        "e": e,
        "h": h,
        "u_next": u_next,
        "v_next": v_next,
    }


def amplification_family(m: int, t: int, k: int) -> dict[str, object]:
    if m < 1 or t < 2 or k < 1:
        raise ValueError("require m >= 1, t >= 2, and k >= 1")
    if math.gcd(m, t * t - t + 1) != 1:
        raise ValueError("require gcd(m, t^2-t+1) = 1")

    q_plus = (k * m * t - 1) * (
        k * m * t * (t * t + 1) - t * t + t - 1
    )
    q = q_plus - t * t * m
    u0 = q - m
    a0 = t + k * q
    v0 = (a0 - 1) * u0 - m

    first = reduced_step(u0, v0)
    assert first["a"] == a0
    assert first["e"] == -m
    assert first["h"] == 1
    assert first["u_next"] == q

    second = reduced_step(first["u_next"], first["v_next"])
    assert second["e"] == -(t * t * m)
    assert second["h"] == q_plus
    assert second["u_next"] == 1

    third = reduced_step(second["u_next"], second["v_next"])
    assert third["e"] == 0

    return {
        "parameters": {"m": m, "t": t, "k": k},
        "q": q,
        "q_plus": q_plus,
        "states": [
            {"u": u0, "v": v0, **first},
            {"u": first["u_next"], "v": first["v_next"], **second},
            {"u": second["u_next"], "v": second["v_next"], **third},
        ],
        "verified_properties": [
            "primitive record amplification -m -> -t^2*m",
            "first step cancellation-free",
            "second step lands at reduced numerator one",
            "third centred residue is zero",
        ],
    }


def clean_erase_land_family(A: int) -> dict[str, object]:
    if A < 5:
        raise ValueError("require A >= 5")

    u0 = A**3 - 2 * A**2 - A + 1
    a0 = A
    e0 = -(A - 2)
    v0 = (a0 - 1) * u0 + e0

    first = reduced_step(u0, v0)
    assert first["a"] == a0
    assert first["e"] == e0
    assert first["h"] == 1
    assert first["u_next"] == A**3 - 2 * A**2 - 1

    second = reduced_step(first["u_next"], first["v_next"])
    assert second["a"] == A**2 - A
    assert second["e"] == -1
    assert second["h"] == A**2
    assert second["u_next"] == A - 2
    assert math.gcd(A, second["v_next"]) == 1

    third = reduced_step(second["u_next"], second["v_next"])
    assert third["a"] == A**4 - 2 * A**3 + 1
    assert third["e"] == -1
    assert third["h"] == A - 1
    assert third["u_next"] == 1

    fourth = reduced_step(third["u_next"], third["v_next"])
    assert fourth["e"] == 0

    return {
        "parameter": {"A": A},
        "states": [
            {"u": u0, "v": v0, **first},
            {"u": first["u_next"], "v": first["v_next"], **second},
            {"u": second["u_next"], "v": second["v_next"], **third},
            {"u": third["u_next"], "v": third["v_next"], **fourth},
        ],
        "verified_properties": [
            "clean introduction of A into the reduced denominator",
            "maximal square payment h=A^2 on the next step",
            "complete deletion of A from the following denominator",
            "eventual centred residue zero",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--m", type=int, default=1)
    parser.add_argument("--t", type=int, default=2)
    parser.add_argument("--k", type=int, default=2)
    parser.add_argument("--erase-scale", type=int, default=101)
    args = parser.parse_args()

    receipt = {
        "schema": "erdos243-record-amplification-receipt/1",
        "status": "verified",
        "amplification_family": amplification_family(args.m, args.t, args.k),
        "clean_erase_land_family": clean_erase_land_family(args.erase_scale),
        "claim_ceiling": (
            "finite exact falsifiers for local descent and static cancellation-budget "
            "arguments; not an infinite orbit and not a solution of Erdős #243"
        ),
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
