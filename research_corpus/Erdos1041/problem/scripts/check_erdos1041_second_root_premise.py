#!/usr/bin/env python3
"""How many roots satisfy |w| <= 1 at the least-critical-value hub.

Companion to [`../GeneralSpokeIdentity.md`](../GeneralSpokeIdentity.md).

The identity (S) of that note generalises the degree-three spoke mechanism to
every degree.  This script measures one input it needs.  Normalise a critical
point ``c`` to the origin and scale by ``f(c)^(1/n)``:

    G(w) = w^n + a_{n-1} w^{n-1} + ... + a_2 w^2 + 1,

with no linear term (exactly ``G'(0) = 0``) and ``G(0) = 1``.  Two facts are then
automatic: ``prod |w_i| = 1`` from the constant term, and ``sum 1/w_i = 0`` from
``G'(0) = 0``.  Together those give **one** root with ``|w_i| <= 1``, never two.

Choosing ``c`` to be the hub of least critical value is exactly the condition

    |G(c')| >= 1  at every other critical point c'  of G,

since ``|G(c')| = |f(c')| / |f(c)|`` and ``|G(0)| = 1``.  The degree-three proof
gets its second root from that minimality.  This script measures whether the
crude form keeps supplying one at higher degree -- see the correction below for
what that does and does not mean.

This script samples normalised ``G`` at several degrees, keeps only the
minimal-hub ones, and counts roots in the closed unit disk.  It also replays
three exact stored degree-four witnesses in which the minimal hub has exactly
one root of modulus at most one.  Their coefficients are stored as IEEE-754 hexadecimal literals
because the minimality margins are near ``1e-2`` but the root moduli that decide
the count sit as close as ``1.028`` to the unit circle, and this directory has
been bitten before by decimal rounding on stored configurations.

Measured counts (400000 samples at n = 3, 4; 200000 at n = 5, 6, 7):

    n = 3   236554 minimal-hub, 0 with exactly one root inside
    n = 4   164174 minimal-hub, 508 with exactly one root inside
    n = 5    55409 minimal-hub, 2 with exactly one root inside
    n = 6    37670 minimal-hub, 0
    n = 7    27257 minimal-hub, 0

**CORRECTION 2026-08-23.**  This script originally concluded from those counts
that the second-root premise is FALSE at degree four.  That inference is
retracted.  ``|w| <= 1`` is only the CRUDE sufficient form of criterion (SC) in
the companion note; against the sharp form ``max_t (1-t)|Q(t)| <= 1`` two roots
pass at all three stored witnesses (moduli 0.7709/1.0280, 1.0514/0.7541,
0.7619/1.0340, SC values 0.49 to 0.67) and both spokes are genuinely contained.
Those configurations therefore SATISFY the mechanism.  The correct sufficient
condition is also weaker than stated: spoke length is ``lambda |w_i|`` with
``lambda = |f(c)|^(1/n) < 1``, so two roots satisfying (SC) with
``|w_1| + |w_2| <= 2`` suffice and individual ``|w_i| <= 1`` is not needed.

What the counts below still show is only this: the CRUDE form stops supplying a
second root from degree four.  Whether sublevel containment on two spokes
survives there is settled by ``StraightSpokeHubCriterionLab.md`` section 2, not
by this script.

The zero counts at n = 6, 7 are sampling statements only and should not be read
as the premise holding there; the n = 5 count of 2 in 55409 shows how rare these
configurations are, so absence at a given sample size means little.

This proves nothing about Erdős #1041; it bounds one mechanism.
"""
from __future__ import annotations

import argparse
import json
import sys
from typing import Any

import numpy as np
from mpmath import mp, mpc

#: Exact degree-four witnesses: ((Re a_3, Im a_3), (Re a_2, Im a_2)) as IEEE-754
#: hexadecimal literals.  At each, the origin is the least-critical-value hub and
#: exactly one root of G has modulus at most one.  NOTE: these are NOT witnesses
#: to the mechanism failing -- two roots pass the sharp criterion (SC) at every
#: one of them.  See the correction in the module docstring.
SECOND_ROOT_FAILURE_WITNESSES: tuple[tuple[tuple[str, str], tuple[str, str]], ...] = (
    (("0x1.158ab9f02e377p-1", "0x1.9a6e171eecee8p-2"),
     ("0x1.56789e08b41f6p-6", "0x1.24f4b7365ffecp-1")),
    (("0x1.51e8b3c2c7da9p-2", "-0x1.8c873297b16ffp-1"),
     ("-0x1.442ae2f99f420p-10", "-0x1.2c1e60c2ebfb5p-1")),
    (("0x1.be817fea33456p-2", "-0x1.24d09e263b930p-1"),
     ("0x1.44496a4daa6a5p-5", "-0x1.329cc7fa2ec8bp-1")),
)

DEFAULT_DIGITS = 50


def witness_coefficients(entry) -> np.ndarray:
    (a3_re, a3_im), (a2_re, a2_im) = entry
    return np.array(
        [
            1.0 + 0.0j,
            complex(float.fromhex(a3_re), float.fromhex(a3_im)),
            complex(float.fromhex(a2_re), float.fromhex(a2_im)),
            0.0 + 0.0j,
            1.0 + 0.0j,
        ],
        dtype=complex,
    )


def normalised_sample(degree: int, rng: np.random.Generator) -> np.ndarray:
    coefficients = np.zeros(degree + 1, dtype=complex)
    coefficients[0] = 1.0
    for index in range(2, degree):
        coefficients[degree - index] = (
            rng.standard_normal() + 1j * rng.standard_normal()
        )
    coefficients[degree] = 1.0
    return coefficients


def is_minimal_hub(coefficients: np.ndarray) -> tuple[bool, list[float]]:
    """Is the origin the critical point of least |G|?"""
    critical = np.roots(np.polyder(coefficients))
    others = [point for point in critical if abs(point) > 1.0e-9]
    if len(others) != len(critical) - 1:
        return False, []
    values = [float(abs(np.polyval(coefficients, point))) for point in others]
    return all(value >= 1.0 for value in values), values


def roots_inside(coefficients: np.ndarray) -> int:
    return int((np.abs(np.roots(coefficients)) <= 1.0).sum())


def replay_witnesses(digits: int) -> list[dict[str, Any]]:
    mp.dps = digits
    rows = []
    for index, entry in enumerate(SECOND_ROOT_FAILURE_WITNESSES):
        coefficients = witness_coefficients(entry)
        minimal, other_values = is_minimal_hub(coefficients)
        roots = np.roots(coefficients)
        high = [mpc(complex(root)) for root in roots]
        exact = [mpc(complex(value)) for value in coefficients]

        def evaluate(point):
            accumulator = mpc(0)
            for value in exact:
                accumulator = accumulator * point + value
            return accumulator

        rows.append(
            {
                "index": index,
                "minimal_hub": bool(minimal),
                "other_critical_values": other_values,
                "root_moduli": [float(abs(root)) for root in roots],
                "roots_in_closed_unit_disk": int(sum(1 for r in high if abs(r) <= 1)),
                "max_residual_at_roots": float(
                    max(abs(evaluate(root)) for root in high)
                ),
                "linear_coefficient_is_zero": bool(coefficients[3] == 0),
                "constant_coefficient": complex(coefficients[4]).real,
            }
        )
    return rows


def sample_rows(trials: int, seed: int) -> list[dict[str, Any]]:
    rng = np.random.default_rng(seed)
    rows = []
    for degree in (3, 4, 5, 6, 7):
        budget = trials if degree < 5 else trials // 2
        minimal = 0
        exactly_one = 0
        fewest = degree + 1
        for _ in range(budget):
            coefficients = normalised_sample(degree, rng)
            ok, _ = is_minimal_hub(coefficients)
            if not ok:
                continue
            minimal += 1
            inside = roots_inside(coefficients)
            fewest = min(fewest, inside)
            if inside == 1:
                exactly_one += 1
        rows.append(
            {
                "degree": degree,
                "sampled": budget,
                "minimal_hub_configurations": minimal,
                "exactly_one_root_inside": exactly_one,
                "fewest_roots_inside": fewest if minimal else None,
            }
        )
    return rows


def build_payload(trials: int, seed: int, digits: int) -> dict[str, Any]:
    witnesses = replay_witnesses(digits)
    samples = sample_rows(trials, seed)
    return {
        "schema": "erdos1041_second_root_premise_v0",
        "boundary": (
            "bounds the reach of the degree-three spoke mechanism; proves "
            "nothing about Erdos 1041"
        ),
        "premise_under_test": (
            "at the least-critical-value hub, at least two roots satisfy the "
            "CRUDE sufficient form |w| <= 1; this is NOT the criterion (SC), "
            "and its failure does not establish containment failure"
        ),
        "witnesses": witnesses,
        "samples": samples,
        "witnesses_have_one_root_within_unit_modulus": all(
            row["minimal_hub"] and row["roots_in_closed_unit_disk"] == 1
            for row in witnesses
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trials", type=int, default=60000)
    parser.add_argument("--seed", type=int, default=20260823)
    parser.add_argument("--digits", type=int, default=DEFAULT_DIGITS)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    payload = build_payload(args.trials, args.seed, args.digits)

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print("stored degree-four witnesses:")
        for row in payload["witnesses"]:
            print(f"  witness {row['index']}: minimal_hub={row['minimal_hub']}"
                  f"  roots inside={row['roots_in_closed_unit_disk']}"
                  f"  max|G(root)|={row['max_residual_at_roots']:.3e}")
            print(f"     root moduli: "
                  f"{[round(m, 12) for m in row['root_moduli']]}")
            print(f"     other critical values: "
                  f"{[round(v, 9) for v in row['other_critical_values']]}")
        print()
        print("sampled counts:")
        for row in payload["samples"]:
            print(f"  n={row['degree']}: {row['minimal_hub_configurations']} "
                  f"minimal-hub of {row['sampled']}, "
                  f"{row['exactly_one_root_inside']} with exactly one root inside, "
                  f"fewest={row['fewest_roots_inside']}")

    if not payload["witnesses_have_one_root_within_unit_modulus"]:
        print("GUARD FAILED: a stored degree-four witness no longer exhibits a "
              "minimal hub with exactly one root of modulus at most one; the "
              "stored configurations have drifted.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
