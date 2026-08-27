#!/usr/bin/env python3
"""The hard witnesses are near-Fekete: perturbed regular n-gons at radius 1-eps.

Erdős #1041.  The resultant identity gives, over the ``n-1`` critical points
counted with multiplicity,

    prod_k |f(c_k)|  =  prod_{i<j} |z_i - z_j|^2 / n^n,

and Fekete bounds the Vandermonde product over the closed unit disk by
``n^{n/2}``, with equality exactly at the ``n``-th roots of unity.  Writing
``T* = min_k |f(c_k)|`` therefore

    T*^(n-1)  <=  prod_k |f(c_k)|  =  disc / n^n  <=  1,

so **``T*`` near one forces the discriminant to its Fekete maximum**, hence the
roots to a rotated regular ``n``-gon on the unit circle.  The hard regime of
this problem is the near-extremal regime; those are the same configurations.

This is not a new theorem -- the equality case is classical and
``CriticalBudgetLab.md`` already records it.  What this script establishes is
the *quantitative* consequence, and it is a statement about where to search:

* the corpus's two stored hard witnesses (degrees 6 and 9, the configurations
  where no admissible hub carries two contained straight spokes) sit at
  discriminant ratio ``0.99999218`` and ``0.99994712`` of the Fekete maximum,
  with maximum deviation ``5.2e-4`` and ``1.2e-4`` from an exact regular gon and
  every angular gap within ``0.1%`` of ``2*pi/n``;
* generic random configurations at the same degrees sit at ratio ``5.9e-6`` and
  ``~1e-13``, with deviation ``0.79`` and ``1.11``.

That is twelve orders of magnitude in the discriminant ratio.  The hard set is
an exponentially thin neighbourhood of a measure-zero configuration, which is
why every adversarial search in ``CriticalBudgetLab.md`` run in bulk root
coordinates has failed to reach it, and why the witnesses had to be stored as
exact IEEE-754 literals.

Consequence for search: parametrise near-Fekete,

    z_k = r (1 + a_k) exp( i (2 pi k / n + t_k) ),   r = 1 - eps,

and search over ``eps`` and the small perturbations ``a_k, t_k``, rather than
over root positions in the bulk.

Consequence for proof: any argument may split on the discriminant ratio.  Away
from the Fekete maximum ``T*`` is bounded away from 1 and the cells of
``{|f| < T*}`` merge with room to spare; near it the configuration is a
perturbation of ``z^n - r^n``, whose descent branches are the radial spokes of
total length exactly ``2r``.  This script does not prove either half.
"""
from __future__ import annotations

import argparse
import cmath
import json
import math
import pathlib
import sys
from typing import Any

_HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

import check_erdos1041_straight_spoke_hub_criterion as _witness_module  # noqa: E402

#: A configuration counts as near-Fekete when its discriminant reaches this
#: fraction of the Fekete maximum.  Both stored witnesses clear it by a wide
#: margin; generic configurations miss it by orders of magnitude.
NEAR_FEKETE_RATIO_FLOOR = 0.99


def discriminant_over_fekete_max(roots: list[complex]) -> float:
    """``prod_{i<j}|z_i-z_j|^2`` divided by the Fekete maximum ``n^n``."""
    n = len(roots)
    log_total = 0.0
    for i in range(n):
        for j in range(i + 1, n):
            separation = abs(roots[i] - roots[j])
            if separation == 0:
                return 0.0
            log_total += 2.0 * math.log(separation)
    return math.exp(log_total - n * math.log(n))


def regular_gon_deviation(roots: list[complex]) -> tuple[float, float]:
    """Max matching distance to the best rotated regular gon, and its radius.

    The gon radius is the mean modulus; the rotation is fixed by the argument
    of ``sum_k z_k^n``, which is the exact aligner for a true regular gon.
    """
    n = len(roots)
    radius = sum(abs(z) for z in roots) / n
    phase = cmath.phase(sum(z ** n for z in roots)) / n
    model = [
        radius * cmath.exp(1j * (phase + 2 * cmath.pi * k / n)) for k in range(n)
    ]
    remaining = list(range(n))
    worst = 0.0
    for z in roots:
        index = min(remaining, key=lambda idx: abs(z - model[idx]))
        remaining.remove(index)
        worst = max(worst, abs(z - model[index]))
    return worst, radius


def normalised_angular_gaps(roots: list[complex]) -> list[float]:
    """Consecutive angular gaps in units of ``2*pi/n``, sorted."""
    n = len(roots)
    ordered = sorted(roots, key=cmath.phase)
    gaps = [
        (cmath.phase(ordered[(i + 1) % n]) - cmath.phase(ordered[i])) % (2 * cmath.pi)
        for i in range(n)
    ]
    return sorted(gap / (2 * cmath.pi / n) for gap in gaps)


def profile(label: str, roots: list[complex]) -> dict[str, Any]:
    n = len(roots)
    ratio = discriminant_over_fekete_max(roots)
    deviation, radius = regular_gon_deviation(roots)
    moduli = [abs(z) for z in roots]
    return {
        "label": label,
        "degree": n,
        "discriminant_over_fekete_max": ratio,
        "implied_critical_value_ceiling": ratio ** (1.0 / (n - 1)) if n > 1 else None,
        "modulus_min": min(moduli),
        "modulus_max": max(moduli),
        "regular_gon_radius": radius,
        "max_deviation_from_regular_gon": deviation,
        "normalised_angular_gaps": normalised_angular_gaps(roots),
        "near_fekete": bool(ratio >= NEAR_FEKETE_RATIO_FLOOR),
    }


def stored_witness_rows() -> list[dict[str, Any]]:
    rows = []
    for degree, literals in sorted(_witness_module.QC_REFUTATION_WITNESSES.items()):
        roots = [
            complex(float.fromhex(real), float.fromhex(imag))
            for real, imag in literals
        ]
        rows.append(profile(f"QC refutation witness, degree {degree}", roots))
    return rows


def control_rows(seed: int = 7) -> list[dict[str, Any]]:
    import numpy as np

    rng = np.random.default_rng(seed)
    rows = []
    for degree in (6, 9):
        radius = 0.99999985
        gon = [
            radius * cmath.exp(2j * cmath.pi * k / degree) for k in range(degree)
        ]
        rows.append(profile(f"exact regular {degree}-gon at r={radius}", gon))
    for degree in (6, 9):
        moduli = np.sqrt(rng.random(degree)) * 0.999
        angles = rng.random(degree) * 2 * np.pi
        generic = [complex(m * np.exp(1j * a)) for m, a in zip(moduli, angles)]
        rows.append(profile(f"generic random degree {degree}", generic))
    return rows


def build_payload() -> dict[str, Any]:
    witnesses = stored_witness_rows()
    controls = control_rows()
    generic = [row for row in controls if row["label"].startswith("generic")]
    return {
        "schema": "erdos1041_hard_regime_near_fekete_v0",
        "boundary": (
            "a measurement of where the stored hard witnesses sit in "
            "configuration space; it proves no statement about Erdos 1041 and "
            "is a search-coordinate and proof-architecture finding only"
        ),
        "near_fekete_ratio_floor": NEAR_FEKETE_RATIO_FLOOR,
        "witnesses": witnesses,
        "controls": controls,
        "every_witness_near_fekete": all(row["near_fekete"] for row in witnesses),
        "no_generic_control_near_fekete": not any(row["near_fekete"] for row in generic),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    payload = build_payload()

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        for row in payload["witnesses"] + payload["controls"]:
            print(f"--- {row['label']} (n={row['degree']})")
            print(f"    discriminant / Fekete max      : "
                  f"{row['discriminant_over_fekete_max']:.12f}")
            print(f"    implied ceiling on T*          : "
                  f"{row['implied_critical_value_ceiling']:.12f}")
            print(f"    modulus min / max              : "
                  f"{row['modulus_min']:.9f} / {row['modulus_max']:.9f}")
            print(f"    max deviation from regular gon : "
                  f"{row['max_deviation_from_regular_gon']:.9f}")
            print(f"    near-Fekete                    : {row['near_fekete']}")
            print()

    if not payload["every_witness_near_fekete"]:
        print("GUARD FAILED: a stored hard witness is no longer near-Fekete; the "
              "search-coordinate finding has drifted.", file=sys.stderr)
        return 1
    if not payload["no_generic_control_near_fekete"]:
        print("GUARD FAILED: a generic control registered as near-Fekete; the "
              "separation this script reports is not real.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
