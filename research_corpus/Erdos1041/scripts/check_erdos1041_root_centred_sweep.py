#!/usr/bin/env python3
"""Receipt for the root-centred reciprocal sweep precondition.

Companion to [`../RootCentredReciprocalSweep.md`](../RootCentredReciprocalSweep.md).

Pendyala's reciprocal sweep (arXiv:2606.19178, assimilated in
``ReciprocalSweepBoundaryLab.md``) is centred at ``0`` because ``g(0) = 1``
exactly for ``g(z) = prod_j (1 - conj(a_j) z)``.  Centring at any point ``p``
needs ``|g(p)| <= 1``, so centring at a *root* needs some root with
``|g(a_k)| <= 1``.

This script is the receipt for **Theorem (RS)**, which the note proves by an
ordinary power-series argument:

    |Res(f, f*)| = prod_{j,k} |1 - conj(a_j) a_k| = exp(-sum_{m>=1} |p_m|^2/m) <= 1,

with ``p_m = sum_j a_j^m`` and equality exactly at ``f = z^n``.  Its corollary
``min_k |g(a_k)| <= 1`` is the precondition above.

Three quantities are checked.

1.  **The power-sum identity** itself, truncated against an explicit tail bound.
2.  **The Cauchy/Szego identity**

        prod_{j,k} (1 - conj(a_j) a_k) = prod_{i<j}|a_i - a_j|^2 / det K,
        K_{jk} = 1/(1 - conj(a_j) a_k),

    which rewrites the same product as a Vandermonde over a Gram determinant and
    gives the corollary ``det K >= prod_{i<j}|a_i - a_j|^2``.
3.  **The precondition**, ``min_k |g(a_k)| <= 1``, directly.

None of this is a theorem about Erdos #1041, and (RS) is very plausibly classical
Schur-Cohn material -- see the note's priority-check section, and do not describe
it as new until that search has been run.  This script fails (exit 1) if a
configuration is found with ``min_k |g(a_k)| > 1``, or if either identity drifts.
"""
from __future__ import annotations

import argparse
import json
import sys
from typing import Any

import numpy as np

DEFAULT_TRIALS = 4000
IDENTITY_TOLERANCE = 1.0e-9


def sweep_product(roots: np.ndarray) -> float:
    """``prod_{j,k} |1 - conj(a_j) a_k|``."""
    matrix = 1.0 - np.conj(roots)[:, None] * roots[None, :]
    return float(np.abs(matrix).prod())


def sweep_levels(roots: np.ndarray) -> np.ndarray:
    """``|g(a_k)|`` for every root, ``g(z) = prod_j (1 - conj(a_j) z)``."""
    return np.array(
        [float(np.abs(1.0 - np.conj(roots) * root).prod()) for root in roots]
    )


def cauchy_identity_error(roots: np.ndarray) -> float:
    matrix = 1.0 - np.conj(roots)[:, None] * roots[None, :]
    left = float(np.abs(matrix).prod())
    determinant = float(np.linalg.det(1.0 / matrix).real)
    vandermonde = 1.0
    for j in range(len(roots)):
        for k in range(j + 1, len(roots)):
            vandermonde *= abs(roots[j] - roots[k]) ** 2
    if determinant == 0.0:
        return float("nan")
    right = vandermonde / determinant
    return abs(left - right) / max(left, 1.0e-300)


def power_sum_identity_error(roots: np.ndarray, tolerance: float = 1.0e-18) -> float:
    """Relative error of ``prod_{j,k}|1-conj(a_j)a_k| = exp(-sum_m |p_m|^2/m)``.

    The series is truncated against the explicit tail bound
    ``n^2 rho^(2M) / (M (1 - rho^2))`` with ``rho = max_j |a_j|``.  Truncating on
    a *small term* instead is wrong: for a regular ``n``-gon ``p_m`` vanishes
    unless ``n | m``, so a run of zero terms triggers a premature break and the
    identity appears to fail by orders of magnitude.
    """
    degree = len(roots)
    rho = float(np.abs(roots).max())
    if rho >= 1.0:
        return float("nan")
    terms = 50
    while (
        degree * degree * rho ** (2 * terms) / (terms * (1.0 - rho * rho)) > tolerance
        and terms < 4_000_000
    ):
        terms *= 2
    total = 0.0
    for order in range(1, terms + 1):
        total += abs((roots ** order).sum()) ** 2 / order
    left = sweep_product(roots)
    right = float(np.exp(-total))
    return abs(left - right) / max(left, 1.0e-300)


def sample(degree: int, mode: int, rng: np.random.Generator) -> np.ndarray:
    if mode == 0:
        radii = np.sqrt(rng.random(degree)) * 0.999
        return radii * np.exp(2j * np.pi * rng.random(degree))
    if mode == 1:
        radii = 0.90 + 0.099 * rng.random(degree)
        return radii * np.exp(2j * np.pi * rng.random(degree))
    gon = 0.999 * np.exp(2j * np.pi * np.arange(degree) / degree)
    gon = gon * (1.0 + 1.0e-3 * rng.standard_normal(degree))
    moduli = np.abs(gon)
    return np.where(moduli < 0.999, gon, gon / moduli * 0.999)


def build_payload(trials: int, seed: int) -> dict[str, Any]:
    rng = np.random.default_rng(seed)
    worst_product = 0.0
    worst_min_level = 0.0
    worst_identity = 0.0
    worst_power_sum = 0.0
    every_root_fails = 0
    total = 0
    for degree in (2, 3, 4, 5, 6, 8, 10):
        for index in range(trials):
            roots = sample(degree, index % 3, rng)
            total += 1
            worst_product = max(worst_product, sweep_product(roots))
            levels = sweep_levels(roots)
            worst_min_level = max(worst_min_level, float(levels.min()))
            if float(levels.min()) > 1.0:
                every_root_fails += 1
            if degree <= 6 and index % 500 == 0:
                error = cauchy_identity_error(roots)
                if np.isfinite(error):
                    worst_identity = max(worst_identity, error)
            if index % 1000 == 0:
                error = power_sum_identity_error(roots)
                if np.isfinite(error):
                    worst_power_sum = max(worst_power_sum, error)
    return {
        "schema": "erdos1041_root_centred_sweep_v0",
        "boundary": (
            "numerical receipt for Theorem (RS) and its precondition; the "
            "theorem is proved in the companion note by ordinary mathematics, "
            "this script only guards against drift. Proves nothing about Erdos "
            "1041 and claims no novelty for (RS), which is plausibly classical "
            "Schur-Cohn material"
        ),
        "configurations": total,
        "max_sweep_product": worst_product,
        "max_min_root_level": worst_min_level,
        "configurations_where_every_root_exceeds_one": every_root_fails,
        "max_cauchy_identity_relative_error": worst_identity,
        "max_power_sum_identity_relative_error": worst_power_sum,
        "precondition_holds_everywhere": every_root_fails == 0,
        "identity_within_tolerance": worst_identity <= IDENTITY_TOLERANCE,
        "power_sum_identity_within_tolerance": worst_power_sum <= IDENTITY_TOLERANCE,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trials", type=int, default=DEFAULT_TRIALS)
    parser.add_argument("--seed", type=int, default=2026)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    payload = build_payload(args.trials, args.seed)

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"configurations                       : {payload['configurations']}")
        print(f"max prod_(j,k) |1-conj(a_j)a_k|      : {payload['max_sweep_product']:.9f}")
        print(f"max over configs of min_k |g(a_k)|   : {payload['max_min_root_level']:.9f}")
        print(f"configs where EVERY root exceeds one : "
              f"{payload['configurations_where_every_root_exceeds_one']}")
        print(f"max Cauchy identity relative error   : "
              f"{payload['max_cauchy_identity_relative_error']:.3e}")
        print(f"max power-sum identity rel. error    : "
              f"{payload['max_power_sum_identity_relative_error']:.3e}")

    if not payload["precondition_holds_everywhere"]:
        print("GUARD FAILED: a configuration has |g(a_k)| > 1 at every root, so no "
              "root admits a centred reciprocal sweep. Theorem (RS) would be "
              "contradicted; re-derive before trusting either.",
              file=sys.stderr)
        return 1
    if not payload["identity_within_tolerance"]:
        print("GUARD FAILED: the Cauchy/Szego identity drifted beyond tolerance.",
              file=sys.stderr)
        return 1
    if not payload["power_sum_identity_within_tolerance"]:
        print("GUARD FAILED: the power-sum identity for |Res(f, f*)| drifted "
              "beyond tolerance; Theorem (RS) as stated would be in question.",
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
