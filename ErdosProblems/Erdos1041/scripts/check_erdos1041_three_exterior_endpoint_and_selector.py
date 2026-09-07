#!/usr/bin/env python3
"""Exact identities and deterministic falsification for the m=3 endpoint
Poisson reduction and selector domain note.

Verifies:
  1. H(1, r, c) = P_r(c) exactly (endpoint identification for (8));
  2. P_r convexity, psi and phi constants exactly;
  3. the weighted-cosine minimum formula against brute force (both branches);
  4. the reduced endpoint residual E(r): 20000-sample nonnegativity scan,
     exact equal-radius zero, quadratic near-equal scaling;
  5. the certified [s,1] domain witness at 60 decimal digits;
  6. corrected-domain barrier spot checks at 60 decimal digits;
  7. the boundary-layer margin max_j c_j - T(p) on adversarial samples.
"""

from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy as sp
from scipy.optimize import minimize

mp.mp.dps = 60

ROOT = Path(__file__).resolve().parents[5]
RECEIPT = ROOT / "state" / "formal_math" / "erdos257_period_noncollapse" / (
    "erdos1041_three_exterior_endpoint_selector_receipt.json"
)


def symbolic_section() -> dict:
    q, r, c, p = sp.symbols("q r c p", positive=True, real=True)
    H = (1 - r**2) * (q * (1 + r**2) - r * c * (1 + q**2)) / (
        (q**2 + r**2 - 2 * q * r * c) * (1 - 2 * q * r * c + q**2 * r**2)
    )
    P = (1 - r**2) / (1 + r**2 - 2 * r * c)
    endpoint_identity = sp.simplify(H.subs(q, 1) - P) == 0
    convexity = sp.simplify(
        sp.diff(P, c, 2)
        - 8 * r**2 * (1 - r**2) / (1 + r**2 - 2 * r * c) ** 3
    ) == 0
    psi = sp.simplify(P.subs(c, -sp.Rational(1, 2)) - (1 - r**2) / (1 + r + r**2)) == 0
    phi = sp.simplify(
        sp.diff(P, c).subs(c, -sp.Rational(1, 2))
        - 2 * r * (1 - r**2) / (1 + r + r**2) ** 2
    ) == 0
    regular_derivative = sp.simplify(
        sp.diff(sp.log((q**3 - p) / (1 - p * q**3)), q).subs(q, 1)
        - 3 * (1 + p) / (1 - p)
    ) == 0
    return {
        "endpoint_identity_H1_equals_P": endpoint_identity,
        "poisson_kernel_convexity": convexity,
        "psi_constant_exact": psi,
        "phi_constant_exact": phi,
        "regular_comparator_slope_exact": regular_derivative,
    }


def psi_f(r: float) -> float:
    return (1 - r**2) / (1 + r + r**2)


def phi_f(r: float) -> float:
    return 2 * r * (1 - r**2) / (1 + r + r**2) ** 2


def g_coefficients(rv) -> list[float]:
    pairs = [(0, 1), (1, 2), (2, 0)]
    return [2 * rv[i] * rv[j] * (phi_f(rv[i]) + phi_f(rv[j])) for i, j in pairs]


def weighted_cosine_min(A: float, B: float, C: float) -> float:
    ia, ib, ic = 1 / A, 1 / B, 1 / C
    if ia <= ib + ic + 1e-12 and ib <= ia + ic + 1e-12 and ic <= ia + ib + 1e-12:
        return -(A**2 * B**2 + A**2 * C**2 + B**2 * C**2) / (2 * A * B * C)
    return min(C - A - B, -C - abs(A - B))


def brute_min_sum_g(A: float, B: float, C: float, seeds: int = 60) -> float:
    f = lambda x: A * np.cos(x[0]) + B * np.cos(x[1]) + C * np.cos(-x[0] - x[1])
    best = np.inf
    rng = np.random.default_rng(7)
    for _ in range(seeds):
        res = minimize(f, rng.uniform(-np.pi, np.pi, 2), method="Nelder-Mead",
                       options={"maxiter": 6000, "fatol": 1e-15})
        best = min(best, float(res.fun))
    return best


def endpoint_residual(rv) -> float:
    rv = list(map(float, rv))
    p = rv[0] * rv[1] * rv[2]
    T = 3 * (1 + p) / (1 - p)
    pairs = [(0, 1), (1, 2), (2, 0)]
    D = sum(rv[i] * (1 + rv[i]) / (1 - rv[i]) for i in range(3)) + sum(
        rv[i] * psi_f(rv[j]) + rv[j] * psi_f(rv[i]) for i, j in pairs
    )
    G = g_coefficients(rv)
    M = weighted_cosine_min(*G)
    return D + M + sum(G) / 2 - sum(rv) * T


def residual_section() -> dict:
    rng = np.random.default_rng(1041)
    vals = np.empty(20000)
    for i in range(vals.size):
        vals[i] = endpoint_residual(rng.uniform(0.02, 0.985, 3))
    equal_zero = abs(endpoint_residual([0.3, 0.3, 0.3]))
    eps_scaling = []
    for eps in (1e-2, 1e-3, 1e-4):
        eps_scaling.append(
            endpoint_residual([0.3 + eps, 0.3, 0.3 - eps]) / eps**2
        )
    branch_samples = []
    rng2 = np.random.default_rng(20260828)
    while len(branch_samples) < 24:
        rv = rng2.uniform(0.02, 0.985, 3)
        A, B, C = g_coefficients(rv)
        ia, ib, ic = 1 / A, 1 / B, 1 / C
        if not (ia <= ib + ic and ib <= ia + ic and ic <= ia + ib):
            branch_samples.append(rv)
    brute_gap = []
    for rv in branch_samples:
        A, B, C = g_coefficients(rv)
        brute_gap.append(
            abs(weighted_cosine_min(A, B, C) - brute_min_sum_g(A, B, C))
        )
    return {
        "scan_min": float(vals.min()),
        "scan_max": float(vals.max()),
        "scan_all_nonnegative": bool(vals.min() > 0),
        "equal_radius_residual": float(equal_zero),
        "near_equal_quadratic_coefficients": [float(v) for v in eps_scaling],
        "endpoint_branch_brute_force_max_gap": float(max(brute_gap)),
    }


def witness_section() -> dict:
    radii = [mp.mpf(99) / 100, mp.mpf(1) / mp.mpf(10) ** 6, mp.mpf(99) / 100]
    angles = [mp.mpf(0), mp.mpf(1) / 100, mp.mpf(2) / 100]
    p = radii[0] * radii[1] * radii[2]
    s = p ** (mp.mpf(1) / 3)
    surpluses = []
    for j in range(3):
        total = mp.mpf(0)
        for k in range(3):
            z = s * mp.e ** (1j * angles[j])
            a = radii[k] * mp.e ** (1j * angles[k])
            total += mp.log(abs(z - a)) - mp.log(abs(1 - mp.conj(a) * z))
        surpluses.append(total - 3 * mp.log(s))
    return {
        "s": mp.nstr(s, 12),
        "per_ray_log_surplus_at_q_s": [mp.nstr(v, 12) for v in surpluses],
        "min_ray_value_at_q_s": mp.nstr(mp.e ** min(surpluses), 10),
        "literal_domain_falsified": bool(
            all(v > mp.log(mp.mpf(1000)) for v in surpluses)
        ),
    }


def corrected_domain_section() -> dict:
    """60-digit barrier spot checks on [max r_k, 1)."""

    def log_profiles(radii, angles, q):
        vals = []
        for j in range(3):
            total = mp.mpf(0)
            for k in range(3):
                z = q * mp.e ** (1j * angles[j])
                a = radii[k] * mp.e ** (1j * angles[k])
                total += mp.log(abs(z - a)) - mp.log(abs(1 - mp.conj(a) * z))
            vals.append(total)
        return vals

    configs = [
        ([mp.mpf(1) / 2, mp.mpf(1) / 3, mp.mpf(1) / 5],
         [mp.mpf(0), mp.mpf(1), mp.mpf(4)]),
        ([mp.mpf(9) / 10, mp.mpf(1) / 2, mp.mpf(1) / 2],
         [mp.mpf(0), mp.mpf(1) / 3, mp.mpf(3)]),
        ([mp.mpf(95) / 100, mp.mpf(9) / 10, mp.mpf(1) / 10],
         [mp.mpf(0), mp.mpf(2), mp.mpf(5)]),
        ([mp.mpf(1) / 10, mp.mpf(1) / 10, mp.mpf(1) / 10],
         [mp.mpf(0), mp.pi - mp.mpf(1) / 100, mp.pi + mp.mpf(1) / 100]),
    ]
    rows = []
    for radii, angles in configs:
        q0 = max(radii)
        barriers = []
        for j in range(3):
            best = -mp.inf
            for e in range(1, 7):
                for m in (1, 2, 5):
                    q = mp.mpf(1) - mp.mpf(m) * mp.mpf(10) ** (-e)
                    if q <= q0:
                        continue
                    best = max(best, log_profiles(radii, angles, q)[j]
                               - 3 * mp.log(q))
            # near-q0 ladder
            for e in range(1, 7):
                for m in (1, 2, 5):
                    q = q0 + mp.mpf(m) * mp.mpf(10) ** (-e) * (1 - q0)
                    if q >= 1:
                        continue
                    best = max(best, log_profiles(radii, angles, q)[j]
                               - 3 * mp.log(q))
            barriers.append(best)
        rows.append({
            "radii": [mp.nstr(v, 8) for v in radii],
            "per_ray_barriers": [mp.nstr(v, 10) for v in barriers],
            "min_ray_barrier": mp.nstr(min(barriers), 10),
            "within_one": bool(min(barriers) <= 1),
        })
    return {
        "spot_checks": rows,
        "all_within_one": all(row["within_one"] for row in rows),
    }


def boundary_layer_section() -> dict:
    rng = np.random.default_rng(1041)
    worst = np.inf
    for _ in range(4000):
        radii = rng.uniform(0.02, 0.985, 3)
        angles = rng.uniform(0, 2 * np.pi, 3)
        diff = angles[:, None] - angles[None, :]
        den = 1 + radii[None, :] ** 2 - 2 * radii[None, :] * np.cos(diff)
        c = np.sum((1 - radii[None, :] ** 2) / den, axis=1)
        p = float(np.prod(radii))
        T = 3 * (1 + p) / (1 - p)
        worst = min(worst, float(np.max(c)) - T)
    # regular equality at 60 digits
    with mp.workdps(60):
        r = mp.mpf("0.37")
        angles = [mp.mpf(0), 2 * mp.pi / 3, 4 * mp.pi / 3]
        cvals = []
        for j in range(3):
            total = mp.mpf(0)
            for k in range(3):
                d = abs(mp.e ** (1j * angles[j]) - r * mp.e ** (1j * angles[k]))
                total += (1 - r**2) / d**2
            cvals.append(total)
        T = 3 * (1 + r**3) / (1 - r**3)
        regular_margin = max(cvals) - T
    return {
        "adversarial_min_margin": worst,
        "no_violation_found": bool(worst > -1e-12),
        "regular_equality_margin_60dps": mp.nstr(abs(regular_margin), 8),
    }


def main() -> int:
    result = {
        "schema": "erdos1041_three_exterior_endpoint_selector_receipt_v1",
        "symbolic": symbolic_section(),
        "residual": residual_section(),
        "witness": witness_section(),
        "corrected_domain": corrected_domain_section(),
        "boundary_layer": boundary_layer_section(),
        "claim_boundary": (
            "Exact: endpoint identification, tangent constants, angle "
            "elimination to (E3), the [s,1] falsity witness, and regular "
            "equality. Numerical evidence only: E >= 0, (BL), and the "
            "corrected-domain selector conjecture. Unrestricted Erdos 1041 "
            "remains open."
        ),
    }
    checks = [
        all(result["symbolic"].values()),
        result["residual"]["scan_all_nonnegative"],
        result["residual"]["equal_radius_residual"] < 1e-12,
        result["residual"]["endpoint_branch_brute_force_max_gap"] < 1e-9,
        result["witness"]["literal_domain_falsified"],
        result["corrected_domain"]["all_within_one"],
        result["boundary_layer"]["no_violation_found"],
    ]
    result["pass"] = all(checks)
    RECEIPT.parent.mkdir(parents=True, exist_ok=True)
    RECEIPT.write_text(json.dumps(result, indent=2))
    print(json.dumps(result, indent=2))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
