#!/usr/bin/env python3
"""Deterministic checks for the six-return Erdős 1041 assimilation.

The checker replays the two locally strengthened scalar steps exactly and
audits representative retained identities.  Geometry and analytic change of
variables remain proved in the companion Markdown source; floating sweeps are
regressions, never replacements for those proofs.
"""

from __future__ import annotations

from fractions import Fraction as F
import math
import random

import sympy as sp


def check_leaf_charge_integral() -> None:
    t, sigma, deriv = sp.symbols("t sigma deriv", positive=True)
    integrand = t**2 / deriv**2 / t
    primitive = sp.integrate(integrand, (t, 0, sigma))
    assert sp.simplify(primitive - sigma**2 / (2 * deriv**2)) == 0


def check_node_excess_regression() -> None:
    # These high-energy representatives make the positive excess visible on a
    # fixed double-precision mesh.  For arbitrary positive energy, positivity
    # is an analytic near-birth statement proved in the companion note; the
    # witnessing interval can be exponentially thinner than this mesh.
    for k in range(2, 33):
        for beta, delta, energy in (
            (0.01, 0.9, 100.0),
            (0.25, 0.5, 100.0),
            (0.9, 0.999, 100.0),
        ):
            excess = 0.0
            previous_t = beta
            for j in range(1, 20001):
                t = beta + (delta - beta) * j / 20000
                q = beta / t
                lam = math.log(
                    (1 + q ** (2.0 / k)) / (1 - q ** (2.0 / k))
                )
                bergman = 2.0 / lam
                leaf_energy = t ** (2.0 / k) * energy
                excess += max(leaf_energy - bergman, 0.0) * (t - previous_t) / t
                previous_t = t
            assert excess > 0.0


def check_spectral_convexity_derivatives() -> None:
    x = sp.symbols("x", positive=True)
    phi = x - 1 - sp.log(x)
    below = phi - (x - 1) ** 2 / 2
    above = phi - (x - 1) ** 2 / (2 * x)
    assert sp.simplify(sp.diff(below, x) + (x - 1) ** 2 / x) == 0
    assert sp.simplify(sp.diff(above, x) - (x - 1) ** 2 / (2 * x**2)) == 0
    assert below.subs(x, 1) == 0
    assert above.subs(x, 1) == 0


def check_spectral_convexity_regression() -> None:
    for m in (1.0, 1.01, 1.5, 2.0, 5.0, 25.0, 100.0):
        for j in range(1, 5000):
            x = m * j / 5000
            phi = x - 1 - math.log(x)
            new_rhs = (x - 1) ** 2 / (2 * m)
            old_rhs = (x - 1) ** 2 / (2 * m * m)
            assert phi + 1e-14 >= new_rhs
            assert new_rhs + 1e-14 >= old_rhs


def check_trace_product_spectral_samples() -> None:
    rng = random.Random(1041)
    for n in range(2, 65):
        for _ in range(200):
            raw = [math.exp(rng.uniform(-2.0, 2.0)) for _ in range(n)]
            scale = n / sum(raw)
            eig = [scale * value for value in raw]
            delta = math.prod(eig)
            if not (0.0 < delta <= 1.0 + 1e-12):
                continue
            m = max(eig)
            defect = sum((value - 1.0) ** 2 for value in eig)
            entropy = -math.log(delta)
            assert defect <= 2 * m * entropy + 1e-9


def check_cubic_ratio_certificate() -> None:
    def sub(z: tuple[F, F], w: tuple[F, F]) -> tuple[F, F]:
        return z[0] - w[0], z[1] - w[1]

    def mul(z: tuple[F, F], w: tuple[F, F]) -> tuple[F, F]:
        return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]

    def scale(c: F, z: tuple[F, F]) -> tuple[F, F]:
        return c * z[0], c * z[1]

    def abs2(z: tuple[F, F]) -> F:
        return z[0] * z[0] + z[1] * z[1]

    one = (F(1), F(0))
    a = (F(-1, 1000), F(9, 10))
    a2 = mul(a, a)
    p = scale(F(-4, 27), mul(sub(a2, one), sub(a2, one)))
    discriminant_ratio = F(121337022963, 250000000000)
    assert abs2(p) == discriminant_ratio**2
    assert discriminant_ratio < F(1, 2)


def check_translated_cut_constants() -> None:
    expected = {
        2: F(1),
        3: F(4, 9),
        4: F(3, 16),
        5: F(2, 25),
        6: F(5, 144),
        8: F(7, 1024),
        10: F(9, 6400),
    }
    for n, target in expected.items():
        tau = F(16 * (n - 1), n * n * 2**n)
        assert tau == target
        assert 0 < tau <= 1


def check_angular_action_scalar_fan_in() -> None:
    rng = random.Random(260826)
    for n in range(2, 100):
        for _ in range(100):
            lengths = [rng.random() for _ in range(n)]
            total = sum(lengths)
            if total == 0:
                continue
            radius = total / n
            lengths.sort()
            for q in (1, 2, max(1, n // 2), n):
                assert sum(lengths[:q]) <= q * radius + 1e-12


def main() -> None:
    check_leaf_charge_integral()
    check_node_excess_regression()
    check_spectral_convexity_derivatives()
    check_spectral_convexity_regression()
    check_trace_product_spectral_samples()
    check_cubic_ratio_certificate()
    check_translated_cut_constants()
    check_angular_action_scalar_fan_in()
    print("PASS: exact singleton leaf-charge integral and positive node-excess regression")
    print("PASS: one-ceiling spectral convexity identities and regression")
    print("PASS: dimension-free spectral fan-in samples through degree 64")
    print("PASS: exact cubic ratio-only no-go certificate")
    print("PASS: translated-cut constants and angular-action scalar fan-in")


if __name__ == "__main__":
    main()
