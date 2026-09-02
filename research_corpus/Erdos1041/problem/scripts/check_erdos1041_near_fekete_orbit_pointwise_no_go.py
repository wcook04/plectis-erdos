#!/usr/bin/env python3
"""High-precision no-go for pointwise complete-orbit charge positivity.

This checks one degree-four near-Fekete model at the exact algebraic seed
``nu_0 = (12 + 5 i)/13`` and common value increment ``s = 5``.  The six
branch endpoints are selected by the source-current guarded homotopy tracer,
then independently refined at 80 and 120 decimal digits.  The total signed
charge density is strictly negative with a margin above ``0.12``.

The result eliminates a pointwise fan-in of the cyclic orbit.  It does not
refute positivity after integration in ``s``, the componentwise combined
charge, COVER, or Erdős 1041.
"""

from __future__ import annotations

import bisect
import cmath
import importlib.util
import math
from pathlib import Path

from mpmath import mp


HERE = Path(__file__).resolve().parent
SOURCE_TRACER = HERE / "check_erdos1041_per_hub_charge_sign.py"


def _load_source_tracer():
    spec = importlib.util.spec_from_file_location("erdos1041_per_hub_charge", SOURCE_TRACER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {SOURCE_TRACER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _guarded_endpoint(tracer, nu: complex, sign: int, tau: float) -> complex:
    intervals = tracer._trace(4, nu, sign, tau * 1.001, 1.0e-12)
    if not intervals:
        raise AssertionError("guarded tracer returned no branch intervals")
    ends = [row[1] for row in intervals]
    index = bisect.bisect_left(ends, tau)
    if index >= len(intervals):
        raise AssertionError("guarded tracer stopped before the target parameter")
    ta, tb, ha, hb = intervals[index]
    prediction = ha + (hb - ha) * (tau - ta) / (tb - ta)
    endpoint, residual = tracer._newton(prediction, nu.conjugate() * tau * tau, 4)
    if residual > 1.0e-12:
        raise AssertionError(f"float branch residual too large: {residual}")
    return endpoint


def _high_precision_total(dps: int) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    tracer = _load_source_tracer()
    mp.dps = dps
    s = mp.mpf(5)
    tau = math.sqrt(5.0)
    zeta = -mp.mpf(1) / 2 + mp.j * mp.sqrt(3) / 2
    seed = mp.mpc(12, 5) / 13
    if abs(abs(seed) - 1) > mp.mpf(10) ** (-(dps - 10)):
        raise AssertionError("the algebraic seed is not unit")

    total = mp.mpf(0)
    worst_residual = mp.mpf(0)
    minimum_other_saddle_separation = mp.inf
    for orbit_index in range(3):
        nu_mp = seed * zeta**orbit_index
        nu_float = complex(nu_mp)
        for sign in (1, -1):
            float_h = _guarded_endpoint(tracer, nu_float, sign, tau)
            target = mp.conj(nu_mp) * s

            def equation(h):
                t = 1 + h
                return t**4 - 4 * t + 3 - target

            h = mp.findroot(equation, mp.mpc(float_h.real, float_h.imag), solver="mnewton")
            residual = abs(equation(h))
            worst_residual = max(worst_residual, residual)
            if abs(complex(h) - float_h) > 2.0e-12:
                raise AssertionError("high-precision root does not match the guarded branch")

            for j in (1, 2):
                other_critical_h = zeta**j - 1
                minimum_other_saddle_separation = min(
                    minimum_other_saddle_separation, abs(h - other_critical_h)
                )

            t = 1 + h
            phi_prime = 4 * t**3 - 4
            phi_second = 12 * t**2
            support = mp.im(nu_mp * t * phi_prime) / abs(phi_prime)
            turning_density = -mp.im(mp.conj(nu_mp) * phi_second / phi_prime**2)
            total += support * turning_density

    return total, worst_residual, minimum_other_saddle_separation


def main() -> None:
    total_80, residual_80, separation_80 = _high_precision_total(80)
    total_120, residual_120, separation_120 = _high_precision_total(120)

    if not total_80 < mp.mpf("-0.12"):
        raise AssertionError(f"pointwise orbit total lost its negative margin: {total_80}")
    if abs(total_80 - total_120) > mp.mpf("1e-60"):
        raise AssertionError("80- and 120-digit evaluations disagree")
    if max(residual_80, residual_120) > mp.mpf("1e-70"):
        raise AssertionError("high-precision polynomial residual is too large")
    if min(separation_80, separation_120) < mp.mpf("0.35"):
        raise AssertionError("a witness branch is too close to another saddle")

    print("NEAR-FEKETE ORBIT POINTWISE NO-GO: PASS")
    print("total_charge_density", mp.nstr(total_120, 40))
    print("minimum_other_saddle_separation", mp.nstr(separation_120, 30))
    print("worst_polynomial_residual", mp.nstr(residual_120, 8))


if __name__ == "__main__":
    main()
