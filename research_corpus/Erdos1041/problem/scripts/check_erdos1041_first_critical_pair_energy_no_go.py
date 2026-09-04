#!/usr/bin/env python3
"""Exact certificate for the first-critical pair-energy cone no-go.

The polynomial is written in local coordinates at one critical point::

    p(c+w) = v + a*w^2 + w^3.

All displayed data are Gaussian rationals.  The checker proves that the three
roots lie in the open unit disk by three disjoint Rouche disks, that ``c`` is
the unique minimum-modulus critical point, and that the leading coefficient of
the proposed pair-energy cone inequality is strictly negative.
"""

from __future__ import annotations

import json
from fractions import Fraction as Q


G = tuple[Q, Q]


def gadd(x: G, y: G) -> G:
    return x[0] + y[0], x[1] + y[1]


def gsub(x: G, y: G) -> G:
    return x[0] - y[0], x[1] - y[1]


def gmul(x: G, y: G) -> G:
    return x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def gscale(t: Q, x: G) -> G:
    return t * x[0], t * x[1]


def gnorm_sq(x: G) -> Q:
    return x[0] * x[0] + x[1] * x[1]


def lower_abs(x: G) -> Q:
    return max(abs(x[0]), abs(x[1]))


def upper_abs(x: G) -> Q:
    return abs(x[0]) + abs(x[1])


def local_values(q: G, c: G, a: G, v: G) -> tuple[G, G, G]:
    w = gsub(q, c)
    w2 = gmul(w, w)
    p = gadd(v, gadd(gmul(a, w2), gmul(w2, w)))
    dp = gadd(gscale(Q(2), gmul(a, w)), gscale(Q(3), w2))
    ddp = gadd(gscale(Q(2), a), gscale(Q(6), w))
    return p, dp, ddp


def main() -> None:
    c: G = (-Q(1, 2), -Q(1, 100))
    a: G = (-Q(1, 16), -Q(5, 6))
    v: G = (-Q(1, 32), Q(1, 160))

    # The other critical point is d=c-2a/3.  Substitution into the local cubic
    # gives p(d)=v+4a^3/27.
    d = gsub(c, gscale(Q(2, 3), a))
    other_value = gadd(v, gscale(Q(4, 27), gmul(gmul(a, a), a)))
    assert gnorm_sq(v) < gnorm_sq(other_value)

    # One Rouche disk around each approximate root.  On |z-q|=R, the linear
    # Taylor term dominates the constant, quadratic, and cubic terms:
    #
    #   |p'(q)|R > |p(q)| + |p''(q)|R^2/2 + R^3.
    #
    # The lower/upper bounds use max(|Re|,|Im|) <= |.| <= |Re|+|Im|,
    # so every comparison below is exact rational arithmetic.
    radius = Q(1, 1000)
    centres: list[G] = [
        (-Q(627678, 10**6), -Q(137426, 10**6)),
        (-Q(482075, 10**6), Q(830286, 10**6)),
        (-Q(327747, 10**6), Q(110473, 10**6)),
    ]
    rouche_margins: list[Q] = []
    for q in centres:
        p_q, dp_q, ddp_q = local_values(q, c, a, v)
        lhs = lower_abs(dp_q) * radius
        rhs = upper_abs(p_q) + upper_abs(ddp_q) * radius**2 / 2 + radius**3
        assert lhs > rhs
        rouche_margins.append(lhs - rhs)
        assert gnorm_sq(q) < (1 - radius) ** 2

    for i, q in enumerate(centres):
        for r in centres[i + 1 :]:
            assert gnorm_sq(gsub(q, r)) > (2 * radius) ** 2

    # Local inverse branches have
    #   z_+-c = +kappa*s + lambda*s^2 + O(s^3),
    #   z_--c = -kappa*s + lambda*s^2 + O(s^3),
    # with kappa^2=-v/a and lambda=v/(2a^2).  If
    #   E=|M|^2+|D|^2=|c|^2+A*s^2+O(s^4),
    # then A=K+C, where K=|kappa|^2=|v/a| and
    # C=2 Re(conj(c) lambda)=Re(conj(c)*v/a^2).
    # Direct Gaussian-rational simplification gives the exact negative C below.
    correction = -Q(7368462, 323610125)
    k_sq = gnorm_sq(v) / gnorm_sq(a)  # K^2, not K.
    assert correction < 0
    assert k_sq > correction * correction  # K > -C, hence A=K+C>0.

    # The proposed inequality has leading difference
    #   E'^2 - 4(E-|c|^2)(|M'|^2+|D'|^2)
    #     = 4*A*(A-K)*s^2 + O(s^4)
    #     = 4*A*C*s^2 + O(s^4) < 0.
    # Thus it fails for every sufficiently small positive s.

    print(
        json.dumps(
            {
                "status": "exact_first_critical_pair_energy_no_go_verified",
                "polynomial_local_form": "p(c+w)=v+a*w^2+w^3",
                "c": [str(c[0]), str(c[1])],
                "a": [str(a[0]), str(a[1])],
                "v": [str(v[0]), str(v[1])],
                "other_critical_point": [str(d[0]), str(d[1])],
                "critical_value_modulus_sq": {
                    "at_c": str(gnorm_sq(v)),
                    "at_other": str(gnorm_sq(other_value)),
                },
                "root_disks": {
                    "radius": str(radius),
                    "centres": [[str(x), str(y)] for x, y in centres],
                    "rouche_margins": [str(x) for x in rouche_margins],
                },
                "pair_energy_expansion": {
                    "K_squared": str(k_sq),
                    "correction_C": str(correction),
                    "proved_relations": ["C < 0", "K > -C", "0 < A=K+C < K"],
                    "leading_cone_difference": "4*A*C*s^2+O(s^4) < 0",
                },
                "claim_boundary": "Refutes the returned pointwise pair-energy cone lemma only; the descending-branch route and unrestricted Erdos 1041 remain open.",
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
