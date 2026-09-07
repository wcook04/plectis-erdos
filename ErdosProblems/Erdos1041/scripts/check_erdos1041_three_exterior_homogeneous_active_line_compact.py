#!/usr/bin/env python3
"""Exact rational B&B for the two homogeneous active-line profiles."""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction as F
from math import comb

from sympy.polys.domains import QQ
from sympy.polys.rings import ring


def iadd(left, right):
    return left[0] + right[0], left[1] + right[1]


def isub(left, right):
    return left[0] - right[1], left[1] - right[0]


def iscale(interval, scalar: F):
    if scalar >= 0:
        return scalar * interval[0], scalar * interval[1]
    return scalar * interval[1], scalar * interval[0]


def imul(left, right):
    values = (
        left[0] * right[0],
        left[0] * right[1],
        left[1] * right[0],
        left[1] * right[1],
    )
    return min(values), max(values)


def ipow_nonnegative(interval, exponent: int):
    assert interval[0] >= 0
    return interval[0] ** exponent, interval[1] ** exponent


def idiv_positive(numerator, denominator):
    assert denominator[0] > 0
    return imul(numerator, (1 / denominator[1], 1 / denominator[0]))


def isquare(interval):
    if interval[0] <= 0 <= interval[1]:
        return F(0), max(interval[0] ** 2, interval[1] ** 2)
    return min(interval[0] ** 2, interval[1] ** 2), max(
        interval[0] ** 2, interval[1] ** 2
    )


def build_intersection_gap(n: int):
    """Cleared gap on the exact double-active kernel alpha=-k(x+y), beta=ky."""
    polynomial_ring, X, Y, Q, t = ring("X,Y,Q,t", QQ)
    d = n - 3
    A = 3 * (1 + t)
    B = 2 * (1 - t)
    radial_den = (1 + X) * (1 + Y)
    own = (1 - Q * (1 + X)) ** 2
    spectator_1 = (
        B * (1 + Q * (1 + Y) + Q**2 * (1 + Y) ** 2)
        + 2 * Q * (1 + Y) * A * (X + Y)
    )
    spectator_2 = (
        B * (radial_den**2 + Q * radial_den + Q**2)
        - 2 * Q * radial_den * A * Y
    )
    regular_square = t ** (2 * d) * (1 - t**3) ** 2
    gap = B**2 * regular_square * radial_den**2 - Q ** (2 * d) * own * spectator_1 * spectator_2
    return gap


def affine_power_coefficients(poly, boxes):
    coefficients = {
        monomial: F(coefficient.numerator, coefficient.denominator)
        for monomial, coefficient in poly.items()
    }
    for axis, (left, right) in enumerate(boxes):
        width = right - left
        transformed = defaultdict(F)
        for monomial, coefficient in coefficients.items():
            exponent = monomial[axis]
            for new_exponent in range(exponent + 1):
                new_monomial = list(monomial)
                new_monomial[axis] = new_exponent
                transformed[tuple(new_monomial)] += (
                    coefficient
                    * comb(exponent, new_exponent)
                    * left ** (exponent - new_exponent)
                    * width**new_exponent
                )
        coefficients = {key: value for key, value in transformed.items() if value}
    return coefficients


def bernstein_data(poly, boxes):
    coefficients = affine_power_coefficients(poly, boxes)
    dimensions = len(boxes)
    degrees = [max((key[i] for key in coefficients), default=0) for i in range(dimensions)]
    for axis, degree in enumerate(degrees):
        grouped = defaultdict(dict)
        for monomial, coefficient in coefficients.items():
            other = monomial[:axis] + monomial[axis + 1 :]
            grouped[other][monomial[axis]] = coefficient
        transformed = {}
        for other, vector in grouped.items():
            for index in range(degree + 1):
                value = sum(
                    vector.get(power_index, F(0))
                    * F(comb(index, power_index), comb(degree, power_index))
                    for power_index in range(index + 1)
                )
                transformed[other[:axis] + (index,) + other[axis:]] = value
        coefficients = transformed
    return coefficients, tuple(degrees)


def subdivide_bernstein(coefficients, degrees, axis: int):
    """Midpoint de Casteljau subdivision along one tensor axis."""
    grouped = defaultdict(dict)
    for monomial, coefficient in coefficients.items():
        other = monomial[:axis] + monomial[axis + 1 :]
        grouped[other][monomial[axis]] = coefficient
    left = {}
    right = {}
    degree = degrees[axis]
    for other, vector_map in grouped.items():
        level = [vector_map[index] for index in range(degree + 1)]
        left_values = [level[0]]
        right_values = [None] * (degree + 1)
        right_values[degree] = level[-1]
        for row in range(1, degree + 1):
            level = [(level[index] + level[index + 1]) / 2 for index in range(len(level) - 1)]
            left_values.append(level[0])
            right_values[degree - row] = level[-1]
        for index in range(degree + 1):
            key = other[:axis] + (index,) + other[axis:]
            left[key] = left_values[index]
            right[key] = right_values[index]
    return left, right


INTERSECTION_GAPS = {degree: build_intersection_gap(degree) for degree in (5, 6)}


def data(n: int):
    if n == 5:
        tbox = F(7368, 10000), F(7369, 10000)
        radial = F(3, 4), F(29, 25)
        xbox = F(-1, 4), F(4, 25)
        qbox = F(0), F(4, 3)
    else:
        tbox = F(7937, 10000), F(7938, 10000)
        radial = F(4, 5), F(11, 10)
        xbox = F(-7, 40), F(1, 10)
        qbox = F(0), F(40, 33)
    d = n - 3
    assert tbox[0] ** 3 < F(d, n) < tbox[1] ** 3
    regular_lower = min((tt**d * (1 - tt**3)) ** 2 for tt in tbox)
    kbox = tuple(3 * (1 + tt) / (2 * (1 - tt)) for tt in tbox)
    bbox = 2 * (1 - tbox[1]), 2 * (1 - tbox[0])
    return d, tbox, radial, xbox, qbox, regular_lower, kbox, bbox


def geometry(box, kbox):
    x, y, q = box
    b0 = 1 + x[0], 1 + x[1]
    b1 = 1 + y[0], 1 + y[1]
    b01 = imul(b0, b1)
    b2 = 1 / b01[1], 1 / b01[0]
    s0 = imul(q, b0)
    s1 = imul(q, b1)
    s2 = imul(q, b2)
    p1 = iadd(iadd((F(1), F(1)), s1), imul(s1, s1))
    p2 = iadd(iadd((F(1), F(1)), s2), imul(s2, s2))
    R = iscale(imul(kbox, isub(x, y)), F(-1))
    S = iscale(imul(kbox, iadd(iscale(x, F(2)), y)), F(-1))
    return b0, b1, b2, s0, s1, s2, p1, p2, R, S


def stationary_interval(kind: str, q, b1, b2, p1, p2, R, S):
    """Return the exact interval extension of the line stationary point."""
    if kind == "R":
        # alpha=(b2 P1-2 b1(P2-q b2 R))/(4 q b1 b2).
        inner = isub(p2, imul(imul(q, b2), R))
        numerator = isub(imul(b2, p1), iscale(imul(b1, inner), F(2)))
        denominator = iscale(imul(imul(q, b1), b2), F(4))
    else:
        # alpha=(2 b2 P1-b1(P2-2 q b2 S))/(8 q b1 b2).
        inner = isub(p2, iscale(imul(imul(q, b2), S), F(2)))
        numerator = isub(iscale(imul(b2, p1), F(2)), imul(b1, inner))
        denominator = iscale(imul(imul(q, b1), b2), F(8))
    return idiv_positive(numerator, denominator)


def line_possible(kind: str, alpha, R, S) -> bool:
    if kind == "R":
        lowers = (
            (F(-1, 2), F(-1, 2)),
            iscale(isub(iscale(S, F(2)), R), F(1, 3)),
            iadd(R, (F(-3), F(-3))),
        )
        uppers = ((F(3, 2), F(3, 2)), iadd(R, (F(1), F(1))))
    else:
        lowers = (
            (F(-1, 2), F(-1, 2)),
            iscale(isub(S, (F(3, 2), F(3, 2))), F(1, 2)),
        )
        uppers = (
            (F(3, 2), F(3, 2)),
            iscale(iadd(S, (F(1, 2), F(1, 2))), F(1, 2)),
            iscale(isub(iscale(S, F(2)), R), F(1, 3)),
        )
    if max(row[0] for row in lowers) > min(row[1] for row in uppers):
        return False
    if alpha[1] < max(row[0] for row in lowers):
        return False
    if alpha[0] > min(row[1] for row in uppers):
        return False
    return True


def linear_candidate(kind: str, R, S):
    """The shared intersection or one of the four upper-cosine clips."""
    if kind == "I":
        alpha = iscale(isub(iscale(S, F(2)), R), F(1, 3))
        beta = iscale(isub(iscale(R, F(2)), S), F(1, 3))
    elif kind == "RA":
        alpha = F(3, 2), F(3, 2)
        beta = iscale(isub(R, alpha), F(1, 2))
    elif kind == "RB":
        alpha = isub(R, (F(3), F(3)))
        beta = F(3, 2), F(3, 2)
    elif kind == "SA":
        alpha = F(3, 2), F(3, 2)
        beta = isub(S, (F(3), F(3)))
    elif kind == "SB":
        beta = F(3, 2), F(3, 2)
        alpha = iscale(isub(S, beta), F(1, 2))
    else:
        raise ValueError(kind)
    return alpha, beta


def polygon_candidate_possible(alpha, beta, R, S) -> bool:
    if alpha[1] < F(-1, 2) or alpha[0] > F(3, 2):
        return False
    if beta[1] < F(-1, 2) or beta[0] > F(3, 2):
        return False
    f3 = isub(iadd(alpha, iscale(beta, F(2))), R)
    f4 = isub(iadd(iscale(alpha, F(2)), beta), S)
    return f3[1] >= 0 and f4[1] >= 0


def in_quantitative_collar(kind, box, alpha, R, S, tbox, bbox):
    delta = F(1, 50)
    x, y, q = box
    if x[0] < -delta or x[1] > delta or y[0] < -delta or y[1] > delta:
        return False
    # This inclusion is uniform for the actual algebraic t in tbox.
    if q[0] < tbox[1] - delta or q[1] > tbox[0] + delta:
        return False
    if kind == "R":
        beta = iscale(isub(R, alpha), F(1, 2))
        residual = isub(iadd(iscale(alpha, F(2)), beta), S)
    else:
        beta = isub(S, iscale(alpha, F(2)))
        residual = isub(iadd(alpha, iscale(beta, F(2))), R)
    # On the applicable active segment the residual is nonnegative.  Its
    # product with B=2(1-t) is respectively V or U in the collar theorem.
    return imul(bbox, residual)[1] <= delta


def profile_ratio(n, kind, box, regular_lower, kbox):
    d = n - 3
    b0, b1, b2, s0, _s1, _s2, p1, p2, R, S = geometry(box, kbox)
    q = box[2]
    if kind == "R":
        J = isub(
            iadd(imul(b2, p1), iscale(imul(b1, p2), F(2))),
            iscale(imul(imul(imul(q, b1), b2), R), F(2)),
        )
    elif kind == "S":
        J = isub(
            iadd(iscale(imul(b2, p1), F(2)), imul(b1, p2)),
            iscale(imul(imul(imul(q, b1), b2), S), F(2)),
        )
    else:
        alpha, beta = linear_candidate(kind, R, S)
        factor1 = isub(p1, iscale(imul(imul(q, b1), alpha), F(2)))
        factor2 = isub(p2, iscale(imul(imul(q, b2), beta), F(2)))
        own = imul(ipow_nonnegative(q, 2 * d), isquare(isub((F(1), F(1)), s0)))
        return own[1] * factor1[1] * factor2[1] / regular_lower
    own = imul(ipow_nonnegative(q, 2 * d), isquare(isub((F(1), F(1)), s0)))
    left_lower = 8 * b1[0] * b2[0] * regular_lower
    right_upper = own[1] * isquare(J)[1]
    return right_upper / left_lower


def profile_certified(n, kind, box, regular_lower, kbox):
    return profile_ratio(n, kind, box, regular_lower, kbox) < 1


def intersection_ratio_from_gap(box, tbox, gap_lower):
    """Convert a positive cleared-gap bound to H_I^2/C_n^2<1."""
    x, y, _q = box
    denominator_upper = (
        (2 * (1 - tbox[0])) ** 2
        * ((1 + x[1]) * (1 + y[1])) ** 2
    )
    assert gap_lower > 0 and denominator_upper > gap_lower
    return 1 - gap_lower / denominator_upper


def certify_profile(n: int, kind: str):
    d, tbox, radial, xbox, qbox, regular_lower, kbox, bbox = data(n)
    spans = (xbox[1] - xbox[0], xbox[1] - xbox[0], qbox[1] - qbox[0])
    if kind == "I":
        root_coefficients, bernstein_degrees = bernstein_data(
            INTERSECTION_GAPS[n], (xbox, xbox, qbox, tbox)
        )
        stack = [((xbox, xbox, qbox), 0, root_coefficients)]
    else:
        bernstein_degrees = None
        stack = [((xbox, xbox, qbox), 0, None)]
    nodes = discarded = collar = certified = maximum_depth = 0
    worst_ratio = F(0)
    while stack:
        box, depth, coefficients = stack.pop()
        nodes += 1
        maximum_depth = max(maximum_depth, depth)
        x, y, q = box
        b0, b1, b2, _s0, _s1, _s2, p1, p2, R, S = geometry(box, kbox)
        if b2[1] < radial[0] or b2[0] > radial[1] or q[0] > 1 / b0[0]:
            discarded += 1
            continue
        if kind == "I":
            alpha, beta = linear_candidate(kind, R, S)
            if not polygon_candidate_possible(alpha, beta, R, S):
                discarded += 1
                continue
            if (
                x[0] >= F(-1, 50)
                and x[1] <= F(1, 50)
                and y[0] >= F(-1, 50)
                and y[1] <= F(1, 50)
                and q[0] >= tbox[1] - F(1, 50)
                and q[1] <= tbox[0] + F(1, 50)
            ):
                collar += 1
                continue
            # Outside the excised equality collar the double-active kernel
            # also has a strict rational Bernstein margin.
            gap_lower = min(coefficients.values())
            if gap_lower > 0:
                ratio = intersection_ratio_from_gap(box, tbox, gap_lower)
                certified += 1
                worst_ratio = max(worst_ratio, ratio)
                continue
        ratio = profile_ratio(n, kind, box, regular_lower, kbox)
        if ratio < 1:
            certified += 1
            worst_ratio = max(worst_ratio, ratio)
            continue
        # q=0 is already certified above.  A non-certified box meeting zero
        # is subdivided before the stationary quotient is formed.
        if kind in ("R", "S") and q[0] > 0:
            alpha = stationary_interval(kind, q, b1, b2, p1, p2, R, S)
            if not line_possible(kind, alpha, R, S):
                discarded += 1
                continue
            if in_quantitative_collar(kind, box, alpha, R, S, tbox, bbox):
                collar += 1
                continue
        elif kind not in ("R", "S"):
            alpha, beta = linear_candidate(kind, R, S)
            if not polygon_candidate_possible(alpha, beta, R, S):
                discarded += 1
                continue
        assert depth < 60, (n, kind, box)
        widths = tuple((interval[1] - interval[0]) / span for interval, span in zip(box, spans))
        axis = max(range(3), key=lambda index: widths[index])
        midpoint = sum(box[axis], F(0)) / 2
        left = list(box)
        right = list(box)
        left[axis] = box[axis][0], midpoint
        right[axis] = midpoint, box[axis][1]
        if kind == "I":
            left_coefficients, right_coefficients = subdivide_bernstein(
                coefficients, bernstein_degrees, axis
            )
        else:
            left_coefficients = right_coefficients = None
        stack.append((tuple(right), depth + 1, right_coefficients))
        stack.append((tuple(left), depth + 1, left_coefficients))
    print(
        f"n={n} line={kind}: nodes={nodes} discarded={discarded} "
        f"collar={collar} certified={certified} depth={maximum_depth} "
        f"worst_ratio<{float(worst_ratio):.12f}"
    )
    assert certified > 0
    if kind == "I":
        assert collar > 0
    return nodes, discarded, collar, certified, maximum_depth, worst_ratio


def main() -> None:
    kinds = ("R", "S", "I", "RA", "RB", "SA", "SB")
    rows = [certify_profile(n, kind) for n in (5, 6) for kind in kinds]
    assert len(rows) == 14
    assert max(row[5] for row in rows) < F(99_999_999, 100_000_000)
    print("uniform active-line ratio < 99999999/100000000")
    print("PASS exact compact homogeneous active-line atlas")


if __name__ == "__main__":
    main()
