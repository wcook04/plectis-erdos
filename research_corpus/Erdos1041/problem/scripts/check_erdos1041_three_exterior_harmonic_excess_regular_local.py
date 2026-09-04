#!/usr/bin/env python3
"""Exact stationary-arc replay for harmonic-excess local stability."""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from math import comb

import sympy as sp


q, s, n, z, t, y, v = sp.symbols("q s n z t y v", positive=True, real=True)
u, delta = sp.symbols("u delta", real=True)


def single_factor_atoms() -> dict[str, dict[str, sp.Expr]]:
    radius = s * sp.exp(u)
    numerator = q**2 + radius**2 - 2 * q * radius * sp.cos(delta)
    denominator = 1 + q**2 * radius**2 - 2 * q * radius * sp.cos(delta)
    factor = sp.Rational(1, 2) * (sp.log(numerator) - sp.log(denominator))
    names = {
        "r": sp.diff(factor, u),
        "a": sp.diff(factor, delta),
        "rr": sp.diff(factor, u, 2),
        "ra": sp.diff(factor, u, delta),
        "aa": sp.diff(factor, delta, 2),
        "rq": sp.diff(factor, u, q),
        "aq": sp.diff(factor, delta, q),
        "qq": sp.diff(factor, q, 2),
    }
    return {
        kind: {
            name: sp.factor(value.subs({u: 0, delta: angle}))
            for name, value in names.items()
        }
        for kind, angle in (
            ("self", 0),
            ("plus", 2 * sp.pi / 3),
            ("minus", -2 * sp.pi / 3),
        )
    }


def reflection_data() -> tuple[sp.Matrix, sp.Matrix]:
    atoms = single_factor_atoms()
    base_angles = [0, 2 * sp.pi / 3, 4 * sp.pi / 3]
    radial = [sp.Integer(1), -sp.Rational(1, 2), -sp.Rational(1, 2)]
    angular = [0, 1 / sp.sqrt(3), -1 / sp.sqrt(3)]

    def factor_kind(j: int, k: int) -> str:
        if j == k:
            return "self"
        return "plus" if sp.sin(base_angles[j] - base_angles[k]) > 0 else "minus"

    common_qq = n / q**2 + atoms["self"]["qq"] + 2 * atoms["plus"]["qq"]
    gradients: list[list[sp.Expr]] = []
    summed_hessian = sp.zeros(2)
    for j in range(3):
        gx = gy = qx = qy = 0
        hessian = sp.zeros(2)
        for k in range(3):
            atom = atoms[factor_kind(j, k)]
            radial_speed = radial[k]
            angular_speed = angular[j] - angular[k]
            gx += atom["r"] * radial_speed
            gy += atom["a"] * angular_speed
            qx += atom["rq"] * radial_speed
            qy += atom["aq"] * angular_speed
            hessian[0, 0] += atom["rr"] * radial_speed**2
            hessian[0, 1] += atom["ra"] * radial_speed * angular_speed
            hessian[1, 0] += atom["ra"] * radial_speed * angular_speed
            hessian[1, 1] += atom["aa"] * angular_speed**2
        mixed_q = sp.Matrix([qx, qy])
        hessian -= mixed_q * mixed_q.T / common_qq
        gradients.append([sp.factor(gx), sp.factor(gy)])
        summed_hessian += hessian

    gradient_matrix = sp.Matrix(gradients)
    assert sp.simplify(sum(gradient_matrix[:, 0])) == 0
    assert sp.simplify(sum(gradient_matrix[:, 1])) == 0
    stationary_n = (
        3 * q**3 / (q**3 - s**3)
        + 3 * s**3 * q**3 / (1 - s**3 * q**3)
    )
    return summed_hessian.subs(n, stationary_n), gradient_matrix.T * gradient_matrix


def parameter_power(degree: int) -> int:
    """Power k in t^k=stationary_ordinate for the rationalized parameter."""
    return 3 if degree % 2 else 6


def substitution_unit(degree: int) -> int:
    """Use t=s^2 in odd degree and t=s in even degree."""
    return 2 if degree % 2 else 1


def parity_convert(expression: sp.Expr, unit: int) -> tuple[sp.Expr, int]:
    polynomial = sp.Poly(sp.expand(expression), s)
    minimum = min(degree for (degree,), _ in polynomial.terms())
    if any((degree - minimum) % unit for (degree,), _ in polynomial.terms()):
        raise AssertionError("incompatible s-powers after q=s*z substitution")
    converted = sum(
        coefficient * t ** ((degree - minimum) // unit)
        for (degree,), coefficient in polynomial.terms()
    )
    return sp.expand(converted), minimum


def reduced_ratio(
    numerator: sp.Expr, denominator: sp.Expr, relation: sp.Expr
) -> tuple[sp.Expr, sp.Expr]:
    reduced_numerator = sp.cancel(sp.rem(numerator, relation, t))
    reduced_denominator = sp.cancel(sp.rem(denominator, relation, t))
    an, ad = sp.fraction(reduced_numerator)
    bn, bd = sp.fraction(reduced_denominator)
    return sp.factor(an * bd), sp.factor(ad * bn)


def reduced_hessian(
    degree: int,
    summed_hessian: sp.Matrix,
    variance: sp.Matrix,
    smooth_power: int = 2,
    include_determinant: bool = True,
) -> tuple[tuple[sp.Expr, sp.Expr], tuple[sp.Expr, sp.Expr]]:
    barrier = q ** (-degree) * (q**3 - s**3) / (1 - s**3 * q**3)
    variance_coefficient = (
        barrier * (smooth_power * barrier + 1) / (3 * (barrier - 1))
    )
    unit = substitution_unit(degree)
    power = parameter_power(degree)
    relation = (
        t**power * z**3 * (degree * z**3 - degree - 3)
        - ((degree - 3) * z**3 - degree)
    )
    entries: list[tuple[sp.Expr, sp.Expr]] = []
    for i, j in ((0, 0), (0, 1), (1, 1)):
        entry = sp.cancel(
            barrier * sp.Rational(1, 3) * summed_hessian[i, j]
            - variance_coefficient * variance[i, j]
        )
        raw_numerator, raw_denominator = sp.fraction(entry.subs(q, s * z))
        numerator, numerator_shift = parity_convert(raw_numerator, unit)
        denominator, denominator_shift = parity_convert(raw_denominator, unit)
        numerator, denominator = reduced_ratio(numerator, denominator, relation)
        shift = numerator_shift - denominator_shift
        if shift % unit:
            raise AssertionError("incompatible net s-power in Hessian entry")
        if shift >= 0:
            numerator = sp.expand(numerator * t ** (shift // unit))
        else:
            denominator = sp.expand(denominator * t ** (-shift // unit))
        entries.append((sp.factor(numerator), sp.factor(denominator)))

    (n00, d00), (n01, d01), (n11, d11) = entries
    if not include_determinant:
        return (sp.factor(n00), sp.factor(d00)), (sp.Integer(1), sp.Integer(1))
    determinant_numerator = sp.expand(
        n00 * n11 * d01**2 - n01**2 * d00 * d11
    )
    determinant_numerator = sp.cancel(sp.rem(determinant_numerator, relation, t))
    determinant_numerator, relation_denominator = sp.fraction(determinant_numerator)
    determinant_denominator = sp.factor(
        relation_denominator * d00 * d11 * d01**2
    )
    determinant_output = (
        sp.factor(determinant_numerator)
        if degree == 5
        else sp.factor_terms(determinant_numerator)
    )
    return (
        (sp.factor(n00), sp.factor(d00)),
        (determinant_output, determinant_denominator),
    )


@lru_cache(maxsize=None)
def root_bounds(
    value: Fraction, power: int, bits: int = 90
) -> tuple[Fraction, Fraction]:
    if value == 0:
        return Fraction(0), Fraction(0)
    lower, upper = Fraction(0), max(Fraction(1), value)
    for _ in range(bits):
        midpoint = (lower + upper) / 2
        if midpoint**power <= value:
            lower = midpoint
        else:
            upper = midpoint
    return lower, upper


def cube_bounds(value: Fraction, bits: int = 90) -> tuple[Fraction, Fraction]:
    return root_bounds(value, 3, bits)


def stationary_ordinate(degree: int, value: Fraction) -> Fraction:
    return Fraction((degree - 3) * value - degree, value * (degree * value - degree - 3))


def curve_box(
    degree: int, lower_y: Fraction, upper_y: Fraction
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    power = parameter_power(degree)
    t_lower = root_bounds(stationary_ordinate(degree, lower_y), power)[0]
    t_upper = root_bounds(stationary_ordinate(degree, upper_y), power)[1]
    z_lower = cube_bounds(lower_y)[0]
    z_upper = cube_bounds(upper_y)[1]
    return (t_lower, t_upper), (z_lower, z_upper)


@lru_cache(maxsize=None)
def polynomial_object(polynomial: sp.Expr) -> sp.Poly:
    return sp.Poly(polynomial, t, z, domain=sp.QQ)


def interval_add(
    left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    return left[0] + right[0], left[1] + right[1]


def interval_multiply(
    left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    products = (
        left[0] * right[0],
        left[0] * right[1],
        left[1] * right[0],
        left[1] * right[1],
    )
    return min(products), max(products)


def horner_interval(
    polynomial: sp.Expr,
    t_bounds: tuple[Fraction, Fraction],
    z_bounds: tuple[Fraction, Fraction],
) -> tuple[Fraction, Fraction]:
    if polynomial == 0:
        return Fraction(0), Fraction(0)
    poly = polynomial_object(polynomial)
    coefficients = {
        degrees: Fraction(coefficient) for degrees, coefficient in poly.terms()
    }
    maximum_t = poly.degree(t)
    maximum_z = poly.degree(z)
    result = (Fraction(0), Fraction(0))
    for t_degree in range(maximum_t, -1, -1):
        z_value = (Fraction(0), Fraction(0))
        for z_degree in range(maximum_z, -1, -1):
            z_value = interval_add(
                interval_multiply(z_value, z_bounds),
                (
                    coefficients.get((t_degree, z_degree), Fraction(0)),
                    coefficients.get((t_degree, z_degree), Fraction(0)),
                ),
            )
        result = interval_add(interval_multiply(result, t_bounds), z_value)
    return result


@lru_cache(maxsize=None)
def polynomial_derivatives(polynomial: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    return sp.diff(polynomial, t), sp.diff(polynomial, z)


def polynomial_interval(
    polynomial: sp.Expr,
    t_bounds: tuple[Fraction, Fraction],
    z_bounds: tuple[Fraction, Fraction],
) -> tuple[Fraction, Fraction]:
    """Exact centered mean-value enclosure on a rational rectangle."""
    t_center = (t_bounds[0] + t_bounds[1]) / 2
    z_center = (z_bounds[0] + z_bounds[1]) / 2
    t_radius = (t_bounds[1] - t_bounds[0]) / 2
    z_radius = (z_bounds[1] - z_bounds[0]) / 2
    center = Fraction(polynomial_object(polynomial).eval({t: t_center, z: z_center}))
    derivative_t, derivative_z = polynomial_derivatives(polynomial)
    dt_bounds = horner_interval(derivative_t, t_bounds, z_bounds)
    dz_bounds = horner_interval(derivative_z, t_bounds, z_bounds)
    error = t_radius * max(abs(dt_bounds[0]), abs(dt_bounds[1]))
    error += z_radius * max(abs(dz_bounds[0]), abs(dz_bounds[1]))
    return center - error, center + error


def sample_sign(polynomial: sp.Expr, degree: int) -> int:
    lower_y = Fraction(degree, degree - 3)
    upper_y = Fraction(degree + 3, degree - 3)
    midpoint = (lower_y + upper_y) / 2
    t_mid = float(stationary_ordinate(degree, midpoint)) ** (1 / 3)
    z_mid = float(midpoint) ** (1 / 3)
    value = float(polynomial.subs({t: t_mid, z: z_mid}))
    if value == 0:
        raise AssertionError("zero midpoint sign probe")
    return 1 if value > 0 else -1


@lru_cache(maxsize=None)
def stationary_zero_resultant(polynomial: sp.Expr, degree: int) -> sp.Expr:
    """Eliminate the two positive cube-root coordinates to a Y polynomial."""
    lifted = 0
    for (t_degree, z_degree), coefficient in sp.Poly(
        polynomial, t, z, domain=sp.QQ
    ).terms():
        quotient, remainder = divmod(z_degree, 3)
        lifted += coefficient * t**t_degree * z**remainder * y**quotient
    power = parameter_power(degree)
    t_relation = (
        t**power * y * (degree * y - degree - 3)
        - ((degree - 3) * y - degree)
    )
    eliminate_t = sp.resultant(sp.expand(lifted), t_relation, t)
    eliminate_z = sp.resultant(eliminate_t, z**3 - y, z)
    return sp.expand(eliminate_z)


@lru_cache(maxsize=None)
def stationary_open_root_count(polynomial: sp.Expr, degree: int) -> tuple[int, int]:
    resultant = stationary_zero_resultant(polynomial, degree)
    if resultant == 0:
        return -1, -1
    poly = sp.Poly(resultant, y, domain=sp.QQ)
    _, integer_poly = poly.clear_denoms(convert=True)
    poly = integer_poly.primitive()[1].sqf_part()
    lower_y = sp.Rational(degree, degree - 3)
    upper_y = sp.Rational(degree + 3, degree - 3)
    # Endpoint zeros encode the two collapse limits and are irrelevant to the
    # strict stationary arc.  Remove them before Sturm counting.
    for endpoint in (lower_y, upper_y):
        divisor = sp.Poly(y - endpoint, y, domain=sp.QQ)
        while poly.eval(endpoint) == 0:
            poly = poly.exquo(divisor)
    poly = poly.primitive()[1].sqf_part()
    bernstein_clear, _, _ = bernstein_constant_sign(
        poly,
        Fraction(lower_y),
        Fraction(upper_y),
    )
    if bernstein_clear:
        return poly.degree(), 0
    print(
        f"INFO degree-{degree} resultant degree {poly.degree()} "
        "not settled by Bernstein",
        flush=True,
    )
    if degree == 6:
        # The sextic parameter introduces real resultant roots belonging to
        # nonpositive/complex cube-root branches.  Preserve the positive
        # branch by returning to the lifted (t,v,z)>0 certificate instead of
        # asking Sturm to settle the over-strong eliminated polynomial.
        return poly.degree(), -2
    print("INFO falling back to Sturm", flush=True)
    return poly.degree(), int(poly.count_roots(lower_y, upper_y))


def initial_bernstein_coefficients(
    polynomial: sp.Poly, left: Fraction, right: Fraction
) -> list[Fraction]:
    """Exact Bernstein coefficients after y=left+(right-left)x."""
    degree = polynomial.degree()
    original = [
        Fraction(polynomial.nth(index)) for index in range(degree + 1)
    ]
    scale = right - left
    power = []
    for k in range(degree + 1):
        coefficient = sum(
            original[i] * comb(i, k) * left ** (i - k)
            for i in range(k, degree + 1)
        )
        power.append(coefficient * scale**k)
    return [
        sum(
            power[i] * Fraction(comb(k, i), comb(degree, i))
            for i in range(k + 1)
        )
        for k in range(degree + 1)
    ]


def split_bernstein(coefficients: list[Fraction]) -> tuple[list[Fraction], list[Fraction]]:
    levels = [coefficients]
    while len(levels[-1]) > 1:
        previous = levels[-1]
        levels.append(
            [(previous[i] + previous[i + 1]) / 2 for i in range(len(previous) - 1)]
        )
    left = [level[0] for level in levels]
    right = [levels[-1 - index][index] for index in range(len(coefficients))]
    return left, right


def bernstein_constant_sign(
    polynomial: sp.Poly,
    left: Fraction,
    right: Fraction,
    max_depth: int = 48,
) -> tuple[bool, int, int]:
    """Prove constant nonzero sign by exact Bernstein subdivision."""
    stack = [(initial_bernstein_coefficients(polynomial, left, right), 0)]
    leaves = deepest = 0
    common_sign: int | None = None
    while stack:
        coefficients, depth = stack.pop()
        sign = 1 if all(value > 0 for value in coefficients) else None
        if sign is None and all(value < 0 for value in coefficients):
            sign = -1
        if sign is not None:
            if common_sign is None:
                common_sign = sign
            elif common_sign != sign:
                return False, leaves, deepest
            leaves += 1
            deepest = max(deepest, depth)
            continue
        if depth >= max_depth:
            return False, leaves, deepest
        left_coefficients, right_coefficients = split_bernstein(coefficients)
        stack.append((right_coefficients, depth + 1))
        stack.append((left_coefficients, depth + 1))
    return True, leaves, deepest


def prove_on_range(
    polynomial: sp.Expr,
    degree: int,
    sign: int,
    lower_y: Fraction,
    upper_y: Fraction,
    max_depth: int = 42,
) -> tuple[int, int, Fraction]:
    stack = [(lower_y, upper_y, 0)]
    leaves = 0
    deepest = 0
    weakest: Fraction | None = None
    while stack:
        left, right, depth = stack.pop()
        lower, upper = polynomial_interval(polynomial, *curve_box(degree, left, right))
        margin = lower if sign > 0 else -upper
        if margin > 0:
            leaves += 1
            deepest = max(deepest, depth)
            weakest = margin if weakest is None else min(weakest, margin)
            continue
        if depth >= max_depth:
            raise AssertionError(
                f"degree-{degree} unresolved factor cell [{left},{right}]"
            )
        midpoint = (left + right) / 2
        stack.append((midpoint, right, depth + 1))
        stack.append((left, midpoint, depth + 1))
    assert weakest is not None
    return leaves, deepest, weakest


@lru_cache(maxsize=None)
def upper_endpoint_remainder(polynomial: sp.Expr, degree: int) -> sp.Expr:
    """Reduce exactly in the positive endpoint cubic number field.

    At the speed-saturation endpoint, ``z^3=Y`` and ``t^3=Y^-2``.
    Positivity selects the common cubic branch ``t=z/Y``.  Reducing only by
    the two cubic equations retains eight spurious complex branch pairs and
    can therefore miss a genuine zero on the positive stationary arc.
    """
    upper_y = Fraction(degree + 3, degree - 3)
    if parameter_power(degree) == 3:
        endpoint_t = z / sp.Rational(upper_y)
    else:
        endpoint_t = z**2 / sp.Rational(upper_y)
    reduced = sp.expand(polynomial.subs(t, endpoint_t))
    return sp.expand(sp.rem(reduced, z**3 - sp.Rational(upper_y), z))


def vanishes_at_upper_endpoint(polynomial: sp.Expr, degree: int) -> bool:
    return upper_endpoint_remainder(polynomial, degree) == 0


@lru_cache(maxsize=None)
def lower_endpoint_remainder(polynomial: sp.Expr, degree: int) -> sp.Expr:
    lower_y = Fraction(degree, degree - 3)
    reduced = sp.expand(polynomial.subs(t, 0))
    return sp.expand(sp.rem(reduced, z**3 - sp.Rational(lower_y), z))


def vanishes_at_lower_endpoint(polynomial: sp.Expr, degree: int) -> bool:
    return lower_endpoint_remainder(polynomial, degree) == 0


def prove_upper_endpoint_collar(
    polynomial: sp.Expr,
    degree: int,
    interior_sign: int,
    width: Fraction,
) -> tuple[Fraction, int, int, Fraction]:
    """Use the first nonzero arc derivative at the saturation endpoint.

    Several reduced Hessian factors have higher-order endpoint zeros.  If the
    first ``m-1`` derivatives vanish and the ``m``-th has sign
    ``(-1)^m * interior_sign`` on a left collar, repeated integration from the
    endpoint proves the requested sign of the original factor.
    """
    if not vanishes_at_upper_endpoint(polynomial, degree):
        raise AssertionError("requested endpoint collar for nonvanishing factor")
    ordinate = ((degree - 3) * y - degree) / (y * (degree * y - degree - 3))
    ordinate_prime = sp.diff(ordinate, y).subs(y, z**3)
    power = parameter_power(degree)
    relation = (
        t**power * z**3 * (degree * z**3 - degree - 3)
        - ((degree - 3) * z**3 - degree)
    )
    derivative: sp.Expr = polynomial
    for order in range(1, 17):
        derivative = sp.factor(
            sp.together(
                sp.diff(derivative, t)
                * ordinate_prime
                / (power * t ** (power - 1))
                + sp.diff(derivative, z) / (3 * z**2)
            )
        )
        derivative_numerator, derivative_denominator = sp.fraction(derivative)
        derivative_numerator, derivative_denominator = reduced_ratio(
            derivative_numerator, derivative_denominator, relation
        )
        derivative = sp.factor(derivative_numerator / derivative_denominator)
        if vanishes_at_upper_endpoint(derivative_numerator, degree):
            if vanishes_at_upper_endpoint(derivative_denominator, degree):
                raise AssertionError("uncancelled endpoint zero in arc derivative")
            continue

        target_derivative_sign = ((-1) ** order) * interior_sign
        numerator_endpoint = endpoint_value_interval(derivative_numerator, degree)
        denominator_endpoint = endpoint_value_interval(derivative_denominator, degree)
        numerator_sign = 1 if numerator_endpoint[0] > 0 else -1
        denominator_sign = 1 if denominator_endpoint[0] > 0 else -1
        if numerator_endpoint[0] <= 0 <= numerator_endpoint[1]:
            raise AssertionError("unresolved nonzero derivative numerator endpoint")
        if denominator_endpoint[0] <= 0 <= denominator_endpoint[1]:
            raise AssertionError("unresolved arc-derivative denominator endpoint")
        if numerator_sign * denominator_sign != target_derivative_sign:
            raise AssertionError("wrong first nonzero endpoint derivative sign")

        numerator_width, numerator_margin = prove_nonzero_endpoint_collar(
            derivative_numerator, degree, numerator_sign
        )
        denominator_width, denominator_margin = prove_nonzero_endpoint_collar(
            derivative_denominator, degree, denominator_sign
        )
        certified_width = min(width, numerator_width, denominator_width)
        return (
            certified_width,
            2,
            order,
            min(numerator_margin, denominator_margin),
        )
    raise AssertionError("endpoint vanishing order exceeds sixteen")


def endpoint_value_interval(
    polynomial: sp.Expr, degree: int
) -> tuple[Fraction, Fraction]:
    upper_y = Fraction(degree + 3, degree - 3)
    upper_t_cubed = stationary_ordinate(degree, upper_y)
    t_bounds = root_bounds(upper_t_cubed, parameter_power(degree), 180)
    z_bounds = cube_bounds(upper_y, 180)
    # Evaluate the exact bidegree-(<3,<3) endpoint representative, not the
    # unreduced high-degree factor.  The latter has catastrophic interval
    # dependency even at 180-bit algebraic point boxes.
    return polynomial_interval(
        upper_endpoint_remainder(polynomial, degree), t_bounds, z_bounds
    )


def lower_endpoint_value_interval(
    polynomial: sp.Expr, degree: int
) -> tuple[Fraction, Fraction]:
    lower_y = Fraction(degree, degree - 3)
    z_bounds = cube_bounds(lower_y, 180)
    return polynomial_interval(
        lower_endpoint_remainder(polynomial, degree),
        (Fraction(0), Fraction(0)),
        z_bounds,
    )


def prove_nonzero_endpoint_collar(
    polynomial: sp.Expr, degree: int, sign: int
) -> tuple[Fraction, Fraction]:
    """Certify a collar by endpoint margin and an exact derivative bound."""
    endpoint_lower, endpoint_upper = endpoint_value_interval(polynomial, degree)
    endpoint_margin = endpoint_lower if sign > 0 else -endpoint_upper
    if endpoint_margin <= 0:
        raise AssertionError("endpoint algebraic value has wrong sign")
    ordinate = ((degree - 3) * y - degree) / (y * (degree * y - degree - 3))
    ordinate_prime = sp.diff(ordinate, y).subs(y, z**3)
    power = parameter_power(degree)
    relation = (
        t**power * z**3 * (degree * z**3 - degree - 3)
        - ((degree - 3) * z**3 - degree)
    )
    curve_derivative = (
        sp.diff(polynomial, t)
        * ordinate_prime
        / (power * t ** (power - 1))
        + sp.diff(polynomial, z) / (3 * z**2)
    )
    derivative_numerator, derivative_denominator = sp.fraction(
        sp.factor(sp.together(curve_derivative))
    )
    upper_y = Fraction(degree + 3, degree - 3)
    width = Fraction(1, 16)
    for _ in range(20):
        bounds = curve_box(degree, upper_y - width, upper_y)
        numerator_bounds = polynomial_interval(derivative_numerator, *bounds)
        denominator_bounds = polynomial_interval(derivative_denominator, *bounds)
        if denominator_bounds[0] > 0:
            derivative_bound = max(
                abs(numerator_bounds[0]), abs(numerator_bounds[1])
            ) / denominator_bounds[0]
        elif denominator_bounds[1] < 0:
            derivative_bound = max(
                abs(numerator_bounds[0]), abs(numerator_bounds[1])
            ) / (-denominator_bounds[1])
        else:
            width /= 2
            continue
        if endpoint_margin > width * derivative_bound:
            return width, endpoint_margin - width * derivative_bound
        width /= 2
    raise AssertionError("could not certify nonzero endpoint collar")


def prove_nonzero_lower_endpoint_collar(
    polynomial: sp.Expr, degree: int, sign: int
) -> tuple[Fraction, Fraction]:
    """Certify a lower collar using the regular parameter ``t``."""
    endpoint_lower, endpoint_upper = lower_endpoint_value_interval(
        polynomial, degree
    )
    endpoint_margin = endpoint_lower if sign > 0 else -endpoint_upper
    if endpoint_margin <= 0:
        raise AssertionError("lower endpoint algebraic value has wrong sign")
    ordinate = ((degree - 3) * y - degree) / (y * (degree * y - degree - 3))
    ordinate_prime = sp.diff(ordinate, y).subs(y, z**3)
    power = parameter_power(degree)
    curve_derivative = sp.diff(polynomial, t) + sp.diff(polynomial, z) * (
        power * t ** (power - 1) / (3 * z**2 * ordinate_prime)
    )
    derivative_numerator, derivative_denominator = sp.fraction(
        sp.factor(sp.together(curve_derivative))
    )
    lower_y = Fraction(degree, degree - 3)
    # Start deep enough that the regular-parameter mean-value bound resolves
    # even the high-order determinant coefficient in one or two attempts.
    # This tiny collar is only the seed for a subsequent proof out to a fixed
    # macroscopic width; it is not the final subdivision boundary.
    width = Fraction(1, 2**64)
    for _ in range(64):
        bounds = curve_box(degree, lower_y, lower_y + width)
        numerator_bounds = polynomial_interval(derivative_numerator, *bounds)
        denominator_bounds = polynomial_interval(derivative_denominator, *bounds)
        if denominator_bounds[0] > 0:
            derivative_bound = max(
                abs(numerator_bounds[0]), abs(numerator_bounds[1])
            ) / denominator_bounds[0]
        elif denominator_bounds[1] < 0:
            derivative_bound = max(
                abs(numerator_bounds[0]), abs(numerator_bounds[1])
            ) / (-denominator_bounds[1])
        else:
            width /= 2
            continue
        t_width = bounds[0][1]
        if endpoint_margin > t_width * derivative_bound:
            return width, endpoint_margin - t_width * derivative_bound
        width /= 2
    raise AssertionError("could not certify nonzero lower endpoint collar")


def prove_lower_endpoint_collar(
    polynomial: sp.Expr,
    degree: int,
    interior_sign: int,
    width: Fraction,
) -> tuple[Fraction, int, int, Fraction]:
    """Use the first nonzero derivative in the regular lower parameter t."""
    if not vanishes_at_lower_endpoint(polynomial, degree):
        raise AssertionError("requested lower collar for nonvanishing factor")
    ordinate = ((degree - 3) * y - degree) / (y * (degree * y - degree - 3))
    ordinate_prime = sp.diff(ordinate, y).subs(y, z**3)
    power = parameter_power(degree)
    relation = (
        t**power * z**3 * (degree * z**3 - degree - 3)
        - ((degree - 3) * z**3 - degree)
    )
    derivative: sp.Expr = polynomial
    for order in range(1, 17):
        derivative = sp.factor(
            sp.together(
                sp.diff(derivative, t)
                + sp.diff(derivative, z)
                * power
                * t ** (power - 1)
                / (3 * z**2 * ordinate_prime)
            )
        )
        derivative_numerator, derivative_denominator = sp.fraction(derivative)
        derivative_numerator, derivative_denominator = reduced_ratio(
            derivative_numerator, derivative_denominator, relation
        )
        derivative = sp.factor(derivative_numerator / derivative_denominator)
        if vanishes_at_lower_endpoint(derivative_numerator, degree):
            if vanishes_at_lower_endpoint(derivative_denominator, degree):
                raise AssertionError("uncancelled lower zero in arc derivative")
            continue
        numerator_endpoint = lower_endpoint_value_interval(
            derivative_numerator, degree
        )
        denominator_endpoint = lower_endpoint_value_interval(
            derivative_denominator, degree
        )
        numerator_sign = 1 if numerator_endpoint[0] > 0 else -1
        denominator_sign = 1 if denominator_endpoint[0] > 0 else -1
        if numerator_endpoint[0] <= 0 <= numerator_endpoint[1]:
            raise AssertionError("unresolved lower derivative numerator endpoint")
        if denominator_endpoint[0] <= 0 <= denominator_endpoint[1]:
            raise AssertionError("unresolved lower derivative denominator endpoint")
        if numerator_sign * denominator_sign != interior_sign:
            raise AssertionError("wrong first nonzero lower derivative sign")
        print(
            f"LOWER degree-{degree} first nonzero order={order}; "
            f"numerator factors="
            f"{[(sp.Poly(f, t, z).degree(t), sp.Poly(f, t, z).degree(z), e) for f, e in sp.factor_list(derivative_numerator, gens=(t, z))[1]]}; "
            f"denominator factors="
            f"{[(sp.Poly(f, t, z).degree(t), sp.Poly(f, t, z).degree(z), e) for f, e in sp.factor_list(derivative_denominator, gens=(t, z))[1]]}",
            flush=True,
        )
        lower_y = Fraction(degree, degree - 3)
        numerator_boxes = certify_expression_on_range(
            derivative_numerator,
            degree,
            numerator_sign,
            lower_y,
            lower_y + width,
        )
        denominator_boxes = certify_expression_on_range(
            derivative_denominator,
            degree,
            denominator_sign,
            lower_y,
            lower_y + width,
        )
        return (
            width,
            numerator_boxes[0] + denominator_boxes[0],
            max(order, numerator_boxes[1], denominator_boxes[1]),
            min(
                numerator_boxes[2],
                denominator_boxes[2],
            ),
        )
    raise AssertionError("lower endpoint vanishing order exceeds sixteen")


def prove_factor(
    polynomial: sp.Expr, degree: int, sign: int, max_depth: int = 42
) -> tuple[int, int, Fraction]:
    poly_degree_z = sp.Poly(polynomial, t, z).degree(z)
    if degree == 5 or poly_degree_z <= 30:
        resultant_degree, root_count = stationary_open_root_count(polynomial, degree)
        if root_count == 0:
            print(
                f"PASS degree-{degree} stationary resultant degree "
                f"{resultant_degree}: no open-arc zeros",
                flush=True,
            )
            return 1, 0, Fraction(1)
    lower_y = Fraction(degree, degree - 3)
    upper_y = Fraction(degree + 3, degree - 3)
    collar_leaves = collar_depth = 0
    collar_weakest: Fraction | None = None
    if vanishes_at_upper_endpoint(polynomial, degree):
        width = Fraction(1, 16)
        (
            width,
            collar_leaves,
            collar_depth,
            collar_weakest,
        ) = prove_upper_endpoint_collar(polynomial, degree, sign, width)
        upper_y -= width
    else:
        width, collar_weakest = prove_nonzero_endpoint_collar(
            polynomial, degree, sign
        )
        collar_leaves = 1
        upper_y -= width
    lower_collar_leaves = lower_collar_depth = 0
    lower_collar_weakest: Fraction | None = None
    if vanishes_at_lower_endpoint(polynomial, degree):
        lower_width = Fraction(1, 16)
        (
            lower_width,
            lower_collar_leaves,
            lower_collar_depth,
            lower_collar_weakest,
        ) = prove_lower_endpoint_collar(polynomial, degree, sign, lower_width)
        lower_y += lower_width
    else:
        lower_width, lower_collar_weakest = prove_nonzero_lower_endpoint_collar(
            polynomial, degree, sign
        )
        lower_collar_leaves = 1
        lower_y += lower_width
    leaves, depth, weakest = prove_lifted_on_range(
        polynomial, degree, sign, lower_y, upper_y, max_depth
    )
    if collar_weakest is not None:
        weakest = min(weakest, collar_weakest)
    if lower_collar_weakest is not None:
        weakest = min(weakest, lower_collar_weakest)
    return (
        leaves + collar_leaves + lower_collar_leaves,
        max(depth, collar_depth, lower_collar_depth),
        weakest,
    )


def elementary_factor_sign(polynomial: sp.Expr, degree: int) -> int | None:
    """Recognize endpoint/monomial factors; return their open-arc sign."""
    candidate = sp.factor(polynomial)
    probes = {
        z: 1,
        t: 1,
        z - 1: 1,
        z**2 + z + 1: 1,
        degree * z**3 - degree - 3: 1,
        (degree - 3) * z**3 - degree: 1,
        z**3 - Fraction(degree + 3, degree - 3): -1,
    }
    return probes.get(candidate)


def lower_shift_positive_orthant_sign(
    polynomial: sp.Expr, degree: int
) -> int | None:
    """Try a coefficientwise sign proof after Y=Y0+v and z^3=Y.

    The variables t, v, z are positive on the lower collar.  Replacing each
    z^(3a+r) by z^r (Y0+v)^a is an exact identity.  Uniform coefficient sign
    is therefore a cheap exact positivity certificate with no interval
    dependency.
    """
    lifted = lower_shift_lift(polynomial, degree)
    coefficients = [
        coefficient
        for _, coefficient in sp.Poly(
            lifted, t, v, z, domain=sp.QQ
        ).terms()
    ]
    if coefficients and all(coefficient > 0 for coefficient in coefficients):
        return 1
    if coefficients and all(coefficient < 0 for coefficient in coefficients):
        return -1
    return None


@lru_cache(maxsize=None)
def lower_shift_lift(polynomial: sp.Expr, degree: int) -> sp.Expr:
    """Rewrite z powers through z^3=Y0+v, leaving z-degree below three."""
    lower_y = sp.Rational(degree, degree - 3)
    lifted = 0
    for (t_degree, z_degree), coefficient in sp.Poly(
        polynomial, t, z, domain=sp.QQ
    ).terms():
        quotient, remainder = divmod(z_degree, 3)
        lifted += (
            coefficient
            * t**t_degree
            * z**remainder
            * (lower_y + v) ** quotient
        )
    return sp.expand(lifted)


@lru_cache(maxsize=None)
def lifted_polynomial_object(polynomial: sp.Expr) -> sp.Poly:
    return sp.Poly(polynomial, t, v, z, domain=sp.QQ)


def horner_interval_lifted(
    polynomial: sp.Expr,
    t_bounds: tuple[Fraction, Fraction],
    v_bounds: tuple[Fraction, Fraction],
    z_bounds: tuple[Fraction, Fraction],
) -> tuple[Fraction, Fraction]:
    if polynomial == 0:
        return Fraction(0), Fraction(0)
    poly = lifted_polynomial_object(polynomial)
    coefficients = {
        degrees: Fraction(coefficient) for degrees, coefficient in poly.terms()
    }
    result = (Fraction(0), Fraction(0))
    for t_degree in range(poly.degree(t), -1, -1):
        v_value = (Fraction(0), Fraction(0))
        for v_degree in range(poly.degree(v), -1, -1):
            z_value = (Fraction(0), Fraction(0))
            for z_degree in range(poly.degree(z), -1, -1):
                coefficient = coefficients.get(
                    (t_degree, v_degree, z_degree), Fraction(0)
                )
                z_value = interval_add(
                    interval_multiply(z_value, z_bounds),
                    (coefficient, coefficient),
                )
            v_value = interval_add(
                interval_multiply(v_value, v_bounds), z_value
            )
        result = interval_add(interval_multiply(result, t_bounds), v_value)
    return result


@lru_cache(maxsize=None)
def lifted_derivatives(polynomial: sp.Expr) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    return (
        sp.diff(polynomial, t),
        sp.diff(polynomial, v),
        sp.diff(polynomial, z),
    )


def lifted_polynomial_interval(
    polynomial: sp.Expr,
    t_bounds: tuple[Fraction, Fraction],
    v_bounds: tuple[Fraction, Fraction],
    z_bounds: tuple[Fraction, Fraction],
) -> tuple[Fraction, Fraction]:
    centers = tuple((bounds[0] + bounds[1]) / 2 for bounds in (t_bounds, v_bounds, z_bounds))
    radii = tuple((bounds[1] - bounds[0]) / 2 for bounds in (t_bounds, v_bounds, z_bounds))
    center = Fraction(
        lifted_polynomial_object(polynomial).eval(
            {t: centers[0], v: centers[1], z: centers[2]}
        )
    )
    error = Fraction(0)
    for derivative, radius in zip(lifted_derivatives(polynomial), radii):
        bounds = horner_interval_lifted(
            derivative, t_bounds, v_bounds, z_bounds
        )
        error += radius * max(abs(bounds[0]), abs(bounds[1]))
    return center - error, center + error


def prove_lifted_on_range(
    polynomial: sp.Expr,
    degree: int,
    sign: int,
    lower_y: Fraction,
    upper_y: Fraction,
    max_depth: int = 42,
) -> tuple[int, int, Fraction]:
    base_y = Fraction(degree, degree - 3)
    lifted = lower_shift_lift(polynomial, degree)
    stack = [(lower_y, upper_y, 0)]
    leaves = deepest = 0
    weakest: Fraction | None = None
    while stack:
        left, right, depth = stack.pop()
        t_bounds, z_bounds = curve_box(degree, left, right)
        bounds = lifted_polynomial_interval(
            lifted,
            t_bounds,
            (left - base_y, right - base_y),
            z_bounds,
        )
        margin = bounds[0] if sign > 0 else -bounds[1]
        if margin > 0:
            leaves += 1
            deepest = max(deepest, depth)
            weakest = margin if weakest is None else min(weakest, margin)
            continue
        if depth >= max_depth:
            raise AssertionError(
                f"degree-{degree} unresolved lifted cell [{left},{right}]"
            )
        midpoint = (left + right) / 2
        stack.append((midpoint, right, depth + 1))
        stack.append((left, midpoint, depth + 1))
    assert weakest is not None
    return leaves, deepest, weakest


def certify_expression_on_range(
    expression: sp.Expr,
    degree: int,
    expected_sign: int,
    lower_y: Fraction,
    upper_y: Fraction,
) -> tuple[int, int, Fraction]:
    """Factorwise exact sign certificate on a bounded stationary subarc."""
    coefficient, factors = sp.factor_list(expression, gens=(t, z))
    total_sign = 1 if coefficient > 0 else -1
    leaves = 0
    deepest = 0
    weakest: Fraction | None = None
    for factor, exponent in factors:
        sign = elementary_factor_sign(factor, degree)
        factor_result: tuple[int, int, Fraction] | None = None
        if sign is None:
            endpoint_lower, endpoint_upper = lower_endpoint_value_interval(
                factor, degree
            )
            if endpoint_lower > 0:
                sign = 1
            elif endpoint_upper < 0:
                sign = -1
            else:
                raise AssertionError("range factor vanishes at lower endpoint")
            orthant_sign = lower_shift_positive_orthant_sign(factor, degree)
            if orthant_sign is not None:
                if orthant_sign != sign:
                    raise AssertionError("lower-shift coefficient sign mismatch")
                factor_result = (1, 0, Fraction(1))
            else:
                factor_result = prove_lifted_on_range(
                    factor,
                    degree,
                    sign,
                    lower_y,
                    upper_y,
                    max_depth=42,
                )
        if exponent % 2:
            total_sign *= sign
        if factor_result is not None:
            leaves += factor_result[0]
            deepest = max(deepest, factor_result[1])
            weakest = (
                factor_result[2]
                if weakest is None
                else min(weakest, factor_result[2])
            )
    if total_sign != expected_sign:
        raise AssertionError("factorwise stationary-subarc sign mismatch")
    if weakest is None:
        weakest = Fraction(1)
    return leaves, deepest, weakest


def certify_expression_sign(expression: sp.Expr, degree: int, label: str) -> int:
    coefficient, factors = sp.factor_list(expression, gens=(t, z))
    total_sign = 1 if coefficient > 0 else -1
    for factor, exponent in factors:
        sign = elementary_factor_sign(factor, degree)
        if sign is None:
            sign = sample_sign(factor, degree)
            endpoint_remainder = upper_endpoint_remainder(factor, degree)
            print(
                f"CHECK degree-{degree} {label} factor "
                f"deg=({sp.Poly(factor, t, z).degree(t)},"
                f"{sp.Poly(factor, t, z).degree(z)}), sign={sign}, "
                f"endpoint_remainder={sp.factor(endpoint_remainder)}",
                flush=True,
            )
            leaves, depth, weakest = prove_factor(factor, degree, sign)
            print(
                f"PASS degree-{degree} {label} factor "
                f"deg=({sp.Poly(factor, t, z).degree(t)},"
                f"{sp.Poly(factor, t, z).degree(z)}): "
                f"{leaves} boxes, depth {depth}, exact margin > {weakest}"
            )
        if exponent % 2:
            total_sign *= sign
    return total_sign


def certify_unfactored_expression_sign(
    expression: sp.Expr, degree: int, label: str
) -> int:
    sign = sample_sign(expression, degree)
    leaves, depth, weakest = prove_factor(expression, degree, sign, max_depth=48)
    print(
        f"PASS degree-{degree} {label} unfactored: "
        f"{leaves} boxes, depth {depth}, exact margin > {weakest}",
        flush=True,
    )
    return sign


def main() -> None:
    summed_hessian, variance = reflection_data()
    for degree in (5, 6):
        (h00_numerator, h00_denominator), (
            determinant_numerator,
            determinant_denominator,
        ) = reduced_hessian(degree, summed_hessian, variance)
        h00_sign = certify_expression_sign(h00_numerator, degree, "H00 numerator")
        h00_sign *= certify_expression_sign(h00_denominator, degree, "H00 denominator")
        determinant_sign = (
            certify_expression_sign(
                determinant_numerator, degree, "determinant numerator"
            )
            if degree == 5
            else certify_unfactored_expression_sign(
                determinant_numerator, degree, "determinant numerator"
            )
        )
        determinant_sign *= certify_expression_sign(
            determinant_denominator, degree, "determinant denominator"
        )
        if h00_sign != -1:
            raise AssertionError(f"degree-{degree} H00 is not negative")
        if determinant_sign != 1:
            raise AssertionError(f"degree-{degree} determinant is not positive")
        print(f"PASS degree-{degree} harmonic-excess Hessian negative definite")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
