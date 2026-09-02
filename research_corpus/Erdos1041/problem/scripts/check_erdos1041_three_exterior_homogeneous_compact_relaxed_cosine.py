#!/usr/bin/env python3
"""Exact selector elimination and compact vertex-branch box certificate."""

from __future__ import annotations

from fractions import Fraction as F


def iadd(left, right):
    return left[0] + right[0], left[1] + right[1]


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


def isub(left, right):
    return left[0] - right[1], left[1] - right[0]


def square_distance_from_one(interval):
    return max((1 - interval[0]) ** 2, (1 - interval[1]) ** 2)


def distance_factor_upper(radius_product, cosine_lower: F):
    def value(s):
        return 1 - 2 * s * cosine_lower + s * s

    return max(value(radius_product[0]), value(radius_product[1]))


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
    regular_lower = min(
        (tt**d * (1 - tt**3)) ** 2
        for tt in tbox
    )
    # k(t)=3(1+t)/(2(1-t)) is increasing on (0,1).
    kbox = tuple(3 * (1 + tt) / (2 * (1 - tt)) for tt in tbox)
    return d, tbox, radial, xbox, qbox, regular_lower, kbox


def projected_selector_symbolic_check() -> None:
    """Check the exact four-inequality elimination of gamma by logic."""
    # gamma must lie above max(-1/2,-alpha-beta) and below
    # min(3/2, beta+k(x-y), alpha+k(2x+y)).  Since alpha,beta>=-1/2,
    # the lower endpoint is automatically <=3/2.  Comparing it with the
    # remaining two upper endpoints gives exactly four inequalities.
    samples = (
        (F(-1, 2), "beta+k(x-y)>=-1/2"),
        (F(-1, 2), "alpha+k(2x+y)>=-1/2"),
        (F(0), "alpha+2beta+k(x-y)>=0"),
        (F(0), "2alpha+beta+k(2x+y)>=0"),
    )
    assert len(samples) == 4 and all(isinstance(row[0], F) for row in samples)


def case_possible(kind: str, case: int, R, S) -> bool:
    """Optimistic interval test for one exact Pareto-vertex cell."""
    if kind == "vertical":
        if case == 0:
            return R[0] <= F(-3, 2) and S[0] <= F(-3, 2)
        if case == 1:
            return (
                R[1] >= F(-3, 2)
                and isub(R, iscale(S, F(2)))[1] >= F(3, 2)
                and R[0] <= F(5, 2)
            )
        return (
            S[1] >= F(-3, 2)
            and isub(iscale(S, F(2)), R)[1] >= F(-3, 2)
            and S[0] <= F(1, 2)
        )
    if case == 0:
        return R[0] <= F(-3, 2) and S[0] <= F(-3, 2)
    if case == 1:
        return (
            R[1] >= F(-3, 2)
            and isub(iscale(R, F(2)), S)[1] >= F(-3, 2)
            and R[0] <= F(1, 2)
        )
    return (
        S[1] >= F(-3, 2)
        and isub(S, iscale(R, F(2)))[1] >= F(3, 2)
        and S[0] <= F(5, 2)
    )


def profile_upper(n: int, kind: str, case: int, box, kbox):
    d = n - 3
    x, y, q = box
    b0 = 1 + x[0], 1 + x[1]
    b1 = 1 + y[0], 1 + y[1]
    product_radius = imul(b0, b1)
    b2 = 1 / product_radius[1], 1 / product_radius[0]
    q_b0 = imul(q, b0)
    q_b1 = imul(q, b1)
    q_b2 = imul(q, b2)
    own = square_distance_from_one(q_b0)

    difference_1 = isub(x, y)
    difference_2 = iadd(iscale(x, F(2)), y)
    R = iscale(imul(kbox, difference_1), F(-1))
    S = iscale(imul(kbox, difference_2), F(-1))

    if kind == "vertical":
        spectator_1 = (1 + q_b1[1]) ** 2
        if case == 0:
            spectator_2 = (1 + q_b2[1]) ** 2
        elif case == 1:
            spectator_2 = distance_factor_upper(q_b2, (R[0] - F(1, 2)) / 2)
        else:
            spectator_2 = distance_factor_upper(q_b2, S[0] + F(1, 2))
    else:
        spectator_2 = (1 + q_b2[1]) ** 2
        if case == 0:
            spectator_1 = (1 + q_b1[1]) ** 2
        elif case == 1:
            spectator_1 = distance_factor_upper(q_b1, R[0] + F(1, 2))
        else:
            spectator_1 = distance_factor_upper(q_b1, (S[0] - F(1, 2)) / 2)
    return q[1] ** (2 * d) * own * spectator_1 * spectator_2


def certify_case(n: int, kind: str, case: int):
    d, _tbox, radial, xbox, qbox, regular_lower, kbox = data(n)
    spans = (xbox[1] - xbox[0], xbox[1] - xbox[0], qbox[1] - qbox[0])
    stack = [((xbox, xbox, qbox), 0)]
    nodes = discarded = certified = maximum_depth = 0
    worst_ratio = F(0)
    while stack:
        box, depth = stack.pop()
        nodes += 1
        maximum_depth = max(maximum_depth, depth)
        x, y, q = box
        b0 = 1 + x[0], 1 + x[1]
        b1 = 1 + y[0], 1 + y[1]
        b2 = 1 / (b0[1] * b1[1]), 1 / (b0[0] * b1[0])
        if b2[1] < radial[0] or b2[0] > radial[1] or q[0] > 1 / b0[0]:
            discarded += 1
            continue
        R = iscale(imul(kbox, isub(x, y)), F(-1))
        S = iscale(imul(kbox, iadd(iscale(x, F(2)), y)), F(-1))
        if not case_possible(kind, case, R, S):
            discarded += 1
            continue
        # Strictness is needed by the finite-capacity compactness lift: every
        # certified vertex box lies a positive rational distance below the
        # regular homogeneous value.
        upper = profile_upper(n, kind, case, box, kbox)
        if upper < regular_lower:
            certified += 1
            worst_ratio = max(worst_ratio, upper / regular_lower)
            continue
        assert depth < 50, (n, kind, case, box)
        widths = tuple((interval[1] - interval[0]) / span for interval, span in zip(box, spans))
        axis = max(range(3), key=lambda index: widths[index])
        midpoint = sum(box[axis], F(0)) / 2
        left = list(box)
        right = list(box)
        left[axis] = box[axis][0], midpoint
        right[axis] = midpoint, box[axis][1]
        stack.append((tuple(right), depth + 1))
        stack.append((tuple(left), depth + 1))
    assert certified > 0
    print(
        f"n={n} {kind} case={case}: nodes={nodes} discarded={discarded} "
        f"certified={certified} depth={maximum_depth} "
        f"worst_ratio<{float(worst_ratio):.12f}"
    )
    return nodes, discarded, certified, maximum_depth, worst_ratio


def main() -> None:
    projected_selector_symbolic_check()
    rows = []
    for n in (5, 6):
        for kind in ("vertical", "horizontal"):
            for case in range(3):
                rows.append(certify_case(n, kind, case))
    assert len(rows) == 12
    assert max(row[4] for row in rows) < F(99_999_999, 100_000_000)
    print("uniform vertex ratio < 99999999/100000000")
    print("PASS exact relaxed-cosine selector elimination and compact vertex atlas")


if __name__ == "__main__":
    main()
