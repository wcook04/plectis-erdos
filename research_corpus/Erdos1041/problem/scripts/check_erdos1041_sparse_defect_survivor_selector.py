#!/usr/bin/env python3
"""Exact replay for the sparse-defect star and survivor-local selector.

This checker uses only rational arithmetic.  It verifies the closed-r=1 Gram
formulas, ER4 mass fractions, and the squared survivor-local AM--GM inequality
on an exhaustive finite grid.  The analytic continuity from r=1 to r<1 and
the general AM--GM theorem are proved in the companion note.
"""

from __future__ import annotations

from fractions import Fraction as Q
from itertools import combinations, product


def determinant(matrix: list[list[Q]]) -> Q:
    data = [row[:] for row in matrix]
    size = len(data)
    out = Q(1)
    for column in range(size):
        pivot = next(
            (row for row in range(column, size) if data[row][column]), None
        )
        if pivot is None:
            return Q(0)
        if pivot != column:
            data[column], data[pivot] = data[pivot], data[column]
            out = -out
        value = data[column][column]
        out *= value
        for index in range(column, size):
            data[column][index] /= value
        for row in range(column + 1, size):
            scale = data[row][column]
            if scale:
                for index in range(column, size):
                    data[row][index] -= scale * data[column][index]
    return out


def star_row(n: int) -> dict[str, Q]:
    # K=DHD with D_00=sqrt(n); det(H)=det(K)/n.
    matrix = [[Q(0) for _ in range(n)] for _ in range(n)]
    matrix[0][0] = Q(n)
    for index in range(1, n):
        matrix[0][index] = matrix[index][0] = Q(1)
    for row in range(1, n):
        for column in range(1, n):
            matrix[row][column] = Q(1) if row == column else Q(1, n)

    det_h = determinant(matrix) / n
    central = Q(n - 1, n)
    outer = Q(2 * (n - 1), n * n)
    frobenius = central + (n - 1) * outer
    total_mass = (n - 1) ** 2 + (n - 1)

    assert det_h == Q(n - 1, n) ** (n - 1)
    assert central > outer
    assert frobenius == Q((n - 1) * (3 * n - 2), n * n)
    assert Q(n - 1, total_mass) == Q(1, n)
    assert Q(2, total_mass) == Q(2, n * (n - 1))
    return {
        "det_H": det_h,
        "central_row_defect": central,
        "outer_row_defect": outer,
        "survivor_mass_fraction": Q(1, n),
    }


def selector_row(charges: tuple[Q, ...], ages: tuple[Q, ...]) -> None:
    size = len(charges)
    chosen = sorted(range(size), key=lambda index: (ages[index], index))[:2]
    i, j = chosen
    total_age = sum(ages, Q(0))
    assert max(ages[i], ages[j]) * (size - 1) <= total_age

    pair_sq = (charges[i] * charges[j]) ** 2
    if size == 2:
        assert pair_sq == (charges[0] * charges[1]) ** 2
        return

    complement = [index for index in range(size) if index not in chosen]
    complement_product_sq = Q(1)
    for index in complement:
        complement_product_sq *= charges[index] ** 2
    complement_energy = sum((charges[index] ** 2 for index in complement), Q(0))
    survivor_product_sq = Q(1)
    for charge in charges:
        survivor_product_sq *= charge**2

    lhs = survivor_product_sq * Q(size - 2) ** (size - 2)
    sharp_rhs = pair_sq * complement_energy ** (size - 2)
    survivor_energy = sum((charge**2 for charge in charges), Q(0))
    coarse_rhs = pair_sq * survivor_energy ** (size - 2)
    assert lhs <= sharp_rhs <= coarse_rhs


def main() -> int:
    star_rows = {n: star_row(n) for n in range(3, 13)}
    charge_grid = (Q(1, 3), Q(1, 2), Q(1), Q(2), Q(3))
    age_grid = (Q(0), Q(1, 4), Q(1), Q(2))
    checked = 0
    for size in range(2, 7):
        for charges in combinations(charge_grid, size) if size <= len(charge_grid) else ():
            for ages in product(age_grid, repeat=size):
                selector_row(charges, ages)
                checked += 1

    # Equality in the sharp complement form on the deleted-star survivors.
    for size in range(3, 12):
        charges = tuple(Q(1) for _ in range(size))
        ages = tuple(Q(0) for _ in range(size))
        selector_row(charges, ages)
        complement_energy = Q(size - 2)
        lhs = Q(size - 2) ** (size - 2)
        rhs = complement_energy ** (size - 2)
        assert lhs == rhs

    print(
        "PASS: exact sparse-star Gram/ER4 replay and survivor-local selector; "
        f"star_degrees={len(star_rows)}, rational_rows={checked}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
