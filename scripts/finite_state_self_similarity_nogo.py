#!/usr/bin/env python3
"""Finite audits for the exact no-go in FiniteStateSelfSimilarityNoGo.md."""

from itertools import product


Matrix = tuple[tuple[int, int], tuple[int, int]]
Vector = tuple[int, int]

IDENTITY: Matrix = ((1, 0), (0, 1))
LEFT: Matrix = ((1, 1), (0, 1))
RIGHT: Matrix = ((1, 0), (1, 1))


def multiply(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2))
        for i in range(2)
    )  # type: ignore[return-value]


def apply(matrix: Matrix, vector: Vector) -> Vector:
    a, b = vector
    return (
        matrix[0][0] * a + matrix[0][1] * b,
        matrix[1][0] * a + matrix[1][1] * b,
    )


def determinant(matrix: Matrix) -> int:
    return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]


def check_split_words(max_length: int = 10, max_endpoint: int = 40) -> int:
    checks = 0
    for length in range(1, max_length + 1):
        for word in product([LEFT, RIGHT], repeat=length):
            matrix = IDENTITY
            for letter in word:
                matrix = multiply(letter, matrix)
            assert determinant(matrix) == 1
            for a in range(1, max_endpoint + 1):
                for b in range(1, max_endpoint + 1):
                    x, y = apply(matrix, (a, b))
                    # No direct projective return Wv = k v.
                    assert x * b != y * a
                    # No projective return after using M(a,b)=M(b,a).
                    assert x * a != y * b
                    checks += 1
    return checks


def affine_iterate(c: int, d: int, n: int, steps: int) -> list[int]:
    orbit = []
    for _ in range(steps):
        orbit.append(n)
        n = c * n + d
    return orbit


def check_affine_clock_examples() -> dict[str, object]:
    additive = affine_iterate(1, 7, 3, 12)
    assert all(additive[k + 1] - additive[k] == 7 for k in range(11))
    expanding = affine_iterate(3, 2, 4, 12)
    reciprocal_partial = sum(1 / n for n in expanding)
    geometric_majorant = sum(1 / (4 * 3**k) for k in range(12))
    assert reciprocal_partial <= geometric_majorant
    return {
        "additive_clock": additive,
        "additive_period": 7,
        "expanding_clock": expanding,
        "expanding_reciprocal_partial": reciprocal_partial,
        "geometric_majorant_partial": geometric_majorant,
    }


def main() -> None:
    print(
        {
            "split_word_vector_checks": check_split_words(),
            "all_split_word_determinants": 1,
            "projective_endpoint_cycles_found": 0,
            "affine_clock_examples": check_affine_clock_examples(),
            "additive_cycle_route": "eventually periodic support",
            "expanding_cycle_route": "reciprocal-summable support",
        }
    )


if __name__ == "__main__":
    main()
