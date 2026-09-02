"""Local cyclotomic source adapter for Zudilin's Erdős 1049 determinant.

The global source rows grow quickly in degree.  For a fixed ``Phi_d`` probe,
only each row modulo one power beyond its known scalar order is needed.  This
adapter reconstructs those rows directly in the bounded local quotient and
then assembles the primitive Hankel leading-residue matrix from row residues
and explicit scalar units.
"""

from __future__ import annotations

from functools import lru_cache
from pathlib import Path
import sys
from typing import Any

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

from check_zudilin_phi3_associated_graded import fast_cleared_row  # noqa: E402
from check_zudilin_residual_border_charge import residual_exponent  # noqa: E402
from check_zudilin_scalar_content import mu, p  # noqa: E402
from system.lib.formal_math_cyclotomic_local import CyclotomicLocalRing  # noqa: E402
from system.lib.formal_math_tropical_determinant import (  # noqa: E402
    minimum_weight_determinant,
)


def scalar_cyclotomic_exponent(cyclotomic_index: int, row_index: int) -> int:
    return max(3 * (row_index // cyclotomic_index) - 1, 0)


def _factor_multiplicities(row_index: int, summation_index: int) -> dict[int, int]:
    multiplicities = {
        exponent: (
            3
            - int(exponent <= summation_index)
            - int(exponent <= row_index - summation_index)
        )
        for exponent in range(1, row_index + 1)
    }
    for shift in range(1, row_index + 1):
        exponent = summation_index + shift
        multiplicities[exponent] = multiplicities.get(exponent, 0) + 1
    return multiplicities


@lru_cache(None)
def local_cleared_row(
    row_index: int,
    cyclotomic_index: int,
) -> tuple[tuple[sp.Poly, sp.Poly, sp.Poly], CyclotomicLocalRing]:
    """Return the exact source row modulo ``Phi_d**(e_d(n)+1)``."""

    if row_index < 0:
        raise ValueError("row_index must be nonnegative")
    scalar_order = scalar_cyclotomic_exponent(cyclotomic_index, row_index)
    ring = CyclotomicLocalRing(
        p,
        cyclotomic_index=cyclotomic_index,
        precision=scalar_order + 1,
    )
    factor_cache: dict[tuple[tuple[int, int], ...], sp.Poly] = {}

    def factor_product(multiplicities: dict[int, int]) -> sp.Poly:
        key = tuple(sorted((index, count) for index, count in multiplicities.items()))
        if key not in factor_cache:
            factor_cache[key] = ring.binomial_factor_product(dict(key))
        return factor_cache[key]

    a_polynomial = ring.poly(0)
    b_polynomial = ring.poly(0)
    for summation_index in range(row_index + 1):
        multiplicities = _factor_multiplicities(row_index, summation_index)
        monomial = ring.poly(
            (-1) ** (row_index + summation_index)
            * p ** (summation_index * (summation_index + 1) // 2)
        )
        base = ring.multiply(factor_product(multiplicities), monomial)
        a_polynomial = ring.reduce(a_polynomial + base)
        for ell in range(1, summation_index + 1):
            reduced = dict(multiplicities)
            reduced[ell] -= 1
            b_polynomial = ring.reduce(
                b_polynomial + ring.multiply(factor_product(reduced), monomial)
            )

    gaussian = ring.gaussian_table(2 * row_index)
    c_polynomial = ring.poly(0)
    for ell in range(row_index):
        inner = ring.poly(0)
        for summation_index in range(ell + 1):
            monomial = ring.poly(
                (-1) ** summation_index
                * p
                ** (
                    (row_index - summation_index)
                    * (row_index - summation_index + 1)
                    // 2
                )
            )
            term = ring.multiply(
                gaussian[(row_index, summation_index)],
                gaussian[(row_index + ell - summation_index, row_index)],
                monomial,
            )
            inner = ring.reduce(inner + term)
        multiplicities = {index: 3 for index in range(1, row_index + 1)}
        multiplicities[row_index - ell] -= 1
        c_polynomial = ring.reduce(
            c_polynomial + ring.multiply(factor_product(multiplicities), inner)
        )

    scale = ring.poly(p ** (row_index + 1))
    return (
        tuple(
            ring.multiply(scale, polynomial)
            for polynomial in (a_polynomial, b_polynomial, c_polynomial)
        ),
        ring,
    )


@lru_cache(None)
def scalar_unit_residue(row_index: int, cyclotomic_index: int) -> sp.Poly:
    """Return the scalar row content after its ``Phi_d`` power is removed."""

    ring = CyclotomicLocalRing(p, cyclotomic_index, precision=1)
    unit = ring.poly((-1) ** row_index)
    for index in range(1, row_index + 1):
        if index == cyclotomic_index:
            continue
        exponent = 3 * (row_index // index) - 1
        factor = sp.Poly(sp.cyclotomic_poly(index, p), p, domain=sp.ZZ)
        unit = ring.multiply(unit, factor**exponent)
    return sp.Poly(unit.as_expr(), p, domain=sp.QQ)


@lru_cache(None)
def primitive_row_residue(
    row_index: int,
    cyclotomic_index: int,
) -> tuple[sp.Poly, sp.Poly, sp.Poly]:
    """Return the primitive source triple in ``QQ[p]/(Phi_d)``."""

    local_row, ring = local_cleared_row(row_index, cyclotomic_index)
    scalar_order = scalar_cyclotomic_exponent(cyclotomic_index, row_index)
    inverse_unit = ring.invert_unit_mod_cyclotomic(
        scalar_unit_residue(row_index, cyclotomic_index)
    )
    cyclotomic = sp.Poly(ring.cyclotomic.as_expr(), p, domain=sp.QQ)
    residues = []
    for component in local_row:
        leading = ring.leading_quotient_residue(component, scalar_order)
        residue = sp.Poly(
            leading.as_expr() * inverse_unit.as_expr(),
            p,
            domain=sp.QQ,
        ).rem(cyclotomic)
        residues.append(residue)
    return tuple(residues)  # type: ignore[return-value]


def local_constructor_regression(
    row_index: int,
    cyclotomic_index: int,
) -> dict[str, Any]:
    local_row, ring = local_cleared_row(row_index, cyclotomic_index)
    reference = tuple(component.rem(ring.modulus) for component in fast_cleared_row(row_index))
    return {
        "row_index": row_index,
        "matches_global_source_modulo_local_power": local_row == reference,
        "local_precision": ring.precision,
        "local_modulus_degree": ring.modulus.degree(),
    }


def associated_graded_first_appearance(cyclotomic_index: int) -> dict[str, Any]:
    """Compute the exact first positive-border determinant residue for ``Phi_d``."""

    if cyclotomic_index < 1:
        raise ValueError("cyclotomic_index must be positive")
    rank = 2 * cyclotomic_index + 1
    maximum_moment_index = 2 * rank - 2
    source_residues = [
        primitive_row_residue(index, cyclotomic_index)
        for index in range(maximum_moment_index + 1)
    ]
    scalar_units = [
        scalar_unit_residue(index, cyclotomic_index)
        for index in range(maximum_moment_index + 1)
    ]
    residue_ring = CyclotomicLocalRing(p, cyclotomic_index, precision=1)
    cyclotomic = sp.Poly(
        residue_ring.cyclotomic.as_expr(),
        p,
        domain=sp.QQ.poly_ring(mu),
    )
    inverse_units = [
        residue_ring.invert_unit_mod_cyclotomic(unit)
        for unit in scalar_units[:rank]
    ]

    def reduce_residue(expression: sp.Expr) -> sp.Expr:
        return sp.Poly(
            sp.expand(expression),
            p,
            domain=sp.QQ.poly_ring(mu),
        ).rem(cyclotomic).as_expr()

    weights: list[list[int]] = []
    coefficients: list[list[sp.Expr]] = []
    for row in range(rank):
        weight_row = []
        coefficient_row = []
        for column in range(rank):
            moment_index = row + column
            a_residue, b_residue, c_residue = source_residues[moment_index]
            primitive_moment = (
                a_residue.as_expr() * mu
                - b_residue.as_expr()
                - c_residue.as_expr()
            )
            scalar_ratio = (
                scalar_units[moment_index].as_expr()
                * inverse_units[row].as_expr()
                * inverse_units[column].as_expr()
            )
            coefficient = reduce_residue(primitive_moment * scalar_ratio)
            if coefficient == 0:
                raise AssertionError(
                    "coefficientwise leading row residue vanished; increase local precision"
                )
            weight_row.append(residual_exponent(cyclotomic_index, row, column))
            coefficient_row.append(coefficient)
        weights.append(weight_row)
        coefficients.append(coefficient_row)

    determinant = minimum_weight_determinant(
        weights,
        coefficients,
        one=sp.Integer(1),
        zero=sp.Integer(0),
        normalize=reduce_residue,
    )
    signed_residue = reduce_residue(determinant.signed_coefficient)
    expected_count = (cyclotomic_index + 1) * 2**cyclotomic_index
    if determinant.minimum_permutation_count != expected_count:
        raise AssertionError("minimum assignment graph violates first-appearance theorem")

    regressions = [
        local_constructor_regression(index, cyclotomic_index)
        for index in range(5)
    ]
    if not all(row["matches_global_source_modulo_local_power"] for row in regressions):
        raise AssertionError("local source constructor disagrees with global source")

    primitive_records = [
        {
            "row_index": index,
            "scalar_cyclotomic_order": scalar_cyclotomic_exponent(
                cyclotomic_index, index
            ),
            "a_residue": str(residues[0].as_expr()),
            "b_residue": str(residues[1].as_expr()),
            "c_residue": str(residues[2].as_expr()),
            "scalar_unit_residue": str(scalar_units[index].as_expr()),
        }
        for index, residues in enumerate(source_residues)
    ]
    primitive_mu_vanishing_indices = [
        index
        for index in range(cyclotomic_index, maximum_moment_index + 1)
        if source_residues[index][0].is_zero
    ]
    return {
        "schema": "erdos1049-zudilin-local-cyclotomic-associated-graded/1",
        "rank": rank,
        "cyclotomic_index": cyclotomic_index,
        "cyclotomic_polynomial": str(sp.cyclotomic_poly(cyclotomic_index, p)),
        "maximum_moment_index": maximum_moment_index,
        "forced_border_order": 1,
        "minimum_permutation_order": determinant.minimum_weight,
        "minimum_permutation_count": determinant.minimum_permutation_count,
        "minimum_assignment_count_formula": "(d+1) * 2^d",
        "minimum_assignment_count_matches_formula": True,
        "subset_state_count": determinant.subset_state_count,
        "signed_leading_residue": str(sp.factor(signed_residue)),
        "signed_leading_residue_nonzero": signed_residue != 0,
        "forced_order_is_exact": (
            determinant.minimum_weight == 1 and signed_residue != 0
        ),
        "genuine_minimum_layer_cancellation": signed_residue == 0,
        "mu_zero_residue": str(sp.factor(reduce_residue(signed_residue.subs(mu, 0)))),
        "mu_one_residue": str(sp.factor(reduce_residue(signed_residue.subs(mu, 1)))),
        "signed_leading_residue_is_mu_independent": not signed_residue.has(mu),
        "primitive_mu_coefficient_zero_from_index_d_through_4d": (
            len(primitive_mu_vanishing_indices)
            == maximum_moment_index - cyclotomic_index + 1
        ),
        "primitive_mu_vanishing_indices": primitive_mu_vanishing_indices,
        "local_constructor_regressions": regressions,
        "local_constructor_matches_global_source": True,
        "maximum_local_modulus_degree": int(
            max(
                sp.totient(cyclotomic_index)
                * (scalar_cyclotomic_exponent(cyclotomic_index, index) + 1)
                for index in range(maximum_moment_index + 1)
            )
        ),
        "primitive_row_residues": primitive_records,
        "authority_boundary": (
            "The local quotient computation decides the coefficientwise first-"
            "appearance minimum layer only; it is not an all-rank theorem or an "
            "irrationality proof."
        ),
    }
