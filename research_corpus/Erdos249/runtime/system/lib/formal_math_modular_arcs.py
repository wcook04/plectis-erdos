"""Exact certificates for central arcs under projection of integer moduli.

If ``m`` divides ``n``, centrality of the least residue modulo ``m`` forces
centrality modulo ``n``.  The direction is easy to reverse accidentally:
centrality modulo the larger modulus need not survive reduction modulo a
divisor.  This module records the residue layer explicitly so experiments can
bind either implication or a converse counterexample without floating point.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class CentralArcProjection:
    value: int
    radius: int
    small_modulus: int
    large_modulus: int
    modulus_factor: int
    small_residue: int
    large_residue: int
    residue_layer: int
    small_central: bool
    large_central: bool

    def to_dict(self) -> dict[str, int | bool]:
        return asdict(self)


def in_open_central_arc(residue: int, modulus: int, radius: int) -> bool:
    """Return ``radius < residue < modulus - radius`` exactly."""

    if modulus <= 0:
        raise ValueError("modulus must be positive")
    if radius < 0:
        raise ValueError("radius must be nonnegative")
    if not 0 <= residue < modulus:
        raise ValueError("residue must be the least nonnegative representative")
    return radius < residue < modulus - radius


def certify_central_arc_projection(
    value: int, *, small_modulus: int, large_modulus: int, radius: int
) -> CentralArcProjection:
    """Certify the one-way central-arc implication for ``small | large``.

    Writing ``r_large = layer * small_modulus + r_small`` gives
    ``0 <= layer < large_modulus / small_modulus``.  Hence a central
    ``r_small`` is automatically farther than ``radius`` from both endpoints
    of the large modulus.  The returned layer is the exact arithmetic witness.
    """

    if small_modulus <= 0 or large_modulus <= 0:
        raise ValueError("moduli must be positive")
    if large_modulus % small_modulus:
        raise ValueError("small_modulus must divide large_modulus")
    if radius < 0:
        raise ValueError("radius must be nonnegative")

    small_residue = value % small_modulus
    large_residue = value % large_modulus
    difference = large_residue - small_residue
    assert difference % small_modulus == 0
    residue_layer = difference // small_modulus
    modulus_factor = large_modulus // small_modulus
    assert 0 <= residue_layer < modulus_factor

    small_central = in_open_central_arc(
        small_residue, small_modulus, radius
    )
    large_central = in_open_central_arc(
        large_residue, large_modulus, radius
    )
    if small_central:
        assert large_central

    return CentralArcProjection(
        value=value,
        radius=radius,
        small_modulus=small_modulus,
        large_modulus=large_modulus,
        modulus_factor=modulus_factor,
        small_residue=small_residue,
        large_residue=large_residue,
        residue_layer=residue_layer,
        small_central=small_central,
        large_central=large_central,
    )
