#!/usr/bin/env python3
"""Exact finite counterexample to laminar set-valued shadow ownership."""

from __future__ import annotations

import json
from fractions import Fraction


def carry_mass(rank: int) -> Fraction:
    if rank < 2:
        raise ValueError("rank must be at least two")
    return Fraction(1, 1 << (rank - 2))


def main() -> None:
    rank = 4
    rho_later = Fraction(32771, 131068)

    # Sixteen equal label quanta realise all masses exactly.
    ancestor = frozenset({0, 1, 2, 3})
    internal_child = frozenset({0})
    external_at_rank_six = frozenset({4})
    external_at_rank_five = frozenset({5, 6})

    assert Fraction(len(ancestor), 16) == carry_mass(rank)
    assert Fraction(len(internal_child), 16) == carry_mass(rank + 2)
    assert Fraction(len(external_at_rank_six), 16) == carry_mass(rank + 2)
    assert Fraction(len(external_at_rank_five), 16) == carry_mass(rank + 1)
    assert Fraction(len(internal_child), len(ancestor)) == Fraction(1, 4)
    assert Fraction(1, 4) < rho_later
    assert internal_child < ancestor
    assert ancestor.isdisjoint(external_at_rank_six)
    assert ancestor.isdisjoint(external_at_rank_five)

    first_carry = internal_child | external_at_rank_six
    assert Fraction(len(first_carry), 16) == carry_mass(rank + 1)
    assert first_carry.isdisjoint(external_at_rank_five)

    returned = first_carry | external_at_rank_five
    assert Fraction(len(returned), 16) == carry_mass(rank)
    overlap = ancestor & returned
    union = ancestor | returned

    assert overlap == internal_child
    assert overlap
    assert not ancestor <= returned
    assert not returned <= ancestor
    assert Fraction(len(union), 16) == Fraction(7, 16)
    assert carry_mass(rank - 1) == Fraction(1, 2)
    assert Fraction(len(union), 16) < carry_mass(rank - 1)

    output = {
        "schema": "laminar_shadow_collision_counterexample_v0",
        "rho_later": str(rho_later),
        "opening_ratio": "1/4",
        "states": {
            "parked_ancestor_A": {"rank": 4, "label": sorted(ancestor), "mass": "1/4"},
            "internal_child_a": {"rank": 6, "label": sorted(internal_child), "mass": "1/16"},
            "external_B": {"rank": 6, "label": sorted(external_at_rank_six), "mass": "1/16"},
            "external_C": {"rank": 5, "label": sorted(external_at_rank_five), "mass": "1/8"},
            "first_carry_X": {"rank": 5, "label": sorted(first_carry), "mass": "1/8"},
            "returned_F": {"rank": 4, "label": sorted(returned), "mass": "1/4"},
        },
        "crossing": {
            "A_intersection_F": sorted(overlap),
            "intersection_mass": "1/16",
            "A_union_F_mass": "7/16",
            "rank_3_required_mass": "1/2",
            "laminar": False,
            "disjoint": False,
            "ownership_doubling_available": False,
        },
        "rollback": (
            "To close A exactly, reverse X+C and then a+B before deleting a. "
            "The returned front F disappears; rollback does not create a "
            "disjoint rank-4 collision."
        ),
        "minimal_repair": (
            "consume or freeze an ancestor shadow before an external descendant "
            "collision, or replace set-valued ownership by a multiplicity/cocycle object"
        ),
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
