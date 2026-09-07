#!/usr/bin/env python3
"""Adversarial receipts for reversible laminar packet stabilization."""

from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction


def shadow_mass(rank: int) -> Fraction:
    return Fraction(1 << 2, 1 << rank)


def weight(rank: int) -> Fraction:
    return Fraction(1, (1 << rank) - 1)


def cylinder(a: int, b: int) -> Fraction:
    return weight(a) * weight(b)


@dataclass
class WeakReplayMachine:
    """The weak semantics permits replaying an unchanged complete epoch."""

    target_rank: int
    rho: Fraction = Fraction(3, 8)
    rewrites: int = 0
    openings: int = 0

    def cycle(self) -> None:
        parent_rank = self.target_rank - 3
        parent_mass = shadow_mass(parent_rank)
        child_mass = 2 * shadow_mass(self.target_rank)
        assert parent_rank < self.target_rank
        assert child_mass < self.rho * parent_mass
        # Open into two finite, later-rank children, then merge them.  Weak
        # rollback restores the same parent epoch, so the method can repeat.
        self.openings += 1
        assert 2 * shadow_mass(self.target_rank) == shadow_mass(
            self.target_rank - 1
        )
        self.rewrites += 1


@dataclass
class LinearEpochMachine:
    """The same local gadget with consume-on-open epoch state."""

    target_rank: int
    opened: bool = False
    rewrites: int = 0

    def cycle(self) -> None:
        if self.opened:
            raise RuntimeError("consumed ownership epoch cannot be replayed")
        self.opened = True
        self.rewrites += 1


def depth_cutoff(total_root_mass: Fraction, rho: Fraction, rank: int) -> int:
    """First k for which depth-k mass cannot fund one rank-r collision."""
    required = 2 * shadow_mass(rank)
    depth = 0
    remaining = total_root_mass
    while remaining >= required:
        remaining *= rho
        depth += 1
    assert remaining < required
    return depth


def prefix_counter(bits: set[int], cutoff: int) -> int:
    return sum(1 << (cutoff - rank) for rank in bits if rank <= cutoff)


def insert_visible(bits: set[int], rank: int) -> None:
    """Insert one shadow bit and normalize duplicate ranks by left carry."""
    while rank in bits:
        bits.remove(rank)
        rank -= 1
        if rank < 1:
            raise OverflowError("rank-one shadow overflow")
    bits.add(rank)


def promote_overlap(bits: set[int], rank: int) -> None:
    """Replace a parked rank-r bit by its exact predecessor recut."""
    assert rank in bits and rank >= 2
    bits.remove(rank)
    insert_visible(bits, rank - 1)


def minimal_complete_packet(rank: int) -> Fraction:
    return shadow_mass(rank) / 3


def funded_run_margin(rank: int, carries: int) -> Fraction:
    value = minimal_complete_packet(rank) + sum(
        (weight(rank - offset) for offset in range(carries)), Fraction()
    )
    return value - weight(rank - carries)


def minimal_funded_run_capacity(rank: int) -> int:
    capacity = 0
    for carries in range(1, rank - 1):
        if funded_run_margin(rank, carries) > 0:
            capacity = carries
        else:
            break
    return capacity


def predecessor_recut_receipt(maximum_rank: int = 180) -> dict[str, object]:
    checks = 0
    for rank in range(4, maximum_rank + 1):
        lower_complete_value = shadow_mass(rank) / 3
        upper_complete_value = Fraction(4, 3) * shadow_mass(rank) / 3
        assert lower_complete_value >= weight(rank) + cylinder(rank - 1, rank)
        assert upper_complete_value < 2 * weight(rank)
        assert 3 * weight(rank) < 2 * weight(rank - 1)
        assert minimal_funded_run_capacity(rank) == (rank - 2) // 2
        checks += 1

    root_tail = (
        cylinder(2, 3)
        - weight(5)
        - weight(7)
        - weight(8)
        - weight(9)
        - weight(10)
    )
    assert root_tail == Fraction(508634, 806159805)
    assert weight(11) < root_tail < 2 * weight(11)
    post_recut_residual = root_tail - weight(11)
    assert post_recut_residual == Fraction(235013993, 1650209120835)
    assert post_recut_residual < minimal_complete_packet(12)

    rank_12_margins = {
        carries: funded_run_margin(12, carries) for carries in range(1, 7)
    }
    assert all(rank_12_margins[carries] > 0 for carries in range(1, 6))
    assert rank_12_margins[6] < 0
    assert rank_12_margins[5] == Fraction(
        530622738299, 13180550289933312
    )
    assert rank_12_margins[6] == -Fraction(
        7817180893091, 92263852029533184
    )

    cutoff = 24
    bits = {5, 7, 8, 9, 10, 12}
    before = prefix_counter(bits, cutoff)
    promote_overlap(bits, 12)
    after = prefix_counter(bits, cutoff)
    assert bits == {5, 7, 8, 9, 10, 11}
    assert after > before

    # Adversarial insertions and overlap promotions remain strict binary
    # counter increments until the finite prefix saturates.
    trace = []
    for rank in [24, 24, 23, 22, 22, 21, 20, 20, 19, 18, 18]:
        previous = prefix_counter(bits, cutoff)
        insert_visible(bits, rank)
        current = prefix_counter(bits, cutoff)
        assert current > previous
        trace.append(current - previous)

    return {
        "full_bank_rank_checks": checks,
        "exact_minimal_run_capacity": "floor((r-2)/2)",
        "root_tail_after_5_7_8_9_10": str(root_tail),
        "root_recut_rank": 11,
        "post_recut_residual": str(post_recut_residual),
        "post_recut_residual_below_minimal_rank_12_packet": True,
        "rank_12_minimal_funded_run_capacity": 5,
        "rank_12_sixth_carry_margin": str(rank_12_margins[6]),
        "rank_12_overlap_counter_increment": after - before,
        "adversarial_counter_increments": trace,
    }


def root_receipt() -> dict[str, object]:
    later_rho = Fraction(32771, 131068)
    global_rho = Fraction(755, 2048)
    assert later_rho < Fraction(251, 1000) < global_rho < Fraction(1, 2)
    assert 2 * shadow_mass(10) == shadow_mass(9)

    coefficient = 1510
    exponents = [bit for bit in range(coefficient.bit_length()) if coefficient & (1 << bit)]
    child_ranks = [2 + 15 - exponent for exponent in exponents]
    assert exponents == [1, 2, 5, 6, 7, 8, 10]
    assert child_ranks == [16, 15, 12, 11, 10, 9, 7]
    assert all(rank > 5 for rank in child_ranks)
    child_load = Fraction(coefficient, 1 << 15)
    parent_load = shadow_mass(5)
    assert child_load / parent_load == global_rho

    cutoffs = {
        str(rank): depth_cutoff(parent_load, global_rho, rank)
        for rank in range(5, 26)
    }
    return {
        "root_front_rank": 5,
        "root_shadow_mass": str(parent_load),
        "global_rho_including_first_opening": str(global_rho),
        "later_complete_component_rho": str(later_rho),
        "first_residual_coefficient": coefficient,
        "first_child_ranks": child_ranks,
        "collision_depth_cutoffs_by_rank": cutoffs,
    }


def main() -> None:
    weak = WeakReplayMachine(target_rank=8)
    for _ in range(1000):
        weak.cycle()
    assert weak.openings == weak.rewrites == 1000

    linear = LinearEpochMachine(target_rank=8)
    linear.cycle()
    blocked = False
    try:
        linear.cycle()
    except RuntimeError:
        blocked = True
    assert blocked and linear.rewrites == 1

    output = {
        "weak_countermodel": {
            "target_rank": weak.target_rank,
            "rho": str(weak.rho),
            "finite_prefix_rewrites": weak.rewrites,
            "can_continue_indefinitely": True,
            "missing_axiom": "linear consume-on-open ownership epochs",
        },
        "linear_epoch_model": {
            "same_epoch_replay_blocked": blocked,
            "rewrites_before_block": linear.rewrites,
        },
        "root_system": root_receipt(),
        "predecessor_recut": predecessor_recut_receipt(),
        "theorem_boundary": (
            "The root violates local disjoint-front laminarity at rank 12; "
            "its first predecessor recut closes exactly, but general prefix "
            "termination additionally needs the funded-hole condition."
        ),
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
