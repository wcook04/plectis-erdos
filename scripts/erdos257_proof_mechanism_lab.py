#!/usr/bin/env python3
"""Discriminate local carry laws from genuinely terminal Erdős-257 structure.

The denominator-21 defect experiments suggest the doubling running-maximum
law

    H(2d) <= 2 H(d),    H(d) = 1 + max_{0 <= k < d} C_k.

This script asks the adversarial question first.  It fixes the exact binary
period of 1/21 and the exact Boolean divisor/carry equations

    tau(n) = 2 C(n-1) + epsilon(n) - C(n),
    tau(n) = sum_{a|n} b(a),                 b(a) in {0,1},

but does *not* impose the terminal boundary condition which identifies a
tempered infinite solution.  A mixed-integer feasibility problem then seeks
a prefix with H(2d) > 2 H(d).  Such a prefix is a rigorous countermodel to
any attempt to prove the doubling law from periodic digits, nonnegative
carry, Booleanity, and a square-root carry ceiling alone.

The second audit searches for a strict carry record away from the observed
1/21 phase n == 19 (mod 20).  This separates the source/carry equations from
the actual greedy boundary condition in the same way.

Finite infeasibility is never promoted to a theorem.  Feasible witnesses are
exact: they are independently checked against the divisor convolution and
the carry recurrence before being reported.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
import math
from dataclasses import dataclass

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


problem_id = "erdos_257"


WORD_1_OVER_21 = "000011"
WORD_PERIOD_22 = "0000100101001011000101"


def mobius_sieve(limit: int) -> list[int]:
    mu = [0] * (limit + 1)
    mu[1] = 1
    primes: list[int] = []
    composite = bytearray(limit + 1)
    for value in range(2, limit + 1):
        if not composite[value]:
            primes.append(value)
            mu[value] = -1
        for prime in primes:
            if value * prime > limit:
                break
            composite[value * prime] = 1
            if value % prime == 0:
                mu[value * prime] = 0
                break
            mu[value * prime] = -mu[value]
    return mu


@dataclass(frozen=True)
class PrefixWitness:
    carry: list[int]
    support: list[int]


def base_system(depth: int, cap_factor: float) -> tuple[list[list[tuple[int, int]]], list[int], np.ndarray, np.ndarray]:
    """Return exact equality rows and variable bounds.

    Variables are C_0,...,C_depth followed by b_1,...,b_depth.  The equality
    rows are the Mobius transforms of the carry equations, exactly as in the
    periodic square-root carry MILP.
    """

    mu = mobius_sieve(depth)
    rows: list[list[tuple[int, int]]] = [[] for _ in range(depth)]
    rhs = [0] * depth
    for divisor in range(1, depth + 1):
        digit = int(WORD_1_OVER_21[(divisor - 1) % len(WORD_1_OVER_21)])
        for multiple in range(divisor, depth + 1, divisor):
            coefficient = mu[multiple // divisor]
            if coefficient == 0:
                continue
            rows[multiple - 1].append((divisor - 1, -2 * coefficient))
            rows[multiple - 1].append((divisor, coefficient))
            rhs[multiple - 1] += coefficient * digit
    for rank in range(1, depth + 1):
        rows[rank - 1].append((depth + rank, 1))

    lower = np.zeros(2 * depth + 1)
    upper = np.ones(2 * depth + 1)
    upper[: depth + 1] = [0] + [
        max(2, math.floor(cap_factor * math.sqrt(rank)) + 2)
        for rank in range(1, depth + 1)
    ]
    upper[depth + 1] = 0  # b_1=0 since the target is below one.
    return rows, rhs, lower, upper


def solve_with_extra_constraints(
    depth: int,
    cap_factor: float,
    extra_rows: list[list[tuple[int, float]]],
    extra_lower: list[float],
    extra_upper: list[float],
    bound_edits: list[tuple[int, float | None, float | None]],
) -> PrefixWitness | None:
    rows, rhs, variable_lower, variable_upper = base_system(depth, cap_factor)
    for index, lo, hi in bound_edits:
        if lo is not None:
            variable_lower[index] = lo
        if hi is not None:
            variable_upper[index] = hi

    all_rows: list[list[tuple[int, float]]] = [list(row) for row in rows]
    all_rows.extend(extra_rows)
    constraint_lower = np.asarray(rhs + extra_lower, dtype=float)
    constraint_upper = np.asarray(rhs + extra_upper, dtype=float)

    row_index: list[int] = []
    col_index: list[int] = []
    value: list[float] = []
    for r, row in enumerate(all_rows):
        for c, coefficient in row:
            row_index.append(r)
            col_index.append(c)
            value.append(float(coefficient))
    matrix = coo_matrix(
        (value, (row_index, col_index)),
        shape=(len(all_rows), 2 * depth + 1),
    ).tocsr()
    result = milp(
        c=np.zeros(2 * depth + 1),
        integrality=np.ones(2 * depth + 1),
        bounds=Bounds(variable_lower, variable_upper),
        constraints=LinearConstraint(matrix, constraint_lower, constraint_upper),
        options={"time_limit": 20.0, "presolve": True},
    )
    if not result.success or result.x is None:
        return None
    vector = np.rint(result.x).astype(np.int64)
    carry = vector[: depth + 1].tolist()
    support = vector[depth + 1 :].tolist()
    witness = PrefixWitness(carry=carry, support=support)
    verify_witness(witness)
    return witness


def verify_witness(witness: PrefixWitness) -> None:
    depth = len(witness.support)
    load = [0] * (depth + 1)
    for divisor, bit in enumerate(witness.support, start=1):
        if bit not in (0, 1):
            raise AssertionError("non-Boolean support")
        if bit:
            for multiple in range(divisor, depth + 1, divisor):
                load[multiple] += 1
    if witness.carry[0] != 0 or witness.support[0] != 0:
        raise AssertionError("bad initial state")
    for rank in range(1, depth + 1):
        digit = int(WORD_1_OVER_21[(rank - 1) % len(WORD_1_OVER_21)])
        expected = 2 * witness.carry[rank - 1] + digit - witness.carry[rank]
        if load[rank] != expected:
            raise AssertionError((rank, load[rank], expected))


def running_height(carry: list[int], horizon: int) -> int:
    return 1 + max(carry[:horizon])


def extend_frozen_prefix_one_step(
    witness: PrefixWitness, cap_factor: float
) -> PrefixWitness | None:
    """Ask whether one exact prefix has even one further legal child."""

    prefix_depth = len(witness.support)
    depth = prefix_depth + 1
    edits: list[tuple[int, float | None, float | None]] = [
        (rank, value, value) for rank, value in enumerate(witness.carry)
    ]
    edits.extend(
        (depth + rank, bit, bit)
        for rank, bit in enumerate(witness.support, start=1)
    )
    return solve_with_extra_constraints(
        depth=depth,
        cap_factor=cap_factor,
        extra_rows=[],
        extra_lower=[],
        extra_upper=[],
        bound_edits=edits,
    )


def divisors(rank: int) -> list[int]:
    result: list[int] = []
    for candidate in range(1, math.isqrt(rank) + 1):
        if rank % candidate:
            continue
        result.append(candidate)
        if candidate * candidate != rank:
            result.append(rank // candidate)
    return result


def enumerate_prefix_tree(
    word: str, depth: int, cap_factor: float, max_states: int
) -> dict[str, object]:
    """Enumerate the small exact prefix tree to expose its branching geometry."""

    states: list[tuple[int, int]] = [(0, 0)]  # (terminal carry, support bitset)
    rows: list[dict[str, object]] = []
    for rank in range(1, depth + 1):
        next_states_with_parent: list[tuple[int, int, int, int]] = []
        parent_profiles: list[dict[str, object]] = []
        digit = int(word[(rank - 1) % len(word)])
        bound = max(2, math.floor(cap_factor * math.sqrt(rank)) + 2)
        for carry, bitset in states:
            proper_load = sum(
                (bitset >> (d - 1)) & 1 for d in divisors(rank) if d < rank
            )
            raw = 2 * carry + digit - proper_load
            choices = (0,) if rank == 1 else (0, 1)
            allowed_children: list[int] = []
            for bit in choices:
                next_carry = raw - bit
                if 0 <= next_carry <= bound:
                    allowed_children.append(next_carry)
                    next_states_with_parent.append(
                        (
                            next_carry,
                            bitset | (bit << (rank - 1)),
                            carry,
                            bit,
                        )
                    )
            parent_profiles.append(
                {
                    "parent_carry": carry,
                    "proper_divisor_load": proper_load,
                    "raw_child_carry_before_new_bit": raw,
                    "allowed_child_carries": sorted(allowed_children),
                }
            )
        # Different supports are intentionally retained even when their
        # terminal carry agrees: their divisor service profiles differ.
        states = list(
            dict.fromkeys(
                (next_carry, bitset)
                for next_carry, bitset, _, _ in next_states_with_parent
            )
        )
        terminal_values = sorted({carry for carry, _ in states})
        multiplicities = Counter(carry for carry, _ in states)
        transition_edges = sorted(
            {
                (parent_carry, next_carry, bit)
                for next_carry, _, parent_carry, bit in next_states_with_parent
            }
        )
        children_by_parent: dict[int, list[int]] = defaultdict(list)
        parents_by_child: dict[int, list[int]] = defaultdict(list)
        for parent_carry, next_carry, _ in transition_edges:
            children_by_parent[parent_carry].append(next_carry)
            parents_by_child[next_carry].append(parent_carry)
        children_by_parent = {
            carry: sorted(set(children))
            for carry, children in children_by_parent.items()
        }
        parents_by_child = {
            carry: sorted(set(parents))
            for carry, parents in parents_by_child.items()
        }

        unique_support_by_carry = {
            carry: bitset
            for carry, bitset in states
            if multiplicities[carry] == 1
        }
        adjacent_support_differences: list[dict[str, object]] = []
        for lower, upper in zip(terminal_values, terminal_values[1:]):
            if lower not in unique_support_by_carry or upper not in unique_support_by_carry:
                continue
            lower_support = unique_support_by_carry[lower]
            upper_support = unique_support_by_carry[upper]
            removed = lower_support & ~upper_support
            added = upper_support & ~lower_support
            adjacent_support_differences.append(
                {
                    "lower_carry": lower,
                    "upper_carry": upper,
                    "removed_support": [
                        index + 1 for index in range(rank) if (removed >> index) & 1
                    ],
                    "added_support": [
                        index + 1 for index in range(rank) if (added >> index) & 1
                    ],
                    "hamming_distance": (removed | added).bit_count(),
                }
            )

        common_prefix_length = 0
        if states:
            for index in range(rank):
                bits = {(bitset >> index) & 1 for _, bitset in states}
                if len(bits) != 1:
                    break
                common_prefix_length = index + 1

        target_prefix_integer = sum(
            int(word[(index - 1) % len(word)]) << (rank - index)
            for index in range(1, rank + 1)
        )
        endpoint_identity_holds = True
        for terminal_carry, bitset in states:
            quotient_sum = 0
            for support_rank in range(1, rank + 1):
                if (bitset >> (support_rank - 1)) & 1:
                    quotient_sum += ((1 << rank) // ((1 << support_rank) - 1))
            if quotient_sum != target_prefix_integer - terminal_carry:
                endpoint_identity_holds = False
                break

        full_allowed_interval = terminal_values == list(range(bound + 1))
        rows.append(
            {
                "rank": rank,
                "carry_bound": bound,
                "state_count": len(states),
                "terminal_carry_values": terminal_values,
                "terminal_carry_multiplicities": {
                    str(carry): multiplicities[carry] for carry in terminal_values
                },
                "terminal_values_form_interval": (
                    not terminal_values
                    or terminal_values
                    == list(range(terminal_values[0], terminal_values[-1] + 1))
                ),
                "terminal_values_fill_allowed_interval": full_allowed_interval,
                "unique_state_per_terminal_carry": all(
                    multiplicities[carry] == 1 for carry in terminal_values
                ),
                "common_support_prefix_length": common_prefix_length,
                "first_support_coordinate_that_can_vary": (
                    common_prefix_length + 1
                    if states and common_prefix_length < rank
                    else None
                ),
                "common_prefix_reaches_midpoint": common_prefix_length >= rank // 2,
                "endpoint_quotient_identity_holds": endpoint_identity_holds,
                "transition_edges": [
                    {
                        "parent_carry": parent,
                        "child_carry": child,
                        "new_support_bit": bit,
                    }
                    for parent, child, bit in transition_edges
                ],
                "children_by_parent_carry": {
                    str(carry): children
                    for carry, children in sorted(children_by_parent.items())
                },
                "parents_by_child_carry": {
                    str(carry): parents
                    for carry, parents in sorted(parents_by_child.items())
                },
                "parent_profiles": sorted(
                    parent_profiles, key=lambda profile: int(profile["parent_carry"])
                ),
                "adjacent_support_differences": adjacent_support_differences,
            }
        )
        if len(states) > max_states:
            return {
                "word": word,
                "requested_depth": depth,
                "completed_depth": rank,
                "truncated": True,
                "max_states": max_states,
                "rows": rows,
            }
        if not states:
            break
    return {
        "word": word,
        "requested_depth": depth,
        "completed_depth": rows[-1]["rank"] if rows else 0,
        "truncated": False,
        "final_state_count": len(states),
        "all_levels_fill_allowed_interval": all(
            bool(row["terminal_values_fill_allowed_interval"]) for row in rows
        ),
        "all_levels_unique_by_terminal_carry": all(
            bool(row["unique_state_per_terminal_carry"]) for row in rows
        ),
        "last_level_not_filling_allowed_interval": max(
            (
                int(row["rank"])
                for row in rows
                if not bool(row["terminal_values_fill_allowed_interval"])
            ),
            default=None,
        ),
        "last_level_with_midpoint_borrow_crossing": max(
            (
                int(row["rank"])
                for row in rows
                if not bool(row["common_prefix_reaches_midpoint"])
            ),
            default=None,
        ),
        "endpoint_quotient_identity_holds_at_every_level": all(
            bool(row["endpoint_quotient_identity_holds"]) for row in rows
        ),
        "rows": rows,
    }


def find_doubling_countermodel(
    max_d: int, cap_factor: float, extension_depth: int
) -> dict[str, object]:
    """Find a square-root-bounded prefix violating H(2d)<=2H(d)."""

    for d in range(3, max_d + 1):
        depth = max(2 * d - 1, extension_depth)
        global_cap = max(2, math.floor(cap_factor * math.sqrt(depth)) + 2)
        for h in range(1, global_cap + 1):
            # H(d)<=h means C_0,...,C_(d-1)<=h-1.  Requiring one later carry
            # C_j>=2h forces H(2d)>=2h+1>2H(d).
            for j in range(d, 2 * d):
                edits = [(k, None, h - 1) for k in range(d)]
                edits.append((j, 2 * h, None))
                witness = solve_with_extra_constraints(
                    depth=depth,
                    cap_factor=cap_factor,
                    extra_rows=[],
                    extra_lower=[],
                    extra_upper=[],
                    bound_edits=edits,
                )
                if witness is None:
                    continue
                hd = running_height(witness.carry, d)
                h2d = running_height(witness.carry, 2 * d)
                if not h2d > 2 * hd:
                    raise AssertionError((d, h, j, hd, h2d))
                one_step_extension = extend_frozen_prefix_one_step(
                    witness, cap_factor
                )
                return {
                    "found": True,
                    "d": d,
                    "witness_rank": j,
                    "H_d": hd,
                    "H_2d": h2d,
                    "margin_H_2d_minus_2H_d": h2d - 2 * hd,
                    "max_carry": max(witness.carry),
                    "extension_depth": depth,
                    "carry_prefix": witness.carry[: min(depth + 1, 96)],
                    "terminal_carry": witness.carry[-1],
                    "frozen_one_step_extension_feasible": (
                        one_step_extension is not None
                    ),
                    "frozen_one_step_extension_terminal_carry": (
                        one_step_extension.carry[-1]
                        if one_step_extension is not None
                        else None
                    ),
                    "selected_support": [
                        rank
                        for rank, bit in enumerate(witness.support, start=1)
                        if bit
                    ],
                }
    return {"found": False, "max_d": max_d}


def find_phase_lock_countermodel(
    max_rank: int, cap_factor: float, minimum_rank: int = 20
) -> dict[str, object]:
    """Find a strict carry record n with n+1 not divisible by twenty."""

    for rank in range(minimum_rank, max_rank + 1):
        if (rank + 1) % 20 == 0:
            continue
        depth = rank
        cap = max(2, math.floor(cap_factor * math.sqrt(rank)) + 2)
        for record_value in range(1, cap + 1):
            edits = [(k, None, record_value - 1) for k in range(rank)]
            edits.append((rank, record_value, record_value))
            witness = solve_with_extra_constraints(
                depth=depth,
                cap_factor=cap_factor,
                extra_rows=[],
                extra_lower=[],
                extra_upper=[],
                bound_edits=edits,
            )
            if witness is None:
                continue
            if witness.carry[rank] <= max(witness.carry[:rank]):
                raise AssertionError("record constraint was not realized")
            return {
                "found": True,
                "rank": rank,
                "successor": rank + 1,
                "record_value": witness.carry[rank],
                "prior_max": max(witness.carry[:rank]),
                "max_carry": max(witness.carry),
                "carry": witness.carry,
                "selected_support": [
                    index
                    for index, bit in enumerate(witness.support, start=1)
                    if bit
                ],
            }
    return {"found": False, "max_rank": max_rank}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-d", type=int, default=40)
    parser.add_argument("--max-record-rank", type=int, default=80)
    parser.add_argument("--extension-depth", type=int, default=200)
    parser.add_argument("--tree-depth", type=int, default=24)
    parser.add_argument("--max-tree-states", type=int, default=500000)
    parser.add_argument("--cap-factor", type=float, default=1.0)
    args = parser.parse_args()

    doubling = find_doubling_countermodel(
        args.max_d, args.cap_factor, args.extension_depth
    )
    phase = find_phase_lock_countermodel(args.max_record_rank, args.cap_factor)
    prefix_trees = [
        enumerate_prefix_tree(
            word, args.tree_depth, args.cap_factor, args.max_tree_states
        )
        for word in (WORD_1_OVER_21, WORD_PERIOD_22)
    ]
    payload = {
        "schema": "erdos257_proof_mechanism_lab_v0",
        "parameters": vars(args),
        "exact_constraints": {
            "target_binary_period": WORD_1_OVER_21,
            "carry": "tau(n)=2*C(n-1)+epsilon(n)-C(n)",
            "boolean_ancestry": "tau(n)=sum_{a|n} b(a), b(a) in {0,1}",
            "carry_ceiling": "C(n)<=floor(cap_factor*sqrt(n))+2",
        },
        "doubling_running_maximum_countermodel": doubling,
        "record_phase_lock_countermodel": phase,
        "small_prefix_tree_geometry": prefix_trees,
        "claim_boundary": (
            "A feasible prefix refutes derivability from the displayed local "
            "constraints only.  It does not refute the law on the actual greedy "
            "orbit and does not decide membership or Erdos 257."
        ),
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
