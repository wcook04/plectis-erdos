#!/usr/bin/env python3
"""Search the constant-negative centered-state obstruction for Erdős #243.

If the centered integer state is fixed at ``E_n = -m``, then

    C_{n+1} = C_n + m,
    C_{n+1} * Δ_n = -m * (a_n^2 - 1).

Thus every next step is forced when the displayed divisibility holds.  This
script searches exact integer seeds and reports long forced prefixes.  The
Lean theorems ``no_constantNegative_orbit`` and
``no_eventuallyConstantNegative_orbit`` now prove that no fixed natural
constant-negative orbit persists at any scale.  The search remains useful as
finite obstruction data and as a regression fixture for the exact recurrence.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import dataclass


problem_id = "erdos_243"


sys.set_int_max_str_digits(1_000_000)


@dataclass(frozen=True)
class State:
    index: int
    a: int
    C: int
    D: int
    defect: int | None


@dataclass(frozen=True)
class Orbit:
    m: int
    a0: int
    C0: int
    states: tuple[State, ...]
    stop_reason: str

    @property
    def completed_steps(self) -> int:
        return len(self.states) - 1


def initial_den_state(m: int, a: int, C: int) -> int:
    return (a - 1) * C - m


def advance(m: int, state: State) -> tuple[State | None, str | None]:
    next_C = state.C + m
    numerator = m * (state.a * state.a - 1)
    if numerator % next_C:
        return None, "defect_not_integral"
    defect = -(numerator // next_C)
    next_a = state.a * state.a - state.a + 1 + defect
    if next_a <= state.a:
        return None, "not_strictly_increasing"
    next_D = state.a * state.D
    expected_D = (next_a - 1) * next_C - m
    if next_D != expected_D:
        raise AssertionError(
            {
                "reason": "defect_identity_mismatch",
                "next_D": next_D,
                "expected_D": expected_D,
            }
        )
    return (
        State(
            index=state.index + 1,
            a=next_a,
            C=next_C,
            D=next_D,
            defect=defect,
        ),
        None,
    )


def orbit(m: int, a0: int, C0: int, step_limit: int) -> Orbit:
    if min(m, C0) < 1 or a0 < 2:
        raise ValueError("require m,C0 >= 1 and a0 >= 2")
    D0 = initial_den_state(m, a0, C0)
    if D0 <= 0:
        return Orbit(m, a0, C0, (), "initial_den_state_nonpositive")
    states = [State(index=0, a=a0, C=C0, D=D0, defect=None)]
    for _ in range(step_limit):
        next_state, reason = advance(m, states[-1])
        if next_state is None:
            return Orbit(m, a0, C0, tuple(states), reason or "unknown")
        states.append(next_state)
    return Orbit(m, a0, C0, tuple(states), "step_limit")


def search(
    max_m: int,
    max_C0: int,
    max_a0: int,
    step_limit: int,
    keep: int,
    include_states: bool,
) -> dict[str, object]:
    leaders: list[Orbit] = []
    stop_counts: dict[str, int] = {}
    seed_count = 0
    for m in range(1, max_m + 1):
        for C0 in range(1, max_C0 + 1):
            for a0 in range(2, max_a0 + 1):
                candidate = orbit(m, a0, C0, step_limit)
                seed_count += 1
                stop_counts[candidate.stop_reason] = stop_counts.get(candidate.stop_reason, 0) + 1
                leaders.append(candidate)
                leaders.sort(
                    key=lambda item: (
                        item.completed_steps,
                        len(item.states),
                        -item.m,
                        -item.C0,
                        -item.a0,
                    ),
                    reverse=True,
                )
                del leaders[keep:]
    def compact_int(value: int, inline_digits: int = 160) -> int | dict[str, object]:
        text = str(value)
        if len(text) <= inline_digits:
            return value
        return {
            "decimal_digits": len(text),
            "leading_40": text[:40],
            "trailing_40": text[-40:],
        }

    def compact_state(state: State) -> dict[str, object]:
        return {
            "index": state.index,
            "a": compact_int(state.a),
            "C": compact_int(state.C),
            "D": compact_int(state.D),
            "defect": None if state.defect is None else compact_int(state.defect),
        }

    return {
        "schema": "erdos243-constant-negative-state-search/1",
        "claim_ceiling": (
            "finite_exact_search_not_counterexample_or_full_rigidity_proof; "
            "every_eventually_constant_negative_branch_is_lean_excluded"
        ),
        "bounds": {
            "max_m": max_m,
            "max_C0": max_C0,
            "max_a0": max_a0,
            "step_limit": step_limit,
        },
        "seed_count": seed_count,
        "stop_counts": dict(sorted(stop_counts.items())),
        "max_completed_steps": leaders[0].completed_steps if leaders else 0,
        "leaders": [
            {
                "m": item.m,
                "a0": item.a0,
                "C0": item.C0,
                "scale_normal_form": {
                    "common_scale": math.gcd(item.m, item.C0),
                    "m": item.m // math.gcd(item.m, item.C0),
                    "C0": item.C0 // math.gcd(item.m, item.C0),
                },
                "completed_steps": item.completed_steps,
                "stop_reason": item.stop_reason,
                **(
                    {"states": [compact_state(state) for state in item.states]}
                    if include_states
                    else {}
                ),
            }
            for item in leaders
        ],
    }


def assert_packet_fixtures() -> list[str]:
    base = orbit(1, 1501, 1, 25)
    scaled = orbit(7, 1501, 7, 25)
    if base.completed_steps != 17 or base.stop_reason != "defect_not_integral":
        raise AssertionError("the a0=1501 exact prefix fixture changed")
    if tuple(state.a for state in base.states) != tuple(state.a for state in scaled.states):
        raise AssertionError("common scaling changed the forced a-orbit")
    if tuple(7 * state.C for state in base.states) != tuple(state.C for state in scaled.states):
        raise AssertionError("common scaling changed the C-orbit incorrectly")
    if tuple(7 * state.D for state in base.states) != tuple(state.D for state in scaled.states):
        raise AssertionError("common scaling changed the D-orbit incorrectly")
    return [
        "a0_1501_has_17_step_exact_prefix",
        "common_scaling_preserves_forced_a_orbit",
        "common_scaling_scales_C_and_D",
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-m", type=int, default=20)
    parser.add_argument("--max-C0", type=int, default=120)
    parser.add_argument("--max-a0", type=int, default=160)
    parser.add_argument("--steps", type=int, default=12)
    parser.add_argument("--keep", type=int, default=12)
    parser.add_argument("--omit-states", action="store_true")
    parser.add_argument("--assert-packet", action="store_true")
    args = parser.parse_args()
    result = search(
        args.max_m,
        args.max_C0,
        args.max_a0,
        args.steps,
        args.keep,
        not args.omit_states,
    )
    if args.assert_packet:
        result["packet_assertions"] = assert_packet_fixtures()
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
