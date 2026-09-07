#!/usr/bin/env python3
"""Exact audits for the zero-buffer target 90/511.

The finite orbit is certified by the directed-interval routine in
``sparse_clock_gauge_audit.py``.  The separate rational calculation gives a
same-binary-cylinder perturbation whose greedy block crosses the endpoint
energy barrier.  No finite output of this script is an all-depth statement.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction

from sparse_clock_gauge_audit import states


TARGET = Fraction(90, 511)
WORD = "001011010"


def source_bits(target: Fraction, depth: int) -> list[int]:
    floors = [int(target * (1 << rank)) for rank in range(depth + 1)]
    return [0] + [
        floors[rank] - 2 * floors[rank - 1]
        for rank in range(1, depth + 1)
    ]


def exact_fraction_states(target: Fraction, depth: int) -> dict[str, object]:
    """Compute a short orbit with exact rational greedy decisions."""
    bits = [0] * (depth + 1)
    residual = target
    for rank in range(1, depth + 1):
        weight = Fraction(1, (1 << rank) - 1)
        if residual >= weight:
            bits[rank] = 1
            residual -= weight

    digits = source_bits(target, depth)
    divisor_count = [0] * (depth + 1)
    for divisor in range(1, depth + 1):
        if bits[divisor]:
            for multiple in range(divisor, depth + 1, divisor):
                divisor_count[multiple] += 1

    prefix_count = [0] * (depth + 1)
    source_count = 0
    defect = 0
    energy = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        prefix_count[rank] = prefix_count[rank - 1] + bits[rank]
        source_count += digits[rank]
        defect = 2 * defect + digits[rank] - divisor_count[rank]
        delayed_state = (
            source_count + prefix_count[rank // 2] - prefix_count[rank]
        )
        energy[rank] = delayed_state - 2 * defect
    return {
        "bits": bits,
        "source_bits": digits,
        "energy": energy,
        "residual": residual,
    }


def same_cylinder_seam_receipt() -> dict[str, object]:
    """Verify the exact 10000/01111 seam at ranks 10--14."""
    # At rank 14 the target phase is 325/511.  Removing 273/(511*2^14)
    # remains inside the same length-14 binary cylinder.
    perturbation = Fraction(273, 511 * (1 << 14))
    perturbed = TARGET - perturbation
    exact = exact_fraction_states(TARGET, 14)
    lower = exact_fraction_states(perturbed, 14)

    assert exact["source_bits"][1:] == lower["source_bits"][1:]
    assert exact["bits"][1:10] == lower["bits"][1:10]
    assert exact["bits"][10:15] == [1, 0, 0, 0, 0]
    assert lower["bits"][10:15] == [0, 1, 1, 1, 1]
    assert exact["energy"][14] == 3
    assert lower["energy"][14] == -2

    prefix = Fraction(1, 7) + Fraction(1, 31)
    exact_seam = (1 << 10) * (TARGET - prefix)
    lower_seam = (1 << 10) * (perturbed - prefix)
    take_threshold = Fraction(1 << 10, (1 << 10) - 1)
    late_block_cost = (1 << 10) * sum(
        (Fraction(1, (1 << rank) - 1) for rank in range(11, 15)),
        Fraction(),
    )
    assert late_block_cost <= lower_seam < take_threshold < exact_seam

    return {
        "target": str(TARGET),
        "perturbed_target": str(perturbed),
        "perturbation": str(perturbation),
        "common_source_prefix": "".join(
            map(str, exact["source_bits"][1:])
        ),
        "common_greedy_prefix_through_9": "".join(
            map(str, exact["bits"][1:10])
        ),
        "target_block_10_14": "10000",
        "perturbed_block_10_14": "01111",
        "target_energy_at_14": exact["energy"][14],
        "perturbed_energy_at_14": lower["energy"][14],
        "late_block_scaled_cost": str(late_block_cost),
        "perturbed_scaled_seam": str(lower_seam),
        "take_threshold": str(take_threshold),
        "target_scaled_seam": str(exact_seam),
        "claim_status": "exact rational calculation",
    }


def block_and_drift_receipt(depth: int) -> dict[str, object]:
    orbit = states(90, 511, 9, depth)
    bits = orbit["bits"]
    defects = orbit["defects"]
    energy = orbit["energy"]

    first_tenth_drift_failure = next(
        (
            {
                "rank": rank,
                "energy": energy[rank],
                "floor_rank_over_10": rank // 10,
            }
            for rank in range(6, depth + 1)
            if energy[rank] < rank // 10
        ),
        None,
    )
    minimum_tenth_drift_slack = min(
        (energy[rank] - rank // 10, rank)
        for rank in range(6, depth + 1)
    )

    worst_blocks: dict[str, object] = {}
    for length in (9, 18):
        row = min(
            (
                energy[start + length] - energy[start],
                start,
                energy[start],
                energy[start + length],
                defects[start],
                defects[start + length],
            )
            for start in range(9, depth - length + 1, 9)
        )
        worst_blocks[str(length)] = {
            "energy_increment": row[0],
            "start": row[1],
            "start_energy": row[2],
            "end_energy": row[3],
            "start_defect": row[4],
            "end_defect": row[5],
        }

    # Check the exact period-nine cocycle at every aligned block.  The seam
    # term is the change in B(floor(N/2)).
    prefix = [0] * (depth + 1)
    for rank in range(1, depth + 1):
        prefix[rank] = prefix[rank - 1] + bits[rank]
    for start in range(9, depth - 8, 9):
        selected = prefix[start + 9] - prefix[start]
        seam = prefix[(start + 9) // 2] - prefix[start // 2]
        asserted_increment = (
            4
            - selected
            + seam
            - 2 * (defects[start + 9] - defects[start])
        )
        assert energy[start + 9] - energy[start] == asserted_increment

    return {
        "depth": depth,
        "first_floor_N_over_10_failure": first_tenth_drift_failure,
        "minimum_floor_N_over_10_slack": {
            "slack": minimum_tenth_drift_slack[0],
            "rank": minimum_tenth_drift_slack[1],
        },
        "worst_aligned_period_blocks": worst_blocks,
        "period_nine_cocycle_verified_through": depth,
        "orbit_summary": orbit["summary"],
        "claim_status": "exact finite directed-interval computation",
    }


def product_renormalisation_receipt() -> dict[str, object]:
    """Verify the first scaled-product subtraction exactly."""
    w = lambda rank: Fraction(1, (1 << rank) - 1)
    residual = 16 * w(5) * w(9)
    after_10 = residual - w(10)
    asserted = 527 * w(5) * w(9) * w(10)
    assert after_10 == asserted > 0
    assert after_10 < w(14)
    assert after_10 >= w(15)
    return {
        "identity": (
            "2^r*w_a*w_b - w_(a+b-r) = "
            "(2^a+2^b-2^r-1)*w_a*w_b*w_(a+b-r)"
        ),
        "instance": "16*w_5*w_9 - w_10 = 527*w_5*w_9*w_10",
        "next_selected_rank": 15,
        "claim_status": "exact rational identity and comparisons",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=10_000)
    args = parser.parse_args()
    if args.depth < 100:
        raise SystemExit("depth must be at least 100")
    print(
        json.dumps(
            {
                "target": str(TARGET),
                "source_word": WORD,
                "same_cylinder_seam": same_cylinder_seam_receipt(),
                "period_block_and_linear_drift": block_and_drift_receipt(
                    args.depth
                ),
                "scaled_product_renormalisation": (
                    product_renormalisation_receipt()
                ),
                "global_claim_status": (
                    "exact identities and one exact finite counterexample; "
                    "the all-depth zero-buffer inequality remains open"
                ),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
