#!/usr/bin/env python3
"""Classify the actual #243 height-24 factor-twenty-five source modes.

The exact height-23 certificate leaves one rigid negative mode: its divided
quotient is zero modulo 24 and its multiplier is one modulo 24.  This checker
does not extend sample orbits.  It refines that complete source cylinder by
25, reconstructs the original source parameter modulo 6,375,600, propagates
the exact quotient chain, and determines the actual height-24 quotient image
modulo 25.  That image decides whether the generic full-payment/cofinal roots
at the factor 25 are genuinely reachable.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any

import numpy as np


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
)
from system.lib.formal_math_residue_cylinder import (  # noqa: E402
    negative_unit_successor_signature,
)

from check_erdos243_height20_payment_seven_cascade import (  # noqa: E402
    HEIGHT_NINETEEN_MODULUS,
    _exact_quotient_array_mod,
)
from check_erdos243_height21_payment_split import (  # noqa: E402
    _affine_coordinates,
    _p_table,
    _source_cylinder,
)
from check_erdos243_height23_composite_split import (  # noqa: E402
    _combine_source_residues,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height24_mod25_split.py"
)
HEIGHT_TWENTY_THREE_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height23_composite_split.py"
)
HEIGHT_TWENTY_THREE_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height23_composite_split_receipt.json"
)
LEAN_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "CleanRecoveryLengthCounterexample.lean"
)
NOTE_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "CleanRecoveryLengthComputationalLab.md"
)
PACKET_REF = (
    "formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/"
    "research_packet.json"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height24_mod25_split_receipt.json"
)
CACHE_PATH = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height24_mod25_affine_cache.npz"
)
CACHE_SCHEMA = "erdos243-height24-mod25-affine-cache/1"
CACHE_SOURCE_REFS = (
    SCRIPT_REF,
    HEIGHT_TWENTY_THREE_REF,
    HEIGHT_TWENTY_THREE_RECEIPT_REF,
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height21_payment_split.py",
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height20_payment_seven_cascade.py",
)

EXPECTED_SOURCE_FAMILIES = 506_880
EXPECTED_HEIGHT_TWENTY_TWO_FAMILIES = 120_931_560
EXPECTED_HEIGHT_TWENTY_THREE_INPUTS = 673_297_902
EXPECTED_HEIGHT_TWENTY_FOUR_INPUTS = EXPECTED_HEIGHT_TWENTY_THREE_INPUTS * 24
EXPECTED_REFINED_CLASSES = EXPECTED_HEIGHT_TWENTY_FOUR_INPUTS * 25
SOURCE_MODULUS = 255_024 * 25
EXPECTED_AFFINE_KEYS = 166_140
EXPECTED_HEIGHT_TWENTY_TWO_KEYS = 32_490
UNIFORM_NONZERO_MODE_COUNT = 11_752_538_688
EXPECTED_C25_COUNTS = {
    0: 298_205_893_008,
    3: UNIFORM_NONZERO_MODE_COUNT,
    5: UNIFORM_NONZERO_MODE_COUNT,
    8: UNIFORM_NONZERO_MODE_COUNT,
    10: UNIFORM_NONZERO_MODE_COUNT,
    13: UNIFORM_NONZERO_MODE_COUNT,
    15: UNIFORM_NONZERO_MODE_COUNT,
    18: UNIFORM_NONZERO_MODE_COUNT,
    20: UNIFORM_NONZERO_MODE_COUNT,
    23: UNIFORM_NONZERO_MODE_COUNT,
}
EXPECTED_MODE_COUNTS = {
    (1, 25, -11): UNIFORM_NONZERO_MODE_COUNT,
    (1, 25, -6): UNIFORM_NONZERO_MODE_COUNT,
    (1, 25, -1): 298_205_893_008,
    (1, 25, 4): UNIFORM_NONZERO_MODE_COUNT,
    (1, 25, 9): UNIFORM_NONZERO_MODE_COUNT,
    (25, 1, 0): 58_762_693_440,
}
COMMON_GLOBAL_MODULUS = 674_632_838_880_000


def _progress(stage: str, **details: int | str) -> None:
    print(
        json.dumps({"stage": stage, **details}, sort_keys=True),
        file=sys.stderr,
        flush=True,
    )


def _cache_source_fingerprint() -> str:
    material = []
    for ref in CACHE_SOURCE_REFS:
        path = REPO_ROOT / ref
        material.append(
            {
                "path": ref,
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            }
        )
    encoded = json.dumps(material, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def _load_height_twenty_two_cache() -> tuple[np.ndarray[Any, Any], np.ndarray[Any, Any], int] | None:
    if not CACHE_PATH.exists():
        return None
    try:
        with np.load(CACHE_PATH, allow_pickle=False) as cache:
            if str(cache["schema"].item()) != CACHE_SCHEMA:
                return None
            if str(cache["source_fingerprint"].item()) != _cache_source_fingerprint():
                return None
            codes = cache["codes"].astype(np.int64)
            weights = cache["weights"].astype(np.int64)
            affine_key_count = int(cache["affine_key_count"].item())
    except (OSError, ValueError, KeyError):
        return None
    if codes.ndim != 1 or weights.shape != codes.shape:
        return None
    if int(np.sum(weights)) != EXPECTED_HEIGHT_TWENTY_TWO_FAMILIES:
        return None
    return codes, weights, affine_key_count


def _write_height_twenty_two_cache(
    codes: np.ndarray[Any, Any],
    weights: np.ndarray[Any, Any],
    affine_key_count: int,
) -> None:
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    temporary = CACHE_PATH.with_suffix(".tmp")
    with temporary.open("wb") as handle:
        np.savez_compressed(
            handle,
            schema=np.array(CACHE_SCHEMA),
            source_fingerprint=np.array(_cache_source_fingerprint()),
            codes=codes,
            weights=weights,
            affine_key_count=np.array(affine_key_count, dtype=np.int64),
        )
    temporary.replace(CACHE_PATH)


def _evaluate_source_polynomial_mod_25(
    coefficients: list[int],
    parameters: np.ndarray[Any, Any],
    modulus: int,
) -> np.ndarray[Any, Any]:
    """Vector Horner evaluation with an explicit operand-size certificate.

    The older source helper uses the deliberately coarse bound ``12*m^2``;
    factor 25 exceeds signed int64 by only 1.1%.  Horner products are much
    smaller because the actual source parameters are bounded independently.
    The sole near-bound product is evaluated as uint64 below.
    """

    parameter_bound = int(np.max(parameters))
    assert (modulus - 1) * parameter_bound + (modulus - 1) < np.iinfo(np.int64).max
    result = np.zeros(parameters.shape, dtype=np.int64)
    for coefficient in reversed(coefficients):
        result = (result * parameters + (coefficient % modulus)) % modulus
    return result


def _t_values_mod_25(
    q10: list[int], parameters: np.ndarray[Any, Any]
) -> np.ndarray[Any, Any]:
    """Evaluate the exact height-19 source coordinate modulo ``10*25``."""

    extra_modulus = 25
    modulus = HEIGHT_NINETEEN_MODULUS * extra_modulus
    q10_values = _evaluate_source_polynomial_mod_25(q10, parameters, modulus)
    left = (q10_values + 1).astype(np.uint64)
    right = ((12 * q10_values - 1) % modulus).astype(np.uint64)
    assert int(np.max(left)) * int(np.max(right)) < np.iinfo(np.uint64).max
    raw_v = ((left * right) % np.uint64(modulus)).astype(np.int64)
    q11 = _exact_quotient_array_mod(
        (raw_v + 1) % modulus,
        divisor=13,
        quotient_modulus=14 * 15 * 17 * 4 * 19 * 10 * extra_modulus,
    )
    w = _exact_quotient_array_mod(
        q11,
        divisor=14,
        quotient_modulus=15 * 17 * 4 * 19 * 10 * extra_modulus,
    )
    c = _exact_quotient_array_mod(
        w,
        divisor=15,
        quotient_modulus=17 * 4 * 19 * 10 * extra_modulus,
    )
    d = _exact_quotient_array_mod(
        c,
        divisor=17,
        quotient_modulus=4 * 19 * 10 * extra_modulus,
    )
    e = _exact_quotient_array_mod(
        d,
        divisor=4,
        quotient_modulus=19 * 10 * extra_modulus,
    )
    return _exact_quotient_array_mod(
        e,
        divisor=19,
        quotient_modulus=10 * extra_modulus,
    )


def _weighted_affine_keys_mod_25() -> tuple[np.ndarray[Any, Any], np.ndarray[Any, Any]]:
    _progress("source_cylinder_start")
    q10, source_classes, t_base = _source_cylinder()
    _progress("source_cylinder_complete", source_family_count=int(source_classes.size))
    columns = [t_base]
    for modulus in (21, 22, 23, 16, 9):
        _progress("affine_coordinate_start", modulus=modulus)
        offset, slope = _affine_coordinates(q10, source_classes, t_base, modulus)
        columns.extend([offset, slope])
        _progress("affine_coordinate_complete", modulus=modulus)
    stacked = np.concatenate(
        [source_classes, source_classes + HEIGHT_NINETEEN_MODULUS]
    )
    _progress("affine_coordinate_start", modulus=25)
    lifted_t = _t_values_mod_25(q10, stacked)
    count = source_classes.size
    at_zero = ((lifted_t[:count] - t_base) // 10) % 25
    at_one = ((lifted_t[count:] - t_base) // 10) % 25
    columns.extend([at_zero, (at_one - at_zero) % 25])
    _progress("affine_coordinate_complete", modulus=25)
    features = np.stack(columns, axis=1)
    keys, weights = np.unique(features, axis=0, return_counts=True)
    assert source_classes.size == EXPECTED_SOURCE_FAMILIES
    assert keys.shape == (EXPECTED_AFFINE_KEYS, 13)
    assert int(np.sum(weights)) == EXPECTED_SOURCE_FAMILIES
    return keys.astype(np.int64), weights.astype(np.int64)


def _pack(columns: list[np.ndarray[Any, Any]]) -> np.ndarray[Any, Any]:
    bases = (462, 23, 23, 16, 16, 9, 9, 25, 25)
    code = columns[0].astype(np.int64)
    for base, column in zip(bases, columns[1:], strict=True):
        code = code * base + column
    return code


def _decode(codes: np.ndarray[Any, Any]) -> list[np.ndarray[Any, Any]]:
    values = codes.copy()
    reversed_columns: list[np.ndarray[Any, Any]] = []
    for base in (25, 25, 9, 9, 16, 16, 23, 23, 462):
        reversed_columns.append(values % base)
        values //= base
    reversed_columns.append(values)
    return list(reversed(reversed_columns))


def _merge_weighted_codes(
    target: Counter[int], codes: np.ndarray[Any, Any], weights: np.ndarray[Any, Any]
) -> None:
    order = np.argsort(codes)
    ordered_codes = codes[order]
    ordered_weights = weights[order]
    starts = np.concatenate([np.array([0]), np.flatnonzero(np.diff(ordered_codes)) + 1])
    totals = np.add.reduceat(ordered_weights, starts)
    for code, weight in zip(ordered_codes[starts], totals, strict=True):
        target[int(code)] += int(weight)


def _height_twenty_two_keys_mod_25() -> tuple[
    np.ndarray[Any, Any], np.ndarray[Any, Any], int, str
]:
    cached = _load_height_twenty_two_cache()
    if cached is not None:
        codes, code_weights, affine_key_count = cached
        _progress("compressed_affine_cache_hit", weighted_key_count=int(codes.size))
        return codes, code_weights, affine_key_count, "source_current_cache_hit"
    _progress("compressed_affine_cache_miss")
    keys, weights = _weighted_affine_keys_mod_25()
    (
        t_base,
        u21,
        slope21,
        u22,
        slope22,
        u23,
        slope23,
        u16,
        slope16,
        u9,
        slope9,
        u25,
        slope25,
    ) = keys.T
    p21_table = _p_table(21)
    p22_table = _p_table(22)
    inverse_21_mod_22 = pow(21, -1, 22)
    aggregated: Counter[int] = Counter()
    weighted_family_count = 0
    for lift21 in range(21):
        coordinate21 = (u21 + slope21 * lift21) % 21
        p21 = p21_table[t_base, coordinate21]
        survives_height_twenty = p21 != 18
        for lift22 in range(22):
            total_lift = lift21 + 21 * lift22
            coordinate22 = (u22 + slope22 * total_lift) % 22
            p22 = p22_table[t_base, coordinate22]
            p462 = p21 + 21 * (((p22 - p21) * inverse_21_mod_22) % 22)
            multiplier20 = 380 * p462 * p462 + 18 * p462 + 1
            r22 = ((multiplier20 - 1) // 21) % 22
            live = survives_height_twenty & (r22 == 0)
            if not bool(np.any(live)):
                continue
            live_weights = weights[live]
            weighted_family_count += int(np.sum(live_weights))
            code = _pack(
                [
                    t_base[live],
                    p462[live],
                    (u23[live] + slope23[live] * total_lift) % 23,
                    (slope23[live] * 462) % 23,
                    (u16[live] + slope16[live] * total_lift) % 16,
                    (slope16[live] * 462) % 16,
                    (u9[live] + slope9[live] * total_lift) % 9,
                    (slope9[live] * 462) % 9,
                    (u25[live] + slope25[live] * total_lift) % 25,
                    slope25[live],
                ]
            )
            _merge_weighted_codes(aggregated, code, live_weights)
    assert weighted_family_count == EXPECTED_HEIGHT_TWENTY_TWO_FAMILIES
    codes = np.array(sorted(aggregated), dtype=np.int64)
    code_weights = np.array([aggregated[int(code)] for code in codes], dtype=np.int64)
    assert int(np.sum(code_weights)) == EXPECTED_HEIGHT_TWENTY_TWO_FAMILIES
    affine_key_count = int(keys.shape[0])
    _write_height_twenty_two_cache(codes, code_weights, affine_key_count)
    _progress("compressed_affine_cache_written", weighted_key_count=int(codes.size))
    return codes, code_weights, affine_key_count, "source_current_cache_written"


def complete_height_twenty_four_split() -> dict[str, Any]:
    codes, weights, affine_key_count, _cache_action = _height_twenty_two_keys_mod_25()
    (
        t_base,
        p462,
        offset23,
        step23,
        offset16,
        step16,
        offset9,
        step9,
        offset25,
        slope25,
    ) = _decode(codes)
    p23_table = _p_table(23)
    p16_table = _p_table(16)
    p9_table = _p_table(9)
    p25_table = _p_table(25)
    inverse_462_mod_23 = pow(462, -1, 23)
    inverse_255024_mod_25 = pow(255_024, -1, 25)
    w25_counts: Counter[int] = Counter()
    c25_counts: Counter[int] = Counter()
    multiplier_counts: Counter[int] = Counter()
    mode_counts: Counter[tuple[int, int, int]] = Counter()
    height_twenty_three_inputs = 0

    for lift23 in range(23):
        coordinate23 = (offset23 + step23 * lift23) % 23
        p23 = p23_table[t_base, coordinate23]
        p10626 = p462 + 462 * (((p23 - p462) * inverse_462_mod_23) % 23)
        multiplier20 = 380 * p10626 * p10626 + 18 * p10626 + 1
        r506 = ((multiplier20 - 1) // 21) % 506
        assert bool(np.all(r506 % 22 == 0))
        s23 = (r506 // 22) % 23
        q23 = (9240 * s23 * s23 + 19 * s23) % 23
        multiplier22_mod23 = (462 * q23 * q23 + 20 * q23 + 1) % 23
        live = multiplier22_mod23 == 1
        height_twenty_three_inputs += int(np.sum(weights[live]))
        if not bool(np.any(live)):
            continue
        live_weights = weights[live]
        p10626_live = p10626[live]
        for lift24 in range(24):
            coordinate16 = (
                offset16[live] + step16[live] * lift23 - step16[live] * lift24
            ) % 16
            coordinate9 = (
                offset9[live] + step9[live] * lift23 - step9[live] * lift24
            ) % 9
            p16 = p16_table[t_base[live], coordinate16]
            p9 = p9_table[t_base[live], coordinate9]
            p255024 = _combine_source_residues(p10626_live, p16, p9)
            for lift25 in range(25):
                total_higher_lift = 462 * lift23 + 10_626 * lift24 + 255_024 * lift25
                coordinate25 = (
                    offset25[live] + slope25[live] * total_higher_lift
                ) % 25
                p25 = p25_table[t_base[live], coordinate25]
                p6375600 = p255024 + 255_024 * (
                    ((p25 - p255024) * inverse_255024_mod_25) % 25
                )
                assert bool(np.all(p6375600 % 255_024 == p255024))
                assert bool(np.all(p6375600 % 25 == p25))
                multiplier20_full = (
                    380 * p6375600 * p6375600 + 18 * p6375600 + 1
                ) % 6_375_600
                assert bool(np.all((multiplier20_full - 1) % 21 == 0))
                r303600 = ((multiplier20_full - 1) // 21) % 303_600
                multiplier21 = (
                    420 * r303600 * r303600 + 19 * r303600 + 1
                ) % 303_600
                assert bool(np.all((multiplier21 - 1) % 22 == 0))
                q13800 = ((multiplier21 - 1) // 22) % 13_800
                multiplier22 = (
                    462 * q13800 * q13800 + 20 * q13800 + 1
                ) % 13_800
                assert bool(np.all((multiplier22 - 1) % 23 == 0))
                z600 = ((multiplier22 - 1) // 23) % 600
                assert bool(np.all(z600 % 24 == 0))
                w25 = (z600 // 24) % 25
                multiplier23 = (506 * z600 * z600 + 21 * z600 + 1) % 600
                assert bool(np.all((multiplier23 - 1) % 24 == 0))
                c25 = ((multiplier23 - 1) // 24) % 25
                assert bool(np.all(c25 == (12_144 * w25 * w25 + 21 * w25) % 25))
                multiplier24 = (552 * c25 * c25 + 22 * c25 + 1) % 25
                unique_w, inverse_w = np.unique(w25, return_inverse=True)
                totals_w = np.bincount(inverse_w, weights=live_weights).astype(np.int64)
                for residue, count in zip(unique_w, totals_w, strict=True):
                    w25_counts[int(residue)] += int(count)
                unique_c, inverse_c = np.unique(c25, return_inverse=True)
                totals_c = np.bincount(inverse_c, weights=live_weights).astype(np.int64)
                for residue, count in zip(unique_c, totals_c, strict=True):
                    c25_counts[int(residue)] += int(count)
                unique_m, inverse_m = np.unique(multiplier24, return_inverse=True)
                totals_m = np.bincount(inverse_m, weights=live_weights).astype(np.int64)
                for residue, count in zip(unique_m, totals_m, strict=True):
                    signature = negative_unit_successor_signature(24, int(residue))
                    multiplier_counts[int(residue)] += int(count)
                    mode_counts[signature] += int(count)

    assert height_twenty_three_inputs == EXPECTED_HEIGHT_TWENTY_THREE_INPUTS
    assert affine_key_count == EXPECTED_AFFINE_KEYS
    assert int(codes.size) == EXPECTED_HEIGHT_TWENTY_TWO_KEYS
    assert sum(w25_counts.values()) == EXPECTED_REFINED_CLASSES
    assert sum(c25_counts.values()) == EXPECTED_REFINED_CLASSES
    assert sum(mode_counts.values()) == EXPECTED_REFINED_CLASSES
    assert c25_counts == EXPECTED_C25_COUNTS
    assert mode_counts == EXPECTED_MODE_COUNTS
    return {
        "compressed_affine_cache_status": "source_current_digest_bound",
        "compressed_affine_cache_schema": CACHE_SCHEMA,
        "compressed_affine_cache_source_fingerprint": _cache_source_fingerprint(),
        "joint_affine_key_count_mod_25": affine_key_count,
        "height_twenty_two_weighted_key_count_mod_25": int(codes.size),
        "height_twenty_three_input_count": height_twenty_three_inputs,
        "height_twenty_four_input_count": EXPECTED_HEIGHT_TWENTY_FOUR_INPUTS,
        "logical_refined_class_count": EXPECTED_REFINED_CLASSES,
        "preceding_quotient_counts_mod_25": {
            str(key): value for key, value in sorted(w25_counts.items())
        },
        "height_twenty_four_quotient_counts_mod_25": {
            str(key): value for key, value in sorted(c25_counts.items())
        },
        "multiplier_residue_counts_mod_25": {
            str(key): value for key, value in sorted(multiplier_counts.items())
        },
        "successor_mode_counts": {
            f"payment={key[0]},height={key[1]},error={key[2]}": value
            for key, value in sorted(mode_counts.items())
        },
    }


def symbolic_height_twenty_four_modes() -> dict[str, Any]:
    modes: dict[tuple[int, int, int], list[int]] = {}
    for c in range(25):
        multiplier = 552 * c * c + 22 * c + 1
        signature = negative_unit_successor_signature(24, multiplier)
        modes.setdefault(signature, []).append(c)
    quotient_map: dict[int, list[int]] = {}
    preceding_modes: dict[tuple[int, int, int], list[int]] = {}
    for w in range(25):
        c = (12_144 * w * w + 21 * w) % 25
        quotient_map.setdefault(c, []).append(w)
        multiplier = (552 * c * c + 22 * c + 1) % 25
        preceding_modes.setdefault(
            negative_unit_successor_signature(24, multiplier), []
        ).append(w)
    cofinal_w = sorted(
        w
        for c, preimages in quotient_map.items()
        if c % 5 in {1, 3}
        for w in preimages
    )
    assert cofinal_w == [2, 4, 7, 9, 12, 14, 17, 19, 22, 24]
    return {
        "height_twenty_four_multiplier": "552*c^2+22*c+1",
        "source_digits_by_successor_mode": {
            f"payment={key[0]},height={key[1]},error={key[2]}": value
            for key, value in sorted(modes.items())
        },
        "full_payment_identity": (
            "(552*c^2+22*c+1)-2*(c-1)*(c-3)="
            "5*(110*c^2+6*c-1)"
        ),
        "full_payment_residue_classes_mod_5": [1, 3],
        "preceding_quotient_map_mod_25": {
            str(key): value for key, value in sorted(quotient_map.items())
        },
        "cofinal_preceding_quotient_classes_mod_25": cofinal_w,
        "cofinal_preceding_quotient_classes_mod_5": [2, 4],
        "preceding_quotient_classes_by_successor_mode": {
            f"payment={key[0]},height={key[1]},error={key[2]}": value
            for key, value in sorted(preceding_modes.items())
        },
    }


def build_receipt() -> dict[str, Any]:
    previous = json.loads(
        (REPO_ROOT / HEIGHT_TWENTY_THREE_RECEIPT_REF).read_text(encoding="utf-8")
    )
    assert previous["status"] == "verified_exact_height_twenty_three_singleton_mode"
    split = complete_height_twenty_four_split()
    modes = symbolic_height_twenty_four_modes()
    cofinal = EXPECTED_MODE_COUNTS[(25, 1, 0)]
    positive = (
        EXPECTED_MODE_COUNTS[(1, 25, 4)]
        + EXPECTED_MODE_COUNTS[(1, 25, 9)]
    )
    negative = EXPECTED_REFINED_CLASSES - cofinal - positive
    zero_global = 21_499_360_633_728 * 25 + 3 * cofinal
    positive_global = 5_437_475_472_528 * 25 + 3 * positive
    negative_global = 3 * negative
    assert (zero_global, positive_global, negative_global) == (
        537_660_303_923_520,
        136_007_402_045_328,
        965_132_911_152,
    )
    assert zero_global + positive_global + negative_global == COMMON_GLOBAL_MODULUS
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact complete classification of 403978741200 actual height-24 "
            "factor-25 refinements: 58762693440 force full payment and cofinal "
            "return, 23505077376 switch positive, and 321710970384 remain "
            "negative; unrestricted #243 remains open."
        ),
        hypothesis_id="height_twenty_four_source_reaches_factor25_cofinal_roots",
        hypothesis_statement=(
            "The actual height-24 quotient image intersects c mod 5 in {1,3}, "
            "forcing full payment 25 and a cofinal return."
        ),
        probe_id="weighted_affine_height24_mod25_source_split",
        probe_question=(
            "Which generic factor-25 successor modes occur on the complete exact "
            "height-24 source image?"
        ),
        computation=(
            "Add the mod-25 affine source coordinates to the compressed cylinder, "
            "reconstruct p modulo 6375600, propagate the exact quotient chain, "
            "and classify all 25-adic refinements."
        ),
        falsifier=(
            "No actual quotient residue congruent to 1 or 3 modulo 5, hence zero "
            "full-payment/cofinal classes."
        ),
        stop_condition=(
            "Stop after the complete factor-25 source image and successor modes "
            "are classified; do not audit later orbit horizons."
        ),
        survival_consequence=(
            "Any actual c congruent to 1 or 3 modulo 5 forces payment 25 and an "
            "immediate cofinal return."
        ),
        falsification_consequence=(
            "An image disjoint from those roots eliminates the factor-25 cofinal "
            "mechanism and isolates the realized negative continuation modes."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.heightTwentyFour_fullPaymentRootIdentity",
            "ErdosProblems.Erdos243.heightTwentyFour_multiplierAtOneModFiveIdentity",
            "ErdosProblems.Erdos243.heightTwentyFour_multiplierAtThreeModFiveIdentity",
            "ErdosProblems.Erdos243.heightTwentyFour_precedingQuotientTwoIdentity",
            "ErdosProblems.Erdos243.heightTwentyFour_precedingQuotientFourIdentity",
            "ErdosProblems.Erdos243.heightTwentyFour_fullPayment",
            "ErdosProblems.Erdos243.heightTwentyFour_fullCollapse",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, HEIGHT_TWENTY_THREE_RECEIPT_REF],
        source_refs=[SCRIPT_REF, HEIGHT_TWENTY_THREE_REF, HEIGHT_TWENTY_THREE_RECEIPT_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "Exactly 58762693440 actual refinements hit payment 25 and return "
            "cofinally; 23505077376 switch positive, the generic error-minus-nine "
            "mode is absent, and 321710970384 remain in three negative modes."
        ),
        progress_class="mechanism_opened",
        decision_basis=(
            "Complete weighted affine source-cylinder enumeration at factor 25 "
            "opens an actual cofinal-return mechanism and removes 20.3643812% of "
            "the incoming negative support by collapse or sign switch."
        ),
        next_analytic_target=(
            "Test whether source-affine fibers give a uniform subunit upper bound "
            "on negative continuation mass across subsequent factors; this would "
            "turn the observed factor-25 loss into an expanding-boundary kill."
        ),
        resource_bounds={
            "source_family_count": EXPECTED_SOURCE_FAMILIES,
            "logical_classified_lifts": EXPECTED_REFINED_CLASSES,
            "source_modulus": SOURCE_MODULUS,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-height24-mod25-split-receipt/1",
        "status": "verified_exact_height_twenty_four_cofinal_opening",
        "complete_height_twenty_four_split": split,
        "symbolic_height_twenty_four_modes": modes,
        "factor_twenty_five_outcome_counts": {
            "cofinal_return": cofinal,
            "positive_switch": positive,
            "continuing_negative": negative,
            "removed_from_negative_support": cofinal + positive,
        },
        "cumulative_source_class_partition": {
            "common_modulus": COMMON_GLOBAL_MODULUS,
            "zero_centered_class_count": zero_global,
            "positive_centered_class_count": positive_global,
            "continuing_negative_candidate_class_count": negative_global,
            "height_twenty_five_negative_candidate_count": negative_global,
            "exact_partition": (
                "537660303923520 zero + 136007402045328 positive + "
                "965132911152 negative = 674632838880000"
            ),
        },
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SCRIPT_REF,
                HEIGHT_TWENTY_THREE_REF,
                HEIGHT_TWENTY_THREE_RECEIPT_REF,
                LEAN_REF,
                NOTE_REF,
                PACKET_REF,
            ]
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--explore", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.explore:
        print(json.dumps({
            "split": complete_height_twenty_four_split(),
            "symbolic_modes": symbolic_height_twenty_four_modes(),
        }, indent=2, sort_keys=True))
        return 0
    rendered = json.dumps(build_receipt(), indent=2, sort_keys=True) + "\n"
    output = args.output.resolve()
    if args.check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"stale or missing receipt: {output}", file=sys.stderr)
            return 1
        print(json.dumps({"status": "current", "output": str(output)}))
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": "written", "output": str(output)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
