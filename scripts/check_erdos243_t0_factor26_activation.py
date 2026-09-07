#!/usr/bin/env python3
"""Test factor-26 activation on the exact inert ``t=0`` #243 subfamily.

The factor-25 parent census proves that all inert parents have source digit
zero modulo ten and that all 25 of their children retain centered error -1.
Thus the next raw height factor is only 26.  This checker proves by exact
comparison that the two possible new 2-adic quotient parities have the same
multiplier-residue multiset on actual parent support.  It can therefore reuse
the factor-25 cache and classify all 26 refinements of each of the
257,072,007,600 inert children parent-by-parent without materializing the
larger source cylinder.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from collections import Counter
from pathlib import Path
from typing import Any

import numpy as np


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_residue_cylinder import (  # noqa: E402
    affine_lift_coordinates_mod,
    centered_successor_signature,
)
from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
    validate_experiment_contract,
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
from check_erdos243_height24_mod25_split import (  # noqa: E402
    EXPECTED_HEIGHT_TWENTY_TWO_FAMILIES,
    _decode,
    _height_twenty_two_keys_mod_25,
    _pack,
)


SCRIPT_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_t0_factor26_activation.py"
)
HEIGHT_TWENTY_FOUR_REF = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height24_parent_contraction.py"
)
HEIGHT_TWENTY_FOUR_RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_height24_parent_contraction_receipt.json"
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
    "erdos243_t0_factor26_activation_receipt.json"
)
CACHE_PATH = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_t0_factor26_affine_cache.npz"
)
CACHE_SCHEMA = "erdos243-t0-factor26-affine-cache/1"
PARENT_CACHE_PATH = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos243_t0_factor26_parent_cache.npz"
)
PARENT_CACHE_SCHEMA = "erdos243-t0-factor26-parent-cache/3"
CACHE_SOURCE_REFS = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height24_mod25_split.py",
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height23_composite_split.py",
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height21_payment_split.py",
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos243_height20_payment_seven_cascade.py",
)

CURRENT_SOURCE_MODULUS = 6_375_600
TARGET_SOURCE_MODULUS = CURRENT_SOURCE_MODULUS * 26
EXPECTED_T0_HEIGHT_TWENTY_THREE_INPUTS = 428_453_346
EXPECTED_T0_HEIGHT_TWENTY_FOUR_PARENTS = 10_282_880_304
EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN = 257_072_007_600
EXPECTED_FACTOR26_REFINEMENTS = EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN * 26
EXPECTED_FACTOR26_PARENT_PROFILES = {
    "cofinal=0,positive=4,negative=22": EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN,
}
EXPECTED_FACTOR26_MULTIPLIER_COUNTS = {
    "1": 2_056_576_060_800,
    "13": 3_599_008_106_400,
    "15": 1_028_288_030_400,
}
EXPECTED_FACTOR26_MODE_COUNTS = {
    "payment=1,height=26,error=-1": 2_056_576_060_800,
    "payment=1,height=26,error=9": 1_028_288_030_400,
    "payment=13,height=2,error=-1": 3_599_008_106_400,
}
EXPECTED_EFFECTIVE_PARENT_PROFILES = {
    "cofinal=14,positive=4,negative=8": EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN,
}
EXPECTED_SOURCE_STEP13_WEIGHT_COUNTS = {
    "1": 19_239_048,
    "5": 19_239_432,
    "8": 19_238_928,
    "12": 19_238_928,
}


def _progress(stage: str, **details: int | str) -> None:
    print(json.dumps({"stage": stage, **details}, sort_keys=True), file=sys.stderr, flush=True)


def _source_fingerprint() -> str:
    rows = []
    for ref in CACHE_SOURCE_REFS:
        path = REPO_ROOT / ref
        rows.append({"path": ref, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    return hashlib.sha256(
        json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def _pack_extension(columns: list[np.ndarray[Any, Any]]) -> np.ndarray[Any, Any]:
    code = columns[0].astype(np.int64)
    for base, column in zip((32, 13, 13), columns[1:], strict=True):
        code = code * base + column
    return code


def _decode_extension(codes: np.ndarray[Any, Any]) -> list[np.ndarray[Any, Any]]:
    values = codes.copy()
    reversed_columns = []
    for base in (13, 13, 32):
        reversed_columns.append(values % base)
        values //= base
    reversed_columns.append(values)
    return list(reversed(reversed_columns))


def _merge_weighted_code_pairs(
    target: Counter[tuple[int, int]],
    old_codes: np.ndarray[Any, Any],
    extension_codes: np.ndarray[Any, Any],
    weights: np.ndarray[Any, Any],
) -> None:
    pairs = np.stack([old_codes, extension_codes], axis=1)
    order = np.lexsort((pairs[:, 1], pairs[:, 0]))
    ordered = pairs[order]
    ordered_weights = weights[order]
    changes = np.any(np.diff(ordered, axis=0) != 0, axis=1)
    starts = np.concatenate([np.array([0]), np.flatnonzero(changes) + 1])
    totals = np.add.reduceat(ordered_weights, starts)
    for pair, weight in zip(ordered[starts], totals, strict=True):
        target[(int(pair[0]), int(pair[1]))] += int(weight)


def _load_cache() -> tuple[np.ndarray[Any, Any], np.ndarray[Any, Any], np.ndarray[Any, Any], int] | None:
    if not CACHE_PATH.exists():
        return None
    try:
        with np.load(CACHE_PATH, allow_pickle=False) as cache:
            if str(cache["schema"].item()) != CACHE_SCHEMA:
                return None
            if str(cache["source_fingerprint"].item()) != _source_fingerprint():
                return None
            old_codes = cache["old_codes"].astype(np.int64)
            extension_codes = cache["extension_codes"].astype(np.int64)
            weights = cache["weights"].astype(np.int64)
            source_key_count = int(cache["source_key_count"].item())
    except (OSError, ValueError, KeyError):
        return None
    if old_codes.shape != extension_codes.shape or old_codes.shape != weights.shape:
        return None
    if int(np.sum(weights)) != EXPECTED_HEIGHT_TWENTY_TWO_FAMILIES:
        return None
    return old_codes, extension_codes, weights, source_key_count


def _write_cache(
    old_codes: np.ndarray[Any, Any],
    extension_codes: np.ndarray[Any, Any],
    weights: np.ndarray[Any, Any],
    source_key_count: int,
) -> None:
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    temporary = CACHE_PATH.with_suffix(".tmp")
    with temporary.open("wb") as handle:
        np.savez_compressed(
            handle,
            schema=np.array(CACHE_SCHEMA),
            source_fingerprint=np.array(_source_fingerprint()),
            old_codes=old_codes,
            extension_codes=extension_codes,
            weights=weights,
            source_key_count=np.array(source_key_count, dtype=np.int64),
        )
    temporary.replace(CACHE_PATH)


def _safe_t_values(
    q10: list[int],
    parameters: np.ndarray[Any, Any],
    extra_modulus: int,
) -> np.ndarray[Any, Any]:
    """Evaluate the source coordinate after reducing both product factors.

    The legacy conservative ``12*m^2`` bound rejects modulus 32 even though
    Horner products and the factorwise-reduced quadratic product fit signed
    int64 on the exact source parameter range.
    """

    modulus = HEIGHT_NINETEEN_MODULUS * extra_modulus
    parameter_bound = int(np.max(parameters))
    assert (modulus - 1) * parameter_bound + (modulus - 1) < np.iinfo(np.int64).max
    q_values = np.zeros(parameters.shape, dtype=np.int64)
    for coefficient in reversed(q10):
        q_values = (q_values * parameters + (coefficient % modulus)) % modulus
    left = (q_values + 1) % modulus
    right = (12 * q_values - 1) % modulus
    assert (modulus - 1) * (modulus - 1) < np.iinfo(np.int64).max
    raw_v = (left * right) % modulus
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


def _weighted_extended_source_keys() -> tuple[np.ndarray[Any, Any], np.ndarray[Any, Any]]:
    _progress("source_cylinder_start")
    q10, source_classes, t_base = _source_cylinder()
    _progress("source_cylinder_complete", source_family_count=int(source_classes.size))
    columns = [t_base]
    for modulus in (21, 22, 23, 16, 9):
        _progress("affine_coordinate_start", modulus=modulus)
        offset, slope = _affine_coordinates(q10, source_classes, t_base, modulus)
        columns.extend([offset, slope])
        _progress("affine_coordinate_complete", modulus=modulus)
    for modulus in (25, 32, 13):
        _progress("affine_coordinate_start", modulus=modulus)
        stacked = np.concatenate(
            [source_classes, source_classes + HEIGHT_NINETEEN_MODULUS]
        )
        lifted = _safe_t_values(q10, stacked, modulus)
        count = source_classes.size
        at_zero = ((lifted[:count] - t_base) // 10) % modulus
        at_one = ((lifted[count:] - t_base) // 10) % modulus
        offset, slope = affine_lift_coordinates_mod(
            at_zero, at_one, modulus=modulus
        )
        columns.extend([offset, slope])
        _progress("affine_coordinate_complete", modulus=modulus)
    features = np.stack(columns, axis=1)
    keys, weights = np.unique(features, axis=0, return_counts=True)
    assert int(np.sum(weights)) == 506_880
    return keys.astype(np.int64), weights.astype(np.int64)


def _height_twenty_two_extended_keys() -> tuple[
    np.ndarray[Any, Any], np.ndarray[Any, Any], np.ndarray[Any, Any], int, str
]:
    cached = _load_cache()
    if cached is not None:
        old_codes, extension_codes, weights, source_key_count = cached
        _progress("extended_affine_cache_hit", weighted_key_count=int(old_codes.size))
        return old_codes, extension_codes, weights, source_key_count, "source_current_cache_hit"
    _progress("extended_affine_cache_miss")
    keys, weights = _weighted_extended_source_keys()
    source_key_count = int(keys.shape[0])
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
        u32,
        slope32,
        u13,
        slope13,
    ) = keys.T
    p21_table = _p_table(21)
    p22_table = _p_table(22)
    inverse_21_mod_22 = pow(21, -1, 22)
    aggregated: Counter[tuple[int, int]] = Counter()
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
            old_code = _pack(
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
            extension_code = _pack_extension(
                [
                    (u32[live] + slope32[live] * total_lift) % 32,
                    slope32[live],
                    (u13[live] + slope13[live] * total_lift) % 13,
                    slope13[live],
                ]
            )
            _merge_weighted_code_pairs(aggregated, old_code, extension_code, live_weights)
    assert weighted_family_count == EXPECTED_HEIGHT_TWENTY_TWO_FAMILIES
    pairs = sorted(aggregated)
    old_codes = np.array([pair[0] for pair in pairs], dtype=np.int64)
    extension_codes = np.array([pair[1] for pair in pairs], dtype=np.int64)
    code_weights = np.array([aggregated[pair] for pair in pairs], dtype=np.int64)
    assert int(np.sum(code_weights)) == EXPECTED_HEIGHT_TWENTY_TWO_FAMILIES
    _write_cache(old_codes, extension_codes, code_weights, source_key_count)
    _progress("extended_affine_cache_written", weighted_key_count=int(old_codes.size))
    return old_codes, extension_codes, code_weights, source_key_count, "source_current_cache_written"


def _merge_profiles(
    target: Counter[tuple[int, int, int]],
    cofinal: np.ndarray[Any, Any],
    positive: np.ndarray[Any, Any],
    negative: np.ndarray[Any, Any],
    weights: np.ndarray[Any, Any],
) -> None:
    codes = cofinal * 27 * 27 + positive * 27 + negative
    order = np.argsort(codes)
    ordered = codes[order]
    ordered_weights = weights[order]
    starts = np.concatenate([np.array([0]), np.flatnonzero(np.diff(ordered)) + 1])
    totals = np.add.reduceat(ordered_weights, starts)
    for code, weight in zip(ordered[starts], totals, strict=True):
        c, remainder = divmod(int(code), 27 * 27)
        p, n = divmod(remainder, 27)
        target[(c, p, n)] += int(weight)


def _pack_factor26_parent(
    p_current: np.ndarray[Any, Any],
) -> np.ndarray[Any, Any]:
    return p_current.astype(np.int64)


def _decode_factor26_parent(
    codes: np.ndarray[Any, Any],
) -> np.ndarray[Any, Any]:
    return codes


def _merge_weighted_codes(
    target: Counter[int],
    codes: np.ndarray[Any, Any],
    weights: np.ndarray[Any, Any],
) -> None:
    order = np.argsort(codes)
    ordered_codes = codes[order]
    ordered_weights = weights[order]
    starts = np.concatenate(
        [np.array([0]), np.flatnonzero(np.diff(ordered_codes)) + 1]
    )
    totals = np.add.reduceat(ordered_weights, starts)
    for code, weight in zip(ordered_codes[starts], totals, strict=True):
        target[int(code)] += int(weight)


def _load_parent_cache() -> tuple[np.ndarray[Any, Any], np.ndarray[Any, Any]] | None:
    if not PARENT_CACHE_PATH.exists():
        return None
    try:
        with np.load(PARENT_CACHE_PATH, allow_pickle=False) as cache:
            if str(cache["schema"].item()) != PARENT_CACHE_SCHEMA:
                return None
            if str(cache["affine_schema"].item()) != CACHE_SCHEMA:
                return None
            if str(cache["source_fingerprint"].item()) != _source_fingerprint():
                return None
            codes = cache["codes"].astype(np.int64)
            weights = cache["weights"].astype(np.int64)
    except (OSError, ValueError, KeyError):
        return None
    if codes.shape != weights.shape:
        return None
    if int(np.sum(weights)) != EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN:
        return None
    return codes, weights


def _write_parent_cache(
    codes: np.ndarray[Any, Any], weights: np.ndarray[Any, Any]
) -> None:
    PARENT_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    temporary = PARENT_CACHE_PATH.with_suffix(".tmp")
    with temporary.open("wb") as handle:
        np.savez_compressed(
            handle,
            schema=np.array(PARENT_CACHE_SCHEMA),
            affine_schema=np.array(CACHE_SCHEMA),
            source_fingerprint=np.array(_source_fingerprint()),
            codes=codes,
            weights=weights,
        )
    temporary.replace(PARENT_CACHE_PATH)


def _build_t0_factor26_parent_keys() -> tuple[
    np.ndarray[Any, Any], np.ndarray[Any, Any], dict[str, int | str]
]:
    cached = _load_parent_cache()
    if cached is not None:
        codes, weights = cached
        _progress("factor26_parent_cache_hit", parent_key_count=int(codes.size))
        return codes, weights, {
            "factor26_parent_cache_action": "source_current_cache_hit",
            "factor26_parent_key_count": int(codes.size),
        }

    old_codes, weights, source_key_count, affine_cache_action = (
        _height_twenty_two_keys_mod_25()
    )
    extended_weighted_key_count = int(old_codes.size)
    old_columns = _decode(old_codes)
    t0_keys = old_columns[0] == 0
    old_columns = [column[t0_keys] for column in old_columns]
    weights = weights[t0_keys]
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
    ) = old_columns
    p23_table = _p_table(23)
    p16_table = _p_table(16)
    p9_table = _p_table(9)
    p25_table = _p_table(25)
    inverse_462_mod_23 = pow(462, -1, 23)
    inverse_255024_mod_25 = pow(255_024, -1, 25)
    aggregated = np.zeros(CURRENT_SOURCE_MODULUS, dtype=np.int64)
    t0_height23_inputs = 0
    t0_height24_parents = 0
    t0_height25_children = 0

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
        t0_height23_inputs += int(np.sum(weights[live]))
        if not bool(np.any(live)):
            continue
        live_weights = weights[live]
        p10626_live = p10626[live]
        for lift24 in range(24):
            t0_height24_parents += int(np.sum(live_weights))
            coordinate16 = (
                offset16[live] + step16[live] * lift23 - step16[live] * lift24
            ) % 16
            coordinate9 = (
                offset9[live] + step9[live] * lift23 - step9[live] * lift24
            ) % 9
            p16 = p16_table[t_base[live], coordinate16]
            p9 = p9_table[t_base[live], coordinate9]
            p255024 = _combine_source_residues(p10626_live, p16, p9)
            t0_height25_children += 25 * int(np.sum(live_weights))
            lift25 = np.arange(25, dtype=np.int64)[None, :]
            total_through_25 = (
                462 * lift23 + 10_626 * lift24 + 255_024 * lift25
            )
            coordinate25 = (
                offset25[live, None]
                + slope25[live, None] * total_through_25
            ) % 25
            p25 = p25_table[t_base[live, None], coordinate25]
            p6375600 = p255024[:, None] + 255_024 * (
                ((p25 - p255024[:, None]) * inverse_255024_mod_25) % 25
            )
            codes = _pack_factor26_parent(p6375600)
            broadcast_weights = np.broadcast_to(live_weights[:, None], codes.shape)
            np.add.at(aggregated, codes.ravel(), broadcast_weights.ravel())
        _progress("factor26_parent_lift23_complete", lift23=lift23)

    assert t0_height23_inputs == EXPECTED_T0_HEIGHT_TWENTY_THREE_INPUTS
    assert t0_height24_parents == EXPECTED_T0_HEIGHT_TWENTY_FOUR_PARENTS
    assert t0_height25_children == EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN
    codes = np.flatnonzero(aggregated).astype(np.int64)
    parent_weights = aggregated[codes]
    assert int(np.sum(parent_weights)) == EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN
    _write_parent_cache(codes, parent_weights)
    _progress("factor26_parent_cache_written", parent_key_count=int(codes.size))
    return codes, parent_weights, {
        "extended_affine_cache_action": affine_cache_action,
        "source_key_count": source_key_count,
        "height_twenty_two_mod25_weighted_key_count": extended_weighted_key_count,
        "t0_height_twenty_two_extended_key_count": int(weights.size),
        "t0_height_twenty_three_input_count": t0_height23_inputs,
        "t0_height_twenty_four_parent_count": t0_height24_parents,
        "t0_height_twenty_five_child_count": t0_height25_children,
        "factor26_parent_cache_action": "source_current_cache_written",
        "factor26_parent_key_count": int(codes.size),
    }


def _factor26_source_lift_certificate() -> dict[str, Any]:
    old_codes, extension_codes, weights, _, cache_action = (
        _height_twenty_two_extended_keys()
    )
    t0_keys = _decode(old_codes)[0] == 0
    _, slope32, _, slope13 = _decode_extension(extension_codes)
    step32 = (slope32[t0_keys] * CURRENT_SOURCE_MODULUS) % 32
    step13 = (slope13[t0_keys] * CURRENT_SOURCE_MODULUS) % 13
    t0_weights = weights[t0_keys]
    assert bool(np.all(step32 == 0))
    assert bool(np.all(step13 != 0))
    step13_counts = {
        str(int(residue)): int(np.sum(t0_weights[step13 == residue]))
        for residue in np.unique(step13)
    }
    assert step13_counts == EXPECTED_SOURCE_STEP13_WEIGHT_COUNTS
    return {
        "extended_affine_cache_action": cache_action,
        "t0_extended_weighted_key_count": int(np.sum(t0_keys)),
        "t0_extended_weight": int(np.sum(t0_weights)),
        "mod32_source_step_image": [0],
        "mod13_source_step_weight_counts": step13_counts,
        "consequence": (
            "each 26-lift source fiber freezes one quotient parity and cycles "
            "through all 13 odd-prime coordinates twice"
        ),
    }


def _uncompressed_reference_census() -> dict[str, Any]:
    old_codes, extension_codes, weights, source_key_count, cache_action = (
        _height_twenty_two_extended_keys()
    )
    extended_weighted_key_count = int(old_codes.size)
    old_columns = _decode(old_codes)
    t0_keys = old_columns[0] == 0
    old_columns = [column[t0_keys] for column in old_columns]
    extension_columns = [
        column[t0_keys] for column in _decode_extension(extension_codes)
    ]
    weights = weights[t0_keys]
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
    ) = old_columns
    offset32, slope32, offset13, slope13 = extension_columns
    p23_table = _p_table(23)
    p16_table = _p_table(16)
    p9_table = _p_table(9)
    p25_table = _p_table(25)
    p32_table = _p_table(32)
    p13_table = _p_table(13)
    inverse_462_mod_23 = pow(462, -1, 23)
    inverse_255024_mod_25 = pow(255_024, -1, 25)
    inverse_12751200_mod_13 = pow(12_751_200, -1, 13)
    profiles: Counter[tuple[int, int, int]] = Counter()
    mode_counts: Counter[tuple[int, int, int]] = Counter()
    multiplier25_counts: Counter[int] = Counter()
    t0_height23_inputs = 0
    t0_height24_parents = 0
    t0_height25_children = 0

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
        t0_height23_inputs += int(np.sum(weights[live]))
        if not bool(np.any(live)):
            continue
        live_weights = weights[live]
        p10626_live = p10626[live]
        for lift24 in range(24):
            t0_height24_parents += int(np.sum(live_weights))
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
                t0_height25_children += int(np.sum(live_weights))
                total_through_25 = 462 * lift23 + 10_626 * lift24 + 255_024 * lift25
                coordinate25 = (
                    offset25[live] + slope25[live] * total_through_25
                ) % 25
                p25 = p25_table[t_base[live], coordinate25]
                p6375600 = p255024 + 255_024 * (
                    ((p25 - p255024) * inverse_255024_mod_25) % 25
                )
                lifts26 = np.arange(26, dtype=np.int64)[None, :]
                total_lifts = total_through_25 + CURRENT_SOURCE_MODULUS * lifts26
                source_digits = t_base[live, None]
                p32 = p32_table[
                    source_digits,
                    (offset32[live, None] + slope32[live, None] * total_lifts) % 32,
                ]
                p13 = p13_table[
                    source_digits,
                    (offset13[live, None] + slope13[live, None] * total_lifts) % 13,
                ]
                p_current = p6375600[:, None]
                assert bool(np.all((p32 - p_current) % 16 == 0))
                step32 = ((p32 - p_current) // 16) % 2
                p12751200 = p_current + CURRENT_SOURCE_MODULUS * step32
                step13 = (
                    (p13 - p12751200) * inverse_12751200_mod_13
                ) % 13
                p_target = p12751200 + 12_751_200 * step13
                assert bool(np.all(p_target % CURRENT_SOURCE_MODULUS == p_current))
                assert bool(np.all(p_target % 32 == p32))
                assert bool(np.all(p_target % 13 == p13))
                assert bool(np.all((0 <= p_target) & (p_target < TARGET_SOURCE_MODULUS)))
                p_u = p_target.astype(np.uint64)
                multiplier20_full = (
                    (np.uint64(380) * p_u * p_u)
                    + np.uint64(18) * p_u
                    + np.uint64(1)
                ) % np.uint64(TARGET_SOURCE_MODULUS)
                multiplier20_full = multiplier20_full.astype(np.int64)
                assert bool(np.all((multiplier20_full - 1) % 21 == 0))
                r7893600 = ((multiplier20_full - 1) // 21) % 7_893_600
                multiplier21 = (
                    420 * r7893600 * r7893600 + 19 * r7893600 + 1
                ) % 7_893_600
                assert bool(np.all((multiplier21 - 1) % 22 == 0))
                q358800 = ((multiplier21 - 1) // 22) % 358_800
                multiplier22 = (
                    462 * q358800 * q358800 + 20 * q358800 + 1
                ) % 358_800
                assert bool(np.all((multiplier22 - 1) % 23 == 0))
                z15600 = ((multiplier22 - 1) // 23) % 15_600
                multiplier23 = (
                    506 * z15600 * z15600 + 21 * z15600 + 1
                ) % 15_600
                assert bool(np.all((multiplier23 - 1) % 24 == 0))
                c650 = ((multiplier23 - 1) // 24) % 650
                multiplier24 = (552 * c650 * c650 + 22 * c650 + 1) % 650
                assert bool(np.all(multiplier24 * multiplier24 % 25 == 1))
                numerator = 24 * multiplier24 * multiplier24 - 25 * multiplier24 + 26
                assert bool(np.all(numerator % 25 == 0))
                multiplier25 = (numerator // 25) % 26
                cofinal_masks = np.zeros(multiplier25.shape, dtype=bool)
                positive_masks = np.zeros(multiplier25.shape, dtype=bool)
                negative_masks = np.zeros(multiplier25.shape, dtype=bool)
                for residue in np.unique(multiplier25):
                    signature = centered_successor_signature(25, -1, int(residue))
                    mask = multiplier25 == residue
                    weighted = int(np.sum(mask * live_weights[:, None]))
                    multiplier25_counts[int(residue)] += weighted
                    mode_counts[signature] += weighted
                    if signature[1] == 1:
                        cofinal_masks |= mask
                    elif signature[2] > 0:
                        positive_masks |= mask
                    elif signature[2] < 0:
                        negative_masks |= mask
                    else:
                        raise AssertionError(f"unexpected zero-error mode {signature}")
                cofinal = np.sum(cofinal_masks, axis=1)
                positive = np.sum(positive_masks, axis=1)
                negative = np.sum(negative_masks, axis=1)
                assert bool(np.all(cofinal + positive + negative == 26))
                _merge_profiles(profiles, cofinal, positive, negative, live_weights)
        _progress("factor26_lift23_complete", lift23=lift23)

    assert t0_height23_inputs == EXPECTED_T0_HEIGHT_TWENTY_THREE_INPUTS
    assert t0_height24_parents == EXPECTED_T0_HEIGHT_TWENTY_FOUR_PARENTS
    assert t0_height25_children == EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN
    assert sum(profiles.values()) == EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN
    assert sum(mode_counts.values()) == EXPECTED_FACTOR26_REFINEMENTS
    return {
        "extended_affine_cache_action": cache_action,
        "source_key_count": source_key_count,
        "height_twenty_two_extended_weighted_key_count": extended_weighted_key_count,
        "t0_height_twenty_two_extended_key_count": int(weights.size),
        "t0_height_twenty_three_input_count": t0_height23_inputs,
        "t0_height_twenty_four_parent_count": t0_height24_parents,
        "t0_height_twenty_five_child_count": t0_height25_children,
        "factor26_logical_refinement_count": EXPECTED_FACTOR26_REFINEMENTS,
        "factor26_parent_profile_counts": {
            f"cofinal={key[0]},positive={key[1]},negative={key[2]}": value
            for key, value in sorted(profiles.items())
        },
        "factor26_multiplier_residue_counts": {
            str(key): value for key, value in sorted(multiplier25_counts.items())
        },
        "factor26_successor_mode_counts": {
            f"payment={key[0]},height={key[1]},error={key[2]}": value
            for key, value in sorted(mode_counts.items())
        },
        "all_negative_parent_count": sum(
            value for key, value in profiles.items() if key[2] == 26
        ),
        "minimum_negative_children_per_parent": min(key[2] for key in profiles),
        "maximum_negative_children_per_parent": max(key[2] for key in profiles),
    }


def _factor26_multiplier_residues(
    p_current: np.ndarray[Any, Any], quotient_parity: int
) -> np.ndarray[Any, Any]:
    quotient_half = np.arange(13, dtype=np.int64)[None, :]
    p_current_column = p_current[:, None]
    p_target = p_current_column + CURRENT_SOURCE_MODULUS * (
        quotient_parity + 2 * quotient_half
    )
    assert bool(np.all(p_target % CURRENT_SOURCE_MODULUS == p_current_column))
    assert bool(np.all((0 <= p_target) & (p_target < TARGET_SOURCE_MODULUS)))
    p_u = p_target.astype(np.uint64)
    multiplier20 = (
        np.uint64(380) * p_u * p_u + np.uint64(18) * p_u + np.uint64(1)
    ) % np.uint64(TARGET_SOURCE_MODULUS)
    multiplier20 = multiplier20.astype(np.int64)
    assert bool(np.all((multiplier20 - 1) % 21 == 0))
    r7893600 = ((multiplier20 - 1) // 21) % 7_893_600
    multiplier21 = (
        420 * r7893600 * r7893600 + 19 * r7893600 + 1
    ) % 7_893_600
    assert bool(np.all((multiplier21 - 1) % 22 == 0))
    q358800 = ((multiplier21 - 1) // 22) % 358_800
    multiplier22 = (
        462 * q358800 * q358800 + 20 * q358800 + 1
    ) % 358_800
    assert bool(np.all((multiplier22 - 1) % 23 == 0))
    z15600 = ((multiplier22 - 1) // 23) % 15_600
    multiplier23 = (506 * z15600 * z15600 + 21 * z15600 + 1) % 15_600
    assert bool(np.all((multiplier23 - 1) % 24 == 0))
    c650 = ((multiplier23 - 1) // 24) % 650
    multiplier24 = (552 * c650 * c650 + 22 * c650 + 1) % 650
    assert bool(np.all(multiplier24 * multiplier24 % 25 == 1))
    numerator = 24 * multiplier24 * multiplier24 - 25 * multiplier24 + 26
    assert bool(np.all(numerator % 25 == 0))
    multiplier25 = (numerator // 25) % 26
    assert bool(np.all(multiplier25 % 2 == 1))
    return multiplier25


def payment_thirteen_forced_height_two_return() -> dict[str, int | str]:
    reduced_multiplier = 13 // 13
    height_two_multiplier = (
        reduced_multiplier * (25 * 13 * reduced_multiplier - 26) + 1
    ) // 2
    payment = math.gcd(3, height_two_multiplier * height_two_multiplier)
    assert reduced_multiplier == 1
    assert height_two_multiplier == 150
    assert payment == 3
    return {
        "input_mode": "payment=13,height=2,error=-1",
        "reduced_multiplier": reduced_multiplier,
        "height_two_multiplier": height_two_multiplier,
        "height_two_payment": payment,
        "final_height": 3 // payment,
    }


def complete_t0_factor26_activation() -> dict[str, Any]:
    source_lift_certificate = _factor26_source_lift_certificate()
    parent_codes, parent_weights, cache_metadata = _build_t0_factor26_parent_keys()
    profiles: Counter[tuple[int, int, int]] = Counter()
    mode_counts: Counter[tuple[int, int, int]] = Counter()
    multiplier25_counts: Counter[int] = Counter()
    chunk_size = 20_000

    for start in range(0, parent_codes.size, chunk_size):
        stop = min(start + chunk_size, parent_codes.size)
        codes = parent_codes[start:stop]
        weights = parent_weights[start:stop]
        p_current = _decode_factor26_parent(codes)
        even_residues = _factor26_multiplier_residues(p_current, 0)
        odd_residues = _factor26_multiplier_residues(p_current, 1)
        assert bool(
            np.all(
                np.sort(even_residues, axis=1)
                == np.sort(odd_residues, axis=1)
            )
        )
        multiplier25 = np.concatenate([even_residues, even_residues], axis=1)

        cofinal_masks = np.zeros(multiplier25.shape, dtype=bool)
        positive_masks = np.zeros(multiplier25.shape, dtype=bool)
        negative_masks = np.zeros(multiplier25.shape, dtype=bool)
        for residue in np.unique(multiplier25):
            signature = centered_successor_signature(25, -1, int(residue))
            mask = multiplier25 == residue
            weighted = int(np.sum(mask * weights[:, None]))
            multiplier25_counts[int(residue)] += weighted
            mode_counts[signature] += weighted
            if signature[1] == 1:
                cofinal_masks |= mask
            elif signature[2] > 0:
                positive_masks |= mask
            elif signature[2] < 0:
                negative_masks |= mask
            else:
                raise AssertionError(f"unexpected zero-error mode {signature}")
        cofinal = np.sum(cofinal_masks, axis=1)
        positive = np.sum(positive_masks, axis=1)
        negative = np.sum(negative_masks, axis=1)
        assert bool(np.all(cofinal + positive + negative == 26))
        _merge_profiles(profiles, cofinal, positive, negative, weights)
        _progress(
            "factor26_classification_chunk_complete",
            parent_key_stop=stop,
            parent_key_count=int(parent_codes.size),
        )

    assert sum(profiles.values()) == EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN
    assert sum(mode_counts.values()) == EXPECTED_FACTOR26_REFINEMENTS
    forced_return = payment_thirteen_forced_height_two_return()
    effective_profiles = {
        "cofinal=14,positive=4,negative=8": EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN
    }
    result: dict[str, Any] = {
        **cache_metadata,
        "factor26_source_lift_certificate": source_lift_certificate,
        "t0_height_twenty_three_input_count": EXPECTED_T0_HEIGHT_TWENTY_THREE_INPUTS,
        "t0_height_twenty_four_parent_count": EXPECTED_T0_HEIGHT_TWENTY_FOUR_PARENTS,
        "t0_height_twenty_five_child_count": EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN,
        "factor26_logical_refinement_count": EXPECTED_FACTOR26_REFINEMENTS,
        "factor26_source_lift_mechanism": {
            "quotient_parity_profile_dependence": "none_on_actual_parent_support",
            "parity_comparison": "exact_sorted_multiplier_residue_multiset_equality",
            "distinct_target_residues_per_parent": 13,
            "multiplicity_per_target_residue": 2,
        },
        "factor26_parent_profile_counts": {
            f"cofinal={key[0]},positive={key[1]},negative={key[2]}": value
            for key, value in sorted(profiles.items())
        },
        "factor26_multiplier_residue_counts": {
            str(key): value for key, value in sorted(multiplier25_counts.items())
        },
        "factor26_successor_mode_counts": {
            f"payment={key[0]},height={key[1]},error={key[2]}": value
            for key, value in sorted(mode_counts.items())
        },
        "payment_thirteen_forced_return": forced_return,
        "effective_parent_profile_counts_after_forced_height_two_step": (
            effective_profiles
        ),
        "effective_outcome_totals_after_forced_height_two_step": {
            "cofinal_return": EXPECTED_FACTOR26_MULTIPLIER_COUNTS["13"],
            "positive_switch": EXPECTED_FACTOR26_MULTIPLIER_COUNTS["15"],
            "continuing_negative": EXPECTED_FACTOR26_MULTIPLIER_COUNTS["1"],
        },
        "all_negative_parent_count": sum(
            value for key, value in profiles.items() if key[2] == 26
        ),
        "minimum_negative_children_per_parent": min(key[2] for key in profiles),
        "maximum_negative_children_per_parent": max(key[2] for key in profiles),
    }
    assert result["factor26_parent_key_count"] == 18
    assert result["factor26_parent_profile_counts"] == EXPECTED_FACTOR26_PARENT_PROFILES
    assert result["factor26_multiplier_residue_counts"] == EXPECTED_FACTOR26_MULTIPLIER_COUNTS
    assert result["factor26_successor_mode_counts"] == EXPECTED_FACTOR26_MODE_COUNTS
    assert (
        result["effective_parent_profile_counts_after_forced_height_two_step"]
        == EXPECTED_EFFECTIVE_PARENT_PROFILES
    )
    assert result["all_negative_parent_count"] == 0
    assert result["minimum_negative_children_per_parent"] == 22
    assert result["maximum_negative_children_per_parent"] == 22
    return result


def build_receipt() -> dict[str, Any]:
    previous = json.loads(
        (REPO_ROOT / HEIGHT_TWENTY_FOUR_RECEIPT_REF).read_text(encoding="utf-8")
    )
    assert previous["status"] == "verified_exact_binary_parent_fiber_split"
    census = complete_t0_factor26_activation()
    contract = build_experiment_contract(
        problem_id="erdos_243",
        target_statement=(
            "Under a_(n+1)/a_n^2 -> 1 and rational reciprocal sum, force "
            "eventual Sylvester recurrence."
        ),
        claim_ceiling=(
            "Exact factor-26 classification of the complete t=0, error=-1 inert "
            "subfamily: every actual parent has 4 positive and 22 continuing-"
            "negative immediate refinements, with no immediate cofinal refinement. "
            "The 14 height-two children then force full payment three and cofinal "
            "return, leaving the effective profile 14 cofinal, 4 positive, 8 "
            "negative and a uniform 4/13 continuation bound; unrestricted Erdos "
            "#243 remains open."
        ),
        hypothesis_id="factor26_activates_every_factor25_inert_fiber",
        hypothesis_statement=(
            "Every factor-25 inert child loses at least one factor-26 refinement "
            "from negative support, eliminating the expanding all-negative mode."
        ),
        probe_id="exact_factor26_parent_profile_and_parity_invariance_census",
        probe_question=(
            "Does the complete factor-26 lift activate every actual t=0 inert "
            "fiber, and does the new 2-adic quotient parity affect its profile?"
        ),
        computation=(
            "Reuse the 32490-key factor-25 cache, aggregate the exact t=0 child "
            "support to 18 current-modulus residues, compare both quotient-parity "
            "multiplier multisets exactly, and classify all 6683872197600 logical "
            "refinements by centered successor signature."
        ),
        falsifier=(
            "Any actual parent with 26 continuing-negative refinements, or any "
            "actual parent whose two quotient-parity residue multisets differ."
        ),
        stop_condition=(
            "Stop after the complete weighted factor-26 parent histogram and "
            "parity comparison are exact; do not extend individual orbits."
        ),
        survival_consequence=(
            "A common profile followed through any forced bounded cascade supplies "
            "a uniform block contraction on the formerly inert boundary."
        ),
        falsification_consequence=(
            "An all-negative fiber would force another activation search at a "
            "later raw factor and refute two-step uniform contraction."
        ),
        consumer_ref=LEAN_REF,
        consumer_declarations=[
            "ErdosProblems.Erdos243.heightTwentyFive_multiplierOdd",
            "ErdosProblems.Erdos243.heightTwentyFive_noFullPaymentDivisibility",
            "ErdosProblems.Erdos243.heightTwentyFivePaymentThirteen_heightTwoMultiplier",
            "ErdosProblems.Erdos243.heightTwentyFivePaymentThirteen_fullPaymentThree",
            "ErdosProblems.Erdos243.heightTwentyFivePaymentThirteen_finalCollapse",
        ],
        analysis_refs=[NOTE_REF, PACKET_REF, HEIGHT_TWENTY_FOUR_RECEIPT_REF],
        source_refs=[SCRIPT_REF, HEIGHT_TWENTY_FOUR_REF, HEIGHT_TWENTY_FOUR_RECEIPT_REF],
        result_status="exact_one_way_result",
        result_summary=(
            "All 257072007600 actual parents share profile (0,4,22). Their "
            "26-lift multiplier multiset is 1^8,13^14,15^4; quotient parity is "
            "profile-invariant. The 14 multiplier-thirteen children force the "
            "height-two multiplier 150, full payment three, and cofinal return, "
            "so the effective profile is (14,4,8) and negative continuation "
            "contracts uniformly by 4/13."
        ),
        progress_class="mechanism_eliminated",
        decision_basis=(
            "The complete exact parent-local histogram has a single activating "
            "profile and zero all-negative fibers."
        ),
        next_analytic_target=(
            "Exploit the uniform 4/13 block continuation in an amortized negative-"
            "mass argument and classify only the surviving (height 26,error -1) "
            "multiplier-one state at factor 27; the height-two state is closed."
        ),
        resource_bounds={
            "factor25_weighted_key_count": 32_490,
            "factor26_parent_key_count": 18,
            "logical_parent_count": EXPECTED_T0_HEIGHT_TWENTY_FIVE_CHILDREN,
            "children_per_parent": 26,
            "logical_refinement_count": EXPECTED_FACTOR26_REFINEMENTS,
        },
    )
    validate_experiment_contract(contract, repo_root=REPO_ROOT)
    return {
        "schema": "erdos243-t0-factor26-activation-receipt/1",
        "status": "verified_uniform_factor26_activation_and_forced_cofinal_cascade",
        "complete_factor26_census": census,
        "mechanism_decision": {
            "factor26_cofinal_return": "eliminated_by_odd_multiplier",
            "payment_thirteen_next_step_cofinal_return": "forced",
            "all_negative_boundary_mode": "eliminated",
            "uniform_negative_continuation_ratio_after_forced_step": "4/13",
            "cofinal_children_per_parent_after_forced_step": 14,
            "positive_children_per_parent": 4,
            "continuing_negative_children_per_parent_after_forced_step": 8,
            "surviving_negative_states": [
                {"height": 26, "error": -1, "children_per_parent": 8},
            ],
        },
        "experiment_contract": contract,
        "source_records": [
            source_record(REPO_ROOT, ref)
            for ref in [
                SCRIPT_REF,
                HEIGHT_TWENTY_FOUR_REF,
                HEIGHT_TWENTY_FOUR_RECEIPT_REF,
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
        print(json.dumps(complete_t0_factor26_activation(), indent=2, sort_keys=True))
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
