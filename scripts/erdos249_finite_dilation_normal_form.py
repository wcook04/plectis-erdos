#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite normal form for joint dyadic totient-observable values.

Run, for example::

    python3 scripts/erdos249_finite_dilation_normal_form.py --input expr.json
    python3 scripts/erdos249_finite_dilation_normal_form.py --self-test

Input is a JSON object with one common integer ``base``, a rational
``constant``, and ``terms``. Each term has positive integers ``d`` and ``k``,
a rational ``coefficient`` (default 1), and a complete rational table of
length 2**k; it denotes sum_{n>=1} table[phi(n) mod 2**k] / base**(d*n).
An optional ``rhs`` contains another constant and term list; then the normal
form is computed for left minus right.

The arithmetic here is finite and exact. The irrationality and equality
verdicts apply the Lean theorem
ErdosProblems.Erdos249.FiniteDilationMixedModuli.rational_mixed_moduli_with_constant_iff,
and the rational value applies mixed_value_eq_of_even_constant from the same
module. This script is not an independent proof of those infinite-series
theorems, and it says nothing about the unreduced series sum phi(n)/2**n of
Erdos problem 249.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from fractions import Fraction
from math import gcd
from pathlib import Path
from typing import Any

THEOREM = (
    "ErdosProblems.Erdos249.FiniteDilationMixedModuli."
    "rational_mixed_moduli_with_constant_iff"
)
VALUE_THEOREM = (
    "ErdosProblems.Erdos249.FiniteDilationMixedModuli."
    "mixed_value_eq_of_even_constant"
)
MAX_TABLE_SIZE = 1 << 16


def rational(value: Any) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (str, int)):
        raise ValueError("rational values must be integers or exact strings")
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError(f"invalid rational value: {value!r}") from exc


def object_keys(value: Any, allowed: set[str], required: set[str], label: str) -> dict:
    if not isinstance(value, dict):
        raise ValueError(f"{label} must be an object")
    extra = set(value) - allowed
    missing = required - set(value)
    if extra or missing:
        raise ValueError(f"{label}: unsupported keys {sorted(extra)}; missing {sorted(missing)}")
    return value


def positive_int(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ValueError(f"{label} must be a positive integer")
    return value


def parse_terms(value: Any, sign: int) -> list[tuple[int, int, Fraction, list[Fraction]]]:
    if not isinstance(value, list):
        raise ValueError("terms must be a list")
    result = []
    for index, raw in enumerate(value):
        term = object_keys(raw, {"d", "k", "coefficient", "table"},
                           {"d", "k", "table"}, f"term {index}")
        d = positive_int(term["d"], f"term {index} d")
        k = positive_int(term["k"], f"term {index} k")
        if k > 16:
            raise ValueError(f"term {index}: table exceeds the {MAX_TABLE_SIZE}-entry evaluator limit")
        table = term["table"]
        if not isinstance(table, list) or len(table) != 1 << k:
            raise ValueError(f"term {index}: table must have exactly 2**k entries")
        result.append((d, k, sign * rational(term.get("coefficient", 1)),
                       [rational(entry) for entry in table]))
    return result


def normalise(payload: Any) -> dict:
    data = object_keys(payload, {"base", "constant", "terms", "rhs"},
                       {"base", "terms"}, "input")
    base = positive_int(data["base"], "base")
    if base < 2:
        raise ValueError("base must be at least 2")
    constant = rational(data.get("constant", 0))
    terms = parse_terms(data["terms"], 1)
    comparison = "rhs" in data
    if comparison:
        rhs = object_keys(data["rhs"], {"constant", "terms"}, {"terms"}, "rhs")
        constant -= rational(rhs.get("constant", 0))
        terms.extend(parse_terms(rhs["terms"], -1))

    by_d: dict[int, list[tuple[int, Fraction, list[Fraction]]]] = defaultdict(list)
    for d, k, coefficient, table in terms:
        by_d[d].append((k, coefficient, table))

    gamma = constant
    coordinates = []
    rows = []
    basis = [{"kind": "rational_unit"}]
    for d in sorted(by_d):
        k = max(item[0] for item in by_d[d])
        table = [sum((coefficient * values[r % (1 << level)]
                      for level, coefficient, values in by_d[d]), Fraction(0))
                 for r in range(1 << k)]
        radix = base ** d
        rho = Fraction(1, radix * radix * (radix - 1))
        gamma += Fraction(radix + 1, radix * radix) * table[1] + rho * table[0]
        for r in range(2, 1 << k, 2):
            basis.append({"kind": "tail_residue", "d": d, "k": k,
                          "even_residue": r})
            beta = table[r] - table[0]
            if beta:
                coordinates.append({"d": d, "k": k, "even_residue": r,
                                    "coefficient": str(beta)})
        rows.append({"d": d, "k": k, "even_zero_value": str(table[0]),
                     "prefix_one_value": str(table[1]), "tail_mass": str(rho)})

    result = {
        "schema": "erdos249_finite_dilation_normal_form_v1",
        "base": base,
        "comparison": comparison,
        "rational_part": str(gamma),
        "coordinates": coordinates,
        "ambient_basis": basis,
        "ambient_span_dimension": len(basis),
        "rows": rows,
        "classification": "irrational" if coordinates else "rational",
        "rational_value": str(gamma) if not coordinates else None,
        "theorem_dependency": THEOREM,
        "rational_value_theorem_dependency": VALUE_THEOREM,
        "evidence_boundary": "finite exact arithmetic applying the named Lean theorems",
    }
    if coordinates:
        result["nonzero_witness"] = coordinates[0]
    if comparison:
        result["equal"] = not coordinates and gamma == 0
    return result


def self_test() -> dict:
    cases = [
        ("same_dilation_cancellation", {"base": 2, "terms": [
            {"d": 1, "k": 2, "table": [0, 0, 1, 0]},
            {"d": 1, "k": 2, "table": [1, 0, 0, 0]}]}, "rational", "1/4"),
        ("cross_dilation_non_cancellation", {"base": 2, "terms": [
            {"d": 1, "k": 2, "table": [0, 0, 1, 0]},
            {"d": 2, "k": 2, "coefficient": -1, "table": [0, 0, 1, 0]}]},
         "irrational", None),
        ("rational_shift_does_not_cancel", {"base": 2, "constant": "7/5", "terms": [
            {"d": 1, "k": 2, "table": [0, 0, 1, 0]}]}, "irrational", None),
        ("unused_odd_residue", {"base": 3, "terms": [
            {"d": 1, "k": 2, "table": [5, 7, 5, 9999]}]}, "rational", "61/18"),
        ("dyadic_refinement", {"base": 2, "terms": [
            {"d": 1, "k": 2, "table": [0, 0, 1, 0]},
            {"d": 1, "k": 3, "coefficient": -1,
             "table": [0, 0, 1, 0, 0, 0, 1, 0]}]}, "rational", "0"),
        ("partition_relation", {"base": 2, "terms": [
            {"d": 1, "k": 2, "table": [1, 0, 0, 0]},
            {"d": 1, "k": 2, "table": [0, 0, 1, 0]},
            {"d": 2, "k": 2, "coefficient": -12, "table": [1, 0, 0, 0]},
            {"d": 2, "k": 2, "coefficient": -12, "table": [0, 0, 1, 0]}]},
         "rational", "0"),
        ("k_one_boundary", {"base": 2, "terms": [
            {"d": 1, "k": 1, "table": [3, 7]}]}, "rational", "6"),
    ]
    checked = []
    for name, payload, classification, value in cases:
        result = normalise(payload)
        assert result["classification"] == classification, name
        assert result["rational_value"] == value, name
        for cutoff in (3, 5, 11):
            direct = rational(payload.get("constant", 0))
            for term in payload["terms"]:
                radix = payload["base"] ** term["d"]
                coefficient = rational(term.get("coefficient", 1))
                table = [rational(entry) for entry in term["table"]]
                for n in range(1, cutoff + 1):
                    phi = sum(gcd(a, n) == 1 for a in range(1, n + 1))
                    direct += coefficient * table[phi % (1 << term["k"])] / radix ** n
            projected = Fraction(result["rational_part"])
            for row in result["rows"]:
                radix = payload["base"] ** row["d"]
                projected -= Fraction(row["even_zero_value"]) / (radix ** cutoff * (radix - 1))
            for coordinate in result["coordinates"]:
                radix = payload["base"] ** coordinate["d"]
                for n in range(3, cutoff + 1):
                    phi = sum(gcd(a, n) == 1 for a in range(1, n + 1))
                    if phi % (1 << coordinate["k"]) == coordinate["even_residue"]:
                        projected += Fraction(coordinate["coefficient"]) / radix ** n
            assert direct == projected, (name, cutoff, direct, projected)
        checked.append(name)
    comparison = normalise({"base": 2, "terms": [
        {"d": 1, "k": 2, "table": [0, 0, 1, 0]}], "rhs": {"terms": [
        {"d": 1, "k": 3, "table": [0, 0, 1, 0, 0, 0, 1, 0]}]}})
    assert comparison["equal"]
    checked.append("cross_level_equality")
    unequal = normalise({"base": 2, "terms": [], "rhs": {
        "constant": "1/3", "terms": []}})
    assert not unequal["equal"] and unequal["rational_value"] == "-1/3"
    checked.append("rational_constant_comparison")
    partition = normalise(next(payload for name, payload, _, _ in cases
                               if name == "partition_relation"))
    assert partition["ambient_span_dimension"] == 3
    assert partition["ambient_basis"] == [
        {"kind": "rational_unit"},
        {"kind": "tail_residue", "d": 1, "k": 2, "even_residue": 2},
        {"kind": "tail_residue", "d": 2, "k": 2, "even_residue": 2},
    ]
    checked.append("raw_four_values_have_rank_three")
    try:
        normalise({"base": 2, "terms": [
            {"d": 1, "k": 2, "denominator_base": 3, "table": [0, 0, 1, 0]}]})
    except ValueError:
        checked.append("unrelated_base_rejected")
    else:
        raise AssertionError("unrelated base must be rejected")
    return {"status": "passed", "checked": checked}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="JSON expression file; stdin if omitted")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    try:
        if args.self_test:
            result = self_test()
        elif args.input:
            result = normalise(json.loads(args.input.read_text(encoding="utf-8")))
        else:
            result = normalise(json.load(sys.stdin))
    except (OSError, ValueError, AssertionError, json.JSONDecodeError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
