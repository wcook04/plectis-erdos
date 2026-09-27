#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact projection of a consumer's affine constraints, with replayable certificates.

When a proof uses a quantitative input only through a few linear inequalities
(a constant ``K`` with ``1 ≤ K`` and ``K · D < 1/100``, say), eliminating the
auxiliary variables gives the exact region of constants the consumer
tolerates: the search specification for a new supplier. Each input row means
``Σ aᵢ xᵢ ≤ b`` (``< b`` when ``strict``), with integer or rational-string
coefficients. Fourier-Motzkin elimination runs in exact ``Fraction``
arithmetic; every output row carries the nonnegative multipliers of the input
rows that produce it, strictness propagates only from a strict input with a
positive multiplier, and ``replay_certificate`` checks a row from its
multipliers alone, without the search. ``lean_projection_file`` writes each
row as a Lean lemma closed by ``linarith``: a candidate for a kernel probe,
never a compiled result.

What this does not do: it proves only rational linear combinations of the
given rows. Binding each row to the Lean hypothesis it stands for is the
caller's work, as is the transfer from the consumer's actual statement. The
budgets (elimination pairs, rows) are counts, so a result does not depend on
the machine; on an exhausted budget the rows of the last complete stage are
returned, valid but not the full projection (``unknown_budget``).
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
from typing import Any, Iterable


@dataclass
class Row:
    a: dict[str, Q]
    b: Q
    strict: bool
    weights: dict[int, Q]

    def payload(self) -> dict[str, Any]:
        return {"a": {k: str(v) for k, v in sorted(self.a.items()) if v}, "b": str(self.b), "strict": self.strict,
                "weights": {str(k): str(v) for k, v in sorted(self.weights.items()) if v}}


def rational(value: Any) -> Q:
    if isinstance(value, (float, bool)) or not isinstance(value, (int, str, Q)):
        raise ValueError("use exact integers or rational strings, not floats or booleans")
    return Q(value)


def parse_rows(items: Iterable[dict[str, Any]]) -> list[Row]:
    rows = []
    for i, item in enumerate(items):
        if not isinstance(item.get("strict", False), bool):
            raise ValueError("strict must be a boolean")
        if not isinstance(item.get("a"), dict):
            raise ValueError("a must be an object of variable -> coefficient")
        if any(not isinstance(k, str) or not k for k in item["a"]):
            raise ValueError("variables must have nonempty string names")
        coefficients = {k: rational(v) for k, v in item["a"].items()}
        rows.append(Row({k: v for k, v in coefficients.items() if v}, rational(item["b"]),
                        item.get("strict", False), {i: Q(1)}))
    return rows


def combine(p: Row, alpha: Q, n: Row, beta: Q) -> Row:
    if alpha < 0 or beta < 0:
        raise ValueError("multipliers must be nonnegative")
    a = {k: alpha * p.a.get(k, Q(0)) + beta * n.a.get(k, Q(0)) for k in p.a.keys() | n.a.keys()}
    w = {k: alpha * p.weights.get(k, Q(0)) + beta * n.weights.get(k, Q(0)) for k in p.weights.keys() | n.weights.keys()}
    return Row({k: v for k, v in a.items() if v}, alpha * p.b + beta * n.b,
               (p.strict and alpha > 0) or (n.strict and beta > 0), {k: v for k, v in w.items() if v})


def normalize(row: Row) -> Row:
    scale = abs(row.a[sorted(row.a)[0]]) if row.a else Q(1)
    return Row({k: v / scale for k, v in row.a.items()}, row.b / scale, row.strict,
               {k: v / scale for k, v in row.weights.items()})


def deduplicate(rows: list[Row]) -> list[Row]:
    """Keep, for each direction, the tightest row (it implies the others)."""
    best: dict[tuple, Row] = {}
    for raw in rows:
        row = normalize(raw)
        key = tuple(sorted(row.a.items()))
        prior = best.get(key)
        if prior is None or row.b < prior.b or (row.b == prior.b and row.strict and not prior.strict):
            best[key] = row
    return [best[key] for key in sorted(best)]


def infeasible(row: Row) -> bool:
    return not row.a and (row.b < 0 or (row.strict and row.b <= 0))


def replay_certificate(inputs: list[dict[str, Any]], output: dict[str, Any]) -> bool:
    """Whether ``output`` is exactly the combination of ``inputs`` its weights
    name, strictness included: the check needs no part of the search."""
    try:
        source = parse_rows(inputs)
        acc = Row({}, Q(0), False, {})
        for raw_index, raw_weight in output["weights"].items():
            index, weight = int(raw_index), rational(raw_weight)
            if index < 0 or index >= len(source) or weight < 0:
                return False
            acc = combine(acc, Q(1), source[index], weight)
        claimed = {k: rational(v) for k, v in output["a"].items()}
        return (acc.a == {k: v for k, v in claimed.items() if v} and acc.b == rational(output["b"])
                and acc.strict == output["strict"])
    except (KeyError, ValueError, TypeError, ZeroDivisionError):
        return False


def project(inputs: list[dict[str, Any]], eliminate: Iterable[str], *, max_pairs: int = 10_000,
            max_rows: int = 2_000) -> dict[str, Any]:
    """Eliminate the named variables. ``projected``: the rows describe exactly
    the region of the remaining variables for which the eliminated ones can be
    chosen; ``infeasible_relaxation``: a row reads ``0 ≤ b`` with ``b < 0``
    (or ``0 < b`` with ``b ≤ 0``), so no point satisfies the inputs;
    ``unknown_budget``: the rows of the last complete stage."""
    rows = deduplicate(parse_rows(inputs))
    pairs = 0
    done: list[str] = []
    complete = True
    for variable in eliminate:
        if any(infeasible(r) for r in rows):
            break
        positive = [r for r in rows if r.a.get(variable, Q(0)) > 0]
        negative = [r for r in rows if r.a.get(variable, Q(0)) < 0]
        zero = [r for r in rows if not r.a.get(variable, Q(0))]
        required = len(positive) * len(negative)
        if pairs + required > max_pairs or len(zero) + required > max_rows:
            complete = False
            break
        combined = list(zero)
        for p in positive:
            for n in negative:
                combined.append(combine(p, -n.a[variable], n, p.a[variable]))
                pairs += 1
        rows = deduplicate(combined)
        done.append(variable)
    certificates = [r.payload() for r in rows]
    if not all(replay_certificate(inputs, c) for c in certificates):
        raise RuntimeError("an emitted row does not replay from its multipliers")
    contradictions = [c for c, r in zip(certificates, rows) if infeasible(r)]
    return {"status": "infeasible_relaxation" if contradictions else "projected" if complete else "unknown_budget",
            "complete": complete, "eliminated": done, "pairs": pairs, "rows": certificates,
            "contradictions": contradictions, "evidence_class": "exact_rational_identity",
            "source_binding": "caller binds each input row to the Lean hypothesis it stands for"}


def interval(rows: list[dict[str, Any]], variable: str) -> dict[str, Any]:
    """The interval a univariate projection allows for ``variable``."""
    lower = upper = None
    impossible = False
    for row in rows:
        a = {k: rational(v) for k, v in row["a"].items() if rational(v)}
        b = rational(row["b"])
        if set(a) - {variable}:
            raise ValueError("interval needs a univariate projection")
        c = a.get(variable, Q(0))
        strict = row.get("strict", False)
        if not c:
            impossible |= b < 0 or (strict and b <= 0)
            continue
        endpoint = (b / c, strict)
        if c > 0:
            if upper is None or endpoint[0] < upper[0] or (endpoint[0] == upper[0] and strict):
                upper = endpoint
        elif lower is None or endpoint[0] > lower[0] or (endpoint[0] == lower[0] and strict):
            lower = endpoint
    if lower and upper:
        impossible |= lower[0] > upper[0] or (lower[0] == upper[0] and (lower[1] or upper[1]))
    return {"variable": variable,
            "lower": None if lower is None else {"value": str(lower[0]), "strict": lower[1]},
            "upper": None if upper is None else {"value": str(upper[0]), "strict": upper[1]},
            "empty": impossible}


def case249() -> dict[str, Any]:
    """The #249 excluded-cofactor budget at η = 1/1000.
    ``eventually_excluded_budget_of_upper_of_dyadic`` takes a dyadic prime
    count with constant ``K`` and asks ``hK : 1 ≤ K`` and ``hKD : K * D < 1/100``;
    at η = 1/1000 the upper density is ``D = 3/1000``. With ``q`` standing for
    ``K * D``: ``1 ≤ K``, ``(3/1000) K ≤ q``, ``q < 1/100``. Eliminating ``q``
    leaves ``1 ≤ K < 10/3``. Chebyshev's bound gives ``K = log 4``, and the
    Lean proof uses ``log 4 ≤ 3``, which is inside the interval with margin
    ``1/100 - 9/1000 = 1/1000``."""
    inputs = [{"a": {"K": -1}, "b": -1}, {"a": {"K": "3/1000", "q": -1}, "b": 0},
              {"a": {"q": 1}, "b": "1/100", "strict": True}]
    result = project(inputs, ["q"])
    result["admissible_K"] = interval(result["rows"], "K")
    result["supplier"] = {"K": "3", "bound_used": "log 4 ≤ 3",
                          "source": "excluded_budget_one_thousandth_of_chebyshev (Chebyshev's bound)"}
    result["margin"] = str(Q(1, 100) - Q(3) * Q(3, 1000))
    result["input_rows"] = inputs
    return result


def lean_certificate(inputs: list[dict[str, Any]], output: dict[str, Any], index: int = 0) -> str:
    """A closed Lean lemma for one replayed row: the inputs as hypotheses over
    real variables ``x0, x1, …`` (the JSON names never reach the source) and
    ``linarith`` over the rows the certificate uses."""
    if not replay_certificate(inputs, output):
        raise ValueError("refusing to emit a row that does not replay")
    source = parse_rows(inputs)
    variables = sorted({k for r in source for k in r.a} | set(output["a"]))
    names = {v: f"x{i}" for i, v in enumerate(variables)}

    def number(value: Any) -> str:
        value = rational(value)
        return f"(({value.numerator} : ℝ) / {value.denominator})"

    def inequality(row: dict[str, Any]) -> str:
        terms = [f"({number(v)} * {names[k]})" for k, v in sorted(row["a"].items()) if rational(v)]
        relation = " < " if row.get("strict", False) else " ≤ "
        return "(" + (" + ".join(terms) or "(0 : ℝ)") + relation + number(row["b"]) + ")"

    binders = (" (" + " ".join(names.values()) + " : ℝ)") if names else ""
    hypotheses = "".join(f" (h{i} : {inequality(r)})" for i, r in enumerate(inputs))
    used = sorted(int(i) for i, w in output["weights"].items() if rational(w))
    tactic = "linarith [" + ", ".join(f"h{i}" for i in used) + "]"
    return f"theorem affine_projection_{index}{binders}{hypotheses} : {inequality(output)} := by\n  {tactic}\n"


def lean_projection_file(result: dict[str, Any], inputs: list[dict[str, Any]]) -> str:
    title = ("Consequences of inconsistent affine inputs" if result.get("status") == "infeasible_relaxation"
             else "Affine consumer-interface consequences")
    header = (f"import Mathlib\n\n/- {title}. Generated by scripts/argument_graph_contracts.py: a candidate for a "
              "kernel probe, not a compiled result. -/\nnamespace ArgumentInterfaceCertificates\n\n")
    body = "\n".join(lean_certificate(inputs, row, i) for i, row in enumerate(result["rows"]))
    return header + body + "\nend ArgumentInterfaceCertificates\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--input", type=Path, help="JSON list of rows {a: {var: coeff}, b, strict}")
    parser.add_argument("--eliminate", nargs="*", default=[])
    parser.add_argument("--case249", action="store_true", help="the #249 budget at η = 1/1000")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--lean-out", type=Path, help="write the rows as Lean lemmas (a probe candidate)")
    args = parser.parse_args(argv)
    if args.case249:
        result = case249()
        inputs = result["input_rows"]
    elif args.input:
        inputs = json.loads(args.input.read_text(encoding="utf-8"))
        result = project(inputs, args.eliminate)
    else:
        parser.error("give --input or --case249")
    if args.lean_out:
        args.lean_out.write_text(lean_projection_file(result, inputs), encoding="utf-8")
    text = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
