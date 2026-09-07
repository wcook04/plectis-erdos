#!/usr/bin/env python3
"""Exact finite checks for coordinate-fibre decoding and the false finite rank claim.

Decisions are integer / Fraction comparisons. Not an irrationality proof.
Quick mode is the default regression; --full extends fibre radix scans.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from itertools import product
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[5]
SCRIPTS = (
    REPO_ROOT
    / "formal_math"
    / "erdos257_period_noncollapse"
    / "scripts"
)
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from check_erdos269_block_mass_identity import height235  # noqa: E402

problem_id = "erdos_269"

ALPHABETS = {
    2: (2, 6, 10, 30),
    3: (6, 12, 30, 60),
    5: (60, 120, 180, 360),
}
CAPS = {2: Fraction(7, 11), 3: Fraction(1, 5), 5: Fraction(1, 59)}


def alphabet_and_separation() -> dict:
    failures = []
    for p, alphabet in ALPHABETS.items():
        for a, b in zip(alphabet, alphabet[1:]):
            if not (Fraction(b, a) > 1 + CAPS[p]):
                failures.append(("ratio", p, a, b))
    gap_610 = Fraction(1, 6) - Fraction(18, 110)
    if gap_610 != Fraction(1, 330):
        failures.append(("gap_6_10", str(gap_610)))
    return {
        "ok": not failures,
        "failures": failures,
        "gap_6_10": str(gap_610),
    }


def fibre_radix_scan(n_powers: int, x_values: tuple[int, ...]) -> dict:
    failures = []
    pair_ok = True
    for p, alphabet in ALPHABETS.items():
        allowed = set(alphabet)
        for x in x_values:
            heights = [height235(x * p**n) for n in range(n_powers)]
            radices = [v // u for u, v in zip(heights, heights[1:])]
            extra = set(radices) - allowed
            if extra:
                failures.append(("alphabet", p, x, sorted(extra)))
            if p == 2:
                if not all(a * b >= 12 for a, b in zip(radices, radices[1:])):
                    pair_ok = False
                    failures.append(("pair12", x))
            cap = CAPS[p]
            for n in range(min(100, len(heights) - 1)):
                finite_tail = sum(
                    (Fraction(heights[n], h) for h in heights[n + 1 :]),
                    Fraction(0),
                )
                if finite_tail > cap:
                    failures.append(("tail", p, x, n, str(finite_tail)))
                    break
    return {
        "ok": not failures,
        "pair12_ok": pair_ok,
        "n_powers": n_powers,
        "x_values": list(x_values),
        "failures": failures,
    }


def rank_one_counterexample() -> dict:
    t11 = Fraction(1, 5)
    a11, a12, a21, a22 = (
        Fraction(3, 10),
        Fraction(9, 10),
        Fraction(1, 10),
        Fraction(3, 10),
    )
    det_a = a11 * a22 - a12 * a21
    err = max(
        abs(t11 - a11),
        abs(Fraction(1) - a12),
        abs(t11 - a21),
        abs(t11 - a22),
    )
    half_gap = Fraction(2, 5)
    return {
        "ok": det_a == 0 and err == Fraction(1, 10) and err < half_gap,
        "det_A": str(det_a),
        "max_err": str(err),
        "half_gap": str(half_gap),
    }


def staircase_inverse_norm(max_n: int) -> dict:
    c = Fraction(1, 5)
    rows = []
    for n in range(1, max_n + 1):
        observed = max(
            (
                (
                    abs(-y[0] + y[-1] / c)
                    + sum(abs(y[i - 1] - y[i]) for i in range(1, n))
                )
                / (1 - c)
            )
            for y in product((-1, 1), repeat=n)
        )
        denominator = 2 * n - (1 if n % 2 == 0 else 3) + 1 / c
        expected = denominator / (1 - c)
        rows.append(
            {
                "n": n,
                "observed": str(observed),
                "expected": str(expected),
                "ok": observed == expected,
            }
        )
    return {"ok": all(r["ok"] for r in rows), "rows": rows}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--quick",
        action="store_true",
        help="alphabets, n=2 counterexample, inverse-norm n<=10, fibres n<=40",
    )
    parser.add_argument(
        "--full",
        action="store_true",
        help="extend fibre radix scans to 130 powers",
    )
    parser.add_argument("--json-out", type=Path, default=None)
    args = parser.parse_args()
    n_powers = 130 if args.full else 40
    x_values = (1, 7, 15, 77, 243, 625)
    payload = {
        "problem_id": problem_id,
        "claim": "coordinate_fibre_decoding_and_finite_rank_distance",
        "alphabet_separation": alphabet_and_separation(),
        "fibre_scan": fibre_radix_scan(n_powers, x_values),
        "rank_one_counterexample": rank_one_counterexample(),
        "staircase_inverse_norm": staircase_inverse_norm(10),
        "claim_boundary": (
            "Exact finite alphabet, confinement, rank-one counterexample, "
            "and staircase inverse-norm identities. Not an irrationality "
            "theorem for the repeated three-prime series."
        ),
    }
    payload["ok"] = (
        payload["alphabet_separation"]["ok"]
        and payload["fibre_scan"]["ok"]
        and payload["rank_one_counterexample"]["ok"]
        and payload["staircase_inverse_norm"]["ok"]
    )
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.json_out is not None:
        args.json_out.write_text(text + "\n")
    print(text)
    if not payload["ok"]:
        print("FAIL", file=sys.stderr)
        return 1
    print("All exact finite regression checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
