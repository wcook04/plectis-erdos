#!/usr/bin/env python3
"""Repetition (stammering) exponent of the Erdos #269 radix word.

Why this is the deciding measurement
------------------------------------
The radix word was shown to be the product of two Sturmian words with slopes
alpha_3 = 1/log_2 3 and alpha_5 = 1/log_2 5, with factor complexity exactly
(n+1)^2.  The transcendence machinery of Adamczewski-Bugeaud (Schmidt Subspace
Theorem applied to stammering expansions) needs one input and one only: does
the word begin in arbitrarily high powers?

For a single Sturmian word with slope alpha the answer is yes, with period
equal to a continued-fraction denominator q of alpha and repetition length
about 1/||q alpha||.  For a *product* of two Sturmian words the period must
work for both slopes at once, so the relevant quantity is simultaneous
Diophantine approximation of (alpha_3, alpha_5):

    repetition of period q persists for about  min(1/||q a_3||, 1/||q a_5||)
    letters, i.e. an exponent of about q * min(...)^-1 / q periods.

Dirichlet in dimension two gives infinitely many q with both ||q a_i|| <=
q^(-1/2), which would make the exponent grow like q^(1/2) -> infinity.

Probe
-----
Search simultaneous approximation denominators directly, then MEASURE the
actual repetition in the literal word rather than trusting the estimate.

Falsifier
---------
A repetition exponent that stays bounded as q grows.  That would mean the
product word is not stammering, and the Subspace-Theorem lane is closed for
this problem rather than opened.
"""

from __future__ import annotations

import argparse
import json
import sys
from math import log2
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal_math.probes.erdos269_torus_coding import beatty_indicator  # noqa: E402


def radix_word(max_a: int) -> str:
    three = beatty_indicator(3, max_a + 2)
    five = beatty_indicator(5, max_a + 2)
    out = []
    for a in range(1, max_a + 1):
        out.append({2: "a", 6: "b", 10: "c", 30: "d"}[
            2 * (3 if a in three else 1) * (5 if a in five else 1)])
    return "".join(out)


def frac_dist(x: float) -> float:
    y = x - int(x)
    if y < 0:
        y += 1.0
    return min(y, 1.0 - y)


def simultaneous_denominators(max_q: int, count: int) -> list[dict]:
    """Record-setting q for max(||q*a3||, ||q*a5||)."""
    a3, a5 = 1.0 / log2(3), 1.0 / log2(5)
    best = 1e9
    rows = []
    for q in range(1, max_q + 1):
        m = max(frac_dist(q * a3), frac_dist(q * a5))
        if m < best:
            best = m
            rows.append({"q": q, "max_defect": m,
                         "dirichlet_exponent": round(-1 * (m and __import__("math").log(m) / __import__("math").log(q)), 4) if q > 1 else None})
    return rows[-count:]


def measured_repetition(word: str, period: int) -> int:
    """Longest L with word[i] == word[i+period] for all i < L (prefix match)."""
    n = len(word)
    limit = n - period
    i = 0
    while i < limit and word[i] == word[i + period]:
        i += 1
    return i


def run(max_a: int, max_q: int) -> dict:
    word = radix_word(max_a)
    records = simultaneous_denominators(max_q, 18)
    rows = []
    for rec in records:
        q = rec["q"]
        if q >= max_a // 2:
            continue
        match_len = measured_repetition(word, q)
        rows.append({
            "period_q": q,
            "max_simultaneous_defect": round(rec["max_defect"], 8),
            "prefix_period_match_length": match_len,
            "repetition_exponent": round(1 + match_len / q, 4),
        })
    exps = [r["repetition_exponent"] for r in rows]
    growing = len(exps) > 3 and max(exps[-4:]) > max(exps[:4])
    return {
        "probe_id": "erdos269_stammering",
        "word_length": len(word),
        "simultaneous_approximation_records": rows,
        "max_repetition_exponent": max(exps) if exps else None,
        "exponent_is_growing": growing,
        "reading": (
            "word begins in arbitrarily high powers => stammering; the "
            "Adamczewski-Bugeaud / Subspace-Theorem lane is open"
            if growing else
            "repetition exponent bounded => stammering lane closed"
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-a", type=int, default=400000)
    ap.add_argument("--max-q", type=int, default=200000)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.max_a, args.max_q)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps(payload, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
