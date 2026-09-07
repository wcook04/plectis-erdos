#!/usr/bin/env python3
"""Replay Type B r2 higher-degree forbidden-word certificates for Erdős #243.

Source of the certificate table: the Type B revision return
`state/formal_math/type_b_return_batches/erdos_revision_packets_r2_20260906/work/erdos_243/05_questions_for_type_a.md`
(the Python block titled "The modular-state verifier").  This script extracts
that block rather than retyping the 412 pairs, then independently enumerates
every multiplier residue.

What is checked
---------------
* Scale thresholds T_{d,±} of the real-root reduction (Corollary D).
* Coverage: one certificate per surviving scale 1..max_scale(d,c).
* Each (p, start) is a prime p > d, the word of length d+1 has an interior
  zero, and exhaustive (a,v)-enumeration leaves an empty terminal state set.

What is not claimed
-------------------
A successful replay is a finite exact certificate that a residue word is
impossible for a primitive uncancelled orbit.  Combined with the ordinary
density-zero → primitive-shape argument it supports positive lower density of
exceptions for each fixed rising-factorial profile of degrees 4–6.  It does
not by itself prove the unrestricted parent problem, Lean-check Chebotarev,
or supply a uniform density constant over all A, B.

Run:
    ./repo-python .../scripts/check_erdos243_higher_degree_certificates.py --quick
    ./repo-python .../scripts/check_erdos243_higher_degree_certificates.py
"""

from __future__ import annotations

import argparse
import ast
import json
import re
import sys
from fractions import Fraction
from math import factorial
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[5]
TYPE_B_05 = (
    REPO_ROOT
    / "state/formal_math/type_b_return_batches"
    / "erdos_revision_packets_r2_20260906/work/erdos_243"
    / "05_questions_for_type_a.md"
)


def is_prime(p: int) -> bool:
    return p >= 2 and all(p % k for k in range(2, int(p ** 0.5) + 1))


def rising_factorial(d: int, n, p: int | None = None):
    product = 1
    for j in range(d):
        product = product * (n + j)
        if p is not None:
            product %= p
    return product


def value(d: int, m: int, c: int, n: int, p: int) -> int:
    return (m * pow(factorial(d), -1, p) * rising_factorial(d, n, p) + c) % p


def possible_denominators(word: list[int], p: int) -> set[int]:
    """Exhaustive multiplier enumeration; zero is allowed unless both u and v vanish."""
    states = set(range(p))
    if word[0] == 0:
        states.discard(0)
    for u, next_u in zip(word, word[1:]):
        following: set[int] = set()
        for v in states:
            for a in range(p):
                if (a * u - v - next_u) % p == 0:
                    next_v = a * v % p
                    if next_u != 0 or next_v != 0:
                        following.add(next_v)
        states = following
    return states


def max_scale(d: int, c: int) -> int:
    x = Fraction(-1, 2) if c == 1 else Fraction(-3, 2)
    product = Fraction(1)
    for j in range(d):
        product *= x + j
    threshold = Fraction(factorial(d), 1) / abs(product)
    return (threshold.numerator - 1) // threshold.denominator


def extract_certificates(path: Path) -> dict[tuple[int, int], list[tuple[int, int]]]:
    text = path.read_text(encoding="utf-8")
    match = re.search(
        r"```python\n(CERTIFICATES = \{.*?^if __name__ == \"__main__\":\n.*?\n```)",
        text,
        flags=re.S | re.M,
    )
    if match is None:
        raise RuntimeError(f"could not extract CERTIFICATES python block from {path}")
    body = match.group(1)
    # Isolate the dict assignment only.
    dict_match = re.search(r"CERTIFICATES = (\{.*?\n\})", body, flags=re.S)
    if dict_match is None:
        raise RuntimeError("CERTIFICATES dict not found in extracted block")
    parsed = ast.literal_eval(dict_match.group(1))
    out: dict[tuple[int, int], list[tuple[int, int]]] = {}
    for key, rows in parsed.items():
        d, c = key
        out[(int(d), int(c))] = [(int(p), int(r)) for p, r in rows]
    return out


EXPECTED_THRESHOLDS = {
    (3, 1): (Fraction(16), 15),
    (3, -1): (Fraction(16), 15),
    (4, 1): (Fraction(128, 5), 25),
    (4, -1): (Fraction(128, 3), 42),
    (5, 1): (Fraction(256, 7), 36),
    (5, -1): (Fraction(256, 3), 85),
    (6, 1): (Fraction(1024, 21), 48),
    (6, -1): (Fraction(1024, 7), 146),
}


def threshold_exact(d: int, c: int) -> Fraction:
    x = Fraction(-1, 2) if c == 1 else Fraction(-3, 2)
    product = Fraction(1)
    for j in range(d):
        product *= x + j
    return Fraction(factorial(d), 1) / abs(product)


def verify(certificates: dict[tuple[int, int], list[tuple[int, int]]], *, degrees: tuple[int, ...]) -> dict:
    failures: list[object] = []
    count = 0
    per_degree: dict[int, int] = {}
    largest_prime: dict[int, int] = {}
    for (d, c), rows in sorted(certificates.items()):
        if d not in degrees:
            continue
        expected_t, expected_n = EXPECTED_THRESHOLDS[(d, c)]
        got_t = threshold_exact(d, c)
        if got_t != expected_t:
            failures.append(("threshold", d, c, str(got_t), str(expected_t)))
        if max_scale(d, c) != expected_n or len(rows) != expected_n:
            failures.append(("coverage", d, c, len(rows), expected_n, max_scale(d, c)))
        for m, (p, start) in enumerate(rows, 1):
            if not (is_prime(p) and p > d and 0 <= start < p):
                failures.append(("bad_prime_or_start", d, m, c, p, start))
                continue
            word = [value(d, m, c, start + j, p) for j in range(d + 1)]
            if 0 not in word[1:-1]:
                failures.append(("no_interior_zero", d, m, c, p, start, word))
                continue
            if possible_denominators(word, p):
                failures.append(("word_possible", d, m, c, p, start, word))
                continue
            count += 1
            per_degree[d] = per_degree.get(d, 0) + 1
            largest_prime[d] = max(largest_prime.get(d, 0), p)
    return {
        "verified_count": count,
        "per_degree": per_degree,
        "largest_prime": largest_prime,
        "failures": failures,
        "degrees": list(degrees),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="degrees 3 only (30 certificates)")
    ap.add_argument("--source", type=Path, default=TYPE_B_05)
    args = ap.parse_args()
    certificates = extract_certificates(args.source)
    degrees = (3,) if args.quick else (3, 4, 5, 6)
    report = verify(certificates, degrees=degrees)
    report["script"] = "check_erdos243_higher_degree_certificates.py"
    report["source"] = str(args.source.relative_to(REPO_ROOT))
    report["quick"] = args.quick
    report["claim_ceiling"] = (
        "finite exact forbidden-word replay only; positive lower density for "
        "each fixed profile of the listed degrees is an ordinary composition, "
        "not a uniform 1/((d+1)p) bound over all A, B; Erdős #243 remains open"
    )
    print(json.dumps(report, sort_keys=True))
    return 1 if report["failures"] else 0


if __name__ == "__main__":
    sys.exit(main())
