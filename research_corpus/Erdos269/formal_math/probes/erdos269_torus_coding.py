#!/usr/bin/env python3
"""Is the Erdos #269 radix word a coding of a rotation on the 2-torus?

Structural claim under test
---------------------------
The radix is b_a = 2 * 3^[a power of 3 lies in [2^a, 2^(a+1))] * 5^[likewise 5].
Now 3^j lies in [2^a, 2^(a+1)) exactly when floor(j*theta) = a with
theta = log_2 3, and 5^k likewise with phi = log_2 5.  So the two indicator
sequences are the characteristic sequences of the Beatty sets {floor(j*theta)}
and {floor(k*phi)}, and the radix word is their superposition -- i.e. a coding
of the orbit of a rotation on the 2-torus by (1/theta, 1/phi).

If that is right, the whole {2,3,5} source system is a cocycle over an ergodic
torus rotation whose angles are ratios of logarithms of 2, 3 and 5 -- a class
where linear forms in logarithms give effective Diophantine control.  That is a
structurally different mechanism from the carry/Lyapunov/observer families the
packet has retired.

Discriminating test
-------------------
A coding of a rank-1 rotation (Sturmian) has factor complexity p(n) = n + 1.
A coding of a genuine rank-2 torus rotation by two rationally independent
angles has quadratic complexity.  Measuring p(n) therefore separates the two
readings, and directly checking the Beatty identity confirms the coding.

Falsifier
---------
(1) Any a where the radix disagrees with the Beatty prediction.
(2) p(n) linear in n, which would mean the system is only Sturmian and the
    two-torus reading is wrong.
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

from formal_math.probes.erdos269_engine import build_dyadic_blocks  # noqa: E402


def beatty_indicator(slope_prime: int, max_a: int) -> set[int]:
    """{ a : some power of `slope_prime` lies in [2^a, 2^(a+1)) }, exactly."""
    hits: set[int] = set()
    value = slope_prime
    while value.bit_length() - 1 <= max_a:
        hits.add(value.bit_length() - 1)      # floor(log2 value)
        value *= slope_prime
    return hits


def factor_complexity(word: str, n: int) -> int:
    return len({word[i:i + n] for i in range(len(word) - n + 1)})


def run(max_a: int, max_factor: int, verify_a: int) -> dict:
    # Verification against the exact source engine on a bounded prefix: the
    # engine's construction is quadratic, so it sets the verification range,
    # not the word length.
    verify_a = min(verify_a, max_a)
    blocks = build_dyadic_blocks(verify_a)
    three = beatty_indicator(3, max_a + 2)
    five = beatty_indicator(5, max_a + 2)
    mismatches = []
    for a in range(1, verify_a + 1):
        predicted = 2 * (3 if a in three else 1) * (5 if a in five else 1)
        actual = blocks[a - 1][0]
        if predicted != actual:
            mismatches.append({"a": a, "predicted": predicted, "actual": actual})
    # The long word is generated from the verified Beatty description.
    letters = []
    for a in range(1, max_a + 1):
        radix = 2 * (3 if a in three else 1) * (5 if a in five else 1)
        letters.append({2: "a", 6: "b", 10: "c", 30: "d"}[radix])
    word = "".join(letters)

    complexity = {}
    for n in range(1, max_factor + 1):
        complexity[n] = factor_complexity(word, n)
    # linear vs quadratic discrimination on the measured range
    ns = list(complexity)
    lin_residual = max(abs(complexity[n] - (complexity[1] + (n - 1) * (complexity[2] - complexity[1])))
                       for n in ns)
    # fit p(n) = c2 n^2 + c1 n + c0 by least squares on the upper half
    upper = ns[len(ns) // 2:]
    import statistics  # noqa: F401
    A = [[n * n, n, 1] for n in upper]
    y = [complexity[n] for n in upper]
    # normal equations, 3x3
    AT_A = [[sum(A[r][i] * A[r][j] for r in range(len(A))) for j in range(3)] for i in range(3)]
    AT_y = [sum(A[r][i] * y[r] for r in range(len(A))) for i in range(3)]
    # gaussian elimination
    M = [row[:] + [AT_y[i]] for i, row in enumerate(AT_A)]
    for i in range(3):
        p = max(range(i, 3), key=lambda r: abs(M[r][i]))
        M[i], M[p] = M[p], M[i]
        for r in range(3):
            if r != i and M[i][i]:
                f = M[r][i] / M[i][i]
                M[r] = [M[r][c] - f * M[i][c] for c in range(4)]
    coef = [M[i][3] / M[i][i] if M[i][i] else 0.0 for i in range(3)]

    letter_freq = {ch: round(word.count(ch) / len(word), 5) for ch in "abcd"}
    # expected densities: P(3-hit) = 1/theta, P(5-hit) = 1/phi, independent
    theta, phi = log2(3), log2(5)
    expected = {
        "a": round((1 - 1 / theta) * (1 - 1 / phi), 5),
        "b": round((1 / theta) * (1 - 1 / phi), 5),
        "c": round((1 - 1 / theta) * (1 / phi), 5),
        "d": round((1 / theta) * (1 / phi), 5),
    }
    return {
        "probe_id": "erdos269_torus_coding",
        "max_a": max_a,
        "engine_verified_prefix": verify_a,
        "beatty_identity_mismatches": mismatches[:10],
        "beatty_identity_mismatch_count": len(mismatches),
        "radix_letter_frequency": letter_freq,
        "independent_rotation_prediction": expected,
        "factor_complexity": complexity,
        "max_deviation_from_linear": lin_residual,
        "quadratic_fit_upper_half": {
            "n^2": round(coef[0], 5), "n": round(coef[1], 4), "const": round(coef[2], 3)
        },
        "reading": (
            "quadratic complexity => rank-2 torus rotation coding"
            if coef[0] > 0.05 else
            "near-linear complexity => Sturmian, two-torus reading refuted"
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-a", type=int, default=200000)
    ap.add_argument("--max-factor", type=int, default=24)
    ap.add_argument("--verify-a", type=int, default=3000)
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    payload = run(args.max_a, args.max_factor, args.verify_a)
    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps(payload, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
