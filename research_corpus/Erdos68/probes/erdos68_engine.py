#!/usr/bin/env python3
"""Exact engine for the Erdos #68 factorial-digit stream.

The object
----------
`S = sum_(n>=2) 1/(n!-1)`.  Write `P_m = sum_(k=2)^m 1/(k!-1)` for the exact
rational prefix and

    N_m = strictFacTopRat(P_m, m) = floor(m! P_m) + 1

for the strict successor.  `FactorialZeroPlateau.lean` proves

    Irrational S  <->  for every B there is m > B with  m does not divide N_m,

so the whole problem is a divisibility test on one integer sequence.

Two derived quantities carry all of that:

    A_m = N_m - m! P_m  in (0, 1]        the predecessor gap, scaled
    D_m = m N_(m-1) - N_m                the factorial digit at index m

with the exact recurrences

    N_m = m N_(m-1) - D_m
    A_m = m A_(m-1) - 1 - 1/(m!-1) - D_m
    D_m = ceil(m A_(m-1) - 1 - 1/(m!-1)) - 1

and `A_(m-1) = sum_(j>=m) (D_j + 1 + 1/(j!-1)) * (m-1)!/j!`, i.e. the `D_j + 1`
are the rounding digits and the constant stream `(1 + 1/(j!-1))` rides along;
the identity is Lean-checked as `predGap_eq_carry_stream` in
`ErdosProblems/Erdos68/GapScalarNormalForm.lean` (omitting the carry stream
shifts the value by ~e/m and corrupts near-edge analysis).  Consequently

    m | N_m  <->  D_m = 0,

and `D_m = 0` is the same event Lean calls a unit carry.  `D_m` ranges over
`{-1, 0, ..., m-2}`.  The tail-free threshold is
`D_m + A_m >= 2/m`: `D_m = -1` always fails it, `D_m >= 1` always passes it,
and `D_m = 0` has the separate boundary condition `A_m >= 2/m` (see
`erdos68_digit_law`).

Why an engine
-------------
Every existing #68 computation rebuilt this recurrence privately, and each one
retained only the single predicate it happened to care about: the exact-Fraction
probe kept the certificate's truth value to m = 210, and the GMP certificate
kept only the nine indices where the carry was a unit.  The digits themselves
were discarded at 300000 indices.  This module keeps the stream, so a new
question about #68 costs a read rather than a rerun.

Two backends, verified equal
----------------------------
* `exact_digits`  -- `fractions.Fraction`, no floating point, no interval, but
  quadratic in the prefix denominator and unusable past a few hundred indices.
* `stream_digits` -- the repository's GMP interval certificate
  (`scripts/check_erdos68_strict_successor_gmp.cpp`), which carries `A_m` as an
  integer interval at `bits(M!) + guard` precision and aborts if the interval
  ever straddles a digit boundary.  The abort is what makes it a certificate:
  every emitted digit is proved, not estimated.

`verify_backends` checks them equal on a stated prefix.  Nothing here promotes a
finite computation to proof authority; that stays with Lean.
"""

from __future__ import annotations

import os
import subprocess
import sys
from fractions import Fraction
from pathlib import Path
from typing import Iterator

REPO_ROOT = Path(__file__).resolve().parents[2]

GMP_SOURCE = (
    "formal_math/erdos257_period_noncollapse/scripts/"
    "check_erdos68_strict_successor_gmp.cpp"
)

# Homebrew on Apple silicon; harmless elsewhere because the compiler ignores
# include/library roots that do not exist.
_GMP_PREFIXES = ("/opt/homebrew", "/usr/local", "/usr")


def exact_digits(max_m: int) -> Iterator[tuple[int, int, Fraction]]:
    """Yield `(m, D_m, A_m)` using exact rational arithmetic only.

    Reference implementation: no interval, no guard bits, no floating point.
    Quadratic in `max_m` in the size of the prefix denominator, so it is a
    cross-check for the certificate rather than a production path.
    """
    prefix = Fraction(0)
    factorial = 1
    previous = None
    for m in range(2, max_m + 1):
        factorial *= m
        prefix += Fraction(1, factorial - 1)
        scaled = factorial * prefix
        strict_successor = scaled.__floor__() + 1
        gap = Fraction(strict_successor) - scaled
        if not 0 < gap <= 1:
            raise AssertionError(f"gap left (0,1] at m={m}: {gap}")
        if previous is not None:
            yield m, m * previous - strict_successor, gap
        previous = strict_successor


def gmp_binary(*, rebuild: bool = False) -> Path:
    """Compile the repository's GMP strict-successor certificate, once."""
    build_dir = Path(
        os.environ.get(
            "ERDOS68_BUILD_DIR",
            REPO_ROOT / "state" / "formal_math" / "probes" / "_build",
        )
    )
    build_dir.mkdir(parents=True, exist_ok=True)
    binary = build_dir / "erdos68_strict_successor_gmp"
    source = REPO_ROOT / GMP_SOURCE
    if binary.exists() and not rebuild:
        if binary.stat().st_mtime >= source.stat().st_mtime:
            return binary
    includes = [f"-I{p}/include" for p in _GMP_PREFIXES if Path(p, "include").is_dir()]
    libs = [f"-L{p}/lib" for p in _GMP_PREFIXES if Path(p, "lib").is_dir()]
    command = [
        os.environ.get("CXX", "clang++"), "-O2", "-std=c++17",
        *includes, *libs, "-lgmpxx", "-lgmp",
        "-o", str(binary), str(source),
    ]
    completed = subprocess.run(command, capture_output=True, text=True)
    if completed.returncode != 0:
        raise RuntimeError(
            "failed to build the GMP strict-successor certificate:\n"
            + completed.stderr.strip()
        )
    return binary


def stream_digits(
    max_m: int,
    *,
    guard_bits: int = 96,
    cache_path: Path | None = None,
) -> tuple[list[int], dict]:
    """Return `(digits, meta)` where `digits[i]` is `D_(i+3)`.

    `digits` is dense and starts at `m = 3`.  `meta` carries the GMP version and
    the precision the certificate actually used, both of which belong in a
    receipt: the precision is what makes the emitted digits proved rather than
    estimated.
    """
    if max_m < 3:
        raise ValueError("max_m must be at least 3")
    text: str | None = None
    if cache_path is not None and cache_path.exists():
        text = cache_path.read_text(encoding="utf-8")
        if not text.rstrip().endswith(("\n", "0", "1", "2", "3", "4", "5",
                                       "6", "7", "8", "9", "a", "b", "c",
                                       "d", "e", "f")):
            text = None
    if text is None:
        binary = gmp_binary()
        completed = subprocess.run(
            [str(binary), str(max_m), str(guard_bits)],
            capture_output=True, text=True,
        )
        if completed.returncode != 0:
            raise RuntimeError(
                f"GMP certificate failed at max_m={max_m}: {completed.stderr.strip()}"
            )
        text = completed.stdout
        if cache_path is not None:
            cache_path.parent.mkdir(parents=True, exist_ok=True)
            cache_path.write_text(text, encoding="utf-8")

    digits: list[int] = []
    meta: dict = {"guard_bits": guard_bits}
    expected = 3
    for line in text.splitlines():
        if not line:
            continue
        tag, _, rest = line.partition("\t")
        if tag == "E":
            index_text, _, carry_text = rest.partition("\t")
            index = int(index_text)
            if index != expected:
                raise AssertionError(f"stream gap: expected {expected}, saw {index}")
            expected += 1
            # The certificate emits Lean's carry b_m; the digit is b_m - 1.
            digits.append(int(carry_text) - 1)
            if index >= max_m:
                break
        elif tag == "V":
            meta["gmp_version"] = rest
        elif tag == "P":
            meta["precision_bits"] = int(rest)
    if len(digits) != max_m - 2:
        raise AssertionError(
            f"truncated stream: {len(digits)} digits for max_m={max_m}"
        )
    meta["max_m"] = max_m
    meta["source"] = GMP_SOURCE
    return digits, meta


def verify_backends(check_m: int = 200) -> dict:
    """Assert the exact and certificate backends agree on `m <= check_m`."""
    reference = {m: digit for m, digit, _ in exact_digits(check_m)}
    digits, meta = stream_digits(check_m)
    mismatches = [
        (m, reference[m], digits[m - 3])
        for m in sorted(reference)
        if reference[m] != digits[m - 3]
    ]
    if mismatches:
        raise AssertionError(f"backend disagreement: {mismatches[:5]}")
    return {
        "checked_through_m": check_m,
        "compared_digits": len(reference),
        "mismatches": 0,
        "digit_min": min(reference.values()),
        "digit_max": max(reference.values()),
        "gmp_version": meta.get("gmp_version"),
        "precision_bits": meta.get("precision_bits"),
    }


def unit_carry_indices(digits: list[int], *, first_m: int = 3) -> list[int]:
    """Indices with `D_m = 0`, equivalently `m | N_m`, equivalently a unit carry."""
    return [first_m + i for i, d in enumerate(digits) if d == 0]


def threshold_failure_indices(digits: list[int], *, first_m: int = 3) -> list[int]:
    """Indices with `D_m = -1`, hence definite threshold failures.

    A full threshold census must additionally test the `D_m = 0` boundary
    `A_m >= 2/m`.  `erdos68_digit_law` performs that separate check.
    """
    return [first_m + i for i, d in enumerate(digits) if d == -1]


if __name__ == "__main__":
    import json

    check = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    print(json.dumps(verify_backends(check), indent=2))
