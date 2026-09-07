#!/usr/bin/env python3
"""Exact finite carry certificates for the Erdős 68 factorial-gap series.

For

    H_m = sum_{n=2}^m 1 / (n! - 1)

let ``N_m = floor(m! H_m) + 1`` and write

    N_m = m N_(m-1) + 1 - b_m.

The Lean development proves that a rational value ``S = a / q`` forces
``b_m = 1`` whenever ``m - 1 >= q``.  This checker computes the actual
``b_m`` with outward integer intervals only.  It does not use floating point,
probabilistic primality tests, or native proof evaluation.

Fix ``B = 2^P``.  The initial state ``Delta_2 = 1`` is exact; after the
first update, enclose the strict-successor gap ``Delta_m`` by
``L / B < Delta_m <= U / B``.  Since ``m! - 1`` is odd,

    floor(B / (m! - 1)) / B
      < 1 / (m! - 1)
      < (floor(B / (m! - 1)) + 1) / B.

The recurrence

    y_m = m Delta_(m-1) - 1 / (m! - 1),
    b_m = ceil(y_m) - 1,
    Delta_m = y_m - b_m

therefore has a certified integer update.  At every step the checker proves
that the full outward interval lies in one half-open unit cell before
recording ``b_m``.

The generated receipt is finite evidence.  In particular, the absence of a
unit carry through one bound does not prove cofinal non-unit carries.
"""

from __future__ import annotations

problem_id = "erdos_68"

import argparse
import difflib
import hashlib
import json
from math import factorial
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_RECEIPT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos68_strict_successor_receipt.json"
)
DEFAULT_MAX_INDEX = 100_000
DEFAULT_GUARD_BITS = 96
GMP_SOURCE = Path(__file__).with_name("check_erdos68_strict_successor_gmp.cpp")

# Independently reported exact data.  The checker re-derives this list and
# refuses a changed prefix, so the receipt is also a regression test.
KNOWN_UNIT_CARRIES_THROUGH_100000 = (
    52,
    591,
    1030,
    1407,
    1438,
    2164,
    4258,
    10991,
    21236,
)


def ceil_div(a: int, b: int) -> int:
    """Return the mathematical ceiling of ``a / b`` for positive ``b``."""

    if b <= 0:
        raise ValueError("ceil_div requires a positive denominator")
    return -((-a) // b)


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def integer_sha256(value: int) -> str:
    """Hash one signed integer using an unambiguous sign-and-magnitude form."""

    sign = b"-" if value < 0 else b"+"
    magnitude = abs(value)
    width = max(1, (magnitude.bit_length() + 7) // 8)
    return hashlib.sha256(sign + magnitude.to_bytes(width, "big")).hexdigest()


def attach_payload_hash(payload: dict[str, Any]) -> dict[str, Any]:
    encoded = json.dumps(payload, separators=(",", ":"), sort_keys=True).encode()
    return {**payload, "receipt_payload_sha256": hashlib.sha256(encoded).hexdigest()}


def verify_unit_carries(max_index: int, unit_carries: list[int]) -> None:
    """Refuse any change to the independently reported prefix."""

    known_prefix = [
        m for m in KNOWN_UNIT_CARRIES_THROUGH_100000 if m <= max_index
    ]
    if max_index <= 100_000 and unit_carries != known_prefix:
        raise AssertionError(
            "unit-carry regression: "
            f"computed {unit_carries}, expected {known_prefix}"
        )
    if max_index > 100_000:
        observed_prefix = [m for m in unit_carries if m <= 100_000]
        if observed_prefix != list(KNOWN_UNIT_CARRIES_THROUGH_100000):
            raise AssertionError(
                "the certified prefix through 100000 changed: "
                f"{observed_prefix}"
            )


def find_gmp_prefix() -> Path | None:
    for prefix in (Path("/opt/homebrew"), Path("/usr/local")):
        if (
            (prefix / "include/gmp.h").exists()
            and (prefix / "include/gmpxx.h").exists()
            and (prefix / "lib/libgmp.dylib").exists()
            and (prefix / "lib/libgmpxx.dylib").exists()
        ):
            return prefix
    return None


def build_gmp_checker() -> tuple[Path, str]:
    """Build and cache the exact GMP recurrence helper outside the repository."""

    prefix = find_gmp_prefix()
    if prefix is None:
        raise RuntimeError("GMP headers and libraries are unavailable")
    if not GMP_SOURCE.exists():
        raise RuntimeError(f"missing GMP checker source: {GMP_SOURCE}")

    source_hash = hashlib.sha256(GMP_SOURCE.read_bytes()).hexdigest()
    binary = (
        Path(tempfile.gettempdir())
        / f"aiw-erdos68-strict-successor-gmp-{source_hash[:20]}"
    )
    if binary.exists():
        return binary, source_hash

    compiler = os.environ.get("CXX", "/usr/bin/clang++")
    command = [
        compiler,
        "-std=c++17",
        "-O3",
        f"-I{prefix / 'include'}",
        str(GMP_SOURCE),
        f"-L{prefix / 'lib'}",
        f"-Wl,-rpath,{prefix / 'lib'}",
        "-lgmpxx",
        "-lgmp",
        "-o",
        str(binary),
    ]
    completed = subprocess.run(command, capture_output=True, text=True)
    if completed.returncode != 0:
        raise RuntimeError(
            "failed to compile GMP checker:\n"
            f"{completed.stdout}{completed.stderr}"
        )
    return binary, source_hash


def evaluate_gmp(max_index: int, guard_bits: int) -> dict[str, Any]:
    """Run the same recurrence with GMP integers and parse its exact trace."""

    binary, gmp_source_hash = build_gmp_checker()
    process = subprocess.Popen(
        [str(binary), str(max_index), str(guard_bits)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    assert process.stdout is not None
    assert process.stderr is not None

    precision_bits: int | None = None
    gmp_version: str | None = None
    event_trace = hashlib.sha256()
    event_count = 0
    unit_carries: list[int] = []
    final_values: dict[str, int] = {}

    for raw_line in process.stdout:
        parts = raw_line.rstrip("\n").split("\t")
        if parts[0] == "V" and len(parts) == 2:
            gmp_version = parts[1]
        elif parts[0] == "P" and len(parts) == 2:
            precision_bits = int(parts[1])
        elif parts[0] == "E" and len(parts) == 3:
            m = int(parts[1])
            carry = int(parts[2])
            event_trace.update(m.to_bytes(8, "big"))
            event_trace.update(carry.to_bytes(8, "big", signed=True))
            event_count += 1
            if carry == 1:
                unit_carries.append(m)
        elif parts[0] in {"L", "U", "N"} and len(parts) == 2:
            final_values[parts[0]] = int(parts[1], 16)
        else:
            process.kill()
            raise RuntimeError(f"unexpected GMP checker output: {raw_line!r}")

    stderr = process.stderr.read()
    return_code = process.wait()
    if return_code != 0:
        raise RuntimeError(
            f"GMP checker failed with exit {return_code}:\n{stderr}"
        )
    if stderr:
        raise RuntimeError(f"GMP checker wrote unexpected stderr:\n{stderr}")
    if precision_bits is None or gmp_version is None:
        raise RuntimeError("GMP checker omitted its version or precision")
    if event_count != max_index - 2:
        raise RuntimeError(
            f"GMP checker emitted {event_count} events, expected {max_index - 2}"
        )
    if set(final_values) != {"L", "U", "N"}:
        raise RuntimeError("GMP checker omitted a final state value")

    verify_unit_carries(max_index, unit_carries)
    lower = final_values["L"]
    upper = final_values["U"]
    return {
        "backend": "gmpxx",
        "backend_version": gmp_version,
        "precision_bits": precision_bits,
        "event_trace_sha256": event_trace.hexdigest(),
        "event_count": event_count,
        "unit_carries": unit_carries,
        "lower": lower,
        "upper": upper,
        "strict_successor": final_values["N"],
        "gmp_source_sha256": gmp_source_hash,
    }


def evaluate_python(max_index: int, guard_bits: int) -> dict[str, Any]:
    """Reference implementation using CPython's exact integers."""

    if max_index < 3:
        raise ValueError("max_index must be at least 3")
    if guard_bits < 1:
        raise ValueError("guard_bits must be positive")

    precision_bits = factorial(max_index).bit_length() + guard_bits
    scale = 1 << precision_bits

    # Delta_2 = 1, and N_2 = floor(2! * 1/(2!-1)) + 1 = 3.
    lower = scale
    upper = scale
    strict_successor = 3
    fac = 2
    unit_carries: list[int] = []
    event_trace = hashlib.sha256()

    for m in range(3, max_index + 1):
        fac *= m
        denominator = fac - 1
        reciprocal_floor = scale // denominator

        # The true y_m lies in (raw_lower / scale, raw_upper / scale].
        raw_lower = m * lower - reciprocal_floor - 1
        raw_upper = m * upper - reciprocal_floor
        carry = ceil_div(raw_upper, scale) - 1
        cell_lower = carry * scale
        cell_upper = (carry + 1) * scale

        if not raw_lower > cell_lower:
            raise AssertionError(
                f"lower interval crosses a carry boundary at m={m}"
            )
        if not raw_upper <= cell_upper:
            raise AssertionError(
                f"upper interval crosses a carry boundary at m={m}"
            )

        lower = raw_lower - cell_lower
        upper = raw_upper - cell_lower
        if not 0 < lower <= upper <= scale:
            raise AssertionError(f"invalid normalized interval at m={m}")

        strict_successor = m * strict_successor + 1 - carry
        if carry == 1:
            unit_carries.append(m)

        event_trace.update(m.to_bytes(8, "big"))
        event_trace.update(carry.to_bytes(8, "big", signed=True))

    verify_unit_carries(max_index, unit_carries)

    return {
        "backend": "python",
        "backend_version": ".".join(str(part) for part in os.sys.version_info[:3]),
        "precision_bits": precision_bits,
        "event_trace_sha256": event_trace.hexdigest(),
        "event_count": max_index - 2,
        "unit_carries": unit_carries,
        "lower": lower,
        "upper": upper,
        "strict_successor": strict_successor,
        "gmp_source_sha256": None,
    }


def evaluate(max_index: int, guard_bits: int, backend: str) -> dict[str, Any]:
    if max_index < 3:
        raise ValueError("max_index must be at least 3")
    if guard_bits < 1:
        raise ValueError("guard_bits must be positive")

    if backend == "auto":
        backend = "gmp" if find_gmp_prefix() is not None else "python"
    state = (
        evaluate_gmp(max_index, guard_bits)
        if backend == "gmp"
        else evaluate_python(max_index, guard_bits)
    )

    precision_bits = state["precision_bits"]
    unit_carries = state["unit_carries"]
    lower = state["lower"]
    upper = state["upper"]
    strict_successor = state["strict_successor"]
    last_unit_carry = unit_carries[-1] if unit_carries else None
    terminal_carry_is_nonunit = max_index not in unit_carries
    if not terminal_carry_is_nonunit:
        raise AssertionError(
            "the selected terminal index is a unit carry and supplies no "
            "denominator lower bound"
        )

    source_sha256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload = {
        "schema": "erdos68_strict_successor_exact_interval_v1",
        "authority": {
            "arithmetic": f"exact_{state['backend']}_integers",
            "backend_version": state["backend_version"],
            "floating_point_used": False,
            "lean_boundary": (
                "Lean proves that a rational representation S=a/q with "
                "q<=m-1 forces factorialGapStepCarry m=1.  This receipt "
                "computes the corresponding finite carries independently."
            ),
            "source_sha256": source_sha256,
            "gmp_source_sha256": state["gmp_source_sha256"],
        },
        "parameters": {
            "guard_bits": guard_bits,
            "max_index": max_index,
            "precision_bits": precision_bits,
            "scale": f"2^{precision_bits}",
        },
        "certificate": {
            "asserted_carry_cells": state["event_count"],
            "event_trace_sha256": state["event_trace_sha256"],
            "final_interval": {
                "lower_sha256": integer_sha256(lower),
                "upper_sha256": integer_sha256(upper),
                "width_bits": (upper - lower).bit_length(),
            },
            "final_strict_successor_sha256": integer_sha256(strict_successor),
            "last_unit_carry": last_unit_carry,
            "terminal_carry_is_nonunit": terminal_carry_is_nonunit,
            "unit_carries": unit_carries,
            "unit_carry_count": len(unit_carries),
        },
        "mathematical_consequence": {
            "claim": (
                f"Every displayed rational representation S=a/q with q>0 "
                f"has q>={max_index}."
            ),
            "logical_reach": "finite_denominator_exclusion",
            "not_claimed": [
                "cofinally many non-unit carries",
                "irrationality of the series",
            ],
            "reason": (
                f"factorialGapStepCarry {max_index} is certified non-unit; "
                "the checked Lean consumer rational_denominator_ge_of_"
                "nonunit_carry converts that finite fact to the displayed "
                "denominator bound."
            ),
        },
    }
    return attach_payload_hash(payload)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-index", type=int, default=DEFAULT_MAX_INDEX)
    parser.add_argument("--guard-bits", type=int, default=DEFAULT_GUARD_BITS)
    parser.add_argument(
        "--backend",
        choices=("auto", "gmp", "python"),
        default="auto",
        help="exact integer backend (auto prefers GMP when available)",
    )
    parser.add_argument("--receipt", type=Path, default=DEFAULT_RECEIPT)
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare the regenerated receipt with the existing file",
    )
    args = parser.parse_args()

    receipt = evaluate(args.max_index, args.guard_bits, args.backend)
    rendered = canonical_json(receipt)

    if args.check:
        if not args.receipt.exists():
            raise SystemExit(f"missing receipt: {args.receipt}")
        current = args.receipt.read_text()
        if current != rendered:
            diff = "".join(
                difflib.unified_diff(
                    current.splitlines(keepends=True),
                    rendered.splitlines(keepends=True),
                    fromfile=str(args.receipt),
                    tofile="regenerated",
                )
            )
            raise SystemExit(diff or "receipt differs")
        print(f"ok: {args.receipt}")
        return 0

    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(rendered)
    print(canonical_json(receipt), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
