#!/usr/bin/env python3
"""Exact finite scan for repeated factorial-gap valuation records in Erdős 68.

For each prime ``q`` in the requested interval, this checker scans

    g_n = n! - 1,    2 <= n < q.

There are no later ``q``-hits because ``q`` divides ``n!`` for ``n >= q``.
The checker records every index at which ``v_q(g_n)`` strictly exceeds
all earlier positive values, and keeps only records with an earlier
``q``-hit.  Such a repeated strict record is exactly an arithmetic input
to the Lean theorems that put its complete prime power into the next
reduced denominator with a nonzero numerator projection.

Through the fixed Python audit prefix the primary scan uses multiplication
modulo ``q^3``.  Larger bounds use the companion exact C++ ``q^2`` scanner,
independently compare its complete prefix through 50,000 with the Python
``q^3`` implementation, and recheck every square prime in Python.  Any
cube hit is escalated with exact modular arithmetic until its full
valuation is known.  Every square prime in the audit prefix is also
rechecked with unrestricted integer factorials.  This is finite evidence,
not an infinitude, density, or irrationality proof.
"""

from __future__ import annotations

problem_id = "erdos_68"

import argparse
import hashlib
import json
from math import factorial, isqrt
import os
from pathlib import Path
import platform
import subprocess
import tempfile
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_RECEIPT = (
    REPO_ROOT
    / "state/formal_math/erdos257_period_noncollapse/"
    "erdos68_arbitrary_valuation_record_receipt.json"
)
FAST_SOURCE = Path(__file__).with_name(
    "check_erdos68_arbitrary_valuation_records_fast.cpp"
)
DEFAULT_MAX_PRIME = 1_000_000
DEFAULT_CHUNK_SIZE = 100_000
PYTHON_PREFIX_BOUND = 50_000

EXPECTED_FIRST_SQUARES_THROUGH_50K = (
    (11, 9),
    (31, 15),
    (107, 105),
    (571, 112),
    (971, 609),
    (4931, 4929),
)
EXPECTED_REPEATED_RECORDS_THROUGH_50K = (
    (107, 53, 105),
    (971, 361, 609),
    (4931, 2327, 4929),
)


def build_fast_checker() -> tuple[Path, str, str]:
    """Build and cache the exact C++ scan helper outside the repository."""

    if not FAST_SOURCE.exists():
        raise RuntimeError(f"missing fast checker source: {FAST_SOURCE}")
    source_hash = hashlib.sha256(FAST_SOURCE.read_bytes()).hexdigest()
    binary = (
        Path(tempfile.gettempdir())
        / f"aiw-erdos68-arbitrary-records-{source_hash[:20]}"
    )
    compiler = os.environ.get("CXX", "/usr/bin/clang++")
    if not binary.exists():
        completed = subprocess.run(
            [
                compiler,
                "-std=c++17",
                "-O3",
                "-pthread",
                str(FAST_SOURCE),
                "-o",
                str(binary),
            ],
            capture_output=True,
            text=True,
        )
        if completed.returncode != 0:
            raise RuntimeError(
                "failed to compile fast checker:\n"
                f"{completed.stdout}{completed.stderr}"
            )
    return binary, source_hash, compiler


def _run_fast_range(
    min_prime: int,
    max_prime: int,
    *,
    binary: Path,
    threads: int,
) -> tuple[list[dict[str, Any]], str]:
    """Run and parse one exact, independently addressable prime interval."""

    completed = subprocess.run(
        [str(binary), str(min_prime), str(max_prime), str(threads)],
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"fast checker failed with exit {completed.returncode}:\n"
            f"{completed.stdout}{completed.stderr}"
        )
    if completed.stderr:
        raise RuntimeError(
            f"fast checker wrote unexpected stderr:\n{completed.stderr}"
        )
    rows: list[dict[str, Any]] = []
    version: str | None = None
    for raw_line in completed.stdout.splitlines():
        fields = raw_line.split("\t")
        if fields[0] == "V" and len(fields) == 2:
            version = fields[1]
            continue
        if fields[0] != "P" or len(fields) != 8:
            raise RuntimeError(f"unexpected fast-checker row: {raw_line!r}")
        (
            _tag,
            raw_q,
            raw_support,
            raw_square,
            raw_cube,
            raw_support_count,
            raw_square_count,
            raw_cube_count,
        ) = fields
        q = int(raw_q)
        first_support = int(raw_support)
        first_square = int(raw_square)
        first_cube = int(raw_cube)
        support_count = int(raw_support_count)
        square_hit_count = int(raw_square_count)
        cube_hit_count = int(raw_cube_count)
        maximum_valuation = (
            3 if first_cube >= 0 else
            2 if first_square >= 0 else
            1 if first_support >= 0 else
            0
        )
        repeated_records: list[dict[str, Any]] = []
        if (
            first_square >= 0
            and first_support >= 0
            and first_support != first_square
        ):
            repeated_records.append(
                {
                    "q": q,
                    "earlier_support_index": first_support,
                    "record_index": first_square,
                    "previous_record_valuation": 1,
                    "new_record_valuation": 2,
                    "prime_power": q * q,
                    "terminal_wilson_index": first_square == q - 2,
                }
            )
        rows.append(
            {
                "q": q,
                "first_support_index":
                    None if first_support < 0 else first_support,
                "first_square_index":
                    None if first_square < 0 else first_square,
                "first_cube_index":
                    None if first_cube < 0 else first_cube,
                "support_count": support_count,
                "square_hit_count": square_hit_count,
                "cube_hit_count": cube_hit_count,
                "maximum_valuation": maximum_valuation,
                "repeated_records": repeated_records,
            }
        )
    if version != "1":
        raise RuntimeError(f"unexpected fast-checker version: {version!r}")
    if any(not (min_prime <= int(row["q"]) <= max_prime) for row in rows):
        raise RuntimeError("fast checker emitted a prime outside its requested range")
    if any(
        int(left["q"]) >= int(right["q"])
        for left, right in zip(rows, rows[1:], strict=False)
    ):
        raise RuntimeError("fast checker rows are not strictly prime-ordered")
    return rows, version


def _checkpoint_payload(
    *,
    source_hash: str,
    min_prime: int,
    max_prime: int,
    output_version: str,
    rows: list[dict[str, Any]],
) -> dict[str, Any]:
    core = {
        "schema": "erdos68-arbitrary-valuation-fast-chunk/1",
        "fast_source_sha256": source_hash,
        "min_prime": min_prime,
        "max_prime": max_prime,
        "output_version": output_version,
        "rows": rows,
    }
    return {**core, "payload_sha256": canonical_payload_sha256(core)}


def _load_checkpoint(
    path: Path,
    *,
    source_hash: str,
    min_prime: int,
    max_prime: int,
) -> list[dict[str, Any]] | None:
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    digest = payload.pop("payload_sha256", None)
    if digest != canonical_payload_sha256(payload):
        raise RuntimeError(f"checkpoint digest mismatch: {path}")
    expected = {
        "schema": "erdos68-arbitrary-valuation-fast-chunk/1",
        "fast_source_sha256": source_hash,
        "min_prime": min_prime,
        "max_prime": max_prime,
        "output_version": "1",
    }
    for key, value in expected.items():
        if payload.get(key) != value:
            raise RuntimeError(
                f"checkpoint metadata mismatch at {path}: {key}"
            )
    rows = payload.get("rows")
    if not isinstance(rows, list):
        raise RuntimeError(f"checkpoint rows are not an array: {path}")
    return rows


def _write_checkpoint(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + f".tmp-{os.getpid()}")
    temporary.write_text(canonical_json(payload), encoding="utf-8")
    os.replace(temporary, path)


def fast_scan_rows(
    max_prime: int,
    *,
    checkpoint_dir: Path | None = None,
    chunk_size: int = DEFAULT_CHUNK_SIZE,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """Run the exact q² scan, optionally resuming content-bound chunks."""

    if max_prime < 2:
        raise ValueError("max_prime must be at least 2")
    if chunk_size <= 0:
        raise ValueError("chunk_size must be positive")
    binary, source_hash, compiler = build_fast_checker()
    threads = max(1, min(os.cpu_count() or 1, 12))
    ranges = (
        [(2, max_prime)]
        if checkpoint_dir is None
        else [
            (lower, min(max_prime, lower + chunk_size - 1))
            for lower in range(2, max_prime + 1, chunk_size)
        ]
    )
    rows: list[dict[str, Any]] = []
    reused_chunk_count = 0
    written_chunk_count = 0
    checkpoint_refs: list[str] = []
    for min_prime, range_max in ranges:
        chunk_rows: list[dict[str, Any]] | None = None
        checkpoint_path: Path | None = None
        if checkpoint_dir is not None:
            checkpoint_path = checkpoint_dir / (
                f"{min_prime:010d}-{range_max:010d}-{source_hash[:20]}.json"
            )
            chunk_rows = _load_checkpoint(
                checkpoint_path,
                source_hash=source_hash,
                min_prime=min_prime,
                max_prime=range_max,
            )
        if chunk_rows is None:
            chunk_rows, version = _run_fast_range(
                min_prime,
                range_max,
                binary=binary,
                threads=threads,
            )
            if checkpoint_path is not None:
                _write_checkpoint(
                    checkpoint_path,
                    _checkpoint_payload(
                        source_hash=source_hash,
                        min_prime=min_prime,
                        max_prime=range_max,
                        output_version=version,
                        rows=chunk_rows,
                    ),
                )
                written_chunk_count += 1
        else:
            reused_chunk_count += 1
        if checkpoint_path is not None:
            checkpoint_refs.append(str(checkpoint_path))
        rows.extend(chunk_rows)
    return rows, {
        "backend": "compiled_cpp_uint64_q_squared_with_uint128_products",
        "fast_source_sha256": source_hash,
        "compiler": compiler,
        "thread_count": threads,
        "output_version": "1",
        "checkpointing": {
            "enabled": checkpoint_dir is not None,
            "chunk_size": chunk_size,
            "chunk_count": len(ranges),
            "reused_chunk_count": reused_chunk_count,
            "written_chunk_count": written_chunk_count,
            "checkpoint_refs": checkpoint_refs,
        },
    }


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def canonical_payload_sha256(payload: Any) -> str:
    encoded = json.dumps(
        payload, separators=(",", ":"), sort_keys=True
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def primes_through(bound: int) -> list[int]:
    if bound < 2:
        return []
    sieve = bytearray(b"\x01") * (bound + 1)
    sieve[:2] = b"\x00\x00"
    for q in range(2, isqrt(bound) + 1):
        if sieve[q]:
            start = q * q
            sieve[start : bound + 1 : q] = b"\x00" * (
                ((bound - start) // q) + 1
            )
    return [n for n in range(2, bound + 1) if sieve[n]]


def factorial_mod(index: int, modulus: int) -> int:
    residue = 1
    for factor in range(2, index + 1):
        residue = (residue * factor) % modulus
    return residue


def exact_modular_valuation(q: int, index: int) -> int:
    """Return ``v_q(index! - 1)`` without constructing ``index!``."""

    exponent = 1
    modulus = q
    while factorial_mod(index, modulus) == 1:
        exponent += 1
        modulus *= q
    return exponent - 1


def scan_prime(q: int) -> dict[str, Any]:
    modulus_squared = q * q
    modulus_cubed = modulus_squared * q
    residue = 1
    first_support_index: int | None = None
    first_square_index: int | None = None
    first_cube_index: int | None = None
    support_count = 0
    square_hit_count = 0
    cube_hit_count = 0
    record_valuation = 0
    repeated_records: list[dict[str, Any]] = []

    for index in range(2, q):
        residue = (residue * index) % modulus_cubed
        if residue % q != 1:
            continue

        support_count += 1
        if first_support_index is None:
            first_support_index = index

        valuation = 1
        if residue % modulus_squared == 1:
            valuation = 2
            square_hit_count += 1
            if first_square_index is None:
                first_square_index = index
        if residue == 1:
            valuation = exact_modular_valuation(q, index)
            cube_hit_count += 1
            if first_cube_index is None:
                first_cube_index = index

        if valuation <= record_valuation:
            continue
        if record_valuation > 0:
            repeated_records.append(
                {
                    "q": q,
                    "earlier_support_index": first_support_index,
                    "record_index": index,
                    "previous_record_valuation": record_valuation,
                    "new_record_valuation": valuation,
                    "prime_power": q**valuation,
                    "terminal_wilson_index": index == q - 2,
                }
            )
        record_valuation = valuation

    return {
        "q": q,
        "first_support_index": first_support_index,
        "first_square_index": first_square_index,
        "first_cube_index": first_cube_index,
        "support_count": support_count,
        "square_hit_count": square_hit_count,
        "cube_hit_count": cube_hit_count,
        "maximum_valuation": record_valuation,
        "repeated_records": repeated_records,
    }


def unrestricted_factorial_crosscheck(q: int) -> dict[str, Any]:
    """Recompute one prime's record trace using full integer factorials."""

    first_support_index: int | None = None
    first_square_index: int | None = None
    first_cube_index: int | None = None
    record_valuation = 0
    repeated_records: list[dict[str, int]] = []

    for index in range(2, q):
        gap = factorial(index) - 1
        if gap % q != 0:
            continue
        if first_support_index is None:
            first_support_index = index
        valuation = 0
        quotient = gap
        while quotient % q == 0:
            quotient //= q
            valuation += 1
        if valuation >= 2 and first_square_index is None:
            first_square_index = index
        if valuation >= 3 and first_cube_index is None:
            first_cube_index = index
        if valuation > record_valuation:
            if record_valuation > 0:
                repeated_records.append(
                    {
                        "record_index": index,
                        "previous_record_valuation": record_valuation,
                        "new_record_valuation": valuation,
                    }
                )
            record_valuation = valuation

    return {
        "q": q,
        "first_support_index": first_support_index,
        "first_square_index": first_square_index,
        "first_cube_index": first_cube_index,
        "maximum_valuation": record_valuation,
        "repeated_records": repeated_records,
    }


def build_receipt(
    max_prime: int,
    *,
    checkpoint_dir: Path | None = None,
    chunk_size: int = DEFAULT_CHUNK_SIZE,
) -> dict[str, Any]:
    if max_prime < 4931:
        raise ValueError(
            "max_prime must be at least 4931 so the complete known "
            "repeated-record prefix is inside the certified interval"
        )

    primes = primes_through(max_prime)
    fast_authority: dict[str, Any] | None = None
    if max_prime <= PYTHON_PREFIX_BOUND:
        rows = [scan_prime(q) for q in primes]
    else:
        rows, fast_authority = fast_scan_rows(
            max_prime,
            checkpoint_dir=checkpoint_dir,
            chunk_size=chunk_size,
        )
        if [int(row["q"]) for row in rows] != primes:
            raise AssertionError(
                "fast checker prime enumeration disagrees with Python sieve"
            )
        prefix_primes = [
            q for q in primes if q <= PYTHON_PREFIX_BOUND
        ]
        python_prefix = [scan_prime(q) for q in prefix_primes]
        fast_prefix = rows[:len(prefix_primes)]
        if fast_prefix != python_prefix:
            raise AssertionError(
                "fast q-squared trace disagrees with the independent "
                "Python q-cubed prefix through 50000"
            )
        row_positions = {
            int(row["q"]): position
            for position, row in enumerate(rows)
        }
        for row in list(rows):
            if row["first_square_index"] is not None:
                q = int(row["q"])
                python_row = scan_prime(q)
                if row != python_row:
                    raise AssertionError(
                        f"fast square-prime trace disagrees with the "
                        f"independent Python q-cubed rescan at q={q}"
                    )
                rows[row_positions[q]] = python_row
    first_squares = [
        (int(row["q"]), int(row["first_square_index"]))
        for row in rows
        if row["first_square_index"] is not None
    ]
    repeated_records = [
        record
        for row in rows
        for record in row["repeated_records"]
    ]
    repeated_record_signature = [
        (
            int(record["q"]),
            int(record["earlier_support_index"]),
            int(record["record_index"]),
        )
        for record in repeated_records
    ]
    cube_hits = [
        (int(row["q"]), int(row["first_cube_index"]))
        for row in rows
        if row["first_cube_index"] is not None
    ]

    if max_prime <= PYTHON_PREFIX_BOUND:
        expected_squares = [
            row
            for row in EXPECTED_FIRST_SQUARES_THROUGH_50K
            if row[0] <= max_prime
        ]
        expected_records = [
            row
            for row in EXPECTED_REPEATED_RECORDS_THROUGH_50K
            if row[0] <= max_prime
        ]
        if first_squares != expected_squares:
            raise AssertionError(
                "first-square prefix regression: "
                f"computed {first_squares}, expected {expected_squares}"
            )
        if repeated_record_signature != expected_records:
            raise AssertionError(
                "repeated-record prefix regression: "
                f"computed {repeated_record_signature}, "
                f"expected {expected_records}"
            )
        if cube_hits:
            raise AssertionError(
                f"unexpected cube hit through {max_prime}: {cube_hits}"
            )
    elif [
        row for row in repeated_record_signature if row[0] <= 50_000
    ] != list(EXPECTED_REPEATED_RECORDS_THROUGH_50K):
        raise AssertionError(
            "the certified repeated-record prefix through 50000 changed"
        )

    square_primes = [q for q, _ in first_squares]
    independent = [
        unrestricted_factorial_crosscheck(q)
        for q in square_primes
        if q <= PYTHON_PREFIX_BOUND
    ]
    later_modular_crosschecks = [
        {
            "q": int(row["q"]),
            "first_support_index": row["first_support_index"],
            "first_square_index": row["first_square_index"],
            "first_cube_index": row["first_cube_index"],
            "maximum_valuation": row["maximum_valuation"],
            "method": "independent_python_q_cubed_rescan",
        }
        for row in rows
        if (
            int(row["q"]) > PYTHON_PREFIX_BOUND
            and row["first_square_index"] is not None
        )
    ]
    row_by_q = {int(row["q"]): row for row in rows}
    for crosscheck in independent:
        q = int(crosscheck["q"])
        primary = row_by_q[q]
        for field in (
            "first_support_index",
            "first_square_index",
            "first_cube_index",
            "maximum_valuation",
        ):
            if crosscheck[field] != primary[field]:
                raise AssertionError(
                    f"independent factorial crosscheck failed at "
                    f"q={q}, field={field}"
                )
        primary_records = [
            {
                "record_index": record["record_index"],
                "previous_record_valuation":
                    record["previous_record_valuation"],
                "new_record_valuation": record["new_record_valuation"],
            }
            for record in primary["repeated_records"]
        ]
        if crosscheck["repeated_records"] != primary_records:
            raise AssertionError(
                f"independent record crosscheck failed at q={q}"
            )

    trace_rows = [
        {
            "q": row["q"],
            "first_support_index": row["first_support_index"],
            "first_square_index": row["first_square_index"],
            "first_cube_index": row["first_cube_index"],
            "support_count": row["support_count"],
            "square_hit_count": row["square_hit_count"],
            "cube_hit_count": row["cube_hit_count"],
            "maximum_valuation": row["maximum_valuation"],
        }
        for row in rows
    ]
    terminal_records = [
        record for record in repeated_records
        if record["terminal_wilson_index"]
    ]
    nonterminal_records = [
        record for record in repeated_records
        if not record["terminal_wilson_index"]
    ]
    source_sha256 = hashlib.sha256(
        Path(__file__).read_bytes()
    ).hexdigest()
    payload: dict[str, Any] = {
        "schema": "erdos68_arbitrary_valuation_record_exact_scan_v2",
        "parameters": {
            "max_prime": max_prime,
            "prime_count": len(primes),
            "factorial_index_interval": "2 <= n < q",
            "primary_modulus": (
                "q^2_fast_scan_with_q^3_python_recheck_for_every_"
                "square_prime"
                if fast_authority is not None else
                "q^3_python_scan_with_exact_escalation_on_cube_hits"
            ),
            "arithmetic": (
                "exact_compiled_integer_modular_multiplication_with_"
                "independent_python_prefix"
                if fast_authority is not None else
                "exact_python_integer_modular_multiplication"
            ),
            "floating_point_used": False,
            "probabilistic_primality_used": False,
        },
        "authority": {
            "source_sha256": source_sha256,
            "python_version": platform.python_version(),
            "prime_enumeration": "deterministic_eratosthenes_sieve",
            "fast_backend": fast_authority,
            "independent_method": (
                "independent Python q^3 scan for every prime through "
                "50000, Python q^3 rescan for every later square prime, "
                "and unrestricted integer factorials for every square "
                "prime"
            ),
            "lean_consumers": [
                "factorialGap_firstRepeatedPrimeSquare_entry",
                "factorialGap_repeatedRecordPrimePower_dvd_succ_den",
                "predecessorGapNumeratorNat_mod_"
                "repeatedRecordPrimePower_ne_zero",
            ],
        },
        "certificate": {
            "first_square_hits": [
                {
                    "q": int(row["q"]),
                    "first_support_index": row["first_support_index"],
                    "first_square_index": row["first_square_index"],
                    "first_square_is_repeated":
                        row["first_support_index"]
                        != row["first_square_index"],
                    "terminal_wilson_index":
                        row["first_square_index"] == int(row["q"]) - 2,
                }
                for row in rows
                if row["first_square_index"] is not None
            ],
            "first_square_hit_count": len(first_squares),
            "repeated_strict_record_events": repeated_records,
            "repeated_strict_record_count": len(repeated_records),
            "terminal_wilson_repeated_records": terminal_records,
            "nonterminal_repeated_records": nonterminal_records,
            "cube_hits": cube_hits,
            "scan_trace_sha256": canonical_payload_sha256(
                {"rows": trace_rows}
            ),
            "independent_exact_factorial_crosschecks": independent,
            "later_square_prime_modular_crosschecks":
                later_modular_crosschecks,
        },
        "mathematical_consequence": {
            "claim": (
                f"Among all primes q<={max_prime} and all factorial "
                f"indices 2<=n<q, exactly {len(repeated_records)} strict "
                "q-adic records occur after an earlier q-hit: "
                + ", ".join(
                    f"(q,n)=({record['q']},{record['record_index']})"
                    for record in repeated_records
                )
                + "."
            ),
            "new_nonterminal_event": (
                "The event (q,n)=(971,609), preceded by q|361!-1, "
                "is not a Wilson terminal index because 609<971-2. "
                "It proves that the arbitrary-index record family is "
                "strictly larger than the n=q-2 Wilson subfamily."
            ),
            "lean_reach": (
                "Each event satisfies the finite arithmetic shape of "
                "the checked repeated-record denominator theorems. "
                "The q=107 and nonterminal q=971 events are separately "
                "certified cell-by-cell in the Lean kernel; this receipt "
                "remains the finite authority for q=4931."
            ),
            "logical_reach":
                "finite_three_event_repeated_valuation_record_evidence",
            "not_claimed": [
                "a Lean-kernel certificate for q=4931",
                f"another repeated record above {max_prime}",
                "infinitely many repeated valuation records",
                "a positive density or asymptotic lower bound",
                "cofinally large amplification mass",
                "the required Archimedean numerator-residue lower bound",
                "irrationality of the Erdős 68 series",
            ],
        },
    }
    payload["receipt_payload_sha256"] = canonical_payload_sha256(payload)
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-prime", type=int, default=DEFAULT_MAX_PRIME
    )
    parser.add_argument(
        "--checkpoint-dir",
        type=Path,
        help=(
            "persist content-bound exact range chunks here and reuse them on rerun"
        ),
    )
    parser.add_argument(
        "--chunk-size", type=int, default=DEFAULT_CHUNK_SIZE
    )
    parser.add_argument(
        "--output", type=Path, default=DEFAULT_RECEIPT
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--write", action="store_true", help="write the canonical receipt"
    )
    mode.add_argument(
        "--check",
        action="store_true",
        help="require the canonical receipt to be current",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.chunk_size <= 0:
        raise SystemExit("chunk-size must be positive")
    payload = build_receipt(
        args.max_prime,
        checkpoint_dir=args.checkpoint_dir,
        chunk_size=args.chunk_size,
    )
    rendered = canonical_json(payload)
    if args.write:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
        print(args.output)
        return 0
    if args.check:
        if not args.output.exists():
            raise SystemExit(f"missing receipt: {args.output}")
        current = args.output.read_text()
        if current != rendered:
            raise SystemExit(f"stale receipt: {args.output}")
        print(
            "erdos68 arbitrary valuation-record receipt current: "
            f"{args.output}"
        )
        return 0
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
