#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the source-backed checked LCM-diagonal depth roster through t = 82.

The roster reads the actual Lean theorem signatures that exhibit

    certifiedKill (periodLcm t) (periodLcm t) L

at every distinct LCM scale in the continuous checked band.  A working depth
is not called least unless a separate Lean theorem states both the certificate
and failure at every smaller depth.

For H = lcm(1,...,t), the arithmetic admissibility floor is the least L >= 1
with

    2^L > 2 * (2H + L + 2).

At a source-proved least depth, depth minus floor is exact.  At a merely
checked working depth, the same subtraction is only an upper bound on the
least-depth excess.

This is finite source extraction, not a new proof search.  It makes no claim
beyond t = 82 and no asymptotic, equidistribution, bounded-excess, or cofinal
inference.

Usage:

    python3 scripts/build_checked_diagonal_depth_roster.py
    python3 scripts/build_checked_diagonal_depth_roster.py --write
    python3 scripts/build_checked_diagonal_depth_roster.py --check
"""

from __future__ import annotations

import argparse
from hashlib import sha256
import json
from math import gcd, lcm
from pathlib import Path
import re
import sys
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = (
    ROOT
    / "docs"
    / "measurements"
    / "checked_diagonal_depth_roster.json"
)

BAND_MIN_T = 1
BAND_MAX_T = 82

# These are the canonical source owners for the certificate declarations in
# this roster.  The t=64 endpoint file is the claims-registry source for that
# cell; the separate chained t=64 module is intentionally not double-counted.
CERTIFICATE_SOURCE_PATHS = (
    "Erdos249257/DiagonalPincerCertificates.lean",
    "Erdos249257/DiagonalPincerCertificatesT19.lean",
    "Erdos249257/DiagonalPincerCertificatesT23.lean",
    "Erdos249257/DiagonalPincerCertificatesT25.lean",
    "Erdos249257/DiagonalPincerCertificatesT27.lean",
    "Erdos249257/DiagonalPincerCertificatesT29.lean",
    "Erdos249257/DiagonalPincerCertificatesT31.lean",
    "Erdos249257/DiagonalPincerCertificatesT32.lean",
    "Erdos249257/DiagonalPincerCertificatesT37.lean",
    "Erdos249257/DiagonalPincerCertificatesT41.lean",
    "Erdos249257/DiagonalPincerCertificatesT43.lean",
    "Erdos249257/DiagonalPincerCertificatesT47.lean",
    "Erdos249257/DiagonalPincerCertificatesT49.lean",
    "Erdos249257/DiagonalPincerCertificatesT53.lean",
    "Erdos249257/DiagonalPincerCertificatesT59.lean",
    "Erdos249257/DiagonalPincerCertificatesT61.lean",
    "Erdos249257/DiagonalPincerCertificateT64Endpoint.lean",
    "ErdosProblems/Lift/Recon67.lean",
    "ErdosProblems/Lift/CertT67.lean",
    "ErdosProblems/Skip/LadderT67.lean",
)
BAND_SOURCE_PATH = "ErdosProblems/Skip/LadderT67.lean"
DEPTH_FLOOR_SOURCE_PATH = "Erdos249257/TotientTailPeriodKiller.lean"

CERTIFICATE_HEAD_RE = re.compile(
    r"(?m)^theorem\s+certifiedKill_diagonal_t\d+\b"
)
CERTIFICATE_RE = re.compile(
    r"""
    ^theorem\s+
    (?P<declaration>certifiedKill_diagonal_t(?P<name_t>\d+))
    \s*:\s*
    certifiedKill
    \s*\(\s*periodLcm\s+(?P<first_t>\d+)\s*\)
    \s*\(\s*periodLcm\s+(?P<second_t>\d+)\s*\)
    \s*(?P<depth>\d+)\s*:=\s*by\b
    """,
    re.MULTILINE | re.VERBOSE,
)

MINIMALITY_HEAD_RE = re.compile(
    r"(?m)^theorem\s+t\d+_minimal_depth\b"
)
MINIMALITY_RE = re.compile(
    r"""
    ^theorem\s+
    (?P<declaration>t(?P<name_t>\d+)_minimal_depth)
    \s*:\s*
    certifiedKill
    \s*\(\s*periodLcm\s+(?P<first_t>\d+)\s*\)
    \s*\(\s*periodLcm\s+(?P<second_t>\d+)\s*\)
    \s*(?P<depth>\d+)\s*∧\s*
    ∀\s+L\s*:\s*ℕ\s*,\s*
    L\s*<\s*(?P<bound>\d+)\s*→\s*¬\s*
    certifiedKill
    \s*\(\s*periodLcm\s+(?P<third_t>\d+)\s*\)
    \s*\(\s*periodLcm\s+(?P<fourth_t>\d+)\s*\)
    \s*L\s*:=
    """,
    re.MULTILINE | re.VERBOSE,
)

BAND_HEAD_RE = re.compile(
    rf"(?m)^theorem\s+exists_diagonalKill_le_{BAND_MAX_T}\b"
)
BAND_RE = re.compile(
    r"""
    ^theorem\s+
    (?P<declaration>exists_diagonalKill_le_(?P<name_max>\d+))
    \s*\(\s*t\s*:\s*ℕ\s*\)
    \s*\(\s*ht\s*:\s*t\s*≤\s*(?P<bound>\d+)\s*\)
    \s*:\s*
    ∃\s+L\s*,\s*
    certifiedKill
    \s*\(\s*periodLcm\s+t\s*\)
    \s*\(\s*periodLcm\s+t\s*\)
    \s+L\s*:=\s*by\b
    """,
    re.MULTILINE | re.VERBOSE,
)

DEPTH_FLOOR_HEAD_RE = re.compile(
    r"(?m)^theorem\s+certifiedKill_depth_floor\b"
)
DEPTH_FLOOR_RE = re.compile(
    r"""
    ^theorem\s+
    (?P<declaration>certifiedKill_depth_floor)
    \s*\{\s*h\s+N\s+L\s*:\s*ℕ\s*\}
    \s*\(\s*hcert\s*:\s*certifiedKill\s+h\s+N\s+L\s*\)
    \s*:\s*
    \(\s*2\s*\*\s*\(\s*N\s*\+\s*h\s*\+\s*L\s*\+\s*2\s*\)
    \s*:\s*ℤ\s*\)
    \s*<\s*2\s*\^\s*L\s*:=\s*by\b
    """,
    re.MULTILINE | re.VERBOSE,
)


class SourceContractError(ValueError):
    """Raised when a source theorem no longer matches the roster contract."""


def line_number(text: str, offset: int) -> int:
    """Return the one-based line containing ``offset``."""
    return text.count("\n", 0, offset) + 1


def lean_module(source_path: str) -> str:
    """Convert a relative Lean path to its import-module spelling."""
    path = Path(source_path)
    return ".".join(path.with_suffix("").parts)


def source_digest(text: str) -> str:
    """Return the full UTF-8 SHA-256 digest of a source."""
    return "sha256:" + sha256(text.encode("utf-8")).hexdigest()


def parse_certificate_declarations(
    text: str, source_path: str
) -> list[dict[str, object]]:
    """Parse and validate every named diagonal certificate in one source."""
    heads = list(CERTIFICATE_HEAD_RE.finditer(text))
    matches = list(CERTIFICATE_RE.finditer(text))
    if len(heads) != len(matches):
        raise SourceContractError(
            f"{source_path}: malformed diagonal certificate theorem "
            f"({len(heads)} heads, {len(matches)} valid signatures)"
        )

    records = []
    digest = source_digest(text)
    for match in matches:
        values = {
            int(match.group(name))
            for name in ("name_t", "first_t", "second_t")
        }
        if len(values) != 1:
            raise SourceContractError(
                f"{source_path}:{line_number(text, match.start())}: "
                "certificate theorem index does not match both periodLcm "
                "arguments"
            )
        t = values.pop()
        records.append(
            {
                "t": t,
                "depth": int(match.group("depth")),
                "provenance": {
                    "source_path": source_path,
                    "lean_module": lean_module(source_path),
                    "declaration": match.group("declaration"),
                    "line": line_number(text, match.start()),
                    "source_sha256": digest,
                },
            }
        )
    return records


def parse_minimality_declarations(
    text: str, source_path: str
) -> list[dict[str, object]]:
    """Parse exact least-depth statements, rejecting weakened signatures."""
    heads = list(MINIMALITY_HEAD_RE.finditer(text))
    matches = list(MINIMALITY_RE.finditer(text))
    if len(heads) != len(matches):
        raise SourceContractError(
            f"{source_path}: malformed least-depth theorem "
            f"({len(heads)} heads, {len(matches)} valid signatures)"
        )

    records = []
    digest = source_digest(text)
    for match in matches:
        t_values = {
            int(match.group(name))
            for name in (
                "name_t",
                "first_t",
                "second_t",
                "third_t",
                "fourth_t",
            )
        }
        depth_values = {
            int(match.group(name)) for name in ("depth", "bound")
        }
        if len(t_values) != 1 or len(depth_values) != 1:
            raise SourceContractError(
                f"{source_path}:{line_number(text, match.start())}: "
                "least-depth theorem does not use one index and one depth"
            )
        records.append(
            {
                "t": t_values.pop(),
                "depth": depth_values.pop(),
                "provenance": {
                    "source_path": source_path,
                    "lean_module": lean_module(source_path),
                    "declaration": match.group("declaration"),
                    "line": line_number(text, match.start()),
                    "source_sha256": digest,
                },
            }
        )
    return records


def parse_band_declaration(text: str, source_path: str) -> dict[str, object]:
    """Verify the exact unconditional source signature for the t <= 82 band."""
    heads = list(BAND_HEAD_RE.finditer(text))
    matches = [
        match
        for match in BAND_RE.finditer(text)
        if int(match.group("name_max")) == BAND_MAX_T
    ]
    if len(heads) != 1 or len(matches) != 1:
        raise SourceContractError(
            f"{source_path}: expected one exact "
            f"exists_diagonalKill_le_{BAND_MAX_T} theorem"
        )
    match = matches[0]
    if int(match.group("bound")) != BAND_MAX_T:
        raise SourceContractError(
            f"{source_path}: band theorem name and quantified bound disagree"
        )
    return {
        "source_path": source_path,
        "lean_module": lean_module(source_path),
        "declaration": match.group("declaration"),
        "line": line_number(text, match.start()),
        "source_sha256": source_digest(text),
    }


def parse_depth_floor_declaration(
    text: str, source_path: str
) -> dict[str, object]:
    """Verify the exact generic necessary depth-floor theorem signature."""
    heads = list(DEPTH_FLOOR_HEAD_RE.finditer(text))
    matches = list(DEPTH_FLOOR_RE.finditer(text))
    if len(heads) != 1 or len(matches) != 1:
        raise SourceContractError(
            f"{source_path}: expected the exact certifiedKill_depth_floor "
            "signature"
        )
    match = matches[0]
    return {
        "source_path": source_path,
        "lean_module": lean_module(source_path),
        "declaration": match.group("declaration"),
        "line": line_number(text, match.start()),
        "source_sha256": source_digest(text),
    }


def lcm_scale_rows(max_t: int = BAND_MAX_T) -> list[dict[str, int]]:
    """Return every distinct LCM scale and its maximal plateau through max_t."""
    if max_t < 1:
        raise ValueError("max_t must be positive")
    scale = 1
    changes = []
    previous_scale = None
    for t in range(1, max_t + 1):
        scale = lcm(scale, t)
        if scale != previous_scale:
            changes.append({"t": t, "period_lcm": scale})
            previous_scale = scale
    for index, row in enumerate(changes):
        row["plateau_max_t"] = (
            changes[index + 1]["t"] - 1
            if index + 1 < len(changes)
            else max_t
        )
    return changes


def admissible_depth_floor(period_lcm: int) -> int:
    """Least L >= 1 with room for a diagonal certificate at this scale."""
    if period_lcm < 0:
        raise ValueError("period_lcm must be nonnegative")
    depth = 1
    while (1 << depth) <= 2 * (2 * period_lcm + depth + 2):
        depth += 1
    return depth


def reduced_rational(numerator: int, denominator: int) -> dict[str, int]:
    """Return an exact rational in reduced form."""
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    divisor = gcd(abs(numerator), denominator)
    return {
        "numerator": numerator // divisor,
        "denominator": denominator // divisor,
    }


def exact_median(values: list[int]) -> dict[str, int]:
    """Return the exact median of a nonempty sorted integer sample."""
    ordered = sorted(values)
    if not ordered:
        raise ValueError("median of empty data")
    middle = len(ordered) // 2
    if len(ordered) % 2:
        return reduced_rational(ordered[middle], 1)
    return reduced_rational(ordered[middle - 1] + ordered[middle], 2)


def exact_distribution(values: Iterable[int]) -> dict[str, object]:
    """Return exact finite statistics with reduced rational proportions."""
    ordered = sorted(values)
    if not ordered:
        return {
            "sample_size": 0,
            "minimum": None,
            "median": None,
            "mean": None,
            "maximum": None,
            "distribution": [],
        }
    if ordered[0] < 0:
        raise ValueError("depth excess must be nonnegative")
    counts: dict[int, int] = {}
    for value in ordered:
        counts[value] = counts.get(value, 0) + 1
    size = len(ordered)
    return {
        "sample_size": size,
        "minimum": ordered[0],
        "median": exact_median(ordered),
        "mean": reduced_rational(sum(ordered), size),
        "maximum": ordered[-1],
        "distribution": [
            {
                "excess": value,
                "count": count,
                "proportion": reduced_rational(count, size),
            }
            for value, count in counts.items()
        ],
    }


def unique_by_t(
    records: Iterable[dict[str, object]], label: str
) -> dict[int, dict[str, object]]:
    """Index records by t, rejecting duplicate theorem ownership."""
    indexed: dict[int, dict[str, object]] = {}
    for record in records:
        t = int(record["t"])
        if t in indexed:
            raise SourceContractError(
                f"duplicate {label} declaration for t={t}"
            )
        indexed[t] = record
    return indexed


def validate_roster_indices(
    certificates: dict[int, dict[str, object]],
    minimalities: dict[int, dict[str, object]],
    max_t: int = BAND_MAX_T,
) -> list[dict[str, int]]:
    """Require exactly one certificate per distinct scale and sound minima."""
    scales = lcm_scale_rows(max_t)
    expected = [row["t"] for row in scales]
    actual = sorted(certificates)
    if actual != expected:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        raise SourceContractError(
            f"certificate roster mismatch: missing={missing}, extra={extra}"
        )
    if not set(minimalities).issubset(certificates):
        extra = sorted(set(minimalities) - set(certificates))
        raise SourceContractError(
            f"least-depth theorem without certificate: {extra}"
        )
    for t, minimum in minimalities.items():
        if int(minimum["depth"]) != int(certificates[t]["depth"]):
            raise SourceContractError(
                f"t={t}: least-depth theorem and certificate depth disagree"
            )
    return scales


def read_source(root: Path, source_path: str) -> str:
    """Read a required UTF-8 source or fail with a contract error."""
    path = root / source_path
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError as error:
        raise SourceContractError(
            f"required source is absent: {source_path}"
        ) from error


def build_measurement(root: Path = ROOT) -> dict[str, object]:
    """Extract the complete deterministic roster from current Lean sources."""
    certificate_records = []
    minimality_records = []
    inventory = []

    source_texts: dict[str, str] = {}
    for source_path in CERTIFICATE_SOURCE_PATHS:
        text = read_source(root, source_path)
        source_texts[source_path] = text
        certificates = parse_certificate_declarations(text, source_path)
        minimalities = parse_minimality_declarations(text, source_path)
        if not certificates:
            raise SourceContractError(
                f"{source_path}: canonical source has no diagonal certificate"
            )
        certificate_records.extend(certificates)
        minimality_records.extend(minimalities)
        inventory.append(
            {
                "source_path": source_path,
                "lean_module": lean_module(source_path),
                "bytes": len(text.encode("utf-8")),
                "source_sha256": source_digest(text),
                "certificate_declarations": len(certificates),
                "least_depth_declarations": len(minimalities),
            }
        )

    floor_text = read_source(root, DEPTH_FLOOR_SOURCE_PATH)
    floor_provenance = parse_depth_floor_declaration(
        floor_text, DEPTH_FLOOR_SOURCE_PATH
    )
    inventory.append(
        {
            "source_path": DEPTH_FLOOR_SOURCE_PATH,
            "lean_module": lean_module(DEPTH_FLOOR_SOURCE_PATH),
            "bytes": len(floor_text.encode("utf-8")),
            "source_sha256": source_digest(floor_text),
            "certificate_declarations": 0,
            "least_depth_declarations": 0,
        }
    )

    band_text = source_texts[BAND_SOURCE_PATH]
    band_provenance = parse_band_declaration(band_text, BAND_SOURCE_PATH)

    certificates = unique_by_t(certificate_records, "certificate")
    minimalities = unique_by_t(minimality_records, "least-depth")
    scales = validate_roster_indices(certificates, minimalities)

    rows = []
    for scale_row in scales:
        t = scale_row["t"]
        period = scale_row["period_lcm"]
        working_depth = int(certificates[t]["depth"])
        floor = admissible_depth_floor(period)
        working_excess = working_depth - floor
        if working_excess < 0:
            raise SourceContractError(
                f"t={t}: checked working depth precedes arithmetic floor"
            )

        minimum = minimalities.get(t)
        exact = minimum is not None
        rows.append(
            {
                "scale_index_t": t,
                "lcm_plateau_t": {
                    "minimum": t,
                    "maximum": scale_row["plateau_max_t"],
                },
                "period_lcm": period,
                "arithmetic_admissibility_floor": floor,
                "checked_working_depth": working_depth,
                "checked_working_depth_excess": working_excess,
                "checked_working_depth_excess_status": (
                    "proved_exact_least_depth_excess"
                    if exact
                    else "upper_bound_on_least_depth_excess"
                ),
                "proved_least_depth": working_depth if exact else None,
                "proved_least_depth_excess": (
                    working_excess if exact else None
                ),
                "least_depth_excess_upper_bound": (
                    None if exact else working_excess
                ),
                "provenance": {
                    "working_certificate": certificates[t]["provenance"],
                    "least_depth": (
                        minimum["provenance"] if minimum is not None else None
                    ),
                },
            }
        )

    exact_rows = [
        row for row in rows if row["proved_least_depth"] is not None
    ]
    working_only_rows = [
        row for row in rows if row["proved_least_depth"] is None
    ]
    all_working_excess = [
        int(row["checked_working_depth_excess"]) for row in rows
    ]
    exact_excess = [
        int(row["proved_least_depth_excess"]) for row in exact_rows
    ]
    upper_bounds = [
        int(row["least_depth_excess_upper_bound"])
        for row in working_only_rows
    ]

    return {
        "schema": "erdos249257-checked-diagonal-depth-roster/1",
        "artifact_role": "generated_source_backed_finite_measurement",
        "generator": "scripts/build_checked_diagonal_depth_roster.py",
        "question": (
            "What checked working depth is recorded at every distinct "
            "LCM-diagonal scale through t=82, and which depths are separately "
            "proved least?"
        ),
        "parameters": {
            "t": {"minimum": BAND_MIN_T, "maximum": BAND_MAX_T},
            "one_row_per": "distinct periodLcm scale",
            "admissibility_floor": (
                "min {L>=1 : 2^L > 2*(2*periodLcm(t)+L+2)}"
            ),
        },
        "source_contract": {
            "working_certificate_shape": (
                "certifiedKill (periodLcm t) (periodLcm t) L"
            ),
            "least_depth_shape": (
                "certifiedKill (periodLcm t) (periodLcm t) L and "
                "for every K<L, not certifiedKill "
                "(periodLcm t) (periodLcm t) K"
            ),
            "generic_depth_floor": floor_provenance,
            "continuous_band": band_provenance,
            "source_inventory": inventory,
        },
        "summary": {
            "covered_positive_t": BAND_MAX_T - BAND_MIN_T + 1,
            "distinct_lcm_scales": len(rows),
            "checked_working_depth_rows": len(rows),
            "proved_exact_least_depth_rows": len(exact_rows),
            "working_depth_only_rows": len(working_only_rows),
            "exact_least_depth_t": [
                row["scale_index_t"] for row in exact_rows
            ],
            "checked_working_depth_excess_all_rows": {
                "interpretation": (
                    "Exact on proved-least rows; otherwise only an upper "
                    "bound on least-depth excess."
                ),
                **exact_distribution(all_working_excess),
            },
            "proved_exact_least_depth_excess": exact_distribution(
                exact_excess
            ),
            "working_depth_only_excess_upper_bounds": exact_distribution(
                upper_bounds
            ),
        },
        "rows": rows,
        "limits": [
            (
                "The roster covers the finite positive band 1<=t<=82. It "
                "does not exhibit a certificate at t=83 or beyond."
            ),
            (
                "A checked working depth is not reported as least unless the "
                "listed Lean least-depth theorem excludes every smaller "
                "depth."
            ),
            (
                "On working-depth-only rows, working depth minus the "
                "arithmetic floor is only an upper bound on the unknown "
                "least-depth excess."
            ),
            (
                "The source extractor verifies current theorem signatures "
                "and hashes; it does not perform a separate proof build."
            ),
            (
                "Finite depth and excess distributions prove no asymptotic "
                "law, equidistribution, uniform excess bound, or cofinal "
                "certificate supply. Erdos #249 remains OPEN."
            ),
        ],
    }


def render_measurement(data: dict[str, object]) -> str:
    """Return the canonical deterministic JSON rendering."""
    return json.dumps(data, ensure_ascii=False, indent=1) + "\n"


def output_is_current(path: Path, rendered: str) -> bool:
    """Return whether ``path`` exists with exactly ``rendered`` contents."""
    try:
        return path.read_text(encoding="utf-8") == rendered
    except FileNotFoundError:
        return False


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--write",
        action="store_true",
        help=f"write {OUTPUT.relative_to(ROOT)}",
    )
    mode.add_argument(
        "--check",
        action="store_true",
        help="fail if the generated roster is absent, stale, or malformed",
    )
    args = parser.parse_args()

    try:
        data = build_measurement()
    except SourceContractError as error:
        print(
            f"build_checked_diagonal_depth_roster: {error}",
            file=sys.stderr,
        )
        return 2
    rendered = render_measurement(data)

    if args.write:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(rendered, encoding="utf-8")
        print(
            "build_checked_diagonal_depth_roster: wrote "
            f"{OUTPUT.relative_to(ROOT)}"
        )
        return 0
    if args.check:
        if not output_is_current(OUTPUT, rendered):
            print(
                "build_checked_diagonal_depth_roster: generated roster is "
                "stale",
                file=sys.stderr,
            )
            return 1
        print("build_checked_diagonal_depth_roster: current")
        return 0

    sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
