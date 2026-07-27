#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the bounded historical roster of off-diagonal Lean certificates.

The source log stores certificate parameters as fields ``N``, ``h``, ``L``.
The public Lean predicate takes them in the different order
``certifiedKill h N L``.  This builder keeps that distinction explicit and
accepts a selected source row only when its exact triple occurs in a public
theorem signature in the named Lean file.

The roster reproduces the finite audit recorded by semantic zone Z27.  Its
upper position is deliberately historical: verified rows above that position
remain visible as an excluded census, but do not silently enlarge the audited
roster.

Usage:

    python3 scripts/build_off_diagonal_certificate_roster.py
    python3 scripts/build_off_diagonal_certificate_roster.py --write
    python3 scripts/build_off_diagonal_certificate_roster.py --check
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
DATA_PATH = ROOT / "ErdosProblems" / "FreePosition" / "data.jsonl"
ZONE_PATH = ROOT / "docs" / "semantic" / "zones" / "Z27.json"
OUTPUT = (
    ROOT
    / "docs"
    / "measurements"
    / "off_diagonal_certificate_roster.json"
)

HISTORICAL_AUDIT_CUTOFF_N = 135960691671824579163806583999
AUDIT_NODE_ID = "free_position_finite_certificates"

PUBLIC_CERTIFIED_KILL_RE = re.compile(
    r"(?m)^[ \t]*theorem[ \t]+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)[ \t]*"
    r":[ \t\r\n]*certifiedKill[ \t\r\n]+"
    r"(?P<h>[0-9][0-9_]*)[ \t\r\n]+"
    r"(?P<N>[0-9][0-9_]*)[ \t\r\n]+"
    r"(?P<L>[0-9][0-9_]*)[ \t\r\n]*:="
)


class RosterError(ValueError):
    """Raised when a source row cannot be bound to its claimed Lean theorem."""


def sha256_bytes(payload: bytes) -> str:
    """Return a lowercase SHA-256 digest."""
    return hashlib.sha256(payload).hexdigest()


def _relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def _lean_numeral(text: str) -> int:
    return int(text.replace("_", ""))


def _exact_int(record: dict[str, Any], field: str, source_row: int) -> int:
    value = record.get(field)
    if isinstance(value, bool) or not isinstance(value, int):
        raise RosterError(
            f"data.jsonl row {source_row}: {field} must be an integer"
        )
    return value


def _certificate_id(h: int, N: int, L: int) -> str:
    return f"certifiedKill:h={h}:N={N}:L={L}"


def read_jsonl_rows(
    path: Path = DATA_PATH,
) -> list[dict[str, Any]]:
    """Read JSON objects while retaining physical row numbers and line hashes."""
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for source_row, raw_line in enumerate(handle, start=1):
            line = raw_line.rstrip("\r\n")
            if not line.strip():
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as error:
                raise RosterError(
                    f"{_relative(path)} row {source_row}: invalid JSON: {error}"
                ) from error
            if not isinstance(record, dict):
                raise RosterError(
                    f"{_relative(path)} row {source_row}: expected an object"
                )
            rows.append(
                {
                    "source_row": source_row,
                    "source_line_sha256": sha256_bytes(
                        line.encode("utf-8")
                    ),
                    "record": record,
                }
            )
    return rows


def _is_verified_kill(row: dict[str, Any]) -> bool:
    record = row["record"]
    return (
        record.get("lean_verified") is True
        and record.get("kill") is True
    )


def select_historical_rows(
    rows: Iterable[dict[str, Any]],
    cutoff_N: int = HISTORICAL_AUDIT_CUTOFF_N,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Partition verified kills at or below the cutoff from later ones."""
    selected: list[dict[str, Any]] = []
    excluded_later: list[dict[str, Any]] = []
    for row in rows:
        if not _is_verified_kill(row):
            continue
        source_row = int(row["source_row"])
        N = _exact_int(row["record"], "N", source_row)
        if N <= cutoff_N:
            selected.append(row)
        else:
            excluded_later.append(row)
    return selected, excluded_later


def extract_public_certified_kills(
    source_text: str,
    source_path: str,
) -> list[dict[str, Any]]:
    """Extract literal public ``certifiedKill h N L`` theorem signatures."""
    signatures: list[dict[str, Any]] = []
    for match in PUBLIC_CERTIFIED_KILL_RE.finditer(source_text):
        h = _lean_numeral(match.group("h"))
        N = _lean_numeral(match.group("N"))
        L = _lean_numeral(match.group("L"))
        line = source_text.count("\n", 0, match.start()) + 1
        signatures.append(
            {
                "declaration": match.group("name"),
                "file": source_path,
                "line": line,
                "predicate": "certifiedKill",
                "argument_order": ["h", "N", "L"],
                "arguments": {"h": h, "N": N, "L": L},
                "signature": f"certifiedKill {h} {N} {L}",
            }
        )
    return signatures


def _validated_row_key(row: dict[str, Any]) -> tuple[int, int, int, str]:
    source_row = int(row["source_row"])
    record = row["record"]
    h = _exact_int(record, "h", source_row)
    N = _exact_int(record, "N", source_row)
    L = _exact_int(record, "L", source_row)
    file_value = record.get("file")
    if not isinstance(file_value, str) or not file_value:
        raise RosterError(
            f"data.jsonl row {source_row}: selected row has no Lean file"
        )
    if h <= 0 or N < 0 or L <= 0:
        raise RosterError(
            f"data.jsonl row {source_row}: require h>0, N>=0, and L>0"
        )
    return h, N, L, file_value


def _resolve_source_path(source_file: str, source_row: int) -> Path:
    relative_path = Path(source_file)
    if relative_path.is_absolute():
        raise RosterError(
            f"data.jsonl row {source_row}: Lean file must be relative"
        )
    resolved_root = ROOT.resolve()
    resolved = (ROOT / relative_path).resolve()
    if not resolved.is_relative_to(resolved_root):
        raise RosterError(
            f"data.jsonl row {source_row}: Lean file escapes repository"
        )
    if not resolved.is_file():
        raise RosterError(
            f"data.jsonl row {source_row}: Lean file does not exist: "
            f"{source_file}"
        )
    return resolved


def bind_rows_to_public_theorems(
    selected_rows: Iterable[dict[str, Any]],
) -> tuple[
    list[dict[str, Any]],
    dict[tuple[int, int, int], list[dict[str, Any]]],
    dict[str, str],
]:
    """Validate every selected triple and return theorem-bound source rows."""
    row_list = list(selected_rows)
    source_cache: dict[str, tuple[list[dict[str, Any]], str]] = {}
    bound_rows: list[dict[str, Any]] = []
    grouped: dict[
        tuple[int, int, int], list[dict[str, Any]]
    ] = defaultdict(list)

    for row in row_list:
        source_row = int(row["source_row"])
        h, N, L, source_file = _validated_row_key(row)
        if source_file not in source_cache:
            source_path = _resolve_source_path(source_file, source_row)
            source_bytes = source_path.read_bytes()
            source_text = source_bytes.decode("utf-8")
            source_cache[source_file] = (
                extract_public_certified_kills(source_text, source_file),
                sha256_bytes(source_bytes),
            )

        signatures, source_digest = source_cache[source_file]
        matches = [
            signature
            for signature in signatures
            if (
                signature["arguments"]["h"],
                signature["arguments"]["N"],
                signature["arguments"]["L"],
            )
            == (h, N, L)
        ]
        if len(matches) != 1:
            raise RosterError(
                f"data.jsonl row {source_row}: expected exactly one public "
                f"certifiedKill {h} {N} {L} theorem in {source_file}, "
                f"found {len(matches)}"
            )

        theorem = dict(matches[0])
        theorem["source_sha256"] = source_digest
        theorem_ref = (
            f"{source_file}:{theorem['line']}#{theorem['declaration']}"
        )
        bound = {
            "source_row": source_row,
            "source_line_sha256": row["source_line_sha256"],
            "certificate_id": _certificate_id(h, N, L),
            "theorem_ref": theorem_ref,
            "record": row["record"],
            "_theorem": theorem,
        }
        bound_rows.append(bound)
        grouped[(h, N, L)].append(bound)

    return (
        bound_rows,
        grouped,
        {
            source_file: source_digest
            for source_file, (_, source_digest) in source_cache.items()
        },
    )


def _unique_theorems(rows: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    by_ref: dict[str, dict[str, Any]] = {}
    for row in rows:
        by_ref[row["theorem_ref"]] = row["_theorem"]
    return [by_ref[ref] for ref in sorted(by_ref)]


def _source_row_projection(row: dict[str, Any]) -> dict[str, Any]:
    return {
        key: row[key]
        for key in (
            "source_row",
            "source_line_sha256",
            "certificate_id",
            "theorem_ref",
            "record",
        )
    }


def _distinct_certificate_roster(
    grouped: dict[tuple[int, int, int], list[dict[str, Any]]],
) -> list[dict[str, Any]]:
    ordered_groups = sorted(
        grouped.items(),
        key=lambda item: min(
            int(row["source_row"]) for row in item[1]
        ),
    )
    roster: list[dict[str, Any]] = []
    for (h, N, L), rows in ordered_groups:
        roster.append(
            {
                "certificate_id": _certificate_id(h, N, L),
                "h": h,
                "N": N,
                "L": L,
                "source_rows": [
                    int(row["source_row"]) for row in rows
                ],
                "source_files": sorted(
                    {str(row["record"]["file"]) for row in rows}
                ),
                "theorems": _unique_theorems(rows),
            }
        )
    return roster


def _duplicate_groups(
    grouped: dict[tuple[int, int, int], list[dict[str, Any]]],
) -> list[dict[str, Any]]:
    duplicate_items = [
        (triple, rows)
        for triple, rows in grouped.items()
        if len(rows) > 1
    ]
    duplicate_items.sort(
        key=lambda item: min(
            int(row["source_row"]) for row in item[1]
        )
    )
    groups: list[dict[str, Any]] = []
    for (h, N, L), rows in duplicate_items:
        groups.append(
            {
                "certificate_id": _certificate_id(h, N, L),
                "duplicate_key": {"h": h, "N": N, "L": L},
                "row_count": len(rows),
                "excess_row_count": len(rows) - 1,
                "source_rows": [
                    int(row["source_row"]) for row in rows
                ],
                "source_line_sha256s": [
                    str(row["source_line_sha256"]) for row in rows
                ],
                "source_files": sorted(
                    {str(row["record"]["file"]) for row in rows}
                ),
                "theorem_refs": sorted(
                    {str(row["theorem_ref"]) for row in rows}
                ),
            }
        )
    return groups


def _excluded_later_summary(
    rows: list[dict[str, Any]],
) -> dict[str, Any]:
    triples: set[tuple[int, int, int]] = set()
    files: set[str] = set()
    positions: list[int] = []
    source_rows: list[int] = []
    for row in rows:
        source_row = int(row["source_row"])
        record = row["record"]
        h = _exact_int(record, "h", source_row)
        N = _exact_int(record, "N", source_row)
        L = _exact_int(record, "L", source_row)
        file_value = record.get("file")
        if not isinstance(file_value, str) or not file_value:
            raise RosterError(
                f"data.jsonl row {source_row}: later verified row has no file"
            )
        triples.add((h, N, L))
        files.add(file_value)
        positions.append(N)
        source_rows.append(source_row)
    return {
        "policy": (
            "Verified kill rows with N above the historical Z27 cutoff are "
            "excluded from this roster; later verified files do not silently "
            "change the bounded historical audit."
        ),
        "selection": (
            "lean_verified is true and kill is true and "
            f"N > {HISTORICAL_AUDIT_CUTOFF_N}"
        ),
        "row_count": len(rows),
        "distinct_h_N_L_certificate_count": len(triples),
        "distinct_file_count": len(files),
        "minimum_N": min(positions) if positions else None,
        "maximum_N": max(positions) if positions else None,
        "first_source_row": min(source_rows) if source_rows else None,
        "last_source_row": max(source_rows) if source_rows else None,
        "files": sorted(files),
    }


def build_roster() -> dict[str, Any]:
    """Re-derive the complete deterministic historical roster."""
    data_bytes = DATA_PATH.read_bytes()
    all_rows = read_jsonl_rows(DATA_PATH)
    selected_rows, excluded_later = select_historical_rows(all_rows)
    bound_rows, grouped, file_digests = bind_rows_to_public_theorems(
        selected_rows
    )
    certificates = _distinct_certificate_roster(grouped)
    duplicates = _duplicate_groups(grouped)
    distinct_theorem_refs = {
        row["theorem_ref"] for row in bound_rows
    }
    selected_positions = [
        int(row["record"]["N"]) for row in bound_rows
    ]
    diagonal = [
        (h, N, L) for h, N, L in grouped if h == N
    ]
    if diagonal:
        raise RosterError(
            "historical off-diagonal roster contains diagonal triples: "
            f"{diagonal}"
        )
    maximum_selected_N = (
        max(selected_positions) if selected_positions else None
    )
    maximum_certificates = [
        {
            "h": certificate["h"],
            "N": certificate["N"],
            "L": certificate["L"],
            "theorem_refs": [
                (
                    f"{theorem['file']}:{theorem['line']}"
                    f"#{theorem['declaration']}"
                )
                for theorem in certificate["theorems"]
            ],
        }
        for certificate in certificates
        if certificate["N"] == maximum_selected_N
    ]

    return {
        "schema": "erdos249257-off-diagonal-certificate-roster/1",
        "artifact_role": "generated_bounded_historical_audit",
        "generator": "scripts/build_off_diagonal_certificate_roster.py",
        "spdx_file_copyright_text": "2026 Will Cook",
        "spdx_license_identifier": "Apache-2.0",
        "question": (
            "Which data.jsonl rows belong to the historical Z27 audit of "
            "finite off-diagonal certifiedKill instances, and which exact "
            "public Lean theorem checks each distinct certificate?"
        ),
        "parameter_contract": {
            "data_field_order": ["N", "h", "L"],
            "lean_certifiedKill_argument_order": ["h", "N", "L"],
            "certificate_identity": ["h", "N", "L"],
            "selection": (
                "lean_verified is true and kill is true and "
                f"N <= {HISTORICAL_AUDIT_CUTOFF_N}"
            ),
            "historical_cutoff_N": HISTORICAL_AUDIT_CUTOFF_N,
            "duplicate_policy": (
                "Retain every selected physical source row; collapse only "
                "the distinct-certificate roster by the exact (h,N,L) key."
            ),
        },
        "inputs": {
            "data_jsonl": {
                "path": _relative(DATA_PATH),
                "sha256": sha256_bytes(data_bytes),
                "physical_line_count": len(
                    DATA_PATH.read_text(encoding="utf-8").splitlines()
                ),
            },
        },
        "projection_contract": {
            "consumer": (
                "docs/semantic/zones/Z27.json::"
                "free_position_finite_certificates"
            ),
            "owner": (
                "docs/measurements/"
                "off_diagonal_certificate_roster.json"
            ),
            "builder": (
                "scripts/build_expansion_semantic_zones.py"
            ),
            "rule": (
                "Public prose must distinguish selected source rows from "
                "distinct (h,N,L) certificates and must retain the finite, "
                "historically bounded scope."
            ),
        },
        "counts": {
            "row_count": len(bound_rows),
            "distinct_h_N_L_certificate_count": len(grouped),
            "distinct_file_count": len(file_digests),
            "distinct_public_theorem_reference_count": len(
                distinct_theorem_refs
            ),
            "duplicate_group_count": len(duplicates),
            "duplicate_row_count": sum(
                int(group["row_count"]) for group in duplicates
            ),
            "duplicate_excess_row_count": sum(
                int(group["excess_row_count"]) for group in duplicates
            ),
        },
        "boundary_observation": {
            "maximum_selected_N": maximum_selected_N,
            "source_rows_at_maximum_N": [
                int(row["source_row"])
                for row in bound_rows
                if int(row["record"]["N"]) == maximum_selected_N
            ] if selected_positions else [],
            "certificates_at_maximum_N": maximum_certificates,
        },
        "lean_files": [
            {"file": source_file, "sha256": file_digests[source_file]}
            for source_file in sorted(file_digests)
        ],
        "duplicate_certificate_groups": duplicates,
        "distinct_certificates": certificates,
        "source_rows": [
            _source_row_projection(row) for row in bound_rows
        ],
        "excluded_later_verified_rows": _excluded_later_summary(
            excluded_later
        ),
        "limits": [
            (
                "Every roster entry is one finite checked instance; no "
                "finite roster supplies the cofinal statement needed for "
                "Erdos #249."
            ),
            (
                "The roster is bounded by the historical Z27 position cutoff, "
                "not by the current end of data.jsonl."
            ),
            (
                "The counts distinguish physical data rows, distinct "
                "(h,N,L) certificates, public theorem references, and files."
            ),
        ],
    }


def public_projection_statement(data: dict[str, Any]) -> str:
    """Render the exact finite-result sentence consumed by semantic zone Z27."""
    counts = data["counts"]
    boundary = data["boundary_observation"]
    maximum = boundary["certificates_at_maximum_N"]
    if len(maximum) != 1:
        raise RosterError(
            "expected exactly one certificate at the historical maximum N"
        )
    return (
        "PROVED: each of the "
        f"{counts['distinct_h_N_L_certificate_count']} distinct "
        "(h,N,L) triples in the bounded historical roster is matched to "
        "a public theorem of type certifiedKill h N L. The source log has "
        f"{counts['row_count']} selected verification rows because "
        f"{counts['duplicate_excess_row_count']} rows duplicate an already "
        f"listed triple; the roster spans {counts['distinct_file_count']} "
        "Lean files. Its largest audited position is "
        f"{boundary['maximum_selected_N']} at depth {maximum[0]['L']}."
    )


def public_projection_scope_caveat(data: dict[str, Any]) -> str:
    """Render the finite and historical boundary consumed by semantic zone Z27."""
    later = data["excluded_later_verified_rows"]
    return (
        "These are finite instances. They do not provide the all-position "
        "or cofinal supply required by the #249 reductions. The artifact "
        f"separately counts {later['row_count']} later verified certificate "
        "triples above the historical position cutoff; they are not silently "
        "added to this bounded roster."
    )


def validate_zone_projection(
    data: dict[str, Any],
    zone_path: Path = ZONE_PATH,
) -> list[str]:
    """Return drift errors for the generated Z27 public projection."""
    zone = json.loads(zone_path.read_text(encoding="utf-8"))
    nodes = [
        node
        for node in zone.get("statement_nodes", [])
        if node.get("id") == AUDIT_NODE_ID
    ]
    if len(nodes) != 1:
        return [
            f"{_relative(zone_path)}: expected one {AUDIT_NODE_ID} node"
        ]
    node = nodes[0]
    errors = []
    expected_statement = public_projection_statement(data)
    expected_caveat = public_projection_scope_caveat(data)
    if node.get("canonical_statement") != expected_statement:
        errors.append(
            f"{_relative(zone_path)}: canonical statement is stale"
        )
    if node.get("scope_caveat") != expected_caveat:
        errors.append(
            f"{_relative(zone_path)}: scope caveat is stale"
        )
    return errors


def render_roster(data: dict[str, Any]) -> str:
    """Return the canonical JSON representation used by all modes."""
    return json.dumps(data, ensure_ascii=False, indent=1) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--write",
        action="store_true",
        help=f"write {_relative(OUTPUT)}",
    )
    mode.add_argument(
        "--check",
        action="store_true",
        help="fail when the generated roster is absent or stale",
    )
    args = parser.parse_args()

    try:
        rendered = render_roster(build_roster())
    except (OSError, UnicodeError, json.JSONDecodeError, RosterError) as error:
        print(
            f"build_off_diagonal_certificate_roster: {error}",
            file=sys.stderr,
        )
        return 1

    if args.write:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(rendered, encoding="utf-8")
        print(
            "build_off_diagonal_certificate_roster: wrote "
            f"{_relative(OUTPUT)}"
        )
        return 0
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text(
            encoding="utf-8"
        ) != rendered:
            print(
                "build_off_diagonal_certificate_roster: generated roster "
                "is absent or stale",
                file=sys.stderr,
            )
            return 1
        projection_errors = validate_zone_projection(
            json.loads(rendered)
        )
        if projection_errors:
            for error in projection_errors:
                print(
                    f"build_off_diagonal_certificate_roster: {error}",
                    file=sys.stderr,
                )
            return 1
        print("build_off_diagonal_certificate_roster: current")
        return 0

    sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
