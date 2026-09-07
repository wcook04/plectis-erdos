#!/usr/bin/env python3
"""Bind the §16 dyadic Diophantine characterization to the canonical orbit.

Consumes the immutable packed 1/21 itinerary, reads the support word as the
binary number x = F(1/21), and evaluates the exact dyadic Diophantine slack

    slack_n = 3 * 4^n * dist(x, nearest odd a / 2^n)

for every n up to a fixed depth, together with the forward opposite-run
length R_n of §1 (maximal run of (1 - b_n) starting at position n + 1).

Exact word algebra gives the bracket, for b_n in {0, 1}:

    3 * 2^(n - R_n - 1) <= slack_n < 3 * 2^(n - R_n),

so death at rank n (slack_n < 1) forces R_n >= n + 2: survival is exactly the
combinatorial statement that no forward opposite-run ever reaches length
n + 2.  This script verifies the bracket and the slack >= 1 law bit-exactly
on the certified orbit and maps the near-edge (n, R_n) profile that an
all-depth proof must control.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import math
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[3]
SOURCE_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_computational_structure_receipt_2000002_v1.json"
)
RECEIPT_REF = (
    "state/formal_math/erdos257_period_noncollapse/"
    "twenty_one_parity_characterization_binding_receipt.json"
)
DEFAULT_RECEIPT = REPO_ROOT / RECEIPT_REF
CHECK_DEPTH = 3000
RUN_CAP = 256
PROFILE_ROWS = 48


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def canonical_payload_sha256(payload: dict[str, Any]) -> str:
    body = {
        k: v
        for k, v in payload.items()
        if k != "canonical_payload_sha256"
    }
    return hashlib.sha256(canonical_json(body).encode("utf-8")).hexdigest()


def validate_payload_digest(source: dict[str, Any]) -> str:
    for field in ("canonical_payload_sha256", "receipt_payload_sha256"):
        if field in source:
            body = {
                k: v for k, v in source.items() if k != field
            }
            computed = hashlib.sha256(
                canonical_json(body).encode("utf-8")
            ).hexdigest()
            if computed != source[field]:
                raise AssertionError("source payload digest mismatch")
            return field
    raise AssertionError("source receipt has no canonical payload digest")


def build_receipt(source_path: Path) -> dict[str, Any]:
    source = json.loads(source_path.read_text())
    digest_field = validate_payload_digest(source)
    if source["schema"] != "twenty_one_computational_structure_lab_v1":
        raise AssertionError("packed-itinerary source is not schema v1")
    packed_metadata = source["packed_itinerary"]
    packed = base64.b64decode(packed_metadata["data_base64"])
    if hashlib.sha256(packed).hexdigest() != packed_metadata["sha256"]:
        raise AssertionError("packed-itinerary digest mismatch")

    ranks = int(source["parameters"]["ranks"])
    bits = bytearray(ranks + 1)
    for rank in range(1, ranks + 1):
        bits[rank] = (packed[(rank - 1) // 8] >> ((rank - 1) % 8)) & 1
    if sum(bits) != int(source["selected_count"]):
        raise AssertionError("decoded selected count mismatch")

    exact_value = 0
    for rank in range(1, ranks + 1):
        exact_value = (exact_value << 1) | bits[rank]
    scale = 1 << ranks

    def forward_run(n: int) -> int:
        opposite = 1 - bits[n]
        length = 0
        position = n + 1
        while position <= ranks and bits[position] == opposite:
            length += 1
            position += 1
            if length >= RUN_CAP:
                break
        return length

    survival_violations: list[dict[str, Any]] = []
    bracket_violations: list[dict[str, Any]] = []
    run_cap_hits: list[int] = []
    slack_rows: list[dict[str, Any]] = []
    minimum_log2_slack = None
    minimum_slack_rows: list[dict[str, Any]] = []

    for n in range(1, CHECK_DEPTH + 1):
        floor_y = (exact_value << n) // scale
        best_distance = None
        best_candidate = None
        for candidate in range(floor_y - 1, floor_y + 3):
            if candidate <= 0 or candidate % 2 == 0:
                continue
            distance = abs((exact_value << n) - candidate * scale)
            if best_distance is None or distance < best_distance:
                best_distance = distance
                best_candidate = candidate
        if best_distance is None:
            raise AssertionError(f"no odd dyadic candidate at n={n}")

        # dist = best_distance / (scale * 2^n), so
        # slack_n = 3*4^n*dist = 3*2^n*best_distance/scale.
        slack_numerator = 3 * (1 << n) * best_distance
        if slack_numerator < scale:
            survival_violations.append(
                {
                    "rank": n,
                    "nearest_odd_numerator": best_candidate,
                    "slack_numerator": slack_numerator,
                    "slack_denominator": scale,
                }
            )

        run_length = forward_run(n)
        if run_length >= RUN_CAP:
            run_cap_hits.append(n)

        def below_power(base: int, exponent: int) -> bool:
            if exponent >= 0:
                return slack_numerator < (base << exponent)
            return (slack_numerator << (-exponent)) < base

        in_upper_bracket = below_power(
            3 * scale, n - run_length
        )
        in_lower_bracket = not below_power(
            3 * scale, n - run_length - 1
        )
        if not (in_lower_bracket and in_upper_bracket):
            bracket_violations.append(
                {
                    "rank": n,
                    "forward_run_length": run_length,
                    "bracket_lower_satisfied": in_lower_bracket,
                    "bracket_upper_satisfied": in_upper_bracket,
                }
            )

        log2_slack = (
            math.log2(3)
            + n
            + math.log2(best_distance)
            - ranks
        )
        row = {
            "rank": n,
            "nearest_odd_numerator": best_candidate,
            "forward_run_length": run_length,
            "log2_slack": log2_slack,
            "predicted_log2_slack_upper": (
                math.log2(3) + (n - run_length)
            ),
        }
        if n <= 96 or len(slack_rows) < 4096 and log2_slack < 8.0:
            slack_rows.append(row)
        if minimum_log2_slack is None or log2_slack < minimum_log2_slack:
            minimum_log2_slack = log2_slack
            minimum_slack_rows = [row]
        elif (
            log2_slack == minimum_log2_slack
            and len(minimum_slack_rows) < 64
        ):
            minimum_slack_rows.append(row)

    near_edge_profile = sorted(slack_rows, key=lambda r: r["log2_slack"])[
        :PROFILE_ROWS
    ]

    payload: dict[str, Any] = {
        "schema": "twenty_one_parity_characterization_binding_v1",
        "authority": {
            "projection_not_authority": (
                "This receipt binds the RunLengthMarginLawAndDivisorMultiplicity"
                ".md section 16 characterization to the canonical orbit; the "
                "analytic statement and the margin law live in that note, and "
                "the canonical itinerary remains owned by its builder."
            ),
            "source_receipt": str(
                source_path.relative_to(REPO_ROOT)
            ),
            "source_schema": source["schema"],
            "source_payload_digest_field": digest_field,
            "source_canonical_payload_sha256": source[digest_field],
            "packed_itinerary_sha256": packed_metadata["sha256"],
        },
        "parameters": {
            "ranks": ranks,
            "check_depth": CHECK_DEPTH,
            "run_cap": RUN_CAP,
        },
        "characterization": {
            "statement": (
                "y survives forever iff |x - a/2^n| >= (1/3)*4^-n for every "
                "n and odd a, with x the support word read as a binary number"
            ),
            "slack_definition": (
                "slack_n = 3*4^n*dist(x, nearest odd a/2^n); survival "
                "requires slack_n >= 1"
            ),
            "exact_run_bracket": (
                "3*2^(n-R_n-1) <= slack_n < 3*2^(n-R_n) with R_n the "
                "maximal run of (1-b_n) starting at n+1, so slack_n < 1 "
                "forces R_n >= n+2"
            ),
        },
        "results": {
            "tested_rank_count": CHECK_DEPTH,
            "survival_violation_count": len(survival_violations),
            "survival_violations": survival_violations,
            "run_bracket_violation_count": len(bracket_violations),
            "run_bracket_violations": bracket_violations,
            "run_cap_hit_ranks": run_cap_hits,
            "minimum_log2_slack": minimum_log2_slack,
            "minimum_slack_rows": minimum_slack_rows,
            "near_edge_profile_by_log2_slack": near_edge_profile,
        },
        "nonclaims": [
            "Finite-depth binding of an analytic characterization; this is "
            "not a survival proof and does not decide Erdos Problem 257.",
            "The near-edge profile maps where an all-depth proof must work; "
            "it does not certify any bound beyond the tested depth.",
        ],
    }
    payload["canonical_payload_sha256"] = canonical_payload_sha256(payload)
    return payload


def resolve_path(value: str | None) -> Path:
    if value is None:
        return DEFAULT_RECEIPT
    path = Path(value)
    return path if path.is_absolute() else REPO_ROOT / path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", default=str(SOURCE_REF))
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--write", nargs="?", const=None, metavar="PATH")
    action.add_argument("--check", nargs="?", const=None, metavar="PATH")
    args = parser.parse_args()
    import sys

    payload = build_receipt(REPO_ROOT / args.source)
    rendered = canonical_json(payload)
    if args.write is not None or "--write" in sys.argv:
        path = resolve_path(args.write)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(rendered)
        print(
            canonical_json(
                {
                    "status": "written",
                    "path": str(path.relative_to(REPO_ROOT)),
                    "canonical_payload_sha256": payload[
                        "canonical_payload_sha256"
                    ],
                }
            ),
            end="",
        )
        return 0
    if args.check is not None or "--check" in sys.argv:
        path = resolve_path(args.check)
        if path.read_text() != rendered:
            raise AssertionError(f"receipt drift: {path}")
        print(
            canonical_json(
                {
                    "status": "matched",
                    "path": str(path.relative_to(REPO_ROOT)),
                    "canonical_payload_sha256": payload[
                        "canonical_payload_sha256"
                    ],
                }
            ),
            end="",
        )
        return 0
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
