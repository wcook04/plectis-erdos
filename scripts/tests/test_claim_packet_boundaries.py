#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Keep exact claim packets connected to their wider open-problem boundary."""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

from query_corpus import claim_packet


CASES = (
    (
        "eb_full_support",
        "structured_support_families",
        "remaining_open.universal_257_all_infinite_supports",
        "arbitrary infinite supports",
    ),
    (
        "certificate_reduction",
        "erdos249_certificate_story",
        "remaining_open.unbounded_certificate_supply",
        "unbounded",
    ),
)


def main() -> int:
    failures: list[str] = []
    for claim_id, route_id, open_id, ceiling_phrase in CASES:
        packet = claim_packet(claim_id)
        contexts = {
            row["id"]: row for row in packet.get("programme_contexts", [])
        }
        context = contexts.get(route_id)
        if context is None:
            failures.append(
                f"{claim_id}: missing programme context {route_id}"
            )
            continue
        if ceiling_phrase.casefold() not in context["claim_ceiling"].casefold():
            failures.append(
                f"{claim_id}: programme ceiling lost phrase {ceiling_phrase!r}"
            )
        visible_open_ids = {
            row["id"]
            for row in (
                packet["remaining_open_propositions"]
                + packet["wider_programme_open_propositions"]
            )
        }
        if open_id not in visible_open_ids:
            failures.append(
                f"{claim_id}: missing wider open proposition {open_id}"
            )
    if failures:
        print(f"test_claim_packet_boundaries: {len(failures)} failure(s)")
        for failure in failures:
            print(f"  FAIL {failure}")
        return 1
    print(
        "test_claim_packet_boundaries: exact claims preserve programme ceilings "
        "and wider open propositions"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
