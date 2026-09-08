#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Bounded entry packet retains every exact open boundary and progress edge."""
from pathlib import Path
from publication_contract import RepositoryReader, CLAIMS_PATH, load_json, build_publication_entry_packet, canonical_json_bytes, validate_publication_entry_packet


def test_entry_boundary_projection_is_exact_and_bounded():
    reader = RepositoryReader(Path(__file__).resolve().parent.parent)
    claims = load_json(reader, CLAIMS_PATH)
    packet = build_publication_entry_packet(reader)
    expected = [{k:v for k,v in row.items() if k not in {"paper_anchor", "additional_paper_anchors"}} for row in claims["remaining_open_propositions"]]
    assert packet["remaining_open_propositions"] == expected
    assert len(canonical_json_bytes(packet)) <= packet["packet_contract"]["max_bytes"]
    assert not validate_publication_entry_packet(reader, packet_override=packet)
    altered = dict(packet, remaining_open_propositions=expected[:-1])
    assert validate_publication_entry_packet(reader, packet_override=altered)


if __name__ == "__main__":
    test_entry_boundary_projection_is_exact_and_bounded()
    print("publication entry boundary and budget contracts passed")
