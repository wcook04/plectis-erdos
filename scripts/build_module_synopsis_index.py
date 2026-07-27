#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the source-header synopsis index used by semantic corpus queries."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
ATLAS = ROOT / "docs" / "declaration_atlas.json"
OUTPUT = ROOT / "docs" / "module_synopsis_index.json"
SCHEMA = "erdos249257-module-synopsis-index/1"


def extract_synopsis(path: Path) -> str | None:
    with path.open(encoding="utf-8") as source:
        prefix = source.read(64_000)
    match = re.search(r"/-!(.*?)-/", prefix, re.S)
    if match is None:
        return None
    lines = []
    for raw in match.group(1).splitlines():
        line = raw.strip()
        if line.startswith("#"):
            line = line.lstrip("#").strip()
        lines.append(line)
    synopsis = re.sub(r"\s+", " ", " ".join(lines)).strip()
    return synopsis[:1600] or None


def build() -> dict[str, Any]:
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    modules = []
    for module in atlas["modules"]:
        synopsis = extract_synopsis(ROOT / module["path"])
        modules.append(
            {
                "id": module["id"],
                "path": module["path"],
                "synopsis": synopsis,
            }
        )
    return {
        "schema_version": SCHEMA,
        "authority_posture": (
            "generated_index_of_authored_Lean_module_headers_not_proof_or_claim_status_authority"
        ),
        "source_fingerprint": atlas["source_fingerprint"],
        "module_count": len(modules),
        "synopsis_count": sum(bool(row["synopsis"]) for row in modules),
        "modules": modules,
        "freshness_contract": {
            "source_owner": "Lean /-! ... -/ module headers",
            "source_fingerprint_owner": "docs/declaration_atlas.json",
            "rebuild": "python3 scripts/build_module_synopsis_index.py",
            "check": (
                "python3 scripts/build_declaration_atlas.py --check && "
                "python3 scripts/build_module_synopsis_index.py --check"
            ),
        },
    }


def render(packet: dict[str, Any]) -> str:
    return json.dumps(packet, ensure_ascii=False, indent=2) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    if args.check:
        if not OUTPUT.is_file():
            print("module synopsis index missing; run builder")
            return 1
        packet = json.loads(OUTPUT.read_text(encoding="utf-8"))
        expected_paths = {row["path"] for row in atlas["modules"]}
        actual_paths = {row["path"] for row in packet.get("modules", [])}
        failures = []
        if packet.get("schema_version") != SCHEMA:
            failures.append("schema")
        if packet.get("source_fingerprint") != atlas.get("source_fingerprint"):
            failures.append("source_fingerprint")
        if expected_paths != actual_paths:
            failures.append("module_inventory")
        if failures:
            print(
                "module synopsis index stale: "
                + ",".join(failures)
                + "; run builder"
            )
            return 1
        print(
            "module synopsis index current: "
            f"{packet['synopsis_count']}/{packet['module_count']} modules"
        )
        return 0
    packet = build()
    OUTPUT.write_text(render(packet), encoding="utf-8")
    print(
        f"wrote {OUTPUT.relative_to(ROOT)}: "
        f"{packet['synopsis_count']}/{packet['module_count']} modules"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
