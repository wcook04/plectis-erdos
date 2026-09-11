#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the methodology guide from docs/methodology.json."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from methodology_contract import render_markdown, validate_contract


ROOT = Path(__file__).resolve().parent.parent
CLAIMS_PATH = ROOT / "docs" / "claims.json"
METHODOLOGY_PATH = ROOT / "docs" / "methodology.json"
OUTPUT = ROOT / "docs/METHODOLOGY.md"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the projection is stale")
    args = parser.parse_args()

    claims = json.loads(CLAIMS_PATH.read_text(encoding="utf-8"))
    methodology = json.loads(METHODOLOGY_PATH.read_text(encoding="utf-8"))
    errors = validate_contract(claims, methodology)
    if errors:
        print(f"methodology contract: {len(errors)} validation failure(s)")
        for error in errors:
            print(f"  FAIL {error}")
        return 1

    expected = render_markdown(methodology, claims)
    if args.check:
        actual = OUTPUT.read_text(encoding="utf-8") if OUTPUT.is_file() else ""
        if actual != expected:
            print("docs/METHODOLOGY.md is stale; run python3 scripts/build_methodology.py")
            return 1
        print("methodology projection current")
        return 0

    OUTPUT.write_text(expected, encoding="utf-8")
    print(f"wrote {OUTPUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
