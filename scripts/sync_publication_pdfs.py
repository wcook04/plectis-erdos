#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Copy Makefile PDF output into each artifact's storage_path."""

from __future__ import annotations

import json
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONTRACT = ROOT / "docs" / "publication_contract.json"
PAPER = ROOT / "paper"


def main() -> int:
    contract = json.loads(CONTRACT.read_text(encoding="utf-8"))
    for artifact in contract["artifacts"]:
        storage = Path(artifact["storage_path"])
        stem = Path(artifact["rendered_path"]).stem
        built = PAPER / f"{stem}.pdf"
        dest = ROOT / storage
        dest.parent.mkdir(parents=True, exist_ok=True)
        if built.is_file():
            shutil.copyfile(built, dest)
        elif not dest.is_file():
            print(f"missing PDF for {artifact['id']}: {built} and {dest}", file=sys.stderr)
            return 1
    print("publication PDFs synchronized to storage_path")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
