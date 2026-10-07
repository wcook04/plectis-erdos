#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Proposed check_ci_release leaf: regenerate independently and compare the register.

No previously built SQLite is trusted. The generated register is deliberately
excluded from its own source fingerprint to avoid a self-referential build loop.
"""
from pathlib import Path
import sys
import tempfile
import corpus_substrate as substrate


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    try:
        with tempfile.TemporaryDirectory(prefix="plectis-substrate-release-") as d:
            db = Path(d) / "corpus.sqlite"
            substrate.build(root, db)
            with substrate.View(root, db) as view:
                target = substrate.safe_file(root, "docs/reference/CORPUS_REGISTER.md")
                substrate.check_generated(view.register(), target.read_text(encoding="utf-8"))
                for p in view.rows("problem"):
                    card = view.frontier(p["id"])
                    if card["programme"]["record"]["id"] != p["record"]["claim_registration"]["programme_claim_id"]:
                        raise substrate.SubstrateError("programme/claim mismatch")
        print("corpus_substrate: complete registered source projection agrees")
        return 0
    except (OSError, ValueError, KeyError) as exc:
        print(f"corpus_substrate release: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
