#!/usr/bin/env python3
"""Validate the standalone compact agent-entry contract."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
COMPACT = ROOT / "AGENTS.override.md"


def main() -> int:
    text = COMPACT.read_text(encoding="utf-8")
    encoded = text.encode("utf-8")

    assert len(encoded) < 8_000, len(encoded)
    for required in (
        'query_corpus.py --ask "<question>"',
        "query_corpus.py --overview",
        "--route instant_orientation",
        "--route erdos249_certificate_story",
        "--route erdos257_half_story",
        "--route browse_claim_status",
        'query_corpus.py --goal-support "<Lean or mathematical goal>"',
        "check_cold_clone_comprehension.py --quick",
        "docs/orientation.json::agent_entry",
        "docs/publication_entry_packet.json",
        "Lean source checked by the pinned Lean kernel",
        "Do not absorb the complete deep contract",
    ):
        assert required in text, required

    claude = (ROOT / "CLAUDE.md").read_text(encoding="utf-8")
    codex = (ROOT / "CODEX.md").read_text(encoding="utf-8")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    assert "@AGENTS.override.md" in claude
    assert "AGENTS.override.md" in codex
    assert "[`AGENTS.override.md`](AGENTS.override.md)" in readme

    print(
        "compact agent entry: pass "
        f"({len(encoded)} bytes; Codex, Claude, and README converge)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
