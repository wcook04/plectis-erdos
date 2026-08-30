#!/usr/bin/env python3
"""Validate the standalone compact agent-entry contract."""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
COMPACT = ROOT / "AGENTS.override.md"
PUBLICATION_ENTRY = ROOT / "docs" / "publication_entry_packet.json"

# Every provider entry file a coding agent may auto-load. Copilot loads
# `.github/copilot-instructions.md` AND the agent files (`AGENTS.md`,
# `CLAUDE.md`, `GEMINI.md`) with no documented precedence between them, so an
# adapter that restated a rule could contradict a sibling inside one session.
# The convergence contract is therefore narrow: every adapter names
# `AGENTS.override.md` as the compact owner and adds no authority of its own.
PROVIDER_ADAPTERS = (
    "CLAUDE.md",
    "CODEX.md",
    "CURSOR.md",
    "GEMINI.md",
    ".github/copilot-instructions.md",
)

# Byte ceiling per adapter. `CLAUDE.md` carries the Claude-specific deltas and
# is separately budgeted at 1_500 bytes by
# `check_cold_clone_comprehension.py::CLAUDE_ENTRY_BUDGET_BYTES`; the rest name
# one owner and one boundary. Growth here means an adapter started carrying
# rules that belong in `AGENTS.override.md`.
ADAPTER_BYTE_CEILING = 1_500


def main() -> int:
    text = COMPACT.read_text(encoding="utf-8")
    encoded = text.encode("utf-8")

    assert len(encoded) < 8_000, len(encoded)
    for required in (
        'query_corpus.py --ask "<question>"',
        "query_corpus.py --overview --format card",
        "--route instant_orientation",
        "--route erdos249_certificate_story",
        "--route erdos257_half_story",
        "--route browse_claim_status",
        'query_corpus.py --goal-support "<Lean or mathematical goal>"',
        "check_cold_clone_comprehension.py --quick",
        "docs/orientation.json::agent_entry",
        "docs/publication_entry_packet.json",
        "--route comparator_assurance",
        "--route palomar_qualification",
        "does not establish novelty, significance, priority, or",
        "does not confer acceptance,",
        "Lean source checked by the pinned Lean kernel",
        "Do not absorb the complete deep contract",
    ):
        assert required in text, required

    # Every adapter must name the compact owner, and Claude Code must actually
    # *import* it: `@AGENTS.override.md`, not a mention of it beside an
    # `@AGENTS.md` import. Naming alone was satisfiable while a cold clone still
    # opened into the deep contract, which is the whole failure. The two gates
    # used to be unsatisfiable together -- `check_cold_clone_comprehension.py`
    # required the `@AGENTS.md` token -- so that gate's token list now agrees
    # with this file rather than contradicting it.
    oversized: dict[str, int] = {}
    for rel in PROVIDER_ADAPTERS:
        adapter = (ROOT / rel).read_text(encoding="utf-8")
        assert "AGENTS.override.md" in adapter, rel
        assert "AGENTS.md" in adapter, rel
        size = len(adapter.encode("utf-8"))
        if size > ADAPTER_BYTE_CEILING:
            oversized[rel] = size
    assert not oversized, (
        f"provider adapters exceeded {ADAPTER_BYTE_CEILING} bytes: {oversized}; "
        "an adapter names the compact owner and the authority boundary, and "
        "rules belong in AGENTS.override.md where they cannot contradict a "
        "sibling adapter loaded in the same session"
    )

    packet = json.loads(PUBLICATION_ENTRY.read_text(encoding="utf-8"))
    frontier = packet["research_frontier"]
    assert frontier["problem_id"] == "erdos_1041"
    assert frontier["query"] == "python3 scripts/query_corpus.py --route erdos_1041"
    assert frontier["strongest_result_summary"]["result_count"] == 35
    assert frontier["strongest_result_summary"]["status"] == "open"
    assert frontier["checkpoint_summary"]["exported_source_file_count"] == 685
    assert set(frontier["files"]) == {
        "frontier",
        "strongest_results",
        "manifest",
        "checkpoint",
    }
    assert "do not close Erdős 1041" in frontier["promotion_boundary"]

    # Naming is not enough for Claude Code, which resolves the `@` import and
    # loads that file. `@AGENTS.md` here means a cold clone opens the deep
    # contract; the compact entry then defers nothing and this whole file is
    # decoration.
    claude = (ROOT / "CLAUDE.md").read_text(encoding="utf-8")
    assert "@AGENTS.override.md" in claude, (
        "CLAUDE.md must import the compact entry, not merely mention it: "
        "Claude Code loads whatever the @ import names"
    )

    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    assert "[`AGENTS.override.md`](AGENTS.override.md)" in readme

    print(
        "compact agent entry: pass "
        f"({len(encoded)} bytes; {len(PROVIDER_ADAPTERS)} provider adapters "
        "and README converge)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
