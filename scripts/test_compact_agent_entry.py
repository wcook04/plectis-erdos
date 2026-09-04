#!/usr/bin/env python3
"""Validate the standalone compact agent-entry contract."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
COMPACT = ROOT / "AGENTS.override.md"
DEEP = ROOT / "AGENTS.md"
WORKBENCH = ROOT / "docs" / "AGENT_WORKBENCH.md"
PUBLICATION_ENTRY = ROOT / "docs" / "publication_entry_packet.json"
README = ROOT / "README.md"

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


def query_route(route_id: str) -> dict[str, object]:
    """Execute one route advertised by the compact cold-clone entry."""
    completed = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "query_corpus.py"),
            "--route",
            route_id,
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0, (
        f"documented compact-entry route failed: {route_id}: "
        f"{completed.stderr.strip()}"
    )
    return json.loads(completed.stdout)


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
        "proof_cockpit.py --format card",
        'agent_entry.py --entry "<task in ordinary language>"',
        "agent_entry.py --skills",
        "skills/<id>/SKILL.md",
        "check_cold_clone_comprehension.py --quick",
        "docs/publication_entry_packet.json",
        "--route comparator_assurance",
        "--route palomar_qualification",
        "does not establish novelty, significance, priority, or",
        "does not confer acceptance,",
        "Lean source checked by the pinned Lean kernel",
        "Do not absorb the complete deep contract",
    ):
        assert required in text, required
    assert "docs/orientation.json::agent_entry" not in text

    readme = README.read_text(encoding="utf-8")
    assert 'scripts/agent_entry.py --entry "<task in ordinary language>"' in readme
    assert "as\nits first action" in readme

    # Projection-only checks can pass while an advertised route returns
    # "unknown route id". Exercise the public commands themselves.
    for route_id, authority_prefix in (
        (
            "comparator_assurance",
            "configured_statement_axiom_and_kernel_assurance",
        ),
        (
            "palomar_qualification",
            "repository_local_qualification_",
        ),
    ):
        packet = query_route(route_id)
        assert packet["kind"] == "reading_route", route_id
        route = packet["route"]
        assert isinstance(route, dict), route_id
        assert route["id"] == route_id
        assert route["route_kind"] == "external_assurance"
        assert route["authority_owners"]
        assert route["adjacent_handle_classes"]
        assert str(packet["authority_posture"]).startswith(authority_prefix)

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
    # The count belongs to the corpus file that holds the results, not to this
    # test; pinning it here made every published #1041 result after the
    # thirty-fifth turn the compact entry red.
    assert frontier["strongest_result_summary"]["result_count"] == len(
        json.loads(
            (ROOT / "research_corpus/Erdos1041/STRONGEST_RESULTS.json").read_text(
                encoding="utf-8"
            )
        )["results"]
    )
    assert frontier["strongest_result_summary"]["status"] == "open"
    # Same again: the checkpoint states its own export size.
    assert frontier["checkpoint_summary"]["exported_source_file_count"] == json.loads(
        (ROOT / "research_corpus/Erdos1041/PUBLIC_CORPUS_CHECKPOINT.json").read_text(
            encoding="utf-8"
        )
    )["exported_source_file_count"]
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

    deep = DEEP.read_text(encoding="utf-8")
    assert "[docs/AGENT_WORKBENCH.md](docs/AGENT_WORKBENCH.md)" in deep
    assert "[CONTRIBUTING.md](CONTRIBUTING.md)" in deep

    skill_router = ROOT / "scripts" / "test_agent_entry.py"
    completed = subprocess.run(
        [sys.executable, str(skill_router)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr

    workbench = WORKBENCH.read_text(encoding="utf-8")
    for paper in (
        "erdos-68-factorial-denominator-irrationality.pdf",
        "erdos-243-reciprocal-tail-rigidity.pdf",
        "erdos-249-binary-totient-series.pdf",
        "erdos-251-prime-gap-dyadic-series.pdf",
        "erdos-257-mersenne-support-subseries.pdf",
        "erdos-269-three-prime-running-lcm.pdf",
        "erdos-1041-lemniscate-newton-flow.pdf",
        "erdos-1049-rational-base-lambert.pdf",
    ):
        assert paper in workbench, paper

    retired_paragraph = " ".join(
        next(
            paragraph
            for paragraph in workbench.split("\n\n")
            if "erdos249-257-main-paper.pdf" in paragraph
        ).split()
    ).lower()
    assert "retired" in retired_paragraph
    assert "archive" in retired_paragraph
    assert "provenance" in retired_paragraph
    assert "do not use" in retired_paragraph
    assert "current gateway" in retired_paragraph
    assert "default" not in retired_paragraph
    assert "canonical" not in retired_paragraph

    # These are public agent dependencies, not private conveniences. A prior
    # deep entry referenced the writing skill even though no such file shipped
    # in a cold clone; keep both native surfaces on disk and executable.
    assert (ROOT / "skills/public-mathematical-writing/SKILL.md").is_file()
    cockpit = ROOT / "scripts/proof_cockpit.py"
    assert cockpit.is_file()
    completed = subprocess.run(
        [sys.executable, str(cockpit), "--format", "json"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr
    cockpit_packet = json.loads(completed.stdout)
    assert cockpit_packet["artifact_role"] == "cold_clone_proof_control_card"
    assert cockpit_packet["corpus"]["problem_count"] == 8

    print(
        "compact agent entry: pass "
        f"({len(encoded)} bytes; {len(PROVIDER_ADAPTERS)} provider adapters "
        "and deep-agent routes converge)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
