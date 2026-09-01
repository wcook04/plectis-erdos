#!/usr/bin/env python3
"""Focused tests for the cold-clone proof cockpit."""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "scripts" / "proof_cockpit.py"
SPEC = importlib.util.spec_from_file_location("proof_cockpit", MODULE_PATH)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def test_default_packet() -> None:
    packet = MODULE.build_cockpit(ROOT)
    assert packet["schema"] == "plectis-lean-proof-cockpit/1"
    assert packet["corpus"]["problem_count"] == 8
    assert packet["corpus"]["open_problem_count"] == 8
    # Against the register, not a frozen number. Both counts were pinned to a
    # snapshot (103 claims, 5 open propositions) of a corpus that keeps
    # growing, so every landed claim broke this test while the projection it
    # guards was correct. Comparing to docs/claims.json still catches the real
    # defect -- a cockpit that drops or invents rows -- and cannot go stale.
    register = json.loads((ROOT / "docs" / "claims.json").read_text(encoding="utf-8"))
    assert packet["corpus"]["claim_count"] == len(register["claims"])
    assert packet["corpus"]["claim_count"] > 0
    assert packet["frontier"]["headline_open_proposition_count"] == len(
        register["remaining_open_propositions"]
    )
    assert packet["proof_authority"] == "Lean source checked by the pinned Lean kernel"
    assert packet["next_actions"]["kernel_check"].endswith("--jobs 2")
    assert all("ai_workflow" not in json.dumps(row) for row in packet["workbench"]["sessions"])


def test_problem_focus() -> None:
    packet = MODULE.build_cockpit(ROOT, problem_number=68)
    problem = packet["selected_problem"]
    assert problem["erdos_number"] == 68
    assert problem["status"] == "open"
    assert problem["module_count"] > 0
    assert problem["declaration_count"] > 0
    assert problem["open_obligations"]


def test_unknown_problem_refuses() -> None:
    try:
        MODULE.build_cockpit(ROOT, problem_number=999)
    except ValueError as exc:
        assert "available: 68, 243, 249, 251, 257, 269, 1041, 1049" in str(exc)
    else:
        raise AssertionError("unknown problem must be rejected")


def test_cli_json_and_card() -> None:
    json_run = subprocess.run(
        [sys.executable, str(MODULE_PATH), "--problem", "257", "--format", "json"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert json_run.returncode == 0, json_run.stderr
    packet = json.loads(json_run.stdout)
    assert packet["selected_problem"]["erdos_number"] == 257

    card_run = subprocess.run(
        [sys.executable, str(MODULE_PATH)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert card_run.returncode == 0, card_run.stderr
    assert "Plectis Lean proof cockpit" in card_run.stdout
    assert "only the pinned Lean kernel checks formal truth" in card_run.stdout


def test_public_agent_assets_exist() -> None:
    skill = ROOT / "skills" / "public-mathematical-writing" / "SKILL.md"
    assert skill.is_file()
    skill_text = skill.read_text(encoding="utf-8")
    assert "Lean source checked by the pinned Lean kernel" in skill_text
    assert "No private" in skill_text
    assert (ROOT / "docs" / "PROOF_COCKPIT.md").is_file()


def main() -> int:
    tests = [
        test_default_packet,
        test_problem_focus,
        test_unknown_problem_refuses,
        test_cli_json_and_card,
        test_public_agent_assets_exist,
    ]
    for test in tests:
        test()
    print(f"proof cockpit: pass ({len(tests)} tests)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
