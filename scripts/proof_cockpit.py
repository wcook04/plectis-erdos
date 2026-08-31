#!/usr/bin/env python3
"""Compact, cold-clone control card for the public Lean proof corpus.

The cockpit composes committed public metadata and local checkout facts.  It
does not read private workflow state, elaborate Lean, or promote navigation
metadata into proof authority.  Use ``--check`` to run the fast public
validation floor explicitly.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "plectis-lean-proof-cockpit/1"


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _git_output(root: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", *args],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    return completed.stdout.strip() if completed.returncode == 0 else ""


def checkout_state(root: Path) -> dict[str, Any]:
    head = _git_output(root, "rev-parse", "HEAD")
    branch = _git_output(root, "branch", "--show-current")
    status = _git_output(root, "status", "--porcelain")
    dirty_paths = [line for line in status.splitlines() if line.strip()]
    return {
        "head": head or "unavailable",
        "branch": branch or "detached_or_unavailable",
        "dirty_path_count": len(dirty_paths),
        "clean": not dirty_paths,
        "authority_posture": "checkout_observation_not_proof_authority",
    }


def workbench_state(root: Path) -> dict[str, Any]:
    sessions_root = root / "workbench" / "sessions"
    ledgers = sorted(sessions_root.glob("*/ledger.jsonl"))
    outcome_counts: Counter[str] = Counter()
    move_counts: Counter[str] = Counter()
    session_rows: list[dict[str, Any]] = []
    for ledger in ledgers:
        rows = [
            json.loads(line)
            for line in ledger.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        for row in rows:
            move_counts[str(row.get("kind", "unknown"))] += 1
        close = next(
            (row for row in reversed(rows) if row.get("kind") == "session_closed"),
            None,
        )
        outcome = str(close.get("outcome")) if close else "open"
        outcome_counts[outcome] += 1
        session_rows.append(
            {
                "session": ledger.parent.name,
                "outcome": outcome,
                "move_count": len(rows),
                "kernel_accepted_probe_count": sum(
                    1
                    for row in rows
                    if row.get("kind") == "probe"
                    and row.get("kernel_receipt", {}).get("verdict")
                    == "kernel_accepted"
                ),
                "claim_count": sum(1 for row in rows if row.get("kind") == "claim"),
                "ledger": str(ledger.relative_to(root)),
            }
        )
    return {
        "session_count": len(ledgers),
        "outcome_counts": dict(sorted(outcome_counts.items())),
        "move_counts": dict(sorted(move_counts.items())),
        "sessions": session_rows,
        "authority_posture": (
            "ledger_notes_are_advisory; only recorded kernel probe receipts assert"
        ),
    }


def selected_problem(problems: dict[str, Any], number: int | None) -> dict[str, Any] | None:
    if number is None:
        return None
    row = next(
        (
            problem
            for problem in problems.get("problems", [])
            if problem.get("erdos_number") == number
        ),
        None,
    )
    if row is None:
        available = ", ".join(
            str(problem.get("erdos_number"))
            for problem in problems.get("problems", [])
        )
        raise ValueError(f"unknown problem {number}; available: {available}")
    modules = row.get("modules", [])
    return {
        "problem_id": row.get("problem_id"),
        "erdos_number": number,
        "title": row.get("short_title"),
        "status": row.get("status"),
        "question": row.get("question"),
        "module_count": len(modules),
        "declaration_count": sum(int(module.get("declaration_count", 0)) for module in modules),
        "theorem_count": sum(int(module.get("theorem_count", 0)) for module in modules),
        "open_obligations": row.get("open_obligations", []),
        "what_is_checked": row.get("what_is_checked", []),
        "what_is_not_checked": row.get("what_is_not_checked", []),
        "paper": row.get("paper"),
        "claim_registry_status": row.get("claim_registry_status"),
    }


FAST_CHECKS: tuple[tuple[str, tuple[str, ...]], ...] = (
    (
        "claim_registry",
        (sys.executable, "scripts/verify_claims.py", "--verify-all"),
    ),
    (
        "cold_clone_comprehension",
        (sys.executable, "scripts/check_cold_clone_comprehension.py", "--quick"),
    ),
    (
        "orientation_freshness",
        (sys.executable, "scripts/build_corpus_descriptor.py", "--check"),
    ),
)


def run_fast_checks(root: Path) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for check_id, command in FAST_CHECKS:
        completed = subprocess.run(
            command,
            cwd=root,
            capture_output=True,
            text=True,
            check=False,
        )
        output = [
            line.strip()
            for line in (completed.stdout + "\n" + completed.stderr).splitlines()
            if line.strip()
        ]
        rows.append(
            {
                "check_id": check_id,
                "status": "pass" if completed.returncode == 0 else "fail",
                "returncode": completed.returncode,
                "command": " ".join(command),
                "summary": output[-1] if output else "no output",
            }
        )
    return {
        "status": "pass" if all(row["status"] == "pass" for row in rows) else "fail",
        "checks": rows,
        "proof_authority": False,
    }


def build_cockpit(
    root: Path = ROOT,
    *,
    problem_number: int | None = None,
    run_checks: bool = False,
) -> dict[str, Any]:
    orientation = _read_json(root / "docs" / "orientation.json")
    claims = _read_json(root / "docs" / "claims.json")
    problems = _read_json(root / "docs" / "problems.json")
    paper_corpus = _read_json(root / "docs" / "papers" / "corpus.json")
    status_counts = Counter(str(row.get("status", "unknown")) for row in claims["claims"])
    problem_rows = problems.get("problems", [])
    packet: dict[str, Any] = {
        "schema": SCHEMA,
        "artifact_role": "cold_clone_proof_control_card",
        "authority_posture": "navigation_and_runtime_observation_not_proof_authority",
        "checkout": checkout_state(root),
        "release": orientation["release"],
        "corpus": {
            "problem_count": len(problem_rows),
            "open_problem_count": sum(
                1 for row in problem_rows if row.get("status") == "open"
            ),
            "claim_count": len(claims["claims"]),
            "claim_status_counts": dict(sorted(status_counts.items())),
            "module_count": orientation["scale"]["module_count"],
            "declaration_count": orientation["scale"]["declaration_count"],
            "theorem_like_count": orientation["scale"]["theorem_like_count"],
            "paper_count": len(paper_corpus.get("papers", [])),
        },
        "frontier": {
            "headline_open_proposition_count": len(
                claims["remaining_open_propositions"]
            ),
            "headline_open_propositions": claims["remaining_open_propositions"],
            "problem_statuses": [
                {
                    "erdos_number": row.get("erdos_number"),
                    "status": row.get("status"),
                    "open_obligation_count": len(row.get("open_obligations", [])),
                }
                for row in problem_rows
            ],
            "boundary": "All eight indexed Erdős problems remain open.",
        },
        "workbench": workbench_state(root),
        "selected_problem": selected_problem(problems, problem_number),
        "next_actions": {
            "orient": "python3 scripts/query_corpus.py --overview",
            "ask": 'python3 scripts/query_corpus.py --ask "<question>"',
            "problem": (
                f'python3 scripts/query_corpus.py --ask "what remains open for Erdős {problem_number}?"'
                if problem_number is not None
                else "python3 scripts/proof_cockpit.py --problem <68|243|249|251|257|269|1041|1049>"
            ),
            "goal_support": 'python3 scripts/query_corpus.py --goal-support "<goal>"',
            "proof_plan": 'python3 scripts/query_corpus.py --proof-plan "<goal>" --depth 4',
            "kernel_check": "python3 scripts/lean_fast_build.py --jobs 2",
            "session_notary": "python3 scripts/proof_workbench.py --help",
            "fast_public_checks": "python3 scripts/proof_cockpit.py --check",
        },
        "proof_authority": orientation["proof_authority"],
        "non_claims": [
            "The cockpit does not prove a theorem or change public claim status.",
            "Workbench notes and navigation projections are not Lean proof authority.",
            "No private ai_workflow, provider, task-ledger, or operator state is read.",
        ],
    }
    if run_checks:
        packet["fast_checks"] = run_fast_checks(root)
    return packet


def render_card(packet: dict[str, Any]) -> str:
    corpus = packet["corpus"]
    checkout = packet["checkout"]
    frontier = packet["frontier"]
    workbench = packet["workbench"]
    lines = [
        "Plectis Lean proof cockpit",
        (
            f"checkout: {checkout['branch']}@{checkout['head'][:12]} | "
            f"{'clean' if checkout['clean'] else str(checkout['dirty_path_count']) + ' dirty paths'} | "
            f"toolchain {packet['release']['lean_toolchain']}"
        ),
        (
            f"corpus: {corpus['problem_count']} open problems | "
            f"{corpus['claim_count']} claims | {corpus['module_count']} modules | "
            f"{corpus['declaration_count']} declarations | {corpus['paper_count']} papers"
        ),
        (
            f"frontier: {frontier['headline_open_proposition_count']} exact headline open "
            "propositions; all eight indexed problems remain open"
        ),
        (
            f"workbench: {workbench['session_count']} recorded sessions | "
            + ", ".join(
                f"{key} {value}" for key, value in workbench["outcome_counts"].items()
            )
        ),
    ]
    problem = packet.get("selected_problem")
    if problem:
        lines.extend(
            [
                (
                    f"problem #{problem['erdos_number']}: {problem['title']} | "
                    f"{problem['module_count']} modules | {problem['declaration_count']} declarations | "
                    f"{len(problem['open_obligations'])} open obligations"
                ),
                f"question: {problem['question']}",
            ]
        )
    checks = packet.get("fast_checks")
    if checks:
        lines.append(
            "fast checks: "
            + checks["status"]
            + " ("
            + ", ".join(
                f"{row['check_id']}={row['status']}" for row in checks["checks"]
            )
            + ")"
        )
    lines.extend(
        [
            f"next: {packet['next_actions']['problem'] if problem else packet['next_actions']['orient']}",
            f"proof gate: {packet['next_actions']['kernel_check']}",
            "boundary: this card routes work; only the pinned Lean kernel checks formal truth.",
        ]
    )
    return "\n".join(lines)


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problem", type=int, help="Focus one indexed Erdős problem")
    parser.add_argument(
        "--format",
        choices=("card", "json"),
        default="card",
        help="Output profile (default: card)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Run the fast public claim, cold-clone, and projection checks",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        packet = build_cockpit(
            problem_number=args.problem,
            run_checks=args.check,
        )
    except (OSError, KeyError, ValueError, json.JSONDecodeError) as exc:
        print(f"proof cockpit: {exc}", file=sys.stderr)
        return 2
    if args.format == "json":
        print(json.dumps(packet, indent=2, ensure_ascii=False))
    else:
        print(render_card(packet))
    checks = packet.get("fast_checks")
    return 1 if checks and checks["status"] != "pass" else 0


if __name__ == "__main__":
    raise SystemExit(main())
