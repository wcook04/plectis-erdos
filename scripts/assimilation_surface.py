#!/usr/bin/env python3
"""Route an incoming research return to the surfaces that must absorb it.

`corpus_navigation.py` answers "what does this problem own".  The claim
frontier answers "what does this problem claim".  Neither answers the question
an agent actually has when a Type B research return arrives:

    *For this problem, what already exists that this return might duplicate,
    what named boundary is this return supposed to close, and which downstream
    surfaces have to move if it does?*

Answering that today means reading the packet, grepping the Lean tree,
listing `state/formal_math/type_b_return_batches/`, opening the claim frontier,
scanning the comparator directories, and running the probe registry -- six
surfaces, none of which point at each other.  This module joins them into one
bounded per-problem card.

What it reports
---------------
* **custody** -- Type B return batches whose campaign or return ids name this
  problem, with arrival state and recorded return count.
* **declared_lean_boundary** -- packet fields whose key or text names a Lean
  boundary, gap, or missing declaration.  These are the sentences a return is
  usually trying to close, and they are otherwise buried in a large packet.
* **claims** -- claim-frontier rows for this problem with evidence class,
  altitude and band, split into Lean-backed and not-Lean-backed, so a return
  that would upgrade an evidence class is visible before any editing.
* **comparator_entries** -- per-family Comparator directories for this problem
  and the Palomar-required files each is missing.
* **probe_receipts** -- receipts bound to this problem's named mechanisms.
* **downstream_surfaces** -- the exact ordered commands that must run if a
  landing changes the problem's state.

Boundary.  Every field is relayed from an owner surface.  This module opens no
Lean, runs no build, and never decides whether a return is correct, novel, or
already known.  It is a routing card; the packet, the exact Lean declaration
and its focused build remain the authorities.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any


PALOMAR_REQUIRED_FILES = (
    "Challenge.lean",
    "Solution.lean",
    "comparator.json",
    "formalization.yaml",
)

BOUNDARY_KEY_MARKERS = ("boundary", "gap", "not_in_lean", "lean_")
BOUNDARY_TEXT_MARKERS = (
    "not in lean",
    "not formalised",
    "not formalized",
    "remains unproved",
    "remaining formal",
    "lean boundary",
    "missing",
    "conditional on",
    "awaits",
)


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _normalize(problem: str) -> str:
    text = problem.strip().lower()
    if text.startswith("erdos_"):
        return text
    return f"erdos_{text.lstrip('#')}"


def _number(problem_id: str) -> str:
    return problem_id.split("_", 1)[1]


def _manifest_rows(project_root: Path) -> list[dict[str, Any]]:
    manifest = _read_json(project_root / "ErdosProblems" / "assimilation_manifest.json")
    rows = manifest.get("problems")
    return [r for r in rows if isinstance(r, dict)] if isinstance(rows, list) else []


def _custody(repo_root: Path, problem_id: str) -> list[dict[str, Any]]:
    base = repo_root / "state" / "formal_math" / "type_b_return_batches"
    if not base.is_dir():
        return []
    number = _number(problem_id)
    out: list[dict[str, Any]] = []
    for capsule in sorted(base.glob("*/intake.json")):
        try:
            payload = _read_json(capsule)
        except (OSError, json.JSONDecodeError):
            continue
        returns = payload.get("returns")
        rows = returns if isinstance(returns, list) else []
        # Match only on identity fields. Scanning the whole capsule would match
        # the project path `erdos257_period_noncollapse`, which every source ref
        # carries, and would attribute every batch to #257.
        identity = " ".join(
            [
                str(payload.get("batch_id", "")),
                str(payload.get("campaign", "")),
                *[str(r.get("return_id", "")) for r in rows if isinstance(r, dict)],
            ]
        ).lower()
        token = f"erdos{number}"
        if token not in identity and problem_id not in identity:
            continue
        matching = [
            str(r.get("return_id"))
            for r in rows
            if isinstance(r, dict) and token in str(r.get("return_id", "")).lower()
        ]
        out.append(
            {
                "batch_id": payload.get("batch_id") or capsule.parent.name,
                "intake_ref": str(capsule.relative_to(repo_root)),
                "arrival_state": payload.get("arrival_state"),
                "recorded_returns": len(rows),
                "returns_naming_this_problem": sorted(matching),
                "verify_command": (
                    "./repo-python tools/meta/bridge/type_b_return_intake.py verify "
                    f"--batch-id {payload.get('batch_id') or capsule.parent.name}"
                ),
            }
        )
    return out


def _declared_boundaries(packet: dict[str, Any], limit: int) -> list[dict[str, str]]:
    """Boundary sentences anywhere in the packet, not only at the top level.

    Packets record their Lean gaps in nested `claim_boundary` and
    `authority_boundary` fields inside `exact_results`, `landed_formal_source`
    and `finite_verification_scripts`, so a top-level key scan misses exactly
    the sentences a return is trying to close.
    """

    found: list[dict[str, str]] = []
    seen: set[str] = set()

    def walk(node: Any, path: str) -> None:
        if isinstance(node, dict):
            for key, value in node.items():
                child = f"{path}.{key}" if path else key
                if any(m in key.lower() for m in BOUNDARY_KEY_MARKERS) and isinstance(
                    value, str
                ):
                    text = " ".join(value.split())
                    if any(m in text.lower() for m in BOUNDARY_TEXT_MARKERS):
                        if text not in seen:
                            seen.add(text)
                            found.append({"packet_field": child, "excerpt": text[:600]})
                walk(value, child)
        elif isinstance(node, list):
            for index, value in enumerate(node):
                walk(value, f"{path}[{index}]")

    walk(packet, "")
    found.sort(key=lambda row: row["packet_field"])
    return found[:limit]


def _claims(frontier: dict[str, Any], problem_id: str) -> dict[str, Any]:
    number = _number(problem_id)
    claims = frontier.get("claims")
    rows = claims if isinstance(claims, dict) else {}
    lean_backed: list[dict[str, Any]] = []
    not_lean_backed: list[dict[str, Any]] = []
    for claim_id, row in sorted(rows.items()):
        if not claim_id.startswith(f"erdos{number}."):
            continue
        evidence = row.get("evidence") if isinstance(row.get("evidence"), dict) else {}
        lean = evidence.get("lean") if isinstance(evidence.get("lean"), dict) else {}
        verified = lean.get("verified")
        entry = {
            "claim_id": claim_id,
            "evidence_class": evidence.get("class"),
            "altitude": row.get("altitude"),
            "band": row.get("band"),
            "lean_status": lean.get("status"),
            "lean_declaration_count": len(verified) if isinstance(verified, list) else 0,
            "lean_missing": lean.get("missing") if isinstance(lean.get("missing"), list) else [],
        }
        if entry["lean_declaration_count"]:
            lean_backed.append(entry)
        else:
            not_lean_backed.append(entry)
    return {
        "lean_backed": lean_backed,
        "not_lean_backed": not_lean_backed,
        "upgrade_candidates": [
            c["claim_id"]
            for c in not_lean_backed
            if c["evidence_class"] in ("ordinary_proof", "conditional_on_named_lemmas")
        ],
    }


def _comparator_entries(project_root: Path, problem_id: str) -> list[dict[str, Any]]:
    number = _number(problem_id)
    out: list[dict[str, Any]] = []
    for directory in sorted(project_root.glob(f"ExternalVerification{number}*")):
        if not directory.is_dir():
            continue
        present = {name for name in PALOMAR_REQUIRED_FILES if (directory / name).is_file()}
        theorem_names: list[str] = []
        config = directory / "comparator.json"
        if config.is_file():
            try:
                theorem_names = list(_read_json(config).get("theorem_names") or [])
            except (OSError, json.JSONDecodeError):
                theorem_names = []
        out.append(
            {
                "directory": directory.name,
                "missing_palomar_files": sorted(set(PALOMAR_REQUIRED_FILES) - present),
                "audited_declaration_count": len(theorem_names),
            }
        )
    return out


def _probe_receipts(repo_root: Path, problem_id: str) -> list[dict[str, Any]]:
    base = repo_root / "state" / "formal_math"
    if not base.is_dir():
        return []
    out: list[dict[str, Any]] = []
    for path in sorted(base.rglob("*.json")):
        if "type_b_return_batches" in path.parts:
            continue
        try:
            payload = _read_json(path)
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(payload, dict):
            continue
        bindings = payload.get("mechanism_bindings")
        if not isinstance(bindings, dict) or bindings.get("problem_id") != problem_id:
            continue
        out.append(
            {
                "receipt_ref": str(path.relative_to(repo_root)),
                "motivated_by": bindings.get("motivated_by"),
                "supports": bindings.get("supports"),
                "eliminates": bindings.get("eliminates"),
            }
        )
    return out


def _downstream(problem_id: str, lean_module: object) -> list[dict[str, str]]:
    number = _number(problem_id)
    steps = [
        (
            "1. validate the exact Lean target",
            "cd formal_math/erdos257_period_noncollapse && "
            f"../../repo-python scripts/lean_fast_build.py --jobs 2 {lean_module}",
        ),
        (
            "2. confirm manifest, packets and aggregate wiring still agree",
            "cd formal_math/erdos257_period_noncollapse && "
            "../../repo-python scripts/check_problem_corpus_index.py --json",
        ),
        (
            "3. re-derive computational coverage for the packet's open producers",
            f"./repo-python -m system.lib.formal_math_probe_registry --problem {problem_id} --coverage",
        ),
        (
            "4. route the consequences of every changed path",
            "./repo-python -m system.lib.mathematical_consequence_map "
            '--query "route this landed formal-math change" '
            "--changed-path <path> --context-budget 12000",
        ),
        (
            "5. rebuild the claim frontier after the editorial ledger is updated",
            "./repo-python tools/meta/formal_math/build_claim_frontier.py",
        ),
        (
            "6. check the claim frontier for drift",
            "./repo-python tools/meta/formal_math/build_claim_frontier.py --check",
        ),
    ]
    return [{"step": label, "command": command} for label, command in steps]


def assimilation_card(
    project_root: Path, repo_root: Path, problem: str, boundary_limit: int = 12
) -> dict[str, Any]:
    problem_id = _normalize(problem)
    rows = _manifest_rows(project_root)
    row = next((r for r in rows if r.get("id") == problem_id), None)
    if row is None:
        known = sorted(str(r.get("id")) for r in rows if r.get("id"))
        raise ValueError(f"unknown manifest problem id: {problem_id}; known: {known}")

    packet_ref = row.get("packet") or row.get("research_packet")
    packet = _read_json(project_root / str(packet_ref))
    frontier_path = repo_root / "state" / "formal_math" / "claim_frontier_v1.json"
    frontier = _read_json(frontier_path) if frontier_path.is_file() else {}

    return {
        "schema_version": "lean_corpus_assimilation_surface_v0",
        "boundary": (
            "Routing only. Every field is relayed from an owner surface; this card "
            "opens no Lean, runs no build, and never decides whether a return is "
            "correct, novel, or already known."
        ),
        "problem_id": problem_id,
        "packet_ref": str(packet_ref),
        "supported_lean_module": row.get("lean_module") or row.get("supported_lean_module"),
        "first_move": (
            "Read declared_lean_boundary before reading the return's own summary: a "
            "return that does not close a named boundary is adjacent work, not an "
            "assimilation."
        ),
        "custody": _custody(repo_root, problem_id),
        "custody_note": (
            "A return with no capsule row has no byte custody. Open one with "
            "`tools/meta/bridge/type_b_return_intake.py open` before deep reading, so "
            "compaction cannot erase the source boundary."
        ),
        "declared_lean_boundary": _declared_boundaries(packet, boundary_limit),
        "claims": _claims(frontier, problem_id),
        "comparator_entries": _comparator_entries(project_root, problem_id),
        "probe_receipts": _probe_receipts(repo_root, problem_id),
        "downstream_surfaces": _downstream(problem_id, row.get("lean_module") or row.get("supported_lean_module")),
        "authority_note": (
            "The research packet owns claim identity and ceiling; the exact Lean "
            "declaration plus its focused build is proof authority; the editorial "
            "ledger owns evidence class. A return changes none of these until one of "
            "them is edited by its own maintenance lane."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Lean project root (defaults to this script's parent)",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[3],
        help="repository root (defaults to the project's grandparent)",
    )
    parser.add_argument("--problem", required=True, help="for example 1049 or erdos_1049")
    parser.add_argument(
        "--boundary-limit",
        type=int,
        default=12,
        help="maximum declared-boundary excerpts to relay",
    )
    parser.add_argument("--json", action="store_true", help="emit the full card")
    args = parser.parse_args()

    try:
        card = assimilation_card(
            args.project_root.resolve(),
            args.repo_root.resolve(),
            args.problem,
            args.boundary_limit,
        )
    except (OSError, ValueError, json.JSONDecodeError) as error:
        parser.error(str(error))

    if args.json:
        print(json.dumps(card, indent=2, sort_keys=True))
    else:
        compact = {
            "problem_id": card["problem_id"],
            "supported_lean_module": card["supported_lean_module"],
            "first_move": card["first_move"],
            "custody_batches": [c["batch_id"] for c in card["custody"]],
            "declared_lean_boundary_fields": [
                b["packet_field"] for b in card["declared_lean_boundary"]
            ],
            "claim_upgrade_candidates": card["claims"]["upgrade_candidates"],
            "lean_backed_claim_count": len(card["claims"]["lean_backed"]),
            "not_lean_backed_claim_count": len(card["claims"]["not_lean_backed"]),
            "comparator_entry_count": len(card["comparator_entries"]),
            "comparator_entries_missing_palomar_files": [
                e["directory"] for e in card["comparator_entries"] if e["missing_palomar_files"]
            ],
            "probe_receipt_count": len(card["probe_receipts"]),
        }
        print(json.dumps(compact, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
