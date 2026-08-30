#!/usr/bin/env python3
"""Compile bounded proof-state transitions by asking Lean, not by guessing.

The static semantic compiler remains the cheap candidate generator.  This
runtime owner takes an explicit goal, context, and bounded candidate list,
executes every candidate through the pinned Lean environment, and emits an
AND/OR obligation hypergraph.  A candidate enters the graph only when Lean
reaches the post-application ``trace_state`` checkpoint.

The packet is navigation and planning evidence.  Only a successful Lean run
with no remaining goals is a proof receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
import subprocess
from pathlib import Path
from typing import Any, Iterable

import validation_singleflight as singleflight


ROOT = Path(__file__).resolve().parents[1]
REQUEST_SCHEMA = "erdos249257-proof-state-request/1"
PACKET_SCHEMA = "erdos249257-proof-state-compilation/1"
PILOT_SCHEMA = "erdos249257-proof-state-pilot/1"
MAX_CANDIDATES = 8
MAX_DISCHARGE_TACTICS = 8
MAX_PACKET_BYTES = 64_000
ENVIRONMENT_COMMAND_TIMEOUT_SECONDS = singleflight.GIT_COMMAND_TIMEOUT_SECONDS


class RequestError(ValueError):
    """Raised when a proof-state request exceeds the bounded contract."""


def _sha256_bytes(payload: bytes) -> str:
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def _sha256_text(payload: str) -> str:
    return _sha256_bytes(payload.encode("utf-8"))


def _file_digest(path: Path) -> str | None:
    if not path.is_file():
        return None
    return _sha256_bytes(path.read_bytes())


def _command_output(
    command: list[str],
    *,
    cwd: Path,
    timeout_seconds: float,
) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        env=singleflight.command_environment(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
        timeout=timeout_seconds,
    )
    if completed.returncode != 0:
        rendered = " ".join(command)
        raise RuntimeError(
            f"environment command failed ({completed.returncode}): {rendered}\n"
            + completed.stdout[-4000:]
        )
    return completed.stdout.strip()


def environment_fingerprint(
    repo_root: Path = ROOT,
    *,
    timeout_seconds: float = ENVIRONMENT_COMMAND_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Return the exact local environment identity used by transition runs."""
    git_head = _command_output(
        ["git", "rev-parse", "HEAD"],
        cwd=repo_root,
        timeout_seconds=timeout_seconds,
    )
    lean_version = _command_output(
        ["lake", "env", "lean", "--version"],
        cwd=repo_root,
        timeout_seconds=timeout_seconds,
    )
    identity = {
        "repository_head": git_head,
        "lean_version": lean_version,
        "lean_toolchain_digest": _file_digest(repo_root / "lean-toolchain"),
        "lake_manifest_digest": _file_digest(
            repo_root / "lake-manifest.json"
        ),
        "lakefile_digest": _file_digest(repo_root / "lakefile.toml"),
    }
    identity["fingerprint"] = _sha256_text(
        json.dumps(identity, sort_keys=True, separators=(",", ":"))
    )
    return identity


def _validate_request(request: dict[str, Any]) -> None:
    if request.get("schema_version") != REQUEST_SCHEMA:
        raise RequestError(
            f"request schema must be {REQUEST_SCHEMA!r}"
        )
    if not str(request.get("goal_id", "")).strip():
        raise RequestError("goal_id is required")
    imports = request.get("imports")
    if not isinstance(imports, list) or not imports:
        raise RequestError("imports must be a nonempty list")
    if any(
        not isinstance(module, str)
        or not module.strip()
        or "\n" in module
        for module in imports
    ):
        raise RequestError("each import must be one Lean module name")
    opens = request.get("opens", [])
    if not isinstance(opens, list) or any(
        not isinstance(namespace, str)
        or not namespace.strip()
        or "\n" in namespace
        for namespace in opens
    ):
        raise RequestError("opens must contain single-line namespace names")
    context = request.get("context", [])
    if not isinstance(context, list):
        raise RequestError("context must be a list")
    for row in context:
        if not isinstance(row, dict):
            raise RequestError("context rows must be objects")
        if not str(row.get("name", "")).strip():
            raise RequestError("context rows require a name")
        binder = row.get("binder")
        if not isinstance(binder, str) or not binder.strip():
            raise RequestError("context rows require Lean binder text")
    target = request.get("target")
    if not isinstance(target, str) or not target.strip():
        raise RequestError("target must be nonempty Lean syntax")
    candidates = request.get("candidates")
    if not isinstance(candidates, list) or not candidates:
        raise RequestError("candidates must be a nonempty list")
    if len(candidates) > MAX_CANDIDATES:
        raise RequestError(
            f"candidate count exceeds {MAX_CANDIDATES}"
        )
    candidate_ids: set[str] = set()
    for candidate in candidates:
        if not isinstance(candidate, dict):
            raise RequestError("candidate rows must be objects")
        candidate_id = str(candidate.get("candidate_id", "")).strip()
        if not candidate_id:
            raise RequestError("candidate_id is required")
        if candidate_id in candidate_ids:
            raise RequestError(f"duplicate candidate_id {candidate_id!r}")
        candidate_ids.add(candidate_id)
        declaration = candidate.get("declaration")
        if not isinstance(declaration, str) or not declaration.strip():
            raise RequestError("candidate declaration is required")
        if "\n" in declaration:
            raise RequestError("candidate declaration must be one line")
        arguments = candidate.get("arguments", [])
        if not isinstance(arguments, list) or any(
            not isinstance(argument, str) or "\n" in argument
            for argument in arguments
        ):
            raise RequestError("candidate arguments must be single-line terms")
        discharge = candidate.get("discharge_tactics", [])
        if not isinstance(discharge, list) or any(
            not isinstance(tactic, str) or not tactic.strip()
            for tactic in discharge
        ):
            raise RequestError("discharge_tactics must be nonempty strings")
        if len(discharge) > MAX_DISCHARGE_TACTICS:
            raise RequestError(
                "discharge tactic count exceeds "
                f"{MAX_DISCHARGE_TACTICS}"
            )


def _application_tactic(candidate: dict[str, Any]) -> str:
    arguments = " ".join(candidate.get("arguments", []))
    suffix = f" {arguments}" if arguments else ""
    return f"apply {candidate['declaration']}{suffix}"


def _render_probe(
    request: dict[str, Any],
    candidate: dict[str, Any],
) -> tuple[str, dict[str, Any]]:
    lines: list[str] = []
    lines.extend(f"import {module}" for module in request["imports"])
    if request.get("opens"):
        lines.append("open " + " ".join(request["opens"]))
    lines.append("set_option linter.unusedTactic false in")
    lines.append("example")
    lines.extend(f"    {row['binder']}" for row in request["context"])
    lines.append("    :")
    target_lines = request["target"].strip().splitlines()
    lines.extend(f"      {line}" for line in target_lines[:-1])
    lines.append(f"      {target_lines[-1]} := by")

    lines.append("  trace_state")
    initial_trace_line = len(lines)
    tactic = _application_tactic(candidate)
    lines.append(f"  {tactic}")
    application_line = len(lines)
    lines.append("  trace_state")
    application_trace_line = len(lines)

    discharge_steps = []
    for index, discharge_tactic in enumerate(
        candidate.get("discharge_tactics", [])
    ):
        lines.append(f"  {discharge_tactic}")
        action_line = len(lines)
        lines.append("  trace_state")
        trace_line = len(lines)
        discharge_steps.append(
            {
                "index": index,
                "tactic": discharge_tactic,
                "action_line": action_line,
                "trace_line": trace_line,
            }
        )
    source = "\n".join(lines) + "\n"
    positions = {
        "initial_trace_line": initial_trace_line,
        "application_line": application_line,
        "application_trace_line": application_trace_line,
        "discharge_steps": discharge_steps,
    }
    return source, positions


def _parse_lean_messages(output: str) -> tuple[list[dict[str, Any]], list[str]]:
    messages: list[dict[str, Any]] = []
    non_json: list[str] = []
    for line in output.splitlines():
        if not line.strip():
            continue
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            non_json.append(line)
            continue
        if isinstance(message, dict):
            messages.append(message)
        else:
            non_json.append(line)
    return messages, non_json


def _message_line(message: dict[str, Any]) -> int | None:
    position = message.get("pos")
    if not isinstance(position, dict):
        return None
    line = position.get("line")
    return line if isinstance(line, int) else None


def _trace_at(
    messages: Iterable[dict[str, Any]],
    source_line: int,
) -> dict[str, Any] | None:
    matches = [
        message
        for message in messages
        if message.get("kind") == "trace"
        and _message_line(message) == source_line
    ]
    return matches[-1] if matches else None


def split_goal_state(state: str) -> list[dict[str, Any]]:
    """Split Lean's ``trace_state`` rendering into exact open-goal blocks."""
    stripped = state.strip()
    if not stripped:
        return []
    blocks = re.split(r"\n\s*\n(?=case [^\n]+\n)", stripped)
    if len(blocks) == 1 and stripped.count("⊢") > 1:
        blocks = re.split(r"\n\s*\n(?=[^\n]*⊢)", stripped)
    goals = []
    for block in blocks:
        lines = block.strip().splitlines()
        target_index = next(
            (index for index, line in enumerate(lines) if line.startswith("⊢")),
            None,
        )
        if target_index is None:
            target_index = next(
                (
                    index
                    for index, line in enumerate(lines)
                    if "⊢" in line
                ),
                None,
            )
        if target_index is None:
            goals.append(
                {
                    "case": None,
                    "context": lines,
                    "target": "",
                    "rendered": block.strip(),
                }
            )
            continue
        case = None
        context_start = 0
        if lines and lines[0].startswith("case "):
            case = lines[0][len("case ") :].strip()
            context_start = 1
        goals.append(
            {
                "case": case,
                "context": lines[context_start:target_index],
                "target": "\n".join(lines[target_index:]),
                "rendered": block.strip(),
            }
        )
    return goals


def _state_node(
    goal: dict[str, Any],
    *,
    environment_id: str,
    assumption_world: list[str],
) -> dict[str, Any]:
    identity_payload = {
        "goal": goal["rendered"],
        "environment": environment_id,
        "assumption_world": assumption_world,
    }
    node_id = "ps_" + hashlib.sha256(
        json.dumps(
            identity_payload,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()[:16]
    return {
        "node_id": node_id,
        "case": goal["case"],
        "context": goal["context"],
        "target": goal["target"],
        "rendered": goal["rendered"],
        "assumption_world": assumption_world,
    }


def minimal_hitting_sets(
    blocker_sets: Iterable[Iterable[str]],
    *,
    limit: int = 16,
) -> list[list[str]]:
    """Return bounded inclusion-minimal sets intersecting every blocker set."""
    normalized = [
        set(blockers) for blockers in blocker_sets if set(blockers)
    ]
    if not normalized:
        return []
    universe = sorted(set().union(*normalized))
    results: list[set[str]] = []
    for size in range(1, len(universe) + 1):
        for combination in itertools.combinations(universe, size):
            candidate = set(combination)
            if not all(candidate & blockers for blockers in normalized):
                continue
            if any(previous <= candidate for previous in results):
                continue
            results.append(candidate)
            if len(results) >= limit:
                return [sorted(row) for row in results]
    return [sorted(row) for row in results]


def minimal_missing_interventions(
    plan_residual_sets: Iterable[Iterable[str]],
) -> list[list[str]]:
    """Return the inclusion-minimal antichain of per-plan residual sets.

    Each returned row is one complete addition plan: supplying every member
    closes at least one Lean-reached route.  This is deliberately not the
    hitting-set family: a cut intersects every route and says which removal
    defeats the whole graph, while an intervention completes one route.  The
    two families coincide only in degenerate cases.
    """
    normalized = sorted(
        {frozenset(rows) for rows in plan_residual_sets},
        key=lambda row: (len(row), tuple(sorted(row))),
    )
    kept: list[frozenset[str]] = []
    for candidate in normalized:
        if not any(previous <= candidate for previous in kept):
            kept.append(candidate)
    return [sorted(row) for row in kept]


def _declaration_receipt(
    declaration: str,
    repo_root: Path,
) -> dict[str, Any]:
    index_path = repo_root / "docs/lean_dependency_index.json"
    if not index_path.is_file():
        return {
            "declaration": declaration,
            "availability": "dependency_index_absent",
        }
    data = json.loads(index_path.read_text(encoding="utf-8"))
    node = next(
        (
            row
            for row in data.get("nodes", [])
            if row.get("handle") == declaration
        ),
        None,
    )
    if node is None:
        return {
            "declaration": declaration,
            "availability": "not_source_joined_in_dependency_index",
        }
    source_path = repo_root / node["module"]
    return {
        "declaration": declaration,
        "availability": "source_joined",
        "declaration_kind": node.get("declaration_kind"),
        "source_ref": node.get("source_ref"),
        "source_digest": _file_digest(source_path),
        "dependency_index_source_fingerprint": data.get(
            "source_fingerprint"
        ),
    }


def _error_receipts(
    messages: Iterable[dict[str, Any]],
    *,
    ignore_unsolved_goals: bool,
) -> list[dict[str, Any]]:
    errors = []
    for message in messages:
        if message.get("severity") != "error":
            continue
        if (
            ignore_unsolved_goals
            and message.get("kind") == "Tactic.unsolvedGoals"
        ):
            continue
        errors.append(
            {
                "kind": message.get("kind"),
                "line": _message_line(message),
                "data": str(message.get("data", ""))[:2000],
            }
        )
    return errors


def _run_candidate(
    request: dict[str, Any],
    candidate: dict[str, Any],
    *,
    repo_root: Path,
    environment: dict[str, Any],
    timeout_seconds: float,
) -> dict[str, Any]:
    source, positions = _render_probe(request, candidate)
    try:
        completed = subprocess.run(
            ["lake", "env", "lean", "--stdin", "--json"],
            cwd=repo_root,
            env=singleflight.command_environment(),
            input=source,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
            timeout=timeout_seconds,
        )
        timed_out = False
        output = completed.stdout
        return_code = completed.returncode
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        output = (exc.stdout or "") + (exc.stderr or "")
        return_code = None

    messages, non_json = _parse_lean_messages(output)
    initial_trace = _trace_at(
        messages, positions["initial_trace_line"]
    )
    application_trace = _trace_at(
        messages, positions["application_trace_line"]
    )
    initial_goals = split_goal_state(
        str(initial_trace.get("data", "")) if initial_trace else ""
    )
    application_goals = split_goal_state(
        str(application_trace.get("data", ""))
        if application_trace
        else ""
    )
    discharge_receipts = []
    latest_goals = application_goals
    for step in positions["discharge_steps"]:
        trace = _trace_at(messages, step["trace_line"])
        goals = split_goal_state(
            str(trace.get("data", "")) if trace else ""
        )
        discharge_receipts.append(
            {
                "index": step["index"],
                "tactic": step["tactic"],
                "trace_reached": trace is not None,
                "open_goals": goals,
                "open_goal_count": len(goals),
            }
        )
        if trace is not None:
            latest_goals = goals

    application_accepted = application_trace is not None
    proof_closed = (
        application_accepted
        and not latest_goals
        and return_code == 0
        and not timed_out
    )
    errors = _error_receipts(
        messages,
        ignore_unsolved_goals=application_accepted,
    )
    if proof_closed and errors:
        proof_closed = False

    assumption_world = [
        row["name"]
        for row in request["context"]
        if row.get("role") == "assumption"
    ]
    root_nodes = [
        _state_node(
            goal,
            environment_id=environment["fingerprint"],
            assumption_world=assumption_world,
        )
        for goal in initial_goals
    ]
    child_nodes = [
        _state_node(
            goal,
            environment_id=environment["fingerprint"],
            assumption_world=assumption_world,
        )
        for goal in application_goals
    ]
    edge_seed = {
        "root": [node["node_id"] for node in root_nodes],
        "children": [node["node_id"] for node in child_nodes],
        "action": _application_tactic(candidate),
        "environment": environment["fingerprint"],
    }
    edge_id = "pe_" + hashlib.sha256(
        json.dumps(
            edge_seed,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()[:16]

    argument_terms = candidate.get("arguments", [])
    return {
        "candidate_id": candidate["candidate_id"],
        "declaration": candidate["declaration"],
        "declaration_receipt": _declaration_receipt(
            candidate["declaration"], repo_root
        ),
        "proposal_receipt": candidate.get("proposal_receipt"),
        "application": {
            "tactic": _application_tactic(candidate),
            "argument_terms": argument_terms,
            "substitution_witness": (
                "explicit_argument_terms_plus_Lean_instantiated_subgoals"
                if argument_terms
                else "Lean_instantiated_subgoals_only"
            ),
        },
        "application_accepted": application_accepted,
        "proof_closed": proof_closed,
        "status": (
            "kernel_checked_closed"
            if proof_closed
            else (
                "lean_accepted_open_obligations"
                if application_accepted
                else "lean_rejected"
            )
        ),
        "root_nodes": root_nodes,
        "child_nodes": child_nodes,
        "hyperedge": (
            {
                "edge_id": edge_id,
                "source_nodes": [
                    node["node_id"] for node in root_nodes
                ],
                "action": _application_tactic(candidate),
                "target_nodes": [
                    node["node_id"] for node in child_nodes
                ],
                "child_semantics": "AND",
                "alternative_semantics_at_source": "OR",
                "closed_after_discharge": proof_closed,
            }
            if application_accepted
            else None
        ),
        "discharge_receipts": discharge_receipts,
        "open_obligations": [
            {
                "node_id": node["node_id"],
                "case": node["case"],
                "target": node["target"],
                "rendered": node["rendered"],
            }
            for node in child_nodes
        ],
        "typed_failures": errors,
        "lean_run_receipt": {
            "command": ["lake", "env", "lean", "--stdin", "--json"],
            "return_code": return_code,
            "timed_out": timed_out,
            "source_digest": _sha256_text(source),
            "message_digest": _sha256_text(output),
            "message_count": len(messages),
            "non_json_output": non_json[:8],
            "expected_unsolved_goal_error_ignored": (
                application_accepted and not proof_closed
            ),
        },
        "cost_vector": {
            "lean_calls": 1,
            "open_subgoals_after_application": len(child_nodes),
            "discharge_tactic_count": len(
                candidate.get("discharge_tactics", [])
            ),
            "closed": proof_closed,
        },
    }


def _pareto_frontier(
    transitions: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    accepted = [
        transition
        for transition in transitions
        if transition["application_accepted"]
    ]
    frontier = []
    for candidate in accepted:
        candidate_cost = candidate["cost_vector"]
        dominated = False
        for other in accepted:
            if other is candidate:
                continue
            other_cost = other["cost_vector"]
            no_worse = (
                other_cost["open_subgoals_after_application"]
                <= candidate_cost["open_subgoals_after_application"]
                and other_cost["discharge_tactic_count"]
                <= candidate_cost["discharge_tactic_count"]
                and int(other_cost["closed"]) >= int(candidate_cost["closed"])
            )
            strictly_better = (
                other_cost["open_subgoals_after_application"]
                < candidate_cost["open_subgoals_after_application"]
                or other_cost["discharge_tactic_count"]
                < candidate_cost["discharge_tactic_count"]
                or int(other_cost["closed"])
                > int(candidate_cost["closed"])
            )
            if no_worse and strictly_better:
                dominated = True
                break
        if not dominated:
            frontier.append(
                {
                    "candidate_id": candidate["candidate_id"],
                    "cost_vector": candidate_cost,
                }
            )
    return frontier


def compile_request(
    request: dict[str, Any],
    *,
    repo_root: Path = ROOT,
    environment: dict[str, Any] | None = None,
    timeout_seconds: float = 90.0,
) -> dict[str, Any]:
    """Execute a bounded candidate forest and compile its proof-state packet."""
    _validate_request(request)
    repo_root = repo_root.resolve()
    environment = environment or environment_fingerprint(
        repo_root, timeout_seconds=min(timeout_seconds, 30.0)
    )
    transitions = [
        _run_candidate(
            request,
            candidate,
            repo_root=repo_root,
            environment=environment,
            timeout_seconds=timeout_seconds,
        )
        for candidate in request["candidates"]
    ]
    accepted = [
        transition
        for transition in transitions
        if transition["application_accepted"]
    ]
    open_plans = [
        transition
        for transition in accepted
        if not transition["proof_closed"]
        and transition["open_obligations"]
    ]
    blocker_sets = [
        [row["node_id"] for row in plan["open_obligations"]]
        for plan in open_plans
    ]
    nodes_by_id: dict[str, dict[str, Any]] = {}
    edges = []
    for transition in accepted:
        for node in (
            transition["root_nodes"] + transition["child_nodes"]
        ):
            nodes_by_id[node["node_id"]] = node
        if transition["hyperedge"] is not None:
            edges.append(transition["hyperedge"])
    completion_sets = [
        {
            "candidate_id": plan["candidate_id"],
            "required_open_node_ids": [
                row["node_id"] for row in plan["open_obligations"]
            ],
            "required_open_targets": [
                row["target"] for row in plan["open_obligations"]
            ],
        }
        for plan in open_plans
    ]
    minimal_cuts = minimal_hitting_sets(blocker_sets)
    interventions = minimal_missing_interventions(
        row["required_open_node_ids"] for row in completion_sets
    )
    closed = [
        transition
        for transition in transitions
        if transition["proof_closed"]
    ]
    packet = {
        "schema_version": PACKET_SCHEMA,
        "kind": "proof_state_compilation_packet",
        "goal_id": request["goal_id"],
        "environment_fingerprint": environment,
        "request_digest": _sha256_text(
            json.dumps(
                request,
                sort_keys=True,
                separators=(",", ":"),
            )
        ),
        "goal_identity": {
            "target": request["target"],
            "context_names": [
                row["name"] for row in request["context"]
            ],
        },
        "assumption_world": [
            row["name"]
            for row in request["context"]
            if row.get("role") == "assumption"
        ],
        "candidate_actions": [
            {
                "candidate_id": row["candidate_id"],
                "declaration": row["declaration"],
                "tactic": _application_tactic(row),
            }
            for row in request["candidates"]
        ],
        "lean_tested_transitions": transitions,
        "proof_state_hypergraph": {
            "root_semantics": "OR_over_candidate_hyperedges",
            "edge_child_semantics": "AND_all_generated_subgoals",
            "nodes": sorted(
                nodes_by_id.values(), key=lambda row: row["node_id"]
            ),
            "edges": edges,
        },
        "pareto_frontier": _pareto_frontier(transitions),
        "plan_blocker_sets": completion_sets,
        "minimal_missing_interventions": [
            {
                "node_ids": row,
                "targets": [
                    nodes_by_id[node_id]["target"]
                    for node_id in row
                    if node_id in nodes_by_id
                ],
            }
            for row in interventions
        ],
        "minimal_blocker_cuts": [
            {
                "node_ids": cut,
                "targets": [
                    nodes_by_id[node_id]["target"]
                    for node_id in cut
                    if node_id in nodes_by_id
                ],
            }
            for cut in minimal_cuts
        ],
        "blocker_algebra_semantics": {
            "plan_blocker_sets": (
                "per-plan AND residuals: every listed obligation of one"
                " plan must be discharged for that plan to close"
            ),
            "minimal_missing_interventions": (
                "antichain over plan residuals: supplying every member of"
                " one row completes at least one Lean-reached route"
            ),
            "minimal_blocker_cuts": (
                "minimal transversals of the plan residuals: the smallest"
                " removals meeting every known route; a cut is not an"
                " addition plan"
            ),
        },
        "closed_proof_receipts": [
            {
                "candidate_id": transition["candidate_id"],
                "lean_run_receipt": transition["lean_run_receipt"],
                "discharge_receipts": transition["discharge_receipts"],
            }
            for transition in closed
        ],
        "abstention_receipt": (
            None
            if closed
            else {
                "status": (
                    "blocked_with_Lean_instantiated_obligations"
                    if open_plans
                    else "all_candidates_rejected_by_Lean"
                ),
                "reentry": (
                    "supply one blocker target or add a new bounded "
                    "candidate action, then replay the packet"
                ),
            }
        ),
        "authority_posture": {
            "transition": (
                "Lean elaboration certifies that the action produced the "
                "recorded subgoals"
            ),
            "closed_proof": (
                "only return_code_zero_with_no_remaining_goals is a "
                "kernel-checked local proof receipt"
            ),
            "planning": (
                "hypergraph ranking, blocker cuts, and counterfactual "
                "interpretation remain advisory"
            ),
            "status_and_exposition": (
                "claim registries and authored papers remain separate "
                "authorities"
            ),
        },
        "omissions_and_reentry": {
            "candidate_limit": MAX_CANDIDATES,
            "candidate_count": len(request["candidates"]),
            "omitted_candidate_count": 0,
            "recursive_search": "not_yet_enabled",
            "bridge_synthesis": "not_claimed",
            "expansion": (
                "submit another explicit request at a generated child target"
            ),
        },
    }
    packet["packet_bytes"] = len(
        json.dumps(packet, sort_keys=True).encode("utf-8")
    )
    return packet


def pilot_requests() -> list[dict[str, Any]]:
    series = "(∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)"
    target = (
        "totientTail (N + h) - totientTail N ∈ "
        "Set.range ((↑) : ℤ → ℝ)"
    )
    common_context = [
        {"name": "r", "binder": "(r : ℚ)", "role": "term"},
        {
            "name": "hS",
            "binder": f"(hS : {series} = (r : ℝ))",
            "role": "assumption",
        },
        {"name": "h", "binder": "(h : ℕ)", "role": "term"},
        {"name": "N", "binder": "(N : ℕ)", "role": "term"},
    ]
    declaration = (
        "Erdos249257.TotientTailPeriodKiller."
        "tail_diff_int_of_den_dvd"
    )
    blocked = {
        "schema_version": REQUEST_SCHEMA,
        "goal_id": "integer_tail_without_divisibility",
        "imports": ["Erdos249257"],
        "opens": [
            "Erdos249257",
            "Erdos249257.TotientTailPeriodKiller",
        ],
        "context": common_context,
        "target": target,
        "candidates": [
            {
                "candidate_id": "tail_period_killer",
                "declaration": declaration,
                "arguments": ["r", "hS", "h", "N"],
                "discharge_tactics": [],
                "proposal_receipt": (
                    "static --proof-plan terminal candidate"
                ),
            }
        ],
    }
    ready = json.loads(json.dumps(blocked))
    ready["goal_id"] = "integer_tail_with_divisibility"
    ready["context"].append(
        {
            "name": "hdvd",
            "binder": (
                "(hdvd : (r.den : ℕ) ∣ 2 ^ N * (2 ^ h - 1))"
            ),
            "role": "assumption",
        }
    )
    ready["candidates"][0]["discharge_tactics"] = ["assumption"]
    curvature = {
        "schema_version": REQUEST_SCHEMA,
        "goal_id": "curvature_supply_control",
        "imports": ["Erdos249257"],
        "opens": [
            "Erdos249257",
            "Erdos249257.TotientTailPeriodKiller",
        ],
        "context": [
            {
                "name": "hsupply",
                "binder": "(hsupply : SharpCurvatureSupply)",
                "role": "assumption",
            }
        ],
        "target": f"Irrational {series}",
        "candidates": [
            {
                "candidate_id": "curvature_supply_consumer",
                "declaration": (
                    "Erdos249257.TotientTailPeriodKiller."
                    "irrational_totientSeries_of_sharpCurvatureSupply"
                ),
                "arguments": [],
                "discharge_tactics": ["assumption"],
                "proposal_receipt": (
                    "static --proof-plan context-ready candidate"
                ),
            }
        ],
    }
    return [blocked, ready, curvature]


def compile_pilot_suite(
    *,
    repo_root: Path = ROOT,
    timeout_seconds: float = 90.0,
) -> dict[str, Any]:
    environment = environment_fingerprint(
        repo_root, timeout_seconds=min(timeout_seconds, 30.0)
    )
    packets = [
        compile_request(
            request,
            repo_root=repo_root,
            environment=environment,
            timeout_seconds=timeout_seconds,
        )
        for request in pilot_requests()
    ]
    cases = {packet["goal_id"]: packet for packet in packets}
    blocked = cases["integer_tail_without_divisibility"]
    ready = cases["integer_tail_with_divisibility"]
    curvature = cases["curvature_supply_control"]
    blocked_targets = [
        row["target"]
        for transition in blocked["lean_tested_transitions"]
        for row in transition["open_obligations"]
    ]
    causal_receipt = {
        "intervention": "add_exact_hdvd_assumption",
        "control_goal_id": blocked["goal_id"],
        "intervention_goal_id": ready["goal_id"],
        "same_target": blocked["goal_identity"]["target"]
        == ready["goal_identity"]["target"],
        "same_candidate_action": (
            blocked["candidate_actions"] == ready["candidate_actions"]
        ),
        "control_closed": bool(blocked["closed_proof_receipts"]),
        "intervention_closed": bool(ready["closed_proof_receipts"]),
        "control_open_targets": blocked_targets,
        "added_assumptions": sorted(
            set(ready["assumption_world"])
            - set(blocked["assumption_world"])
        ),
        "effect": (
            "exact_obligation_is_causally_sufficient_for_this_transition"
            if (
                not blocked["closed_proof_receipts"]
                and ready["closed_proof_receipts"]
                and blocked_targets
            )
            else "causal_effect_not_established"
        ),
        "claim_ceiling": (
            "the intervention closes this exact Lean application; it does "
            "not establish that the assumption is globally necessary for "
            "every possible proof"
        ),
    }
    packet = {
        "schema_version": PILOT_SCHEMA,
        "kind": "proof_state_compiler_pilot",
        "environment_fingerprint": environment,
        "cases": cases,
        "causal_obstruction_receipt": causal_receipt,
        "pilot_verdict": {
            "blocked_control_is_precise": bool(blocked_targets)
            and not blocked["closed_proof_receipts"],
            "counterfactual_closes": bool(ready["closed_proof_receipts"]),
            "independent_ready_control_closes": bool(
                curvature["closed_proof_receipts"]
            ),
        },
        "claim_ceiling": (
            "bounded vertical slice of exact Lean transitions, one causal "
            "obstruction intervention, and one independent control; not "
            "recursive proof search or autonomous lemma invention"
        ),
    }
    packet["packet_bytes"] = len(
        json.dumps(packet, sort_keys=True).encode("utf-8")
    )
    return packet


def _load_request(args: argparse.Namespace) -> dict[str, Any] | None:
    if args.request_file is not None:
        return json.loads(args.request_file.read_text(encoding="utf-8"))
    if args.request_stdin:
        import sys

        return json.load(sys.stdin)
    return None


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Compile bounded Lean application transitions into an AND/OR "
            "proof-state packet."
        )
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--pilot-controls",
        action="store_true",
        help="run the blocked, counterfactual, and curvature controls",
    )
    mode.add_argument(
        "--request-file",
        type=Path,
        help="read one proof-state request JSON file",
    )
    mode.add_argument(
        "--request-stdin",
        action="store_true",
        help="read one proof-state request JSON object from stdin",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=ROOT,
        help="Lean repository root (default: this checkout)",
    )
    parser.add_argument(
        "--timeout-seconds",
        type=float,
        default=90.0,
        help="timeout for each Lean transition",
    )
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args()

    request = _load_request(args)
    if request is not None:
        packet = compile_request(
            request,
            repo_root=args.repo_root,
            timeout_seconds=args.timeout_seconds,
        )
    else:
        packet = compile_pilot_suite(
            repo_root=args.repo_root,
            timeout_seconds=args.timeout_seconds,
        )
    if packet.get("packet_bytes", 0) > MAX_PACKET_BYTES:
        raise SystemExit(
            "proof_state_compiler: packet exceeds 64000 bytes; "
            "reduce the candidate list or context"
        )
    print(
        json.dumps(
            packet,
            indent=None if args.compact else 2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
