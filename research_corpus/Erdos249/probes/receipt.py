"""One-call durable receipt publishing for formal-math probes, any problem.

A probe that finishes without a receipt is ephemeral: nobody can replay it,
nobody can tell which analytic mechanism it bears on, and nobody notices when
the sources it read have since changed.  This wraps the three things a probe
needs -- the typed experiment contract, the mechanism bindings that make it
addressable from a research packet, and content hashes of every source it
depends on -- behind a single call, so writing a bound receipt is cheaper than
not writing one.

Problem-agnostic by construction: `problem_id` is a parameter and the packet is
resolved from it, so the same call works for Erdos 68, 243, 249, 251, 257, 269,
1041 and 1049.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from system.lib.formal_math_experiment_contract import (  # noqa: E402
    build_experiment_contract,
    source_record,
)
from system.lib.formal_math_probe_registry import mechanism_bindings  # noqa: E402

PACKET_ROOTS = ("formal_math/erdos257_period_noncollapse/ErdosProblems",)


def packet_ref(problem_id: str) -> str:
    """Repository-relative research packet for a problem id like `erdos_269`."""
    number = problem_id.split("_")[-1]
    for root in PACKET_ROOTS:
        candidate = f"{root}/Erdos{number}/research_packet.json"
        if (REPO_ROOT / candidate).exists():
            return candidate
    raise FileNotFoundError(f"no research packet for {problem_id!r}")


def publish(
    *,
    out_path: str,
    problem_id: str,
    hypothesis_id: str,
    hypothesis_statement: str,
    probe_id: str,
    probe_question: str,
    computation: str,
    falsifier: str,
    stop_condition: str,
    survival_consequence: str,
    falsification_consequence: str,
    consumer_ref: str,
    analysis_refs: Iterable[str],
    source_refs: Iterable[str],
    result_status: str,
    result_summary: str,
    payload: Mapping[str, Any],
    motivated_by: Iterable[str],
    eliminates: Iterable[str] = (),
    opens: Iterable[str] = (),
    supports: Iterable[str] = (),
    binding_rationale: str = "",
    progress_class: str | None = None,
    decision_basis: str | None = None,
    next_analytic_target: str | None = None,
    resource_bounds: Mapping[str, int] | None = None,
) -> Path:
    """Write a receipt carrying the contract, the bindings, and source hashes."""
    packet = packet_ref(problem_id)
    packet_data = json.loads((REPO_ROOT / packet).read_text(encoding="utf-8"))
    target = packet_data.get("target") or {}

    analysis = list(dict.fromkeys([*analysis_refs, packet]))
    sources = list(dict.fromkeys(source_refs))

    contract = build_experiment_contract(
        problem_id=problem_id,
        target_statement=target.get("statement", "see research packet target"),
        claim_ceiling=packet_data.get("claim_ceiling", "see research packet"),
        hypothesis_id=hypothesis_id,
        hypothesis_statement=hypothesis_statement,
        probe_id=probe_id,
        probe_question=probe_question,
        computation=computation,
        falsifier=falsifier,
        stop_condition=stop_condition,
        survival_consequence=survival_consequence,
        falsification_consequence=falsification_consequence,
        consumer_ref=consumer_ref,
        analysis_refs=analysis,
        source_refs=sources,
        result_status=result_status,
        result_summary=result_summary,
        progress_class=progress_class,
        decision_basis=decision_basis,
        next_analytic_target=next_analytic_target,
        resource_bounds=resource_bounds,
    )
    bindings = mechanism_bindings(
        problem_id=problem_id,
        motivated_by=motivated_by,
        eliminates=eliminates,
        opens=opens,
        supports=supports,
        rationale=binding_rationale,
    )
    bound_ids = sorted(
        {str(x) for group in (motivated_by, eliminates, opens, supports)
         for x in group if str(x)}
    )
    receipt = {
        "probe_id": probe_id,
        "experiment_contract": contract,
        "mechanism_bindings": bindings,
        # The packet is hashed twice: whole-file, and scoped to just the
        # mechanism entries this receipt binds to.  Without the scoped digest
        # every later deposit into the packet marks this receipt stale and
        # forces an unrelated rerun.
        "sources": [
            source_record(REPO_ROOT, ref, scope_ids=bound_ids)
            for ref in (*analysis, *sources)
        ],
        "result": payload,
    }
    destination = REPO_ROOT / out_path
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(receipt, indent=1) + "\n")
    return destination
