#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Use a semantic slice to assemble and kernel-check a new scratch corollary."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any

import query_corpus


DOGFOOD_SCHEMA = "erdos249257-semantic-proof-dogfood/1"
DEFAULT_QUERY = (
    "which premises let either sharp curvature or exponent only three "
    "transport prove irrationality of the totient series"
)
REQUIRED_DECLARATIONS = {
    "irrational_totientSeries_of_sharpCurvatureSupply",
    "irrational_totient_series_of_exponentOnlyThreeTransportSupply",
}
SCRATCH_THEOREM = """\
import Erdos249257.CurvatureCarry
import Erdos249257.ExponentOnlyTransport

open scoped BigOperators

/- A query-derived composition of two independent conditional proof sockets.
   This does not assert either open supply. -/
theorem semanticCompiler_disjunctiveSupplySocket
    (h :
      Erdos249257.TotientTailPeriodKiller.SharpCurvatureSupply ∨
        Erdos249257.ExponentOnlyTransport.ExponentOnlyThreeTransportSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  rcases h with hcurvature | htransport
  · exact
      Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_sharpCurvatureSupply
        hcurvature
  · exact
      Erdos249257.ExponentOnlyTransport.irrational_totient_series_of_exponentOnlyThreeTransportSupply
        htransport
"""


def retrieved_declarations(packet: dict[str, Any]) -> set[str]:
    names: set[str] = set()
    for cell in packet["semantic_cells"]:
        if cell["kind"] == "declaration":
            names.add(cell["handle"])
        elif cell["kind"] == "claim":
            names.update(
                row["name"]
                for row in cell["content"]["claim_record"].get(
                    "declarations", []
                )
            )
    return names


def dogfood_packet(query: str) -> dict[str, Any]:
    ranked_search = query_corpus.search_packet(
        query, query_corpus.MAX_SEMANTIC_CELLS
    )
    ranked_declarations = {
        query_corpus.semantic_result_handle(result)
        for result in ranked_search["results"]
        if result["kind"] == "declaration"
    }
    semantic_slice = query_corpus.semantic_slice_packet(query, 4)
    recovered = retrieved_declarations(semantic_slice)
    missing = sorted(REQUIRED_DECLARATIONS - recovered)
    if missing:
        return {
            "kind": "semantic_proof_dogfood",
            "schema_version": DOGFOOD_SCHEMA,
            "query": query,
            "passed": False,
            "stage": "semantic_retrieval",
            "retrieved_declarations": sorted(recovered),
            "ranked_search_recovered_required_declarations": sorted(
                REQUIRED_DECLARATIONS & ranked_declarations
            ),
            "missing_required_declarations": missing,
            "semantic_slice_id": semantic_slice.get("slice_id"),
        }

    started = time.monotonic()
    with tempfile.TemporaryDirectory(
        prefix="semantic-proof-dogfood-"
    ) as temp_dir:
        source = Path(temp_dir) / "SemanticCompilerDogfood.lean"
        source.write_text(SCRATCH_THEOREM, encoding="utf-8")
        completed = subprocess.run(
            ["lake", "env", "lean", str(source)],
            cwd=query_corpus.ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
    elapsed = time.monotonic() - started
    return {
        "kind": "semantic_proof_dogfood",
        "schema_version": DOGFOOD_SCHEMA,
        "query": query,
        "passed": completed.returncode == 0,
        "stage": "kernel_validation",
        "semantic_slice_id": semantic_slice["slice_id"],
        "semantic_operator": semantic_slice["query_interpretation"]["operator"][
            "id"
        ],
        "retrieved_declarations": sorted(recovered),
        "required_declarations": sorted(REQUIRED_DECLARATIONS),
        "ranked_search_recovered_required_declarations": sorted(
            REQUIRED_DECLARATIONS & ranked_declarations
        ),
        "semantic_expansion_gain": (
            len(REQUIRED_DECLARATIONS & recovered)
            - len(REQUIRED_DECLARATIONS & ranked_declarations)
        ),
        "scratch_theorem_sha256": hashlib.sha256(
            SCRATCH_THEOREM.encode("utf-8")
        ).hexdigest(),
        "scratch_posture": (
            "temporary_new_corollary_not_a_new_supply_claim_or_open_problem_solution"
        ),
        "lean_command": "lake env lean <temporary>/SemanticCompilerDogfood.lean",
        "lean_exit_code": completed.returncode,
        "lean_output": completed.stdout,
        "elapsed_seconds": round(elapsed, 3),
        "authority_posture": (
            "semantic_compiler_selects_premises;Lean_kernel_validates_the_composition"
        ),
    }


def render_card(packet: dict[str, Any]) -> str:
    if packet["stage"] == "semantic_retrieval":
        return (
            f"semantic proof dogfood | FAIL retrieval "
            f"| missing={','.join(packet['missing_required_declarations'])}"
        )
    return (
        f"semantic proof dogfood {packet['schema_version']} "
        f"| {'PASS' if packet['passed'] else 'FAIL'} "
        f"| operator={packet['semantic_operator']} "
        f"| declarations={len(packet['required_declarations'])} "
        f"| lean_exit={packet['lean_exit_code']} "
        f"| elapsed={packet['elapsed_seconds']}s"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--query", default=DEFAULT_QUERY)
    parser.add_argument("--format", choices=("json", "card"), default="card")
    args = parser.parse_args()
    packet = dogfood_packet(args.query)
    if args.format == "json":
        print(json.dumps(packet, ensure_ascii=False, indent=2))
    else:
        print(render_card(packet))
    return 0 if packet["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
