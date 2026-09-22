#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Replay paper-selected premise substitutions with the existing Lean compiler.

This file supplies no new prover or similarity metric. The research choices
are explicit request files; Lean determines application and closure.
"""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
import proof_state_compiler as compiler


def run(request_paths, output):
    output.mkdir(parents=True, exist_ok=True)
    rows = []
    environment = compiler.environment_fingerprint(ROOT)
    for path in request_paths:
        request = json.loads(path.read_text())
        packet = compiler.compile_request(request, repo_root=ROOT,
                                          environment=environment,
                                          timeout_seconds=120)
        (output / (path.stem + "-result.json")).write_text(
            json.dumps(packet, indent=2) + "\n")
        for transition in packet["lean_tested_transitions"]:
            rows.append({"question": request["goal_id"],
                         "candidate": transition["candidate_id"],
                         "application_accepted": transition["application_accepted"],
                         "proof_closed": transition["proof_closed"],
                         "obligations_after_application": transition["open_obligations"],
                         "remaining_obligations": ([] if transition["proof_closed"]
                                                   else transition["open_obligations"])})
    summary = {"evidence": "Lean application and remaining-goal traces",
               "boundary": "Closure proves the displayed conditional statement; it does not establish novelty or any unstated premise.",
               "transitions": rows}
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("requests", nargs="+", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    run(args.requests, args.output)
