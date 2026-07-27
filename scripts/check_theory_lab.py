#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Contract for the theory-laboratory layer.

The layer's value depends entirely on not being able to lie. Each rule below
exists because a specific failure mode has either already happened in this
repository or is the obvious next one.

    1  mechanism evidence resolves        an induced mechanism citing a declaration
                                          that does not exist is a fabricated
                                          explanation; this caught invented
                                          declaration names once already
    2  mechanism nodes resolve            a mechanism must explain statements that
                                          exist
    3  mechanisms are predictive          invariant, transformation and controlled
                                          observable are all required; a record
                                          without them is a label, not a mechanism
    4  failures are grounded              a claimed failure cites formal evidence
                                          or declares itself a scope argument
    5  siblings are enumerated            a barrier must say which sibling
                                          mechanisms it does NOT reach; omitting
                                          this produced a near-published overclaim
                                          about the squarefree obstruction
    6  capsules are attached              no capsule without its mechanism
    7  predictions are immutable          an outcome cites a prediction fingerprint
                                          that still recomputes, so a prediction
                                          cannot be rewritten after the result
    8  holdouts do not leak               the held-out declaration is absent from
                                          the cut commit
    9  evaluations are attributable       a result names its item, arm and packet
   10  novelty is reviewed                no novelty assertion without a prior-art
                                          state that is not 'not_assessed'
   11  controls accompany effects         a mechanism-arm result is not reportable
                                          without a control arm and both baseline
                                          arms; comparable published work shows
                                          such gains vanish under compute matching
"""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ATLAS = ROOT / "docs" / "declaration_atlas.json"
CORPUS = ROOT / "docs" / "semantic_corpus.json"
LAB = ROOT / "docs" / "theory_lab.json"

sys.path.insert(0, str(ROOT / "scripts"))
from build_theory_lab import (  # noqa: E402
    BENCHMARK_ARMS,
    CONTROL_ARMS,
    INTERVENTION_OPERATORS,
    OUTCOME_STATES,
    prediction_fingerprint,
)

REQUIRED_MECHANISM_FIELDS = (
    "mechanism_id",
    "human_name",
    "core_idea",
    "invariant",
    "observable_controlled",
    "transformation",
    "proves_when_hypotheses_hold",
)


def git(*args: str) -> tuple[int, str]:
    proc = subprocess.run(
        ("git",) + args, cwd=str(ROOT), capture_output=True, text=True, check=False
    )
    return proc.returncode, proc.stdout


def main() -> int:
    if not LAB.exists():
        print("check_theory_lab: docs/theory_lab.json is missing", file=sys.stderr)
        return 1

    lab = json.loads(LAB.read_text(encoding="utf-8"))
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    corpus = json.loads(CORPUS.read_text(encoding="utf-8"))

    declarations = {d["name"] for d in atlas["declarations"]}
    nodes = {n["id"] for n in corpus["statement_nodes"]}

    mechanisms = lab.get("mechanisms", [])
    capsules = lab.get("capsules", [])
    interventions = lab.get("interventions", [])
    receipts = lab.get("failure_receipts", [])
    items = lab.get("benchmark", {}).get("items", [])
    results = lab.get("benchmark", {}).get("results", [])

    mech_ids = {m.get("mechanism_id") for m in mechanisms}
    failures: list[str] = []

    # 1 / 2 / 3  mechanism integrity
    seen: set[str] = set()
    for mech in mechanisms:
        mid = mech.get("mechanism_id", "<unnamed>")
        if mid in seen:
            failures.append(f"duplicate mechanism id {mid}")
        seen.add(mid)

        for field in REQUIRED_MECHANISM_FIELDS:
            if not str(mech.get(field, "")).strip():
                failures.append(f"mechanism {mid} has empty required field {field}")

        for name in mech.get("realising_declarations", ()) or ():
            if name not in declarations:
                failures.append(
                    f"mechanism {mid} cites declaration {name} not present in the atlas"
                )
        if not (mech.get("realising_declarations") or ()):
            failures.append(f"mechanism {mid} cites no realising declaration")

        for node in mech.get("statement_nodes", ()) or ():
            if node not in nodes:
                failures.append(f"mechanism {mid} cites statement node {node} that does not exist")

        # 4  failures are grounded
        for failure in mech.get("sharp_failures", ()) or ():
            text = str(failure)
            grounded = any(name in text for name in declarations) or any(
                node in text for node in nodes
            )
            if not grounded and mech.get("sharp_failure_basis") != "scope_argument":
                failures.append(
                    f"mechanism {mid} claims a sharp failure that names no known "
                    f"declaration or node and is not declared a scope argument: "
                    f"{text[:80]!r}"
                )

    # 5  siblings are enumerated
    for receipt in receipts:
        rid = receipt.get("receipt_id", "<unnamed>")
        ruled_out = receipt.get("mechanism_ruled_out")
        if not ruled_out:
            continue
        if ruled_out not in mech_ids:
            failures.append(f"receipt {rid} rules out unknown mechanism {ruled_out}")
        unreached = receipt.get("mechanisms_not_ruled_out")
        if unreached is None:
            failures.append(
                f"receipt {rid} rules out {ruled_out} without recording which sibling "
                "mechanisms it does NOT reach"
            )
        elif not unreached and not str(receipt.get("siblings_enumerated_reason", "")).strip():
            failures.append(
                f"receipt {rid} claims no surviving sibling mechanism but gives no reason; "
                "an empty list must be justified"
            )
        for sibling in unreached or ():
            if sibling not in mech_ids:
                failures.append(f"receipt {rid} names unknown surviving mechanism {sibling}")

    # 6  capsules are attached
    for capsule in capsules:
        cid = capsule.get("mechanism_id")
        if cid not in mech_ids:
            failures.append(f"capsule cites unknown mechanism {cid}")
        for field in ("one_sentence", "five_minute", "transfer_challenge"):
            if not str(capsule.get(field, "")).strip():
                failures.append(f"capsule {cid} has empty {field}")

    # 7  predictions are immutable
    for record in interventions:
        iid = record.get("intervention_id", "<unnamed>")
        operator = record.get("operator")
        if operator not in INTERVENTION_OPERATORS:
            failures.append(f"intervention {iid} uses unknown operator {operator}")

        state = record.get("outcome_state", "predicted_only")
        if state not in OUTCOME_STATES:
            failures.append(f"intervention {iid} has unknown outcome_state {state}")

        for key in ("predicted_preserved", "predicted_broken"):
            for name in record.get(key, ()) or ():
                if name not in mech_ids:
                    failures.append(f"intervention {iid} {key} names unknown mechanism {name}")

        recomputed = prediction_fingerprint(record)
        stored = record.get("prediction_fingerprint")
        if stored and stored != recomputed:
            failures.append(
                f"intervention {iid} prediction fingerprint does not recompute; the "
                "prediction was edited after it was stamped"
            )

        if state in ("confirmed", "refuted", "partially_confirmed"):
            if not str(record.get("outcome_evidence", "")).strip():
                failures.append(
                    f"intervention {iid} reports outcome {state} with no outcome_evidence"
                )
            if not record.get("prediction_fingerprint"):
                failures.append(
                    f"intervention {iid} reports outcome {state} without a stamped prediction"
                )

    # 8  holdouts do not leak
    for item in items:
        target = item.get("target")
        cut = item.get("cut_commit")
        iid = item.get("item_id", target or "<unnamed>")
        if not target or not cut:
            failures.append(f"benchmark item {iid} lacks a target or cut_commit")
            continue
        if target not in declarations:
            failures.append(f"benchmark item {iid} holds out {target}, absent from the atlas")
        code, _ = git("merge-base", "--is-ancestor", cut, "HEAD")
        if code != 0:
            # Reconciliation branches may port a checked declaration without
            # making its original development branch an ancestor. Preserve
            # the real holdout cut when it is proven to precede the recorded
            # introducing commit; requiring HEAD ancestry would force a fake
            # replacement cut and destroy benchmark provenance.
            introducing = item.get("introducing_commit")
            lineage_code, _ = git(
                "merge-base",
                "--is-ancestor",
                str(cut),
                str(introducing or ""),
            )
            if not introducing or lineage_code != 0:
                failures.append(
                    f"benchmark item {iid} cut {cut[:8]} is neither an ancestor "
                    "of HEAD nor of its recorded introducing commit"
                )
                continue
        code, out = git("grep", "-l", target, cut, "--", "*.lean")
        if code == 0 and out.strip():
            failures.append(
                f"benchmark item {iid} LEAKS: {target} is already present at cut {cut[:8]}"
            )

    # 9  evaluations are attributable
    item_ids = {i.get("item_id") for i in items}
    for result in results:
        rid = result.get("result_id", "<unnamed>")
        if result.get("item_id") not in item_ids:
            failures.append(f"benchmark result {rid} names unknown item {result.get('item_id')}")
        if result.get("arm") not in BENCHMARK_ARMS:
            failures.append(f"benchmark result {rid} uses unknown arm {result.get('arm')}")
        if not str(result.get("packet_cut_commit", "")).strip():
            failures.append(f"benchmark result {rid} does not record the packet cut commit")
        if result.get("self_reported_files_read") is None:
            failures.append(
                f"benchmark result {rid} carries no leakage self-report; an evaluation "
                "with no record of what the agent read is not attributable"
            )

    # 11  a mechanism effect is not reportable without its controls
    #
    # This rule is the one that keeps the benchmark honest. Published results in
    # exactly this area show that library-learning gains disappear under compute
    # matching, and that unrelated subgraphs reproduce full-graph behaviour. So a
    # recovery under the mechanism arm, on its own, is not evidence that the
    # mechanism did anything -- it is consistent with the agent simply having
    # more plausible mathematical prose in front of it. The contract therefore
    # refuses to let a mechanism-arm success stand in the record unless the same
    # item was also run under a control.
    by_item: dict[str, set[str]] = {}
    for result in results:
        by_item.setdefault(result.get("item_id"), set()).add(result.get("arm"))
    for item_id, arms in by_item.items():
        if "mechanism" not in arms and "negative" not in arms:
            continue
        if not (set(arms) & set(CONTROL_ARMS)):
            failures.append(
                f"benchmark item {item_id} has a mechanism-arm result with no control "
                f"arm ({' or '.join(CONTROL_ARMS)}); a mechanism effect is not "
                "reportable without one"
            )
        if "graph" not in arms or "signatures" not in arms:
            failures.append(
                f"benchmark item {item_id} has a mechanism-arm result without both "
                "baseline arms; the comparison has no floor"
            )

    # 10  novelty is reviewed
    for record in mechanisms + receipts:
        rid = record.get("mechanism_id") or record.get("receipt_id") or "<unnamed>"
        if record.get("novelty_claim"):
            state = record.get("prior_art_state")
            if not state or state == "not_assessed":
                failures.append(
                    f"{rid} asserts novelty with prior_art_state {state!r}; a novelty "
                    "assertion requires a reviewed prior-art state"
                )

    summary = lab.get("summary", {})
    print(
        f"check_theory_lab: {summary.get('mechanisms', 0)} mechanisms, "
        f"{summary.get('interventions', 0)} interventions, "
        f"{summary.get('failure_receipts', 0)} receipts, "
        f"{summary.get('benchmark_items', 0)} items, "
        f"{summary.get('benchmark_results', 0)} results"
    )
    print(
        f"  explained {summary.get('statement_nodes_explained', 0)}/"
        f"{summary.get('statement_nodes_total', 0)} statement nodes "
        f"({summary.get('explained_fraction', 0):.1%})"
    )
    arm_tally = summary.get("arm_tally", {})
    for arm in BENCHMARK_ARMS:
        bucket = arm_tally.get(arm)
        if bucket:
            print(
                f"  arm {arm:<11} runs={bucket['runs']:<3} "
                f"statement={bucket['statement_recovered']} "
                f"mechanism={bucket['mechanism_recovered']}"
            )

    if failures:
        print(f"\ncheck_theory_lab: {len(failures)} contract failure(s)", file=sys.stderr)
        for failure in failures:
            print(f"  FAIL {failure}", file=sys.stderr)
        return 1

    print("\ncheck_theory_lab: contract satisfied")
    return 0


if __name__ == "__main__":
    sys.exit(main())
