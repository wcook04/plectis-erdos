<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Theory laboratory

The semantic corpus records statements and their relationships. This laboratory
records reusable proof mechanisms, predicts what breaks under a mathematical
perturbation, and prepares historical holdouts for testing recovery. A readable
explanation alone does not establish improved recovery.

## Files

`mechanisms.json`, `capsules.json`, `interventions.json`, `receipts.json`,
`benchmark_items.json`, `benchmark_results.json` are **authored**.
`docs/theory_lab.json` is **generated** from them by
`scripts/build_theory_lab.py` and guarded by `scripts/check_theory_lab.py`.

## Preparing a recovery packet

`scripts/build_benchmark_packet.py` exports the exact `cut_commit` registered in
`benchmark_items.json`. It does not select a newer cutoff when history is
reconciled. The export contains the tracked historical files without a `.git`
directory or shared object database. Existing destinations are refused; prepare
each arm in a fresh directory outside every Git worktree.

The `signatures` arm gives a participant the full historical source for ordinary
search. Other arms add the selected graph, mechanisms, or failure records.
Records citing unavailable declarations are removed, and capsule transfer
challenges are withheld. An evaluator receipt records the frozen cutoff, future
commit, and answer key outside the participant export. Those identities are
excluded from its `docs/_packet/MANIFEST.json`.

This is packet preparation, not a scored evaluation. Every manifest records
`evaluation_ready: false`. Before recording results, bind a participant runner
that cannot read the evaluator's filesystem or retrieve later source, use fresh
participants, and fix the question, scoring rubric, model, search tools, and
compute budget. Review the current concepts and explanatory prose separately:
checking their declaration references does not prove that their wording is free
of answer hints. The shuffled and off-problem controls also need capsule and
prose-volume matching; their current payloads do not implement that comparison.

Packet construction and repository checks alone provide no evidence that the
semantic layer improves mathematical recovery.

## What a mechanism is

Each record names an `invariant`, a `transformation`, and the
`observable_controlled`. It should explain whether a new nearby statement is
reachable by that method. A theorem-family label or dependency cluster alone
does not supply this explanation.

## Why the negative space is first-class

`receipts.json` records failed generalisations and their scope. Every receipt
ruling out a mechanism must name unaffected siblings: a barrier to one
certificate engine may leave a weaker engine available.

## Prediction integrity

An intervention records its prediction before the outcome is known.
`scripts/build_theory_lab.py --stamp` fingerprints the predictive fields and
refuses an outcome-bearing record. The checker rejects a changed fingerprint.

## Packet arms

The four main arms add successive layers to the same frozen source export:

    signatures   the historical source export alone
    graph        + statement graph, filtered to the cut
    mechanism    + mechanism records and capsules, filtered to the cut
    negative     + failure receipts

```bash
python3 scripts/build_benchmark_packet.py --target NAME --arm mechanism --dest /tmp/cut --answer-key /tmp/key.json
```

Use a target registered in `benchmark_items.json`. The answer key is refused if
it would be written inside the packet or replace an existing file. Keep it in
the evaluator's filesystem when arranging a participant run.

## Routes

```bash
python3 scripts/query_semantic.py mechanisms --problem 257
python3 scripts/query_semantic.py mechanism <mechanism_id>
python3 scripts/query_semantic.py explains <node_id>
python3 scripts/query_semantic.py unexplained
python3 scripts/query_semantic.py interventions
python3 scripts/query_semantic.py discrepancies
python3 scripts/query_semantic.py receipts
python3 scripts/query_semantic.py benchmark
```

`unexplained` reports statements not covered by the recorded mechanisms.

## Return to public evidence

Follow the [complete eight-problem return matrix](../../reference/SOURCE_MAP.md#complete-eight-problem-return-matrix)
back to the problem's source, paper and open boundary. Exact reverse routes are
available through `python3 scripts/query_corpus.py` with `--source
<module.lean:line>`, `--paper-anchor <TeX_label_or_source_ref>`, or
`--module <module_path_or_sigil>`. The module route includes its synopsis,
declarations, source identity, attached claims and route-memory context.

The generated [Formal Conjectures crosswalk](../../verification/FORMAL_CONJECTURES_CROSSWALK.md)
binds each of the eight problems to its pinned upstream declaration, source
hash and local route. Following a link does not verify a lab explanation.

## What this layer does not decide

The [round-8 transfer record](../../research-commons/rounds/round8/README.md)
links ordinary proofs of separated-cut transcendence, independent-clock
classification, calibrated height countermodels and signed interpolation.
Their reusable mechanisms and surviving boundaries are explicit in the papers
and claim registry. They are not inserted into the formal mechanism inventory:
that inventory's declaration links would otherwise suggest kernel evidence
that these infinite results do not yet have.

Lean owns proof correctness; the semantic corpus owns statement records. Lab
mechanisms do not establish correctness, novelty or significance.
`docs/methodology.json::blinded_recovery_evaluation` defines the separate
evidence required for recovery results.
