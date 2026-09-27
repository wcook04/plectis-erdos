<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Theory laboratory

The semantic corpus answers *what is proved and how statements relate*. This
layer asks three further questions:

- **Which few mechanisms underlie those proofs?** The reusable reasons theorems
  hold and methods fail, rather than the theorems themselves.
- **What survives when the mathematics is deliberately perturbed?** A typed
  intervention shifts a coefficient, changes a base, or drops a structural
  precondition, records which mechanisms it predicts will break, and then checks.
- **Does the explanation transfer to unseen mathematics?** A holdout uses the
  commit before a theorem landed and measures whether the layer helps recover it.

The third question tests the first two: a mechanism that reads well but does not
improve held-out recovery is a story, not an explanation.

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

An invariant, plus a transformation, plus the observable it controls. The test is
predictive, not descriptive: given only the record, could a mathematician who has
never seen this repository decide whether a *new* nearby statement is reachable
by it? If not, the record is a label and the contract rejects it for missing one
of `invariant`, `transformation`, `observable_controlled`.

A theorem family is not a mechanism. A restatement is not a mechanism. A
dependency cluster is not a mechanism.

## Why the negative space is first-class

Most formal libraries record what worked. This corpus also keeps blocked engines,
failed generalisations, and repairs that expose the next precondition.
`receipts.json` requires each receipt ruling out a mechanism to name the sibling
mechanisms it does **not** reach.

A barrier here nearly got recorded as closing a family of certificate engines
although a weaker low-carry engine survived it. The contract now prevents a
barrier from being recorded without naming unaffected siblings.

## Prediction integrity

An intervention records what it predicts *before* the outcome is known.
`scripts/build_theory_lab.py --stamp` fingerprints exactly the predictive fields;
the checker recomputes and rejects a mismatch, and `--stamp` refuses to stamp a
record whose outcome is already known. So "we predicted this" is auditable rather
than a story assembled afterwards.

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

`unexplained` is the honest one. A large residual is a finding about the
mechanism basis, not a bookkeeping gap, and it is reported rather than hidden.

## Return to public evidence

A theory-lab record explains a mechanism; it is not proof authority or a public
claim. After following a mechanism, intervention, discrepancy, or holdout,
return through the canonical [complete eight-problem return matrix](../../SOURCE_MAP.md#complete-eight-problem-return-matrix)
to rejoin the problem-owned source, paper, and exact frontier. From an exact
source or paper handle, use `python3 scripts/query_corpus.py --source
<module.lean:line>` or `--paper-anchor <TeX_label_or_source_ref>` to recover the
corresponding reverse route. This keeps a useful explanation connected to the
checked declaration and its unresolved boundary without promoting the lab's
mechanism vocabulary into a mathematical result.

For a module-level handoff, use `python3 scripts/query_corpus.py --module
<module_path_or_sigil>`. A source path or paper sigil returns the authored
synopsis, declaration preview, exact source identity, attached claims, and
route-memory context before you return to the problem matrix and its boundary.

For external statement identity, follow the generated [Formal Conjectures
crosswalk](../../verification/FORMAL_CONJECTURES_CROSSWALK.md). Its eight problem rows bind
the pinned upstream declaration and source hash to the matching local route;
the lab remains an explanation layer and does not become proof or claim
authority by following that link.

## What this layer does not decide

Not novelty, not significance, not correctness. A mechanism is an explanation;
Lean remains the proof authority and the semantic corpus remains the statement
authority. `docs/methodology.json` carries the evidence class
`blinded_recovery_evaluation`, which states exactly what a recovery result does
and does not establish.
