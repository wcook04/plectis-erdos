<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Theory laboratory

The semantic corpus records proved statements and their relations. This layer
records reusable proof mechanisms, predicts what changes under a perturbation,
and prepares holdouts for testing whether an explanation helps recover a proof.

## Files

`mechanisms.json`, `capsules.json`, `interventions.json`, `receipts.json`,
`benchmark_items.json`, `benchmark_results.json` are **authored**.
`docs/theory_lab.json` is **generated** from them by
`scripts/build_theory_lab.py` and guarded by `scripts/check_theory_lab.py`.

## What a mechanism is

A mechanism record names an invariant, a transformation, and the observable it
controls. The checker requires `invariant`, `transformation`, and
`observable_controlled`; the author must explain how these help assess a nearby
statement. A theorem name or dependency cluster alone does not supply that
explanation.

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

## How holdouts avoid leaking

`scripts/build_benchmark_packet.py` exports a source snapshot from the commit
before the target declaration was introduced and checks that the declaration
is absent. The snapshot contains no Git metadata: a linked worktree would let
the agent recover later answers from the shared object store. Introducing-commit
metadata and the answer key stay outside the packet. Injected artifacts are
filtered against declarations extracted from the snapshot, so a mechanism record
citing a future theorem is dropped rather than trimmed. Arms are cumulative:

    signatures   the cut checkout alone
    graph        + statement graph, filtered to the cut
    mechanism    + mechanism records and capsules, filtered to the cut
    negative     + failure receipts

```bash
python3 scripts/build_benchmark_packet.py --target NAME --arm mechanism --dest /tmp/cut --answer-key /tmp/key.json
```

The destination must be a new directory outside the source repository. The
answer key is refused if it would be written inside the packet. The evaluator
must give the agent an isolated filesystem and restricted network access; the
builder creates inputs, not a process sandbox. Review historical source and
injected explanations for answer hints before selecting an evaluation item.
No performance improvement follows from constructing these packets alone.

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
crosswalk](../../FORMAL_CONJECTURES_CROSSWALK.md). Its eight problem rows bind
the pinned upstream declaration and source hash to the matching local route;
the lab remains an explanation layer and does not become proof or claim
authority by following that link.

## What this layer does not decide

Not novelty, not significance, not correctness. A mechanism is an explanation;
Lean remains the proof authority and the semantic corpus remains the statement
authority. `docs/methodology.json` carries the evidence class
`blinded_recovery_evaluation`, which states exactly what a recovery result does
and does not establish.
