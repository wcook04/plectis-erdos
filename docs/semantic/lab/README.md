<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Theory laboratory

The semantic corpus one directory up answers *what has been proved and how the
statements relate*. This layer answers three further questions:

- **What are the few mechanisms underneath those proofs?** Not the theorems — the
  reusable reasons the theorems are true, and the reasons methods fail.
- **What survives when the mathematics is deliberately perturbed?** A typed
  intervention shifts a coefficient, changes a base, or drops a structural
  precondition, records which mechanisms it predicts will break, and then checks.
- **Does the explanation transfer to mathematics the system was not shown?** A
  holdout checks the repository out at the commit before a theorem landed and
  measures whether the layer helps recover it.

The third question is the one that decides whether the first two are worth
anything. A mechanism that reads well but does not improve recovery of held-out
mathematics is a story, not an explanation.

## Files

`mechanisms.json`, `capsules.json`, `interventions.json`, `receipts.json`,
`benchmark_items.json`, `benchmark_results.json` are **authored**.
`docs/theory_lab.json` is **generated** from them by
`scripts/build_theory_lab.py` and guarded by `scripts/check_theory_lab.py`.

## What a mechanism is

An invariant, plus a transformation, plus the observable it controls. The test is
predictive, not descriptive: given only the record, could a mathematician who has
never seen this repository decide whether a *new* nearby statement is reachable
by it? If not, the record is a label and the contract rejects it for missing one
of `invariant`, `transformation`, `observable_controlled`.

A theorem family is not a mechanism. A restatement is not a mechanism. A
dependency cluster is not a mechanism.

## Why the negative space is first-class

Most formal libraries are survivorship-biased: they record what worked. This
corpus's unusual asset is the opposite — blocked engines, failed generalisations,
repairs that restore one precondition and expose another. `receipts.json` keeps
those, and the contract requires every receipt that rules a mechanism out to also
name the sibling mechanisms it does **not** reach.

That rule exists for a specific reason. A barrier here was very nearly written up
as closing a family of certificate engines when a weaker low-carry engine in the
same development survived it. The omission was caught by luck. The contract now
makes it impossible to record the barrier without answering the question.

## Prediction integrity

An intervention records what it predicts *before* the outcome is known.
`scripts/build_theory_lab.py --stamp` fingerprints exactly the predictive fields;
the checker recomputes and rejects a mismatch, and `--stamp` refuses to stamp a
record whose outcome is already known. So "we predicted this" is auditable rather
than a story assembled afterwards.

## How holdouts avoid leaking

`scripts/build_benchmark_packet.py` creates a detached git worktree at the commit
before the target declaration was introduced. The target is absent from that
checkout by construction — the control does not depend on the agent's restraint.
Injected artifacts are filtered against declarations extracted from the checkout
itself, so a mechanism record citing a future theorem is dropped rather than
trimmed. Arms are cumulative:

    signatures   the cut checkout alone
    graph        + statement graph, filtered to the cut
    mechanism    + mechanism records and capsules, filtered to the cut
    negative     + failure receipts

```bash
python3 scripts/build_benchmark_packet.py --target NAME --arm mechanism --dest /tmp/cut --answer-key /tmp/key.json
```

The answer key is refused if it would be written inside the packet.

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

## What this layer does not decide

Not novelty, not significance, not correctness. A mechanism is an explanation;
Lean remains the proof authority and the semantic corpus remains the statement
authority. `docs/methodology.json` carries the evidence class
`blinded_recovery_evaluation`, which states exactly what a recovery result does
and does not establish.
