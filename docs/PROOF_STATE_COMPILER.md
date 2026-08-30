<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Proof-state compiler

The proof-state compiler is the runtime continuation of the repository's
static semantic compiler.  `query_corpus.py --goal-support` and
`--proof-plan` cheaply nominate declarations from elaborated type and
dependency projections.  `scripts/proof_state_compiler.py` then asks the
pinned Lean environment what those applications actually do.

The distinction is strict:

- a static conclusion or context match is a candidate;
- a transition exists only when Lean reaches the post-application
  `trace_state` checkpoint;
- the generated children are an AND set of real subgoals;
- competing accepted applications are OR alternatives;
- a proof receipt exists only when Lean exits successfully with no remaining
  goals.

The packet is planning and navigation evidence.  It does not change claim
status, author mathematical exposition, or promote an unproved bridge.

## First run

```sh
python3 scripts/proof_state_compiler.py --pilot-controls
python3 scripts/test_proof_state_compiler.py
```

The pilot contains three causally related controls:

1. applying `tail_diff_int_of_den_dvd` without `hdvd` must produce the exact
   divisibility subgoal;
2. adding only that exact assumption must close the same application through
   `assumption`;
3. the independent `SharpCurvatureSupply` control must elaborate and close.

This is stronger than repeating the static telescope: Lean supplies the
instantiated child goals and decides whether the replay closes.

## Explicit requests

Use `--request-file PATH` or `--request-stdin`.  The request schema is
`erdos249257-proof-state-request/1`:

```json
{
  "schema_version": "erdos249257-proof-state-request/1",
  "goal_id": "example_goal",
  "imports": ["Erdos249257"],
  "opens": [
    "Erdos249257",
    "Erdos249257.TotientTailPeriodKiller"
  ],
  "context": [
    {"name": "hsupply", "binder": "(hsupply : SharpCurvatureSupply)", "role": "assumption"}
  ],
  "target": "Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)",
  "candidates": [
    {
      "candidate_id": "curvature_consumer",
      "declaration": "Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_sharpCurvatureSupply",
      "arguments": [],
      "discharge_tactics": ["assumption"]
    }
  ]
}
```

Requests are trusted local Lean input.  They are bounded to eight candidate
applications and eight discharge tactics per candidate.  Each candidate is
run independently from the same root state, so a rejected alternative cannot
contaminate another branch.

## Packet contract

`erdos249257-proof-state-compilation/1` carries:

- the Git, Lean, toolchain, manifest, and lakefile fingerprint;
- exact target and assumption-world identity;
- source-joined declaration and file-digest receipts when the dependency
  index is available;
- Lean-tested transitions and typed failures;
- proof-state nodes and application hyperedges;
- AND children and OR alternatives;
- non-dominated candidates under the emitted cost vector;
- plan blocker sets, the minimal-missing-interventions antichain, and
  bounded minimal hitting cuts, with a `blocker_algebra_semantics` block
  keeping the three projections non-interchangeable;
- discharge and closed-proof replay receipts;
- an abstention receipt when no bounded route closes;
- omissions and an explicit re-entry route.

The compiler records explicit tactic arguments plus Lean-instantiated
subgoals as the substitution witness.  It does not pretend that source-level
argument text is a complete dump of Lean's internal metavariable assignment.

## Return to public evidence

A proof-state packet is a typed continuation artifact, not a public claim. When
a candidate closes (or the compiler abstains), return to the [complete
eight-problem return matrix](SOURCE_MAP.md#complete-eight-problem-return-matrix).
Select the matching row in [`docs/problems.json`](problems.json) to recover its
exact note, paper/source joins, and open-obligation statement; then use the
packet's declaration and source coordinates to verify the corresponding Lean
witness. A closed tactic run does not settle the problem unless the public
claim registry says so.

## Causal obstruction receipt

The pilot's divisibility pair is an intervention, not merely two examples.
The goal and application are fixed; the only added assumption is `hdvd`.
Failure before the intervention and closure afterward establishes that this
exact obligation is sufficient for this exact application.  It does not prove
that every possible proof of the target must use the same premise.

For a larger candidate forest, each accepted application contributes its open
AND set.  The packet reports full completion sets per plan, the antichain of
minimal missing interventions, and bounded minimal hitting cuts across
alternatives.  The intervention and cut families answer different questions
and must not be substituted for one another: supplying every member of one
intervention row completes a route, while a cut names the smallest removal
that defeats every known route.  For plans `{a,b}` and `{b,c}` the cuts are
`{b}` and `{a,c}`, yet adding `b` alone closes nothing.  These are critic
inputs, not proof terms.

## Historical shadow

```sh
python3 scripts/historical_bridge_experiment.py
```

The historical evaluator:

1. checks out the parent of a real bridge-introduction commit in a disposable
   local clone;
2. rebuilds the authorised pre-introduction dependency target there;
3. verifies that the future module and declaration name are absent;
4. compiles the exact obstruction using only that parent environment;
5. kernel-checks an anonymised authored bridge candidate;
6. only after the proof run, measures later independent reuse in current
   history.

This is deliberately labelled a historical shadow evaluator.  It proves that
the runtime can identify the obstruction, reject future-name leakage, and
admit a useful bridge in the historical environment.  It does **not** claim
that the current system autonomously invented the candidate.  Promotion to a
completion engine requires a cut-conditioned generator and a second-corpus or
prospective unseen-bridge result.

## Validation

```sh
python3 -m py_compile \
  scripts/proof_state_compiler.py \
  scripts/test_proof_state_compiler.py \
  scripts/historical_bridge_experiment.py
python3 scripts/test_proof_state_compiler.py
python3 scripts/historical_bridge_experiment.py
python3 scripts/test_query_corpus_resilience.py
python3 scripts/dogfood_semantic_proof.py
```

The historical command is intentionally separate because it creates and
builds a disposable parent checkout.  No generated historical state is
written into the repository.
