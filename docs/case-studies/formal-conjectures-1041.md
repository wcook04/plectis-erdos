# From ani's counterexample to the Formal Conjectures #1041 update

This follows the statement, source, proof, and upstream check for one
completed Formal Conjectures contribution.

## The question and the source

Formal Conjectures asked whether every monic complex polynomial of degree at
least two, with roots inside the open unit disc, has two root occurrences
joined by a path inside `{z : |f(z)| < 1}` whose image has one-dimensional
Hausdorff measure below two. Its `length` definition is `μH[1]` of the path's
image. [Read the merged statement](https://github.com/google-deepmind/formal-conjectures/blob/a01ad23474c14781e4f16f48f6e5a430895e10a0/FormalConjectures/ErdosProblems/1041.lean).

[ani posted a degree-seven counterexample](https://www.erdosproblems.com/forum/thread/1041#post-8861)
on 7 September 2026. The polynomial and the mathematical counterexample are
ani's. The public Lean development fixes the member of ani's family with
`s = 10^-6`; one example is enough to answer the universal question.

## What the Lean proof establishes

The development proves a stronger statement for that polynomial: any
preconnected subset of the strict unit lemniscate containing two distinct
roots has one-dimensional Hausdorff measure greater than two. A path image
joining such roots is preconnected, so the existing Formal Conjectures
statement is false. The [linked Lean theorem](https://github.com/wcook04/plectis-erdos/blob/0ee31b3a99ef93d2b679a427b474b23710597bad/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L449-L454)
states `False ↔` the benchmark proposition, with `fcLength` defined as the
same `μH[1]` measure.

The contribution also corrected a hidden formal hypothesis. The upstream
file's variables for a preceding component lemma remained in scope at the
main conjecture. [PR #6505](https://github.com/google-deepmind/formal-conjectures/pull/6505)
put those variables in their own section. That confines the hypotheses to
the component lemma and gives the main question its intended quantifiers.

## Checking the artifact

The public source at the immutable proof commit contains `#print axioms` for
the linked declaration. Its recorded result lists `propext`,
`Classical.choice`, and `Quot.sound`, without `sorryAx`. The
[public Lean CI run](https://github.com/wcook04/plectis-erdos/actions/runs/35797573885)
completed successfully at descendant commit `5aa9f1019e8bf6ff1a02ea6c189a198e74c87ef2`;
the proof file has the same Git blob at that commit and the linked proof commit.
Formal Conjectures' [merged PR](https://github.com/google-deepmind/formal-conjectures/pull/6505)
stores the corrected statement and external proof link. Its theorem still
has a `by sorry` body; the linked source contains the checked proof. The PR
has a passing project build and checks. To rerun the two relevant module
builds from clean clones with the repositories' pinned toolchains:

```sh
git clone --filter=blob:none https://github.com/wcook04/plectis-erdos.git
cd plectis-erdos
git checkout 0ee31b3a99ef93d2b679a427b474b23710597bad
lake exe cache get
lake --wfail build ErdosProblems.Erdos1041.Counterexample.HausdorffLength

cd ..
git clone --filter=blob:none https://github.com/google-deepmind/formal-conjectures.git
cd formal-conjectures
git checkout a01ad23474c14781e4f16f48f6e5a430895e10a0
lake exe cache get
lake --wfail build 'FormalConjectures.ErdosProblems.«1041»'
```

The commands specify the relevant module builds; the linked CI runs are the
recorded checks from the contribution.

## Who did what, and the remaining limit

ani supplied the degree-seven counterexample. Will Cook chose the benchmark
target, directed the AI-assisted public formalisation and submitted the
statement correction and proof link. Claude Code and OpenAI Codex contributed
Lean code and preparation under his direction; the Lean kernel checked the
result. The Formal Conjectures merge records acceptance of that exact update.
Independent human review that the present FC formulation matches every nuance
of the original 1958 Erdős–Herzog–Piranian wording has not been recorded.
The checked proof establishes one specified polynomial, not ani's whole
reported parameter family.

## Other merged contributions

The [#257 divisor-count variant](https://github.com/google-deepmind/formal-conjectures/pull/6506),
[#258 constant-base variant](https://github.com/google-deepmind/formal-conjectures/pull/5034),
and [#1049 integer-base variant](https://github.com/google-deepmind/formal-conjectures/pull/6507)
link Lean proofs based on Erdős's 1948 irrationality theorem for Lambert
series. These are three integrations of that result, not three new
irrationality theorems. Will Cook selected and submitted the targets and takes
responsibility for them; Claude Code and OpenAI Codex assisted with the Lean
development and submission preparation under his direction. The linked
proofs were checked by Lean. Their repository merge records acceptance of
those exact links, not independent mathematical review.
