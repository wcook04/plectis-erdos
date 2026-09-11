/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# ResidualBench — ground-truth fixtures for semantic residual evaluation

Google DeepMind's AlphaProof Nexus paper reports, in its failure analysis, that
its evolutionary proof search "frequently offloaded a problem's core difficulty
into a single `sorry` within a helper lemma that reiterated the target statement
in a slightly different form", and that "explicitly prompting against this
behavior failed to prevent it". Its raters score sketches on, among other things,
"the plausibility of remaining goals" — a language model's guess about a relation
the kernel can sometimes decide outright.

This file is the labelled corpus for deciding it with the kernel instead.

Each fixture is a *sketch*: a target proposition `P`, plus one or more residual
obligations `R i` that the sketch leaves unproved. The evaluator asks Lean three
bounded questions per sketch:

* soundness    `(⋀ R i) → P`   — do the residuals actually suffice?
* laundering   `P → (⋀ R i)`   — is the residual just the target again?
* refutation   `¬ (⋀ R i)`     — is the residual outright false?

A `laundering` proof is a hard veto: the sketch renamed the difficulty rather
than reducing it. A `refutation` proof is a hard veto too: the residual is a
hallucinated "known result". Everything else is a candidate, not a verdict.

The detector is deliberately *sound but incomplete*. It only ever reports
laundering when the kernel proves `P → ⋀ R i` inside a fixed tactic budget, so a
false accusation is impossible; a sufficiently disguised restatement escapes.
That asymmetry is the point — the evaluator supplies vetoes, never scores.

## Ground truth

Every fixture below carries its expected verdict in its docstring. The bench is
useless if the evaluator agrees with everything, so it contains four negatives —
sketches that a naive "does it look like the target?" heuristic would flag and
the kernel must not.
-/

namespace ResidualBench

/-! ### Target 1 — sum of the first `n` odd numbers -/

/-- The target proposition. -/
def OddSum : Prop := ∀ n : ℕ, ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2

/-! #### Sketch A — laundering by notation

The residual writes `n * n` where the target writes `n ^ 2`. This is the
paper's failure mode in its purest form: the difficulty has not moved.

Expected verdict: `endpoint_equivalent`. -/
def A_residual : Prop := ∀ n : ℕ, ∑ i ∈ Finset.range n, (2 * i + 1) = n * n

/-! #### Sketch B — laundering by reassociation

The residual reindexes the sum over `Finset.Ico 0 n` and swaps the addend order.
Superficially further from the target than sketch A, yet still equivalent.

Expected verdict: `endpoint_equivalent`. -/
def B_residual : Prop := ∀ n : ℕ, ∑ i ∈ Finset.Ico 0 n, (1 + 2 * i) = n ^ 2

/-! #### Sketch C — genuine decomposition

Base case plus inductive step. Neither residual implies the target on its own,
and the target implies neither conjunct's universal form, so the difficulty has
actually been split.

Expected verdict: `strict_decomposition_candidate`. -/
def C_residual_base : Prop := ∑ i ∈ Finset.range 0, (2 * i + 1) = 0 ^ 2

def C_residual_step : Prop :=
  ∀ n : ℕ, (∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2) →
    (∑ i ∈ Finset.range (n + 1), (2 * i + 1) = (n + 1) ^ 2)

/-! #### Sketch D — self-assumption

The residual is an implication whose antecedent is the target. It typechecks,
it is trivially true, and it establishes nothing. Comparator's negative control
is the same shape at the level of a whole declaration.

Expected verdict: `endpoint_equivalent` (the residual is implied by the target
and implies it back given the sketch), flagged `self_assumption`. -/
def D_residual : Prop := OddSum → OddSum

/-! #### Sketch E — hallucinated literature

The residual is cited as a known closed form and is false: the sum of the first
`n` odd numbers is `n ^ 2`, not `n ^ 2 + 1`. A rater judging "plausibility of
remaining goals" has no way to see this; the kernel refutes it.

Expected verdict: `residual_refuted`. -/
def E_residual : Prop := ∀ n : ℕ, ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 + 1

/-! #### Sketch F — productive strengthening (NEGATIVE CONTROL)

The residual is a strictly stronger statement about a general arithmetic-progression
sum. It implies the target; the target does not imply it. A heuristic that flags
"residual mentions the same sum" would wrongly reject this, and rejecting it would
be the expensive error — this is the representation change that actually pays.

Expected verdict: `strict_decomposition_candidate`, NOT `endpoint_equivalent`. -/
def F_residual : Prop :=
  ∀ (a d n : ℕ), ∑ i ∈ Finset.range n, (a + d * i) = n * a + d * (n * (n - 1) / 2)

/-! ### Target 2 — a divisor-sum identity in the shape of the live corpus

This target is the arithmetic core of the Lambert-series bridge that carries the
public adapter, reduced to a finite statement so the bench stays cheap. It exists
so the bench is not made only of toy sums.
-/

def DivisorCount : Prop :=
  ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, (Nat.divisors n).card
    = ∑ d ∈ Finset.Icc 1 N, N / d

/-! #### Sketch G — laundering across a representation change

The residual counts lattice points under a hyperbola instead of summing divisor
counts. The two are the same statement written in different notation, and the
identification is exactly the rewriting the sketch would perform anyway.

Expected verdict: `endpoint_equivalent`. -/
def G_residual : Prop :=
  ∀ N : ℕ, ∑ d ∈ Finset.Icc 1 N, N / d
    = ∑ n ∈ Finset.Icc 1 N, (Nat.divisors n).card

/-! #### Sketch H — incomparable residual (NEGATIVE CONTROL)

A true and relevant statement about the same objects that neither implies the
target nor follows from it within the budget. The evaluator must abstain rather
than guess.

Expected verdict: `unknown_relation`. -/
def H_residual : Prop := ∀ n : ℕ, 0 < n → 0 < (Nat.divisors n).card

end ResidualBench
