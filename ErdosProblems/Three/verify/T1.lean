import ErdosProblems.Three.T1

/-!
# Adversarial verification of `ErdosProblems/Three/T1.lean`

* §1  Axiom audit of every declaration in T1.
* §2  Independent re-derivation of every numeral asserted in T1.
* §3  **Satisfiability** of every non-trivial hypothesis, on real corpus data,
      over a wide range of rows.
* §4  Independent stress test of the §4 no-go: the pointwise-minimal
      `IntervalCeiling` is computed directly and checked against
      `IntervalCeiling.four_pow_le`.
* §5  Faithfulness of `ResidualInvariant` to C6's measurement note.
-/

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.Three.T1

namespace ErdosProblems.Three.VerifyT1

/-! ## 1. Axiom audit -/

#print axioms ErdosProblems.Three.T1.seamResidualUpto_one
#print axioms ErdosProblems.Three.T1.seamResidualUpto_succ
#print axioms ErdosProblems.Three.T1.seamResidualUpto_succ_le
#print axioms ErdosProblems.Three.T1.integerGreedyRemainder_seamWeightsFrom
#print axioms ErdosProblems.Three.T1.seamResidualUpto_last
#print axioms ErdosProblems.Three.T1.seamResidualUpto_thirteen_seven
#print axioms ErdosProblems.Three.T1.not_residualInvariant
#print axioms ErdosProblems.Three.T1.residual_thirteen_seven_exceeds
#print axioms ErdosProblems.Three.T1.seamIntegerGreedyRemainder_thirteen
#print axioms ErdosProblems.Three.T1.seamIntegerGreedyRemainder_thirteen_lt
#print axioms ErdosProblems.Three.T1.seamIntegerGreedyRemainder_thirteen_gt
#print axioms ErdosProblems.Three.T1.residual_lt_of_taken
#print axioms ErdosProblems.Three.T1.residual_lt_of_declined
#print axioms ErdosProblems.Three.T1.invariant_step_dichotomy
#print axioms ErdosProblems.Three.T1.seamResidualUpto_thirteen_six
#print axioms ErdosProblems.Three.T1.tangency_window_thirteen
#print axioms ErdosProblems.Three.T1.residualInvariant_twelve
#print axioms ErdosProblems.Three.T1.residualInvariant_fourteen
#print axioms ErdosProblems.Three.T1.invariant_holds_at_six_fails_at_seven
#print axioms ErdosProblems.Three.T1.weight_two_le_target
#print axioms ErdosProblems.Three.T1.seamResidualUpto_two
#print axioms ErdosProblems.Three.T1.weight_three_le_residual
#print axioms ErdosProblems.Three.T1.seamResidualUpto_succ_eq_greedyStep
#print axioms ErdosProblems.Three.T1.intervalCeiling_obligations_iff
#print axioms ErdosProblems.Three.T1.IntervalCeiling.sound
#print axioms ErdosProblems.Three.T1.trivialCeiling
#print axioms ErdosProblems.Three.T1.fifteen_mul_weightSum_tail_le
#print axioms ErdosProblems.Three.T1.IntervalCeiling.chain
#print axioms ErdosProblems.Three.T1.IntervalCeiling.weight_three_le
#print axioms ErdosProblems.Three.T1.IntervalCeiling.four_pow_le
#print axioms ErdosProblems.Three.T1.IntervalCeiling.two_pow_lt
#print axioms ErdosProblems.Three.T1.IntervalCeiling.no_better_than_trivial
#print axioms ErdosProblems.Three.T1.truncatedMersenneWeight_antitone
#print axioms ErdosProblems.Three.T1.weight_satisfies_declined
#print axioms ErdosProblems.Three.T1.declined_floor
#print axioms ErdosProblems.Three.T1.declined_floor_terminal
#print axioms ErdosProblems.Three.T1.start_lt_of_terminal_lt
#print axioms ErdosProblems.Three.T1.declined_floor_terminal_weight
#print axioms ErdosProblems.Three.T1.trivialCeiling_two_pow_lt
#print axioms ErdosProblems.Three.T1.remainder_lt_of_weightCeiling
#print axioms ErdosProblems.Three.T1.weightCeiling_thirteen
#print axioms ErdosProblems.Three.T1.seamIntegerGreedyRemainder_thirteen_lt'
#print axioms ErdosProblems.Three.T1.weightCeiling_not_intervalCeiling
#print axioms ErdosProblems.Three.T1.weight_fails_taken

/-! ## 2. Independent re-derivation of the numerals

Everything below is recomputed from the *corpus* definitions
(`truncatedMersenneWeight s d = 4 ^ s / (2 ^ d - 1)`,
`seamSubsetTarget s = 2 ^ (2 * s - 1) - 2 ^ s`) via T1's `seamResidualUpto`,
and separately via the corpus's own `seamIntegerGreedyRemainder`. -/

-- 524419, and 2 ^ 19 = 524288: the invariant really is violated.
#eval seamResidualUpto 13 7                -- expect 524419
#eval (2 : ℕ) ^ (2 * 13 - 7)               -- expect 524288
#eval seamResidualUpto 13 6                -- expect 524419
#eval truncatedMersenneWeight 13 7         -- expect 528416  (tangency window top)
#eval seamResidualUpto 13 12               -- expect 15147 = ρ 13
#eval seamIntegerGreedyRemainder 13        -- corpus object: expect 15147
#eval truncatedMersenneWeight 13 4         -- expect 4473924
#eval 2 * truncatedMersenneWeight 13 5     -- expect 4329604
#eval truncatedMersenneWeight 13 12        -- expect 16388 = 2 ^ 14 + 4

/-- Kernel-checked (not `#eval`-checked) agreement between T1's rank-indexed
residual and the corpus greedy remainder at the refuting row. -/
example : seamResidualUpto 13 12 = seamIntegerGreedyRemainder 13 := by
  exact seamResidualUpto_last (by norm_num)

/-! ## 3. Satisfiability of every non-trivial hypothesis

### 3a.  The two branch hypotheses of §3 (`htaken`, `hdecl`)

`residual_lt_of_taken` needs `w (d+1) ≤ residual d`; `residual_lt_of_declined`
needs the reverse.  Both are counted below over all `(s, d)` with
`6 ≤ s ≤ S`, `2 ≤ d < s - 1`.  If either count were `0` the corresponding
theorem would be vacuous. -/

def takenCount (S : ℕ) : ℕ :=
  ((List.range (S + 1)).flatMap fun s =>
    (List.range s).filterMap fun d =>
      if 6 ≤ s ∧ 2 ≤ d ∧ d + 1 < s ∧
          truncatedMersenneWeight s (d + 1) ≤ seamResidualUpto s d
        then some (s, d) else none).length

def declinedCount (S : ℕ) : ℕ :=
  ((List.range (S + 1)).flatMap fun s =>
    (List.range s).filterMap fun d =>
      if 6 ≤ s ∧ 2 ≤ d ∧ d + 1 < s ∧
          seamResidualUpto s d < truncatedMersenneWeight s (d + 1)
        then some (s, d) else none).length

#eval takenCount 120     -- both must be large
#eval declinedCount 120

/-! ### 3b.  The hypothesis `h : residual d < 2 ^ (2*s-d)` of
`residual_lt_of_taken` / `invariant_step_dichotomy`

This is C6's invariant *at rank d*.  It is refuted as a universal statement,
so it must still be checked that it HOLDS often enough that those two theorems
are not vacuous.  `c6Failures S` lists every `(s, d)` where it fails. -/

def c6Failures (S : ℕ) : List (ℕ × ℕ) :=
  (List.range (S + 1)).flatMap fun s =>
    (List.range s).filterMap fun d =>
      if 6 ≤ s ∧ 2 ≤ d ∧ 2 ^ (2 * s - d) ≤ seamResidualUpto s d
        then some (s, d) else none

def c6Holds (S : ℕ) : ℕ :=
  ((List.range (S + 1)).flatMap fun s =>
    (List.range s).filterMap fun d =>
      if 6 ≤ s ∧ 2 ≤ d ∧ seamResidualUpto s d < 2 ^ (2 * s - d)
        then some (s, d) else none).length

#eval c6Failures 200     -- expect exactly [(13, 7)]
#eval c6Holds 200        -- expect a large number: hypothesis is satisfiable

/-- The failure at `(13,7)` is the ONLY one below row 200 — proved in the
kernel, not merely `#eval`-ed. -/
theorem c6Failures_200 : c6Failures 200 = [(13, 7)] := by
  decide +kernel

/-! ### 3c.  The second disjunct of `invariant_step_dichotomy`
(the tangency window).  T1 exhibits it at `(13, 6)`; here it is counted. -/

def tangencyHits (S : ℕ) : List (ℕ × ℕ) :=
  (List.range (S + 1)).flatMap fun s =>
    (List.range s).filterMap fun d =>
      if 6 ≤ s ∧ 2 ≤ d ∧ d + 1 < s ∧
          2 ^ (2 * s - (d + 1)) ≤ seamResidualUpto s d ∧
          seamResidualUpto s d < truncatedMersenneWeight s (d + 1)
        then some (s, d) else none

#eval (tangencyHits 60).length
#eval (tangencyHits 60).take 12

/-! ### 3d.  `WeightCeilingAt` — the MEASURED hypothesis of
`remainder_lt_of_weightCeiling`.  T1 proves it only at `s = 13`. -/

def wcFailures (S : ℕ) : List (ℕ × ℕ) :=
  (List.range (S + 1)).flatMap fun s =>
    (List.range s).filterMap fun d =>
      if 6 ≤ s ∧ 2 ≤ d ∧ truncatedMersenneWeight s d ≤ seamResidualUpto s d
        then some (s, d) else none

#eval wcFailures 200     -- expect []

/-- Kernel-checked: `WeightCeilingAt s` holds at every row `6 ≤ s ≤ 200`.
(T1 states it only at `s = 13`; this widens the anti-vacuity evidence but is
still finite verification, NOT a proof of `WeightCeilingAt` in general.) -/
theorem wcFailures_200 : wcFailures 200 = [] := by
  decide +kernel

/-- The degenerate row `5` really does break the weight ceiling, exactly as
T1's measurement note says. -/
theorem wcFails_at_five :
    truncatedMersenneWeight 5 4 ≤ seamResidualUpto 5 4 := by
  norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-! ### 3e.  `IntervalCeiling s` — the class hypothesised in §4.
Inhabited by `trivialCeiling`, which T1 proves.  Re-checked here. -/

example (s : ℕ) : IntervalCeiling s := trivialCeiling s

example : 2 ^ (100 + 1) < (trivialCeiling 100).bound (100 - 1) :=
  trivialCeiling_two_pow_lt (by norm_num)

/-! ### 3f.  The `hdec` hypothesis of `declined_floor` /
`declined_floor_terminal` / `start_lt_of_terminal_lt`.

T1's anti-vacuity witness is the weight family, for which the conclusion is
`min (w a) (2^(s+1)+4) ≤ w (s-1) = 2^(s+1)+4`, i.e. TRIVIALLY true by
`min_le_right`.  A sharper witness is needed to show the statement has
content: below, a family that satisfies `hdec` and for which the conclusion is
attained by the LEFT branch of the `min`. -/

/-- A non-degenerate witness: the constant family `B ≡ 2 ^ s`.  It satisfies
`hdec`, and `declined_floor_terminal` then gives `2 ^ s ≤ 2 ^ s` via the left
branch of the `min` — i.e. the min is NOT resolved by `min_le_right` here. -/
theorem declined_floor_terminal_const {s : ℕ} (hs : 4 ≤ s) {a : ℕ}
    (ha : 1 ≤ a) (has : a ≤ s - 1) :
    min ((fun _ : ℕ => 2 ^ s) a) (2 ^ (s + 1) + 4) ≤ (fun _ : ℕ => 2 ^ s) (s - 1) :=
  declined_floor_terminal hs ha has (B := fun _ => 2 ^ s)
    (fun _ _ _ => min_le_left _ _)

/-- And the contrapositive `start_lt_of_terminal_lt` is non-vacuous on it:
both hypotheses hold simultaneously. -/
theorem start_lt_of_terminal_lt_const {s : ℕ} (hs : 4 ≤ s) {a : ℕ}
    (ha : 1 ≤ a) (has : a ≤ s - 1) :
    (2 : ℕ) ^ s < 2 ^ (s + 1) :=
  start_lt_of_terminal_lt hs ha has (B := fun _ => 2 ^ s)
    (fun _ _ _ => min_le_left _ _)
    (by show (2 : ℕ) ^ s < 2 ^ (s + 1)
        have h1 : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
        have h2 : (0 : ℕ) < 2 ^ s := Nat.two_pow_pos s
        omega)

/-! ## 4. Independent stress test of the §4 no-go

`IntervalCeiling.four_pow_le` claims `4 ^ s ≤ 105 * bound (s-1) + 90` for
EVERY `IntervalCeiling s`.  The strongest test is the *pointwise minimal*
family: `B 2 := residual 2 + 1` (the least value satisfying `start`), and
`B (d+1) := max (min (B d) w) (B d - w)` — the least value satisfying both
obligations.  Every `IntervalCeiling` dominates it pointwise, so if the
no-go's inequality holds for this family it holds for all of them; and if it
FAILED for this family the theorem would be false. -/

/-- `minCeil s k` is the minimal admissible bound at rank `k + 2`. -/
def minCeil (s : ℕ) : ℕ → ℕ
  | 0 => seamResidualUpto s 2 + 1
  | k + 1 =>
      let B := minCeil s k
      let w := truncatedMersenneWeight s (k + 3)
      max (min B w) (B - w)

/-- The minimal admissible bound at rank `s - 1`. -/
def minCeilTop (s : ℕ) : ℕ := minCeil s (s - 3)

/-- The no-go inequality, evaluated on the minimal family. -/
def nogoHolds (s : ℕ) : Bool := decide (4 ^ s ≤ 105 * minCeilTop s + 90)

def nogoFailures (S : ℕ) : List ℕ :=
  (List.range (S + 1)).filter fun s => 6 ≤ s && !nogoHolds s

#eval nogoFailures 150      -- expect []

theorem nogoFailures_150 : nogoFailures 150 = [] := by decide +kernel

/-- How much slack does the no-go have?  `4 ^ s / minCeilTop s` — if this were
close to `105` the constant would be tight; the printout shows how far the
TRUE minimal interval ceiling is from `4 ^ s`. -/
def nogoRatioPercent (s : ℕ) : ℕ := 100 * 4 ^ s / minCeilTop s

#eval (List.range 40).filterMap fun s =>
  if 6 ≤ s then some (s, nogoRatioPercent s) else none

/-! The minimal interval ceiling really is astronomically larger than
`2 ^ (s + 1)`: the ratio `minCeilTop s / 2 ^ (s+1)` at a few rows. -/
#eval [10, 20, 40, 80, 160].map fun s => (s, minCeilTop s / 2 ^ (s + 1))

/-! And the true residual is astronomically SMALLER, so the gap the no-go
identifies is real, not an artefact of a bad minimal family. -/
#eval [10, 20, 40, 80, 160].map fun s => (s, seamResidualUpto s (s - 1), 2 ^ (s + 1))

/-! ### 4b.  Is the branch-blindness of `IntervalCeiling` doing hidden work?

`IntervalCeiling` demands BOTH obligations at every rank, i.e. it knows nothing
about which branch the greedy takes.  That is a real restriction, and T1 itself
escapes it twice (`weight_three_le_residual` proves rank 3 is taken; C6 §6
proves ranks 4 and 5 are declined).  So the honest question is: does adding a
FIXED finite amount of proved branch knowledge break the `4 ^ s` barrier?

`minCeilKnown s K` is the pointwise-minimal ceiling when the branch at every
rank `≤ K` is treated as known (and therefore only the relevant one of the two
obligations is imposed there), and blind above.  `K = 1` is `minCeil`;
`K = s` is full knowledge, which collapses to `ρ s + 1`. -/

def minCeilKnown (s K : ℕ) : ℕ → ℕ
  | 0 => seamResidualUpto s 2 + 1
  | k + 1 =>
      let B := minCeilKnown s K k
      let d := k + 3
      let w := truncatedMersenneWeight s d
      if d ≤ K then
        (if w ≤ seamResidualUpto s (d - 1) then max (B - w) 1 else min B w)
      else max (max (min B w) (B - w)) 1

def minCeilKnownTop (s K : ℕ) : ℕ := minCeilKnown s K (s - 3)

/-! `4 ^ s / minCeilKnownTop s K` for `K = 1, 3, 5, 6, 8, 12, 20` and then
`K = s`.  For every FIXED `K` the ratio is a constant independent of `s` — so a
fixed finite amount of branch knowledge leaves the ceiling `Θ(4 ^ s)` and the
no-go stands.  Only `K = s` (full branch knowledge, i.e. the open problem
itself) collapses it. -/
#eval ([1, 3, 5, 6, 8, 12, 20, 80].map fun K => (K, 4 ^ 80 / minCeilKnownTop 80 K))
#eval ([1, 3, 5, 6, 8, 12, 20, 160].map fun K => (K, 4 ^ 160 / minCeilKnownTop 160 K))

/-- Kernel-checked: even with the branch at every rank `≤ 20` proved, the
minimal ceiling at `s = 80` still exceeds `2 ^ (s + 1)` by a factor `> 10 ^ 9`.
So the escape from `IntervalCeiling` that T1's own §4 uses does NOT reach the
target. -/
theorem branch_knowledge_20_does_not_help :
    10 ^ 9 * 2 ^ (80 + 1) < minCeilKnownTop 80 20 := by decide +kernel

/-- And full branch knowledge DOES collapse it — confirming that
branch-blindness is exactly the load-bearing hypothesis of §4. -/
theorem full_branch_knowledge_collapses :
    minCeilKnownTop 80 80 = seamResidualUpto 80 (80 - 1) + 1 := by decide +kernel

/-! ## 5. Faithfulness of `ResidualInvariant` to C6

C6's measurement note reads: "the residual after rank `d` has been offered
stays strictly below `2 ^ (2 * s - d)` … at every `d` and every `s` tested"
and "At `d = s - 1` that is exactly `ρ s < 2 ^ (s + 1)`".

The second sentence pins the indexing convention uniquely: it forces
`residual (s-1) = ρ s` and `2 ^ (2*s-(s-1)) = 2 ^ (s+1)`.  Both are what
T1's `seamResidualUpto` gives.  Checked here at a concrete row. -/

example : seamResidualUpto 30 (30 - 1) = seamIntegerGreedyRemainder 30 :=
  seamResidualUpto_last (by norm_num)

example : (2 : ℕ) ^ (2 * 30 - (30 - 1)) = 2 ^ (30 + 1) := by norm_num

/-- The alternative reading — "residual *before* rank `d` is offered" — is
refuted at the same row, so the refutation does not depend on the convention:
`seamResidualUpto 13 6` (before rank 7) also exceeds `2 ^ (2*13-7)`. -/
theorem alt_reading_also_fails : 2 ^ (2 * 13 - 7) ≤ seamResidualUpto 13 (7 - 1) := by
  norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-! ## 6. The one place where the hypothesis equals the conclusion

`remainder_lt_of_weightCeiling` instantiates `WeightCeilingAt s` at `d = s-1`
and rewrites; nothing else happens.  Recorded here explicitly: the `d = s-1`
slice of the hypothesis is already logically equivalent to the conclusion. -/

theorem weightCeiling_slice_iff {s : ℕ} (hs : 4 ≤ s) :
    (seamResidualUpto s (s - 1) < truncatedMersenneWeight s (s - 1))
      ↔ seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 4 := by
  rw [seamResidualUpto_last (by omega), RemC6.truncatedMersenneWeight_terminal hs]

end ErdosProblems.Three.VerifyT1
