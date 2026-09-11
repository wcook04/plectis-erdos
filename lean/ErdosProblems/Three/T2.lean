/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.R2
import ErdosProblems.Bit.R3
import ErdosProblems.Half.H1

/-!
# Three T2: the seam row map is the doubling map — exactly, with the error term

`Rem/C3` observed that with `u s = ρ s / 2 ^ s`, `ρ = seamIntegerGreedyRemainder`,
the right-branch recurrence `rightBranch_remainder_succ_eq` reads
`u (s+1) = 2 u s - 1`, that the upper/middle branch is **measured** to read
`u (s+1) = 2 u s + 1`, and that together this looks like `y ↦ 2 y mod 1` in the
coordinate `y = u / 2 + 1/2`.  It stated plainly that the second branch was not
proved and that the pulse made the conjugacy inexact by `O(s / 2 ^ s)`.

This file settles all of that.

## 1. The measured branch, proved

`middleBranch_remainder_succ_eq` — **PROVED, new**:

    `¬ carry s → 4 ρ s < 2 ^ (s+1) + 4 + p s
       → ρ (s+1) + p s = 4 ρ s + 2 ^ (s+1)`

which is exactly `u (s+1) = 2 u s + 1 - p s / 2 ^ (s+1)`, with `p s ≤ 2 (s-2)`
the row's below-pulse.  `middleBranch_remainder_succ_eq_of_small` drops the
branch hypotheses entirely: below a quarter of the doubled gap the remainder
alone determines the branch.

`upperBranch_remainder_succ_eq` and `upperBranch_remainder_succ_eq'` — **PROVED,
new** — supply the third branch, which `Rem/C3` never separated from the middle
one:

    `carry s → ρ (s+1) + 3 * 2 ^ (s+1) + (4 g s + q s) = 4 ρ s`,

i.e. `u (s+1) = 2 u s - 3 - (4 g s + q s)/2 ^ (s+1)`, where `q s` is the
above-pulse and `g s := adjGapExcess s` is the excess of the true adjacent-word
gap `remainder + overshoot` over the nominal `2 ^ (s+1)`.

## 2. The branch thresholds, exactly

`successorCarries_iff` — **PROVED**: the carry fires **iff**

    `3 * 2 ^ (s+1) + 4 g s + q s ≤ 4 ρ s`,

and the middle trigger is `4 ρ s < 2 ^ (s+1) + 4 + p s`.  So the row map is a
three-branch map whose thresholds sit at `u = 1/2 + (4 + p s)/2 ^ (s+2)` and
`u = 3/2 + (4 g s + q s)/2 ^ (s+2)` — the thresholds `1/2` and `3/2` of
`(2u + 1) mod 2` on `[0, 2)`, displaced by explicit defects.
`branch_trichotomy` records that the three cases partition.

## 3. One line for the whole map

`remainder_succ_perturbed_doubling` — **PROVED**: for every `s ≥ 5` there are
`n ≤ 2` and `E ≤ 4 g s + 2 s` with

    `ρ (s+1) + n * 2 ^ (s+2) + E = 4 ρ s + 2 ^ (s+1)`,

equivalently (`y_succ`, in `ℝ`, with `y s = ρ s / 2 ^ (s+1) + 1/2`)

    `y (s+1) = 2 * y s - n - E / 2 ^ (s+2)`.

`n = 0, 1, 2` on the middle, right, carry branch; `E = p s`, `p s + 4`,
`4 g s + q s`.  `hitAt_iff_y_le_one`: a hit is exactly `y s ≤ 1`.

## 4. Is the perturbation summable?  Branch by branch

* **Right and middle: yes, and geometrically.**  `E ≤ 2 s`
  (`remainder_succ_perturbed_doubling_of_not_carry`), so the perturbation is
  at most `s / 2 ^ (s+1)`.  **PROVED.**
* **Carry: it depends on the largest declined rank `d`, and the dependence is
  exact.**  `three_mul_adjGapExcess_eq_exactLateGap` and
  `twentyOne_mul_adjGapExcess_eq_skipHalfGap` transport the corpus's exact
  adjacent-gap identities onto `g s`, and `twentyOne_mul_carryDefect_le` gives,
  throughout the half zone `s < 2 d`,

      `21 (4 g s + q s) ≤ 128 * 4 ^ (s-d) + 42 s + 160`,

  i.e. perturbation `≈ (32/21) * 4 ^ (s-d) / 2 ^ s`.  At a **late** row
  `2 s < 3 d` this is `O(2 ^ (-s/3))` — summable (`four_pow_cube_le_of_late`).
  At the **bottom of the half zone** `d ≈ s/2` it is `Θ(1)`.  **PROVED.**

  This is a concrete large defect, not a maximality statement:
  `Witness.carryDefect_thirteen` computes the defect at `s = 13` to be exactly
  `11044`, so the third branch misses
  `u ↦ 2u - 3` by `2 * 11044 / 2 ^ 15 = 0.674` in `u`
  (`Witness.carryDefect_thirteen_large`).  Row `13` is one of the corpus's four
  known **bad** rows.  At the good rows `19, 25, 31` the same defect is
  `2739, 691, 695`, i.e. `1.3e-3, 5.1e-6, 8.1e-8` after normalisation — machine
  precision.  All six numbers are **PROVED** in the kernel; the classification
  of `19, 25, 31` as good rows is `Bit/R2`'s **MEASUREMENT**, not used in any
  proof here.

  The mechanism is identified exactly, not inferred.  `Witness` certifies the
  largest false rank of row `15` to be `14` (late) and of row `13` to be `7`
  (bottom of the half zone: `13 < 2 * 7` but `2 * 13 > 3 * 7`), and then reads
  off the adjacent-gap excess from the corpus identities:

      `adjGapExcess 15 = 4`      (`4 / 2 ^ 16 = 6.1e-5` of the gap)
      `adjGapExcess 13 = 2760`   (`2760 / 2 ^ 14 = 0.168` of the gap)

  a factor of `690` between two rows two apart.  Every quantity in the exact
  carry recurrence at row `13` is then pinned: `ρ 13 = 15147`, `ρ 14 = 392`,
  `g 13 = 2760`, `q 13 = 4`.

## 5. Shadowing: how exact the conjugacy really is

`shadow_of_not_carry_run` (in `ℕ`) and `y_shadow` (in `ℝ`) — **PROVED**: along a
run of carry-free rows from `N`,

    `y (N+k) = 2 ^ k * (y N - δ) - M`,  `0 ≤ δ ≤ (N+1) / 2 ^ (N+1)`,

for every horizon `k`, with `δ` bounded **uniformly in `k`**.  So the orbit is
not merely close to a doubling orbit: it *is* one, of a point displaced from
`y N` by an explicitly summable amount.  That is the strongest possible form of
  the finite-horizon form of `Rem/C3`'s conjecture, and it holds.

`exists_no_carry_above_of_not_half_mem` and `shadow_of_not_half_mem` — **PROVED**
— then say the negative branch of `#257` is entirely inside that regime: if
`1/2 ∉ mersenneAchievementSet` then the carry never fires past some row (by
`half_mem_of_carryCofinally` below), so only the two summable branches survive
and the whole tail is an exact doubling orbit.

## 6. Why this does **not** resolve `#257`, stated exactly

Three obstructions, all proved here or immediate from what is proved.

1. **`y N` is always dyadic.**  `two_pow_mul_y`: `2 ^ (s+1) * y s = ρ s + 2 ^ s`
   is an integer at *every* row.  The criterion "the initial point is not a
   dyadic rational", which is what would give infinitely many `1` bits, can
   therefore never be applied to `y N` itself.  All of the content sits in the
   displacement `δ`, which is an infinite sum over all future row pulses — an
   object at least as hard as the problem.
2. **The shadowing point drifts.**  `y_shadow` supplies, for each horizon `k`, a
   displacement `δ k`; it does not supply one `δ` for all `k`.  The file does not
   construct the limit.
3. **The uncertainty interval outruns the resolution.**  `y_shadow_interval`
   puts the shadowing point in a fixed interval of length `(N+1)/2 ^ (N+1)`;
   `shadow_interval_covers` shows its `k`-th doubling image has length `≥ 1` once
   `k ≥ N + 1`.  So the conjugacy determines at most `≈ N` further bits, never a
   cofinal statement.

## 7. What is new and unconditional

`hitAt_succ_of_successorCarries` — **PROVED**: a carry at row `s` forces
`ρ (s+1) ≤ 2 ^ (s+1)`, i.e. a *hit* at row `s+1`.  Hence
`half_mem_of_carryCofinally`: **if the successor carries at arbitrarily large
rows then `1/2 ∈ mersenneAchievementSet`** and Erdős `#257`'s `1/2` question
resolves positively.  Combined with `successorCarries_iff` this is an *upper*
excursion criterion — `u s` reaching `3/2 + (4 g s + q s)/2 ^ (s+2)` cofinally —
complementary to `Bit/R2`'s lower one.

`RemainderReachesHalfPointCofinally` is **not** proved here, and neither is
`CarryCofinally`.  Erdős `#257`'s `1/2` question is **not** resolved by this
file.

## Hypothesis status

The finite row hypotheses used by the recurrence and finite-horizon shadowing
theorems are exhibited by kernel-checked instances in section 12.  Two global
hypotheses are not exhibited: `CarryCofinally` is open, and
`(1 / 2 : ℝ) ∉ mersenneAchievementSet`, required by
`exists_no_carry_above_of_not_half_mem` and `shadow_of_not_half_mem`, is the
negative branch of the open problem itself.  Those implications are therefore
conditional; the file proves neither global hypothesis.  The inner carry
predicate is certified only at the finite rows `13, 19, 25, 31`.  Both truth
values of both
triggers occur: `MiddleTrigger` holds at `14` and fails at `9`;
`successorCarries` holds at `13, 19, 25, 31` and fails at `9` and at
`14, 15, 16, 17, 18`.  The exact recurrences are used in reverse to *compute*
`p 14 = 3`, `p 9 = 1`, `g 13 = 2760`, `q 13 = 4`, `g 15 = 4` and the four carry
defects.  The largest-false-rank hypotheses of the two adjacent-gap identities
are discharged outright at rows `13` and `15`.  The carry-free run `[14, 19)`
instantiates the shadowing theorem with `M = 15`, `D = 1241`
(`Witness.shadow_witness`, `Witness.y_shadow_witness`).

The normalized carry defect at row `13` is not the largest even among the early
rows: direct evaluation gives a larger normalized defect at row `5`.  Row `13`
is used because its exact largest-false-rank data are proved here, not because
it is extremal.
-/

namespace ErdosProblems.ThreeT2

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.BitR2

noncomputable section

noncomputable local instance
    {α : Type*} {F : PerturbedFamily α} {C : ℕ}
    (K : F.AdjacentCut C) : Decidable K.successorCarries :=
  Classical.propDecidable _

/-! ## 1. The adjacent-word gap -/

/-- The excess of the actual adjacent-word gap over the nominal gap `2 ^ (s+1)`.
`remainder + overshoot` is exactly `oldSum above - oldSum below`, the distance
between the two seam words bracketing the target. -/
def adjGapExcess (s : ℕ) (hs : 5 ≤ s) : ℕ :=
  seamIntegerGreedyRemainder s + (seamAdjacentCut s hs).overshoot - 2 ^ (s + 1)

/-- The adjacent-word gap is at least the nominal gap `2 ^ (s + 1)`. -/
theorem two_pow_le_adjacentGap {s : ℕ} (hs : 5 ≤ s) :
    2 ^ (s + 1) ≤
      seamIntegerGreedyRemainder s + (seamAdjacentCut s hs).overshoot := by
  have hbelow := (seamAdjacentCut s hs).old_below_add_remainder
  have habove := (seamAdjacentCut s hs).capacity_add_overshoot
  have hbadm := (seamAdjacentCut s hs).below_admissible
  have hastr := (seamAdjacentCut s hs).above_strict
  have hlt := Nat.lt_of_le_of_lt hbadm hastr
  have hsep := PerturbedFamily.separated _ hlt
  rw [seamAdjacentCut_gap_eq] at hsep
  have hrem := seamAdjacentCut_remainder hs
  omega

theorem adjGapExcess_spec {s : ℕ} (hs : 5 ≤ s) :
    seamIntegerGreedyRemainder s + (seamAdjacentCut s hs).overshoot =
      2 ^ (s + 1) + adjGapExcess s hs := by
  have h := two_pow_le_adjacentGap hs
  unfold adjGapExcess
  omega

/-! ## 2. The exact branch thresholds -/

/-- **The carry threshold, exactly.**  The successor carries iff the remainder
has reached three quarters of the doubled gap, displaced by the adjacent-gap
excess and the upper pulse.  In the normalised coordinate `u s = ρ s / 2 ^ s`
this reads `u s ≥ 3/2 + (4 * g s + q s) / 2 ^ (s + 2)`. -/
theorem successorCarries_iff {s : ℕ} (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).successorCarries ↔
      3 * 2 ^ (s + 1) + 4 * adjGapExcess s hs +
          (seamAdjacentCut s hs).abovePulse ≤
        4 * seamIntegerGreedyRemainder s := by
  have hg := adjGapExcess_spec hs
  have hdef : (seamAdjacentCut s hs).successorCarries ↔
      4 * (seamAdjacentCut s hs).overshoot +
        (seamAdjacentCut s hs).abovePulse ≤ 2 ^ (s + 1) := Iff.rfl
  rw [hdef]
  omega

/-- A carry forces the remainder past three quarters of the doubled gap:
`u s ≥ 3/2`. -/
theorem three_mul_two_pow_le_of_successorCarries {s : ℕ} (hs : 5 ≤ s)
    (hc : (seamAdjacentCut s hs).successorCarries) :
    3 * 2 ^ (s + 1) ≤ 4 * seamIntegerGreedyRemainder s := by
  have h := (successorCarries_iff hs).mp hc
  omega

/-! ## 3. The three exact branch recurrences -/

/-- **Exact middle-branch remainder recurrence.**  This is the branch that
`Rem/C3` could only *measure*: in the normalised coordinate it says
`u (s+1) = 2 * u s + 1 - p s / 2 ^ (s+1)`.  Here it is proved. -/
theorem middleBranch_remainder_succ_eq
    {s : ℕ} (hs : 5 ≤ s)
    (hnc : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmid : 4 * seamIntegerGreedyRemainder s <
      2 ^ (s + 1) + 4 + (seamAdjacentCut s hs).belowPulse) :
    seamIntegerGreedyRemainder (s + 1) + (seamAdjacentCut s hs).belowPulse =
      4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1) := by
  classical
  have htri := (seamAdjacentCut s hs).nextRemainder_trichotomy
  have hnext := seamAdjacentCut_nextRemainder hs
  have hrem := seamAdjacentCut_remainder hs
  have hgap : (seamPerturbedFamily s (by omega)).gap = 2 ^ (s + 1) := rfl
  have hterm : (seamAdjacentCut s hs).terminalWeight = 2 * 2 ^ (s + 1) + 4 := rfl
  have hbp : (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) :=
    seamAdjacentCut_belowPulse_le hs
  have hpc : 2 * (s - 2) + 4 < 2 ^ (s + 1) :=
    by have := two_mul_add_four_lt_two_pow_succ (show 3 ≤ s by omega); omega
  have hmid' : 4 * (seamAdjacentCut s hs).remainder +
      (seamPerturbedFamily s (by omega)).gap -
      (seamAdjacentCut s hs).belowPulse <
      (seamAdjacentCut s hs).terminalWeight := by
    rw [hrem, hgap, hterm]; omega
  rw [if_neg hnc, if_pos hmid'] at htri
  rw [← hnext, htri, hrem, hgap]
  omega

/-- **Exact upper (carry) branch remainder recurrence, direct form.**  The
successor remainder is the unused part of the new gap. -/
theorem upperBranch_remainder_succ_eq
    {s : ℕ} (hs : 5 ≤ s)
    (hc : (seamAdjacentCut s hs).successorCarries) :
    seamIntegerGreedyRemainder (s + 1) +
        (4 * (seamAdjacentCut s hs).overshoot +
          (seamAdjacentCut s hs).abovePulse) = 2 ^ (s + 1) := by
  classical
  have htri := (seamAdjacentCut s hs).nextRemainder_trichotomy
  have hnext := seamAdjacentCut_nextRemainder hs
  have hgap : (seamPerturbedFamily s (by omega)).gap = 2 ^ (s + 1) := rfl
  rw [if_pos hc] at htri
  have hc' : 4 * (seamAdjacentCut s hs).overshoot +
      (seamAdjacentCut s hs).abovePulse ≤ 2 ^ (s + 1) := hc
  rw [← hnext, htri, hgap]
  omega

/-- **Exact upper (carry) branch recurrence in doubling form.**  Eliminating the
overshoot through the adjacent-gap excess turns the carry branch into
`u (s+1) = 2 * u s - 3 - (4 * g s + q s) / 2 ^ (s+1)`. -/
theorem upperBranch_remainder_succ_eq'
    {s : ℕ} (hs : 5 ≤ s)
    (hc : (seamAdjacentCut s hs).successorCarries) :
    seamIntegerGreedyRemainder (s + 1) + 3 * 2 ^ (s + 1) +
        (4 * adjGapExcess s hs + (seamAdjacentCut s hs).abovePulse) =
      4 * seamIntegerGreedyRemainder s := by
  have h := upperBranch_remainder_succ_eq hs hc
  have hg := adjGapExcess_spec hs
  omega

/-! ## 4. The exact branch partition -/

/-- The middle-branch trigger, in explicit remainder form: `u s < 1/2 +
(4 + p s) / 2 ^ (s + 2)`. -/
def MiddleTrigger (s : ℕ) (hs : 5 ≤ s) : Prop :=
  4 * seamIntegerGreedyRemainder s <
    2 ^ (s + 1) + 4 + (seamAdjacentCut s hs).belowPulse

theorem middleCond_iff {s : ℕ} (hs : 5 ≤ s) :
    (4 * (seamAdjacentCut s hs).remainder +
        (seamPerturbedFamily s (by omega)).gap -
        (seamAdjacentCut s hs).belowPulse <
      (seamAdjacentCut s hs).terminalWeight) ↔ MiddleTrigger s hs := by
  have hrem := seamAdjacentCut_remainder hs
  have hgap : (seamPerturbedFamily s (by omega)).gap = 2 ^ (s + 1) := rfl
  have hterm : (seamAdjacentCut s hs).terminalWeight = 2 * 2 ^ (s + 1) + 4 := rfl
  have hbp : (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) :=
    seamAdjacentCut_belowPulse_le hs
  have hpc : 2 * (s - 2) + 4 < 2 ^ (s + 1) :=
    by have := two_mul_add_four_lt_two_pow_succ (show 3 ≤ s by omega); omega
  rw [hrem, hgap, hterm]
  unfold MiddleTrigger
  omega

/-- The corpus's `U/M` disjunction, restated with both triggers explicit in the
remainder. -/
theorem upperOrMiddle_iff {s : ℕ} (hs : 5 ≤ s) :
    SeamGreedyUpperOrMiddleAt s hs ↔
      (seamAdjacentCut s hs).successorCarries ∨
        (¬ (seamAdjacentCut s hs).successorCarries ∧ MiddleTrigger s hs) := by
  unfold SeamGreedyUpperOrMiddleAt
  rw [middleCond_iff hs]

/-- The three triggers are mutually exclusive and exhaustive: the row map is a
genuine three-branch map with thresholds `u = 1/2 + (4 + p s)/2 ^ (s+2)` and
`u = 3/2 + (4 * g s + q s)/2 ^ (s+2)`. -/
theorem branch_trichotomy {s : ℕ} (hs : 5 ≤ s) :
    (MiddleTrigger s hs ∧ ¬ (seamAdjacentCut s hs).successorCarries) ∨
      (¬ MiddleTrigger s hs ∧ ¬ (seamAdjacentCut s hs).successorCarries) ∨
      (¬ MiddleTrigger s hs ∧ (seamAdjacentCut s hs).successorCarries) := by
  by_cases hc : (seamAdjacentCut s hs).successorCarries
  · have hge := three_mul_two_pow_le_of_successorCarries hs hc
    have hbp : (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) :=
      seamAdjacentCut_belowPulse_le hs
    have hpc : 2 * (s - 2) + 4 < 2 ^ (s + 1) :=
      by have := two_mul_add_four_lt_two_pow_succ (show 3 ≤ s by omega); omega
    refine Or.inr (Or.inr ⟨?_, hc⟩)
    unfold MiddleTrigger
    omega
  · by_cases hm : MiddleTrigger s hs
    · exact Or.inl ⟨hm, hc⟩
    · exact Or.inr (Or.inl ⟨hm, hc⟩)

/-- A right branch is exactly the failure of both triggers. -/
theorem not_upperOrMiddle_iff {s : ℕ} (hs : 5 ≤ s) :
    ¬ SeamGreedyUpperOrMiddleAt s hs ↔
      (¬ (seamAdjacentCut s hs).successorCarries ∧ ¬ MiddleTrigger s hs) := by
  rw [upperOrMiddle_iff hs]
  constructor
  · intro h
    refine ⟨fun hc => h (Or.inl hc), fun hm => ?_⟩
    exact h (Or.inr ⟨fun hc => h (Or.inl hc), hm⟩)
  · rintro ⟨hc, hm⟩ (h | ⟨_, h⟩)
    · exact hc h
    · exact hm h

/-- **Exact right-branch recurrence**, restated from the two explicit triggers.
This is `Erdos249257.rightBranch_remainder_succ_eq` with the branch hypothesis
given in remainder form. -/
theorem rightBranch_remainder_succ_eq_of_triggers {s : ℕ} (hs : 5 ≤ s)
    (hnc : ¬ (seamAdjacentCut s hs).successorCarries)
    (hnm : ¬ MiddleTrigger s hs) :
    seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) +
        ((seamAdjacentCut s hs).belowPulse + 4) =
      4 * seamIntegerGreedyRemainder s := by
  have hR : ¬ SeamGreedyUpperOrMiddleAt s hs :=
    (not_upperOrMiddle_iff hs).mpr ⟨hnc, hnm⟩
  have h := rightBranch_remainder_succ_eq hs hR
  omega

/-! ## 5. The unified perturbed-doubling law -/

/-- **The exact row map, in one line.**  For every `s ≥ 5` there is a *digit*
`n ∈ {0, 1, 2}` and a nonnegative *defect* `E` with

    `ρ (s+1) + n * 2 ^ (s+2) + E = 4 * ρ s + 2 ^ (s+1)`.

Dividing by `2 ^ (s+2)` and writing `y s = ρ s / 2 ^ (s+1) + 1/2` this is
exactly `y (s+1) = 2 * y s - n - E / 2 ^ (s+2)`: the doubling map `y ↦ 2 y`
followed by subtraction of the integer `n`, perturbed by `E / 2 ^ (s+2)`.

The digit is `0` on the middle branch, `1` on the right branch, `2` on the
carry branch, and the defect is `p s`, `p s + 4`, `4 * g s + q s` respectively,
where `p, q ≤ 2 * (s - 2)` are the two row pulses and `g s` is the
adjacent-gap excess. -/
theorem remainder_succ_perturbed_doubling {s : ℕ} (hs : 5 ≤ s) :
    ∃ n E : ℕ, n ≤ 2 ∧ E ≤ 4 * adjGapExcess s hs + 2 * s ∧
      seamIntegerGreedyRemainder (s + 1) + n * 2 ^ (s + 2) + E =
        4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1) := by
  have hbp : (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) :=
    seamAdjacentCut_belowPulse_le hs
  have hap : (seamAdjacentCut s hs).abovePulse ≤ 2 * (s - 2) :=
    seamAdjacentCut_abovePulse_le hs
  have hp2 : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by rw [pow_succ]; ring
  rcases branch_trichotomy hs with ⟨hm, hnc⟩ | ⟨hnm, hnc⟩ | ⟨_, hc⟩
  · exact ⟨0, (seamAdjacentCut s hs).belowPulse, by omega, by omega,
      by have := middleBranch_remainder_succ_eq hs hnc hm; omega⟩
  · exact ⟨1, (seamAdjacentCut s hs).belowPulse + 4, by omega, by omega,
      by have := rightBranch_remainder_succ_eq_of_triggers hs hnc hnm; omega⟩
  · exact ⟨2, 4 * adjGapExcess s hs + (seamAdjacentCut s hs).abovePulse,
      by omega, by omega,
      by have := upperBranch_remainder_succ_eq' hs hc; omega⟩

/-- **The non-carry law with a summable defect.**  Off the carry branch the
defect is at most `2 * s`, so the perturbation of the doubling map is at most
`2 * s / 2 ^ (s+2) = s / 2 ^ (s+1)` — geometrically summable in `s`. -/
theorem remainder_succ_perturbed_doubling_of_not_carry {s : ℕ} (hs : 5 ≤ s)
    (hnc : ¬ (seamAdjacentCut s hs).successorCarries) :
    ∃ n E : ℕ, n ≤ 1 ∧ E ≤ 2 * s ∧
      seamIntegerGreedyRemainder (s + 1) + n * 2 ^ (s + 2) + E =
        4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1) := by
  have hbp : (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) :=
    seamAdjacentCut_belowPulse_le hs
  have hp2 : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by rw [pow_succ]; ring
  by_cases hm : MiddleTrigger s hs
  · exact ⟨0, (seamAdjacentCut s hs).belowPulse, by omega, by omega,
      by have := middleBranch_remainder_succ_eq hs hnc hm; omega⟩
  · exact ⟨1, (seamAdjacentCut s hs).belowPulse + 4, by omega, by omega,
      by have := rightBranch_remainder_succ_eq_of_triggers hs hnc hm; omega⟩

/-! ## 6. The carry defect: exact value, and exactly how small it is -/

/-- **Exact adjacent-gap excess at a late largest false rank**, transported from
`Erdos249257.three_mul_remainder_add_overshoot_eq_exactLateGap`. -/
theorem three_mul_adjGapExcess_eq_exactLateGap
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) :
    3 * adjGapExcess s hs = 2 * 4 ^ (s - d) + 4 := by
  have h := three_mul_remainder_add_overshoot_eq_exactLateGap hs hd hlate
  rw [seamAdjacentCut_remainder hs] at h
  have hg := adjGapExcess_spec hs
  omega

/-- **Exact adjacent-gap excess throughout the half zone** `s < 2 * d`,
transported from `Half/H1`'s unconditional identity.  This covers strictly more
rows than the late zone `2 * s < 3 * d`, and `Skip/D1` places the residue of
`#257` exactly here. -/
theorem twentyOne_mul_adjGapExcess_eq_skipHalfGap
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hhalf : s < 2 * d) :
    21 * adjGapExcess s hs = ErdosProblems.HalfH1.skipHalfGapCorrection s d := by
  have h :=
    ErdosProblems.HalfH1.twentyOne_mul_remainder_add_overshoot_eq_skipHalfGap
      hs hd hhalf
  rw [seamAdjacentCut_remainder hs] at h
  have hg := adjGapExcess_spec hs
  omega

theorem skipHalfGapCorrection_le {s d : ℕ} (hd2 : 2 ≤ d) (hds : d < s) :
    ErdosProblems.HalfH1.skipHalfGapCorrection s d ≤ 32 * 4 ^ (s - d) + 40 := by
  unfold ErdosProblems.HalfH1.skipHalfGapCorrection
    ErdosProblems.HalfH1.halfGapCorrection
  have h1 : (2 : ℕ) ^ (2 * s - 3 * d) ≤ 4 ^ (s - d) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (2 : ℕ) ^ ((2 * s) % 3) ≤ 4 := by
    calc (2 : ℕ) ^ ((2 * s) % 3) ≤ 2 ^ 2 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  split <;> omega

/-- **The carry defect, bounded sharply, throughout the half zone.**  In the
conjugating coordinate the third-branch perturbation is
`(4 * g s + q s) / 2 ^ (s+2) ≤ (128 * 4 ^ (s-d) + 42 s + 160) / (21 * 2 ^ (s+2))`,
i.e. `≈ (32/21) * 4 ^ (s-d) / 2 ^ s`.  So it is geometrically small exactly when
`2 * (s - d)` is bounded away from `s` by a linear amount, and it is `Θ(1)` at
the bottom of the half zone `d ≈ s / 2`. -/
theorem twentyOne_mul_carryDefect_le
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hhalf : s < 2 * d) :
    21 * (4 * adjGapExcess s hs + (seamAdjacentCut s hs).abovePulse) ≤
      128 * 4 ^ (s - d) + 42 * s + 160 := by
  have h := twentyOne_mul_adjGapExcess_eq_skipHalfGap hs hd hhalf
  have hb := skipHalfGapCorrection_le hd.1 hd.2.1
  have hq := seamAdjacentCut_abovePulse_le hs
  omega

/-- At a **late** row the defect is genuinely geometric: `3 * (s - d) ≤ s`, so
`(4 ^ (s-d)) ^ 3 ≤ 4 ^ s`, i.e. `4 ^ (s-d) ≤ 2 ^ (2s/3)` and the third-branch
perturbation is `O(2 ^ (-s/3))` — summable. -/
theorem four_pow_cube_le_of_late {s d : ℕ} (hds : d < s) (hlate : 2 * s < 3 * d) :
    (4 ^ (s - d)) ^ 3 ≤ 4 ^ s := by
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ## 7. A carry resets the remainder below the half point -/

/-- **A carry at row `s` is a hit at row `s + 1`.**  The carry-branch remainder
is the unused part of the new gap, hence at most `2 ^ (s+1)`.  In the doubling
picture this is the statement that the third branch of `y ↦ 2 y mod 1` maps
`[3/2, 2)` back into `[1/2, 1)`. -/
theorem hitAt_succ_of_successorCarries {s : ℕ} (hs : 5 ≤ s)
    (hc : (seamAdjacentCut s hs).successorCarries) :
    seamIntegerGreedyRemainder (s + 1) ≤ 2 ^ (s + 1) := by
  have h := upperBranch_remainder_succ_eq hs hc
  omega

/-- The successor carries at arbitrarily large rows. -/
def CarryCofinally : Prop :=
  ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ ∃ hs : 5 ≤ s,
    (seamAdjacentCut s hs).successorCarries

/-- **A new sufficient condition for Erdős `#257`'s `1/2` question.**  If the
adjacent-word successor carries at arbitrarily large rows, then
`1/2 ∈ mersenneAchievementSet`.

Equivalently, by `successorCarries_iff`: if `u s = ρ s / 2 ^ s` reaches
`3/2 + (4 * g s + q s)/2 ^ (s+2)` at arbitrarily large rows, the question
resolves positively.  Note the direction — this is an *upper* excursion
criterion, complementary to `RemainderReachesHalfPointCofinally`, which is a
*lower* one. -/
theorem half_mem_of_carryCofinally (h : CarryCofinally) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  refine half_mem_of_remainderReachesHalfPointCofinally ?_
  intro N
  obtain ⟨s, hs1, hs5, hc⟩ := h (max N 5)
  exact ⟨s + 1, by omega, by omega, hitAt_succ_of_successorCarries hs5 hc⟩

/-- Numerical carry certificate: if the observed pair `(ρ s, ρ (s+1))` is
incompatible with both the middle and the right recurrence, the branch must be
the carry.  Both tests are decidable computations on `Bit/R3.rem`. -/
theorem successorCarries_of_numeric {s : ℕ} (hs : 5 ≤ s)
    (hright : seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 4 +
        2 * (s - 2) < 4 * seamIntegerGreedyRemainder s)
    (hmid : seamIntegerGreedyRemainder (s + 1) + 2 * (s - 2) <
        4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1)) :
    (seamAdjacentCut s hs).successorCarries := by
  by_contra hnc
  have hbp : (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) :=
    seamAdjacentCut_belowPulse_le hs
  by_cases hm : MiddleTrigger s hs
  · have := middleBranch_remainder_succ_eq hs hnc hm
    omega
  · have := rightBranch_remainder_succ_eq_of_triggers hs hnc hm
    omega

/-! ## 8. Shadowing: the orbit is an exact doubling orbit of a shifted point -/

/-- **Integral shadowing along a carry-free run.**  If no row of
`[N, N + k)` carries, then

    `ρ (N+k) + 2 ^ (N+k) + M * 2 ^ (N+k+1) + D = 4 ^ k * ρ N + 2 ^ (N + 2k)`

for natural numbers `M` (the accumulated digit word) and `D` (the accumulated
defect), with `D < 4 ^ k * (N + 1)`.

Dividing by `2 ^ (N+k+1)` and writing `y s = ρ s / 2 ^ (s+1) + 1/2` this reads

    `y (N+k) = 2 ^ k * (y N - δ) - M`,   `δ = D / 2 ^ (N+2k+1) ≤ (N+1)/2 ^ (N+1)`,

i.e. the row orbit is *exactly* the doubling orbit of the single displaced
initial point `y N - δ`, with the displacement bounded uniformly in the horizon
`k`.  That is the precise sense in which the conjugacy of `Rem/C3` is real. -/
theorem shadow_of_not_carry_run {N : ℕ} (hN : 5 ≤ N) (k : ℕ)
    (hnc : ∀ j : ℕ, j < k → ∀ h : 5 ≤ N + j,
      ¬ (seamAdjacentCut (N + j) h).successorCarries) :
    ∃ M D : ℕ,
      D + (N + 1) + 2 * k ≤ 4 ^ k * (N + 1) ∧
      seamIntegerGreedyRemainder (N + k) + 2 ^ (N + k) +
          M * 2 ^ (N + k + 1) + D =
        4 ^ k * seamIntegerGreedyRemainder N + 2 ^ (N + 2 * k) := by
  induction k with
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | succ k ih =>
      obtain ⟨M, D, hbd, hid⟩ := ih (fun j hj => hnc j (by omega))
      obtain ⟨n, E, hn, hE, hstep⟩ :=
        remainder_succ_perturbed_doubling_of_not_carry
          (s := N + k) (by omega) (hnc k (by omega) (by omega))
      refine ⟨2 * M + n, 4 * D + E, ?_, ?_⟩
      · have h1 : 4 * (D + (N + 1) + 2 * k) ≤ 4 * (4 ^ k * (N + 1)) :=
          Nat.mul_le_mul_left 4 hbd
        have h2 : (4 : ℕ) ^ (k + 1) * (N + 1) = 4 * (4 ^ k * (N + 1)) := by
          rw [pow_succ]; ring
        omega
      · have hp3 : (2 : ℕ) ^ (N + k + 1) = 2 * 2 ^ (N + k) := by
          rw [pow_succ]; ring
        have hp4 : (2 : ℕ) ^ (N + k + 2) = 4 * 2 ^ (N + k) := by
          rw [pow_succ, pow_succ]; ring
        have hp5 : (2 : ℕ) ^ (N + (k + 1)) = 2 * 2 ^ (N + k) := by
          rw [← Nat.add_assoc, pow_succ]; ring
        have hp6 : (2 : ℕ) ^ (N + (k + 1) + 1) = 4 * 2 ^ (N + k) := by
          rw [← Nat.add_assoc, pow_succ, pow_succ]; ring
        have hq : (2 : ℕ) ^ (N + 2 * (k + 1)) = 4 * 2 ^ (N + 2 * k) := by
          rw [show N + 2 * (k + 1) = N + 2 * k + 1 + 1 by ring, pow_succ, pow_succ]
          ring
        have hx : (4 : ℕ) ^ (k + 1) * seamIntegerGreedyRemainder N =
            4 * (4 ^ k * seamIntegerGreedyRemainder N) := by
          rw [pow_succ]; ring
        have hrho : seamIntegerGreedyRemainder (N + (k + 1)) =
            seamIntegerGreedyRemainder (N + k + 1) := by
          rw [← Nat.add_assoc]
        have ha : M * 2 ^ (N + k + 1) = 2 * (M * 2 ^ (N + k)) := by
          rw [hp3]; ring
        have hb : n * 2 ^ (N + k + 2) = 4 * (n * 2 ^ (N + k)) := by
          rw [hp4]; ring
        have hcmb : (2 * M + n) * 2 ^ (N + (k + 1) + 1) =
            8 * (M * 2 ^ (N + k)) + 4 * (n * 2 ^ (N + k)) := by
          rw [hp6]; ring
        rw [hrho, hp5, hcmb, hq, hx]
        rw [ha] at hid
        rw [hb] at hstep
        omega

/-! ## 9. The conjugating coordinate -/

/-- The conjugating coordinate of `Rem/C3`: `y s = u s / 2 + 1/2` where
`u s = ρ s / 2 ^ s`.  A hit (`ρ s ≤ 2 ^ s`) is exactly `y s ≤ 1`. -/
def y (s : ℕ) : ℝ := (seamIntegerGreedyRemainder s : ℝ) / 2 ^ (s + 1) + 1 / 2

theorem half_le_y (s : ℕ) : 1 / 2 ≤ y s := by
  unfold y
  have : (0 : ℝ) ≤ (seamIntegerGreedyRemainder s : ℝ) / 2 ^ (s + 1) := by positivity
  linarith

/-- `HitAt s` in the conjugating coordinate. -/
theorem hitAt_iff_y_le_one (s : ℕ) :
    seamIntegerGreedyRemainder s ≤ 2 ^ s ↔ y s ≤ 1 := by
  have hy : y s ≤ 1 ↔ (seamIntegerGreedyRemainder s : ℝ) ≤ 2 ^ s := by
    unfold y
    rw [pow_succ]
    constructor
    · intro h
      have hh : (seamIntegerGreedyRemainder s : ℝ) / (2 ^ s * 2) ≤ 1 / 2 := by
        linarith
      rw [div_le_iff₀ (by positivity)] at hh
      linarith
    · intro h
      have hh : (seamIntegerGreedyRemainder s : ℝ) / (2 ^ s * 2) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
  rw [hy]
  constructor <;> intro h <;> exact_mod_cast h

/-- **The row map in the conjugating coordinate, exactly.**  For every `s ≥ 5`
there is a digit `n ∈ {0, 1, 2}` and a nonnegative perturbation `ε` with

    `y (s+1) = 2 * y s - n - ε`,   `ε ≤ (4 * g s + 2 * s) / 2 ^ (s+2)`.

Without the `ε` this is verbatim `y ↦ 2 y mod 1` read on the fundamental domain
`[1/2, 3/2)`, with the branch of the mod supplied by `n`. -/
theorem y_succ {s : ℕ} (hs : 5 ≤ s) :
    ∃ (n : ℕ) (ε : ℝ), n ≤ 2 ∧ 0 ≤ ε ∧
      ε ≤ ((4 * adjGapExcess s hs + 2 * s : ℕ) : ℝ) / 2 ^ (s + 2) ∧
      y (s + 1) = 2 * y s - n - ε := by
  obtain ⟨n, E, hn, hE, hid⟩ := remainder_succ_perturbed_doubling hs
  refine ⟨n, (E : ℝ) / 2 ^ (s + 2), hn, by positivity, ?_, ?_⟩
  · gcongr
  · have hidR : (seamIntegerGreedyRemainder (s + 1) : ℝ) +
        (n : ℝ) * 2 ^ (s + 2) + (E : ℝ) =
      4 * (seamIntegerGreedyRemainder s : ℝ) + 2 ^ (s + 1) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hid
    unfold y
    have h1 : (2 : ℝ) ^ (s + 2) = 2 ^ (s + 1) * 2 := by rw [pow_succ]
    rw [h1] at hidR ⊢
    have hpos : (0 : ℝ) < 2 ^ (s + 1) := by positivity
    field_simp
    linarith [hidR]

/-- **Shadowing in the conjugating coordinate.**  Along a carry-free run from
row `N`, the orbit of `y` is *exactly* the orbit of the doubling map started at
the single displaced point `y N - δ`, where `0 ≤ δ ≤ (N+1)/2 ^ (N+1)`
uniformly in the horizon `k`. -/
theorem y_shadow {N : ℕ} (hN : 5 ≤ N) (k : ℕ)
    (hnc : ∀ j : ℕ, j < k → ∀ h : 5 ≤ N + j,
      ¬ (seamAdjacentCut (N + j) h).successorCarries) :
    ∃ (M : ℕ) (δ : ℝ), 0 ≤ δ ∧ δ ≤ ((N : ℝ) + 1) / 2 ^ (N + 1) ∧
      y (N + k) = 2 ^ k * (y N - δ) - M := by
  obtain ⟨M, D, hbd, hid⟩ := shadow_of_not_carry_run hN k hnc
  have e1 : (2 : ℝ) ^ (N + k) = 2 ^ N * 2 ^ k := by rw [pow_add]
  have e2 : (2 : ℝ) ^ (N + k + 1) = 2 ^ N * 2 ^ k * 2 := by
    rw [pow_succ, pow_add]
  have e3 : (2 : ℝ) ^ (N + 2 * k) = 2 ^ N * (2 ^ k) ^ 2 := by
    rw [pow_add, ← pow_mul, mul_comm 2 k]
  have e4 : (2 : ℝ) ^ (N + 2 * k + 1) = 2 ^ N * (2 ^ k) ^ 2 * 2 := by
    rw [pow_succ, e3]
  have e5 : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have e6 : (2 : ℝ) ^ (N + 1) = 2 ^ N * 2 := by rw [pow_succ]
  have hNpos : (0 : ℝ) < 2 ^ N := by positivity
  have hkpos : (0 : ℝ) < 2 ^ k := by positivity
  refine ⟨M, (D : ℝ) / 2 ^ (N + 2 * k + 1), by positivity, ?_, ?_⟩
  · have hD : (D : ℝ) ≤ 4 ^ k * ((N : ℝ) + 1) := by
      have : (D : ℕ) ≤ 4 ^ k * (N + 1) := by omega
      exact_mod_cast this
    rw [div_le_div_iff₀ (by positivity) (by positivity), e4, e6, e5] at *
    nlinarith [hD, hNpos, hkpos, sq_nonneg ((2 : ℝ) ^ k)]
  · have hidR : (seamIntegerGreedyRemainder (N + k) : ℝ) + 2 ^ (N + k) +
        (M : ℝ) * 2 ^ (N + k + 1) + (D : ℝ) =
      4 ^ k * (seamIntegerGreedyRemainder N : ℝ) + 2 ^ (N + 2 * k) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hid
    rw [e1, e2, e3, e5] at hidR
    unfold y
    rw [e2, e4, e6]
    field_simp
    nlinarith [hidR, hNpos, hkpos]

/-- The shadowing displacement lives in a fixed interval, so along a carry-free
run the whole future orbit is the doubling image of *some* point of
`[y N - (N+1)/2 ^ (N+1), y N]`. -/
theorem y_shadow_interval {N : ℕ} (hN : 5 ≤ N) (k : ℕ)
    (hnc : ∀ j : ℕ, j < k → ∀ h : 5 ≤ N + j,
      ¬ (seamAdjacentCut (N + j) h).successorCarries) :
    ∃ (M : ℕ) (z : ℝ),
      y N - ((N : ℝ) + 1) / 2 ^ (N + 1) ≤ z ∧ z ≤ y N ∧
        y (N + k) = 2 ^ k * z - M := by
  obtain ⟨M, δ, hδ0, hδ1, hy⟩ := y_shadow hN k hnc
  exact ⟨M, y N - δ, by linarith, by linarith, hy⟩

/-! ## 10. Where the conjugacy stops -/

/-- `y s` is a dyadic rational of level `s + 1` at **every** row: `2 ^ (s+1) *
y s = ρ s + 2 ^ s` is an integer.  Consequently the criterion "the initial point
is not a dyadic rational", which would give infinitely many `1` bits under an
*unperturbed* doubling map, can never be applied to `y N` itself.  All of the
content sits in the shadowing displacement `δ`, which is an infinite sum over
all future row pulses. -/
theorem two_pow_mul_y (s : ℕ) :
    2 ^ (s + 1) * y s = ((seamIntegerGreedyRemainder s + 2 ^ s : ℕ) : ℝ) := by
  unfold y
  have h : (0 : ℝ) < 2 ^ (s + 1) := by positivity
  push_cast
  field_simp
  rw [pow_succ]
  ring

/-- **The prediction horizon.**  The displacement interval of `y_shadow_interval`
has length `(N+1)/2 ^ (N+1)`; after `k ≥ N + 1` doublings its image has length at
least `1`, i.e. it covers the whole circle and determines no further bit.  So the
exact conjugacy constrains only the first `≈ N` rows past `N`, which is never
enough for a cofinality statement. -/
theorem shadow_interval_covers {N k : ℕ} (h : N + 1 ≤ k) :
    (1 : ℝ) ≤ 2 ^ k * (((N : ℝ) + 1) / 2 ^ (N + 1)) := by
  have h1 : ((2 : ℝ)) ^ (N + 1) ≤ 2 ^ k := by
    exact pow_le_pow_right₀ (by norm_num) h
  have h2 : (0 : ℝ) < 2 ^ (N + 1) := by positivity
  have h3 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) N; linarith
  have key : (2 : ℝ) ^ k * (((N : ℝ) + 1) / 2 ^ (N + 1)) =
      (2 ^ k * ((N : ℝ) + 1)) / 2 ^ (N + 1) := by ring
  rw [key, le_div_iff₀ h2]
  nlinarith [h1, h2, h3]

/-! ## 10b. The negative branch of `#257` is carry-free, hence exactly doubling -/

/-- If `1/2` is *not* achieved then the successor never carries past some row.
Immediate from `half_mem_of_carryCofinally`, but worth isolating: it says the
one branch whose perturbation the corpus cannot bound — the carry branch, whose
defect is `4 * g s + q s` with `g s` the adjacent-gap excess — does not occur at
all in the failure scenario. -/
theorem exists_no_carry_above_of_not_half_mem
    (hnot : (1 / 2 : ℝ) ∉ mersenneAchievementSet) :
    ∃ N : ℕ, 5 ≤ N ∧ ∀ s : ℕ, N ≤ s → ∀ h : 5 ≤ s,
      ¬ (seamAdjacentCut s h).successorCarries := by
  by_contra hcon
  refine hnot (half_mem_of_carryCofinally ?_)
  intro N
  by_contra hN
  exact hcon ⟨max N 5, by omega, fun s hs h hc => hN ⟨s, by omega, h, hc⟩⟩

/-- **The reformulation.**  If Erdős `#257`'s `1/2` question has the negative
answer, then from some row `N` on the seam orbit is *exactly* an orbit of the
doubling map: for every horizon `k`, `y (N+k) = 2 ^ k * z - M` for some point
`z` of the fixed interval `[y N - (N+1)/2 ^ (N+1), y N]` and some integer `M`.

Only the right and middle branches survive there, and both have defect at most
`2 * s`, so the perturbation of the doubling map is summable along the whole
tail.  This is the strongest form the `Rem/C3` conjugacy route supports.  What
it does **not** supply is a single `z` valid for all `k`: the shadowing point
`z = y N - δ k` drifts monotonically with the horizon, and the file does not
construct its limit. -/
theorem shadow_of_not_half_mem
    (hnot : (1 / 2 : ℝ) ∉ mersenneAchievementSet) :
    ∃ N : ℕ, 5 ≤ N ∧ ∀ k : ℕ, ∃ (M : ℕ) (z : ℝ),
      y N - ((N : ℝ) + 1) / 2 ^ (N + 1) ≤ z ∧ z ≤ y N ∧
        y (N + k) = 2 ^ k * z - M := by
  obtain ⟨N, hN, hno⟩ := exists_no_carry_above_of_not_half_mem hnot
  exact ⟨N, hN, fun k =>
    y_shadow_interval hN k (fun j _ h => hno (N + j) (by omega) h)⟩

/-! ## 11. Convenient small-remainder triggers -/

theorem not_successorCarries_of_four_mul_remainder_lt {s : ℕ} (hs : 5 ≤ s)
    (h : 4 * seamIntegerGreedyRemainder s < 3 * 2 ^ (s + 1)) :
    ¬ (seamAdjacentCut s hs).successorCarries := fun hc =>
  absurd (three_mul_two_pow_le_of_successorCarries hs hc) (by omega)

theorem middleTrigger_of_four_mul_remainder_lt {s : ℕ} (hs : 5 ≤ s)
    (h : 4 * seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 4) :
    MiddleTrigger s hs := by
  unfold MiddleTrigger; omega

/-- **Unconditional middle-branch law.**  Below a quarter of the doubled gap the
successor remainder is *exactly* `4 * ρ s + 2 ^ (s+1) - p s`.  No branch
hypothesis is needed: the remainder alone determines the branch there. -/
theorem middleBranch_remainder_succ_eq_of_small {s : ℕ} (hs : 5 ≤ s)
    (h : 4 * seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 4) :
    seamIntegerGreedyRemainder (s + 1) + (seamAdjacentCut s hs).belowPulse =
      4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1) := by
  have hone : (4 : ℕ) ≤ 2 ^ (s + 1) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact middleBranch_remainder_succ_eq hs
    (not_successorCarries_of_four_mul_remainder_lt hs (by omega))
    (middleTrigger_of_four_mul_remainder_lt hs h)

/-! ## 12. Non-vacuity: all three branches occur, with their defects computed -/

namespace Witness

set_option maxRecDepth 200000

theorem rem_eq' (s : ℕ) : seamIntegerGreedyRemainder s = BitR3.rem s :=
  (BitR3.rem_eq s).symm

theorem hs9 : (5 : ℕ) ≤ 9 := by norm_num
theorem hs13 : (5 : ℕ) ≤ 13 := by norm_num
theorem hs14 : (5 : ℕ) ≤ 14 := by norm_num
theorem hs15 : (5 : ℕ) ≤ 15 := by norm_num
theorem hs19 : (5 : ℕ) ≤ 19 := by norm_num
theorem hs25 : (5 : ℕ) ≤ 25 := by norm_num
theorem hs31 : (5 : ℕ) ≤ 31 := by norm_num

theorem remainder_thirteen : seamIntegerGreedyRemainder 13 = 15147 := by
  rw [rem_eq']; decide +kernel

theorem remainder_fourteen : seamIntegerGreedyRemainder 14 = 392 := by
  rw [rem_eq']; decide +kernel

theorem remainder_fifteen : seamIntegerGreedyRemainder 15 = 34333 := by
  rw [rem_eq']; decide +kernel

theorem remainder_nineteen : seamIntegerGreedyRemainder 19 = 924455 := by
  rw [rem_eq']; decide +kernel

theorem remainder_twenty : seamIntegerGreedyRemainder 20 = 549353 := by
  rw [rem_eq']; decide +kernel

theorem remainder_twentyfive : seamIntegerGreedyRemainder 25 = 59218477 := by
  rw [rem_eq']; decide +kernel

theorem remainder_twentysix : seamIntegerGreedyRemainder 26 = 35546625 := by
  rw [rem_eq']; decide +kernel

theorem remainder_thirtyone : seamIntegerGreedyRemainder 31 = 4187487147 := by
  rw [rem_eq']; decide +kernel

theorem remainder_thirtytwo : seamIntegerGreedyRemainder 32 = 3865046005 := by
  rw [rem_eq']; decide +kernel

/-! ### The middle branch really fires, and its pulse is `3` at row `14` -/

theorem middleTrigger_fourteen : MiddleTrigger 14 hs14 :=
  middleTrigger_of_four_mul_remainder_lt hs14
    (by rw [remainder_fourteen]; norm_num)

theorem not_successorCarries_fourteen :
    ¬ (seamAdjacentCut 14 hs14).successorCarries :=
  not_successorCarries_of_four_mul_remainder_lt hs14
    (by rw [remainder_fourteen]; norm_num)

/-- The exact middle-branch recurrence at row `14` pins the row pulse:
`ρ 15 + p 14 = 4 * ρ 14 + 2 ^ 15`, i.e. `34333 + p 14 = 34336`. -/
theorem belowPulse_fourteen : (seamAdjacentCut 14 hs14).belowPulse = 3 := by
  have h := middleBranch_remainder_succ_eq hs14 not_successorCarries_fourteen
    middleTrigger_fourteen
  norm_num [remainder_fourteen, remainder_fifteen] at h
  omega

/-! ### The right branch really fires, and its pulse is `1` at row `9` -/

theorem right_triggers_nine :
    ¬ (seamAdjacentCut 9 hs9).successorCarries ∧ ¬ MiddleTrigger 9 hs9 :=
  (not_upperOrMiddle_iff hs9).mp not_upperOrMiddle_nine

theorem belowPulse_nine : (seamAdjacentCut 9 hs9).belowPulse = 1 := by
  have h := rightBranch_remainder_succ_eq_of_triggers hs9
    right_triggers_nine.1 right_triggers_nine.2
  norm_num [remainder_nine, remainder_ten] at h
  omega

/-! ### The carry branch really fires -/

theorem successorCarries_thirteen :
    (seamAdjacentCut 13 hs13).successorCarries :=
  successorCarries_of_numeric hs13
    (by norm_num [remainder_thirteen, remainder_fourteen])
    (by norm_num [remainder_thirteen, remainder_fourteen])

theorem successorCarries_nineteen :
    (seamAdjacentCut 19 hs19).successorCarries :=
  successorCarries_of_numeric hs19
    (by norm_num [remainder_nineteen, remainder_twenty])
    (by norm_num [remainder_nineteen, remainder_twenty])

theorem successorCarries_twentyfive :
    (seamAdjacentCut 25 hs25).successorCarries :=
  successorCarries_of_numeric hs25
    (by norm_num [remainder_twentyfive, remainder_twentysix])
    (by norm_num [remainder_twentyfive, remainder_twentysix])

theorem successorCarries_thirtyone :
    (seamAdjacentCut 31 hs31).successorCarries :=
  successorCarries_of_numeric hs31
    (by norm_num [remainder_thirtyone, remainder_thirtytwo])
    (by norm_num [remainder_thirtyone, remainder_thirtytwo])

/-- `CarryCofinally` is **not** proved; its inner predicate is certified at a
spread of concrete rows. -/
theorem carry_rows :
    (seamAdjacentCut 13 hs13).successorCarries ∧
      (seamAdjacentCut 19 hs19).successorCarries ∧
      (seamAdjacentCut 25 hs25).successorCarries ∧
      (seamAdjacentCut 31 hs31).successorCarries :=
  ⟨successorCarries_thirteen, successorCarries_nineteen,
    successorCarries_twentyfive, successorCarries_thirtyone⟩

/-! ### The carry defect, measured exactly, at a bad row and at good rows

The carry defect `4 * g s + q s` is what the conjugacy must control: divided by
`2 ^ (s+2)` it is the deviation of the third branch from `u ↦ 2 u - 3`.  Row
`13` is a **bad** row (`Bit/R2.not_largestSkipLateAt_thirteen`), rows `19, 25,
31` are good.  The four exact values below are

    `s = 13`:  `11044 / 2 ^ 15 = 0.337`      (bad row)
    `s = 19`:  ` 2739 / 2 ^ 21 = 1.3e-3`     (good row)
    `s = 25`:  `  691 / 2 ^ 27 = 5.1e-6`     (good row)
    `s = 31`:  `  695 / 2 ^ 33 = 8.1e-8`     (good row)

so the third branch of the doubling map is exact to machine precision at good
rows and wrong by a third of the unit interval at the bad row. -/
theorem carryDefect_thirteen :
    4 * adjGapExcess 13 hs13 + (seamAdjacentCut 13 hs13).abovePulse = 11044 := by
  have h := upperBranch_remainder_succ_eq' hs13 successorCarries_thirteen
  norm_num [remainder_thirteen, remainder_fourteen] at h
  omega

theorem carryDefect_nineteen :
    4 * adjGapExcess 19 hs19 + (seamAdjacentCut 19 hs19).abovePulse = 2739 := by
  have h := upperBranch_remainder_succ_eq' hs19 successorCarries_nineteen
  norm_num [remainder_nineteen, remainder_twenty] at h
  omega

theorem carryDefect_twentyfive :
    4 * adjGapExcess 25 hs25 + (seamAdjacentCut 25 hs25).abovePulse = 691 := by
  have h := upperBranch_remainder_succ_eq' hs25 successorCarries_twentyfive
  norm_num [remainder_twentyfive, remainder_twentysix] at h
  omega

theorem carryDefect_thirtyone :
    4 * adjGapExcess 31 hs31 + (seamAdjacentCut 31 hs31).abovePulse = 695 := by
  have h := upperBranch_remainder_succ_eq' hs31 successorCarries_thirtyone
  norm_num [remainder_thirtyone, remainder_thirtytwo] at h
  omega

/-- **The bad-row carry defect is not small.**  At `s = 13` the defect exceeds
`2 ^ (s+2) / 4`, i.e. the third branch misses `u ↦ 2 u - 3` by more than a
quarter of the unit interval.  So `Rem/C3`'s measured conjugacy is
quantitatively **false** at a bad row. -/
theorem carryDefect_thirteen_large :
    2 ^ (13 + 2) < 4 * (4 * adjGapExcess 13 hs13 +
      (seamAdjacentCut 13 hs13).abovePulse) := by
  rw [carryDefect_thirteen]; norm_num

/-! ### The late-row bound on the adjacent-gap excess is non-vacuous -/

theorem adjGapExcess_late_bound_fifteen :
    ∃ d : ℕ, 2 * 15 < 3 * d ∧
      3 * adjGapExcess 15 hs15 = 2 * 4 ^ (15 - d) + 4 ∧
      (4 ^ (15 - d)) ^ 3 ≤ 4 ^ 15 := by
  obtain ⟨d, hd, hlate⟩ := BitR3.lateAt_15
  exact ⟨d, hlate, three_mul_adjGapExcess_eq_exactLateGap hs15 hd hlate,
    four_pow_cube_le_of_late hd.2.1 hlate⟩

theorem carryDefect_bound_fifteen :
    ∃ d : ℕ, 15 < 2 * d ∧
      21 * (4 * adjGapExcess 15 hs15 + (seamAdjacentCut 15 hs15).abovePulse) ≤
        128 * 4 ^ (15 - d) + 42 * 15 + 160 := by
  obtain ⟨d, hd, hlate⟩ := BitR3.lateAt_15
  exact ⟨d, by omega, twentyOne_mul_carryDefect_le hs15 hd (by omega)⟩

/-! ### The largest false ranks of rows `13` and `15`, and every quantity in the
carry recurrence at row `13`

Row `15` is **late**: its largest false rank is the terminal rank `14`, so the
adjacent-gap excess is `4`, i.e. `4 / 2 ^ 16 = 6.1e-5` of the gap.  Row `13` is
**bad**: its largest false rank is `7`, at the very bottom of the half zone
(`13 < 14 = 2 * 7` but `26 = 2 * 13 > 21 = 3 * 7`), so the excess is `2760`,
i.e. `0.168` of the gap.  A factor `690`, from one row to another two apart. -/

theorem isLargestFalseRank_thirteen_seven :
    IsLargestFalseRank (seamGreedyWord 13) 7 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [SkipD3.mem_support_iff (show (2 : ℕ) ≤ 7 by norm_num)
      (show (7 : ℕ) < 13 by norm_num)]
    decide +kernel
  · intro e he1 he2
    interval_cases e
    · rw [SkipD3.mem_support_iff (by norm_num) (by norm_num)]; decide +kernel
    · rw [SkipD3.mem_support_iff (by norm_num) (by norm_num)]; decide +kernel
    · rw [SkipD3.mem_support_iff (by norm_num) (by norm_num)]; decide +kernel
    · rw [SkipD3.mem_support_iff (by norm_num) (by norm_num)]; decide +kernel
    · rw [SkipD3.mem_support_iff (by norm_num) (by norm_num)]; decide +kernel

theorem isLargestFalseRank_fifteen_fourteen :
    IsLargestFalseRank (seamGreedyWord 15) 14 := by
  refine ⟨by norm_num, by norm_num, ?_, fun e he1 he2 => absurd he1 (by omega)⟩
  rw [SkipD3.mem_support_iff (show (2 : ℕ) ≤ 14 by norm_num)
    (show (14 : ℕ) < 15 by norm_num)]
  decide +kernel

/-- The adjacent-gap excess at the late row `15`: exactly `4`. -/
theorem adjGapExcess_fifteen : adjGapExcess 15 hs15 = 4 := by
  have h := three_mul_adjGapExcess_eq_exactLateGap hs15
    isLargestFalseRank_fifteen_fourteen (by norm_num)
  norm_num at h
  omega

/-- The adjacent-gap excess at the bad row `13`: exactly `2760`, computed from
`Half/H1`'s half-zone identity at `d = 7`. -/
theorem adjGapExcess_thirteen : adjGapExcess 13 hs13 = 2760 := by
  have h := twentyOne_mul_adjGapExcess_eq_skipHalfGap hs13
    isLargestFalseRank_thirteen_seven (by norm_num)
  norm_num [ErdosProblems.HalfH1.skipHalfGapCorrection,
    ErdosProblems.HalfH1.halfGapCorrection] at h
  omega

/-- With the excess known, the exact carry recurrence pins the above-pulse too:
`ρ 14 + 3 * 2 ^ 14 + (4 * 2760 + 4) = 4 * ρ 13`. -/
theorem abovePulse_thirteen : (seamAdjacentCut 13 hs13).abovePulse = 4 := by
  have h := carryDefect_thirteen
  rw [adjGapExcess_thirteen] at h
  omega

/-- The hypothesis of `carryDefect_thirteen_forces_low_rank` is discharged. -/
theorem largestFalseRank_thirteen_is_seven :
    IsLargestFalseRank (seamGreedyWord 13) 7 ∧ 13 < 2 * 7 :=
  ⟨isLargestFalseRank_thirteen_seven, by norm_num⟩

/-- Row `13` is a **bad** row (`Bit/R2.not_largestSkipLateAt_thirteen`) and its
carry defect is `11044`, more than a quarter of `2 ^ 15`.  Fed back through
`twentyOne_mul_carryDefect_le`, that pins its largest false rank to the very
bottom of the half zone: `d = 7`, with `2 * 13 = 26 > 21 = 3 * 7`.  So the
third branch departs from `u ↦ 2 u - 3` exactly when the largest declined rank
is low — the configuration the negative branch of `#257` consists of. -/
theorem carryDefect_thirteen_forces_low_rank
    {d : ℕ} (hd : IsLargestFalseRank (seamGreedyWord 13) d) (hhalf : 13 < 2 * d) :
    d = 7 := by
  have h := twentyOne_mul_carryDefect_le hs13 hd hhalf
  rw [carryDefect_thirteen] at h
  have hds : d < 13 := hd.2.1
  have hlow : 7 ≤ d := by omega
  interval_cases d
  · rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

/-! ### `hitAt_succ_of_successorCarries` is non-vacuous -/

theorem hitAt_fourteen : seamIntegerGreedyRemainder 14 ≤ 2 ^ 14 :=
  hitAt_succ_of_successorCarries hs13 successorCarries_thirteen

/-! ### A genuine carry-free run, so the shadowing theorem is non-vacuous

Rows `14, 15, 16, 17, 18` all satisfy `4 * ρ s < 3 * 2 ^ (s+1)` (equivalently
`u s < 3/2`), hence none of them carries; row `19` does.  So the hypothesis of
`shadow_of_not_carry_run` and `y_shadow` holds with `N = 14`, `k = 5`. -/

theorem remainder_sixteen : seamIntegerGreedyRemainder 16 = 71791 := by
  rw [rem_eq']; decide +kernel

theorem remainder_eighteen : seamIntegerGreedyRemainder 18 = 362187 := by
  rw [rem_eq']; decide +kernel

theorem carryFree_run_fourteen :
    ∀ j : ℕ, j < 5 → ∀ h : 5 ≤ 14 + j,
      ¬ (seamAdjacentCut (14 + j) h).successorCarries := by
  intro j hj h
  interval_cases j
  · exact not_successorCarries_of_four_mul_remainder_lt h
      (by norm_num [remainder_fourteen])
  · exact not_successorCarries_of_four_mul_remainder_lt h
      (by norm_num [remainder_fifteen])
  · exact not_successorCarries_of_four_mul_remainder_lt h
      (by norm_num [remainder_sixteen])
  · exact not_successorCarries_of_four_mul_remainder_lt h
      (by norm_num [remainder_seventeen])
  · exact not_successorCarries_of_four_mul_remainder_lt h
      (by norm_num [remainder_eighteen])

/-- The integral shadowing law, instantiated on the genuine five-row carry-free
run `[14, 19)`.  Numerically `M = 15`, `D = 1241`, well inside the bound
`D + 15 + 10 ≤ 4 ^ 5 * 15 = 15360`. -/
theorem shadow_witness :
    ∃ M D : ℕ,
      D + (14 + 1) + 2 * 5 ≤ 4 ^ 5 * (14 + 1) ∧
      seamIntegerGreedyRemainder (14 + 5) + 2 ^ (14 + 5) +
          M * 2 ^ (14 + 5 + 1) + D =
        4 ^ 5 * seamIntegerGreedyRemainder 14 + 2 ^ (14 + 2 * 5) :=
  shadow_of_not_carry_run hs14 5 carryFree_run_fourteen

/-- The same run in the conjugating coordinate: `y 19` is *exactly* the fifth
doubling iterate of a point of `[y 14 - 15/2 ^ 15, y 14]`. -/
theorem y_shadow_witness :
    ∃ (M : ℕ) (δ : ℝ), 0 ≤ δ ∧ δ ≤ ((14 : ℝ) + 1) / 2 ^ (14 + 1) ∧
      y (14 + 5) = 2 ^ 5 * (y 14 - δ) - M := by
  have h := y_shadow hs14 5 carryFree_run_fourteen
  norm_num at h ⊢
  exact h

end Witness

end

end ErdosProblems.ThreeT2
