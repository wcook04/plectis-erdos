/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.AngleB2
import Erdos249257.HalfCylinderLastProducerContradiction
import Erdos249257.HalfCylinderLargestSkipInduction

/-!
# Skip Wire1: conditional consequences of an unexhibited landing equation

This file does not close a branch of Erdős #257.  It separates two kinds of
statements that earlier prose conflated.

## PROVED: consequences of a right-tail hypothesis

The corpus theorem

  `seamGreedyEventuallyRight_iff_half_not_mem :
      SeamGreedyEventuallyRight ↔ (1/2 : ℝ) ∉ mersenneAchievementSet`

implies that an assumed all-right tail rules out the half-membership disjunct.
Thus `allRight_branch_disjunction_collapse` proves, for every proposition `P`,

  `(P ∨ (1/2 : ℝ) ∈ mersenneAchievementSet) ↔ P`

under that tail hypothesis.  At a producer row, the same tail freezes the
largest false rank.  The support and right-tail theorems in Sections 1, 2, and
4 do not use the landing equation.

## PROVED, CONDITIONAL, AND UNINSTANTIATED

The theorems in Sections 3, 5, and 6 that assume

  `Recon257.seamExcess (D + 1) = 2`

are logical consequences of that equation.  They do not describe an exhibited
greedy row.  Direct evaluation of the concrete greedy gives the following
status:

* **MEASURED:** `Recon257.seamExcess s ≠ 2` for every `s ∈ [5,102]`.
  The consumed range begins at `s = D+1 ≥ 61`, so no instance exists in its
  checked portion.  Values in this range have magnitude comparable to `2^s`.
* `Recon257.seamExcess` is an auxiliary quantity on the concrete
  `seamGreedyWord`.  The corpus's actual final-middle-cell branch instead
  quantifies a hypothetical candidate support and states its conditions using
  `producerCarry` and `erdosSupportSeries`.  Failure of the concrete landing
  equation does not refute that corpus branch; it shows that Wire1 does not
  address it.
* `AngleB2.allRight_landingExcess_two_impossible`, on which the conditional
  skip statements below depend, also assumes `hcof`.  In the audited range,
  every `D` satisfying `hcof` already dies by depth `3` under the concrete
  `belowPulse`; `hcof` fails at the known surviving classes
  `D = 101, 122, 164, 314, 545, 629, 1112`.
* `SkipD1.exists_bound_allRight_landingExcess_two_impossible` excludes zero
  classes: its bound lies beyond every class admitted by its own hypotheses,
  while its alternative branch contradicts the all-right hypothesis directly.

Wire1 inherits both the unobserved landing equation and the zero-class
`AngleB2`/`SkipD1` route.  Its derived skip statements are therefore
conditional descriptions of a configuration not exhibited by the concrete
data, not progress on Erdős #257.

## RETRACTED

Earlier prose called the early-tail theorem a genuine branch closure and called
the derived large skip positive information about the live branch.  Those
claims were too strong.  The early-tail condition is incompatible with the
producer-row setting, and every derived large-skip statement also assumes the
unobserved landing equation.  Erdős #257 remains open.
-/

namespace Erdos249257

namespace Wire1

open HalfCylinderIntegerGreedy

/-! ## 1. PROVED: the right-tail hypothesis refutes the membership disjunct -/

/-- **PROVED, CONDITIONAL ON `hright`.**  An eventual right tail is exactly
half non-membership.  This restates the corpus classification in the
hypothesis shape used here; it does not establish that such a tail occurs. -/
theorem half_not_mem_of_rightTail {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (1 / 2 : ℝ) ∉ mersenneAchievementSet :=
  seamGreedyEventuallyRight_iff_half_not_mem.mp ⟨S, hS5, hright⟩

/-- **PROVED, CONDITIONAL ON `hright`.**  Under the all-right tail hypothesis
of `AngleB2.allRight_landingExcess_two_impossible`, `1/2` is not in the
Mersenne achievement set. -/
theorem allRight_half_not_mem (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (1 / 2 : ℝ) ∉ mersenneAchievementSet :=
  half_not_mem_of_rightTail (by omega) hright

/-- **PROVED, CONDITIONAL ON `hright`.**  For every proposition `P`, adjoining
the half-membership disjunct to `P` changes nothing under an all-right tail.
This is a logical collapse of the proposed disjunction, not a proof that the
remaining proposition `P` holds. -/
theorem allRight_branch_disjunction_collapse (P : Prop) (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (P ∨ (1 / 2 : ℝ) ∈ mersenneAchievementSet) ↔ P := by
  constructor
  · rintro (hp | hmem)
    · exact hp
    · exact absurd hmem (allRight_half_not_mem D hD hright)
  · exact Or.inl

/-- **PROVED, CONDITIONAL ON `hright`.**  The same logical collapse with
`P = False`.  This theorem supplies no contradiction by itself. -/
theorem allRight_branch_resolved_iff_false (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (False ∨ (1 / 2 : ℝ) ∈ mersenneAchievementSet) ↔ False :=
  allRight_branch_disjunction_collapse False D hD hright

/-- **PROVED, CONDITIONAL ON `hright`.**  Every hypothesis that implies half
membership is refuted under an all-right tail.  In particular the
first-crossing socket of `HalfCylinderLargestSkipInduction` cannot be combined
with that tail hypothesis. -/
theorem not_largestSkipLateStepSocket_of_rightTail {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ¬ LargestSkipLateStepSocket := fun hstep =>
  half_not_mem_of_rightTail hS5 hright
    (half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket hstep)

/-! ## 2. PROVED: what a producer row and right tail imply

Under `hright` the largest false rank is frozen at the producer rank `D`, and
`D` is late for every row of the three-row window.  Consequently the right
disjunct of `cofRanks s ⊆ support ∨ LargestSkipLateAt s` holds there.  This
gives no information about the left disjunct or the cofactor ranks. -/

/-- **PROVED, CONDITIONAL ON `hUM` AND `hright`.**  Under an all-right tail
from `D+1` after a producer row `D`, the largest false rank remains `D`. -/
theorem isLargestFalseRank_frozen (D : ℕ) (hD : 5 ≤ D)
    (hUM : SeamGreedyUpperOrMiddleAt D hD)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ∀ k : ℕ, IsLargestFalseRank (seamGreedyWord (D + 1 + k)) D := by
  intro k
  induction k with
  | zero =>
      simpa using
        seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle D hD hUM
  | succ k ih =>
      rw [show D + 1 + (k + 1) = (D + 1 + k) + 1 by ring,
        hright (D + 1 + k) (by omega)]
      exact ih.extend_true (by omega)

/-- **PROVED, CONDITIONAL ON `hUM` AND `hright`.**  Every row from `D+1` to
just below `3*D/2` then has `D` as a late largest false rank. -/
theorem largestSkipLateAt_of_frozen (D : ℕ) (hD : 5 ≤ D)
    (hUM : SeamGreedyUpperOrMiddleAt D hD)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {s : ℕ} (h1 : D + 1 ≤ s) (h2 : 2 * s < 3 * D) :
    LargestSkipLateAt s := by
  refine ⟨D, ?_, h2⟩
  have h := isLargestFalseRank_frozen D hD hUM hright (s - (D + 1))
  rwa [show D + 1 + (s - (D + 1)) = s by omega] at h

/-- **PROVED, CONDITIONAL ON `hUM` AND `hright`.**  Every one of the three
rows `D+1, D+2, D+3` in AngleB2's ratchet window already satisfies
`LargestSkipLateAt`.  Thus the disjunction
`cofRanks s ⊆ seamWordSupport (seamGreedyWord s) ∨ LargestSkipLateAt s`
is true there through its right disjunct and carries no information about the
cofactor ranks. -/
theorem ratchetWindow_all_late (D : ℕ) (hD : 60 ≤ D)
    (hUM : SeamGreedyUpperOrMiddleAt D (by omega))
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ∀ s : ℕ, D + 1 ≤ s → s < D + 4 → LargestSkipLateAt s := by
  intro s h1 h2
  exact largestSkipLateAt_of_frozen D (by omega) hUM hright h1 (by omega)

/-- **PROVED, CONDITIONAL.**  The same statement in the corpus's concrete
final-middle-cell notation.  The theorem does not assert that its middle-cell
and right-tail hypotheses occur. -/
theorem finalMiddleCell_ratchetWindow_all_late (D : ℕ) (hD : 60 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega : 5 ≤ D)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega : 5 ≤ D)).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse <
          (seamAdjacentCut D (by omega : 5 ≤ D)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ∀ s : ℕ, D + 1 ≤ s → s < D + 4 → LargestSkipLateAt s :=
  ratchetWindow_all_late D hD (Or.inr ⟨hncarry, hmiddle⟩) hright

/-! ## 3. A formal removal of `hcof` that does not reach a live case

If the right tail starts early enough — `2 * S ≤ D + 1` — then all of AngleB2's
cofactor ranks at the landing rows already lie in the *filled* block `[S, s)`,
so the cofactor-selection premise follows from the tail.  The resulting
contradiction still assumes the unobserved equation
`Recon257.seamExcess (D+1) = 2`, and Section 4 proves that the early-tail
condition is incompatible with the producer-row setting. -/

/-- **PROVED, CONDITIONAL ON `hright`.**  Every cofactor rank of a row
`s ≥ 2 * S` lies in the filled block `[S, s)`, hence in the support.  This
support fact does not use the landing equation. -/
theorem cofRanks_subset_of_rightTail {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {s : ℕ} (hs61 : 61 ≤ s) (hs : 2 * S ≤ s) :
    AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := by
  have hsupp := seamWordSupport_add_eq_of_eventually_right S hS5 hright (s - S)
  rw [show S + (s - S) = s by omega] at hsupp
  intro d hd
  have hdlt : d < s := AngleB2.cofRanks_lt s hs61 hd
  have hdS : S ≤ d := by
    rcases AngleB2.cofRanks_cases hd with rfl | rfl | rfl <;> omega
  rw [hsupp]
  exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨hdS, hdlt⟩)

/-- **PROVED, CONDITIONAL, AND UNINSTANTIATED.**  This derives `hcof` from the
early-tail condition and applies
`AngleB2.allRight_landingExcess_two_impossible`.  It still assumes
`Recon257.seamExcess (D+1) = 2`, which has no instance for `D+1 ∈ [5,102]`,
and the early-tail condition fails in the producer-row setting. -/
theorem allRight_landingExcess_two_impossible_of_earlyRightTail
    (S D : ℕ) (hS5 : 5 ≤ S) (hD : 60 ≤ D) (hearly : 2 * S ≤ D + 1)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    False :=
  AngleB2.allRight_landingExcess_two_impossible D hD
    (fun s hs => hright s (by omega)) hlanding
    (fun s h1 _ => cofRanks_subset_of_rightTail hS5 hright (by omega) (by omega))

/-! ## 4. PROVED: the early-tail condition fails at a producer row

A right-tail threshold can never reach back past a producer row. -/

/-- **PROVED, CONDITIONAL ON `hUM` AND `hright`.**  At a producer row `D` the
rank `D` is skipped, so a right-tail threshold must satisfy `D < S`. -/
theorem rightTail_threshold_gt_producer {D S : ℕ} (hD : 5 ≤ D)
    (hUM : SeamGreedyUpperOrMiddleAt D hD)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    D < S := by
  by_contra hcon
  have hSD : S ≤ D := by omega
  obtain ⟨-, -, hDnot, -⟩ :=
    seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle D hD hUM
  refine hDnot ?_
  rw [hright D hSD, seamWordSupport_extend_true (by omega)]
  exact Finset.mem_insert_self _ _

/-- **PROVED, CONDITIONAL ON `hUM` AND `hright`.**  At a producer row the
factor-two condition
`2 * S ≤ D + 1` of `allRight_landingExcess_two_impossible_of_earlyRightTail`
fails. -/
theorem earlyRightTail_never_at_producer {D S : ℕ} (hD : 5 ≤ D)
    (hUM : SeamGreedyUpperOrMiddleAt D hD)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ¬ (2 * S ≤ D + 1) := by
  have := rightTail_threshold_gt_producer hD hUM hright
  omega

/-- **PROVED, CONDITIONAL ON `hUM` AND `hright`.**  The ratchet window ends at
`D+3`, while the first row at which this right-tail argument certifies the
cofactor ranks is at least `2*D+2`.  The gap is at least `D-2`, hence at least
`58` when `D ≥ 60`. -/
theorem cofactor_certification_gap {D S : ℕ} (hD : 60 ≤ D)
    (hUM : SeamGreedyUpperOrMiddleAt D (by omega))
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (D + 4) + (D - 2) ≤ 2 * S ∧ 58 ≤ D - 2 := by
  have := rightTail_threshold_gt_producer (D := D) (by omega) hUM hright
  omega

/-! ## 5. Conditional consequences of the unobserved landing equation

The following statements remove `hcof` from their conclusions by negating the
premise required by AngleB2.  They still assume both an all-right tail and
`Recon257.seamExcess (D+1) = 2`.  Direct evaluation finds no instance of the
landing equation for `D+1 ∈ [5,102]`; these are not exhibited skip
certificates. -/

/-- **PROVED, CONDITIONAL, AND UNINSTANTIATED.**  Under `hright` and the
unobserved landing equation, negating the cofactor-selection premise of
`AngleB2.allRight_landingExcess_two_impossible` yields a cofactor skip in the
three-row window. -/
theorem exists_cofSkip_in_window (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∃ s : ℕ, D + 1 ≤ s ∧ s < D + 4 ∧
      ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := by
  by_cases h : ∀ s : ℕ, D + 1 ≤ s → s < D + 4 →
      AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)
  · exact (AngleB2.allRight_landingExcess_two_impossible D hD hright hlanding h).elim
  · push Not at h
    obtain ⟨s, h1, h2, h3⟩ := h
    exact ⟨s, h1, h2, h3⟩

/-- **PROVED, CONDITIONAL, AND UNINSTANTIATED.**  Under the same hypotheses,
the cofactor skip can be pulled back to `seamGreedyWord (D+1)`, producing a
rank `d` with `D + 1 ≤ 2 * d` and `d < D`.  This is a statement about the
unexhibited landing configuration, not a skip found in concrete data. -/
theorem allRight_landingExcess_two_forces_large_frozen_skip
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∃ d : ℕ, D + 1 ≤ 2 * d ∧ d < D ∧
      d ∉ seamWordSupport (seamGreedyWord (D + 1)) := by
  obtain ⟨s, h1, h2, h3⟩ := exists_cofSkip_in_window D hD hright hlanding
  rw [Finset.not_subset] at h3
  obtain ⟨d, hd, hdns⟩ := h3
  have hcases := AngleB2.cofRanks_cases hd
  refine ⟨d, ?_, ?_, ?_⟩
  · rcases hcases with rfl | rfl | rfl <;> omega
  · rcases hcases with rfl | rfl | rfl <;> omega
  · intro hmem
    have hsupp :=
      seamWordSupport_add_eq_of_eventually_right (D + 1) (by omega) hright (s - (D + 1))
    rw [show D + 1 + (s - (D + 1)) = s by omega] at hsupp
    exact hdns (by rw [hsupp]; exact Finset.mem_union_left _ hmem)

/-- **PROVED, CONDITIONAL, AND UNINSTANTIATED.**  Adding the producer
hypothesis shows that the hypothetical landing word skips both `d` and `D`.
The theorem still depends on the unobserved landing equation. -/
theorem allRight_landingExcess_two_forces_two_large_skips
    (D : ℕ) (hD : 60 ≤ D)
    (hUM : SeamGreedyUpperOrMiddleAt D (by omega))
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∃ d : ℕ, D + 1 ≤ 2 * d ∧ d < D ∧
      d ∉ seamWordSupport (seamGreedyWord (D + 1)) ∧
      D ∉ seamWordSupport (seamGreedyWord (D + 1)) := by
  obtain ⟨d, h1, h2, h3⟩ :=
    allRight_landingExcess_two_forces_large_frozen_skip D hD hright hlanding
  obtain ⟨-, -, hDnot, -⟩ :=
    seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle D (by omega) hUM
  exact ⟨d, h1, h2, h3, hDnot⟩

/-! ## 6. Status

The right-tail facts above explain why a half-membership disjunct cannot help
inside an assumed all-right branch.  The remaining theorems in this section
still assume the landing equation absent from the checked concrete range.
They are consistency statements about a hypothetical configuration and do not
close the branch or advance Erdős #257. -/

/-- **PROVED, CONDITIONAL, AND UNINSTANTIATED.**  Under the displayed producer,
right-tail, and landing hypotheses:

1. `1/2` is *not* in the Mersenne achievement set — the positive horn of the
   intended disjunction is refuted by `hright` itself;
2. every row of the ratchet window is `LargestSkipLateAt` for free, so the skip
   dichotomy is satisfied by its right disjunct and gives no cofactor-selection
   information;
3. the unobserved landing equation implies a large skip in the frozen landing
   word.

Only items 1 and 2 are independent of the landing equation. -/
theorem allRight_branch_status (D : ℕ) (hD : 60 ≤ D)
    (hUM : SeamGreedyUpperOrMiddleAt D (by omega))
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ((1 / 2 : ℝ) ∉ mersenneAchievementSet) ∧
      (∀ s : ℕ, D + 1 ≤ s → s < D + 4 → LargestSkipLateAt s) ∧
      (∃ d : ℕ, D + 1 ≤ 2 * d ∧ d < D ∧
        d ∉ seamWordSupport (seamGreedyWord (D + 1))) :=
  ⟨allRight_half_not_mem D hD hright,
    ratchetWindow_all_late D hD hUM hright,
    allRight_landingExcess_two_forces_large_frozen_skip D hD hright hlanding⟩

/-- **PROVED, CONDITIONAL, AND UNINSTANTIATED.**  This contradiction replaces
`hcof` by an early-tail hypothesis.  It also assumes the unobserved landing
equation.  At producer rows, `earlyRightTail_never_at_producer` refutes the
early-tail hypothesis, so this theorem supplies no live branch closure. -/
theorem allRight_branch_resolved (S D : ℕ) (hS5 : 5 ≤ S) (hD : 60 ≤ D)
    (hearly : 2 * S ≤ D + 1)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    False :=
  allRight_landingExcess_two_impossible_of_earlyRightTail S D hS5 hD hearly hright hlanding

/-- **PROVED, CONDITIONAL, AND UNINSTANTIATED.**  The same implication in the
middle-cell notation used by `HalfFinalMiddlePhaseSieve`.  The notation change
does not remove the incompatible early-tail premise or exhibit a live case. -/
theorem finalMiddleCell_neg_two_impossible_of_earlyRightTail
    (S D : ℕ) (hS5 : 5 ≤ S) (hD : 60 ≤ D) (hearly : 2 * S ≤ D + 1)
    (hncarry : ¬ (seamAdjacentCut D (by omega : 5 ≤ D)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega : 5 ≤ D)).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse <
          (seamAdjacentCut D (by omega : 5 ≤ D)).terminalWeight)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hcell :
      4 * ((seamAdjacentCut D (by omega : 5 ≤ D)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse : ℤ) - 4 = -2) :
    False :=
  allRight_branch_resolved S D hS5 hD hearly hright
    (Recon257.seamExcess_landing_eq_two D (by omega) hncarry hmiddle hcell)

/-- **PROVED.**  The middle-cell producer hypotheses and an all-right tail
imply that `2 * S ≤ D + 1` is false.  Thus the preceding early-tail implication
cannot be applied in this setting. -/
theorem finalMiddleCell_defeats_earlyRightTail
    (S D : ℕ) (hD : 60 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega : 5 ≤ D)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega : 5 ≤ D)).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse <
          (seamAdjacentCut D (by omega : 5 ≤ D)).terminalWeight)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ¬ (2 * S ≤ D + 1) :=
  earlyRightTail_never_at_producer (by omega) (Or.inr ⟨hncarry, hmiddle⟩) hright

/-
## Axiom audit

Checked with `#print axioms`; the `#print` lines are commented out so that
`lake env lean ErdosProblems/Skip/Wire1.lean` exits `0` with empty output.

-- #print axioms half_not_mem_of_rightTail
-- #print axioms allRight_branch_disjunction_collapse
-- #print axioms ratchetWindow_all_late
-- #print axioms allRight_landingExcess_two_impossible_of_earlyRightTail
-- #print axioms earlyRightTail_never_at_producer
-- #print axioms allRight_landingExcess_two_forces_large_frozen_skip
-- #print axioms allRight_branch_status
-- #print axioms allRight_branch_resolved
-/

end Wire1

end Erdos249257
