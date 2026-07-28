/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.AngleB2

/-!
# Angle D1: half-zone cofactor arithmetic and conditional skip statements

This file does **not** close the all-right-tail branch of Erdős #257 and does
not discharge `AngleB2`'s `hcof` hypothesis for any class to which the claimed
cutoff applies.  Erdős #257 remains open.

`ErdosProblems/Lift/AngleB2.lean` proves a conditional contradiction from
three hypotheses at a class `D ≥ 60`: an all-right tail, the landing equality
`Recon257.seamExcess (D+1) = 2`, and

    hcof : ∀ s, D+1 ≤ s → s < D+4 → cofRanks s ⊆ seamWordSupport (seamGreedyWord s)

The last part of this file derives further implications from those assumptions.
Those implications are formally proved but do not describe an exhibited
configuration:

* **MEASURED:** direct evaluation of the concrete greedy gives
  `Recon257.seamExcess s ≠ 2` for every tested real row
  `s ∈ [5, 102]`.  Thus the landing hypothesis is false throughout that
  finite range.
* **PROVED:**
  `SkipD1.probe_certificationThreshold_gt_landing` in
  `ErdosProblems/Skip/verify/V1.lean` shows that any eventual-`hcof` threshold
  for a class satisfying the branch assumptions must be strictly greater than
  its landing row.  The derived
  `SkipD1.probe_bound_never_reaches_live_class` states the resulting
  incompatibility directly.  Hence the existential bound in
  `exists_bound_allRight_landingExcess_two_impossible` exceeds every `D`
  admitted by the branch assumptions and excludes zero classes.
* **PROVED:** in the other disjunct,
  `1/2 ∈ mersenneAchievementSet`; the `hright` hypothesis supplies
  `SeamGreedyEventuallyRight`, which is equivalent to
  `1/2 ∉ mersenneAchievementSet`.  This disjunct is contradictory and yields
  no new exclusion.

The unconditional content is the cofactor-rank arithmetic, the rowwise
dichotomy, and the cofinal membership implication described next.

## PROVED: the half-row threshold

`LargestSkipLateAt s` asks the row's largest false rank `d` to satisfy
`2 * s < 3 * d`.  The candidate forms `(2s+1)/3` and `2(s+1)/3` sit in that
zone when they occur, but the candidate `(s+1)/2` never does
(`halfCofRank_not_late`).  Dropping the threshold to `s < 2 * d` captures every
member of `cofRanks s` (`cofRanks_half`), and is still strong enough for the
membership route provided such skips occur at cofinally many rows, because a
skipped rank above `s/2` then tends to infinity with `s`.

One half is exact for the `rowPulse` mechanism used here:

* `mem_cofRanks_iff_half_rowPulse_pos` — for `s ≥ 5`, `cofRanks s` **is** the
  set of ranks `2 ≤ d < s` above `s/2` carrying a positive row pulse.  This
  particular pulse certificate cannot be enlarged within that zone.
* `cofactor_ge_five_not_half` — for `s ≥ 4`, no divisor of `2s+1` or `2s+2`
  with cofactor `≥ 5` reaches `s/2`.  Thus cofactors `5, 7, …` are neither
  late nor half-late.
* `cofactorThree_of_late_of_rowPulse_pos` — among ranks `2 ≤ d < s` carrying
  positive row pulse in the two-thirds zone, only cofactor `3` survives.

## PROVED: unconditional results

* `cofRanks_subset_or_largestSkipHalfAt` — **the dichotomy.**  For every
  `s ≥ 61`, either the cofactor ranks at that row are all selected, or the
  row's largest false rank is above `s/2`.
* `half_mem_of_cofinal_largestSkipHalfAt` — **the positive branch.**  Half-late
  skips at *cofinally many* rows already give `1/2 ∈ mersenneAchievementSet`.
* `half_mem_or_eventually_cofRanks_subset` — either that membership holds, or
  every sufficiently large row selects all its cofactor ranks.

## Formally proved but uninstantiated consequences

* **PROVED:** `allRight_landingExcess_two_forces_halfSkip_landingRow` is
  conditional on `Recon257.seamExcess (D+1) = 2`.  **MEASURED:** this equality
  is false on every tested real row in `[5,102]`.  The theorem therefore does
  not identify a remaining obstruction for #257.
* **PROVED:** `exists_bound_allRight_landingExcess_two_impossible` is an
  existential implication whose bound exceeds every `D` admitted by its branch
  assumptions.  It excludes zero such classes.
* **PROVED:** `exists_bound_finalMiddleCell_neg_two_impossible` is a
  notation-specialized consequence in the `seamAdjacentCut` coordinates.  It
  inherits the same zero-class bound and is not a closure of the actual open
  branch.
-/

namespace Erdos249257

namespace SkipD1

open HalfCylinderIntegerGreedy
open Erdos249257.AngleB2
open Filter
open scoped BigOperators

noncomputable section

/-- **DEFINITION.** Row `s` has a largest false rank strictly beyond half the row. -/
def LargestSkipHalfAt (s : ℕ) : Prop :=
  ∃ d : ℕ, IsLargestFalseRank (seamGreedyWord s) d ∧ s < 2 * d

theorem largestSkipHalfAt_of_largestSkipLateAt {s : ℕ} (h : LargestSkipLateAt s) :
    LargestSkipHalfAt s := by
  obtain ⟨d, hmax, hmargin⟩ := h
  exact ⟨d, hmax, by omega⟩

/-- **PROVED.** At a row `s ≥ 5`, any skipped rank `m < s` above half the row
upgrades to the largest false rank. -/
theorem largestSkipHalfAt_of_skipped
    {s m : ℕ} (hs : 5 ≤ s) (hms : m < s)
    (hmnot : m ∉ seamWordSupport (seamGreedyWord s))
    (hhalf : s < 2 * m) :
    LargestSkipHalfAt s := by
  classical
  obtain ⟨D, u, hD2, hDs, _hDnot, hu, hsupp⟩ :=
    exists_maximal_missing_rank_support_decomposition s hs
  have hmD : m ≤ D := by
    by_contra hlt
    apply hmnot
    rw [hsupp]
    exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, hms⟩)
  exact ⟨D, (isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix
    (seamGreedyWord s) hD2 hDs).mpr ⟨u, hu, hsupp⟩, by omega⟩

/-! ## PROVED: the cofactor ranks all sit strictly above half the row -/

/-- **PROVED.** Every cofactor rank of `AngleB2` lies in the open half zone
`(s/2, s)`. -/
theorem cofRanks_half {s d : ℕ} (hd : d ∈ cofRanks s) :
    s < 2 * d := by
  unfold cofRanks at hd
  split_ifs at hd with h1 h2 h3 h4 h5 <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] at hd <;>
    omega

/-- **PROVED.** For `s ≥ 3`, the cofactor rank `(s+1)/2` is never in the
two-thirds late zone.  This is why the dichotomy has to be stated at the half
threshold. -/
theorem halfCofRank_not_late {s : ℕ} (hs : 3 ≤ s) : ¬ (2 * s < 3 * ((s + 1) / 2)) := by
  omega

/-- **PROVED.** The cofactor ranks in equation form: cofactor `3` of `2s+1`, cofactor `3`
of `2s+2`, cofactor `4` of `2s+2`. -/
theorem cofRanks_eq {s d : ℕ} (hd : d ∈ cofRanks s) :
    3 * d = 2 * s + 1 ∨ 3 * d = 2 * s + 2 ∨ 4 * d = 2 * s + 2 := by
  unfold cofRanks at hd
  split_ifs at hd with h1 h2 h3 h4 h5 <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] at hd <;>
    omega

theorem rowPulse_pos_of_cofactorEq {s d : ℕ}
    (h : 3 * d = 2 * s + 1 ∨ 3 * d = 2 * s + 2 ∨ 4 * d = 2 * s + 2) :
    0 < rowPulse s d := by
  rcases h with h | h | h
  · have hdvd : d ∣ 2 * s + 1 := ⟨3, by omega⟩
    simp only [rowPulse, if_pos hdvd]
    split_ifs <;> omega
  · have hdvd : d ∣ 2 * s + 2 := ⟨3, by omega⟩
    simp only [rowPulse, if_pos hdvd]
    split_ifs <;> omega
  · have hdvd : d ∣ 2 * s + 2 := ⟨4, by omega⟩
    simp only [rowPulse, if_pos hdvd]
    split_ifs <;> omega

/-! ### PROVED: the half zone contains no other pulse-carrying rank -/

/-- **PROVED.** Every rank `2 ≤ d < s` strictly above half the row that carries
positive row pulse has cofactor `3` or `4`.  There is nothing else to certify
there by this criterion. -/
theorem cofactorEq_of_half_of_rowPulse_pos {s d : ℕ}
    (hd2 : 2 ≤ d) (hds : d < s) (hhalf : s < 2 * d) (hpulse : 0 < rowPulse s d) :
    3 * d = 2 * s + 1 ∨ 3 * d = 2 * s + 2 ∨ 4 * d = 2 * s + 2 := by
  have hdvd : d ∣ 2 * s + 2 ∨ d ∣ 2 * s + 1 := by
    by_contra hcon
    push Not at hcon
    simp only [rowPulse, if_neg hcon.1, if_neg hcon.2] at hpulse
    omega
  rcases hdvd with ⟨c, hc⟩ | ⟨c, hc⟩
  · have hlow : d * 2 < d * c := by
      calc d * 2 = 2 * d := by ring
        _ < 2 * s + 2 := by omega
        _ = d * c := hc
    have hhigh : d * c < d * 5 := by
      calc d * c = 2 * s + 2 := hc.symm
        _ < 4 * d + 2 := by omega
        _ ≤ d * 5 := by omega
    have hc3 : 2 < c := Nat.lt_of_mul_lt_mul_left hlow
    have hc5 : c < 5 := Nat.lt_of_mul_lt_mul_left hhigh
    have hcval : c = 3 ∨ c = 4 := by omega
    rcases hcval with rfl | rfl
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))
  · have hlow : d * 2 < d * c := by
      calc d * 2 = 2 * d := by ring
        _ < 2 * s + 1 := by omega
        _ = d * c := hc
    have hhigh : d * c < d * 5 := by
      calc d * c = 2 * s + 1 := hc.symm
        _ < 4 * d + 1 := by omega
        _ ≤ d * 5 := by omega
    have hc3 : 2 < c := Nat.lt_of_mul_lt_mul_left hlow
    have hc5 : c < 5 := Nat.lt_of_mul_lt_mul_left hhigh
    have hcval : c = 3 ∨ c = 4 := by omega
    rcases hcval with rfl | rfl
    · exact Or.inl (by omega)
    · exact absurd hc (by omega)

/-- **PROVED.** For `s ≥ 5`, `cofRanks s` is exactly the positive-`rowPulse`
part of the half zone `2 ≤ d < s`.  Thus no further rank in this zone can be
adjoined by the same positive-pulse criterion. -/
theorem mem_cofRanks_iff_half_rowPulse_pos {s d : ℕ} (hs : 5 ≤ s) :
    d ∈ cofRanks s ↔ (2 ≤ d ∧ d < s ∧ s < 2 * d ∧ 0 < rowPulse s d) := by
  constructor
  · intro hd
    have heq := cofRanks_eq hd
    exact ⟨by omega, by omega, by omega, rowPulse_pos_of_cofactorEq heq⟩
  · rintro ⟨hd2, hds, hhalf, hpulse⟩
    have heq := cofactorEq_of_half_of_rowPulse_pos hd2 hds hhalf hpulse
    unfold cofRanks
    split_ifs with h1 h2 h3 h4 h5 <;>
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] <;>
      omega

/-- **PROVED.** For `s ≥ 4`, no rank arising with cofactor `≥ 5` from `2s+1`
or `2s+2` reaches half the row.  Hence the two-thirds late zone contains none:
cofactors `5` and `7` cannot enlarge the certified pulse floor. -/
theorem cofactor_ge_five_not_half {s d c : ℕ} (hs : 4 ≤ s) (hc : 5 ≤ c)
    (h : c * d = 2 * s + 1 ∨ c * d = 2 * s + 2) : 2 * d ≤ s := by
  have h5 : 5 * d ≤ c * d := Nat.mul_le_mul_right d hc
  omega

/-- **PROVED.** Among ranks `2 ≤ d < s` carrying positive row pulse in the
two-thirds late zone, only cofactor `3` survives.  In particular the
cofactor-`4` rank `(s+1)/2` drops out, which is why the dichotomy cannot be
stated at the two-thirds threshold. -/
theorem cofactorThree_of_late_of_rowPulse_pos {s d : ℕ}
    (hd2 : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d) (hpulse : 0 < rowPulse s d) :
    3 * d = 2 * s + 1 ∨ 3 * d = 2 * s + 2 := by
  rcases cofactorEq_of_half_of_rowPulse_pos hd2 hds (by omega) hpulse with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · omega

/-! ## PROVED: the rowwise skip dichotomy -/

/-- **PROVED.** At every row `s ≥ 61`, either every cofactor rank present in
`cofRanks s` is selected by the concrete integer seam greedy, or the row's
largest false rank lies strictly beyond half the row.  This is a rowwise
disjunction; it does not by itself establish the three-row `hcof` assumption
for any class. -/
theorem cofRanks_subset_or_largestSkipHalfAt (s : ℕ) (hs : 61 ≤ s) :
    cofRanks s ⊆ seamWordSupport (seamGreedyWord s) ∨ LargestSkipHalfAt s := by
  classical
  by_cases hhalf : LargestSkipHalfAt s
  · exact Or.inr hhalf
  · refine Or.inl fun m hm => ?_
    by_contra hmnot
    exact hhalf (largestSkipHalfAt_of_skipped (by omega)
      (cofRanks_lt s (by omega) hm) hmnot (cofRanks_half hm))

/-! ## PROVED: cofinally many half-late rows imply membership -/

/-- **PROVED.** A half-late largest skip on a cofinal set of rows supplies skipped seam
ranks tending to infinity, in exactly the format consumed by the compactness
theorem.  Note that no step socket and no lateness at *every* row is needed:
cofinality suffices, because a skipped rank above `s / 2` grows with `s`. -/
theorem seamGreedyUnboundedSkippedRanksAlong_of_cofinal_largestSkipHalfAt
    (h : ∀ B : ℕ, ∃ s : ℕ, B ≤ s ∧ LargestSkipHalfAt s) :
    ∃ rows : ℕ → ℕ, SeamGreedyUnboundedSkippedRanksAlong rows := by
  classical
  choose row hrow hhalf using h
  choose rank hrank hmargin using hhalf
  let skip : ∀ j : ℕ, Fin (row j - 2) := fun j =>
    ⟨rank j - 2, by
      rcases hrank j with ⟨_hd2, hds, _hdnot, _hfull⟩
      omega⟩
  refine ⟨row, skip, ?_, ?_, ?_⟩
  · exact tendsto_atTop_mono hrow tendsto_id
  · apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop (2 * B)] with j hj
    rcases hrank j with ⟨hd2, hds, _hdnot, _hfull⟩
    have hj' := hrow j
    have hm := hmargin j
    have hrankEq : (skip j : ℕ) + 2 = rank j := by
      dsimp [skip]
      omega
    rw [hrankEq]
    omega
  · intro j
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    rcases hrank j with ⟨hd2, hds, hdnot, _hfull⟩
    have hrankEq : rank j = (skip j : ℕ) + 2 := by
      dsimp [skip]
      omega
    exact hdnot (mem_seamWordSupport_iff.mpr ⟨skip j, htrue, hrankEq⟩)

/-- **PROVED.** Cofinally many half-late largest skips give
`1/2 ∈ mersenneAchievementSet`. -/
theorem half_mem_of_cofinal_largestSkipHalfAt
    (h : ∀ B : ℕ, ∃ s : ℕ, B ≤ s ∧ LargestSkipHalfAt s) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  obtain ⟨rows, hrows⟩ :=
    seamGreedyUnboundedSkippedRanksAlong_of_cofinal_largestSkipHalfAt h
  exact half_mem_mersenneAchievementSet_of_unboundedSkippedRanks rows hrows

/-! ## PROVED: the global disjunction -/

/-- **PROVED.** Either `1/2` is in the Mersenne
achievement set, or `AngleB2`'s residual hypothesis `hcof` holds at every
sufficiently large row.  This statement does not supply a threshold that is
applicable to a class satisfying the later all-right and landing assumptions. -/
theorem half_mem_or_eventually_cofRanks_subset :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S : ℕ, ∀ s : ℕ, S ≤ s →
        cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := by
  by_cases h : ∀ B : ℕ, ∃ s : ℕ, B ≤ s ∧ LargestSkipHalfAt s
  · exact Or.inl (half_mem_of_cofinal_largestSkipHalfAt h)
  · push Not at h
    obtain ⟨B, hB⟩ := h
    refine Or.inr ⟨max B 61, fun s hs => ?_⟩
    rcases cofRanks_subset_or_largestSkipHalfAt s
        (le_trans (le_max_right B 61) hs) with h1 | h2
    · exact h1
    · exact absurd h2 (hB s (le_trans (le_max_left B 61) hs))

/-! ## Conditional consequences under a measured-false landing antecedent

Every theorem below that takes
`Recon257.seamExcess (D + 1) = 2` inherits the following limitation:
**MEASURED:** direct evaluation gives the negation of this equality at every
tested real row with `5 ≤ D + 1 ≤ 102`.  Accordingly these are formally checked
implications, not exclusions of an exhibited class and not progress on the
open #257 statement.
-/

/-- **PROVED:** Given the exact all-right and `seamExcess (D+1) = 2`
assumptions in the statement, the concrete seam greedy must skip a rank
strictly above half the row somewhere in the three-row landing window.
**MEASURED:** the landing equality is false throughout the tested range. -/
theorem allRight_landingExcess_two_forces_halfSkip
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∃ s : ℕ, D + 1 ≤ s ∧ s < D + 4 ∧ LargestSkipHalfAt s := by
  by_contra hcon
  push Not at hcon
  refine allRight_landingExcess_two_impossible D hD hright hlanding
    (fun s hs1 hs2 => ?_)
  rcases cofRanks_subset_or_largestSkipHalfAt s (by omega) with h1 | h2
  · exact h1
  · exact absurd h2 (hcon s hs1 hs2)

/-- **PROVED:** Under the assumptions shown, the all-right tail freezes the
largest false rank, so the conditional half-late skip can be pinned to the
landing row `D+1`.  **MEASURED:** the landing equality is false throughout the
tested range, so this is not an actual remaining obstruction for #257. -/
theorem allRight_landingExcess_two_forces_halfSkip_landingRow
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    LargestSkipHalfAt (D + 1) := by
  classical
  obtain ⟨s, hs1, hs2, hhalf⟩ :=
    allRight_landingExcess_two_forces_halfSkip D hD hright hlanding
  obtain ⟨d, hmax, hmargin⟩ := hhalf
  obtain ⟨hd2, hds, hdnot, _hfull⟩ := hmax
  have hsupp := seamWordSupport_add_eq_of_eventually_right (D + 1)
    (by omega) hright (s - (D + 1))
  rw [show D + 1 + (s - (D + 1)) = s by omega] at hsupp
  have hdS : d < D + 1 := by
    by_contra hcon
    refine hdnot ?_
    rw [hsupp]
    exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, hds⟩)
  refine largestSkipHalfAt_of_skipped (by omega) hdS ?_ (by omega)
  intro hmem
  refine hdnot ?_
  rw [hsupp]
  exact Finset.mem_union_left _ hmem

/-- **PROVED:** This is a zero-class existential implication.
`SkipD1.probe_certificationThreshold_gt_landing` proves that, whenever the
all-right and landing assumptions hold, any eventual-`hcof` threshold `S`
satisfies `D + 1 < S`; `SkipD1.probe_bound_never_reaches_live_class` states
that no such threshold can satisfy `S ≤ D`.  Hence the existential bound
exceeds every admitted `D`.  In the other disjunct, the `hright` assumption is
`SeamGreedyEventuallyRight`, hence equivalent to
`1/2 ∉ mersenneAchievementSet`, while that disjunct assumes membership. -/
theorem exists_bound_allRight_landingExcess_two_impossible :
    ∃ S : ℕ, 60 ≤ S ∧ ∀ D : ℕ, S ≤ D →
      (∀ s : ℕ, D + 1 ≤ s →
        seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) →
      Recon257.seamExcess (D + 1) = 2 → False := by
  rcases half_mem_or_eventually_cofRanks_subset with hmem | ⟨S, hS⟩
  · refine ⟨60, le_rfl, fun D hD hright _hlanding => ?_⟩
    exact (seamGreedyEventuallyRight_iff_half_not_mem.mp
      ⟨D + 1, by omega, hright⟩) hmem
  · refine ⟨max S 60, le_max_right S 60, fun D hD hright hlanding => ?_⟩
    have hDS : S ≤ D := le_trans (le_max_left S 60) hD
    have hD60 : 60 ≤ D := le_trans (le_max_right S 60) hD
    exact allRight_landingExcess_two_impossible D hD60 hright hlanding
      (fun s hs1 _ => hS s (by omega))

/-- **PROVED:** This zero-class consequence expresses the preceding
existential implication in the `seamAdjacentCut` notation used by
`HalfFinalMiddlePhaseSieve`.  It inherits the same bound, which exceeds every
admitted `D`; changing notation does not turn it into a closure theorem for
#257. -/
theorem exists_bound_finalMiddleCell_neg_two_impossible :
    ∃ S : ℕ, ∀ D : ℕ, ∀ hD : 60 ≤ D, S ≤ D →
      ¬ (seamAdjacentCut D (by omega : 5 ≤ D)).successorCarries →
      (4 * (seamAdjacentCut D (by omega : 5 ≤ D)).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse <
          (seamAdjacentCut D (by omega : 5 ≤ D)).terminalWeight) →
      (∀ s : ℕ, D + 1 ≤ s →
        seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) →
      (4 * ((seamAdjacentCut D (by omega : 5 ≤ D)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse : ℤ) - 4 = -2) →
      False := by
  obtain ⟨S, _hS60, hS⟩ := exists_bound_allRight_landingExcess_two_impossible
  refine ⟨S, fun D hD hDS hncarry hmiddle hright hcell => ?_⟩
  exact hS D hDS hright
    (Recon257.seamExcess_landing_eq_two D (by omega) hncarry hmiddle hcell)

end

end SkipD1

end Erdos249257
