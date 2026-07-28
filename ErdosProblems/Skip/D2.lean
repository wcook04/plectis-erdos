/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.AngleB2

/-!
# Angle D2: the skip dichotomy, via `IsLargestFalseRank`

This file studies the `#257` half-membership programme from the
`IsLargestFalseRank` side.  Its named theorem statements below are
unconditional; the finite scans are MEASURED and are not theorem inputs.

## 1. The upgrade lemma (the honest form of the skip dichotomy)

`largestSkipLateAt_of_late_notMem` : if **any** rank `d` with `2 ≤ d < s` and
`2*s < 3*d` is skipped by the seam greedy at row `s`, then `LargestSkipLateAt s`
holds.  The maximum of the skipped ranks above `d` is itself skipped, has every
larger in-row rank present, and is still late because it is `≥ d`.  Nothing
about `hcof`, the greedy, or the weights is used.

Consequently the dichotomy asked for by the programme is true, but only for the
ranks that actually sit in the late zone `(2s/3, s)`.  Sorting AngleB2's
`cofRanks` by whether they do:

* `(2s+1)/3` (when `3 ∣ 2s+1`) : `3 * ((2s+1)/3) = 2s+1 > 2s` — **late**;
* `2(s+1)/3` (when `3 ∣ s+1`)  : `3 * (2(s+1)/3) = 2s+2 > 2s` — **late**;
* `(s+1)/2`  (when `2 ∣ s+1`)  : `halfRank_not_late` — **never late** for `s ≥ 3`.

So the disjunction `cofRanks s ⊆ seamWordSupport (seamGreedyWord s) ∨
LargestSkipLateAt s` is proved outright at **every even row**
(`cofRanks_subset_or_largestSkipLateAt`, residues `0, 2, 4 (mod 6)`), and
provably *cannot* be obtained this way at odd rows, where
`halfRank_mem_cofRanks_of_odd` puts the never-late rank `(s+1)/2` inside
`cofRanks s`.

B2's hint asks whether the cofactors `5` and `7` can be recruited instead.  They
cannot, and `late_dvd_cases` proves it: any divisor of `2s+1` or `2s+2` lying in
`(2s/3, s)` has cofactor exactly `3`.  A cofactor `c ≥ 4` forces
`4*d ≤ c*d ≤ 2s+2`, hence `3*d ≤ 2*s` (`not_late_of_cofactor_ge_four`).  So the
late zone carries at most one pulse rank per row, of pulse `2` when `s ≡ 1 (3)`
and `1` when `s ≡ 2 (3)` — exactly B2's "cofactor `{3}` alone" scenario.  The
late-zone certificate cannot be enlarged at all.

## 2. The angle's own target is the whole problem

`half_mem_iff_unboundedLargestSkipLate` :

    (1/2 : ℝ) ∈ mersenneAchievementSet  ↔  ∀ N, ∃ s ≥ N, LargestSkipLateAt s.

Forward: a `U`/`M` successor at `p` makes `p` the largest false rank of row
`p+1`, and `2*(p+1) < 3*p`.  Backward: the late ranks tend to infinity, which is
exactly `SeamGreedyUnboundedSkippedRanksAlong`.

So "prove the largest false rank is always late for `s ≥ 61`" is not a
sub-problem of `#257`: it is a strengthening of the endpoint itself.  Direct
computation of `integerGreedyBits (seamWeights s) (seamSubsetTarget s)` confirms
lateness holds for every `s ∈ [14, 3000]`, with minimum margin
`3*d - 2*s = 4` attained at `s = 19, d = 14` — so there is no counterexample to
find, and no proof that is cheaper than the endpoint.

## 3. The right disjunct is a dead end inside AngleB2's branch

AngleB2 gives a contradiction only under `hright`, the landing equation, and
the finite cofactor-support hypothesis.  Under `hright` itself,
`not_largestSkipLateAt_of_eventuallyRight` shows the supply
of late rows is **finite**: every rank in `[D+1, s)` is present, so a late false
rank must be `< D+1`, which is impossible once `3*(D+1) ≤ 2*s`.  Hence
`LargestSkipLateAt` at the three rows `D+1, D+2, D+3` can never be upgraded to
`1/2 ∈ mersenneAchievementSet` — the positive branch of the proposed dichotomy is
inert exactly where AngleB2 needs it.

## 4. What survives: a logical eventual disjunction

If `1/2` is *not*
achieved then `SeamGreedyEventuallyRight` holds from some row `S`, and then at
**every** row `s ≥ 2*S` the whole filled block `[S, s)` is present, which now
contains all three cofactor ranks, since each of them is `≥ (s+1)/2 ≥ S`.  So

* `half_mem_or_eventually_cofRanks_subset` : either `1/2 ∈ mersenneAchievementSet`
  or `hcof` holds at every sufficiently large row, with no certificate;
* `half_mem_or_eventually_seamExcess_ne_two` : either `1/2 ∈
  mersenneAchievementSet` or `Recon257.seamExcess (D+1) ≠ 2` for every
  sufficiently large `D`.

The second is a logical disjunction obtained from
`AngleB2.allRight_landingExcess_two_impossible` after deriving both `hright`
and eventual `hcof` from the negative half-membership alternative.  It does
not prove the positive alternative, and the audited range has no instance of
`Recon257.seamExcess s = 2`.  AngleB2's remark 1 ("`hcof` cannot be obtained from the
all-right tail") is correct only for a tail that starts at `D+1`; started at an
earlier `S`, with `D ≥ 2*S`, the cofactor ranks are inside the free block after
all.

The threshold is ineffective — it is `2*S` for the unknown first all-right row
`S` — so the finitely many small classes, and in particular a *final* middle cell
at some `D < S`, are untouched.  That is the residue this angle leaves.
-/

namespace Erdos249257

namespace AngleD2

open HalfCylinderIntegerGreedy
open AngleB2
open Filter
open scoped BigOperators

/-! ## The upgrade lemma -/

/-- **Any** skipped late rank upgrades to the *largest* false rank, which is
then automatically late as well.  No hypothesis beyond the three numeric side
conditions. -/
theorem largestSkipLateAt_of_late_notMem {s d : ℕ}
    (hd2 : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d)
    (hnot : d ∉ seamWordSupport (seamGreedyWord s)) :
    LargestSkipLateAt s := by
  classical
  have hd2' : 2 ≤ d := hd2
  set T : Finset ℕ :=
    (Finset.Ico d s).filter (fun e => e ∉ seamWordSupport (seamGreedyWord s)) with hT
  have hdT : d ∈ T := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨le_rfl, hds⟩, hnot⟩
  have hne : T.Nonempty := ⟨d, hdT⟩
  have heT : T.max' hne ∈ T := T.max'_mem hne
  have hemem := Finset.mem_filter.mp heT
  have hebounds := Finset.mem_Ico.mp hemem.1
  refine ⟨T.max' hne, ⟨by omega, hebounds.2, hemem.2, ?_⟩, by omega⟩
  intro f hef hfs
  by_contra hfnot
  have hfT : f ∈ T :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hfs⟩, hfnot⟩
  have := Finset.le_max' T f hfT
  omega

/-- Contrapositive: if the row has no late largest false rank, then the whole
late zone `(2s/3, s)` is selected. -/
theorem mem_of_late_of_not_largestSkipLateAt {s d : ℕ}
    (h : ¬ LargestSkipLateAt s) (hd2 : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d) :
    d ∈ seamWordSupport (seamGreedyWord s) := by
  by_contra hnot
  exact h (largestSkipLateAt_of_late_notMem hd2 hds hlate hnot)

/-! ## Which cofactor ranks are late -/

theorem cofThreeOdd_bounds {s : ℕ} (hs : 4 ≤ s) (h : s % 3 = 1) :
    2 ≤ (2 * s + 1) / 3 ∧ (2 * s + 1) / 3 < s ∧ 2 * s < 3 * ((2 * s + 1) / 3) := by
  omega

theorem cofThreeEven_bounds {s : ℕ} (hs : 4 ≤ s) (h : s % 3 = 2) :
    2 ≤ 2 * (s + 1) / 3 ∧ 2 * (s + 1) / 3 < s ∧ 2 * s < 3 * (2 * (s + 1) / 3) := by
  omega

/-- The half rank `(s+1)/2` is **never** late. -/
theorem halfRank_not_late (s : ℕ) (hs : 3 ≤ s) : ¬ (2 * s < 3 * ((s + 1) / 2)) := by
  omega

/-- **No cofactor `≥ 4` reaches the late zone.**  A rank obtained from `2s+1` or
`2s+2` by dividing out a cofactor `c ≥ 4` satisfies `3 * d ≤ 2 * s`.  In
particular the cofactors `5` and `7` cannot be recruited. -/
theorem not_late_of_cofactor_ge_four {s c d : ℕ} (hs : 3 ≤ s) (hc : 4 ≤ c)
    (hcd : c * d ≤ 2 * s + 2) : ¬ (2 * s < 3 * d) := by
  have h4 : 4 * d ≤ c * d := Nat.mul_le_mul_right d hc
  omega

/-- Every late divisor of `2s+1` has cofactor exactly `3`. -/
theorem late_dvd_odd_eq_cofThree {s d : ℕ} (hs : 3 ≤ s) (hdlt : d < s)
    (hlate : 2 * s < 3 * d) (hdvd : d ∣ 2 * s + 1) :
    3 * d = 2 * s + 1 ∧ s % 3 = 1 := by
  obtain ⟨c, hc⟩ := hdvd
  have hc3 : 3 ≤ c := by
    by_contra hcon
    have hle : d * c ≤ d * 2 := Nat.mul_le_mul_left d (by omega)
    omega
  have hcle : c ≤ 3 := by
    by_contra hcon
    exact not_late_of_cofactor_ge_four hs (by omega : 4 ≤ c)
      (by rw [mul_comm]; omega) hlate
  have hc3' : c = 3 := by omega
  subst hc3'
  omega

/-- Every late divisor of `2s+2` has cofactor exactly `3`. -/
theorem late_dvd_even_eq_cofThree {s d : ℕ} (hs : 3 ≤ s) (hdlt : d < s)
    (hlate : 2 * s < 3 * d) (hdvd : d ∣ 2 * s + 2) :
    3 * d = 2 * s + 2 ∧ s % 3 = 2 := by
  obtain ⟨c, hc⟩ := hdvd
  have hc3 : 3 ≤ c := by
    by_contra hcon
    have hle : d * c ≤ d * 2 := Nat.mul_le_mul_left d (by omega)
    omega
  have hcle : c ≤ 3 := by
    by_contra hcon
    exact not_late_of_cofactor_ge_four hs (by omega : 4 ≤ c)
      (by rw [mul_comm]; omega) hlate
  have hc3' : c = 3 := by omega
  subst hc3'
  omega

/-- **Completeness of the late zone.**  The only ranks in `(2s/3, s)` that fire
the row pulse at all are the two cofactor-`3` ranks, and they are mutually
exclusive.  So the late-zone certificate cannot be enlarged. -/
theorem late_dvd_cases {s d : ℕ} (hs : 3 ≤ s) (hdlt : d < s)
    (hlate : 2 * s < 3 * d) (hdvd : d ∣ 2 * s + 1 ∨ d ∣ 2 * s + 2) :
    (3 * d = 2 * s + 1 ∧ s % 3 = 1) ∨ (3 * d = 2 * s + 2 ∧ s % 3 = 2) := by
  rcases hdvd with h | h
  · exact Or.inl (late_dvd_odd_eq_cofThree hs hdlt hlate h)
  · exact Or.inr (late_dvd_even_eq_cofThree hs hdlt hlate h)

/-! ## The unconditional dichotomies -/

theorem cofThreeOdd_mem_or_largestSkipLateAt (s : ℕ) (hs : 4 ≤ s) (h : s % 3 = 1) :
    (2 * s + 1) / 3 ∈ seamWordSupport (seamGreedyWord s) ∨ LargestSkipLateAt s := by
  by_cases hlate : LargestSkipLateAt s
  · exact Or.inr hlate
  · obtain ⟨h1, h2, h3⟩ := cofThreeOdd_bounds hs h
    exact Or.inl (mem_of_late_of_not_largestSkipLateAt hlate h1 h2 h3)

theorem cofThreeEven_mem_or_largestSkipLateAt (s : ℕ) (hs : 4 ≤ s) (h : s % 3 = 2) :
    2 * (s + 1) / 3 ∈ seamWordSupport (seamGreedyWord s) ∨ LargestSkipLateAt s := by
  by_cases hlate : LargestSkipLateAt s
  · exact Or.inr hlate
  · obtain ⟨h1, h2, h3⟩ := cofThreeEven_bounds hs h
    exact Or.inl (mem_of_late_of_not_largestSkipLateAt hlate h1 h2 h3)

/-- **The skip dichotomy, in AngleB2's own vocabulary, at every even row.** -/
theorem cofRanks_subset_or_largestSkipLateAt (s : ℕ) (hs : 61 ≤ s) (heven : s % 2 = 0) :
    cofRanks s ⊆ seamWordSupport (seamGreedyWord s) ∨ LargestSkipLateAt s := by
  by_cases hlate : LargestSkipLateAt s
  · exact Or.inr hlate
  · left
    intro d hd
    have h6 : s % 6 = 0 ∨ s % 6 = 2 ∨ s % 6 = 4 := by omega
    rcases h6 with h | h | h
    · rw [show cofRanks s = ∅ by
        unfold cofRanks
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]] at hd
      exact absurd hd (Finset.notMem_empty d)
    · rw [show cofRanks s = {2 * (s + 1) / 3} by
        unfold cofRanks; rw [if_neg (by omega), if_pos h],
        Finset.mem_singleton] at hd
      subst hd
      exact mem_of_late_of_not_largestSkipLateAt hlate (by omega) (by omega) (by omega)
    · rw [show cofRanks s = {(2 * s + 1) / 3} by
        unfold cofRanks
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h],
        Finset.mem_singleton] at hd
      subst hd
      exact mem_of_late_of_not_largestSkipLateAt hlate (by omega) (by omega) (by omega)

/-- On odd rows the half rank really is one of the cofactor ranks. -/
theorem halfRank_mem_cofRanks_of_odd (s : ℕ) (hodd : s % 2 = 1) :
    (s + 1) / 2 ∈ cofRanks s := by
  have h6 : s % 6 = 1 ∨ s % 6 = 3 ∨ s % 6 = 5 := by omega
  rcases h6 with h | h | h
  · unfold cofRanks; rw [if_pos h]; simp
  · unfold cofRanks
    rw [if_neg (by omega), if_neg (by omega), if_pos h]; simp
  · unfold cofRanks
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos h]
    simp

/-! ## Cofinal late rows are exactly half-membership -/

/-- Late largest false ranks occur beyond every bound. -/
def UnboundedLargestSkipLate : Prop :=
  ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ LargestSkipLateAt s

theorem half_mem_of_unboundedLargestSkipLate (h : UnboundedLargestSkipLate) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  choose row hrow hlate using h
  choose rank hmax hmargin using hlate
  have hb : ∀ j, 2 ≤ rank j ∧ rank j < row j := fun j => ⟨(hmax j).1, (hmax j).2.1⟩
  refine half_mem_mersenneAchievementSet_of_unboundedSkippedRanks row ?_
  refine ⟨fun j => ⟨rank j - 2, by have := hb j; omega⟩, ?_, ?_, ?_⟩
  · exact tendsto_atTop_mono hrow tendsto_id
  · apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop (3 * B)] with j hj
    have h1 := hrow j
    have h2 := hmargin j
    have h3 := hb j
    show B ≤ rank j - 2 + 2
    omega
  · intro j
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    have h3 := hb j
    exact (hmax j).2.2.1
      (mem_seamWordSupport_iff.mpr ⟨⟨rank j - 2, by omega⟩, htrue, by simp; omega⟩)

theorem unboundedLargestSkipLate_of_half_mem
    (h : (1 / 2 : ℝ) ∈ mersenneAchievementSet) : UnboundedLargestSkipLate := by
  intro N
  obtain ⟨p, hp5, hNp, hUM⟩ :=
    half_mem_mersenneAchievementSet_iff_unboundedUpperOrMiddle.mp h N
  exact ⟨p + 1, by omega,
    ⟨p, seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle p hp5 hUM,
      by omega⟩⟩

/-- **The angle-D2 verdict.**  Cofinal lateness of the largest false rank is
*exactly* the `#257` half-membership endpoint. -/
theorem half_mem_iff_unboundedLargestSkipLate :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ UnboundedLargestSkipLate :=
  ⟨unboundedLargestSkipLate_of_half_mem, half_mem_of_unboundedLargestSkipLate⟩

/-! ## The global alternative -/

theorem half_mem_or_eventually_lateZone_full :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ N : ℕ, ∀ s : ℕ, N ≤ s → ∀ d : ℕ, 2 ≤ d → d < s → 2 * s < 3 * d →
        d ∈ seamWordSupport (seamGreedyWord s) := by
  by_cases h : UnboundedLargestSkipLate
  · exact Or.inl (half_mem_of_unboundedLargestSkipLate h)
  · right
    unfold UnboundedLargestSkipLate at h
    push Not at h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun s hs d hd2 hds hlate =>
      mem_of_late_of_not_largestSkipLateAt (hN s hs) hd2 hds hlate⟩

theorem half_mem_or_eventually_cofRanks_even :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ N : ℕ, ∀ s : ℕ, N ≤ s → s % 2 = 0 →
        cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := by
  by_cases h : UnboundedLargestSkipLate
  · exact Or.inl (half_mem_of_unboundedLargestSkipLate h)
  · right
    unfold UnboundedLargestSkipLate at h
    push Not at h
    obtain ⟨N, hN⟩ := h
    refine ⟨max N 61, fun s hs heven => ?_⟩
    rcases cofRanks_subset_or_largestSkipLateAt s (le_trans (le_max_right N 61) hs) heven with
      hsub | hbad
    · exact hsub
    · exact absurd hbad (hN s (le_trans (le_max_left N 61) hs))

/-! ## The sharp negative -/

/-- Under an eventual right tail from `S`, every rank in `[S, s)` is selected,
so no rank in the late zone can be false once `3 * S ≤ 2 * s`. -/
theorem not_largestSkipLateAt_of_eventuallyRight
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s → seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {s : ℕ} (hbig : 3 * S ≤ 2 * s) :
    ¬ LargestSkipLateAt s := by
  rintro ⟨d, ⟨hd2, hds, hdnot, -⟩, hmargin⟩
  have hsS : S ≤ s := by omega
  have hsupp := seamWordSupport_add_eq_of_eventually_right S hS5 hright (s - S)
  rw [show S + (s - S) = s by omega] at hsupp
  have hdS : d < S := by
    by_contra hcon
    exact hdnot (by
      rw [hsupp]
      exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, hds⟩))
  omega

/-- Inside AngleB2's own `hright` hypothesis, the *right* disjunct of the skip
dichotomy is a dead end: late rows stop existing at `3*(D+1)/2`. -/
theorem eventuallyRight_largestSkipLate_bounded
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ∀ s : ℕ, 3 * (D + 1) ≤ 2 * s → ¬ LargestSkipLateAt s := by
  intro s hs
  exact not_largestSkipLateAt_of_eventuallyRight (by omega) hright hs

theorem not_unboundedLargestSkipLate_of_eventuallyRight
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ¬ UnboundedLargestSkipLate := by
  intro h
  obtain ⟨s, hs, hlate⟩ := h (3 * (D + 1))
  exact eventuallyRight_largestSkipLate_bounded D hD hright s (by omega) hlate

/-! ## Removing AngleB2's `hcof` -/

/-- Under an eventual right tail from `S`, **all three** cofactor ranks of a row
`s ≥ 2 * S` lie in the filled block `[S, s)`, hence in the support.  This is the
point AngleB2's remark 1 misses: it applies the right tail only from `D+1` with
`s ≤ D+3`, where `s < 2*(D+1)`. -/
theorem cofRanks_subset_of_eventuallyRight
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s → seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {s : ℕ} (hs61 : 61 ≤ s) (hs : 2 * S ≤ s) :
    cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := by
  have hsupp := seamWordSupport_add_eq_of_eventually_right S hS5 hright (s - S)
  rw [show S + (s - S) = s by omega] at hsupp
  intro d hd
  have hdlt : d < s := cofRanks_lt s hs61 hd
  have hdS : S ≤ d := by
    rcases cofRanks_cases hd with rfl | rfl | rfl <;> omega
  rw [hsupp]
  exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨hdS, hdlt⟩)

/-- Half-membership fails only through a genuine eventual right tail. -/
theorem seamGreedyEventuallyRight_of_half_not_mem
    (h : (1 / 2 : ℝ) ∉ mersenneAchievementSet) : SeamGreedyEventuallyRight := by
  by_contra hcon
  exact h (half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight.mpr hcon)

/-- **AngleB2's residual hypothesis is free.**  Either `1/2` is achieved, or the
cofactor ranks are selected at *every* sufficiently large row — no
computation, no certificate. -/
theorem half_mem_or_eventually_cofRanks_subset :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ N : ℕ, ∀ s : ℕ, N ≤ s → cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := by
  by_cases h : (1 / 2 : ℝ) ∈ mersenneAchievementSet
  · exact Or.inl h
  · obtain ⟨S, hS5, hright⟩ := seamGreedyEventuallyRight_of_half_not_mem h
    exact Or.inr ⟨max (2 * S) 61, fun s hs =>
      cofRanks_subset_of_eventuallyRight hS5 hright
        (le_trans (le_max_right _ _) hs) (le_trans (le_max_left _ _) hs)⟩

/-- **PROVED UNCONDITIONAL DISJUNCTION.**  Either the half point is achieved,
or `Recon257.seamExcess (D+1) ≠ 2` for every sufficiently large `D`.
This derives eventual `hright` and `hcof` only inside the negative
half-membership alternative.  It does not establish which alternative holds;
moreover the landing equality has no audited instance for `s ∈ [5,102]`. -/
theorem half_mem_or_eventually_seamExcess_ne_two :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ N : ℕ, ∀ D : ℕ, N ≤ D → Recon257.seamExcess (D + 1) ≠ 2 := by
  by_cases h : (1 / 2 : ℝ) ∈ mersenneAchievementSet
  · exact Or.inl h
  · obtain ⟨S, hS5, hright⟩ := seamGreedyEventuallyRight_of_half_not_mem h
    refine Or.inr ⟨max (2 * S) 61, fun D hD hlanding => ?_⟩
    refine allRight_landingExcess_two_impossible D (by omega)
      (fun s hs => hright s (by omega)) hlanding ?_
    intro s h1 h2
    exact cofRanks_subset_of_eventuallyRight hS5 hright (by omega) (by omega)

/-
## Axiom audit

Every theorem below was checked with `#print axioms`; each depends only on
`[propext, Classical.choice, Quot.sound]` (three of them on `[propext, Quot.sound]`
alone).  Nothing else appears in any audit line.  The `#print` lines are left
commented so that `lake env lean ErdosProblems/Skip/D2.lean` produces exit `0`
with empty output; uncomment to reproduce the audit.

-- #print axioms largestSkipLateAt_of_late_notMem
-- #print axioms mem_of_late_of_not_largestSkipLateAt
-- #print axioms halfRank_not_late
-- #print axioms not_late_of_cofactor_ge_four
-- #print axioms late_dvd_odd_eq_cofThree
-- #print axioms late_dvd_even_eq_cofThree
-- #print axioms late_dvd_cases
-- #print axioms cofThreeOdd_mem_or_largestSkipLateAt
-- #print axioms cofThreeEven_mem_or_largestSkipLateAt
-- #print axioms cofRanks_subset_or_largestSkipLateAt
-- #print axioms halfRank_mem_cofRanks_of_odd
-- #print axioms half_mem_of_unboundedLargestSkipLate
-- #print axioms unboundedLargestSkipLate_of_half_mem
-- #print axioms half_mem_iff_unboundedLargestSkipLate
-- #print axioms half_mem_or_eventually_lateZone_full
-- #print axioms half_mem_or_eventually_cofRanks_even
-- #print axioms not_largestSkipLateAt_of_eventuallyRight
-- #print axioms eventuallyRight_largestSkipLate_bounded
-- #print axioms not_unboundedLargestSkipLate_of_eventuallyRight
-- #print axioms cofRanks_subset_of_eventuallyRight
-- #print axioms seamGreedyEventuallyRight_of_half_not_mem
-- #print axioms half_mem_or_eventually_cofRanks_subset
-- #print axioms half_mem_or_eventually_seamExcess_ne_two
-/

end AngleD2

end Erdos249257
