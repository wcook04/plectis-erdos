/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Skip.D1
import Erdos249257.HalfCylinderMiddleCarryLowerBound

/-!
# Half H1: the quotient-three weight and the exact half-zone adjacent gap

`Erdos249257/HalfCylinderLargestSkipGap.lean` computes the truncated Mersenne
weight, and the exact adjacent lower-to-upper gap, in the **two-thirds zone**
`2 * s < 3 * d`, where the Euclidean quotient of `2 * s` by `d` is exactly two:

    `truncatedMersenneWeight s d = 2 ^ (2s - d) + 4 ^ (s - d)`,
    `3 * (remainder + overshoot) = 3 * 2 ^ (s+1) + 2 * 4 ^ (s-d) + 4`.

`ErdosProblems/Skip/D1.lean` shows the residue of Erdős #257 sits one notch
lower, at the **half zone**: the surviving branch is `LargestSkipHalfAt s`,
i.e. `s < 2 * d`, which is strictly wider.  Its complement inside the
two-thirds zone is

    `s < 2 * d`  and  `3 * d ≤ 2 * s`,

on which the Euclidean quotient of `2 * s` by `d` is exactly **three**.  This
file supplies what the corpus is missing there.

## What is proved

* `truncatedMersenneWeight_eq_threeTerm_of_halfRank` — the quotient-three
  weight `2 ^ (2s-d) + 4 ^ (s-d) + 2 ^ (2s-3d)`.
* `seven_mul_cubeSuffixSum_add_boundary` — the base-eight suffix telescope,
  the third column's analogue of `three_mul_fourPowerSuffixSum_add_four`.
* `seamWeightsFrom_sum_halfZone` — the strict suffix above a half-zone rank
  splits at `⌊2s/3⌋`: half-zone below, two-thirds zone above.
* `twentyOne_mul_tailWeight_add_exactHalfGap` — the division-free adjacent
  gap identity at scale `21 = 3 * 7`.
* `twentyOne_mul_remainder_add_overshoot_eq_exactHalfGap` — the same for the
  *actual* `seamAdjacentCut`, the direct analogue of
  `three_mul_remainder_add_overshoot_eq_exactLateGap`.
* `twentyOne_mul_remainder_add_overshoot_eq_skipHalfGap` — the two zones
  glued, giving an unconditional exact gap for **every** half-late largest
  false rank, and `gap_strictly_between_of_largestSkipHalf`:
  `2 ^ (s+1) < remainder + overshoot < 2 ^ (s+2)`.

## What is *not* proved, and why

Feeding in the landing constraint `seamIntegerGreedyRemainder s = 2^(s+1)+2`
collapses the identity to `21 * overshoot + 42 = skipHalfGapCorrection s d`
(`twentyOne_mul_overshoot_add_fortyTwo_eq_skipHalfGap`).  Neither of the two
routes the brief suggested closes the branch from there, and both closures
are recorded as theorems rather than left as opinion:

That landing constraint is itself **not realised in the audited concrete
greedy data**: direct evaluation finds no `s ∈ [5,64]` with
`seamIntegerGreedyRemainder s = 2^(s+1)+2`.  Thus
`twentyOne_mul_overshoot_add_fortyTwo_eq_skipHalfGap` is a valid conditional
identity with no exhibited instance; it is not evidence about a live branch.
The unconditional weight and adjacent-gap identities listed above do not use
the landing constraint and remain the content of this file.

* **Divisibility gives nothing** — `twentyOne_dvd_halfGapCorrection` shows the
  correction is a multiple of `21` for *every* half-zone rank, so the
  congruence is `0 = 0` (`landing_congruence_is_trivial`).
* **Size gives nothing** — `le_halfGapCorrection` shows the correction always
  exceeds `105`, and `halfGapCorrection_lt_twentyOne_mul_gap` shows it is
  always below `21 * 2 ^ (s+1)`; so the window
  `landing_forces_correction_window` extracts is automatically satisfied.

A machine scan of the greedy rows `5 ≤ s ≤ 300` moreover finds the largest
false rank above `s / 2` at **every** such `s`.  So `LargestSkipHalfAt` is not
refutable on its own, and the remaining contradiction, if any, has to come
from the all-right tail hypothesis interacting with the pulse, not from this
gap alone.  See the non-vacuity section at the end of the file.
-/

namespace ErdosProblems.HalfH1

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open scoped BigOperators

/-! ## The half zone -/

/-- The half zone at seam length `s`: rank `d` is above `s / 2` but not above
`2 * s / 3`.  Exactly the ranks the two-thirds identities miss. -/
def InHalfZone (s d : ℕ) : Prop := 2 ≤ d ∧ s < 2 * d ∧ 3 * d ≤ 2 * s

theorem InHalfZone.two_le {s d : ℕ} (h : InHalfZone s d) : 2 ≤ d := h.1

theorem InHalfZone.half {s d : ℕ} (h : InHalfZone s d) : s < 2 * d := h.2.1

theorem InHalfZone.third {s d : ℕ} (h : InHalfZone s d) : 3 * d ≤ 2 * s := h.2.2

theorem InHalfZone.three_le_s {s d : ℕ} (h : InHalfZone s d) : 3 ≤ s := by
  obtain ⟨hd2, _, hthird⟩ := h; omega

theorem InHalfZone.lt {s d : ℕ} (h : InHalfZone s d) : d < s := by
  obtain ⟨hd2, _, hthird⟩ := h; omega

/-- The half zone and the two-thirds zone together are the `s < 2 * d`
region: this is why they are the only two cases of `LargestSkipHalfAt`. -/
theorem inHalfZone_or_late_of_half {s d : ℕ} (hd2 : 2 ≤ d)
    (hhalf : s < 2 * d) :
    InHalfZone s d ∨ 2 * s < 3 * d := by
  by_cases h : 3 * d ≤ 2 * s
  · exact Or.inl ⟨hd2, hhalf, h⟩
  · exact Or.inr (by omega)

/-! ## The quotient-three truncated weight -/

/-- **Quotient-three weight identity.**  In the half zone `s/2 < d ≤ 2s/3`
Euclidean division of `2 * s` by `d` has quotient exactly three, so the
truncated Mersenne weight has exactly three power terms.  This is the
three-term analogue of
`truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank`. -/
theorem truncatedMersenneWeight_eq_threeTerm_of_halfRank
    {s d : ℕ} (h : InHalfZone s d) :
    truncatedMersenneWeight s d =
      2 ^ (2 * s - d) + 4 ^ (s - d) + 2 ^ (2 * s - 3 * d) := by
  obtain ⟨hd2, hhalf, hthird⟩ := h
  have hds : d < s := by omega
  rw [truncatedMersenneWeight_eq_geometricCore hd2]
  have hdiv : (2 * s) / d = 3 := by
    apply Nat.div_eq_of_lt_le <;> omega
  have hrem : (2 * s) % d = 2 * s - 3 * d := by
    conv_lhs => rw [show 2 * s = d * 3 + (2 * s - 3 * d) from by omega]
    rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hpow4 : 4 ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
  have he1 : 2 * s - 3 * d + d + d = 2 * s - d := by omega
  have he2 : 2 * s - 3 * d + d = 2 * (s - d) := by omega
  rw [hdiv, hrem]
  calc
    2 ^ (2 * s - 3 * d) * ∑ i ∈ Finset.range 3, (2 ^ d) ^ i
        = 2 ^ (2 * s - 3 * d) * 2 ^ d * 2 ^ d +
            (2 ^ (2 * s - 3 * d) * 2 ^ d + 2 ^ (2 * s - 3 * d)) := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_one]
          ring
    _ = 2 ^ (2 * s - 3 * d + d + d) +
          (2 ^ (2 * s - 3 * d + d) + 2 ^ (2 * s - 3 * d)) := by
            rw [pow_add, pow_add]
    _ = 2 ^ (2 * s - d) + (2 ^ (2 * (s - d)) + 2 ^ (2 * s - 3 * d)) := by
          rw [he1, he2]
    _ = 2 ^ (2 * s - d) + 4 ^ (s - d) + 2 ^ (2 * s - 3 * d) := by
          rw [hpow4]; ring

/-! ## The base-eight suffix telescope -/

/-- Division-free base-eight telescope: the descending cube powers over the
half-zone part of the strict suffix. -/
theorem seven_mul_cubeSuffixSum_add_boundary
    (s d T : ℕ) (hdT : d ≤ T) (hT : 3 * T ≤ 2 * s) :
    7 * (∑ e ∈ Finset.Ico (d + 1) (T + 1), 2 ^ (2 * s - 3 * e)) +
        2 ^ (2 * s - 3 * T) =
      2 ^ (2 * s - 3 * d) := by
  by_cases hstep : d < T
  · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : d + 1 < T + 1)]
    have ih :
        7 * (∑ e ∈ Finset.Ico (d + 2) (T + 1), 2 ^ (2 * s - 3 * e)) +
            2 ^ (2 * s - 3 * T) =
          2 ^ (2 * s - 3 * (d + 1)) := by
      simpa [Nat.add_assoc] using
        seven_mul_cubeSuffixSum_add_boundary s (d + 1) T (by omega) hT
    calc
      7 * (2 ^ (2 * s - 3 * (d + 1)) +
            ∑ e ∈ Finset.Ico (d + 2) (T + 1), 2 ^ (2 * s - 3 * e)) +
          2 ^ (2 * s - 3 * T)
          = 7 * 2 ^ (2 * s - 3 * (d + 1)) +
              (7 * (∑ e ∈ Finset.Ico (d + 2) (T + 1), 2 ^ (2 * s - 3 * e)) +
                2 ^ (2 * s - 3 * T)) := by ring
      _ = 7 * 2 ^ (2 * s - 3 * (d + 1)) + 2 ^ (2 * s - 3 * (d + 1)) := by
            rw [ih]
      _ = 2 ^ (2 * s - 3 * (d + 1)) * 8 := by ring
      _ = 2 ^ (2 * s - 3 * (d + 1) + 3) := by
            rw [pow_add]; norm_num
      _ = 2 ^ (2 * s - 3 * d) := by congr 1; omega
  · have hdeq : d = T := by omega
    subst hdeq
    rw [Finset.Ico_self]
    simp
termination_by T - d
decreasing_by omega

/-! ## The exact half-zone strict-suffix sum -/

/-- The strict suffix above a half-zone rank splits at `⌊2s/3⌋`: below that
cut the ranks are still half-zone (three power terms), above it they are
two-thirds-zone (two power terms).  The result is the late two-column sum
plus one extra base-eight column carried only by the half-zone part. -/
theorem seamWeightsFrom_sum_halfZone {s d : ℕ} (h : InHalfZone s d) :
    (seamWeightsFrom s (d + 1)).sum =
      ((∑ e ∈ Finset.Ico (d + 1) s, 2 ^ (2 * s - e)) +
          ∑ e ∈ Finset.Ico (d + 1) s, 4 ^ (s - e)) +
        ∑ e ∈ Finset.Ico (d + 1) ((2 * s) / 3 + 1), 2 ^ (2 * s - 3 * e) := by
  classical
  obtain ⟨hd2, hhalf, hthird⟩ := h
  set T := (2 * s) / 3 with hTdef
  have hT3 : 3 * T ≤ 2 * s := by omega
  have hTlt : 2 * s < 3 * T + 3 := by omega
  have hdT : d ≤ T := by omega
  have hTs : T + 1 ≤ s := by omega
  rw [← sum_truncatedMersenneWeight_Ico_eq_seamWeightsFrom_sum s (d + 1)
    (by omega), ← Finset.sum_add_distrib]
  have hsplit1 :
      (∑ e ∈ Finset.Ico (d + 1) (T + 1), truncatedMersenneWeight s e) +
          (∑ e ∈ Finset.Ico (T + 1) s, truncatedMersenneWeight s e) =
        ∑ e ∈ Finset.Ico (d + 1) s, truncatedMersenneWeight s e :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  have hsplit2 :
      (∑ e ∈ Finset.Ico (d + 1) (T + 1),
            (2 ^ (2 * s - e) + 4 ^ (s - e))) +
          (∑ e ∈ Finset.Ico (T + 1) s, (2 ^ (2 * s - e) + 4 ^ (s - e))) =
        ∑ e ∈ Finset.Ico (d + 1) s, (2 ^ (2 * s - e) + 4 ^ (s - e)) :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  have hlow :
      (∑ e ∈ Finset.Ico (d + 1) (T + 1), truncatedMersenneWeight s e) =
        ∑ e ∈ Finset.Ico (d + 1) (T + 1),
          ((2 ^ (2 * s - e) + 4 ^ (s - e)) + 2 ^ (2 * s - 3 * e)) := by
    refine Finset.sum_congr rfl ?_
    intro e he
    have heb := Finset.mem_Ico.mp he
    have hz : InHalfZone s e := ⟨by omega, by omega, by omega⟩
    rw [truncatedMersenneWeight_eq_threeTerm_of_halfRank hz]
  have hhigh :
      (∑ e ∈ Finset.Ico (T + 1) s, truncatedMersenneWeight s e) =
        ∑ e ∈ Finset.Ico (T + 1) s, (2 ^ (2 * s - e) + 4 ^ (s - e)) := by
    refine Finset.sum_congr rfl ?_
    intro e he
    have heb := Finset.mem_Ico.mp he
    exact truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank
      (by omega) heb.2 (by omega)
  rw [hlow, hhigh, Finset.sum_add_distrib] at hsplit1
  omega

/-! ## The exact half-zone adjacent gap -/

/-- The correction term of the exact half-zone adjacent gap: the analogue of
the late correction `2 * 4 ^ (s - d) + 4`, scaled by seven.  Dividing the
whole gap by `21` gives
`2 ^ (s+1) + (2 * 4 ^ (s-d) + 4)/3 + (6 * 2 ^ (2s-3d) + 2 ^ (2s mod 3))/7`. -/
def halfGapCorrection (s d : ℕ) : ℕ :=
  14 * 4 ^ (s - d) + 18 * 2 ^ (2 * s - 3 * d) + 3 * 2 ^ ((2 * s) % 3) + 28

/-- **Exact half-zone adjacent-gap identity**, stated without division.
This is the analogue of
`three_mul_tailWeight_add_exactLateGap_eq_three_mul_headWeight`,
with the scale `3` replaced by `21 = 3 * 7`. -/
theorem twentyOne_mul_tailWeight_add_exactHalfGap
    {s d : ℕ} (h : InHalfZone s d) :
    21 * (seamWeightsFrom s (d + 1)).sum +
        (21 * 2 ^ (s + 1) + halfGapCorrection s d) =
      21 * truncatedMersenneWeight s d := by
  obtain ⟨hd2, hhalf, hthird⟩ := h
  have h' : InHalfZone s d := ⟨hd2, hhalf, hthird⟩
  have hds : d < s := h'.lt
  have hhead := truncatedMersenneWeight_eq_threeTerm_of_halfRank h'
  have htail := seamWeightsFrom_sum_halfZone h'
  have htwo := twoPowerSuffixSum_add_boundary s d hds
  have hfour := three_mul_fourPowerSuffixSum_add_four s d hds
  have hcube := seven_mul_cubeSuffixSum_add_boundary s d ((2 * s) / 3)
    (by omega) (by omega)
  rw [show 2 * s - 3 * ((2 * s) / 3) = (2 * s) % 3 from by omega] at hcube
  unfold halfGapCorrection
  rw [hhead, htail]
  omega

/-- Numerical consistency check of the quotient-three weight identity. -/
example : truncatedMersenneWeight 11 7 = 2 ^ (2 * 11 - 7) + 4 ^ (11 - 7) +
    2 ^ (2 * 11 - 3 * 7) :=
  truncatedMersenneWeight_eq_threeTerm_of_halfRank
    (by exact ⟨by norm_num, by norm_num, by norm_num⟩)

example : truncatedMersenneWeight 11 7 = 33026 := by
  norm_num [truncatedMersenneWeight]

/-! ## The correction is small -/

/-- The half-zone correction is strictly smaller than one further scaled
dyadic gap.  This is the analogue of
`exactLateGap_correction_lt_three_mul_gap`. -/
theorem halfGapCorrection_lt_twentyOne_mul_gap
    {s d : ℕ} (hs : 5 ≤ s) (h : InHalfZone s d) :
    halfGapCorrection s d < 21 * 2 ^ (s + 1) := by
  obtain ⟨hd2, hhalf, hthird⟩ := h
  have hds : d < s := by omega
  have hfour : (4 : ℕ) ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
  have e1 : 2 * 4 ^ (s - d) ≤ 2 ^ s := by
    rw [hfour, show (2 : ℕ) * 2 ^ (2 * (s - d)) = 2 ^ (2 * (s - d) + 1) from by
      rw [pow_succ]; ring]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have e2 : 8 * 2 ^ (2 * s - 3 * d) ≤ 2 ^ s := by
    rw [show (8 : ℕ) * 2 ^ (2 * s - 3 * d) = 2 ^ (2 * s - 3 * d + 3) from by
      rw [pow_add]; ring]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have e3 : 2 ^ ((2 * s) % 3) ≤ 4 := by
    calc 2 ^ ((2 * s) % 3) ≤ 2 ^ 2 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  have e4 : (32 : ℕ) ≤ 2 ^ s := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have e5 : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  unfold halfGapCorrection
  omega

/-! ## Word level -/

/-- Exact half-zone adjacent word gap, including an arbitrary common lower
prefix.  Analogue of
`three_mul_largestSkipLowerWeight_add_exactLateGap_eq_upperWeight`. -/
theorem twentyOne_mul_largestSkipLowerWeight_add_exactHalfGap_eq_upperWeight
    {s d : ℕ} {u : Finset ℕ} (h : InHalfZone s d)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d) :
    21 * wordWeightSum s (largestSkipLowerWord s d u).toNatWord +
        (21 * 2 ^ (s + 1) + halfGapCorrection s d) =
      21 * wordWeightSum s (largestSkipUpperWord s d u).toNatWord := by
  classical
  have hd2 : 2 ≤ d := h.two_le
  have hds : d < s := h.lt
  have hdnotu : d ∉ u := by
    intro hdu
    exact (Nat.lt_irrefl d) (hu d hdu).2
  have hdisjoint : Disjoint u (Finset.Ico (d + 1) s) := by
    apply Finset.disjoint_left.mpr
    intro e heu heinterval
    have heu' := hu e heu
    have heinterval' := Finset.mem_Ico.mp heinterval
    omega
  have hlowerBounds :
      ∀ e ∈ u ∪ Finset.Ico (d + 1) s, 2 ≤ e ∧ e < s := by
    intro e he
    rcases Finset.mem_union.mp he with heu | heinterval
    · have hebounds := hu e heu
      exact ⟨hebounds.1, by omega⟩
    · have hebounds := Finset.mem_Ico.mp heinterval
      exact ⟨by omega, hebounds.2⟩
  have hupperBounds : ∀ e ∈ insert d u, 2 ≤ e ∧ e < s := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | heu
    · exact ⟨hd2, hds⟩
    · have hebounds := hu e heu
      exact ⟨hebounds.1, by omega⟩
  have hgap := twentyOne_mul_tailWeight_add_exactHalfGap h
  unfold largestSkipLowerWord largestSkipUpperWord
  rw [wordWeightSum_eq_sum_seamWordSupport,
    wordWeightSum_eq_sum_seamWordSupport,
    seamWordSupport_seamRowWordOfFinset hlowerBounds,
    seamWordSupport_seamRowWordOfFinset hupperBounds,
    Finset.sum_union hdisjoint, Finset.sum_insert hdnotu,
    sum_truncatedMersenneWeight_Ico_eq_seamWeightsFrom_sum
      s (d + 1) (by omega)]
  omega

/-! ## The actual adjacent cut -/

/-- At a half-zone largest false rank, the actual upper adjacent word is the
explicit largest-skip upper word.  Analogue of
`seamAdjacentCut_above_eq_largestSkipUpperWord_of_support`. -/
theorem seamAdjacentCut_above_eq_largestSkipUpperWord_of_halfZone
    {s d : ℕ} {u : Finset ℕ} (hs : 5 ≤ s) (h : InHalfZone s d)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d)
    (hsupp : seamWordSupport (seamGreedyWord s) =
      u ∪ Finset.Ico (d + 1) s) :
    (seamAdjacentCut s hs).above = largestSkipUpperWord s d u := by
  classical
  have hd2 : 2 ≤ d := h.two_le
  have hds : d < s := h.lt
  have hlower :=
    largestSkipLowerWord_weight_eq_greedy_of_support hd2 hu hds hsupp
  have hgap :=
    twentyOne_mul_largestSkipLowerWeight_add_exactHalfGap_eq_upperWeight h hu
  have hcorrection := halfGapCorrection_lt_twentyOne_mul_gap hs h
  have hpos : 0 < 2 ^ (s + 1) := by positivity
  have hupperGt :
      wordWeightSum s (seamGreedyWord s).toNatWord <
        wordWeightSum s (largestSkipUpperWord s d u).toNatWord := by
    omega
  have hcandidateAbove : seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum
        (largestSkipUpperWord s d u) := by
    by_contra hnot
    have hle : (seamPerturbedFamily s (by omega)).oldSum
        (largestSkipUpperWord s d u) ≤ seamSubsetTarget s :=
      Nat.le_of_not_gt hnot
    have hmax := (seamAdjacentCut s hs).below_maximal _ hle
    exact (Nat.not_lt_of_ge hmax) hupperGt
  have hcandidateWindow :
      (seamPerturbedFamily s (by omega)).oldSum
          (largestSkipUpperWord s d u) <
        (seamPerturbedFamily s (by omega)).oldSum
            (seamAdjacentCut s hs).below +
          2 * (seamPerturbedFamily s (by omega)).gap := by
    change wordWeightSum s (largestSkipUpperWord s d u).toNatWord <
      wordWeightSum s (seamGreedyWord s).toNatWord + 2 * 2 ^ (s + 1)
    omega
  exact PerturbedFamily.AdjacentCut.above_eq_of_candidate_lt_two_gap
    (seamAdjacentCut s hs) _ hcandidateAbove hcandidateWindow

/-- **The exact half-zone adjacent gap of the actual seam cut.**  This is the
half-zone analogue of `three_mul_remainder_add_overshoot_eq_exactLateGap`.
Dividing by `21`, the gap is
`2 ^ (s+1) + (2 * 4 ^ (s-d) + 4)/3 + (6 * 2 ^ (2s-3d) + 2 ^ (2s mod 3))/7`. -/
theorem twentyOne_mul_remainder_add_overshoot_eq_exactHalfGap
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (h : InHalfZone s d) :
    21 * ((seamAdjacentCut s hs).remainder +
        (seamAdjacentCut s hs).overshoot) =
      21 * 2 ^ (s + 1) + halfGapCorrection s d := by
  classical
  have hd2 : 2 ≤ d := h.two_le
  have hds : d < s := h.lt
  obtain ⟨u, hu, hsupp⟩ :=
    (isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix
      (seamGreedyWord s) hd2 hds).mp hd
  have hlower :=
    largestSkipLowerWord_weight_eq_greedy_of_support hd2 hu hds hsupp
  have hgap :=
    twentyOne_mul_largestSkipLowerWeight_add_exactHalfGap_eq_upperWeight h hu
  have habove :=
    seamAdjacentCut_above_eq_largestSkipUpperWord_of_halfZone hs h hu hsupp
  have hbelowRem := (seamAdjacentCut s hs).old_below_add_remainder
  have hcapOver := (seamAdjacentCut s hs).capacity_add_overshoot
  change wordWeightSum s (seamGreedyWord s).toNatWord +
      (seamAdjacentCut s hs).remainder = seamSubsetTarget s at hbelowRem
  change seamSubsetTarget s + (seamAdjacentCut s hs).overshoot =
      wordWeightSum s (seamAdjacentCut s hs).above.toNatWord at hcapOver
  rw [habove] at hcapOver
  omega

/-- The half-zone correction is a multiple of `21`, so the gap identity does
divide exactly.  Consequently **no contradiction can be extracted from
divisibility by `21`** (or by `3`, or by `7`): the correction is congruent to
zero for every half-zone rank, unconditionally. -/
theorem twentyOne_dvd_halfGapCorrection {s d : ℕ} (h : InHalfZone s d) :
    21 ∣ halfGapCorrection s d := by
  have hgap := twentyOne_mul_tailWeight_add_exactHalfGap h
  exact ⟨truncatedMersenneWeight s d - (seamWeightsFrom s (d + 1)).sum -
    2 ^ (s + 1), by omega⟩

/-! ## The two zones combined: the exact gap on all of `LargestSkipHalfAt` -/

/-- The exact adjacent-gap correction, at scale `21`, on the whole
`s < 2 * d` region.  The two-thirds branch is the corpus's late correction
`2 * 4 ^ (s - d) + 4` scaled by seven; the half branch is
`halfGapCorrection`. -/
def skipHalfGapCorrection (s d : ℕ) : ℕ :=
  if 2 * s < 3 * d then 7 * (2 * 4 ^ (s - d) + 4) else halfGapCorrection s d

/-- **Unconditional exact adjacent gap for every half-late largest false
rank.**  This is the union of the corpus's two-thirds identity with the
half-zone identity proved above; together they cover all of
`SkipD1.LargestSkipHalfAt`. -/
theorem twentyOne_mul_remainder_add_overshoot_eq_skipHalfGap
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d) (hhalf : s < 2 * d) :
    21 * ((seamAdjacentCut s hs).remainder +
        (seamAdjacentCut s hs).overshoot) =
      21 * 2 ^ (s + 1) + skipHalfGapCorrection s d := by
  unfold skipHalfGapCorrection
  by_cases hlate : 2 * s < 3 * d
  · rw [if_pos hlate]
    have hcorpus :=
      three_mul_remainder_add_overshoot_eq_exactLateGap hs hd hlate
    omega
  · rw [if_neg hlate]
    exact twentyOne_mul_remainder_add_overshoot_eq_exactHalfGap hs hd
      ⟨hd.1, hhalf, by omega⟩

/-- The combined correction is positive and below one further scaled gap. -/
theorem skipHalfGapCorrection_pos_and_lt
    {s d : ℕ} (hs : 5 ≤ s) (hd2 : 2 ≤ d) (hds : d < s) (hhalf : s < 2 * d) :
    0 < skipHalfGapCorrection s d ∧
      skipHalfGapCorrection s d < 21 * 2 ^ (s + 1) := by
  unfold skipHalfGapCorrection halfGapCorrection
  by_cases hlate : 2 * s < 3 * d
  · rw [if_pos hlate]
    have hcorpus := exactLateGap_correction_lt_three_mul_gap hs hds hlate
    have hpos : 0 < (4 : ℕ) ^ (s - d) := by positivity
    omega
  · rw [if_neg hlate]
    have hbound := halfGapCorrection_lt_twentyOne_mul_gap hs
      (⟨hd2, hhalf, by omega⟩ : InHalfZone s d)
    unfold halfGapCorrection at hbound
    have hpos : 0 < (4 : ℕ) ^ (s - d) := by positivity
    omega

/-- **The adjacent gap of a half-late row sits strictly between one and two
dyadic gaps.**  A sharp, correction-free consequence of the two identities. -/
theorem gap_strictly_between_of_largestSkipHalf
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d) (hhalf : s < 2 * d) :
    2 ^ (s + 1) <
        (seamAdjacentCut s hs).remainder + (seamAdjacentCut s hs).overshoot ∧
      (seamAdjacentCut s hs).remainder + (seamAdjacentCut s hs).overshoot <
        2 ^ (s + 2) := by
  have hid := twentyOne_mul_remainder_add_overshoot_eq_skipHalfGap hs hd hhalf
  obtain ⟨hpos, hlt⟩ :=
    skipHalfGapCorrection_pos_and_lt hs hd.1 hd.2.1 hhalf
  have hdouble : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
    rw [pow_succ]; ring
  omega

/-! ## Feeding in the landing constraint -/

/-- Under the `seamExcess = 2` landing constraint the whole gap identity
collapses onto the overshoot alone.  This is the exact form the surviving
`SkipD1` branch has to contradict. -/
theorem twentyOne_mul_overshoot_add_fortyTwo_eq_skipHalfGap
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d) (hhalf : s < 2 * d)
    (hland : seamIntegerGreedyRemainder s = 2 ^ (s + 1) + 2) :
    21 * (seamAdjacentCut s hs).overshoot + 42 = skipHalfGapCorrection s d := by
  have hid := twentyOne_mul_remainder_add_overshoot_eq_skipHalfGap hs hd hhalf
  rw [seamAdjacentCut_remainder hs, hland] at hid
  omega

/-- The landing constraint forces the correction into the window
`[42, 21 * 2 ^ (s+1))`. -/
theorem landing_forces_correction_window
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d) (hhalf : s < 2 * d)
    (hland : seamIntegerGreedyRemainder s = 2 ^ (s + 1) + 2) :
    42 ≤ skipHalfGapCorrection s d ∧
      skipHalfGapCorrection s d < 21 * 2 ^ (s + 1) := by
  have hcollapse :=
    twentyOne_mul_overshoot_add_fortyTwo_eq_skipHalfGap hs hd hhalf hland
  obtain ⟨_, hlt⟩ := skipHalfGapCorrection_pos_and_lt hs hd.1 hd.2.1 hhalf
  exact ⟨by omega, hlt⟩

/-- **The size route is dead.**  The lower end of the landing window is met
automatically: every half-zone correction already exceeds `105 > 42`, with no
hypothesis on the row at all.  Combined with
`halfGapCorrection_lt_twentyOne_mul_gap` for the upper end, this says
`landing_forces_correction_window` is vacuously satisfied — the landing
constraint extracts no size contradiction from a half-zone rank. -/
theorem le_halfGapCorrection {s d : ℕ} (h : InHalfZone s d) :
    105 ≤ halfGapCorrection s d := by
  obtain ⟨hd2, hhalf, hthird⟩ := h
  have hds : d < s := by omega
  have h1 : (4 : ℕ) ^ 1 ≤ 4 ^ (s - d) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (1 : ℕ) ≤ 2 ^ (2 * s - 3 * d) := Nat.one_le_two_pow
  have h3 : (1 : ℕ) ≤ 2 ^ ((2 * s) % 3) := Nat.one_le_two_pow
  unfold halfGapCorrection
  simp only [pow_one] at h1
  omega

/-- Likewise the `21`-divisibility route is dead: the correction is a
multiple of `21` for every half-zone rank, so reducing the landing identity
`21 * overshoot + 42 = halfGapCorrection s d` modulo `21`, `7` or `3`
produces `0 = 0`. -/
theorem landing_congruence_is_trivial {s d : ℕ} (h : InHalfZone s d) :
    halfGapCorrection s d % 21 = 0 := by
  have hdvd := twentyOne_dvd_halfGapCorrection h
  omega

/-! ## Non-vacuity

The half zone is not empty and it is not unreachable: the greedy seam word
really does have a half-zone largest false rank.  A machine scan of the
greedy rows `5 ≤ s ≤ 300` finds the largest false rank is *always* above
`s / 2` (so `SkipD1.LargestSkipHalfAt s` holds throughout that range), and
that it lies in the half zone rather than the two-thirds zone exactly at
`s = 5` (`d = 3`) and `s = 11, 12, 13` (`d = 7`).  The `s = 11` instance is
certified below by kernel evaluation, so the identity above is applied, not
merely true. -/

/-- `7` is the largest false rank of the greedy seam word at `s = 11`. -/
theorem isLargestFalseRank_eleven_seven :
    IsLargestFalseRank (seamGreedyWord 11) 7 := by
  refine ⟨by norm_num, by norm_num, by decide +kernel, ?_⟩
  intro e he1 he2
  interval_cases e <;> decide +kernel

/-- And that rank is in the half zone, not the two-thirds zone. -/
theorem inHalfZone_eleven_seven : InHalfZone 11 7 :=
  ⟨by norm_num, by norm_num, by norm_num⟩

theorem not_late_eleven_seven : ¬ (2 * 11 < 3 * 7) := by norm_num

/-- The hypotheses of the half-zone gap identity are satisfiable, and the
identity pins the adjacent gap at `s = 11` to the exact value `4270`. -/
theorem seamAdjacentCut_gap_eleven (hs : 5 ≤ 11) :
    (seamAdjacentCut 11 hs).remainder + (seamAdjacentCut 11 hs).overshoot =
      4270 := by
  have hid := twentyOne_mul_remainder_add_overshoot_eq_exactHalfGap hs
    isLargestFalseRank_eleven_seven inHalfZone_eleven_seven
  have hcorr : halfGapCorrection 11 7 = 3654 := by
    norm_num [halfGapCorrection]
  have hpow : (2 : ℕ) ^ (11 + 1) = 4096 := by norm_num
  rw [hcorr, hpow] at hid
  omega

end ErdosProblems.HalfH1
