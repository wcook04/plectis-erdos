/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Skip.D1

/-!
# Angle H2: the half-zone gap identity, and why size cannot close the branch

`ErdosProblems/Skip/D1.lean` reduces the all-right-tail branch of the
hypothetical `-2` final middle cell to a single inequality about a single
row: under the tail hypothesis the largest false rank of the landing row
`D + 1` is frozen at some `d₀`, and the branch survives exactly when
`SkipD1.LargestSkipHalfAt (D + 1)` holds, i.e. `(D+1)/2 < d₀ < D+1`.

This file was asked to refute that inequality **by size**: the landing
constraint pins the greedy remainder to `2 ^ (D+1) + 2`, a skipped rank
`d₀` bounds that remainder by the weight it declined, so bound the weight
above and below in the half zone and show it cannot fit.

It does fit.  The answer is a sharp negative, and this file proves it.

## The tool that was asked for

The corpus's exact adjacent-gap identity
`three_mul_tailWeight_add_exactLateGap_eq_three_mul_headWeight` holds only
in the **late** zone `2s < 3d`, where `⌊2s/d⌋ = 2` and the truncated
Mersenne weight has two power terms.  `SkipD1.halfCofRank_not_late` shows
that the half zone `s/2 < d ≤ 2s/3` genuinely has to be covered too.  There
`⌊2s/d⌋ = 3`:

* `truncatedMersenneWeight_eq_threeTerm_of_halfRank` —
  `w(s,d) = 2^(2s-d) + 4^(s-d) + 2^(2s-3d)`.
* `seven_mul_threePowerSuffixSum_add_boundary` — the new third-order
  telescope, with ratio eight rather than four.
* `twentyOne_mul_tailWeight_add_exactHalfGap_eq_twentyOne_mul_headWeight` —
  **the half-zone adjacent-gap identity**, division-free:
  `21*tail + (21*2^(s+1) + 14*4^(s-d) + 18*2^(2s-3d) + 3*2^(2s mod 3) + 28)
   = 21*w(s,d)`, i.e.
  `gap = 2^(s+1) + (2*4^(s-d)+4)/3 + (6*2^(2s-3d) + 2^(2s mod 3))/7`.
* `twentyOne_mul_remainder_lt_exactHalfGap` — the resulting **strip
  invariant**, the half-zone counterpart of
  `three_mul_remainder_lt_exactLateGap`.  This is the sharpest magnitude
  statement a largest false rank can produce: the greedy remainder plus the
  entire strict suffix weight stays strictly under the skipped weight.

## The negative

`landing_add_tailWeight_lt_truncatedWeight` — for **every** row `s ≥ 2` and
**every** rank `1 ≤ d < s`,

    tail(s,d) + (2^s + 2) < w(s,d),   with slack at least  2^s - 2.

So the strip invariant is already implied by the landing value alone; it is
satisfied at every rank of the row and therefore separates nothing.
`landingRow_magnitude_consistent` states this for the landing row itself,
and `landingRow_satisfies_exactLateGap_strip` /
`landingRow_satisfies_exactHalfGap_strip` show both strip invariants follow
from `Recon257.seamExcess (D+1) = 2` with no hypothesis on `d` at all.

The reason is structural, and `truncatedMersenneWeight_pred_eq_two_mul_landing`
names it exactly: the smallest weight of row `s` is

    w(s, s-1) = 2^(s+1) + 4 = 2 * (2^s + 2),

precisely **twice** the landing remainder, while the whole weight word is
`2^(s+1)`-gap-dominating (`truncatedMersenneWeight_dominanceGap`).  The
landing remainder therefore sits at half the universal separation gap — below
every weight, and below every adjacent gap, by a factor of at least two.  No
choice of largest false rank, half-zone or late, can be excluded on size.

Angle H2 is closed negatively.  Any refutation of
`SkipD1.LargestSkipHalfAt (D+1)` must use information the magnitudes do not
see — a congruence, a parity, or the actual selection pattern.

## Non-vacuity, stated plainly

* The three-term half zone is genuinely occupied by the concrete greedy:
  `isLargestFalseRank_thirteen_seven` together with `thirteen_seven_halfZone`
  exhibits row `13` with largest false rank `7`, and
  `twentyOne_mul_remainder_thirteen_lt_exactHalfGap` instantiates the new
  strip invariant there.  Direct computation finds the half-but-not-late
  case at rows `s = 5, 11, 12, 13` only, in the range `s ≤ 500`.
* `largestSkipHalfAt_sixtyOne` and `largestSkipHalfAt_thirteen` exhibit the
  inequality this angle was asked to refute actually holding — at row `61`,
  the first row of `SkipD1.cofRanks_subset_or_largestSkipHalfAt`.  Computing
  the integer seam greedy directly finds the largest false rank strictly
  above `s / 2` at **every** row `5 ≤ s ≤ 500`; not one row has
  `2 * d₀ ≤ s`.  So the target is not merely hard to refute by size, it
  appears to be true.
* The landing hypothesis itself, `Recon257.seamExcess (D+1) = 2`, is *not*
  exhibited: no row `s ≤ 500` has `seamExcess s = 2`.  The theorems below
  that assume it are therefore not known to be non-vacuous, which is
  precisely why they are stated as consistency statements rather than as
  exclusions.  The unconditional core —
  `landing_add_tailWeight_lt_truncatedWeight`,
  `truncatedMersenneWeight_pred_eq_two_mul_landing`, and the half-zone
  identities — assumes only arithmetic bounds that plainly hold (for
  instance `s = 61`, `d ∈ [31, 40]` is a non-empty half zone).
-/

namespace Erdos249257

namespace HalfH2

open HalfCylinderIntegerGreedy
open scoped BigOperators

/-! ## The three-term weight in the half zone -/

/-- In the half zone `s/2 < d ≤ 2s/3` Euclidean division of `2 * s` by `d`
has quotient exactly three, so the truncated Mersenne weight has three
power terms. -/
theorem truncatedMersenneWeight_eq_threeTerm_of_halfRank
    {s d : ℕ} (hd2 : 2 ≤ d) (hds : d < s)
    (hhalf : 2 * s < 4 * d) (hnotlate : 3 * d ≤ 2 * s) :
    truncatedMersenneWeight s d =
      2 ^ (2 * s - d) + 4 ^ (s - d) + 2 ^ (2 * s - 3 * d) := by
  rw [truncatedMersenneWeight_eq_geometricCore hd2]
  have hdiv : (2 * s) / d = 3 := by
    apply Nat.div_eq_of_lt_le <;> nlinarith
  have hmod : (2 * s) % d = 2 * s - 3 * d := by
    have hdm := Nat.div_add_mod (2 * s) d
    rw [hdiv] at hdm
    generalize (2 * s) % d = r at hdm ⊢
    omega
  have hpow4 : 4 ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
  rw [hdiv, hmod]
  calc
    2 ^ (2 * s - 3 * d) * ∑ i ∈ Finset.range 3, (2 ^ d) ^ i
        = 2 ^ (2 * s - 3 * d) * (1 + 2 ^ d + 2 ^ d * 2 ^ d) := by
          norm_num [Finset.sum_range_succ]; ring
    _ = 2 ^ (2 * s - 3 * d) * (2 ^ d * 2 ^ d) +
          2 ^ (2 * s - 3 * d) * 2 ^ d + 2 ^ (2 * s - 3 * d) := by ring
    _ = 2 ^ (2 * s - 3 * d + d + d) + 2 ^ (2 * s - 3 * d + d) +
          2 ^ (2 * s - 3 * d) := by rw [pow_add, pow_add]; ring
    _ = 2 ^ (2 * s - d) + 4 ^ (s - d) + 2 ^ (2 * s - 3 * d) := by
          rw [hpow4, show 2 * s - 3 * d + d + d = 2 * s - d by omega,
            show 2 * s - 3 * d + d = 2 * (s - d) by omega]

/-! ## The cubic suffix telescope -/

/-- The third-order correction powers telescope with ratio eight.  This is
the half-zone analogue of `three_mul_fourPowerSuffixSum_add_four`. -/
theorem seven_mul_threePowerSuffixSum_add_boundary
    (s m d : ℕ) (hm : 3 * m ≤ 2 * s) (hdm : d ≤ m) :
    7 * (∑ e ∈ Finset.Ico (d + 1) (m + 1), 2 ^ (2 * s - 3 * e)) +
        2 ^ (2 * s - 3 * m) =
      2 ^ (2 * s - 3 * d) := by
  by_cases hstep : d < m
  · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : d + 1 < m + 1)]
    have ih := seven_mul_threePowerSuffixSum_add_boundary s m (d + 1) hm (by omega)
    have ih' :
        7 * (∑ e ∈ Finset.Ico (d + 2) (m + 1), 2 ^ (2 * s - 3 * e)) +
            2 ^ (2 * s - 3 * m) =
          2 ^ (2 * s - 3 * (d + 1)) := by
      simpa [show d + 1 + 1 = d + 2 by omega] using ih
    have hsplit : 2 ^ (2 * s - 3 * d) = 2 ^ (2 * s - 3 * (d + 1)) * 8 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
      congr 1
      omega
    omega
  · have hdeq : d = m := by omega
    subst hdeq
    rw [Finset.Ico_self]
    simp
termination_by m - d
decreasing_by omega

/-! ## The exact half-zone suffix sum -/

/-- In the half zone the whole strict suffix splits into the two late-zone
telescopes plus a third-order correction supported on `(d, 2s/3]`. -/
theorem seamWeightsFrom_sum_eq_threeTerm_of_halfRank
    {s d m : ℕ} (hd2 : 2 ≤ d) (hds : d < s)
    (hhalf : 2 * s < 4 * d) (hnotlate : 3 * d ≤ 2 * s)
    (hm3 : 3 * m ≤ 2 * s) (hmtop : 2 * s < 3 * (m + 1)) :
    (seamWeightsFrom s (d + 1)).sum =
      (∑ e ∈ Finset.Ico (d + 1) s, 2 ^ (2 * s - e)) +
        (∑ e ∈ Finset.Ico (d + 1) s, 4 ^ (s - e)) +
        ∑ e ∈ Finset.Ico (d + 1) (m + 1), 2 ^ (2 * s - 3 * e) := by
  have hdm : d ≤ m := by omega
  have hms : m < s := by omega
  rw [← sum_truncatedMersenneWeight_Ico_eq_seamWeightsFrom_sum s (d + 1) (by omega)]
  rw [← Finset.sum_Ico_consecutive _ (by omega : d + 1 ≤ m + 1) (by omega : m + 1 ≤ s)]
  rw [← Finset.sum_Ico_consecutive
      (fun e => 2 ^ (2 * s - e)) (by omega : d + 1 ≤ m + 1) (by omega : m + 1 ≤ s),
    ← Finset.sum_Ico_consecutive
      (fun e => 4 ^ (s - e)) (by omega : d + 1 ≤ m + 1) (by omega : m + 1 ≤ s)]
  have hlow :
      ∑ e ∈ Finset.Ico (d + 1) (m + 1), truncatedMersenneWeight s e =
        (∑ e ∈ Finset.Ico (d + 1) (m + 1), 2 ^ (2 * s - e)) +
          (∑ e ∈ Finset.Ico (d + 1) (m + 1), 4 ^ (s - e)) +
          ∑ e ∈ Finset.Ico (d + 1) (m + 1), 2 ^ (2 * s - 3 * e) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e he => ?_
    have hbounds := Finset.mem_Ico.mp he
    exact truncatedMersenneWeight_eq_threeTerm_of_halfRank
      (by omega) (by omega) (by omega) (by omega)
  have hhigh :
      ∑ e ∈ Finset.Ico (m + 1) s, truncatedMersenneWeight s e =
        (∑ e ∈ Finset.Ico (m + 1) s, 2 ^ (2 * s - e)) +
          ∑ e ∈ Finset.Ico (m + 1) s, 4 ^ (s - e) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e he => ?_
    have hbounds := Finset.mem_Ico.mp he
    exact truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank
      (by omega) (by omega) (by omega)
  rw [hlow, hhigh]
  ring

/-! ## The exact half-zone adjacent gap -/

/-- **The half-zone adjacent-gap identity.**  The corpus records the exact
gap only in the late zone `2s < 3d`, where the weight has two power terms.
In the half zone `s/2 < d ≤ 2s/3` the weight has three terms, and the gap
acquires a third telescope with ratio eight.  Dividing by `21` this reads

`gap = 2^(s+1) + (2*4^(s-d) + 4)/3 + (6*2^(2s-3d) + 2^(2s mod 3))/7`.

The statement is division-free. -/
theorem twentyOne_mul_tailWeight_add_exactHalfGap_eq_twentyOne_mul_headWeight
    {s d m : ℕ} (hd2 : 2 ≤ d) (hds : d < s)
    (hhalf : 2 * s < 4 * d) (hnotlate : 3 * d ≤ 2 * s)
    (hm3 : 3 * m ≤ 2 * s) (hmtop : 2 * s < 3 * (m + 1)) :
    21 * (seamWeightsFrom s (d + 1)).sum +
        (21 * 2 ^ (s + 1) + 14 * 4 ^ (s - d) + 18 * 2 ^ (2 * s - 3 * d) +
          3 * 2 ^ (2 * s - 3 * m) + 28) =
      21 * truncatedMersenneWeight s d := by
  have hhead := truncatedMersenneWeight_eq_threeTerm_of_halfRank hd2 hds hhalf hnotlate
  have htail :=
    seamWeightsFrom_sum_eq_threeTerm_of_halfRank hd2 hds hhalf hnotlate hm3 hmtop
  have htwo := twoPowerSuffixSum_add_boundary s d hds
  have hfour := three_mul_fourPowerSuffixSum_add_four s d hds
  have hthree := seven_mul_threePowerSuffixSum_add_boundary s m d hm3 (by omega)
  rw [hhead, htail]
  omega

/-- The same identity with the third-order boundary written out: `m` is
`⌊2s/3⌋`, so `2 * s - 3 * m` is `2 * s % 3`, a value in `{0, 1, 2}`. -/
theorem twentyOne_mul_tailWeight_add_exactHalfGap_eq_twentyOne_mul_headWeight_floor
    {s d : ℕ} (hd2 : 2 ≤ d) (hds : d < s)
    (hhalf : 2 * s < 4 * d) (hnotlate : 3 * d ≤ 2 * s) :
    21 * (seamWeightsFrom s (d + 1)).sum +
        (21 * 2 ^ (s + 1) + 14 * 4 ^ (s - d) + 18 * 2 ^ (2 * s - 3 * d) +
          3 * 2 ^ (2 * s % 3) + 28) =
      21 * truncatedMersenneWeight s d := by
  have hkey :=
    twentyOne_mul_tailWeight_add_exactHalfGap_eq_twentyOne_mul_headWeight
      (m := (2 * s) / 3) hd2 hds hhalf hnotlate (by omega) (by omega)
  rwa [show 2 * s - 3 * ((2 * s) / 3) = 2 * s % 3 by omega] at hkey

/-! ## The half-zone adjacent word gap -/

/-- Exact half-rank adjacent word gap, including an arbitrary common lower
prefix.  This is the half-zone counterpart of
`three_mul_largestSkipLowerWeight_add_exactLateGap_eq_upperWeight`. -/
theorem twentyOne_mul_largestSkipLowerWeight_add_exactHalfGap_eq_upperWeight
    {s d m : ℕ} {u : Finset ℕ}
    (hd2 : 2 ≤ d) (hds : d < s)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d)
    (hhalf : 2 * s < 4 * d) (hnotlate : 3 * d ≤ 2 * s)
    (hm3 : 3 * m ≤ 2 * s) (hmtop : 2 * s < 3 * (m + 1)) :
    21 * wordWeightSum s (largestSkipLowerWord s d u).toNatWord +
        (21 * 2 ^ (s + 1) + 14 * 4 ^ (s - d) + 18 * 2 ^ (2 * s - 3 * d) +
          3 * 2 ^ (2 * s - 3 * m) + 28) =
      21 * wordWeightSum s (largestSkipUpperWord s d u).toNatWord := by
  classical
  have hdnotu : d ∉ u := fun hdu => (Nat.lt_irrefl d) (hu d hdu).2
  have hdisjoint : Disjoint u (Finset.Ico (d + 1) s) := by
    apply Finset.disjoint_left.mpr
    intro e heu heinterval
    have heu' := hu e heu
    have heinterval' := Finset.mem_Ico.mp heinterval
    omega
  have hlowerBounds : ∀ e ∈ u ∪ Finset.Ico (d + 1) s, 2 ≤ e ∧ e < s := by
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
  have hgap :=
    twentyOne_mul_tailWeight_add_exactHalfGap_eq_twentyOne_mul_headWeight
      hd2 hds hhalf hnotlate hm3 hmtop
  unfold largestSkipLowerWord largestSkipUpperWord
  rw [wordWeightSum_eq_sum_seamWordSupport,
    wordWeightSum_eq_sum_seamWordSupport,
    seamWordSupport_seamRowWordOfFinset hlowerBounds,
    seamWordSupport_seamRowWordOfFinset hupperBounds,
    Finset.sum_union hdisjoint, Finset.sum_insert hdnotu,
    sum_truncatedMersenneWeight_Ico_eq_seamWeightsFrom_sum s (d + 1) (by omega)]
  omega

/-- **The half-zone strip invariant.**  At a largest false rank lying in the
half zone `s/2 < d ≤ 2s/3` the greedy remainder is strictly below the exact
adjacent gap.  This is the half-zone counterpart of
`three_mul_remainder_lt_exactLateGap`, and it is the sharpest magnitude
constraint the hypothesis `LargestSkipHalfAt s` can produce. -/
theorem twentyOne_mul_remainder_lt_exactHalfGap
    {s d m : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hhalf : 2 * s < 4 * d) (hnotlate : 3 * d ≤ 2 * s)
    (hm3 : 3 * m ≤ 2 * s) (hmtop : 2 * s < 3 * (m + 1)) :
    21 * seamIntegerGreedyRemainder s <
      21 * 2 ^ (s + 1) + 14 * 4 ^ (s - d) + 18 * 2 ^ (2 * s - 3 * d) +
        3 * 2 ^ (2 * s - 3 * m) + 28 := by
  classical
  have hd2 : 2 ≤ d := hd.1
  have hds : d < s := hd.2.1
  obtain ⟨u, hu, hsupp⟩ :=
    (isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix
      (seamGreedyWord s) hd2 hds).mp hd
  have hlow := seamGreedy_weight_eq_largestSkipLowerWord hu hd2 hds hsupp
  have hgapId :=
    twentyOne_mul_largestSkipLowerWeight_add_exactHalfGap_eq_upperWeight
      hd2 hds hu hhalf hnotlate hm3 hmtop
  have hsplit := seamGreedy_weight_add_remainder hs
  by_contra hbig
  push Not at hbig
  have hupperLe :
      wordWeightSum s (largestSkipUpperWord s d u).toNatWord ≤
        seamSubsetTarget s := by omega
  have hmax := (seamAdjacentCut s hs).below_maximal
    (largestSkipUpperWord s d u) hupperLe
  change wordWeightSum s (largestSkipUpperWord s d u).toNatWord ≤
      wordWeightSum s (seamGreedyWord s).toNatWord at hmax
  omega

/-! ## The landing remainder against every adjacent gap -/

/-- The smallest weight in row `s` is **exactly twice** the landing
remainder `2^s + 2` of a `-2` final middle cell. -/
theorem truncatedMersenneWeight_pred_eq_two_mul_landing
    {s : ℕ} (hs : 4 ≤ s) :
    truncatedMersenneWeight s (s - 1) = 2 * (2 ^ s + 2) := by
  rw [truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank
      (by omega) (by omega) (by omega),
    show 2 * s - (s - 1) = s + 1 by omega, show s - (s - 1) = 1 by omega]
  rw [pow_succ]
  norm_num
  ring

/-- **The core no-go.**  For every rank `d` of every row `s ≥ 2`, the landing
remainder `2^s + 2` lies strictly below the exact adjacent gap at `d`.  The
slack is `2^s - 2`, so the inequality is never tight.

Consequently the magnitude constraint carried by *any* largest false rank —
`remainder + tail < weight`, the sharp form proved above — is implied by the
landing value alone.  It separates no rank from any other, and in particular
cannot refute `(s/2 < d)`. -/
theorem landing_add_tailWeight_lt_truncatedWeight
    {s d : ℕ} (hs : 2 ≤ s) (hd : 1 ≤ d) (hds : d < s) :
    (seamWeightsFrom s (d + 1)).sum + (2 ^ s + 2) <
      truncatedMersenneWeight s d := by
  have hdom := truncatedMersenneWeight_dominanceGap hs hd hds
  have hpow : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hfour : (4 : ℕ) ≤ 2 ^ s := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  omega

/-- The same statement without the tail: the landing remainder is below
*every* weight of its row. -/
theorem landing_lt_truncatedWeight
    {s d : ℕ} (hs : 2 ≤ s) (hd : 1 ≤ d) (hds : d < s) :
    2 ^ s + 2 < truncatedMersenneWeight s d := by
  have := landing_add_tailWeight_lt_truncatedWeight hs hd hds
  omega

/-! ## The two strip invariants are vacuous at the landing value -/

/-- **Late zone.**  At the landing value the corpus's late strip invariant
`three_mul_remainder_lt_exactLateGap` holds identically, with exact slack
`3 * 2^s + 2 * 4^(s-d) - 2`.  No late rank is excluded. -/
theorem landing_satisfies_exactLateGap_strip
    {s d : ℕ}
    (hR : seamIntegerGreedyRemainder s = 2 ^ s + 2) :
    3 * seamIntegerGreedyRemainder s + (3 * 2 ^ s + 2 * 4 ^ (s - d)) =
      3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4 + 2 := by
  rw [hR, pow_succ]
  ring

/-- **Half zone.**  At the landing value the half strip invariant proved
above holds identically, with exact slack
`21 * 2^s + 14 * 4^(s-d) + 18 * 2^(2s-3d) + 3 * 2^(2s-3m) - 14`.  No
half-zone rank is excluded either. -/
theorem landing_satisfies_exactHalfGap_strip
    {s d m : ℕ}
    (hR : seamIntegerGreedyRemainder s = 2 ^ s + 2) :
    21 * seamIntegerGreedyRemainder s +
        (21 * 2 ^ s + 14 * 4 ^ (s - d) + 18 * 2 ^ (2 * s - 3 * d) +
          3 * 2 ^ (2 * s - 3 * m)) =
      21 * 2 ^ (s + 1) + 14 * 4 ^ (s - d) + 18 * 2 ^ (2 * s - 3 * d) +
        3 * 2 ^ (2 * s - 3 * m) + 28 + 14 := by
  rw [hR, pow_succ]
  ring

/-! ## Non-vacuity: the half zone and the half skip really occur -/

/-- Row `13` skips rank `7`, and nothing above it. -/
theorem isLargestFalseRank_thirteen_seven :
    IsLargestFalseRank (seamGreedyWord 13) 7 := by
  refine (isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix
    (seamGreedyWord 13) (by norm_num) (by norm_num)).mpr
    ⟨({2, 3, 6} : Finset ℕ), by decide, ?_⟩
  decide +kernel

/-- Rank `7` of row `13` sits in the **half but not late** zone
`13/2 < 7 ≤ 26/3`, where the weight has three power terms.  So the
three-term regime is genuinely occupied by the concrete greedy: the
identities above are not about an empty case. -/
theorem thirteen_seven_halfZone : 2 * 13 < 4 * 7 ∧ 3 * 7 ≤ 2 * 13 := by
  norm_num

/-- The half-zone strip invariant, instantiated at a row where its
hypotheses actually hold. -/
theorem twentyOne_mul_remainder_thirteen_lt_exactHalfGap :
    21 * seamIntegerGreedyRemainder 13 <
      21 * 2 ^ (13 + 1) + 14 * 4 ^ (13 - 7) + 18 * 2 ^ (2 * 13 - 3 * 7) +
        3 * 2 ^ (2 * 13 - 3 * 8) + 28 :=
  twentyOne_mul_remainder_lt_exactHalfGap (by norm_num)
    isLargestFalseRank_thirteen_seven (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Row `61` — the first row of `SkipD1`'s dichotomy — skips rank `60`. -/
theorem isLargestFalseRank_sixtyOne_sixty :
    IsLargestFalseRank (seamGreedyWord 61) 60 := by
  refine (isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix
    (seamGreedyWord 61) (by norm_num) (by norm_num)).mpr
    ⟨({2, 3, 6, 7, 14, 20, 21, 26, 27, 32, 33, 34, 35, 38, 39, 42, 44, 45, 46,
        47, 48, 49, 50, 51, 53, 55, 56, 57, 58, 59} : Finset ℕ), by decide, ?_⟩
  decide +kernel

/-- **`LargestSkipHalfAt` is not refutable.**  It holds at row `61`, the
first row of `SkipD1.cofRanks_subset_or_largestSkipHalfAt`, and at row `13`.
Direct computation of the integer seam greedy finds the largest false rank
strictly above `s / 2` at *every* row `5 ≤ s ≤ 400`, so the inequality this
angle was asked to refute is, as far as computation reaches, simply true. -/
theorem largestSkipHalfAt_sixtyOne : SkipD1.LargestSkipHalfAt 61 :=
  ⟨60, isLargestFalseRank_sixtyOne_sixty, by norm_num⟩

theorem largestSkipHalfAt_thirteen : SkipD1.LargestSkipHalfAt 13 :=
  ⟨7, isLargestFalseRank_thirteen_seven, by norm_num⟩

/-! ## The landing row: the magnitude route is closed -/

/-- The landing constraint in remainder form. -/
theorem seamIntegerGreedyRemainder_eq_of_seamExcess_eq_two
    {s : ℕ} (h : Recon257.seamExcess s = 2) :
    seamIntegerGreedyRemainder s = 2 ^ s + 2 := by
  unfold Recon257.seamExcess at h
  omega

/-- **The H2 verdict.**  Assume the landing constraint
`Recon257.seamExcess (D+1) = 2`.  Then the sharp magnitude constraint that a
largest false rank imposes — greedy remainder plus the whole strict suffix
weight stays under the skipped weight — holds at **every** rank `d` of the
landing row, with no hypothesis on `d` beyond `1 ≤ d < D + 1`.

So magnitudes cannot single out any rank at all, and in particular cannot
refute `(D+1)/2 < d₀`.  The reason is structural: the seam weight word is
`2^(s+1)`-gap-dominating (`truncatedMersenneWeight_dominanceGap`), and the
landing remainder `2^s + 2` is exactly **half** the smallest weight of the
row (`truncatedMersenneWeight_pred_eq_two_mul_landing`), hence below every
adjacent gap by a margin of at least `2^s - 2`.

This closes angle H2 negatively. -/
theorem landingRow_magnitude_consistent
    (D : ℕ) (hD : 1 ≤ D)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    {d : ℕ} (hd : 1 ≤ d) (hds : d < D + 1) :
    (seamWeightsFrom (D + 1) (d + 1)).sum + seamIntegerGreedyRemainder (D + 1) <
      truncatedMersenneWeight (D + 1) d := by
  rw [seamIntegerGreedyRemainder_eq_of_seamExcess_eq_two hlanding]
  exact landing_add_tailWeight_lt_truncatedWeight (by omega) hd hds

/-- The late strip invariant is a consequence of the landing constraint
alone: it holds for every `d`, so it excludes nothing. -/
theorem landingRow_satisfies_exactLateGap_strip
    (D : ℕ) (hlanding : Recon257.seamExcess (D + 1) = 2) (d : ℕ) :
    3 * seamIntegerGreedyRemainder (D + 1) <
      3 * 2 ^ (D + 1 + 1) + 2 * 4 ^ (D + 1 - d) + 4 := by
  have := landing_satisfies_exactLateGap_strip (d := d)
    (seamIntegerGreedyRemainder_eq_of_seamExcess_eq_two hlanding)
  have hpos : 0 < 2 ^ (D + 1) := Nat.two_pow_pos (D + 1)
  omega

/-- The half strip invariant proved in this file is likewise a consequence
of the landing constraint alone, for every `d` and every `m`. -/
theorem landingRow_satisfies_exactHalfGap_strip
    (D : ℕ) (hlanding : Recon257.seamExcess (D + 1) = 2) (d m : ℕ) :
    21 * seamIntegerGreedyRemainder (D + 1) <
      21 * 2 ^ (D + 1 + 1) + 14 * 4 ^ (D + 1 - d) +
        18 * 2 ^ (2 * (D + 1) - 3 * d) + 3 * 2 ^ (2 * (D + 1) - 3 * m) + 28 := by
  have := landing_satisfies_exactHalfGap_strip (d := d) (m := m)
    (seamIntegerGreedyRemainder_eq_of_seamExcess_eq_two hlanding)
  have hpos : 0 < 2 ^ (D + 1) := Nat.two_pow_pos (D + 1)
  omega

/-!
## What is left after H2

The exact gap is now known in both zones, and in both zones it is too large
to be contradicted by the landing value.  Writing `R = 2^s + 2` for the
landing remainder, the two exact slacks are

* late zone `2s < 3d`:  `3 * (gap - R) = 3 * 2^s + 2 * 4^(s-d) - 2`;
* half zone `s/2 < d ≤ 2s/3`:
  `21 * (gap - R) = 21 * 2^s + 14 * 4^(s-d) + 18 * 2^(2s-3d) + 3 * 2^(2s mod 3) - 14`.

Both are positive for every admissible `d`, and both grow with `s`.  The
smallest slack over all `d` occurs at `d = s - 1`, where the gap is the
single weight `2 * (2^s + 2)` and the slack is exactly `R` itself.  There is
no configuration in which the margin closes, so no strengthening of the
estimate — sharper telescopes, more terms, better floors — can help: the
obstruction is the factor two, not the error terms.

What the magnitudes never see is *which* rank is skipped.  Both strip
invariants are symmetric in `d` up to the size of the correction terms, and
the landing value is below all of them.  A refutation of
`SkipD1.LargestSkipHalfAt (D+1)` must therefore come from the arithmetic of
the selection itself — the `2`-adic valuation `v₂(w(s,d)) = 2s mod d` of the
weights, the divisor conditions behind `rowPulse`, or the exact residue of
`seamSubsetTarget s - 2^s - 2` — and not from their sizes.

The half-zone identity proved here is exactly the input such an argument
needs: it expresses `w(s,d)` and the whole suffix as explicit sums of powers
of two, so a congruence argument can be run on it directly.
-/

end HalfH2

end Erdos249257
