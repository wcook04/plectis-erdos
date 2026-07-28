/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.AngleB2

/-!
# Half H3: the two-adic valuation of the seam weights

This file attacks the residue left by `ErdosProblems/Skip/D1.lean` —

  `allRight_landingExcess_two_forces_halfSkip_landingRow` : an all-right tail
  from `D+1` together with `Recon257.seamExcess (D+1) = 2` forces
  `LargestSkipHalfAt (D+1)`

— from the arithmetic side rather than the size side.  The landing constraint
pins the greedy remainder to the *exact* value `2 ^ (D+1) + 2`, whose two-adic
valuation is exactly one.  So it is natural to ask whether the valuations
forced by a half-zone largest false rank can clash with that.

The answer is developed here in three steps.  The third step proves that the
modulo-`2` and modulo-`4` shadows cannot produce the desired clash; it does not
rule out every higher two-adic argument.

## 1. The valuation law

`truncatedMersenneWeight s d = 4 ^ s / (2 ^ d - 1)` has Euclidean form
`2 ^ ((2*s) % d) * G` with `G = ∑ i < (2*s)/d, (2^d)^i`, and `G = 2^d * H + 1`.
Hence

  `v₂ (truncatedMersenneWeight s d) = (2 * s) % d`

exactly (`truncatedMersenneWeight_eq_twoPow_mul_geom`,
`truncatedMersenneWeight_mod_two`, `truncatedMersenneWeight_mod_four`).  In
particular the weight of rank `d` is **odd exactly when `d ∣ 2 * s`**, and is
`≡ 2 (mod 4)` exactly when `d ∣ 2 * s - 1`.

## 2. The parity law for the concrete integer seam greedy

`seamSubsetTarget s = 2 ^ (2s-1) - 2 ^ s` is even, and the greedy remainder is
the target minus the selected weight sum, so

  `seamIntegerGreedyRemainder s ≡ # { d ∈ support s : d ∣ 2 * s }  (mod 2)`

(`seamIntegerGreedyRemainder_mod_two`).  This file proves that parity identity
for the concrete remainder.

Its sharpest consequence is unconditional.  For a **prime** row the only rank
below the row that divides `2 * s` is `2` itself, and rank `2` is a proven
member of the greedy support from row `13` on.  So the count is `1`, and:

* `seamIntegerGreedyRemainder_odd_of_prime` — for every prime `s ≥ 13` the
  concrete greedy remainder is **odd**;
* `seamExcess_ne_two_of_prime` — hence `Recon257.seamExcess s ≠ 2`, and indeed
  `seamExcess s` is odd, so it misses every even value;
* `finalMiddleCell_neg_two_impossible_of_prime_succ` — hence a final middle
  cell of charge `-2` at rank `D` is impossible whenever `D + 1` is prime,
  **with no tail hypothesis at all**: no `hright`, no `hcof`, no bound `S`.

### Honest accounting of what that gains

It is *not* a new set of classes.  `Recon257.SurvivorPhase D` demands
`D % 21 ∈ {11, 14, 17, 20}`, i.e. `D + 1 ≡ 0 (mod 3)`, so a class with `D + 1`
prime is never a survivor and was already killed by
`Recon257.ratchetRun_eq_zero_of_not_survivorPhase` — but only *given* the
all-right tail, which the ratchet's soundness proof consumes.  What is gained
here is the removal of that hypothesis on this family, and a route that is
insensitive to the ratchet's geometric-discount obstruction.  The hypotheses of
`seamExcess_ne_two_of_prime` are satisfied by `s = 13, 17, 19, 23, 29, …`, so
nothing here is vacuous; but the *class count* is unchanged.

## 3. The sharp negative: the two-adic shadow is blind to the late zone

The reason the valuation route cannot refute `LargestSkipHalfAt (D+1)` is exact
and is proved here:

* `dvd_two_mul_not_late` — every rank `d < s` dividing `2 * s` satisfies
  `3 * d ≤ 2 * s`, and the *only* one that even reaches the half zone is the
  cofactor-`3` rank `3 * d = 2 * s` itself (`dvd_two_mul_half_eq_cofThree`).
  The same holds for `2 * s - 1` (`dvd_two_mul_sub_one_not_late`).
* `four_dvd_truncatedMersenneWeight_of_late` — every rank strictly inside the
  late zone `2 * s < 3 * d` has weight divisible by `4`.
* `four_dvd_lateBlock`, `sum_seamWordSupport_mod_four_of_late` — therefore the
  entire filled block above a late largest false rank contributes `0` modulo
  `4`, and the mod-`4` residue of the selected weight sum is carried **entirely
  by ranks at or below two thirds of the row**.
* `lateBlock_mod_four_indep` — two different late largest false ranks give
  literally the same mod-`4` shadow.

So the mod-`2` and mod-`4` reductions of `seamExcess (D+1) = 2` are functions
of the sub-two-thirds support alone; they cannot distinguish `d₀ > (D+1)/2`
from `d₀ ≤ (D+1)/2`, and no modulo-`2` or modulo-`4` clash of that order exists.
The finer
reduction modulo `2 ^ (s+1)` does see the late rank — by
`truncatedMersenneWeight_mod_twoPow_of_late` the entire low half of a late
weight is the single power `4 ^ (s-d)`.  This file does not prove that this
higher-modulus information is absorbed by the low support, and therefore makes
no no-go claim for that finer reduction.

**I did not refute `LargestSkipHalfAt (D+1)`.**  The measurement is worse than
neutral for that hope: direct computation of
`integerGreedyBits (seamWeights s) (seamSubsetTarget s)` gives
`LargestSkipHalfAt s` at *every* row `s ∈ [5, 400]` without exception (and
`LargestSkipLateAt s` at every row except `s = 5, 11, 12, 13`), so the
inequality to be refuted is in fact always true on the computed range.  The
hypothesis it would be refuted from, `seamExcess s = 2`, holds at **no** row in
`[5, 400]`.  Any proof of the D1 target is therefore a proof that
`seamIntegerGreedyRemainder s ≠ 2 ^ s + 2` outright, and the prime family above
is exactly the part of that statement the valuation law can reach.
-/

namespace Erdos249257

namespace HalfH3

open HalfCylinderIntegerGreedy
open scoped BigOperators

/-! ## 1. The two-adic law for the truncated Mersenne weights -/

/-- A positive power of two is twice something. -/
theorem two_dvd_two_pow {n : ℕ} (hn : 1 ≤ n) : ∃ k : ℕ, (2 : ℕ) ^ n = 2 * k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨2 ^ m, by rw [pow_succ]; ring⟩

/-- A power of two with exponent at least two is four times something. -/
theorem four_dvd_two_pow {n : ℕ} (hn : 2 ≤ n) : ∃ k : ℕ, (2 : ℕ) ^ n = 4 * k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact ⟨2 ^ m, by rw [pow_add]; ring⟩

/-- The geometric core `∑ i < q, (2^d)^i` is `2^d * H + 1`. -/
theorem geometricCore_eq_twoPow_mul_add_one (d : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    ∃ H : ℕ, (∑ i ∈ Finset.range q, (2 ^ d) ^ i) = 2 ^ d * H + 1 := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  refine ⟨∑ i ∈ Finset.range q', (2 ^ d) ^ i, ?_⟩
  rw [Finset.sum_range_succ', pow_zero, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by rw [pow_succ]; ring)

/-- **The valuation law.**  The truncated Mersenne weight factors as
`2 ^ ((2*s) % d)` times an odd number of the shape `2^d * H + 1`.  Its two-adic
valuation is therefore exactly `(2 * s) % d`. -/
theorem truncatedMersenneWeight_eq_twoPow_mul_geom
    {s d : ℕ} (hd2 : 2 ≤ d) (hds : d ≤ 2 * s) :
    ∃ H : ℕ, truncatedMersenneWeight s d =
      2 ^ ((2 * s) % d) * (2 ^ d * H + 1) := by
  have hq : 1 ≤ (2 * s) / d := (Nat.one_le_div_iff (by omega)).mpr hds
  obtain ⟨H, hH⟩ := geometricCore_eq_twoPow_mul_add_one d hq
  exact ⟨H, by rw [truncatedMersenneWeight_eq_geometricCore hd2, hH]⟩

/-- The weight of rank `d` at row `s` is **odd exactly when `d ∣ 2 * s`**. -/
theorem truncatedMersenneWeight_mod_two
    {s d : ℕ} (hd2 : 2 ≤ d) (hds : d ≤ 2 * s) :
    truncatedMersenneWeight s d % 2 = if d ∣ 2 * s then 1 else 0 := by
  obtain ⟨H, hH⟩ := truncatedMersenneWeight_eq_twoPow_mul_geom hd2 hds
  obtain ⟨k, hk⟩ := two_dvd_two_pow (show 1 ≤ d by omega)
  have hkH : 2 ^ d * H = 2 * (k * H) := by rw [hk]; ring
  by_cases hdvd : d ∣ 2 * s
  · obtain ⟨c, hc⟩ := hdvd
    have hr : (2 * s) % d = 0 := by rw [hc]; exact Nat.mul_mod_right d c
    rw [hr, pow_zero, one_mul] at hH
    rw [if_pos ⟨c, hc⟩]
    omega
  · have hr : (2 * s) % d ≠ 0 := fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
    obtain ⟨j, hj⟩ := two_dvd_two_pow (show 1 ≤ (2 * s) % d by omega)
    have hsplit : 2 ^ ((2 * s) % d) * (2 ^ d * H + 1)
        = 2 * (j * (2 ^ d * H + 1)) := by rw [hj]; ring
    rw [if_neg hdvd]
    omega

/-- The mod-`4` refinement.  The weight is `≡ 1` when `d ∣ 2*s`, `≡ 2` when
`d ∣ 2*s - 1`, and `≡ 0` otherwise. -/
theorem truncatedMersenneWeight_mod_four
    {s d : ℕ} (hd2 : 2 ≤ d) (hds : d ≤ 2 * s) :
    truncatedMersenneWeight s d % 4 =
      (if (2 * s) % d = 0 then 1 else if (2 * s) % d = 1 then 2 else 0) := by
  obtain ⟨H, hH⟩ := truncatedMersenneWeight_eq_twoPow_mul_geom hd2 hds
  obtain ⟨k, hk⟩ := four_dvd_two_pow hd2
  have hkH : 2 ^ d * H = 4 * (k * H) := by rw [hk]; ring
  rcases Nat.lt_or_ge ((2 * s) % d) 2 with hr | hr
  · rcases Nat.lt_or_ge ((2 * s) % d) 1 with hr0 | hr1
    · have h0 : (2 * s) % d = 0 := by omega
      rw [h0, pow_zero, one_mul] at hH
      rw [if_pos h0]
      omega
    · have h1 : (2 * s) % d = 1 := by omega
      rw [h1, pow_one] at hH
      rw [if_neg (by omega : ¬ (2 * s) % d = 0), if_pos h1]
      omega
  · obtain ⟨j, hj⟩ := four_dvd_two_pow hr
    have hsplit : 2 ^ ((2 * s) % d) * (2 ^ d * H + 1)
        = 4 * (j * (2 ^ d * H + 1)) := by rw [hj]; ring
    rw [if_neg (by omega : ¬ (2 * s) % d = 0),
      if_neg (by omega : ¬ (2 * s) % d = 1)]
    omega

/-- Rank `2` always carries an odd weight: `2 ∣ 2 * s` for every `s`. -/
theorem truncatedMersenneWeight_two_mod_two {s : ℕ} (hs : 1 ≤ s) :
    truncatedMersenneWeight s 2 % 2 = 1 := by
  rw [truncatedMersenneWeight_mod_two (le_refl 2) (by omega), if_pos ⟨s, rfl⟩]

/-! ## 2. The parity law for the concrete integer seam greedy -/

/-- The selected weight sum and the greedy remainder add up to the target. -/
theorem wordWeightSum_add_seamIntegerGreedyRemainder {s : ℕ} (hs : 2 ≤ s) :
    wordWeightSum s (seamGreedyWord s).toNatWord + seamIntegerGreedyRemainder s
      = seamSubsetTarget s := by
  have hadm := integerGreedyBits_admissible (seamWeights s) (seamSubsetTarget s)
  have heq : weightedBoolSum (seamWeights s)
      (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
      = wordWeightSum s (seamGreedyWord s).toNatWord := by
    rw [← seamGreedyWord_toList s, weightedBoolSum_toList_eq_wordWeightSum hs]
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  omega

/-- The seam subset target is even. -/
theorem seamSubsetTarget_mod_two {s : ℕ} (hs : 1 ≤ s) :
    seamSubsetTarget s % 2 = 0 := by
  unfold seamSubsetTarget
  have hle : (2 : ℕ) ^ s ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨a, ha⟩ := two_dvd_two_pow (show 1 ≤ 2 * s - 1 by omega)
  obtain ⟨b, hb⟩ := two_dvd_two_pow (show 1 ≤ s by omega)
  omega

/-- **The support parity law.**  Modulo two, the selected weight sum counts the
selected ranks that divide `2 * s`. -/
theorem sum_seamWordSupport_mod_two {s : ℕ} (hs : 1 ≤ s)
    (b : SeamRowWord s) :
    (∑ d ∈ seamWordSupport b, truncatedMersenneWeight s d) % 2 =
      ((seamWordSupport b).filter (fun d => d ∣ 2 * s)).card % 2 := by
  have hstep : ∀ d ∈ seamWordSupport b,
      truncatedMersenneWeight s d % 2 = (if d ∣ 2 * s then 1 else 0) := by
    intro d hd
    obtain ⟨hd2, hds⟩ := seamWordSupport_below hd
    exact truncatedMersenneWeight_mod_two hd2 (by omega)
  calc (∑ d ∈ seamWordSupport b, truncatedMersenneWeight s d) % 2
      = (∑ d ∈ seamWordSupport b, truncatedMersenneWeight s d % 2) % 2 :=
        Finset.sum_nat_mod _ _ _
    _ = (∑ d ∈ seamWordSupport b, (if d ∣ 2 * s then 1 else 0)) % 2 := by
        rw [Finset.sum_congr rfl hstep]
    _ = ((seamWordSupport b).filter (fun d => d ∣ 2 * s)).card % 2 := by
        rw [Finset.card_filter]

/-- **The remainder parity law.**  The concrete integer seam greedy remainder is
congruent modulo two to the number of selected ranks dividing `2 * s`. -/
theorem seamIntegerGreedyRemainder_mod_two {s : ℕ} (hs : 2 ≤ s) :
    seamIntegerGreedyRemainder s % 2 =
      ((seamWordSupport (seamGreedyWord s)).filter (fun d => d ∣ 2 * s)).card % 2 := by
  have hsum := wordWeightSum_add_seamIntegerGreedyRemainder hs
  have hword := wordWeightSum_eq_sum_seamWordSupport (seamGreedyWord s)
  have hpar := sum_seamWordSupport_mod_two (by omega : 1 ≤ s) (seamGreedyWord s)
  have htar := seamSubsetTarget_mod_two (by omega : 1 ≤ s)
  rw [hword] at hsum
  omega

/-! ## 3. Prime rows: the remainder is odd -/

/-- A rank strictly below a **prime** row that divides `2 * s` is `2`. -/
theorem eq_two_of_dvd_two_mul_of_prime {s d : ℕ} (hp : Nat.Prime s)
    (hd2 : 2 ≤ d) (hds : d < s) (hdvd : d ∣ 2 * s) : d = 2 := by
  have hnot : ¬ s ∣ d := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have hcop : Nat.Coprime d s := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnot).symm
  have hdvd2 : d ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd2
  omega

/-- On a prime row the selected ranks dividing `2 * s` are exactly `{2}`. -/
theorem divisorSelected_prime {s : ℕ} (hs : 13 ≤ s) (hp : Nat.Prime s) :
    (seamWordSupport (seamGreedyWord s)).filter (fun d => d ∣ 2 * s) = {2} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · exact Finset.mem_filter.mpr
      ⟨(two_three_six_mem_seamGreedySupport s hs).1, ⟨s, rfl⟩⟩
  · intro d hd
    obtain ⟨hdmem, hdvd⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd2, hds⟩ := seamWordSupport_below hdmem
    exact eq_two_of_dvd_two_mul_of_prime hp hd2 hds hdvd

/-- **Prime rows have an odd greedy remainder.**  Unconditional. -/
theorem seamIntegerGreedyRemainder_odd_of_prime {s : ℕ} (hs : 13 ≤ s)
    (hp : Nat.Prime s) : seamIntegerGreedyRemainder s % 2 = 1 := by
  rw [seamIntegerGreedyRemainder_mod_two (by omega), divisorSelected_prime hs hp]
  simp

/-- On a prime row the greedy remainder is not `2 ^ s + 2`, so the landing
excess of a hypothetical `-2` final middle cell cannot occur there. -/
theorem seamExcess_ne_two_of_prime {s : ℕ} (hs : 13 ≤ s) (hp : Nat.Prime s) :
    Recon257.seamExcess s ≠ 2 := by
  intro hexc
  have hR : seamIntegerGreedyRemainder s = 2 ^ s + 2 := by
    unfold Recon257.seamExcess at hexc
    have hz : ((seamIntegerGreedyRemainder s : ℕ) : ℤ) = (((2 ^ s + 2 : ℕ)) : ℤ) := by
      push_cast
      push_cast at hexc
      omega
    exact_mod_cast hz
  have hodd := seamIntegerGreedyRemainder_odd_of_prime hs hp
  obtain ⟨k, hk⟩ := two_dvd_two_pow (show 1 ≤ s by omega)
  omega

/-- The same for the dyadic half point itself: on a prime row the remainder is
never `2 ^ s`, i.e. the excess never vanishes. -/
theorem seamExcess_ne_zero_of_prime {s : ℕ} (hs : 13 ≤ s) (hp : Nat.Prime s) :
    Recon257.seamExcess s ≠ 0 := by
  intro hexc
  have hR : seamIntegerGreedyRemainder s = 2 ^ s := by
    unfold Recon257.seamExcess at hexc
    have hz : ((seamIntegerGreedyRemainder s : ℕ) : ℤ) = (((2 ^ s : ℕ)) : ℤ) := by
      push_cast
      push_cast at hexc
      omega
    exact_mod_cast hz
  have hodd := seamIntegerGreedyRemainder_odd_of_prime hs hp
  obtain ⟨k, hk⟩ := two_dvd_two_pow (show 1 ≤ s by omega)
  omega

/-- **The unconditional exclusion.**  A hypothetical final middle cell of charge
`-2` at rank `D` is impossible whenever `D + 1` is prime.  There is no tail
hypothesis: neither `hright` nor `hcof` nor any bound `S` appears.  Compare
`SkipD1.exists_bound_allRight_landingExcess_two_impossible`, which needs both an
all-right tail and an ineffective bound. -/
theorem finalMiddleCell_neg_two_impossible_of_prime_succ
    (D : ℕ) (hD : 12 ≤ D) (hp : Nat.Prime (D + 1))
    (hncarry : ¬ (seamAdjacentCut D (by omega : 5 ≤ D)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega : 5 ≤ D)).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse <
          (seamAdjacentCut D (by omega : 5 ≤ D)).terminalWeight)
    (hcell :
      4 * ((seamAdjacentCut D (by omega : 5 ≤ D)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse : ℤ) - 4 = -2) :
    False :=
  seamExcess_ne_two_of_prime (by omega) hp
    (Recon257.seamExcess_landing_eq_two D (by omega) hncarry hmiddle hcell)

/-! ## 4. The sharp negative: the two-adic shadow cannot see the late zone -/

/-- Every rank strictly below the row that divides `2 * s` sits at or below two
thirds of the row.  So no divisor of `2 * s` is ever *late*. -/
theorem dvd_two_mul_not_late {s d : ℕ} (_hd2 : 2 ≤ d) (hds : d < s)
    (hdvd : d ∣ 2 * s) : 3 * d ≤ 2 * s := by
  obtain ⟨c, hc⟩ := hdvd
  have hlow : d * 2 < d * c := by
    calc d * 2 = 2 * d := by ring
      _ < 2 * s := by omega
      _ = d * c := hc
  have hc3 : 2 < c := Nat.lt_of_mul_lt_mul_left hlow
  have : 3 * d ≤ c * d := Nat.mul_le_mul_right d (by omega)
  calc 3 * d ≤ c * d := this
    _ = d * c := by ring
    _ = 2 * s := hc.symm

/-- The only divisor of `2 * s` that reaches the half zone at all is the
cofactor-`3` rank, which sits exactly on the two-thirds boundary. -/
theorem dvd_two_mul_half_eq_cofThree {s d : ℕ} (_hd2 : 2 ≤ d) (hds : d < s)
    (hhalf : s < 2 * d) (hdvd : d ∣ 2 * s) : 3 * d = 2 * s := by
  obtain ⟨c, hc⟩ := hdvd
  have hlow : d * 2 < d * c := by
    calc d * 2 = 2 * d := by ring
      _ < 2 * s := by omega
      _ = d * c := hc
  have hhigh : d * c < d * 4 := by
    calc d * c = 2 * s := hc.symm
      _ < 4 * d := by omega
      _ = d * 4 := by ring
  have hc3 : 2 < c := Nat.lt_of_mul_lt_mul_left hlow
  have hc4 : c < 4 := Nat.lt_of_mul_lt_mul_left hhigh
  have hc3' : c = 3 := by omega
  subst hc3'
  omega

/-- The same for `2 * s - 1`, the ranks the mod-`4` shadow can see. -/
theorem dvd_two_mul_sub_one_not_late {s d : ℕ} (hs : 1 ≤ s) (_hd2 : 2 ≤ d)
    (hds : d < s) (hdvd : d ∣ 2 * s - 1) : 3 * d ≤ 2 * s := by
  obtain ⟨c, hc⟩ := hdvd
  have hlow : d * 2 < d * c := by
    calc d * 2 = 2 * d := by ring
      _ < 2 * s - 1 := by omega
      _ = d * c := hc
  have hc3 : 2 < c := Nat.lt_of_mul_lt_mul_left hlow
  have hle : 3 * d ≤ c * d := Nat.mul_le_mul_right d (by omega)
  have : c * d = 2 * s - 1 := by rw [mul_comm]; omega
  omega

/-- **Late weights are divisible by four.**  In the late zone the weight has two
power terms `2 ^ (2s-d) + 4 ^ (s-d)`, both of which are multiples of `4`. -/
theorem four_dvd_truncatedMersenneWeight_of_late {s d : ℕ}
    (hd2 : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d) :
    4 ∣ truncatedMersenneWeight s d := by
  rw [truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank hd2 hds hlate]
  refine Nat.dvd_add ?_ ?_
  · obtain ⟨t, ht⟩ := four_dvd_two_pow (show 2 ≤ 2 * s - d by omega)
    exact ⟨t, ht⟩
  · exact dvd_pow_self 4 (by omega)

/-- Sharper: in the late zone the entire low half of the weight is the single
power `4 ^ (s - d)`. -/
theorem truncatedMersenneWeight_mod_twoPow_of_late {s d : ℕ}
    (hd2 : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d) :
    truncatedMersenneWeight s d % 2 ^ (s + 1) = 4 ^ (s - d) := by
  rw [truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank hd2 hds hlate]
  have hsplit : (2 : ℕ) ^ (2 * s - d) = 2 ^ (s + 1) * 2 ^ (s - d - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hsmall : (4 : ℕ) ^ (s - d) < 2 ^ (s + 1) := by
    have h4 : (4 : ℕ) ^ (s - d) = 2 ^ (2 * (s - d)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [h4]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [hsplit, Nat.mul_add_mod, Nat.mod_eq_of_lt hsmall]

/-- The block of ranks above a late largest false rank contributes nothing
modulo four. -/
theorem four_dvd_lateBlock {s d₀ : ℕ} (hlate : 2 * s < 3 * d₀) :
    4 ∣ ∑ d ∈ Finset.Ico (d₀ + 1) s, truncatedMersenneWeight s d := by
  refine Finset.dvd_sum (fun d hd => ?_)
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hd
  exact four_dvd_truncatedMersenneWeight_of_late (by omega) h2 (by omega)

/-- **The blindness statement.**  Two different late largest false ranks give
exactly the same mod-`4` block contribution, namely `0`. -/
theorem lateBlock_mod_four_indep {s d₀ d₁ : ℕ}
    (h0 : 2 * s < 3 * d₀) (h1 : 2 * s < 3 * d₁) :
    (∑ d ∈ Finset.Ico (d₀ + 1) s, truncatedMersenneWeight s d) % 4 =
      (∑ d ∈ Finset.Ico (d₁ + 1) s, truncatedMersenneWeight s d) % 4 := by
  obtain ⟨a, ha⟩ := four_dvd_lateBlock h0
  obtain ⟨b, hb⟩ := four_dvd_lateBlock h1
  omega

/-- **The mod-`4` shadow of the landing equation lives below two thirds.**  If
the row has a late largest false rank then the mod-`4` residue of the selected
weight sum equals that of the lower prefix alone. -/
theorem sum_seamWordSupport_mod_four_of_late
    {s d₀ : ℕ} {u : Finset ℕ} (_hd2 : 2 ≤ d₀) (_hds : d₀ < s)
    (hlate : 2 * s < 3 * d₀)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d₀)
    (hsupp : seamWordSupport (seamGreedyWord s) = u ∪ Finset.Ico (d₀ + 1) s) :
    (∑ d ∈ seamWordSupport (seamGreedyWord s), truncatedMersenneWeight s d) % 4 =
      (∑ d ∈ u, truncatedMersenneWeight s d) % 4 := by
  classical
  have hdisj : Disjoint u (Finset.Ico (d₀ + 1) s) := by
    refine Finset.disjoint_left.mpr (fun e heu hei => ?_)
    have h1 := hu e heu
    have h2 := Finset.mem_Ico.mp hei
    omega
  rw [hsupp, Finset.sum_union hdisj]
  obtain ⟨a, ha⟩ := four_dvd_lateBlock hlate
  omega

/-- Packaged for the D1 target.  Under `IsLargestFalseRank … d₀` with `d₀` late,
the mod-`4` content of `seamExcess (D+1) = 2` is a statement about ranks below
`d₀` only, so it cannot refute the lateness of `d₀`. -/
theorem exists_lowerPrefix_sum_mod_four_of_largestSkipLate
    {s d₀ : ℕ} (hd2 : 2 ≤ d₀) (hds : d₀ < s)
    (hmax : IsLargestFalseRank (seamGreedyWord s) d₀)
    (hlate : 2 * s < 3 * d₀) :
    ∃ u : Finset ℕ, (∀ e ∈ u, 2 ≤ e ∧ e < d₀) ∧
      (∑ d ∈ seamWordSupport (seamGreedyWord s), truncatedMersenneWeight s d) % 4 =
        (∑ d ∈ u, truncatedMersenneWeight s d) % 4 := by
  obtain ⟨u, hu, hsupp⟩ :=
    (isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix
      (seamGreedyWord s) hd2 hds).mp hmax
  exact ⟨u, hu, sum_seamWordSupport_mod_four_of_late hd2 hds hlate hu hsupp⟩

/-
## Axiom audit

Every theorem in this file was checked with `#print axioms`; each depends only
on `[propext, Classical.choice, Quot.sound]`.  The `#print` lines are left
commented so that `lake env lean ErdosProblems/Half/H3.lean` exits `0` with
empty output; uncomment to reproduce.

-- #print axioms geometricCore_eq_twoPow_mul_add_one
-- #print axioms truncatedMersenneWeight_eq_twoPow_mul_geom
-- #print axioms truncatedMersenneWeight_mod_two
-- #print axioms truncatedMersenneWeight_mod_four
-- #print axioms wordWeightSum_add_seamIntegerGreedyRemainder
-- #print axioms seamSubsetTarget_mod_two
-- #print axioms sum_seamWordSupport_mod_two
-- #print axioms seamIntegerGreedyRemainder_mod_two
-- #print axioms eq_two_of_dvd_two_mul_of_prime
-- #print axioms divisorSelected_prime
-- #print axioms seamIntegerGreedyRemainder_odd_of_prime
-- #print axioms seamExcess_ne_two_of_prime
-- #print axioms seamExcess_ne_zero_of_prime
-- #print axioms finalMiddleCell_neg_two_impossible_of_prime_succ
-- #print axioms dvd_two_mul_not_late
-- #print axioms dvd_two_mul_half_eq_cofThree
-- #print axioms dvd_two_mul_sub_one_not_late
-- #print axioms four_dvd_truncatedMersenneWeight_of_late
-- #print axioms truncatedMersenneWeight_mod_twoPow_of_late
-- #print axioms four_dvd_lateBlock
-- #print axioms lateBlock_mod_four_indep
-- #print axioms sum_seamWordSupport_mod_four_of_late
-- #print axioms exists_lowerPrefix_sum_mod_four_of_largestSkipLate
-/

end HalfH3

end Erdos249257
