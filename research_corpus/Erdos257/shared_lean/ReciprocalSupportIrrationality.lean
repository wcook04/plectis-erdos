import Erdos257PeriodNoncollapse.RationalSupportCarrySkeleton
import Erdos257PeriodNoncollapse.MersenneTailAtoms
import Erdos257PeriodNoncollapse.CarrySurvivorExtinction

/-!
# Reciprocal-summable support irrationality

This module develops the shifted-atom description of binary support tails.
-/

namespace Erdos257PeriodNoncollapse

open Filter Set
open TotientTailPeriodKiller

noncomputable section

/-- The contribution of support rank `d` to the binary coefficient tail at
shift `N`.  Rank zero is normalized to zero, consistently with
`erdosSupportSeries`. -/
noncomputable def shiftedMersenneAtom (N d : ℕ) : ℝ :=
  if d = 0 then 0
  else (2 : ℝ) ^ (N % d) / ((2 : ℝ) ^ d - 1)

/-- The shifted atom restricted to a support set. -/
noncomputable def shiftedSupportAtom (A : Set ℕ) (N d : ℕ) : ℝ :=
  Set.indicator A (shiftedMersenneAtom N) d

theorem shiftedMersenneAtom_nonneg (N d : ℕ) :
    0 ≤ shiftedMersenneAtom N d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedMersenneAtom]
  · rw [shiftedMersenneAtom, if_neg hd.ne']
    have hden : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
      have : (1 : ℝ) < (2 : ℝ) ^ d := one_lt_pow₀ (by norm_num) hd.ne'
      linarith
    positivity

theorem shiftedMersenneAtom_zero (d : ℕ) :
    shiftedMersenneAtom 0 d = (1 : ℝ) / ((2 : ℝ) ^ d - 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedMersenneAtom]
  · simp [shiftedMersenneAtom, hd.ne']

/-! ## GCD orbit means -/

/-- The exact mean of the `d`-atom sampled along positive multiples of `Q`.
The conductor-zero branch matches the normalization of
`shiftedMersenneAtom`. -/
noncomputable def shiftedMersenneOrbitMean (Q d : ℕ) : ℝ :=
  if d = 0 then 0
  else (Nat.gcd Q d : ℝ) /
    ((d : ℝ) * ((2 : ℝ) ^ Nat.gcd Q d - 1))

/-- The GCD orbit mean restricted to a support set. -/
noncomputable def shiftedSupportOrbitMean (A : Set ℕ) (Q d : ℕ) : ℝ :=
  Set.indicator A (shiftedMersenneOrbitMean Q) d

theorem shiftedMersenneOrbitMean_nonneg (Q d : ℕ) :
    0 ≤ shiftedMersenneOrbitMean Q d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedMersenneOrbitMean]
  · rw [shiftedMersenneOrbitMean, if_neg hd.ne']
    have hg : 0 < Nat.gcd Q d := Nat.gcd_pos_of_pos_right Q hd
    have hden : (0 : ℝ) < (2 : ℝ) ^ Nat.gcd Q d - 1 := by
      have : (1 : ℝ) < (2 : ℝ) ^ Nat.gcd Q d :=
        one_lt_pow₀ (by norm_num) hg.ne'
      linarith
    positivity

/-- Every GCD orbit mean is bounded by the reciprocal conductor.  This is
the `Q`-independent majorant used in the outer LCM-prefix limit. -/
theorem shiftedMersenneOrbitMean_le_reciprocal (Q d : ℕ) :
    shiftedMersenneOrbitMean Q d ≤ (1 : ℝ) / (d : ℝ) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedMersenneOrbitMean]
  · rw [shiftedMersenneOrbitMean, if_neg hd.ne']
    let g := Nat.gcd Q d
    have hg : 0 < g := Nat.gcd_pos_of_pos_right Q hd
    have hden : (0 : ℝ) < (2 : ℝ) ^ g - 1 := by
      have : (1 : ℝ) < (2 : ℝ) ^ g :=
        one_lt_pow₀ (by norm_num) hg.ne'
      linarith
    have haddOnePow : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
          rw [pow_succ]
          omega
    have hgpowNat : g ≤ 2 ^ g - 1 :=
      Nat.le_sub_of_add_le (haddOnePow g)
    have hgpow : (g : ℝ) ≤ (2 : ℝ) ^ g - 1 := by
      have hcast : (g : ℝ) ≤ ((2 ^ g - 1 : ℕ) : ℝ) := by
        exact_mod_cast hgpowNat
      rw [Nat.cast_sub Nat.one_le_two_pow] at hcast
      norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hcast
      exact hcast
    have hratio : (g : ℝ) / ((2 : ℝ) ^ g - 1) ≤ 1 :=
      (div_le_one hden).2 hgpow
    change (g : ℝ) /
        ((d : ℝ) * ((2 : ℝ) ^ g - 1)) ≤ (1 : ℝ) / (d : ℝ)
    calc
      (g : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ g - 1)) =
          ((g : ℝ) / ((2 : ℝ) ^ g - 1)) * (1 / (d : ℝ)) := by
            field_simp
      _ ≤ 1 * (1 / (d : ℝ)) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = (1 : ℝ) / (d : ℝ) := one_mul _

theorem shiftedSupportOrbitMean_nonneg (A : Set ℕ) (Q d : ℕ) :
    0 ≤ shiftedSupportOrbitMean A Q d :=
  Set.indicator_nonneg
    (fun k _ => shiftedMersenneOrbitMean_nonneg Q k) d

theorem shiftedSupportOrbitMean_le_reciprocalSupportTerm
    (A : Set ℕ) (Q d : ℕ) :
    shiftedSupportOrbitMean A Q d ≤ reciprocalSupportTerm A d := by
  classical
  by_cases hdA : d ∈ A
  · simpa [shiftedSupportOrbitMean, reciprocalSupportTerm, hdA] using
      shiftedMersenneOrbitMean_le_reciprocal Q d
  · simp [shiftedSupportOrbitMean, reciprocalSupportTerm, hdA]

theorem norm_shiftedSupportOrbitMean_le_reciprocalSupportTerm
    (A : Set ℕ) (Q d : ℕ) :
    ‖shiftedSupportOrbitMean A Q d‖ ≤ reciprocalSupportTerm A d := by
  rw [Real.norm_eq_abs, abs_of_nonneg (shiftedSupportOrbitMean_nonneg A Q d)]
  exact shiftedSupportOrbitMean_le_reciprocalSupportTerm A Q d

/-- When the conductor divides the sampling step, its orbit is frozen at the
zero-shift atom. -/
theorem shiftedMersenneOrbitMean_eq_zero_of_dvd
    (Q d : ℕ) (hd : 0 < d) (hdiv : d ∣ Q) :
    shiftedMersenneOrbitMean Q d = shiftedMersenneAtom 0 d := by
  have hgcd : Nat.gcd Q d = d := Nat.gcd_eq_right_iff_dvd.mpr hdiv
  rw [shiftedMersenneOrbitMean, if_neg hd.ne', hgcd,
    shiftedMersenneAtom_zero]
  have hdne : (d : ℝ) ≠ 0 := by positivity
  field_simp

theorem shiftedSupportOrbitMean_eq_zero_of_dvd
    (A : Set ℕ) (Q d : ℕ) (hd : 0 < d) (hdiv : d ∣ Q) :
    shiftedSupportOrbitMean A Q d = shiftedSupportAtom A 0 d := by
  classical
  by_cases hdA : d ∈ A
  · simpa [shiftedSupportOrbitMean, shiftedSupportAtom, hdA] using
      shiftedMersenneOrbitMean_eq_zero_of_dvd Q d hd hdiv
  · simp [shiftedSupportOrbitMean, shiftedSupportAtom, hdA]

/-- One complete GCD orbit of positive `Q`-multiples has the exact geometric
atom mass `1 / (2^g - 1)`, where `g = gcd Q d`. -/
theorem sum_shiftedMersenneAtom_gcdOrbit
    (Q d : ℕ) (hQ : 0 < Q) (hd : 0 < d) :
    ∑ k ∈ Finset.range (d / Nat.gcd Q d),
        shiftedMersenneAtom ((k + 1) * Q) d =
      (1 : ℝ) / ((2 : ℝ) ^ Nat.gcd Q d - 1) := by
  classical
  let g := Nat.gcd Q d
  let q := Q / g
  let h := d / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hQ
  have hgQ : g ∣ Q := Nat.gcd_dvd_left Q d
  have hgd : g ∣ d := Nat.gcd_dvd_right Q d
  have hQfac : g * q = Q := by
    exact Nat.mul_div_cancel' hgQ
  have hdfac : g * h = d := by
    exact Nat.mul_div_cancel' hgd
  have hh : 0 < h := by
    exact Nat.div_pos (Nat.gcd_le_right Q hd) hg
  have hcop : Nat.Coprime q h := by
    exact Nat.coprime_div_gcd_div_gcd hg
  let e : Fin h → Fin h := fun j =>
    ⟨((j : ℕ) + 1) * q % h, Nat.mod_lt _ hh⟩
  have heinj : Function.Injective e := by
    intro a b hab
    have habval : (e a : ℕ) = (e b : ℕ) := congrArg Fin.val hab
    have hmod : ((a : ℕ) + 1) * q ≡ ((b : ℕ) + 1) * q [MOD h] := by
      exact habval
    have hcancel : (a : ℕ) + 1 ≡ (b : ℕ) + 1 [MOD h] :=
      Nat.ModEq.cancel_right_of_coprime hcop.symm.gcd_eq_one hmod
    have habmod : (a : ℕ) ≡ (b : ℕ) [MOD h] := by
      have hcancel' : 1 + (a : ℕ) ≡ 1 + (b : ℕ) [MOD h] := by
        simpa [add_comm] using hcancel
      exact hcancel'.add_left_cancel' 1
    exact Fin.ext (habmod.eq_of_lt_of_lt a.isLt b.isLt)
  have hebij : Function.Bijective e :=
    (Fintype.bijective_iff_injective_and_card e).2 ⟨heinj, rfl⟩
  have hresidue : ∀ j : Fin h,
      (((j : ℕ) + 1) * Q) % d = g * (e j : ℕ) := by
    intro j
    rw [← hQfac, ← hdfac]
    rw [show ((j : ℕ) + 1) * (g * q) =
        g * (((j : ℕ) + 1) * q) by ring]
    rw [Nat.mul_mod_mul_left]
  have hsumPerm :
      (∑ j : Fin h, (2 : ℝ) ^ ((((j : ℕ) + 1) * Q) % d)) =
        ∑ r : Fin h, (2 : ℝ) ^ (g * (r : ℕ)) := by
    apply Fintype.sum_bijective e hebij
    intro j
    rw [hresidue]
  have hpowg : (2 : ℝ) ^ g ≠ 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ g :=
      one_lt_pow₀ (by norm_num) hg.ne'
    linarith
  have hdenD : (2 : ℝ) ^ d - 1 ≠ 0 := by
    have : (1 : ℝ) < (2 : ℝ) ^ d :=
      one_lt_pow₀ (by norm_num) hd.ne'
    linarith
  have hdenG : (2 : ℝ) ^ g - 1 ≠ 0 := sub_ne_zero.mpr hpowg
  calc
    ∑ k ∈ Finset.range (d / Nat.gcd Q d),
        shiftedMersenneAtom ((k + 1) * Q) d =
        (∑ j : Fin h, (2 : ℝ) ^ ((((j : ℕ) + 1) * Q) % d)) /
          ((2 : ℝ) ^ d - 1) := by
            rw [show d / Nat.gcd Q d = h from rfl,
              ← Fin.sum_univ_eq_sum_range]
            simp only [shiftedMersenneAtom, if_neg hd.ne', Finset.sum_div]
    _ = (∑ r : Fin h, (2 : ℝ) ^ (g * (r : ℕ))) /
          ((2 : ℝ) ^ d - 1) := by rw [hsumPerm]
    _ = (∑ r ∈ Finset.range h, ((2 : ℝ) ^ g) ^ r) /
          ((2 : ℝ) ^ d - 1) := by
            rw [← Fin.sum_univ_eq_sum_range]
            apply congrArg (fun z : ℝ => z / ((2 : ℝ) ^ d - 1))
            apply Fintype.sum_congr
            intro r
            rw [pow_mul]
    _ = (((2 : ℝ) ^ g) ^ h - 1) /
          ((2 : ℝ) ^ g - 1) / ((2 : ℝ) ^ d - 1) := by
            rw [geom_sum_eq hpowg]
    _ = (1 : ℝ) / ((2 : ℝ) ^ Nat.gcd Q d - 1) := by
      change (((2 : ℝ) ^ g) ^ h - 1) /
          ((2 : ℝ) ^ g - 1) / ((2 : ℝ) ^ d - 1) =
        (1 : ℝ) / ((2 : ℝ) ^ g - 1)
      rw [← pow_mul, hdfac]
      field_simp

/-- Every aligned block of length `d / gcd Q d` is the same complete GCD
orbit. -/
theorem sum_shiftedMersenneAtom_gcdOrbit_block
    (Q d : ℕ) (hQ : 0 < Q) (hd : 0 < d) (b : ℕ) :
    ∑ j ∈ Finset.range (d / Nat.gcd Q d),
        shiftedMersenneAtom
          ((b * (d / Nat.gcd Q d) + j + 1) * Q) d =
      (1 : ℝ) / ((2 : ℝ) ^ Nat.gcd Q d - 1) := by
  let g := Nat.gcd Q d
  let q := Q / g
  let h := d / g
  have hgQ : g ∣ Q := Nat.gcd_dvd_left Q d
  have hgd : g ∣ d := Nat.gcd_dvd_right Q d
  have hQfac : g * q = Q := Nat.mul_div_cancel' hgQ
  have hdfac : g * h = d := Nat.mul_div_cancel' hgd
  have hperiod : d ∣ h * Q := by
    refine ⟨q, ?_⟩
    rw [← hdfac, ← hQfac]
    ring
  calc
    ∑ j ∈ Finset.range (d / Nat.gcd Q d),
        shiftedMersenneAtom
          ((b * (d / Nat.gcd Q d) + j + 1) * Q) d =
        ∑ j ∈ Finset.range (d / Nat.gcd Q d),
          shiftedMersenneAtom ((j + 1) * Q) d := by
            apply Finset.sum_congr rfl
            intro j _
            rw [shiftedMersenneAtom, if_neg hd.ne',
              shiftedMersenneAtom, if_neg hd.ne']
            apply congrArg (fun z : ℕ =>
              (2 : ℝ) ^ z / ((2 : ℝ) ^ d - 1))
            change
              ((b * h + j + 1) * Q) % d = ((j + 1) * Q) % d
            have hdecomp :
                (b * h + j + 1) * Q = b * (h * Q) + (j + 1) * Q := by
              ring
            have hbperiod : d ∣ b * (h * Q) :=
              dvd_mul_of_dvd_right hperiod b
            rw [hdecomp, Nat.add_mod,
              Nat.mod_eq_zero_of_dvd hbperiod, zero_add]
            exact Nat.mod_mod _ _
    _ = (1 : ℝ) / ((2 : ℝ) ^ Nat.gcd Q d - 1) :=
      sum_shiftedMersenneAtom_gcdOrbit Q d hQ hd

theorem shiftedMersenneAtom_le_one (N d : ℕ) :
    shiftedMersenneAtom N d ≤ 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedMersenneAtom]
  · rw [shiftedMersenneAtom, if_neg hd.ne', div_le_one]
    · have hmod : N % d < d := Nat.mod_lt N hd
      have hpowlt : 2 ^ (N % d) < 2 ^ d :=
        Nat.pow_lt_pow_right (by norm_num) hmod
      have hpowle : 2 ^ (N % d) ≤ 2 ^ d - 1 := by omega
      have hcast : ((2 ^ (N % d) : ℕ) : ℝ) ≤
          ((2 ^ d - 1 : ℕ) : ℝ) := by
        exact_mod_cast hpowle
      rw [Nat.cast_sub Nat.one_le_two_pow] at hcast
      norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hcast
      exact hcast
    · have : (1 : ℝ) < (2 : ℝ) ^ d :=
        one_lt_pow₀ (by norm_num) hd.ne'
      linarith

/-- Sampling a positive Mersenne atom along positive `Q`-multiples has the
exact GCD-orbit Cesàro mean. -/
theorem tendsto_cesaroMean_shiftedMersenneAtom_mul
    (Q d : ℕ) (hQ : 0 < Q) (hd : 0 < d) :
    Tendsto
      (cesaroMean (fun k : ℕ => shiftedMersenneAtom ((k + 1) * Q) d))
      atTop (nhds (shiftedMersenneOrbitMean Q d)) := by
  let g := Nat.gcd Q d
  let h := d / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hQ
  have hgd : g ∣ d := Nat.gcd_dvd_right Q d
  have hdfac : g * h = d := Nat.mul_div_cancel' hgd
  have hh : 0 < h := Nat.div_pos (Nat.gcd_le_right Q hd) hg
  have hlim := tendsto_cesaroMean_of_constant_blocks
    (fun k : ℕ => shiftedMersenneAtom ((k + 1) * Q) d)
    h ((1 : ℝ) / ((2 : ℝ) ^ g - 1)) hh
    (fun k => shiftedMersenneAtom_nonneg ((k + 1) * Q) d)
    (fun k => shiftedMersenneAtom_le_one ((k + 1) * Q) d)
    (fun b => by
      simpa [g, h, add_assoc] using
        sum_shiftedMersenneAtom_gcdOrbit_block Q d hQ hd b)
  have hmean :
      (1 / ((2 : ℝ) ^ g - 1)) / (h : ℝ) =
        shiftedMersenneOrbitMean Q d := by
    rw [shiftedMersenneOrbitMean, if_neg hd.ne']
    change
      (1 / ((2 : ℝ) ^ g - 1)) / (h : ℝ) =
        (g : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ g - 1))
    have hgden : (2 : ℝ) ^ g - 1 ≠ 0 := by
      have : (1 : ℝ) < (2 : ℝ) ^ g :=
        one_lt_pow₀ (by norm_num) hg.ne'
      linarith
    have hhne : (h : ℝ) ≠ 0 := by positivity
    rw [← hdfac]
    push_cast
    field_simp
  rw [hmean] at hlim
  exact hlim

theorem sum_pow_positiveMultiples_le (Q K : ℕ) (hQ : 0 < Q) :
    ∑ k ∈ Finset.range K, 2 ^ ((k + 1) * Q) ≤ 2 ^ (K * Q + 1) - 1 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have hexp : K * Q + 1 ≤ (K + 1) * Q := by
        rw [Nat.add_mul]
        omega
      have hpow : 2 ^ (K * Q + 1) ≤ 2 ^ ((K + 1) * Q) :=
        Nat.pow_le_pow_right (by norm_num) hexp
      have hsucc : 2 ^ ((K + 1) * Q + 1) = 2 * 2 ^ ((K + 1) * Q) := by
        rw [pow_succ]
        ring
      omega

theorem blockRemainder_le_blockSum
    (x : ℕ → ℝ) (h : ℕ) (blockSum : ℝ) (hh : 0 < h)
    (hx0 : ∀ n : ℕ, 0 ≤ x n)
    (hblock : ∀ q : ℕ,
      ∑ j ∈ Finset.range h, x (q * h + j) = blockSum)
    (N : ℕ) :
    blockRemainder x h N ≤ blockSum := by
  rw [← hblock (N / h)]
  unfold blockRemainder
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.mod_lt N hh).le)
  intro j _ _
  exact hx0 ((N / h) * h + j)

/-- In the wrapped range, complete GCD-orbit blocks and the final prefix give
the sharp block-count upper bound. -/
theorem sum_shiftedMersenneAtom_mul_le_blockCount
    (Q d K : ℕ) (hQ : 0 < Q) (hd : 0 < d) :
    ∑ k ∈ Finset.range K, shiftedMersenneAtom ((k + 1) * Q) d ≤
      ((K / (d / Nat.gcd Q d) : ℕ) : ℝ) + 1 := by
  let g := Nat.gcd Q d
  let h := d / g
  let blockSum : ℝ := 1 / ((2 : ℝ) ^ g - 1)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hQ
  have hh : 0 < h := Nat.div_pos (Nat.gcd_le_right Q hd) hg
  have hblock : ∀ b : ℕ,
      ∑ j ∈ Finset.range h,
        shiftedMersenneAtom (((b * h + j) + 1) * Q) d = blockSum := by
    intro b
    simpa [g, h, blockSum, add_assoc] using
      sum_shiftedMersenneAtom_gcdOrbit_block Q d hQ hd b
  have hrem :
      blockRemainder (fun k => shiftedMersenneAtom ((k + 1) * Q) d) h K ≤
        blockSum :=
    blockRemainder_le_blockSum _ h blockSum hh
      (fun k => shiftedMersenneAtom_nonneg ((k + 1) * Q) d) hblock K
  have hsum := sum_range_eq_mul_blockSum_add_blockRemainder
    (fun k => shiftedMersenneAtom ((k + 1) * Q) d) h blockSum hblock K
  have hblock1 : blockSum ≤ 1 := by
    dsimp [blockSum]
    rw [div_le_one]
    · have hpowNat : g + 1 ≤ 2 ^ g := by
        induction g with
        | zero => simp
        | succ g ih => rw [pow_succ]; omega
      have hpow : (g : ℝ) + 1 ≤ (2 : ℝ) ^ g := by
        exact_mod_cast hpowNat
      have hgR : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
      linarith
    · have : (1 : ℝ) < (2 : ℝ) ^ g :=
        one_lt_pow₀ (by norm_num) hg.ne'
      linarith
  rw [hsum]
  calc
    ((K / h : ℕ) : ℝ) * blockSum +
        blockRemainder (fun k => shiftedMersenneAtom ((k + 1) * Q) d) h K ≤
        ((K / h : ℕ) : ℝ) * blockSum + blockSum :=
      by gcongr
    _ = (((K / h : ℕ) : ℝ) + 1) * blockSum := by ring
    _ ≤ (((K / h : ℕ) : ℝ) + 1) * 1 :=
      mul_le_mul_of_nonneg_left hblock1 (by positivity)
    _ = ((K / (d / Nat.gcd Q d) : ℕ) : ℝ) + 1 := by
      simp [h, g]

/-- Before the first wrap, the sampled numerator is a sparse subset of the
initial binary geometric sum; the remaining exponent gap controls its mass. -/
theorem sum_shiftedMersenneAtom_mul_le_inv_pow_gap_of_lt
    (Q d K : ℕ) (hQ : 0 < Q) (hd : 0 < d) (hnowrap : K * Q < d) :
    ∑ k ∈ Finset.range K, shiftedMersenneAtom ((k + 1) * Q) d ≤
      (1 : ℝ) / (2 : ℝ) ^ (d - K * Q - 1) := by
  let M := K * Q
  let t := d - M
  have ht : 0 < t := Nat.sub_pos_of_lt hnowrap
  have hden : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ d :=
      one_lt_pow₀ (by norm_num) hd.ne'
    linarith
  have hrewrite :
      ∑ k ∈ Finset.range K, shiftedMersenneAtom ((k + 1) * Q) d =
        (∑ k ∈ Finset.range K, (2 : ℝ) ^ ((k + 1) * Q)) /
          ((2 : ℝ) ^ d - 1) := by
    calc
      ∑ k ∈ Finset.range K, shiftedMersenneAtom ((k + 1) * Q) d =
          ∑ k ∈ Finset.range K,
            (2 : ℝ) ^ ((k + 1) * Q) / ((2 : ℝ) ^ d - 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hklt : (k + 1) * Q < d := by
          have hkK : k < K := Finset.mem_range.mp hk
          have : (k + 1) * Q ≤ K * Q :=
            Nat.mul_le_mul_right Q (by omega)
          omega
        rw [shiftedMersenneAtom, if_neg hd.ne', Nat.mod_eq_of_lt hklt]
      _ = (∑ k ∈ Finset.range K, (2 : ℝ) ^ ((k + 1) * Q)) /
          ((2 : ℝ) ^ d - 1) := by rw [Finset.sum_div]
  have hnumNat := sum_pow_positiveMultiples_le Q K hQ
  have hnum :
      (∑ k ∈ Finset.range K, (2 : ℝ) ^ ((k + 1) * Q)) ≤
        ((2 ^ (M + 1) - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnumNat
  have hpowEq :
      2 ^ (t - 1) * 2 ^ (M + 1) = 2 ^ d := by
    rw [← pow_add]
    congr 1
    dsimp [t, M]
    omega
  have hcrossNat :
      2 ^ (t - 1) * (2 ^ (M + 1) - 1) ≤ 2 ^ d - 1 := by
    rw [Nat.mul_sub_left_distrib, hpowEq]
    have hone : 0 < 2 ^ (t - 1) := by positivity
    omega
  have hcross :
      ((2 ^ (M + 1) - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (t - 1) ≤
        (2 : ℝ) ^ d - 1 := by
    have hc :
        ((2 ^ (t - 1) * (2 ^ (M + 1) - 1) : ℕ) : ℝ) ≤
          ((2 ^ d - 1 : ℕ) : ℝ) := by
      exact_mod_cast hcrossNat
    have hpowM : 1 ≤ 2 ^ (M + 1) := Nat.one_le_two_pow
    have hpowd : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    rw [Nat.cast_mul, Nat.cast_sub hpowM, Nat.cast_sub hpowd] at hc
    norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hc
    simpa [mul_comm] using hc
  rw [hrewrite]
  calc
    (∑ k ∈ Finset.range K, (2 : ℝ) ^ ((k + 1) * Q)) /
        ((2 : ℝ) ^ d - 1) ≤
        ((2 ^ (M + 1) - 1 : ℕ) : ℝ) / ((2 : ℝ) ^ d - 1) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (1 : ℝ) / (2 : ℝ) ^ (t - 1) := by
      rw [div_le_div_iff₀ hden (by positivity)]
      simpa [mul_comm] using hcross
    _ = (1 : ℝ) / (2 : ℝ) ^ (d - K * Q - 1) := by rfl

/-- A finite Cesàro mean along positive `Q`-multiples has a conductor
majorant independent of the averaging length.  Complete gcd-orbit blocks
control the wrapped range, while the initial geometric gap controls the
range before the first wrap. -/
theorem cesaroMean_shiftedMersenneAtom_mul_le
    (Q d K : ℕ) (hQ : 0 < Q) (hK : 0 < K) :
    cesaroMean (fun k : ℕ => shiftedMersenneAtom ((k + 1) * Q) d) K ≤
      (2 * (Q + 1) : ℝ) / (d : ℝ) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [cesaroMean, shiftedMersenneAtom]
  · have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    unfold cesaroMean
    by_cases hnowrap : K * Q < d
    · let t := d - K * Q
      have ht : 0 < t := Nat.sub_pos_of_lt hnowrap
      have htPowNat : t ≤ 2 ^ (t - 1) := by
        have haddOnePow : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
          intro n
          induction n with
          | zero => norm_num
          | succ n ih => rw [pow_succ]; omega
        have h := haddOnePow (t - 1)
        omega
      have htPow : (t : ℝ) ≤ (2 : ℝ) ^ (t - 1) := by
        exact_mod_cast htPowNat
      have hsum :=
        sum_shiftedMersenneAtom_mul_le_inv_pow_gap_of_lt
          Q d K hQ hd hnowrap
      have hsumt :
          ∑ k ∈ Finset.range K,
              shiftedMersenneAtom ((k + 1) * Q) d ≤ (1 : ℝ) / (t : ℝ) := by
        calc
          ∑ k ∈ Finset.range K,
              shiftedMersenneAtom ((k + 1) * Q) d ≤
              (1 : ℝ) / (2 : ℝ) ^ (t - 1) := by simpa [t] using hsum
          _ ≤ (1 : ℝ) / (t : ℝ) :=
            one_div_le_one_div_of_le (by positivity) htPow
      have hddecomp : d = K * Q + t := by
        dsimp [t]
        omega
      have hfirst : K * Q ≤ K * t * Q := by
        calc
          K * Q = (K * Q) * 1 := by ring
          _ ≤ (K * Q) * t := Nat.mul_le_mul_left _ ht
          _ = K * t * Q := by ring
      have hsecond : t ≤ K * t := by
        calc
          t = 1 * t := by simp
          _ ≤ K * t := Nat.mul_le_mul_right t hK
      have hdmajorNat : d ≤ K * t * (Q + 1) := by
        rw [hddecomp]
        calc
          K * Q + t ≤ K * t * Q + K * t := Nat.add_le_add hfirst hsecond
          _ = K * t * (Q + 1) := by ring
      have hdmajor :
          (d : ℝ) ≤ (K : ℝ) * (t : ℝ) * ((Q : ℝ) + 1) := by
        exact_mod_cast hdmajorNat
      calc
        (∑ k ∈ Finset.range K,
            shiftedMersenneAtom ((k + 1) * Q) d) / (K : ℝ) ≤
            ((1 : ℝ) / (t : ℝ)) / (K : ℝ) :=
          div_le_div_of_nonneg_right hsumt hKR.le
        _ = (1 : ℝ) / ((K : ℝ) * (t : ℝ)) := by ring
        _ ≤ ((Q : ℝ) + 1) / (d : ℝ) := by
          rw [div_le_div_iff₀ (by positivity) hdR]
          simpa [mul_assoc, mul_left_comm, mul_comm] using hdmajor
        _ ≤ (2 * (Q + 1) : ℝ) / (d : ℝ) := by
          gcongr
          have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := by positivity
          linarith
    · have hdle : d ≤ K * Q := Nat.le_of_not_gt hnowrap
      let g := Nat.gcd Q d
      let h := d / g
      have hg : 0 < g := Nat.gcd_pos_of_pos_left d hQ
      have hh : 0 < h := Nat.div_pos (Nat.gcd_le_right Q hd) hg
      have hgd : g ∣ d := Nat.gcd_dvd_right Q d
      have hdfac : g * h = d := Nat.mul_div_cancel' hgd
      have hgQ : g ≤ Q := Nat.gcd_le_left d hQ
      have hsum := sum_shiftedMersenneAtom_mul_le_blockCount Q d K hQ hd
      have hcastDiv : ((K / h : ℕ) : ℝ) ≤ (K : ℝ) / (h : ℝ) :=
        Nat.cast_div_le
      have hratioEq :
          (K : ℝ) / (h : ℝ) =
            (K : ℝ) * (g : ℝ) / (d : ℝ) := by
        rw [← hdfac]
        push_cast
        have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
        have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
        field_simp
      have hblockRatio :
          ((K / h : ℕ) : ℝ) ≤
            (K : ℝ) * (Q : ℝ) / (d : ℝ) := by
        calc
          ((K / h : ℕ) : ℝ) ≤ (K : ℝ) / (h : ℝ) := hcastDiv
          _ = (K : ℝ) * (g : ℝ) / (d : ℝ) := hratioEq
          _ ≤ (K : ℝ) * (Q : ℝ) / (d : ℝ) := by
            gcongr
      have honeK_le_Qd : (1 : ℝ) / (K : ℝ) ≤ (Q : ℝ) / (d : ℝ) := by
        rw [div_le_div_iff₀ hKR hdR]
        simpa [mul_comm] using (show (d : ℝ) ≤ (K : ℝ) * (Q : ℝ) by
          exact_mod_cast hdle)
      calc
        (∑ k ∈ Finset.range K,
            shiftedMersenneAtom ((k + 1) * Q) d) / (K : ℝ) ≤
            (((K / h : ℕ) : ℝ) + 1) / (K : ℝ) := by
          simpa [h, g] using div_le_div_of_nonneg_right hsum hKR.le
        _ ≤ ((K : ℝ) * (Q : ℝ) / (d : ℝ) + 1) /
              (K : ℝ) := div_le_div_of_nonneg_right (by linarith) hKR.le
        _ = (Q : ℝ) / (d : ℝ) + 1 / (K : ℝ) := by field_simp
        _ ≤ (Q : ℝ) / (d : ℝ) + (Q : ℝ) / (d : ℝ) :=
          by gcongr
        _ ≤ (2 * (Q + 1) : ℝ) / (d : ℝ) := by
          have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := by positivity
          rw [← two_mul, ← mul_div_assoc]
          gcongr
          norm_num

theorem cesaroMean_shiftedSupportAtom_mul_nonneg
    (A : Set ℕ) (Q d K : ℕ) :
    0 ≤ cesaroMean
      (fun k : ℕ => shiftedSupportAtom A ((k + 1) * Q) d) K := by
  unfold cesaroMean
  exact div_nonneg
    (Finset.sum_nonneg fun k _ => Set.indicator_nonneg
      (fun n _ => shiftedMersenneAtom_nonneg ((k + 1) * Q) n) d)
    (by positivity)

theorem tendsto_cesaroMean_shiftedSupportAtom_mul
    (A : Set ℕ) (Q d : ℕ) (hQ : 0 < Q) :
    Tendsto
      (fun K : ℕ => cesaroMean
        (fun k : ℕ => shiftedSupportAtom A ((k + 1) * Q) d) K)
      atTop (nhds (shiftedSupportOrbitMean A Q d)) := by
  classical
  by_cases hdA : d ∈ A
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [cesaroMean, shiftedSupportAtom, shiftedSupportOrbitMean,
        shiftedMersenneAtom, shiftedMersenneOrbitMean, hdA]
    · simpa [shiftedSupportAtom, shiftedSupportOrbitMean, hdA] using
        tendsto_cesaroMean_shiftedMersenneAtom_mul Q d hQ hd
  · simp [cesaroMean, shiftedSupportAtom, shiftedSupportOrbitMean, hdA]

/-- The finite means admit a fixed-`Q`, summable conductor majorant. -/
theorem norm_cesaroMean_shiftedSupportAtom_mul_le
    (A : Set ℕ) (Q d K : ℕ) (hQ : 0 < Q) (hK : 0 < K) :
    ‖cesaroMean
        (fun k : ℕ => shiftedSupportAtom A ((k + 1) * Q) d) K‖ ≤
      (2 * (Q + 1) : ℝ) * reciprocalSupportTerm A d := by
  classical
  rw [Real.norm_eq_abs,
    abs_of_nonneg (cesaroMean_shiftedSupportAtom_mul_nonneg A Q d K)]
  by_cases hdA : d ∈ A
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [cesaroMean, shiftedSupportAtom, reciprocalSupportTerm,
        shiftedMersenneAtom, hdA]
    · simpa [cesaroMean, shiftedSupportAtom, reciprocalSupportTerm, hdA,
        div_eq_mul_inv, mul_assoc] using
        cesaroMean_shiftedMersenneAtom_mul_le Q d K hQ hK
  · simp [cesaroMean, shiftedSupportAtom, reciprocalSupportTerm, hdA]

/-- The real-valued atom inherits the exact carry step of the rational atom
already present in `MersenneTailAtoms`. -/
theorem shiftedMersenneAtom_step (N d : ℕ) :
    2 * shiftedMersenneAtom N d - shiftedMersenneAtom (N + 1) d =
      if 0 < d ∧ d ∣ N + 1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedMersenneAtom]
  · let dp : ℕ+ := ⟨d, hd⟩
    have hq := mersenneTailAtom_step dp N
    have hr := congrArg (fun q : ℚ => (q : ℝ)) hq
    rw [shiftedMersenneAtom, if_neg hd.ne', shiftedMersenneAtom,
      if_neg hd.ne']
    by_cases hdiv : d ∣ N + 1
    · simpa [hd, hdiv, mersenneTailAtom, dp] using hr
    · simpa [hd, hdiv, mersenneTailAtom, dp] using hr

theorem shiftedMersenneAtom_le_pow_mul_zero (N d : ℕ) :
    shiftedMersenneAtom N d ≤
      (2 : ℝ) ^ N * ((1 : ℝ) / ((2 : ℝ) ^ d - 1)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedMersenneAtom]
  · rw [shiftedMersenneAtom, if_neg hd.ne']
    have hden : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
      have : (1 : ℝ) < (2 : ℝ) ^ d := one_lt_pow₀ (by norm_num) hd.ne'
      linarith
    have hmod : N % d ≤ N := Nat.mod_le _ _
    have hp : (2 : ℝ) ^ (N % d) ≤ (2 : ℝ) ^ N :=
      pow_le_pow_right₀ (by norm_num) hmod
    calc
      (2 : ℝ) ^ (N % d) / ((2 : ℝ) ^ d - 1) =
          (2 : ℝ) ^ (N % d) * (1 / ((2 : ℝ) ^ d - 1)) := by ring
      _ ≤ (2 : ℝ) ^ N * (1 / ((2 : ℝ) ^ d - 1)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)

theorem summable_shiftedSupportAtom (A : Set ℕ) (N : ℕ) :
    Summable (shiftedSupportAtom A N) := by
  have hbase := summable_erdosSupport_indicator 2 A (by norm_num)
  have hscaled : Summable (fun d : ℕ =>
      (2 : ℝ) ^ N *
        Set.indicator A (fun d => (1 : ℝ) / ((2 : ℝ) ^ d - 1)) d) :=
    hbase.mul_left ((2 : ℝ) ^ N)
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hscaled
  · exact Set.indicator_nonneg
      (fun d _ => shiftedMersenneAtom_nonneg N d) d
  · by_cases hdA : d ∈ A
    · simp only [shiftedSupportAtom, Set.indicator_of_mem hdA]
      exact shiftedMersenneAtom_le_pow_mul_zero N d
    · simp [shiftedSupportAtom, hdA]

/-- Summing in the conductor commutes with the finite Cesàro mean. -/
theorem tsum_cesaroMean_shiftedSupportAtom_mul
    (A : Set ℕ) (Q K : ℕ) :
    (∑' d : ℕ, cesaroMean
        (fun k : ℕ => shiftedSupportAtom A ((k + 1) * Q) d) K) =
      cesaroMean
        (fun k : ℕ => ∑' d : ℕ,
          shiftedSupportAtom A ((k + 1) * Q) d) K := by
  unfold cesaroMean
  rw [tsum_div_const]
  rw [Summable.tsum_finsetSum]
  intro k _
  exact summable_shiftedSupportAtom A ((k + 1) * Q)

/-- For a fixed positive step, the Cesàro means of the complete support
tail converge to the sum of the gcd-orbit means. -/
theorem tendsto_cesaroMean_tsum_shiftedSupportAtom_mul
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (Q : ℕ) (hQ : 0 < Q) :
    Tendsto
      (fun K : ℕ => cesaroMean
        (fun k : ℕ => ∑' d : ℕ,
          shiftedSupportAtom A ((k + 1) * Q) d) K)
      atTop (nhds (∑' d : ℕ, shiftedSupportOrbitMean A Q d)) := by
  have hbound : Summable
      (fun d : ℕ => (2 * (Q + 1) : ℝ) * reciprocalSupportTerm A d) :=
    hsum.mul_left (2 * (Q + 1) : ℝ)
  have htannery := tendsto_tsum_of_dominated_convergence hbound
    (tendsto_cesaroMean_shiftedSupportAtom_mul A Q · hQ)
    ((eventually_gt_atTop (0 : ℕ)).mono fun K hK d =>
      norm_cesaroMean_shiftedSupportAtom_mul_le A Q d K hQ hK)
  exact htannery.congr'
    (Filter.Eventually.of_forall fun K =>
      tsum_cesaroMean_shiftedSupportAtom_mul A Q K)

theorem tendsto_shiftedSupportOrbitMean_periodLcm
    (A : Set ℕ) (d : ℕ) :
    Tendsto (fun P : ℕ => shiftedSupportOrbitMean A (periodLcm P) d)
      atTop (nhds (shiftedSupportAtom A 0 d)) := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · by_cases hzero : 0 ∈ A <;>
      simp [shiftedSupportOrbitMean, shiftedSupportAtom,
        shiftedMersenneOrbitMean, shiftedMersenneAtom, hzero]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop d] with P hPd
    exact (shiftedSupportOrbitMean_eq_zero_of_dvd A (periodLcm P) d hd
      (dvd_periodLcm hd hPd)).symm

/-- Along the LCM-prefix steps, the orbit-mean sum returns to the zero-shift
support sum.  This is the outer dominated-convergence limit. -/
theorem tendsto_tsum_shiftedSupportOrbitMean_periodLcm
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A)) :
    Tendsto
      (fun P : ℕ => ∑' d : ℕ,
        shiftedSupportOrbitMean A (periodLcm P) d)
      atTop (nhds (∑' d : ℕ, shiftedSupportAtom A 0 d)) := by
  exact tendsto_tsum_of_dominated_convergence hsum
    (tendsto_shiftedSupportOrbitMean_periodLcm A)
    (Filter.Eventually.of_forall fun P d =>
      norm_shiftedSupportOrbitMean_le_reciprocalSupportTerm
        A (periodLcm P) d)

/-- The support-atom sum at shift zero is the original support series. -/
theorem tsum_shiftedSupportAtom_zero (A : Set ℕ) :
    (∑' d : ℕ, shiftedSupportAtom A 0 d) = erdosSupportSeries 2 A := by
  unfold erdosSupportSeries shiftedSupportAtom
  apply tsum_congr
  intro d
  by_cases hdA : d ∈ A
  · simp [hdA, shiftedMersenneAtom_zero]
  · simp [hdA]

theorem shiftedSupportAtom_step (A : Set ℕ) [DecidablePred (· ∈ A)] (N d : ℕ) :
    2 * shiftedSupportAtom A N d - shiftedSupportAtom A (N + 1) d =
      if d ∈ A ∧ 0 < d ∧ d ∣ N + 1 then 1 else 0 := by
  classical
  by_cases hdA : d ∈ A
  · simp only [shiftedSupportAtom, Set.indicator_of_mem hdA, hdA, true_and]
    exact shiftedMersenneAtom_step N d
  · simp [shiftedSupportAtom, hdA]

/-- Summing the atom carry steps recovers the support coefficient. -/
theorem tsum_shiftedSupportAtom_step (A : Set ℕ) (N : ℕ) :
    2 * (∑' d : ℕ, shiftedSupportAtom A N d) -
        (∑' d : ℕ, shiftedSupportAtom A (N + 1) d) =
      (supportCoeff A (N + 1) : ℝ) := by
  classical
  have hsN := summable_shiftedSupportAtom A N
  have hsS := summable_shiftedSupportAtom A (N + 1)
  calc
    2 * (∑' d, shiftedSupportAtom A N d) -
          ∑' d, shiftedSupportAtom A (N + 1) d =
        (∑' d, 2 * shiftedSupportAtom A N d) -
          ∑' d, shiftedSupportAtom A (N + 1) d := by
            rw [tsum_mul_left]
    _ = ∑' d, (2 * shiftedSupportAtom A N d -
          shiftedSupportAtom A (N + 1) d) :=
      ((hsN.mul_left 2).tsum_sub hsS).symm
    _ = ∑' d, (if d ∈ A ∧ 0 < d ∧ d ∣ N + 1 then 1 else 0) :=
      tsum_congr (shiftedSupportAtom_step A N)
    _ = (supportCoeff A (N + 1) : ℝ) := by
      rw [tsum_eq_sum (s := (N + 1).divisors)]
      · rw [supportCoeff_cast_eq_sum_indicator]
        apply Finset.sum_congr rfl
        intro d hddiv
        have hdiv : d ∣ N + 1 := (Nat.mem_divisors.mp hddiv).1
        have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv (by omega)
        by_cases hdA : d ∈ A
        · simp [hdA, hpos, hdiv]
        · simp [hdA]
      · intro d hdnot
        have hndvd : ¬ d ∣ N + 1 := by
          intro hdiv
          exact hdnot (Nat.mem_divisors.mpr ⟨hdiv, by omega⟩)
        simp [hndvd]

/-- The whole shifted-atom sum is exactly the binary coefficient tail.  This
is the atomization identity needed to transfer pointwise support information
to the existing tail orbit. -/
theorem binaryCoeffTail_supportCoeff_eq_tsum_shiftedSupportAtom
    (A : Set ℕ) (N : ℕ) :
    binaryCoeffTail (supportCoeff A) N =
      ∑' d : ℕ, shiftedSupportAtom A N d := by
  induction N with
  | zero =>
      rw [binaryCoeffTail_zero, ← erdosSupportSeries_two_eq_binaryCoeffSeries,
        ← tsum_shiftedSupportAtom_zero]
  | succ N ih =>
      rw [binaryCoeffTail_succ (supportCoeff A) (supportCoeff_le_self A) N]
      have hstep := tsum_shiftedSupportAtom_step A N
      rw [ih]
      linarith

theorem shiftedMersenneAtom_zero_le (N d : ℕ) :
    shiftedMersenneAtom 0 d ≤ shiftedMersenneAtom N d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedMersenneAtom]
  · rw [shiftedMersenneAtom_zero, shiftedMersenneAtom, if_neg hd.ne']
    have hden : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
      have : (1 : ℝ) < (2 : ℝ) ^ d := one_lt_pow₀ (by norm_num) hd.ne'
      linarith
    exact div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num)) hden.le

theorem shiftedMersenneAtom_zero_lt_of_lt
    (N d : ℕ) (hN : 0 < N) (hNd : N < d) :
    shiftedMersenneAtom 0 d < shiftedMersenneAtom N d := by
  have hd : 0 < d := hN.trans hNd
  rw [shiftedMersenneAtom_zero, shiftedMersenneAtom, if_neg hd.ne',
    Nat.mod_eq_of_lt hNd]
  have hden : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ d := one_lt_pow₀ (by norm_num) hd.ne'
    linarith
  exact div_lt_div_of_pos_right (one_lt_pow₀ (by norm_num) hN.ne') hden

theorem shiftedSupportAtom_zero_le (A : Set ℕ) (N d : ℕ) :
    shiftedSupportAtom A 0 d ≤ shiftedSupportAtom A N d := by
  classical
  by_cases hdA : d ∈ A
  · simpa [shiftedSupportAtom, hdA] using shiftedMersenneAtom_zero_le N d
  · simp [shiftedSupportAtom, hdA]

theorem shiftedSupportAtom_zero_lt_of_mem_of_lt
    (A : Set ℕ) (N d : ℕ) (hdA : d ∈ A) (hN : 0 < N) (hNd : N < d) :
    shiftedSupportAtom A 0 d < shiftedSupportAtom A N d := by
  simpa [shiftedSupportAtom, hdA] using
    shiftedMersenneAtom_zero_lt_of_lt N d hN hNd

/-- For an infinite support, shift zero is the strict global minimum of the
binary support-tail orbit.  The strict witness is any support rank above the
positive shift. -/
theorem binaryCoeffTail_supportCoeff_zero_strictMinimum
    (A : Set ℕ) (hA : A.Infinite) (N : ℕ) (hN : 0 < N) :
    binaryCoeffTail (supportCoeff A) 0 <
      binaryCoeffTail (supportCoeff A) N := by
  obtain ⟨d, hdA, hNd⟩ := hA.exists_gt N
  rw [binaryCoeffTail_supportCoeff_eq_tsum_shiftedSupportAtom,
    binaryCoeffTail_supportCoeff_eq_tsum_shiftedSupportAtom]
  exact Summable.tsum_lt_tsum_of_nonneg (i := d)
    (fun e => by
      exact Set.indicator_nonneg
        (fun k _ => shiftedMersenneAtom_nonneg 0 k) e)
    (shiftedSupportAtom_zero_le A N)
    (shiftedSupportAtom_zero_lt_of_mem_of_lt A N d hdA hN hNd)
    (summable_shiftedSupportAtom A N)

/-- An infinite support tail orbit never returns to its initial value at a
positive time. -/
theorem binaryCoeffTail_supportCoeff_ne_initial_of_pos
    (A : Set ℕ) (hA : A.Infinite) (N : ℕ) (hN : 0 < N) :
    binaryCoeffTail (supportCoeff A) N ≠
      binaryCoeffTail (supportCoeff A) 0 :=
  ne_of_gt (binaryCoeffTail_supportCoeff_zero_strictMinimum A hA N hN)

/-! ## The integer-gap endgame -/

/-- A coefficient tail with a strict initial minimum and arbitrarily close
positive returns cannot start from a rational binary series.  Rationality
would put every tail, after multiplication by one fixed positive integer, in
the integer lattice; a positive return gap smaller than one lattice spacing
is then impossible. -/
theorem irrational_binaryCoeffSeries_of_strictInitialMin_of_closeReturn
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    (hstrict : ∀ N : ℕ, 0 < N →
      binaryCoeffTail c 0 < binaryCoeffTail c N)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      binaryCoeffTail c N < binaryCoeffTail c 0 + ε) :
    Irrational (binaryCoeffSeries c) := by
  by_contra hrat
  have hvalue : HasRationalValue (binaryCoeffSeries c) :=
    (hasRationalValue_iff_not_irrational _).2 hrat
  obtain ⟨v, hv, u, hu⟩ :=
    exists_temperedBinaryOrbit_of_rational c hgrowth hvalue
  have hutail := temperedBinaryOrbit_eq_scaledTail c hgrowth hu
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  obtain ⟨N, hN, hnear⟩ := hclose (1 / (v : ℝ)) (by positivity)
  have hgap_pos : (0 : ℝ) < ((u N - u 0 : ℤ) : ℝ) := by
    push_cast
    rw [hutail N, hutail 0]
    nlinarith [mul_pos hvR (sub_pos.mpr (hstrict N hN))]
  have htail_gap_lt :
      binaryCoeffTail c N - binaryCoeffTail c 0 < 1 / (v : ℝ) := by
    linarith
  have hgap_lt : ((u N - u 0 : ℤ) : ℝ) < 1 := by
    have hmul := mul_lt_mul_of_pos_left htail_gap_lt hvR
    have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvR
    push_cast
    rw [hutail N, hutail 0]
    rw [show (v : ℝ) * (1 / (v : ℝ)) = 1 by field_simp] at hmul
    linarith
  have hgap_pos_int : 0 < u N - u 0 := by exact_mod_cast hgap_pos
  have hgap_lt_int : u N - u 0 < 1 := by exact_mod_cast hgap_lt
  omega

/-- Infinite support supplies the strict-minimum half of the generic
integer-gap endgame.  The remaining hypothesis is stated exactly as the
positive shifted-atom near-return property; no summability-to-return theorem
is assumed here. -/
theorem irrational_erdosSupportSeries_two_of_infinite_of_shiftedAtom_closeReturn
    (A : Set ℕ) (hA : A.Infinite)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      (∑' d : ℕ, shiftedSupportAtom A N d) <
        (∑' d : ℕ, shiftedSupportAtom A 0 d) + ε) :
    Irrational (erdosSupportSeries 2 A) := by
  rw [erdosSupportSeries_two_eq_binaryCoeffSeries]
  apply irrational_binaryCoeffSeries_of_strictInitialMin_of_closeReturn
    (supportCoeff A) (supportCoeff_le_self A)
    (binaryCoeffTail_supportCoeff_zero_strictMinimum A hA)
  intro ε hε
  obtain ⟨N, hN, hnear⟩ := hclose ε hε
  refine ⟨N, hN, ?_⟩
  simpa only [binaryCoeffTail_supportCoeff_eq_tsum_shiftedSupportAtom] using hnear

/-- Reciprocal summability supplies arbitrarily close positive returns of the
complete shifted-atom sum.  The proof first takes the LCM-prefix limit of the
gcd-orbit means, then a Cesàro limit at the selected positive LCM step, and
finally chooses one term no larger than that finite average. -/
theorem exists_shiftedSupportAtom_closeReturn_of_summable_reciprocal
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧
      (∑' d : ℕ, shiftedSupportAtom A N d) <
        (∑' d : ℕ, shiftedSupportAtom A 0 d) + ε := by
  classical
  let T₀ : ℝ := ∑' d : ℕ, shiftedSupportAtom A 0 d
  have houter := tendsto_tsum_shiftedSupportOrbitMean_periodLcm A hsum
  have houterBound : ∀ᶠ P : ℕ in atTop,
      (∑' d : ℕ, shiftedSupportOrbitMean A (periodLcm P) d) <
        T₀ + ε / 2 := by
    exact (tendsto_order.1 houter).2 _ (by dsimp [T₀]; linarith)
  obtain ⟨P, hP⟩ := houterBound.exists
  let Q : ℕ := periodLcm P
  have hQ : 0 < Q := by
    dsimp [Q]
    exact periodLcm_pos P
  have hinner := tendsto_cesaroMean_tsum_shiftedSupportAtom_mul A hsum Q hQ
  have hinnerBound : ∀ᶠ K : ℕ in atTop,
      cesaroMean
          (fun k : ℕ => ∑' d : ℕ,
            shiftedSupportAtom A ((k + 1) * Q) d) K <
        (∑' d : ℕ, shiftedSupportOrbitMean A Q d) + ε / 2 :=
    (tendsto_order.1 hinner).2 _ (by linarith)
  obtain ⟨K, hKnear, hK⟩ :=
    (hinnerBound.and (eventually_gt_atTop (0 : ℕ))).exists
  let f : ℕ → ℝ := fun k =>
    ∑' d : ℕ, shiftedSupportAtom A ((k + 1) * Q) d
  have hKnonempty : (Finset.range K).Nonempty :=
    ⟨0, Finset.mem_range.mpr hK⟩
  have hsumMean :
      ∑ k ∈ Finset.range K, f k ≤
        ∑ k ∈ Finset.range K, cesaroMean f K := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    unfold cesaroMean
    have hKR : (K : ℝ) ≠ 0 := by positivity
    field_simp
    exact le_rfl
  obtain ⟨k, hkK, hkMean⟩ :=
    Finset.exists_le_of_sum_le hKnonempty hsumMean
  refine ⟨(k + 1) * Q, Nat.mul_pos (by omega) hQ, ?_⟩
  calc
    (∑' d : ℕ, shiftedSupportAtom A ((k + 1) * Q) d) = f k := rfl
    _ ≤ cesaroMean f K := hkMean
    _ < (∑' d : ℕ, shiftedSupportOrbitMean A Q d) + ε / 2 := by
      simpa [f] using hKnear
    _ < T₀ + ε := by
      have hP' :
          (∑' d : ℕ, shiftedSupportOrbitMean A Q d) < T₀ + ε / 2 := by
        simpa [Q] using hP
      linarith
    _ = (∑' d : ℕ, shiftedSupportAtom A 0 d) + ε := rfl

/-- Every infinite reciprocal-summable support gives an irrational binary
Mersenne subseries. -/
theorem irrational_erdosSupportSeries_two_of_summable_reciprocal
    (A : Set ℕ) (hA : A.Infinite)
    (hsum : Summable (reciprocalSupportTerm A)) :
    Irrational (erdosSupportSeries 2 A) := by
  exact irrational_erdosSupportSeries_two_of_infinite_of_shiftedAtom_closeReturn
    A hA (fun ε hε =>
      exists_shiftedSupportAtom_closeReturn_of_summable_reciprocal
        A hsum ε hε)

/-! ## Generalised integer-gap endgame -/

/-- **Generalised integer-gap endgame.**  Irrationality follows from a single
sequence of witnesses at which the tail exceeds `binaryCoeffTail c 0 + c0` and
approaches it arbitrarily closely, for any NATURAL shift `c0`.

Two weakenings of `irrational_binaryCoeffSeries_of_strictInitialMin_of_closeReturn`.
First, that theorem's strict minimum is stated globally but its proof consumes it at
exactly one `N` -- the witness produced by the close return -- so the two hypotheses
merge into one two-sided condition at a common witness.  Second, the return may be to
a shifted value.  **Integrality of the shift is essential**: the endgame closes
because no integer lies strictly inside `(v*c0, v*c0 + 1)`, and a non-integer shift
would leave exactly one integer there. -/
theorem irrational_binaryCoeffSeries_of_shiftedTwoSidedReturn
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (c0 : ℕ)
    (hreturn : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      binaryCoeffTail c 0 + (c0 : ℝ) < binaryCoeffTail c N ∧
      binaryCoeffTail c N < binaryCoeffTail c 0 + (c0 : ℝ) + ε) :
    Irrational (binaryCoeffSeries c) := by
  by_contra hrat
  have hvalue : HasRationalValue (binaryCoeffSeries c) :=
    (hasRationalValue_iff_not_irrational _).2 hrat
  obtain ⟨v, hv, u, hu⟩ :=
    exists_temperedBinaryOrbit_of_rational c hgrowth hvalue
  have hutail := temperedBinaryOrbit_eq_scaledTail c hgrowth hu
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvR
  obtain ⟨N, hN, hlow, hhigh⟩ := hreturn (1 / (v : ℝ)) (by positivity)
  have htail_gap_pos :
      (0 : ℝ) < binaryCoeffTail c N - binaryCoeffTail c 0 - (c0 : ℝ) := by
    linarith
  have htail_gap_lt :
      binaryCoeffTail c N - binaryCoeffTail c 0 - (c0 : ℝ) < 1 / (v : ℝ) := by
    linarith
  have hgap_pos : ((v * c0 : ℕ) : ℝ) < ((u N - u 0 : ℤ) : ℝ) := by
    have hmul := mul_pos hvR htail_gap_pos
    push_cast
    rw [hutail N, hutail 0]
    nlinarith
  have hgap_lt : ((u N - u 0 : ℤ) : ℝ) < ((v * c0 : ℕ) : ℝ) + 1 := by
    have hmul := mul_lt_mul_of_pos_left htail_gap_lt hvR
    rw [show (v : ℝ) * (1 / (v : ℝ)) = 1 by field_simp] at hmul
    push_cast
    rw [hutail N, hutail 0]
    nlinarith
  have hgap_pos_int : ((v * c0 : ℕ) : ℤ) < u N - u 0 := by exact_mod_cast hgap_pos
  have hgap_lt_int : u N - u 0 < ((v * c0 : ℕ) : ℤ) + 1 := by exact_mod_cast hgap_lt
  omega

/-- Regression: the previously stated form -- global strict minimum, shift zero -- is
the special case `c0 = 0` of the generalised endgame. -/
theorem irrational_binaryCoeffSeries_of_strictInitialMin_of_closeReturn_of_shifted
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    (hstrict : ∀ N : ℕ, 0 < N →
      binaryCoeffTail c 0 < binaryCoeffTail c N)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      binaryCoeffTail c N < binaryCoeffTail c 0 + ε) :
    Irrational (binaryCoeffSeries c) := by
  refine irrational_binaryCoeffSeries_of_shiftedTwoSidedReturn c hgrowth 0 ?_
  intro ε hε
  obtain ⟨N, hN, hnear⟩ := hclose ε hε
  refine ⟨N, hN, ?_, ?_⟩
  · have := hstrict N hN
    push_cast
    linarith
  · push_cast
    linarith

/-! ## Pratt's shift identity -- the arithmetic core

Pratt (arXiv:2409.15185, Proposition 2.1) forces `omega` to reproduce its own head,
shifted by one, across a block of consecutive integers.  The load-bearing step is
purely arithmetic and is isolated here; the prime `k`-tuples input enters only as the
primality hypothesis `hp`. -/

/-- If `k` divides `m` then `k` is coprime to `m + 1`. -/
theorem coprime_succ_of_dvd {k m : ℕ} (h : k ∣ m) : Nat.Coprime k (m + 1) := by
  have hdvd : Nat.gcd k (m + 1) ∣ 1 := by
    have h1 : Nat.gcd k (m + 1) ∣ m := dvd_trans (Nat.gcd_dvd_left _ _) h
    have h2 : Nat.gcd k (m + 1) ∣ m + 1 := Nat.gcd_dvd_right _ _
    exact (Nat.dvd_add_right h1).mp h2
  exact Nat.dvd_one.mp hdvd

/-- **The coprimality that makes the block factorisation work.**  When `k^2 ∣ Q`, the
cofactor `n * (Q / k) + 1` is coprime to `k`, because `k ∣ Q / k`. -/
theorem coprime_cofactor_of_sq_dvd
    {k Q : ℕ} (hk : 0 < k) (hsq : k * k ∣ Q) (n : ℕ) :
    Nat.Coprime k (n * (Q / k) + 1) := by
  obtain ⟨c, hc⟩ := hsq
  have hQk : Q / k = k * c := by
    subst hc
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ hk]
  refine coprime_succ_of_dvd ?_
  rw [hQk]
  exact ⟨n * c, by ring⟩

/-- The block factorisation itself: `n * Q + k = k * (n * (Q / k) + 1)` whenever
`k ∣ Q`. -/
theorem block_factorisation {k Q : ℕ} (hk : 0 < k) (hdvd : k ∣ Q) (n : ℕ) :
    n * Q + k = k * (n * (Q / k) + 1) := by
  obtain ⟨c, hc⟩ := hdvd
  subst hc
  rw [Nat.mul_div_cancel_left _ hk]
  ring

/-- `omega` is additive on coprime factors. -/
theorem card_primeFactors_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : Nat.Coprime a b) :
    (a * b).primeFactors.card = a.primeFactors.card + b.primeFactors.card := by
  rw [Nat.primeFactors_mul ha hb]
  exact Finset.card_union_of_disjoint hab.disjoint_primeFactors

/-- **Pratt's shift identity.**  If `k^2 ∣ Q`, `0 < k`, and the cofactor
`n * (Q / k) + 1` is prime, then the block index `n * Q + k` carries exactly one more
distinct prime factor than `k` does:

    omega (n * Q + k) = omega k + 1.

This is the step that makes the tail reproduce the head shifted by one, and hence the
step that produces a return to `y + 1/(t-1)` rather than to `y`. -/
theorem card_primeFactors_block_of_sq_dvd
    {k Q n : ℕ} (hk : 0 < k) (hsq : k * k ∣ Q)
    (hp : Nat.Prime (n * (Q / k) + 1)) :
    (n * Q + k).primeFactors.card = k.primeFactors.card + 1 := by
  have hdvd : k ∣ Q := dvd_trans (dvd_mul_left k k) hsq
  rw [block_factorisation hk hdvd n]
  rw [card_primeFactors_mul_of_coprime hk.ne' hp.ne_zero
        (coprime_cofactor_of_sq_dvd hk hsq n)]
  rw [Nat.Prime.primeFactors hp]
  simp


/-! ## Finite tail splitting, and the shifted-block identity -/

/-- `sum_{j=1}^{K} 2^-j = 1 - 2^-K`. -/
theorem geom_sum_half : ∀ K : ℕ,
    (∑ j ∈ Finset.Icc 1 K, ((1 : ℝ) / 2 ^ j)) = 1 - 1 / 2 ^ K := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero K)), ih]
      have h2 : ((2 : ℝ) ^ K) ≠ 0 := by positivity
      field_simp
      ring

/-- **Finite split.**  The tail at `N` is its first `K` coefficients, weighted
dyadically, plus `2^-K` times the tail at `N + K`.  Proved by induction from the
one-step recurrence `binaryCoeffTail_succ`; no series rearrangement is needed. -/
theorem binaryCoeffTail_split (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (N : ℕ) :
    ∀ K : ℕ,
      binaryCoeffTail c N
        = (∑ j ∈ Finset.Icc 1 K, (c (N + j) : ℝ) / 2 ^ j)
          + binaryCoeffTail c (N + K) / 2 ^ K := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
      have hrec := binaryCoeffTail_succ c hgrowth (N + K)
      have hstep : binaryCoeffTail c (N + K)
          = (binaryCoeffTail c (N + K + 1) + (c (N + K + 1) : ℝ)) / 2 := by
        linarith
      have hN : N + (K + 1) = N + K + 1 := by omega
      rw [Finset.sum_Icc_succ_top (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero K)), ih,
        hstep, hN]
      have h2 : ((2 : ℝ) ^ K) ≠ 0 := by positivity
      field_simp
      ring

/-- **The shifted-block identity.**  If the coefficient sequence at `N` reproduces its
own head shifted by one across `1 ≤ j ≤ K`, then the tail at `N` sits exactly one above
the tail at `0`, up to a `2^-K`-scaled remainder.  This is the `S_1` computation of
Pratt's argument, as an exact identity rather than an estimate. -/
theorem binaryCoeffTail_shifted_block (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    (N K : ℕ) (hshift : ∀ j : ℕ, 1 ≤ j → j ≤ K → c (N + j) = c j + 1) :
    binaryCoeffTail c N
      = binaryCoeffTail c 0 + 1
        + (binaryCoeffTail c (N + K) - binaryCoeffTail c K - 1) / 2 ^ K := by
  have hsplitN := binaryCoeffTail_split c hgrowth N K
  have hsplit0 := binaryCoeffTail_split c hgrowth 0 K
  have hhead : (∑ j ∈ Finset.Icc 1 K, (c (N + j) : ℝ) / 2 ^ j)
      = (∑ j ∈ Finset.Icc 1 K, (c (0 + j) : ℝ) / 2 ^ j) + (1 - 1 / 2 ^ K) := by
    rw [← geom_sum_half K, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjK : j ≤ K := (Finset.mem_Icc.mp hj).2
    rw [hshift j hj1 hjK, zero_add]
    push_cast
    ring
  rw [hsplitN, hhead, hsplit0]
  simp only [zero_add]
  ring


/-- The tail dominates half its own leading coefficient.  Immediate from the finite
split at `K = 1` together with non-negativity of the remaining tail. -/
theorem binaryCoeffTail_ge_head (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (M : ℕ) :
    (c (M + 1) : ℝ) / 2 ≤ binaryCoeffTail c M := by
  have h := binaryCoeffTail_split c hgrowth M 1
  rw [Finset.Icc_self, Finset.sum_singleton] at h
  have hnn := binaryCoeffTail_nonneg c (M + 1)
  rw [h]
  simp only [pow_one]
  linarith

/-- **Lower half of the shifted return.**  Under the `+1` shift on `1 ≤ j ≤ K`, a single
large coefficient just past the block forces the tail at `N` strictly above
`tail 0 + 1`.  The bound `B` on `binaryCoeffTail c K` is taken as a hypothesis: for
`c = omega` it needs an arithmetic input (`omega n << log n`) beyond `c n ≤ n`, and
`binaryCoeffTail_le` is far too weak to supply it. -/
theorem binaryCoeffTail_shifted_block_lower (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    (N K : ℕ) (B : ℝ)
    (hshift : ∀ j : ℕ, 1 ≤ j → j ≤ K → c (N + j) = c j + 1)
    (hK : binaryCoeffTail c K ≤ B)
    (hbig : 2 * (B + 1) < (c (N + K + 1) : ℝ)) :
    binaryCoeffTail c 0 + 1 < binaryCoeffTail c N := by
  have hid := binaryCoeffTail_shifted_block c hgrowth N K hshift
  have hhead := binaryCoeffTail_ge_head c hgrowth (N + K)
  have h2 : (0 : ℝ) < 2 ^ K := by positivity
  have hbracket : 0 < binaryCoeffTail c (N + K) - binaryCoeffTail c K - 1 := by
    linarith
  have hpos : 0 < (binaryCoeffTail c (N + K) - binaryCoeffTail c K - 1) / 2 ^ K :=
    div_pos hbracket h2
  rw [hid]
  linarith


/-- **Upper half of the shifted return.**  Under the `+1` shift on `1 ≤ j ≤ K`, a bound
`U` on the tail just past the block caps the tail at `N` within `eps` of `tail 0 + 1`,
provided `U - 1 < eps * 2^K`.  Mirror of `binaryCoeffTail_shifted_block_lower`. -/
theorem binaryCoeffTail_shifted_block_upper (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    (N K : ℕ) (U eps : ℝ)
    (hshift : ∀ j : ℕ, 1 ≤ j → j ≤ K → c (N + j) = c j + 1)
    (hU : binaryCoeffTail c (N + K) ≤ U)
    (hsmall : U - 1 < eps * 2 ^ K) :
    binaryCoeffTail c N < binaryCoeffTail c 0 + 1 + eps := by
  have hid := binaryCoeffTail_shifted_block c hgrowth N K hshift
  have hKnn := binaryCoeffTail_nonneg c K
  have h2 : (0 : ℝ) < 2 ^ K := by positivity
  have hnum : binaryCoeffTail c (N + K) - binaryCoeffTail c K - 1 < eps * 2 ^ K := by
    linarith
  have hdiv : (binaryCoeffTail c (N + K) - binaryCoeffTail c K - 1) / 2 ^ K < eps := by
    rw [div_lt_iff₀ h2]
    linarith
  rw [hid]
  linarith

/-- **The per-witness two-sided return.**  Both halves at a single `N`: exactly the body
of the `hreturn` hypothesis consumed by
`irrational_binaryCoeffSeries_of_shiftedTwoSidedReturn` at `c0 = 1`. -/
theorem binaryCoeffTail_shifted_block_two_sided (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    (N K : ℕ) (B U eps : ℝ)
    (hshift : ∀ j : ℕ, 1 ≤ j → j ≤ K → c (N + j) = c j + 1)
    (hK : binaryCoeffTail c K ≤ B)
    (hbig : 2 * (B + 1) < (c (N + K + 1) : ℝ))
    (hU : binaryCoeffTail c (N + K) ≤ U)
    (hsmall : U - 1 < eps * 2 ^ K) :
    binaryCoeffTail c 0 + 1 < binaryCoeffTail c N ∧
      binaryCoeffTail c N < binaryCoeffTail c 0 + 1 + eps :=
  ⟨binaryCoeffTail_shifted_block_lower c hgrowth N K B hshift hK hbig,
   binaryCoeffTail_shifted_block_upper c hgrowth N K U eps hshift hU hsmall⟩


/-- **Tail bound from a uniform coefficient bound.**  If every coefficient past `M` is at
most `B`, the whole tail at `M` is at most `B`.  Unlike everything else in this
development this genuinely needs the infinite sum: `binaryCoeffTail_split` leaves a
`2^-K`-scaled remainder that is itself the quantity being bounded. -/
theorem binaryCoeffTail_le_of_bound (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    (M : ℕ) (B : ℝ) (hb : ∀ j : ℕ, (c (M + j + 1) : ℝ) ≤ B) :
    binaryCoeffTail c M ≤ B := by
  have hsum := summable_coeff_shift_tail 2 M c (by norm_num) hgrowth
  have hfun : (fun j : ℕ => B / (2 : ℝ) ^ (j + 1))
      = (fun n : ℕ => B / 2 / (2 : ℝ) ^ n) := by
    funext j
    rw [pow_succ]
    ring
  have hgeom : Summable (fun j : ℕ => B / (2 : ℝ) ^ (j + 1)) := by
    rw [hfun]
    exact summable_geometric_two' B
  have hval : (∑' j : ℕ, B / (2 : ℝ) ^ (j + 1)) = B := by
    rw [hfun]
    exact tsum_geometric_two' B
  have hle : ∀ j : ℕ, (c (M + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
      ≤ B / (2 : ℝ) ^ (j + 1) := by
    intro j
    gcongr
    exact hb j
  calc binaryCoeffTail c M
      = ∑' j : ℕ, (c (M + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1) := rfl
    _ ≤ ∑' j : ℕ, B / (2 : ℝ) ^ (j + 1) := Summable.tsum_le_tsum hle hsum hgeom
    _ = B := hval


/-- **The pointwise-bound witness form is UNSATISFIABLE.**  An earlier version of the
assembly below took uniform *coefficient* bounds `forall j, c (K + j + 1) <= B` where the
underlying lemma wants the *tail* bound `binaryCoeffTail c K <= B`.  That form is
self-contradictory: instantiating the coefficient bound at `j = N` gives
`c (N + K + 1) <= B`, which the large-coefficient clause `2 * (B + 1) < c (N + K + 1)`
contradicts outright, since `B >= c (K + 1) >= 0`.

Recorded rather than deleted, because this defect is invisible to every check that was
run on it: the wrapper elaborated, the build reported `rc = 0`, and `#print axioms` gave
`[propext, Classical.choice, Quot.sound]`.  A vacuously true theorem passes all three.  A
conditional theorem is worth exactly what its hypothesis is worth, and nothing in the
toolchain checks that a hypothesis is satisfiable. -/
theorem shiftedBlockWitnesses_coeffBounds_unsatisfiable
    (c : ℕ → ℕ) (N K : ℕ) (B : ℝ)
    (hBK : ∀ j : ℕ, (c (K + j + 1) : ℝ) ≤ B)
    (hbig : 2 * (B + 1) < (c (N + K + 1) : ℝ)) : False := by
  have hNK : (c (N + K + 1) : ℝ) ≤ B := by
    have h := hBK N
    rwa [show K + N + 1 = N + K + 1 by ring] at h
  have hB0 : (0 : ℝ) ≤ B := le_trans (Nat.cast_nonneg _) (hBK 0)
  linarith

/-- **Irrationality from a supply of shifted-block witnesses.**  Given, for every
`eps > 0`, a block `(N, K)` on which the coefficient sequence reproduces its own head
shifted by one, a tail bound `B` at `K`, one anomalously large coefficient at `N + K + 1`,
and a tail bound `U` at `N + K` small against `eps * 2 ^ K`, the series is irrational.

The two bounds are on **tails**, not on individual coefficients; see
`shiftedBlockWitnesses_coeffBounds_unsatisfiable`.  The distinction is what keeps this
statement non-vacuous for an unbounded `c`: `binaryCoeffTail c K <= B` forces only
`c (N + K + 1) <= B * 2 ^ (N + 1)`, which leaves room for `2 * (B + 1) < c (N + K + 1)`.
That matters because the intended instantiation `c = omega` is unbounded, so any
hypothesis demanding a uniform coefficient bound past a point is unsatisfiable at the
one instance the theorem exists to serve. -/
theorem irrational_binaryCoeffSeries_of_shiftedBlockWitnesses
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    (hwit : ∀ eps : ℝ, 0 < eps → ∃ N K : ℕ, ∃ B U : ℝ, 0 < N ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ K → c (N + j) = c j + 1) ∧
      binaryCoeffTail c K ≤ B ∧
      2 * (B + 1) < (c (N + K + 1) : ℝ) ∧
      binaryCoeffTail c (N + K) ≤ U ∧
      U - 1 < eps * 2 ^ K) :
    Irrational (binaryCoeffSeries c) := by
  refine irrational_binaryCoeffSeries_of_shiftedTwoSidedReturn c hgrowth 1 ?_
  intro eps heps
  obtain ⟨N, K, B, U, hN, hshift, hK, hbig, hU, hsmall⟩ := hwit eps heps
  obtain ⟨hlo, hhi⟩ := binaryCoeffTail_shifted_block_two_sided
    c hgrowth N K B U eps hshift hK hbig hU hsmall
  refine ⟨N, hN, ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith


/-! ## What the witness hypothesis costs: the block length must diverge -/

/-- **Any witness forces its own head-tail to be small against `2 ^ K`.**  Chaining the
four numeric clauses: `binaryCoeffTail_ge_head` gives
`c (N+K+1) / 2 <= binaryCoeffTail c (N+K) <= U`, and `hbig` makes that lower bound exceed
`B + 1`; with `U - 1 < eps * 2 ^ K` this pins `B`, hence the tail at `K`, below
`eps * 2 ^ K`.

No new analysis -- this is the engine's own hypotheses talking to each other.  It matters
because it converts a statement about coefficients into a lower bound on the BLOCK LENGTH
`K`, which is the quantity the shift clause has to supply. -/
theorem shiftedBlockWitness_forces_small_tail
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (N K : ℕ) (B U eps : ℝ)
    (hK : binaryCoeffTail c K ≤ B)
    (hbig : 2 * (B + 1) < (c (N + K + 1) : ℝ))
    (hU : binaryCoeffTail c (N + K) ≤ U)
    (hsmall : U - 1 < eps * 2 ^ K) :
    binaryCoeffTail c K < eps * 2 ^ K := by
  have hhead : (c (N + K + 1) : ℝ) / 2 ≤ binaryCoeffTail c (N + K) :=
    binaryCoeffTail_ge_head c hgrowth (N + K)
  linarith

/-- **The block length diverges as `eps -> 0`.**  If the head-tails are bounded below by
`delta > 0` -- which holds whenever `c` is not eventually zero, i.e. for every infinite
support set -- then every witness for `eps` satisfies `delta < eps * 2 ^ K`.  So
`2 ^ K > delta / eps`, and `K` is forced past any bound as `eps` shrinks.

**Consequence.** The engine cannot be driven by short blocks. A support set that admits
shift blocks only up to some fixed length `K_max` supplies no witness for
`eps < delta / 2 ^ K_max`, and the conditional is unusable there -- however true it is. -/
theorem shiftedBlockWitness_forces_large_block
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (N K : ℕ) (B U eps delta : ℝ)
    (hdelta : delta ≤ binaryCoeffTail c K)
    (hK : binaryCoeffTail c K ≤ B)
    (hbig : 2 * (B + 1) < (c (N + K + 1) : ℝ))
    (hU : binaryCoeffTail c (N + K) ≤ U)
    (hsmall : U - 1 < eps * 2 ^ K) :
    delta < eps * 2 ^ K :=
  lt_of_le_of_lt hdelta
    (shiftedBlockWitness_forces_small_tail c hgrowth N K B U eps hK hbig hU hsmall)


/-! ## The parity obstruction to the Erdos 1948 zero-run mechanism -/

/-- **A socket run cannot pass an odd coefficient.**  Erdos's 1948 argument produces a
run of `K` binary zeros in `sum_n c n / 2^n` by forcing `2 ^ k` to divide `c (N + k)` for
`k = 1, ..., K`, which makes each of the first `K` terms of the shifted sum an integer.
Since `1 <= k` gives `2 | 2 ^ k`, every coefficient inside the run is even.  So a single
odd coefficient anywhere in the window destroys the run. -/
theorem socketRun_excludes_odd_coeff
    (c : ℕ → ℕ) (N K k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ K)
    (hrun : ∀ i : ℕ, 1 ≤ i → i ≤ K → 2 ^ i ∣ c (N + i))
    (hodd : ¬ (2 ∣ c (N + k))) : False :=
  hodd (dvd_trans (dvd_pow_self 2 (by omega)) (hrun k hk hkK))

/-- **The run length is bounded by the gaps of `{m : c m odd}`.**  If every window of `g`
consecutive indices past `N` contains an odd coefficient, no run of length `g` starts at
`N`.  Writing `Odd_c := {m : c m is odd}`, this says

    maxrun  <=  maxgap (Odd_c) - 1,

so **arbitrarily long socket runs require `Odd_c` to have unbounded gaps** -- if `Odd_c`
is syndetic the mechanism is unavailable, not merely unproven.

At `c = tau_N = d` the odd set is exactly the perfect squares, whose gaps grow like
`2 sqrt m`; the obstruction is vacuous there, as it must be, since Erdos carried the
construction out.  At `c = v_2` (support `{2,4,8,...}`) the odd set contains every
`m = 2 mod 4`, so `g = 4` and the run caps at 3. -/
theorem no_socketRun_of_odd_in_window
    (c : ℕ → ℕ) (N g : ℕ)
    (hwin : ∃ k : ℕ, 1 ≤ k ∧ k ≤ g ∧ ¬ (2 ∣ c (N + k))) :
    ¬ (∀ i : ℕ, 1 ≤ i → i ≤ g → 2 ^ i ∣ c (N + i)) := by
  obtain ⟨k, hk, hkg, hodd⟩ := hwin
  intro hrun
  exact socketRun_excludes_odd_coeff c N g k hk hkg hrun hodd


/-- **A socket run forces its nonzero coefficients to be exponentially large.**  Inside a
run, `2 ^ k` divides `c (N + k)`; a nonzero natural divisible by `2 ^ k` is at least
`2 ^ k`.  Zero coefficients are exempt -- zero is divisible by everything -- so the force
lands only where `c` is actually positive. -/
theorem socketRun_forces_pow_le_coeff
    (c : ℕ → ℕ) (N K k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (hrun : ∀ i : ℕ, 1 ≤ i → i ≤ K → 2 ^ i ∣ c (N + i))
    (hpos : 0 < c (N + k)) :
    2 ^ k ≤ c (N + k) :=
  Nat.le_of_dvd hpos (hrun k hk1 hkK)

/-- **The search-depth law.**  Combined with the fact that any `a` in the support divides
one of every `a` consecutive integers -- so some index `k` in the top `a` of the window has
`c (N + k) > 0` -- this gives `2 ^ (K - a + 1) <= max c` over the window.

**This is NOT a cap.**  Since `c = tau_A` is unbounded for every infinite `A`, the right
side grows without bound and no `K` is ever excluded outright.  What the bound gives is a
DEPTH: to observe a run of length `K` one must search out to where `c` reaches `2 ^ K`.
That is the quantitative form of "finite search never refutes existence" -- contrast the
parity obstruction, which bounds the run for ALL `N` at once. -/
theorem socketRun_forces_pow_le_of_le
    (c : ℕ → ℕ) (N K k j : ℕ) (hj : j ≤ k) (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (hrun : ∀ i : ℕ, 1 ≤ i → i ≤ K → 2 ^ i ∣ c (N + i))
    (hpos : 0 < c (N + k)) :
    2 ^ j ≤ c (N + k) :=
  le_trans (Nat.pow_le_pow_right (by norm_num) hj)
    (socketRun_forces_pow_le_coeff c N K k hk1 hkK hrun hpos)


/-! ## The two-powers-apart obstruction behind the `A*` block cap -/

/-- **Two powers of two cannot differ by 2 once both are at least 4.**  This is the
load-bearing step of the block cap proved in `CertificateSocketCollapse.md` section 56:
for the support set `A* = (N \ {2^i}) xor {4p}`, a shifted block of length `>= 4` starting
at an EVEN `N` would force both `N+2` and `N+4` to be powers of two at least 8, and this
lemma forbids it -- so the block length is at most 3.

The argument is a residue count, not a valuation computation: both `2^v` and `2^w` are
divisible by 4 once the exponents are at least 2, while `2^v + 2` is congruent to 2. -/
theorem no_two_powers_two_apart {v w : ℕ} (hv : 2 ≤ v) (hw : 2 ≤ w)
    (h : 2 ^ w = 2 ^ v + 2) : False := by
  have hdv : (4 : ℕ) ∣ 2 ^ v := by
    simpa using pow_dvd_pow 2 hv
  have hdw : (4 : ℕ) ∣ 2 ^ w := by
    simpa using pow_dvd_pow 2 hw
  omega


/-! ## Erdos problem 69 at the witness boundary -/

/-- `supportCoeff` at the primes, as a function identity, for rewriting under
`binaryCoeffTail`. -/
theorem supportCoeff_primes_eq_omega_fun :
    supportCoeff {p : ℕ | p.Prime} = fun n => n.primeFactors.card :=
  funext supportCoeff_primes_eq_card_primeFactors

/-- **Erdos #69, conditional on block witnesses.**  `CertificateKernel`'s
`erdosSupportSeries_primes_eq_tsum_omega` records that
`∑_p 1/(b^p - 1) = ∑_m omega(m)/b^m` and says the identity "places [the analytic input]
at the exact theorem boundary where it belongs".  This theorem consumes that boundary:
the shift clause is `card_primeFactors_block_of_sq_dvd` in support language, and the
remaining clauses are exactly Pratt's Proposition 2.1, which is **assumed here and never
proved**. -/
theorem irrational_erdosSupportSeries_two_primes_of_shiftedBlockWitnesses
    (hwit : ∀ eps : ℝ, 0 < eps → ∃ N K : ℕ, ∃ B U : ℝ, 0 < N ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ K →
        supportCoeff {p : ℕ | p.Prime} (N + j)
          = supportCoeff {p : ℕ | p.Prime} j + 1) ∧
      binaryCoeffTail (supportCoeff {p : ℕ | p.Prime}) K ≤ B ∧
      2 * (B + 1) < (supportCoeff {p : ℕ | p.Prime} (N + K + 1) : ℝ) ∧
      binaryCoeffTail (supportCoeff {p : ℕ | p.Prime}) (N + K) ≤ U ∧
      U - 1 < eps * 2 ^ K) :
    Irrational (erdosSupportSeries 2 {p : ℕ | p.Prime}) := by
  rw [erdosSupportSeries_two_eq_binaryCoeffSeries]
  exact irrational_binaryCoeffSeries_of_shiftedBlockWitnesses _
    (supportCoeff_le_self _) hwit

/-- The same statement with every hypothesis phrased in `omega`, via
`supportCoeff_primes_eq_card_primeFactors`.  This is Erdos problem 69 verbatim:
irrationality of `∑_p 1/(2^p - 1)`, conditional on the block witnesses. -/
theorem irrational_erdosSupportSeries_two_primes_of_omega_witnesses
    (hwit : ∀ eps : ℝ, 0 < eps → ∃ N K : ℕ, ∃ B U : ℝ, 0 < N ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ K →
        (N + j).primeFactors.card = j.primeFactors.card + 1) ∧
      binaryCoeffTail (fun n => n.primeFactors.card) K ≤ B ∧
      2 * (B + 1) < (((N + K + 1).primeFactors.card : ℕ) : ℝ) ∧
      binaryCoeffTail (fun n => n.primeFactors.card) (N + K) ≤ U ∧
      U - 1 < eps * 2 ^ K) :
    Irrational (erdosSupportSeries 2 {p : ℕ | p.Prime}) := by
  refine irrational_erdosSupportSeries_two_primes_of_shiftedBlockWitnesses ?_
  simpa only [supportCoeff_primes_eq_omega_fun, supportCoeff_primes_eq_card_primeFactors]
    using hwit



#print axioms binaryCoeffTail_supportCoeff_eq_tsum_shiftedSupportAtom
#print axioms binaryCoeffTail_supportCoeff_zero_strictMinimum
#print axioms binaryCoeffTail_supportCoeff_ne_initial_of_pos
#print axioms irrational_binaryCoeffSeries_of_strictInitialMin_of_closeReturn
#print axioms irrational_erdosSupportSeries_two_of_infinite_of_shiftedAtom_closeReturn
#print axioms sum_shiftedMersenneAtom_gcdOrbit
#print axioms sum_shiftedMersenneAtom_gcdOrbit_block
#print axioms tendsto_cesaroMean_shiftedMersenneAtom_mul
#print axioms cesaroMean_shiftedMersenneAtom_mul_le
#print axioms tendsto_cesaroMean_tsum_shiftedSupportAtom_mul
#print axioms tendsto_tsum_shiftedSupportOrbitMean_periodLcm
#print axioms exists_shiftedSupportAtom_closeReturn_of_summable_reciprocal
#print axioms irrational_erdosSupportSeries_two_of_summable_reciprocal
#print axioms coprime_succ_of_dvd
#print axioms coprime_cofactor_of_sq_dvd
#print axioms block_factorisation
#print axioms card_primeFactors_mul_of_coprime
#print axioms card_primeFactors_block_of_sq_dvd
#print axioms binaryCoeffTail_shifted_block_upper
#print axioms binaryCoeffTail_shifted_block_two_sided
#print axioms irrational_binaryCoeffSeries_of_shiftedBlockWitnesses
#print axioms irrational_erdosSupportSeries_two_primes_of_shiftedBlockWitnesses
#print axioms irrational_erdosSupportSeries_two_primes_of_omega_witnesses
#print axioms binaryCoeffTail_le_of_bound
#print axioms binaryCoeffTail_ge_head
#print axioms binaryCoeffTail_shifted_block_lower
#print axioms geom_sum_half
#print axioms binaryCoeffTail_split
#print axioms binaryCoeffTail_shifted_block
#print axioms irrational_binaryCoeffSeries_of_shiftedTwoSidedReturn
#print axioms irrational_binaryCoeffSeries_of_strictInitialMin_of_closeReturn_of_shifted
#print axioms shiftedBlockWitnesses_coeffBounds_unsatisfiable
#print axioms supportCoeff_primes_eq_omega_fun
#print axioms shiftedBlockWitness_forces_small_tail
#print axioms shiftedBlockWitness_forces_large_block
#print axioms socketRun_excludes_odd_coeff
#print axioms no_socketRun_of_odd_in_window
#print axioms no_two_powers_two_apart
#print axioms socketRun_forces_pow_le_coeff
#print axioms socketRun_forces_pow_le_of_le

end
end Erdos257PeriodNoncollapse
