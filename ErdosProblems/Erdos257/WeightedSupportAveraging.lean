import Erdos257PeriodNoncollapse.ReciprocalSupportIrrationality

/-!
# Finite averaging for divisibility-weighted supports

The weighted support proof needs two finite estimates before taking any
limit. The orbit estimate retains the geometric GCD factor discarded by the
reciprocal-mass bound. The observation-length estimate sums incomplete-period
errors across dyadic scales, charging each conductor only once.

These are the actual finite estimates used in the analytic proof. The
prime-part decomposition and the final choice of scales are separate steps.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse TotientTailPeriodKiller

noncomputable section

/-- Retain the geometric factor in both full blocks and the incomplete block. -/
theorem sum_shiftedMersenneAtom_mul_le_gcdBlockCount
    (Q d K : ℕ) (hQ : 0 < Q) (hd : 0 < d) :
    ∑ k ∈ Finset.range K, shiftedMersenneAtom ((k + 1) * Q) d ≤
      (((K / (d / Nat.gcd Q d) : ℕ) : ℝ) + 1) /
        ((2 : ℝ) ^ Nat.gcd Q d - 1) := by
  let g := Nat.gcd Q d
  let h := d / g
  let B : ℝ := 1 / ((2 : ℝ) ^ g - 1)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hQ
  have hh : 0 < h := Nat.div_pos (Nat.gcd_le_right Q hd) hg
  have hblock : ∀ q : ℕ,
      ∑ j ∈ Finset.range h,
        shiftedMersenneAtom (((q * h + j) + 1) * Q) d = B := by
    intro q
    simpa [g, h, B, add_assoc] using
      sum_shiftedMersenneAtom_gcdOrbit_block Q d hQ hd q
  have hr := blockRemainder_le_blockSum
    (fun k => shiftedMersenneAtom ((k + 1) * Q) d) h B hh
    (fun k => shiftedMersenneAtom_nonneg ((k + 1) * Q) d) hblock K
  rw [sum_range_eq_mul_blockSum_add_blockRemainder _ h B hblock K]
  calc
    ((K / h : ℕ) : ℝ) * B +
        blockRemainder (fun k => shiftedMersenneAtom ((k + 1) * Q) d) h K ≤
        ((K / h : ℕ) : ℝ) * B + B := add_le_add le_rfl hr
    _ = _ := by dsimp [B, h, g]; ring

/-- The error of a finite progression average is at most one GCD orbit. -/
theorem cesaroMean_shiftedMersenneAtom_mul_le_gcdMean_add_error
    (Q d K : ℕ) (hQ : 0 < Q) (hd : 0 < d) (hK : 0 < K) :
    cesaroMean (fun k => shiftedMersenneAtom ((k + 1) * Q) d) K ≤
      (Nat.gcd Q d : ℝ) /
        ((d : ℝ) * ((2 : ℝ) ^ Nat.gcd Q d - 1)) +
      1 / ((K : ℝ) * ((2 : ℝ) ^ Nat.gcd Q d - 1)) := by
  let g := Nat.gcd Q d
  let h := d / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hQ
  have hh : 0 < h := Nat.div_pos (Nat.gcd_le_right Q hd) hg
  have hdFac : g * h = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right Q d)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hden : (0 : ℝ) < (2 : ℝ) ^ g - 1 := by
    have := one_lt_pow₀ (a := (2 : ℝ)) (by norm_num) hg.ne'
    linarith
  have hratio : (K : ℝ) / h = (K : ℝ) * g / d := by
    rw [← hdFac]
    push_cast
    field_simp
  have hquot : ((K / h : ℕ) : ℝ) ≤ (K : ℝ) * g / d := by
    rw [← hratio]
    exact Nat.cast_div_le
  have hsum := sum_shiftedMersenneAtom_mul_le_gcdBlockCount Q d K hQ hd
  unfold cesaroMean
  calc
    _ ≤ ((((K / h : ℕ) : ℝ) + 1) / ((2 : ℝ) ^ g - 1)) / K := by
      exact div_le_div_of_nonneg_right hsum hKR.le
    _ ≤ (((K : ℝ) * g / d + 1) / ((2 : ℝ) ^ g - 1)) / K := by
      gcongr
    _ = _ := by dsimp [g]; field_simp <;> ring

/-- A finite geometric tail, indexed by an arbitrary finite set. -/
theorem sum_half_pow_le_twice_min (s : Finset ℕ) (m : ℕ)
    (hm : ∀ j ∈ s, m ≤ j) :
    ∑ j ∈ s, (1 / 2 : ℝ) ^ j ≤ 2 * (1 / 2 : ℝ) ^ m := by
  classical
  have hinj : Set.InjOn (fun j : ℕ => j - m) s := by
    intro i hi j hj hij
    have := hm i hi
    have := hm j hj
    dsimp at hij
    omega
  have hgeom := summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  have htail : ∑ j ∈ s, (1 / 2 : ℝ) ^ (j - m) ≤ 2 := by
    rw [← Finset.sum_image hinj]
    calc
      _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n :=
        hgeom.sum_le_tsum _ (fun _ _ => by positivity)
      _ = 2 := by rw [tsum_geometric_of_abs_lt_one (by norm_num)]; norm_num
  calc
    ∑ j ∈ s, (1 / 2 : ℝ) ^ j =
        (1 / 2 : ℝ) ^ m * ∑ j ∈ s, (1 / 2 : ℝ) ^ (j - m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← pow_add, Nat.add_sub_of_le (hm j hj)]
    _ ≤ (1 / 2 : ℝ) ^ m * 2 := mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

/-- A conductor's dyadic observation weights have total mass at most `2Q/a`.
No infinite sum or interchange of limits occurs. -/
theorem sum_dyadic_observation_weights_le (J : Finset ℕ) (Q a : ℕ)
    (ha : 0 < a) :
    ∑ j ∈ J.filter (fun j => a ≤ Q * 2 ^ j), (1 / 2 : ℝ) ^ j ≤
      2 * (Q : ℝ) / a := by
  classical
  let s := J.filter (fun j => a ≤ Q * 2 ^ j)
  by_cases hs : s.Nonempty
  · let m := s.min' hs
    have hm : m ∈ s := Finset.min'_mem _ hs
    have ham : a ≤ Q * 2 ^ m := (Finset.mem_filter.mp hm).2
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hamR : (a : ℝ) ≤ (Q : ℝ) * (2 : ℝ) ^ m := by exact_mod_cast ham
    have hmul : (1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    have hscale := mul_le_mul_of_nonneg_left hamR
      (show 0 ≤ (1 / 2 : ℝ) ^ m by positivity)
    have hproduct : (1 / 2 : ℝ) ^ m * ((Q : ℝ) * (2 : ℝ) ^ m) = Q := by
      calc
        _ = (Q : ℝ) * ((1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m) := by ring
        _ = Q := by rw [hmul]; ring
    rw [hproduct] at hscale
    have hbound : 2 * (1 / 2 : ℝ) ^ m ≤ 2 * (Q : ℝ) / a := by
      rw [le_div_iff₀ haR]
      nlinarith
    exact (sum_half_pow_le_twice_min s m
      (fun j hj => Finset.min'_le s j hj)).trans hbound
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (∑ j ∈ s, (1 / 2 : ℝ) ^ j) ≤ _
    rw [this]
    simp only [Finset.sum_empty]
    positivity

/-- The finite weighted dyadic averaging inequality used to control the
incomplete-period term when the ordinary reciprocal mass diverges. -/
theorem dyadic_observation_sum_le (J F : Finset ℕ) (Q : ℕ) (α : ℕ → ℝ)
    (hF : ∀ a ∈ F, 0 < a) (hα : ∀ a ∈ F, 0 ≤ α a) :
    (∑ j ∈ J, (1 / 2 : ℝ) ^ j *
      ∑ a ∈ F.filter (fun a => a ≤ Q * 2 ^ j), α a) ≤
      2 * (Q : ℝ) * ∑ a ∈ F, α a / a := by
  classical
  calc
    _ = ∑ a ∈ F, α a *
        ∑ j ∈ J.filter (fun j => a ≤ Q * 2 ^ j), (1 / 2 : ℝ) ^ j := by
      simp only [Finset.sum_filter, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring
    _ ≤ ∑ a ∈ F, α a * (2 * (Q : ℝ) / a) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left
        (sum_dyadic_observation_weights_le J Q a (hF a ha)) (hα a ha)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha; ring

#print axioms dyadic_observation_sum_le
#print axioms cesaroMean_shiftedMersenneAtom_mul_le_gcdMean_add_error

end
end ErdosProblems.Erdos257
