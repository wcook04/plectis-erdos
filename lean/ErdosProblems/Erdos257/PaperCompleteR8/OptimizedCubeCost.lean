import ErdosProblems.Erdos257.PaperCompleteR8.DivisorCubeProduct
import ErdosProblems.Erdos257.PaperCompleteR8.CoverGaugeComplete

/-!
# Optimised finite divisor-cube cost, with positive epsilon padding

The upper bound e*S/q requires S >= 1. The valid general bound is exp(S)/q.
The q multiplier can share primes with P. Infima need not be attained.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset Filter

def exponentFromIncrement (z : ℝ) : ℝ := Real.log (1 + z) / Real.log 2

theorem exponentFromIncrement_bounds {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    0 < exponentFromIncrement z ∧ exponentFromIncrement z ≤ 1 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : (1 : ℝ) < 1 + z := by linarith
  have hbu : 1 + z ≤ (2 : ℝ) := by linarith
  constructor
  · exact div_pos (Real.log_pos hb) hl
  · exact (div_le_one hl).mpr (Real.log_le_log (by linarith) hbu)

theorem two_rpow_exponentFromIncrement {z : ℝ} (hz : 0 < z) :
    (2 : ℝ) ^ exponentFromIncrement z = 1 + z := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have he : Real.log 2 * exponentFromIncrement z = Real.log (1 + z) := by
    unfold exponentFromIncrement
    field_simp
  rw [he, Real.exp_log (by linarith : 0 < 1 + z)]

theorem cubePrimeRank_cast (q : ℕ) (P : Finset ℕ) (n : ℕ) :
    (cubePrimeRank q P n : ℝ) = ∑ p ∈ P, if q * p ∣ n then (1 : ℝ) else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp only [cubePrimeRank, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem cubePrimeRank_mean (q : ℕ) (P : Finset ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ n ∈ Icc 1 (q * P.prod id), (cubePrimeRank q P n : ℝ)) /
      (q * P.prod id : ℕ) = primeReciprocalMass P / (q : ℝ) := by
  classical
  simp_rw [cubePrimeRank_cast]
  rw [mean_finite_divisor_atoms]
  · unfold primeReciprocalMass
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    push_cast
    ring
  · exact Nat.mul_pos hq (prime_product_pos P hP)
  · intro p hp
    exact Nat.mul_pos hq (hP p hp).pos
  · intro p hp
    exact Nat.mul_dvd_mul_left q (Finset.dvd_prod_of_mem id hp)

/-- A pointwise lower bound with the correct off-q zero term. -/
theorem cube_gauge_rank_lower (q : ℕ) (P : Finset ℕ) (n : ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hn : 0 < n) :
    Real.exp 1 * ((cubePrimeRank q P n : ℝ) - (if q ∣ n then 1 else 0)) ≤
      coverGauge (((divisorCube q P).filter (fun a => a ∣ n)).card : ℝ) := by
  classical
  by_cases hqn : q ∣ n
  · rw [if_pos hqn, cube_incidence_exact q P n hq hP hn hqn]
    have h := exp_one_mul_sub_one_le_coverGauge_two_rpow (cubePrimeRank q P n : ℝ)
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using h
  · have hr : cubePrimeRank q P n = 0 := by
      unfold cubePrimeRank
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hqn ((dvd_mul_right q p).trans (Finset.mem_filter.mp hp).2)
    simp only [if_neg hqn, hr, Nat.cast_zero, sub_zero, mul_zero]
    exact coverGauge_nonneg (Nat.cast_nonneg _)

theorem cube_gauge_mean_lower (q : ℕ) (P : Finset ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) :
    Real.exp 1 * (primeReciprocalMass P - 1) / (q : ℝ) ≤
      finiteGaugeMean (divisorCube q P) (q * P.prod id) := by
  classical
  have hX : 0 < q * P.prod id := Nat.mul_pos hq (prime_product_pos P hP)
  have hs := Finset.sum_le_sum (s := Icc 1 (q * P.prod id))
    (fun n hn => cube_gauge_rank_lower q P n hq hP (mem_Icc.mp hn).1)
  have hm := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (q * P.prod id))
  have heq : (∑ n ∈ Icc 1 (q * P.prod id),
      Real.exp 1 * ((cubePrimeRank q P n : ℝ) - (if q ∣ n then 1 else 0))) /
      (q * P.prod id : ℕ) = Real.exp 1 * (primeReciprocalMass P - 1) / (q : ℝ) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    have hr := cubePrimeRank_mean q P hq hP
    have hqmean := mean_divisibility_atom q (q * P.prod id) hq hX (dvd_mul_right _ _) 1
    calc
      _ = Real.exp 1 *
          ((∑ n ∈ Icc 1 (q * P.prod id), (cubePrimeRank q P n : ℝ)) /
              (q * P.prod id : ℕ) -
           (∑ n ∈ Icc 1 (q * P.prod id), if q ∣ n then (1 : ℝ) else 0) /
              (q * P.prod id : ℕ)) := by ring
      _ = _ := by rw [hr, hqmean]; ring
  rw [heq] at hm
  exact hm

/-- The exact lower bound applies to every actual countable cover. -/
theorem cube_every_cover_cost_lower (q : ℕ) (P : Finset ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p)
    (C : LogBudgetCover (divisorCube q P : Set ℕ)) :
    max 0 (Real.exp 1 * (primeReciprocalMass P - 1) / (q : ℝ)) ≤ C.cost := by
  apply max_le C.cost_nonneg
  exact (cube_gauge_mean_lower q P hq hP).trans
    (finiteGaugeMean_le_cost C _ (Set.Subset.refl _) _
      (Nat.mul_pos hq (prime_product_pos P hP)))

theorem optimized_cube_cost_lower (q : ℕ) (P : Finset ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) :
    max 0 (Real.exp 1 * (primeReciprocalMass P - 1) / (q : ℝ)) ≤
      optimizedLogCoverCost (divisorCube q P : Set ℕ) := by
  let F := cubeCoverFrame q P 1 hq hP (by norm_num) le_rfl
  let C := F.padded (1 / 2) (by norm_num) (by norm_num)
  apply le_csInf (show (admissibleLogCoverCosts (divisorCube q P : Set ℕ)).Nonempty from
    ⟨C.cost, C, rfl⟩)
  rintro _ ⟨D, rfl⟩
  exact cube_every_cover_cost_lower q P hq hP D

/-- General upper bound for every admissible increment 0<z<=1. -/
theorem optimized_cube_cost_le_increment (q : ℕ) (P : Finset ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (z : ℝ) (hz : 0 < z) (hz1 : z ≤ 1) :
    optimizedLogCoverCost (divisorCube q P : Set ℕ) ≤
      Real.exp (z * primeReciprocalMass P) / ((q : ℝ) * z) := by
  obtain ⟨hα, hα1⟩ := exponentFromIncrement_bounds hz hz1
  let F := cubeCoverFrame q P (exponentFromIncrement z) hq hP hα hα1
  have h := F.optimizedCost_le
  have hF : F.scalarCost = cubeProductCost q P z / z := by
    unfold FiniteCoverFrame.scalarCost
    rw [cubeCoverFrame_cost, show F.exponent = exponentFromIncrement z from rfl,
      two_rpow_exponentFromIncrement hz]
    simp only [add_sub_cancel_left]
  rw [hF] at h
  exact h.trans (by
    have hb := div_le_div_of_nonneg_right (cubeProductCost_le_exp q P z hz.le) hz.le
    simpa only [div_div] using hb)

/-- The universally valid bound, including S<1 and P empty. -/
theorem optimized_cube_cost_le_exp (q : ℕ) (P : Finset ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) :
    optimizedLogCoverCost (divisorCube q P : Set ℕ) ≤
      Real.exp (primeReciprocalMass P) / (q : ℝ) := by
  simpa using optimized_cube_cost_le_increment q P hq hP 1 (by norm_num) le_rfl

/-- Corrected optimised theorem: the S>=1 hypothesis is essential. -/
theorem optimized_cube_cost_two_sided (q : ℕ) (P : Finset ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hS : 1 ≤ primeReciprocalMass P) :
    max 0 (Real.exp 1 * (primeReciprocalMass P - 1) / (q : ℝ)) ≤
      optimizedLogCoverCost (divisorCube q P : Set ℕ) ∧
    optimizedLogCoverCost (divisorCube q P : Set ℕ) ≤
      Real.exp 1 * primeReciprocalMass P / (q : ℝ) := by
  refine ⟨optimized_cube_cost_lower q P hq hP, ?_⟩
  have hSpos : 0 < primeReciprocalMass P := by linarith
  have hz : 0 < (1 : ℝ) / primeReciprocalMass P := one_div_pos.mpr hSpos
  have hz1 : (1 : ℝ) / primeReciprocalMass P ≤ 1 := (div_le_one hSpos).mpr hS
  have h := optimized_cube_cost_le_increment q P hq hP _ hz hz1
  have harg : (1 : ℝ) / primeReciprocalMass P * primeReciprocalMass P = 1 := by
    field_simp
  rw [harg] at h
  convert h using 1 <;> field_simp <;> ring

/-- A nonempty cube contains its mandatory factor q. -/
theorem factor_mem_divisorCube (q : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) : q ∈ divisorCube q P := by
  classical
  rw [divisorCube_eq_powerset_image q P hP]
  exact mem_image.mpr ⟨∅, by simp, by simp⟩

theorem finiteGaugeMean_singleton (q : ℕ) (hq : 0 < q) :
    finiteGaugeMean {q} q = 1 / (q : ℝ) := by
  classical
  have hψ : coverGauge 1 = 1 := coverGauge_eq_self_of_one_le_le_four le_rfl (by norm_num)
  unfold finiteGaugeMean
  have heq : (∑ n ∈ Icc 1 q, coverGauge ((({q} : Finset ℕ).filter (fun a => a ∣ n)).card : ℝ)) =
      ∑ n ∈ Icc 1 q, if q ∣ n then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : q ∣ n
    · simp [Finset.filter_singleton, h, hψ]
    · simp [Finset.filter_singleton, h]
  rw [heq]
  exact mean_divisibility_atom q q hq hq dvd_rfl 1

theorem one_div_factor_le_optimized_cube_cost (q : ℕ) (P : Finset ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) :
    1 / (q : ℝ) ≤ optimizedLogCoverCost (divisorCube q P : Set ℕ) := by
  let C := (cubeCoverFrame q P 1 hq hP (by norm_num) le_rfl).padded
    (1 / 2) (by norm_num) (by norm_num)
  have hsub : (({q} : Finset ℕ) : Set ℕ) ⊆ (divisorCube q P : Set ℕ) := by
    intro a ha
    have : a = q := by simpa using ha
    subst a
    exact factor_mem_divisorCube q P hP
  have h := finiteGaugeMean_le_optimizedCost C {q} hsub q hq
  rwa [finiteGaugeMean_singleton q hq] at h

/-- The empty prime cube is a singleton, and its infimum is exactly 1/q. -/
theorem optimized_cube_cost_empty (q : ℕ) (hq : 0 < q) :
    optimizedLogCoverCost (divisorCube q ∅ : Set ℕ) = 1 / (q : ℝ) := by
  apply le_antisymm
  · simpa [primeReciprocalMass] using optimized_cube_cost_le_exp q ∅ hq (by simp)
  · exact one_div_factor_le_optimized_cube_cost q ∅ hq (by simp)

/-- Exact counterexample to the unqualified e*S/q assertion. -/
theorem unrestricted_linear_cube_upper_bound_false :
    ¬ (∀ (q : ℕ) (P : Finset ℕ), 0 < q → (∀ p ∈ P, Nat.Prime p) →
      optimizedLogCoverCost (divisorCube q P : Set ℕ) ≤
        Real.exp 1 * primeReciprocalMass P / (q : ℝ)) := by
  intro h
  have hh := h 1 ∅ (by decide) (by simp)
  rw [optimized_cube_cost_empty 1 (by decide)] at hh
  norm_num [primeReciprocalMass] at hh

end ErdosProblems.Erdos257.PaperCompleteR8
end
