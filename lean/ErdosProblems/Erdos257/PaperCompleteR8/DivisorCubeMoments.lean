import ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCubeCost
import ErdosProblems.Erdos257.PaperCompleteR8.OldCoverObstruction

/-! Exact first moments and a finite variance lower bound for divisor cubes.
No independence premise, limiting distribution, or coprimality with q is used.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset

theorem cubePrimeRank_zero_of_not_dvd (q : ℕ) (P : Finset ℕ) (n : ℕ)
    (hqn : ¬ q ∣ n) : cubePrimeRank q P n = 0 := by
  classical
  unfold cubePrimeRank
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact hqn ((dvd_mul_right q p).trans (mem_filter.mp hp).2)

theorem cube_log_incidence_exact (q : ℕ) (P : Finset ℕ) (n : ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hn : 0 < n) :
    Real.log (((divisorCube q P).filter (fun a => a ∣ n)).card : ℝ) =
      Real.log 2 * (cubePrimeRank q P n : ℝ) := by
  by_cases hqn : q ∣ n
  · rw [cube_incidence_exact q P n hq hP hn hqn]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mul_comm]
  · rw [cube_incidence_zero q P n hqn, cubePrimeRank_zero_of_not_dvd q P n hqn]
    simp

/-- A finite variance calculation restricted to the multiples of q.
Using the whole period without this restriction would lose a factor q. -/
theorem cube_rank_square_mean_lower (q : ℕ) (P : Finset ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) :
    (primeReciprocalMass P) ^ 2 / (q : ℝ) ≤
      (∑ n ∈ Icc 1 (q * P.prod id), (cubePrimeRank q P n : ℝ) ^ 2) /
        (q * P.prod id : ℕ) := by
  classical
  let X := q * P.prod id
  let T := (Icc 1 X).filter (fun n => q ∣ n)
  let S := primeReciprocalMass P
  let r : ℕ → ℝ := fun n => cubePrimeRank q P n
  have hX : 0 < X := Nat.mul_pos hq (prime_product_pos P hP)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hM : (0 : ℝ) < ((P.prod id : ℕ) : ℝ) := by exact_mod_cast prime_product_pos P hP
  have hcard : (T.card : ℝ) = ((P.prod id : ℕ) : ℝ) := by
    dsimp [T, X]
    rw [card_Icc_one_filter_dvd hq,
      Nat.cast_div (dvd_mul_right q (P.prod id)) (by exact_mod_cast hq.ne')]
    push_cast
    field_simp
  have hr0 : ∀ n, ¬ q ∣ n → r n = 0 := by
    intro n hn
    simp only [r, cubePrimeRank_zero_of_not_dvd q P n hn, Nat.cast_zero]
  have hsumr : (∑ n ∈ T, r n) = ∑ n ∈ Icc 1 X, r n := by
    unfold T
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hd : q ∣ n
    · simp [hd]
    · simp [hd, hr0 n hd]
  have hsumr2 : (∑ n ∈ T, r n ^ 2) = ∑ n ∈ Icc 1 X, r n ^ 2 := by
    unfold T
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hd : q ∣ n
    · simp [hd]
    · simp [hd, hr0 n hd]
  have hfirst : (∑ n ∈ T, r n) = ((P.prod id : ℕ) : ℝ) * S := by
    rw [hsumr]
    have h := cubePrimeRank_mean q P hq hP
    have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
    have he := (div_eq_iff hX0).mp h
    change (∑ n ∈ Icc 1 X, r n) = S / (q : ℝ) * (X : ℝ) at he
    rw [he]
    dsimp [X]
    push_cast
    field_simp
    <;> ring
  have hvariance : 0 ≤ ∑ n ∈ T, (r n - S) ^ 2 :=
    Finset.sum_nonneg (fun n hn => sq_nonneg _)
  have hexpand : (∑ n ∈ T, (r n - S) ^ 2) =
      (∑ n ∈ T, r n ^ 2) - 2 * S * (∑ n ∈ T, r n) + (T.card : ℝ) * S ^ 2 := by
    calc
      _ = ∑ n ∈ T, (r n ^ 2 - 2 * S * r n + S ^ 2) := by
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hexpand, hfirst, hcard] at hvariance
  have hb : ((P.prod id : ℕ) : ℝ) * S ^ 2 ≤ ∑ n ∈ T, r n ^ 2 := by nlinarith
  rw [hsumr2] at hb
  apply (div_le_div_iff₀ hqR (by exact_mod_cast hX)).mpr
  have hm := mul_le_mul_of_nonneg_left hb hqR.le
  simp only [X, r, S] at hm
  rw [Nat.cast_mul]
  nlinarith only [hm]

/-- The exact old-cover obstruction constant on a finite cube. -/
theorem cube_logSquare_mean_lower (q : ℕ) (P : Finset ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) :
    (Real.log 2) ^ 2 * (primeReciprocalMass P) ^ 2 / (2 * (q : ℝ)) ≤
      finiteLogSquareMean (divisorCube q P) (q * P.prod id) := by
  have h := mul_le_mul_of_nonneg_left (cube_rank_square_mean_lower q P hq hP)
    (div_nonneg (sq_nonneg (Real.log 2)) (by norm_num : (0 : ℝ) ≤ 2))
  have heq : finiteLogSquareMean (divisorCube q P) (q * P.prod id) =
      ((Real.log 2) ^ 2 / 2) *
        ((∑ n ∈ Icc 1 (q * P.prod id), (cubePrimeRank q P n : ℝ) ^ 2) /
          (q * P.prod id : ℕ)) := by
    unfold finiteLogSquareMean
    have hs : (∑ n ∈ Icc 1 (q * P.prod id),
        (Real.log (((divisorCube q P).filter (fun a => a ∣ n)).card : ℝ)) ^ 2 / 2) =
        ∑ n ∈ Icc 1 (q * P.prod id),
          ((Real.log 2) ^ 2 / 2) * (cubePrimeRank q P n : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [cube_log_incidence_exact q P n hq hP (mem_Icc.mp hn).1]
      ring
    rw [hs, ← Finset.mul_sum]
    ring
  rw [heq]
  convert h using 1 <;> ring

/-- Logarithmic lower bound on every Euler-product factor in the needed range. -/
theorem half_le_log_one_add {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) := by
  have hpos : 0 < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have hlow : x / (1 + x) ≤ Real.log (1 + x) := by
    have hi : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    linarith
  have hratio : x / 2 ≤ x / (1 + x) :=
    div_le_div_of_nonneg_left hx hpos (by linarith)
  exact hratio.trans hlow

/-- A lower product bound sufficient for both reciprocal and fixed-alpha divergence. -/
theorem cubeProductCost_exp_lower (q : ℕ) (P : Finset ℕ) (z : ℝ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp (z * primeReciprocalMass P / 2) / (q : ℝ) ≤ cubeProductCost q P z := by
  have hx : ∀ p ∈ P, 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 := by
    intro p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    refine ⟨div_nonneg hz hpR.le, (div_le_one hpR).mpr ?_⟩
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_lt.le
    linarith
  have hprod : (∏ p ∈ P, Real.exp ((z / (p : ℝ)) / 2)) ≤
      ∏ p ∈ P, (1 + z / (p : ℝ)) := by
    apply Finset.prod_le_prod
    · intro p hp; exact (Real.exp_pos _).le
    · intro p hp
      have h := Real.exp_le_exp.mpr (half_le_log_one_add (hx p hp).1 (hx p hp).2)
      rwa [Real.exp_log (by linarith [(hx p hp).1] : 0 < 1 + z / (p : ℝ))] at h
  have he : (∏ p ∈ P, Real.exp ((z / (p : ℝ)) / 2)) =
      Real.exp (z * primeReciprocalMass P / 2) := by
    rw [← Real.exp_sum]
    congr 1
    unfold primeReciprocalMass
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [he] at hprod
  have h := mul_le_mul_of_nonneg_left hprod (one_div_nonneg.mpr (Nat.cast_nonneg q))
  simpa [cubeProductCost, div_eq_mul_inv, mul_comm] using h

/-- A polynomial lower bound avoids any unproved asymptotic comparison. -/
theorem cubeProductCost_quadratic_lower (q : ℕ) (P : Finset ℕ) (z : ℝ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    z ^ 2 * (primeReciprocalMass P) ^ 2 / (4 * (q : ℝ)) ≤ cubeProductCost q P z := by
  have hS : 0 ≤ primeReciprocalMass P := Finset.sum_nonneg
    (fun p hp => one_div_nonneg.mpr (Nat.cast_nonneg p))
  have h := div_le_div_of_nonneg_right
    (sq_le_exp_of_nonneg (div_nonneg (mul_nonneg hz hS) (by norm_num : (0 : ℝ) ≤ 2))) (Nat.cast_nonneg q)
  have heq : (z * primeReciprocalMass P / 2) ^ 2 / (q : ℝ) =
      z ^ 2 * (primeReciprocalMass P) ^ 2 / (4 * (q : ℝ)) := by ring
  rw [heq] at h
  exact h.trans (cubeProductCost_exp_lower q P z hP hz hz1)

theorem cube_reciprocal_sum (q : ℕ) (P : Finset ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ a ∈ divisorCube q P, (1 : ℝ) / a) = cubeProductCost q P 1 := by
  classical
  rw [divisorCube, Finset.sum_image]
  · calc
      _ = (1 / (q : ℝ)) * ∑ d ∈ (P.prod id).divisors, (1 : ℝ) / d := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        push_cast
        ring
      _ = _ := by rw [reciprocal_divisor_prime_product P hP]; rfl
  · intro a ha b hb heq
    exact Nat.eq_of_mul_eq_mul_left hq heq

end ErdosProblems.Erdos257.PaperCompleteR8
end
