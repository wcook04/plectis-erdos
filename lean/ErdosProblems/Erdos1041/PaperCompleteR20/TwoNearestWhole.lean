import ErdosProblems.Erdos1041.CriticalTwoRootProximity
import ErdosProblems.Erdos1041.PaperReflectedBoundary

/-! Derive the two-nearest-root distance bound from the actual open-disc
locations and critical logarithmic balance, without assumed geometric budgets. -/
namespace ErdosProblems.Erdos1041.PaperCompleteR20
open scoped BigOperators
open Finset Polynomial

private theorem disk_inverse_square_bound {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℂ) (c : ℂ) (hz : ∀ k, ‖z k‖ < 1)
    (hne : ∀ k, c - z k ≠ 0) (hcrit : ∑ k, (c - z k)⁻¹ = 0) :
    (n : ℝ) < (1 - ‖c‖ ^ 2) * ∑ k, 1 / ‖c - z k‖ ^ 2 := by
  have hpoint (k : Fin n) :
      1 - 2 * (c / (c - z k)).re < (1 - ‖c‖ ^ 2) / ‖c - z k‖ ^ 2 := by
    have H := PaperReflectedBoundary.radial_fraction_identity c (z k) (hne k)
    simp only [Complex.normSq_eq_norm_sq] at H
    apply (lt_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr (hne k)))).mpr
    nlinarith [hz k, norm_nonneg (z k)]
  have hsum := Finset.sum_lt_sum (s := Finset.univ)
    (fun k _ => (hpoint k).le) ⟨⟨0, hn⟩, mem_univ _, hpoint _⟩
  have hzero : ∑ k, (c / (c - z k)).re = 0 := by
    rw [← Complex.re_sum]
    simp only [div_eq_mul_inv, ← Finset.mul_sum, hcrit, mul_zero, Complex.zero_re]
  simp only [div_eq_mul_inv] at hzero
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, mul_zero,
    sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, div_eq_mul_inv, one_mul] using hsum

theorem two_nearest_roots_open_disc {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (c : ℂ) (hz : ∀ k, ‖z k‖ < 1)
    (hne : ∀ k, c - z k ≠ 0) (hcrit : ∑ k, (c - z k)⁻¹ = 0)
    (i j : Fin n) (hij : i ≠ j)
    (hi : ∀ k, ‖c - z i‖ ≤ ‖c - z k‖)
    (hj : ∀ k, k ≠ i → ‖c - z j‖ ≤ ‖c - z k‖) :
    ‖c - z i‖ + ‖c - z j‖ < 2 := by
  classical
  let d : Fin n → ℝ := fun k => ‖c - z k‖
  have hdpos : ∀ k, 0 < d k := fun k => norm_pos_iff.mpr (hne k)
  have hdi := hdpos i
  have hdj := hdpos j
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcard : (univ.erase i).card = n - 1 := by simp
  have hn1R : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hbal : d j ≤ ((n : ℝ) - 1) * d i := by
    have hsum := Finset.add_sum_erase univ (fun k => (c - z k)⁻¹) (mem_univ i)
    rw [hcrit] at hsum
    have hsplit : (c - z i)⁻¹ = -∑ k ∈ univ.erase i, (c - z k)⁻¹ := by
      linear_combination hsum
    have hnorm : (d i)⁻¹ ≤ ∑ k ∈ univ.erase i, (d k)⁻¹ := by
      calc (d i)⁻¹ = ‖(c - z i)⁻¹‖ := by rw [norm_inv]
           _ = ‖∑ k ∈ univ.erase i, (c - z k)⁻¹‖ := by rw [hsplit, norm_neg]
           _ ≤ ∑ k ∈ univ.erase i, ‖(c - z k)⁻¹‖ := norm_sum_le _ _
           _ = ∑ k ∈ univ.erase i, (d k)⁻¹ := by
             exact Finset.sum_congr rfl fun k _ => by rw [norm_inv]
    have hbound : ∑ k ∈ univ.erase i, (d k)⁻¹ ≤ ((n : ℝ) - 1) * (d j)⁻¹ := by
      calc ∑ k ∈ univ.erase i, (d k)⁻¹ ≤ ∑ _k ∈ univ.erase i, (d j)⁻¹ := by
             exact Finset.sum_le_sum fun k hk => inv_anti₀ hdj (hj k (mem_erase.mp hk).1)
           _ = ((n : ℝ) - 1) * (d j)⁻¹ := by
             rw [Finset.sum_const, nsmul_eq_mul, hcard, hn1R]
    have hmul := mul_le_mul_of_nonneg_right (hnorm.trans hbound)
      (by positivity : (0 : ℝ) ≤ d i * d j)
    have hL : (d i)⁻¹ * (d i * d j) = d j := by field_simp
    have hR : (((n : ℝ) - 1) * (d j)⁻¹) * (d i * d j) = ((n : ℝ) - 1) * d i := by
      field_simp
    rwa [hL, hR] at hmul
  let S : ℝ := ∑ k, 1 / d k ^ 2
  let A : ℝ := 1 - ‖c‖ ^ 2
  have hstar : (n : ℝ) < A * S := disk_inverse_square_bound (by omega) z c hz hne hcrit
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ => by positivity)
  have hA : 0 < A := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hS
    linarith
  have hc : ‖c‖ < 1 := by dsimp [A] at hA; nlinarith [norm_nonneg c]
  have hupper : S ≤ (n : ℝ) / d i ^ 2 := by
    calc S ≤ ∑ _k : Fin n, 1 / d i ^ 2 := by
           exact Finset.sum_le_sum (fun k _ => one_div_le_one_div_of_le
             (sq_pos_of_pos hdi) (sq_le_sq₀ hdi.le (hdpos k).le |>.mpr (hi k)))
         _ = (n : ℝ) / d i ^ 2 := by simp [div_eq_mul_inv]
  have hδ1 : d i ≤ 1 := by
    have H := hstar.trans_le (mul_le_mul_of_nonneg_left hupper hA.le)
    have H' : (n : ℝ) * d i ^ 2 < A * n := by
      apply (lt_div_iff₀ (sq_pos_of_pos hdi)).mp
      simpa only [← mul_div_assoc] using H
    have hAsmall : A ≤ 1 := by dsimp [A]; nlinarith [sq_nonneg ‖c‖]
    nlinarith [mul_le_mul_of_nonneg_right hAsmall (by positivity : (0 : ℝ) ≤ n)]
  have hupper2 : S ≤ 1 / d i ^ 2 + ((n : ℝ) - 1) / d j ^ 2 := by
    rw [show S = 1 / d i ^ 2 + ∑ k ∈ univ.erase i, 1 / d k ^ 2 from
      (Finset.add_sum_erase _ _ (mem_univ i)).symm]
    gcongr
    calc ∑ k ∈ univ.erase i, 1 / d k ^ 2 ≤ ∑ _k ∈ univ.erase i, 1 / d j ^ 2 := by
           exact Finset.sum_le_sum fun k hk => one_div_le_one_div_of_le
             (sq_pos_of_pos hdj) (sq_le_sq₀ hdj.le (hdpos k).le |>.mpr (hj k (mem_erase.mp hk).1))
         _ = ((n : ℝ) - 1) / d j ^ 2 := by
           rw [Finset.sum_const, nsmul_eq_mul, hcard, hn1R]; ring
  apply two_add_lt_two_of_disk_inverse_balance_of_strict_diameter hnR hc hdi
    (hi j) hδ1
  · exact (norm_sub_le c (z j)).trans_lt (by linarith [hz j])
  · exact hbal
  · exact hstar.le.trans (mul_le_mul_of_nonneg_left hupper2 hA.le)

#print axioms two_nearest_roots_open_disc
end ErdosProblems.Erdos1041.PaperCompleteR20
