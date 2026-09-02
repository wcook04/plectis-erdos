import Mathlib

open scoped ComplexConjugate

namespace Erdos249257.ExternalVerification1041SignedMomentTetranomial

/-- Exact finite-family energy identity, including the signed mixed moment. -/
theorem sum_normSq_const_add_mul
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c : ℂ) :
    ∑ i ∈ S, Complex.normSq (c + b * v i) =
      (S.card : ℝ) * Complex.normSq c +
        Complex.normSq b * ∑ i ∈ S, Complex.normSq (v i) +
          2 * (conj c * b * (∑ i ∈ S, v i)).re := by
  sorry

/-- Energy below `card S - 1` forces two distinct strict unit tails. -/
theorem exists_two_tails_norm_lt_one_of_exact_L2_budget
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c : ℂ)
    (hcard : 2 ≤ S.card)
    (hbudget :
      (S.card : ℝ) * Complex.normSq c +
          Complex.normSq b * ∑ i ∈ S, Complex.normSq (v i) +
            2 * (conj c * b * (∑ i ∈ S, v i)).re <
        (S.card : ℝ) - 1) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      ‖c + b * v i‖ < 1 ∧ ‖c + b * v j‖ < 1 := by
  sorry

/-- Finite indexed-root form: the signed moment budget selects two distinct
indices whose complete tetranomial spokes lie strictly below one. Distinct
root values additionally require injectivity of `w`. -/
theorem exists_two_tetranomialRoot_safeSpokes_of_moment_coeff_budget
    {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    {m r s : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hrm : r ≤ m)
    {a b c moment : ℂ}
    (hcard : 2 ≤ S.card)
    (hroot : ∀ i ∈ S, w i ^ m + a * w i ^ r + b * w i ^ s + c = 0)
    (hw : ∀ i ∈ S, ‖w i‖ < 1) (hc : ‖c‖ < 1)
    (hmoment : ∑ i ∈ S, w i ^ s = moment)
    (hcoeff :
      (S.card : ℝ) * (Complex.normSq b + Complex.normSq c) +
          2 * (conj c * b * moment).re <
        (S.card : ℝ) - 1) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(u : ℂ) ^ m * w i ^ m + a * (u : ℂ) ^ r * w i ^ r +
          b * (u : ℂ) ^ s * w i ^ s + c‖ < 1) ∧
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(u : ℂ) ^ m * w j ^ m + a * (u : ℂ) ^ r * w j ^ r +
          b * (u : ℂ) ^ s * w j ^ s + c‖ < 1) := by
  sorry

end Erdos249257.ExternalVerification1041SignedMomentTetranomial
