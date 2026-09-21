import ErdosProblems.Erdos1041.PaperCriticalConsequencesR10

/-! The three critical-value budgets and simultaneous sharpness, including
zero radius and repeated critical points. -/

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR20
open Polynomial PaperAnalyticTargets

/-- All three displayed inequalities in the long-paper theorem. -/
theorem critical_value_three_budgets {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.Monic) (hdeg : f.natDegree = n) (h : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hroots : RootsInClosedDisc f h R) (c : Fin (n - 1) → ℂ)
    (hc : CriticalEnumeration f c) :
    (∑ j, ‖f.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤
      ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ j, ‖f.eval (c j)‖ ^ (1 / ((n : ℝ) - 1))) ≤
      ((n : ℝ) - 1) * R ^ ((n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ j, ‖f.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R := by
  have H := paper_critical_value_mean n f c h R hn hf hdeg hR hroots hc
  exact ⟨H.1, paper_critical_value_power_budget hn f hf hdeg h R hR hroots c hc, H.2⟩

/-- The literal radius in the paper has the required nth power, also at λ=0. -/
theorem binomial_radius_power {n : ℕ} (hn : 0 < n) (lam : ℂ) :
    (‖lam‖ ^ (1 / (n : ℝ))) ^ n = ‖lam‖ := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  have he : (1 / (n : ℝ)) * (n : ℝ) = 1 := by field_simp
  rw [he, Real.rpow_one]

/-- Simultaneous attainment of all three constants by the stated binomial
family, at its literal enclosing radius rather than an assumed radius identity. -/
theorem critical_value_three_budgets_sharp (n : ℕ) (hn : 2 ≤ n) (h lam : ℂ) :
    let R := ‖lam‖ ^ (1 / (n : ℝ))
    let f := radialEqualityPolynomial n h lam
    f.Monic ∧ f.natDegree = n ∧ RootsInClosedDisc f h R ∧
    CriticalEnumeration f (fun _ : Fin (n - 1) => h) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (2 / ((n : ℝ) - 1))) =
      ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (1 / ((n : ℝ) - 1))) =
      ((n : ℝ) - 1) * R ^ ((n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (1 / (n : ℝ))) = ((n : ℝ) - 1) * R := by
  let R := ‖lam‖ ^ (1 / (n : ℝ))
  have hn0 : 0 < n := by omega
  have hR : 0 ≤ R := Real.rpow_nonneg (norm_nonneg _) _
  have hlam : ‖lam‖ = R ^ n := (binomial_radius_power hn0 lam).symm
  have H := paper_critical_mean_sharpness n hn h lam R hR hlam
  refine ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1, ?_, H.2.2.2.2.2⟩
  have Hmiddle := radialEqualityPolynomial_moment n hn0 h lam R hR hlam
    (1 / ((n : ℝ) - 1))
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  simpa only [hcast, mul_one_div] using Hmiddle

#print axioms critical_value_three_budgets
#print axioms binomial_radius_power
#print axioms critical_value_three_budgets_sharp

end ErdosProblems.Erdos1041.PaperCompleteR20
