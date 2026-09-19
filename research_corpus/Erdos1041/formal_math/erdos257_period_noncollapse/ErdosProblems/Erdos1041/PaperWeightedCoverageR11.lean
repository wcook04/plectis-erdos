import research_corpus.Erdos1041.PaperAnalyticR10

/-!
# Explicit weighted Cauchy equality and small-cardinality paper endpoints

This module does not replace or shorten the R10 80-declaration audit.
It supplies the exact variance identity, its positive-support equality case,
the simultaneous Cauchy/Taylor deficit, and the retained FP3/FP4 conclusions.
The retired three- and four-point alternative arguments are NOT claimed to follow
as formal arguments from these conclusions. See the exact paper patches.
All Lean compilation and axiom checks for this return are UNRUN.
-/
set_option autoImplicit false
open scoped BigOperators ComplexConjugate
noncomputable section
namespace ErdosProblems.Erdos1041

/-- The complete algebraic identity behind probability-weighted Cauchy--Schwarz.
The identity itself needs only normalisation, not positivity of the weights. -/
theorem probability_variance_identity {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hsum : ∑ j, w j = 1) :
    (∑ j, w j * x j) ^ 2 +
      (∑ j, w j * (x j - ∑ k, w k * x k) ^ 2) =
        ∑ j, w j * x j ^ 2 := by
  let μ := ∑ j, w j * x j
  have he : (∑ j, w j * (x j - μ) ^ 2) =
      (∑ j, w j * x j ^ 2) - μ ^ 2 := by
    calc
      _ = ∑ j, (w j * x j ^ 2 - 2 * μ * (w j * x j) + μ ^ 2 * w j) :=
        Finset.sum_congr rfl (fun j _ => by ring)
      _ = (∑ j, w j * x j ^ 2) - 2 * μ * (∑ j, w j * x j) +
          μ ^ 2 * (∑ j, w j) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by
        rw [hsum]
        change _ - 2 * μ * μ + μ ^ 2 * 1 = _
        ring
  change μ ^ 2 + (∑ j, w j * (x j - μ) ^ 2) = _
  rw [he]
  ring

/-- Equality in weighted Cauchy--Schwarz means constancy on positive support.
No distinctness or sign assumption on the observations `x` is imposed. -/
theorem probability_cauchy_equality_iff {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) :
    ((∑ j, w j * x j) ^ 2 = ∑ j, w j * x j ^ 2) ↔
      ∀ j, 0 < w j → x j = ∑ k, w k * x k := by
  classical
  have hid := probability_variance_identity w x hsum
  constructor
  · intro heq
    have hv : (∑ j, w j * (x j - ∑ k, w k * x k) ^ 2) = 0 := by
      linarith
    intro j hj
    have hone := Finset.single_le_sum (s := Finset.univ)
      (f := fun i => w i * (x i - ∑ k, w k * x k) ^ 2)
      (fun i _ => mul_nonneg (hw i) (sq_nonneg _)) (Finset.mem_univ j)
    rw [hv] at hone
    have hsq : (x j - ∑ k, w k * x k) ^ 2 ≤ 0 := by
      apply (mul_le_mul_iff_of_pos_left hj).mp
      simpa only [mul_zero] using hone
    nlinarith [sq_nonneg (x j - ∑ k, w k * x k)]
  · intro hx
    have hv : (∑ j, w j * (x j - ∑ k, w k * x k) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : w j = 0
      · simp only [hj, zero_mul]
      · rw [hx j (lt_of_le_of_ne (hw j) (Ne.symm hj))]
        simp
    rw [hv, add_zero] at hid
    exact hid

/-- Cauchy variance and every finite Taylor deficit can be retained together.
The actual analytic construction supplies the energy estimate: it is not a
hypothesis. The point condition is closed-disc, and zero weights are allowed. -/
theorem weighted_linear_variance_finite_deficit_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (c : ι → ℂ) (hw : ∀ j, 0 ≤ w j)
    (hsum : ∑ j, w j = 1) (hc : ∀ j, ‖c j‖ ≤ 1) (s : Finset ℕ) :
    (∑ j, w j * weightedGeometric w c (c j)) ^ 2 +
      (∑ j, w j * (weightedGeometric w c (c j) -
        ∑ k, w k * weightedGeometric w c (c k)) ^ 2) +
      (∑ n ∈ s, taylorDeficitTerm (weightedTaylorCoeff w c) n) ≤ 1 := by
  rw [probability_variance_identity w
    (fun j => weightedGeometric w c (c j)) hsum]
  exact weighted_closed_disc_add_finite_deficit_le w c hw hsum hc s

/-- An explicit normalisation identity avoids the Wave56 unit-factor regression.
It remains an algebraic identity even for `m = 0`; probability endpoints below
correctly require `0 < m`. -/
theorem equal_weight_sum_eq_div {m : ℕ} (x : Fin m → ℝ) :
    (∑ j, (1 / (m : ℝ)) * x j) = (∑ j, x j) / (m : ℝ) := by
  rw [← Finset.mul_sum]
  simp only [one_div, div_eq_mul_inv, one_mul, mul_one]
  exact mul_comm _ _

/-- Equality in the literal equal-weight row sum, in every positive degree. -/
theorem equal_free_point_linear_equality_iff {m : ℕ} (hm : 0 < m)
    (c : Fin m → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1) :
    (∑ j, equalFreePointRow c j) = (m : ℝ) ↔ ∀ j, c j = 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hwpos : ∀ _j : Fin m, 0 < (1 / (m : ℝ)) :=
    fun _ => one_div_pos.mpr hmpos
  have H := weighted_linear_equality_iff (fun _ : Fin m => 1 / (m : ℝ)) c
    (fun j => (hwpos j).le) (equalWeight_sum hm) hc
  have hnorm :
      (∑ j, (1 / (m : ℝ)) *
        weightedGeometric (fun _ : Fin m => 1 / (m : ℝ)) c (c j)) =
          (∑ j, equalFreePointRow c j) / (m : ℝ) := by
    simp only [← equalFreePointRow_eq_weighted]
    exact equal_weight_sum_eq_div (fun j => equalFreePointRow c j)
  constructor
  · intro he
    have hlin : (∑ j, (1 / (m : ℝ)) *
        weightedGeometric (fun _ : Fin m => 1 / (m : ℝ)) c (c j)) = 1 := by
      rw [hnorm, he, div_self hmne]
    exact fun j => H.mp hlin j (hwpos j)
  · intro hz
    have hlin := H.mpr (fun j _ => hz j)
    rw [hnorm] at hlin
    have he := (div_eq_iff hmne).mp hlin
    simpa only [one_mul] using he

/-- A nonzero centre makes the equal-weight linear inequality strict, including
repeated centres and centres on the unit circle. -/
theorem equal_free_point_linear_strict {m : ℕ} (hm : 0 < m)
    (c : Fin m → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1) (hnz : ∃ j, c j ≠ 0) :
    (∑ j, equalFreePointRow c j) < (m : ℝ) := by
  apply lt_of_le_of_ne (equal_free_point_linear hm c hc)
  intro he
  obtain ⟨j, hj⟩ := hnz
  exact hj ((equal_free_point_linear_equality_iff hm c hc).mp he j)

/-- The retained three-point conclusion, not a certification of the retired
Hölder/defect argument. -/
theorem paper_fp_three (c : Fin 3 → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1) :
    (∑ j, equalFreePointRow c j) ≤ 3 ∧
      ((∑ j, equalFreePointRow c j) = 3 ↔ ∀ j, c j = 0) := by
  constructor
  · exact equal_free_point_linear (by decide) c hc
  · exact equal_free_point_linear_equality_iff (by decide) c hc

/-- The retained four-point conclusion has no central/outer radius split. -/
theorem paper_fp_four (c : Fin 4 → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1) :
    (∑ j, equalFreePointRow c j) ≤ 4 ∧
      ((∑ j, equalFreePointRow c j) = 4 ↔ ∀ j, c j = 0) := by
  constructor
  · exact equal_free_point_linear (by decide) c hc
  · exact equal_free_point_linear_equality_iff (by decide) c hc

end ErdosProblems.Erdos1041
end
