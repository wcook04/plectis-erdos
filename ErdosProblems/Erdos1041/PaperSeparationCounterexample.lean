import ErdosProblems.Erdos1041.NewtonFlowRaySeparation
import Mathlib

/-!
# The complete elementary separation-or counterexample

Target: short_note/res:sep-or-false. The root-disc claim is proved directly
from the root equation and a norm inequality; Rouché is not assumed.

The statement includes monicity, degree, the exhaustive list of critical
points, their simplicity, their values, a least-modulus witness, distinct
positive rays, and the strict normalised separation bound.

Validation: uncompiled proof source. No axioms or admitted steps are added.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperSeparationCounterexample

open Polynomial

def P : ℂ[X] := X ^ 3 + (C (3 / 100 : ℂ) * X ^ 1 + C (-3 / 4 : ℂ))

def value (z : ℂ) : ℂ := z ^ 3 + (3 / 100 : ℂ) * z - 3 / 4

def plus : ℂ := Complex.I / 10

def minus : ℂ := -Complex.I / 10

@[simp] theorem eval_P (z : ℂ) : P.eval z = value z := by
  simp only [P, value, eval_add, eval_pow, eval_X, eval_mul, eval_C, pow_one]
  ring

theorem P_monic_and_degree : P.Monic ∧ P.natDegree = 3 := by
  let tail : ℂ[X] := C (3 / 100 : ℂ) * X ^ 1 + C (-3 / 4 : ℂ)
  have h1 : (C (3 / 100 : ℂ) * X ^ 1).degree ≤ (1 : WithBot ℕ) :=
    degree_C_mul_X_pow_le 1 (3 / 100 : ℂ)
  have h2 : (C (-3 / 4 : ℂ)).degree ≤ (1 : WithBot ℕ) :=
    le_trans degree_C_le (by norm_num)
  have ht : tail.degree ≤ (1 : WithBot ℕ) :=
    le_trans (degree_add_le _ _) (max_le h1 h2)
  have hlt : tail.degree < (X ^ 3 : ℂ[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt ht (by norm_num)
  have hm : P.Monic := (monic_X_pow 3).add_of_left hlt
  have hd : P.degree = (3 : WithBot ℕ) := by
    change (X ^ 3 + tail).degree = _
    rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
    simp
  exact ⟨hm, natDegree_eq_of_degree_eq_some hd⟩

@[simp] theorem eval_derivative (z : ℂ) :
    P.derivative.eval z = 3 * z ^ 2 + 3 / 100 := by
  norm_num [P, Polynomial.derivative_pow]

@[simp] theorem eval_second_derivative (z : ℂ) :
    P.derivative.derivative.eval z = 6 * z := by
  norm_num [P, Polynomial.derivative_pow]
  ring

theorem roots_in_open_disc {z : ℂ} (hz : P.eval z = 0) : ‖z‖ < 1 := by
  rw [eval_P] at hz
  have he : z ^ 3 = -((3 / 100 : ℂ) * z) + 3 / 4 := by
    unfold value at hz
    linear_combination hz
  have hbound : ‖z‖ ^ 3 ≤ (3 / 100 : ℝ) * ‖z‖ + 3 / 4 := by
    calc
      ‖z‖ ^ 3 = ‖z ^ 3‖ := (norm_pow z 3).symm
      _ = ‖-((3 / 100 : ℂ) * z) + 3 / 4‖ := congrArg norm he
      _ ≤ ‖-((3 / 100 : ℂ) * z)‖ + ‖(3 / 4 : ℂ)‖ := norm_add_le _ _
      _ = (3 / 100 : ℝ) * ‖z‖ + 3 / 4 := by
        rw [norm_neg, norm_mul]
        norm_num
  by_contra hnot
  have hge : 1 ≤ ‖z‖ := le_of_not_gt hnot
  have hprod : 0 ≤ (‖z‖ - 1) * (‖z‖ ^ 2 + ‖z‖) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [norm_nonneg z]

theorem critical_factor (z : ℂ) :
    P.derivative.eval z = (3 : ℂ) * (z - plus) * (z - minus) := by
  rw [eval_derivative]
  apply Complex.ext <;>
    norm_num [plus, minus, pow_two, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply] <;> ring

theorem all_critical_points (z : ℂ) :
    P.derivative.eval z = 0 ↔ z = plus ∨ z = minus := by
  rw [critical_factor]
  simp [mul_eq_zero, sub_eq_zero]

theorem plus_ne_minus : plus ≠ minus := by
  intro he
  have hi := congrArg Complex.im he
  norm_num [plus, minus, Complex.div_im, Complex.normSq_apply] at hi

theorem critical_points_simple (z : ℂ) (hz : P.derivative.eval z = 0) :
    P.derivative.derivative.eval z ≠ 0 := by
  rcases (all_critical_points z).mp hz with rfl | rfl
  · rw [eval_second_derivative]
    intro he
    have hi := congrArg Complex.im he
    norm_num [plus, Complex.mul_im, Complex.div_im, Complex.normSq_apply] at hi
  · rw [eval_second_derivative]
    intro he
    have hi := congrArg Complex.im he
    norm_num [minus, Complex.mul_im, Complex.div_im, Complex.normSq_apply] at hi

@[simp] theorem value_plus : P.eval plus = -3 / 4 + Complex.I / 500 := by
  rw [eval_P]
  apply Complex.ext <;>
    norm_num [value, plus, pow_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply]

@[simp] theorem value_minus : P.eval minus = -3 / 4 - Complex.I / 500 := by
  rw [eval_P]
  apply Complex.ext <;>
    norm_num [value, minus, pow_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply]

theorem values_normSq :
    Complex.normSq (P.eval plus) = (9 / 16 : ℝ) + 1 / 250000 ∧
    Complex.normSq (P.eval minus) = (9 / 16 : ℝ) + 1 / 250000 := by
  constructor
  · rw [value_plus]
    norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]
  · rw [value_minus]
    norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]

def mu : ℝ := ‖P.eval plus‖

theorem norm_minus_eq_mu : ‖P.eval minus‖ = mu := by
  unfold mu
  rw [Complex.norm_def, Complex.norm_def, values_normSq.1, values_normSq.2]

theorem mu_gt_three_fourths : (3 / 4 : ℝ) < mu := by
  have hs : mu ^ 2 = (9 / 16 : ℝ) + 1 / 250000 := by
    rw [mu, ← Complex.normSq_eq_norm_sq, values_normSq.1]
  have hn : 0 ≤ mu := norm_nonneg _
  nlinarith

theorem mu_gt_threshold : (13 / 25 : ℝ) < mu := by
  linarith [mu_gt_three_fourths]

theorem mu_is_least : IsLeast
    {x : ℝ | ∃ c : ℂ, P.derivative.eval c = 0 ∧ x = ‖P.eval c‖} mu := by
  constructor
  · exact ⟨plus, (all_critical_points plus).mpr (Or.inl rfl), rfl⟩
  · rintro x ⟨c, hc, rfl⟩
    rcases (all_critical_points c).mp hc with rfl | rfl
    · exact le_rfl
    · rw [norm_minus_eq_mu]

theorem distinct_positive_rays :
    ¬ SamePositiveRay (P.eval plus) (P.eval minus) := by
  rintro ⟨t, ht, he⟩
  rw [value_plus, value_minus, Complex.ext_iff] at he
  obtain ⟨hr, hi⟩ := he
  norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.normSq_apply] at hr hi
  linarith

theorem plus_value_ne_zero : P.eval plus ≠ 0 := by
  intro h
  have hmu : mu = 0 := by simp [mu, h]
  linarith [mu_gt_three_fourths]

theorem ratio_norm :
    ‖1 - P.eval minus / P.eval plus‖ = (1 / 250 : ℝ) / mu := by
  have hid : 1 - P.eval minus / P.eval plus =
      (P.eval plus - P.eval minus) / P.eval plus := by
    rw [sub_div, div_self plus_value_ne_zero]
  rw [hid, norm_div]
  have hd : P.eval plus - P.eval minus = Complex.I / 250 := by
    rw [value_plus, value_minus]
    ring
  rw [hd]
  norm_num [mu, norm_div]

theorem strict_separation_bound :
    ‖1 - P.eval minus / P.eval plus‖ < (2 / 375 : ℝ) := by
  rw [ratio_norm]
  apply (div_lt_iff₀ (by linarith [mu_gt_three_fourths] : 0 < mu)).2
  nlinarith [mu_gt_three_fourths]

/-- Complete statement of the labelled counterexample. `mu_is_least`
provides the minimum, rather than postulating that the chosen value is least. -/
theorem complete_sep_or_counterexample :
    P.Monic ∧ P.natDegree = 3 ∧
    (∀ z : ℂ, P.eval z = 0 → ‖z‖ < 1) ∧
    (∀ z : ℂ, P.derivative.eval z = 0 ↔ z = plus ∨ z = minus) ∧
    plus ≠ minus ∧
    (∀ z : ℂ, P.derivative.eval z = 0 → P.derivative.derivative.eval z ≠ 0) ∧
    IsLeast {x : ℝ | ∃ c : ℂ, P.derivative.eval c = 0 ∧ x = ‖P.eval c‖} mu ∧
    (13 / 25 : ℝ) < mu ∧
    ¬ SamePositiveRay (P.eval plus) (P.eval minus) ∧
    ‖1 - P.eval minus / P.eval plus‖ < (2 / 375 : ℝ) ∧
    (2 / 375 : ℝ) < 2 := by
  exact ⟨P_monic_and_degree.1, P_monic_and_degree.2, fun _ => roots_in_open_disc,
    all_critical_points, plus_ne_minus, critical_points_simple, mu_is_least,
    mu_gt_threshold, distinct_positive_rays, strict_separation_bound, by norm_num⟩

#print axioms complete_sep_or_counterexample

end ErdosProblems.Erdos1041.PaperSeparationCounterexample
