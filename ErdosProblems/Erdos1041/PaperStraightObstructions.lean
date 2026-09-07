import ErdosProblems.Erdos1041.CriticalTwoRootProximity
import Mathlib

/-!
# Complete polynomial straight-path obstructions

Paper target: short_note/res:straight-no-go. The quintic certificate is
assembled into a polynomial, with exhaustive root classification and the
actual critical-point/spoke assertions. The cubic argument quantifies over
ALL its roots directly; it is not restricted to a supplied root enumeration.

New proof source, not elaborated in this environment.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperStraightObstructions

open Polynomial

private def p : ℂ := 999 / 1000
private def a : ℂ := (901 / 902 : ℂ) * p
private def uPlus : ℂ := ((-451 : ℂ) + 780 * Complex.I) / 901
private def uMinus : ℂ := ((-451 : ℂ) - 780 * Complex.I) / 901

def quinticRoot : Fin 5 → ℂ
  | 0 => a
  | 1 => Complex.I * p
  | 2 => -Complex.I * p
  | 3 => p * uPlus
  | 4 => p * uMinus

def quadratic (u v : ℂ) : ℂ[X] := X ^ 2 + (C u * X ^ 1 + C v)

def Q : ℂ[X] :=
  (X - C a) * quadratic 0 (p ^ 2) * quadratic ((902 / 901 : ℂ) * p) (p ^ 2)

private theorem quadratic_monic_degree (u v : ℂ) :
    (quadratic u v).Monic ∧ (quadratic u v).degree = (2 : WithBot ℕ) := by
  have hu : (C u * X ^ 1 : ℂ[X]).degree ≤ (1 : WithBot ℕ) :=
    degree_C_mul_X_pow_le 1 u
  have hv : (C v : ℂ[X]).degree ≤ (1 : WithBot ℕ) :=
    le_trans degree_C_le (by norm_num)
  have ht : (C u * X ^ 1 + C v : ℂ[X]).degree < (X ^ 2 : ℂ[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt (le_trans (degree_add_le _ _) (max_le hu hv)) (by norm_num)
  refine ⟨(monic_X_pow 2).add_of_left ht, ?_⟩
  rw [quadratic, degree_add_eq_left_of_degree_lt ht, degree_X_pow]
  simp

theorem Q_monic_degree : Q.Monic ∧ Q.natDegree = 5 := by
  have h₁ := quadratic_monic_degree 0 (p ^ 2)
  have h₂ := quadratic_monic_degree ((902 / 901 : ℂ) * p) (p ^ 2)
  have hmonic : Q.Monic := ((monic_X_sub_C a).mul h₁.1).mul h₂.1
  have hd : Q.degree = (5 : WithBot ℕ) := by
    rw [Q, degree_mul, degree_mul, degree_X_sub_C, h₁.2, h₂.2]
    norm_num
  exact ⟨hmonic, natDegree_eq_of_degree_eq_some hd⟩

/-- All five roots, including the real uniquely nearest root. -/
theorem Q_factor (z : ℂ) : Q.eval z = ∏ k : Fin 5, (z - quinticRoot k) := by
  rw [Fin.prod_univ_five]
  simp only [Q, quadratic, eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C,
    quinticRoot]
  apply Complex.ext <;>
    norm_num [a, p, uPlus, uMinus, pow_succ,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_apply] <;> ring

theorem Q_roots_iff (z : ℂ) : Q.eval z = 0 ↔ ∃ k : Fin 5, z = quinticRoot k := by
  rw [Q_factor]
  simp [Finset.prod_eq_zero_iff, sub_eq_zero]

theorem quinticRoot_norm_lt_one (k : Fin 5) : ‖quinticRoot k‖ < 1 := by
  have hs : Complex.normSq (quinticRoot k) < 1 := by
    fin_cases k <;> norm_num [quinticRoot, a, p, uPlus, uMinus,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]
  rw [Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (quinticRoot k)]

theorem Q_all_roots_open (z : ℂ) (hz : Q.eval z = 0) : ‖z‖ < 1 := by
  obtain ⟨k, rfl⟩ := (Q_roots_iff z).mp hz
  exact quinticRoot_norm_lt_one k

theorem Q_critical_zero : Q.derivative.eval 0 = 0 := by
  norm_num [Q, quadratic, a, p, Polynomial.derivative_pow]

theorem Q_zero_not_root : Q.eval 0 ≠ 0 := by
  norm_num [Q, quadratic, a, p]

/-- The squared-distance certificate for the public root function. The live
module `CriticalTwoRootProximity` carries the same certificate, but over a
`private` root function whose name is not accessible here, so the identical
finite computation is redone rather than transported. -/
theorem quinticRoot_unique_nearest_normSq (k : Fin 5) (hk : k ≠ 0) :
    Complex.normSq (quinticRoot 0) < Complex.normSq (quinticRoot k) := by
  fin_cases k <;>
    norm_num [quinticRoot, a, p, uPlus, uMinus, Complex.normSq_apply] at *

theorem Q_unique_nearest (z : ℂ) (hz : Q.eval z = 0) (hne : z ≠ quinticRoot 0) :
    ‖quinticRoot 0‖ < ‖z‖ := by
  obtain ⟨k, rfl⟩ := (Q_roots_iff z).mp hz
  have hk : k ≠ 0 := by intro hk; subst k; exact hne rfl
  have hs : Complex.normSq (quinticRoot 0) < Complex.normSq (quinticRoot k) :=
    quinticRoot_unique_nearest_normSq k hk
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (quinticRoot 0), norm_nonneg (quinticRoot k)]

private def escapeValue : ℝ :=
  (900099 / 902000 : ℝ) * (1 - 1 / 10) *
    (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 + (999 / 1000) ^ 2) *
    (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 +
      (1 / 10) * (999 / 1000) ^ 2 + (999 / 1000) ^ 2)

theorem Q_spoke_escapes :
    1 < ‖Q.eval (((1 / 10 : ℝ) : ℂ) * quinticRoot 0)‖ := by
  have hE : (1 : ℝ) < escapeValue := nearestSpoke_unique_nearest_spoke_escapes
  have he : Q.eval (((1 / 10 : ℝ) : ℂ) * quinticRoot 0) = -(escapeValue : ℂ) := by
    norm_num [Q, quadratic, quinticRoot, a, p, escapeValue]
  rw [he, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith : 0 < escapeValue)]
  exact hE

/-- The monic cubic used in the all-pairs obstruction. -/
def C₃ : ℂ[X] := X ^ 3 + C (-((99 / 100 : ℂ) ^ 3))

@[simp] theorem C₃_eval (z : ℂ) : C₃.eval z = z ^ 3 - (99 / 100 : ℂ) ^ 3 := by
  simp [C₃, sub_eq_add_neg]

theorem C₃_monic_degree : C₃.Monic ∧ C₃.natDegree = 3 := by
  have ht : (C (-((99 / 100 : ℂ) ^ 3)) : ℂ[X]).degree < (X ^ 3 : ℂ[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_C_le (by norm_num)
  have hm : C₃.Monic := (monic_X_pow 3).add_of_left ht
  have hd : C₃.degree = (3 : WithBot ℕ) := by
    rw [C₃, degree_add_eq_left_of_degree_lt ht, degree_X_pow]
    simp
  exact ⟨hm, natDegree_eq_of_degree_eq_some hd⟩

theorem C₃_all_roots_open (z : ℂ) (hz : C₃.eval z = 0) : ‖z‖ < 1 := by
  have he : z ^ 3 = (99 / 100 : ℂ) ^ 3 := sub_eq_zero.mp (by simpa using hz)
  have hn : ‖z‖ ^ 3 = (99 / 100 : ℝ) ^ 3 := by
    have h := congrArg norm he
    simpa [norm_pow] using h
  by_contra hnot
  have hge : 1 ≤ ‖z‖ := le_of_not_gt hnot
  have hprod := mul_nonneg (sub_nonneg.mpr hge)
    (show 0 ≤ ‖z‖ ^ 2 + ‖z‖ + 1 by positivity)
  nlinarith

/-- Algebraic midpoint formula, quantified over arbitrary distinct roots. -/
theorem C₃_midpoint_value {z w : ℂ}
    (hz : C₃.eval z = 0) (hw : C₃.eval w = 0) (hne : z ≠ w) :
    C₃.eval ((z + w) / 2) = -(9 / 8 : ℂ) * (99 / 100 : ℂ) ^ 3 := by
  have hz3 : z ^ 3 = (99 / 100 : ℂ) ^ 3 := sub_eq_zero.mp (by simpa using hz)
  have hw3 : w ^ 3 = (99 / 100 : ℂ) ^ 3 := sub_eq_zero.mp (by simpa using hw)
  have hmul : (z - w) * (z ^ 2 + z * w + w ^ 2) = 0 := by
    calc
      (z - w) * (z ^ 2 + z * w + w ^ 2) = z ^ 3 - w ^ 3 := by ring
      _ = 0 := by rw [hz3, hw3]; ring
  have hquad : z ^ 2 + z * w + w ^ 2 = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
  have hsum : (z + w) ^ 3 = -(99 / 100 : ℂ) ^ 3 := by
    linear_combination (3 / 2 : ℂ) * (z + w) * hquad -
      (1 / 2 : ℂ) * hz3 - (1 / 2 : ℂ) * hw3
  rw [C₃_eval, div_pow, hsum]
  ring

theorem C₃_all_pair_midpoints_escape {z w : ℂ}
    (hz : C₃.eval z = 0) (hw : C₃.eval w = 0) (hne : z ≠ w) :
    1 < ‖C₃.eval ((z + w) / 2)‖ := by
  rw [C₃_midpoint_value hz hw hne]
  norm_num [norm_mul, norm_pow]

/-- Both clauses of the displayed proposition, with actual polynomial
quantifiers and with the nearest-root condition quantified over all zeros. -/
theorem complete_straight_path_obstructions :
    (∃ f : ℂ[X], f.Monic ∧ f.natDegree = 5 ∧
      (∀ z : ℂ, f.eval z = 0 → ‖z‖ < 1) ∧
      ∃ c w : ℂ, f.derivative.eval c = 0 ∧ f.eval c ≠ 0 ∧ f.eval w = 0 ∧
        (∀ z : ℂ, f.eval z = 0 → z ≠ w → ‖c - w‖ < ‖c - z‖) ∧
        ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 1 < ‖f.eval (c + (t : ℂ) * (w - c))‖) ∧
    (∃ g : ℂ[X], g.Monic ∧ g.natDegree = 3 ∧
      (∀ z : ℂ, g.eval z = 0 → ‖z‖ < 1) ∧
      ∀ z w : ℂ, g.eval z = 0 → g.eval w = 0 → z ≠ w →
        1 < ‖g.eval ((z + w) / 2)‖) := by
  constructor
  · refine ⟨Q, Q_monic_degree.1, Q_monic_degree.2, Q_all_roots_open,
      0, quinticRoot 0, Q_critical_zero, Q_zero_not_root,
      (Q_roots_iff _).mpr ⟨0, rfl⟩, ?_, ?_⟩
    · intro z hz hne
      simpa only [zero_sub, norm_neg] using Q_unique_nearest z hz hne
    · exact ⟨1 / 10, by norm_num, by norm_num, by simpa using Q_spoke_escapes⟩
  · exact ⟨C₃, C₃_monic_degree.1, C₃_monic_degree.2, C₃_all_roots_open,
      fun _ _ hz hw hne => C₃_all_pair_midpoints_escape hz hw hne⟩

#print axioms complete_straight_path_obstructions

end ErdosProblems.Erdos1041.PaperStraightObstructions
