import ErdosProblems.Erdos1049.ZudilinConeArithmetic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# R7: integral homogeneous evaluation at a rational base

Uncompiled proof-source candidate. This is the finite algebraic bridge in the
main irrationality proof, not the existence or asymptotics of the cancelled
source forms. It reuses `homEval`; it does not define a different clearing.

All degrees below are natural degrees. This is harmless for a zero polynomial:
its natural degree is zero and every displayed evaluation identity still holds.
-/

namespace ErdosProblems.Erdos1049.PaperR7

open scoped BigOperators

/-- Evaluate over precisely the common-width coefficient range. -/
theorem eval_real_eq_sum_range (P : Polynomial ℤ) (W : ℕ) (x : ℝ)
    (hdegree : P.natDegree ≤ W) :
    P.eval₂ (Int.castRingHom ℝ) x =
      ∑ i ∈ Finset.range (W + 1), (P.coeff i : ℝ) * x ^ i := by
  classical
  rw [Polynomial.eval₂_eq_sum]
  change (∑ i ∈ P.support, (P.coeff i : ℝ) * x ^ i) = _
  apply Finset.sum_subset
  · intro i hi
    apply Finset.mem_range.mpr
    have hi' : i ≤ P.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
    omega
  · intro i _ hi
    have hzero : P.coeff i = 0 := by
      by_contra hn
      exact hi (Polynomial.mem_support_iff.mpr hn)
    simp [hzero]

/-- The denominator clearer is an integer BEFORE rational specialisation.
The degree bound is necessary: `homEval` truncates at W by definition. -/
theorem homEval_cast_eq_real_eval (a b W : ℕ) (P : Polynomial ℤ)
    (hb : b ≠ 0) (hdegree : P.natDegree ≤ W) :
    (homEval a b W P : ℝ) =
      (b : ℝ) ^ W * P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) := by
  classical
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  rw [eval_real_eq_sum_range P W _ hdegree, Finset.mul_sum]
  simp only [homEval, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro i hi
  have hiW : i ≤ W := by
    have hi' := Finset.mem_range.mp hi
    omega
  have hsplit : (b : ℝ) ^ W = (b : ℝ) ^ i * (b : ℝ) ^ (W - i) := by
    rw [← pow_add, Nat.add_sub_of_le hiW]
  rw [div_pow, hsplit]
  field_simp [hbR]

/-- The exact linear-form identity used after cancelling cyclotomic factors. -/
theorem cleared_linear_form_identity (a b W : ℕ) (U V : Polynomial ℤ)
    (ξ : ℝ) (hb : b ≠ 0)
    (hU : U.natDegree ≤ W) (hV : V.natDegree ≤ W) :
    (homEval a b W U : ℝ) * ξ - (homEval a b W V : ℝ) =
      (b : ℝ) ^ W *
        (U.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) * ξ -
          V.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b)) := by
  rw [homEval_cast_eq_real_eval a b W U hb hU,
    homEval_cast_eq_real_eval a b W V hb hV]
  ring

/-- Finite coefficient-ℓ¹ bound. This is not the long record's max norm. -/
noncomputable def coeffL1 (P : Polynomial ℤ) : ℝ :=
  ∑ i ∈ P.support, |(P.coeff i : ℝ)|

/-- Re-express the ℓ¹ norm on a common-width range. -/
theorem coeffL1_eq_sum_range (P : Polynomial ℤ) (W : ℕ)
    (hdegree : P.natDegree ≤ W) :
    coeffL1 P = ∑ i ∈ Finset.range (W + 1), |(P.coeff i : ℝ)| := by
  classical
  unfold coeffL1
  apply Finset.sum_subset
  · intro i hi
    apply Finset.mem_range.mpr
    have hi' := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
    omega
  · intro i _ hi
    have hzero : P.coeff i = 0 := by
      by_contra hn
      exact hi (Polynomial.mem_support_iff.mpr hn)
    simp [hzero]

/-- The usual evaluation bound with the ACTUAL ℓ¹ norm. This supplies the
finite estimate used before the source-specific exponential height bound. -/
theorem abs_eval_real_le_coeffL1_mul_pow (P : Polynomial ℤ) (W : ℕ)
    (x : ℝ) (hx : 1 ≤ x) (hdegree : P.natDegree ≤ W) :
    |P.eval₂ (Int.castRingHom ℝ) x| ≤ coeffL1 P * x ^ W := by
  classical
  rw [eval_real_eq_sum_range P W x hdegree,
    coeffL1_eq_sum_range P W hdegree, Finset.sum_mul]
  calc
    |∑ i ∈ Finset.range (W + 1), (P.coeff i : ℝ) * x ^ i| ≤
        ∑ i ∈ Finset.range (W + 1), |(P.coeff i : ℝ) * x ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (W + 1), |(P.coeff i : ℝ)| * x ^ W := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (pow_nonneg (show (0:ℝ) ≤ x by linarith) i)]
      have hiW : i ≤ W := by
        have hi' := Finset.mem_range.mp hi
        omega
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hiW) (abs_nonneg _)

/-- More common width only introduces the corresponding scalar power. -/
theorem homEval_width_add (a b W k : ℕ) (P : Polynomial ℤ)
    (hb : b ≠ 0) (hdegree : P.natDegree ≤ W) :
    homEval a b (W + k) P = (b : ℤ) ^ k * homEval a b W P := by
  have heq : (homEval a b (W + k) P : ℝ) =
      ((b : ℤ) ^ k * homEval a b W P : ℤ) := by
    push_cast
    rw [homEval_cast_eq_real_eval a b (W + k) P hb (by omega),
      homEval_cast_eq_real_eval a b W P hb hdegree, pow_add]
    ring
  exact_mod_cast heq

end ErdosProblems.Erdos1049.PaperR7
