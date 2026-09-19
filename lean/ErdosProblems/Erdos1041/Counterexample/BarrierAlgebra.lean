import ErdosProblems.Erdos1041.Counterexample.Defs
import Mathlib
/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Explicit separating barriers replacing the Riemann-Hurwitz step of Lemma 2.1, at `s = 10⁻⁶`. -/

/-!
The namespace `S7Proof` keeps the barrier lemmas separate from the shared
definitions in `Defs.lean`.  These lemmas are consumed by
`InstanceBarriers.lean` and belong to the successfully checked counterexample
dependency chain.
-/
noncomputable section

open scoped ComplexConjugate

namespace Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def scaleR : ℝ := (ρ : ℝ) * (ε : ℝ)
def rootScale : ℝ := 1 / (ε : ℝ)
def K_hi : ℝ := 7 / 10 ^ 12 + 1 / 10 ^ 105

theorem rho_pos : 0 < (ρ : ℝ) := by norm_num [ρ, s]
theorem eps_pos : 0 < (ε : ℝ) := by norm_num [ε, s]
theorem scale_pos : 0 < scaleR := mul_pos rho_pos eps_pos

theorem scale_cast : (scaleR : ℂ) = (ρ : ℂ) * (ε : ℂ) := by
  unfold scaleR
  push_cast <;> rfl

theorem scale_ne : (scaleR : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt scale_pos)

theorem rootScale_ge : (100 : ℝ) ≤ rootScale := by
  norm_num [rootScale, ε, s]

theorem scale_rootScale : scaleR * rootScale = (ρ : ℝ) := by
  unfold scaleR rootScale
  field_simp [ne_of_gt eps_pos] <;> ring

theorem f_eval_scaled (w : ℂ) :
    f.eval ((ρ : ℂ) * (ε : ℂ) * w) =
      (ρ : ℂ) ^ 7 * (-1 + (ε : ℂ) ^ 7 * Q.eval w) := by
  simp only [f, Q, P, G, E, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  unfold a b c ε
  push_cast <;> ring

theorem f_re_scaled (w : ℂ) :
    (f.eval ((ρ : ℂ) * (ε : ℂ) * w)).re =
      (ρ : ℝ) ^ 7 * (-1 + (ε : ℝ) ^ 7 * (Q.eval w).re) := by
  rw [f_eval_scaled]
  have hr : (ρ : ℂ) = ((ρ : ℝ) : ℂ) := by norm_cast
  have he : (ε : ℂ) = ((ε : ℝ) : ℂ) := by norm_cast
  rw [hr, he, ← Complex.ofReal_pow, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
    Complex.one_re, Complex.one_im]
  ring

theorem real_threshold :
    (ρ : ℝ) ^ 7 * (-1 + (ε : ℝ) ^ 7 * (-K_hi)) ≤ -1 := by
  norm_num [ρ, ε, s, K_hi]

/-- A stronger sufficient condition than the squared-norm condition: here the
real part of the scaled polynomial is already at most -1. -/
theorem norm_ge_one_of_Q_re (w : ℂ) (hw : K_hi + (Q.eval w).re ≤ 0) :
    1 ≤ ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ := by
  have hq : (Q.eval w).re ≤ -K_hi := by linarith
  have he : 0 ≤ (ε : ℝ) ^ 7 := pow_nonneg eps_pos.le 7
  have hr : 0 ≤ (ρ : ℝ) ^ 7 := pow_nonneg rho_pos.le 7
  have hf : (f.eval ((ρ : ℂ) * (ε : ℂ) * w)).re ≤ -1 := by
    rw [f_re_scaled]
    have h1 : (ε : ℝ) ^ 7 * (Q.eval w).re ≤ (ε : ℝ) ^ 7 * (-K_hi) :=
      mul_le_mul_of_nonneg_left hq he
    have h2 : (ρ : ℝ) ^ 7 * (-1 + (ε : ℝ) ^ 7 * (Q.eval w).re)
        ≤ (ρ : ℝ) ^ 7 * (-1 + (ε : ℝ) ^ 7 * (-K_hi)) := by
      refine mul_le_mul_of_nonneg_left ?_ hr
      linarith
    linarith [real_threshold]
  have habs := Complex.abs_re_le_norm (f.eval ((ρ : ℂ) * (ε : ℂ) * w))
  rw [abs_of_nonpos (by linarith : (f.eval ((ρ : ℂ) * (ε : ℂ) * w)).re ≤ 0)] at habs
  linarith

def Hpoly (x y : ℝ) : ℝ :=
  1 * x ^ 7
    + (-23013813 / 32000000000000000000000000000000000000000000000000000000000000000) * x ^ 6
    + (-21) * x ^ 5 * y ^ 2
    + (243 / 6250000000000000000000000000000000000000000000000000000000000000000) * x ^ 5 * y
    + (-9 / 5000000000000000000000000000000000000000000) * x ^ 5
    + (69041439 / 6400000000000000000000000000000000000000000000000000000000000000) * x ^ 4 * y ^ 2
    + (-551827 / 160000000000000000000000000000000000000) * x ^ 4 * y
    + (329507 / 1600000000000000) * x ^ 4
    + 35 * x ^ 3 * y ^ 4
    + (-81 / 625000000000000000000000000000000000000000000000000000000000000000) * x ^ 3 * y ^ 3
    + (9 / 500000000000000000000000000000000000000000) * x ^ 3 * y ^ 2
    + (1 / 250000000000000000) * x ^ 3 * y
    + (-329507 / 1600) * x ^ 3
    + (-69041439 / 6400000000000000000000000000000000000000000000000000000000000000) * x ^ 2 * y ^ 4
    + (551827 / 80000000000000000000000000000000000000) * x ^ 2 * y ^ 3
    + (-988521 / 800000000000000) * x ^ 2 * y ^ 2
    + (3 / 1000000) * x ^ 2 * y
    + (9 / 5000000) * x ^ 2
    + (-7) * x * y ^ 6
    + (243 / 6250000000000000000000000000000000000000000000000000000000000000000) * x * y ^ 5
    + (-9 / 1000000000000000000000000000000000000000000) * x * y ^ 4
    + (-1 / 250000000000000000) * x * y ^ 3
    + (988521 / 1600) * x * y ^ 2
    + (-551827 / 400) * x * y
    + (23013813 / 32000) * x
    + (23013813 / 32000000000000000000000000000000000000000000000000000000000000000) * y ^ 6
    + (-551827 / 800000000000000000000000000000000000000) * y ^ 5
    + (329507 / 1600000000000000) * y ^ 4
    + (-1 / 1000000) * y ^ 3
    + (-9 / 5000000) * y ^ 2
    + (81 / 12500000) * y
    + (7000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001 / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

theorem conj_a : conj a = (A : ℂ) + (s : ℂ) * Complex.I := by
  simp only [a, map_sub, map_mul, map_ratCast, Complex.conj_I]
  ring

theorem conj_b : conj b = -(Complex.I * (B : ℂ)) + ((9 / 5 : ℚ) : ℂ) * (s : ℂ) := by
  simp only [b, map_add, map_mul, map_ratCast, Complex.conj_I]
  ring

theorem conj_c : conj c = -(Cconst : ℂ) + ((162 / 25 : ℚ) : ℂ) * (s : ℂ) * Complex.I := by
  simp only [c, map_sub, map_neg, map_mul, map_ratCast, Complex.conj_I]
  ring

theorem Hpoly_eq (w : ℂ) : Hpoly w.re w.im = K_hi + (Q.eval w).re := by
  simp only [Q, P, G, E, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, conj_a, conj_b, conj_c]
  norm_num [Hpoly, K_hi, a, b, c, A, B, Cconst, t, s, pow_succ,
    Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem norm_ge_one_of_Hpoly (w : ℂ) (hw : Hpoly w.re w.im ≤ 0) :
    1 ≤ ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ := by
  apply norm_ge_one_of_Q_re
  simpa only [Hpoly_eq] using hw

def xi (z : ℂ) : ℝ := -5 * z.re + 4 * z.im
def eta (z : ℂ) : ℝ := 4 * z.re + 5 * z.im

theorem continuous_xi : Continuous xi := by unfold xi; fun_prop
theorem continuous_eta : Continuous eta := by unfold eta; fun_prop

theorem xi_sub (z w : ℂ) : xi (z - w) = xi z - xi w := by
  simp only [xi, Complex.sub_re, Complex.sub_im]
  ring

theorem eta_sub (z w : ℂ) : eta (z - w) = eta z - eta w := by
  simp only [eta, Complex.sub_re, Complex.sub_im]
  ring

theorem xi_real_mul (r : ℝ) (z : ℂ) : xi ((r : ℂ) * z) = r * xi z := by
  simp only [xi, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem eta_real_mul (r : ℝ) (z : ℂ) : eta ((r : ℂ) * z) = r * eta z := by
  simp only [eta, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem re_from_coordinates (z : ℂ) : z.re = (-5 * xi z + 4 * eta z) / 41 := by
  unfold xi eta
  ring

theorem im_from_coordinates (z : ℂ) : z.im = (4 * xi z + 5 * eta z) / 41 := by
  unfold xi eta
  ring

theorem abs_xi_le (z : ℂ) : |xi z| ≤ 9 * ‖z‖ := by
  have h1 := abs_le.mp (Complex.abs_re_le_norm z)
  have h2 := abs_le.mp (Complex.abs_im_le_norm z)
  rw [abs_le]
  unfold xi
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem abs_eta_le (z : ℂ) : |eta z| ≤ 9 * ‖z‖ := by
  have h1 := abs_le.mp (Complex.abs_re_le_norm z)
  have h2 := abs_le.mp (Complex.abs_im_le_norm z)
  rw [abs_le]
  unfold eta
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem norm_div_sub (z a : ℂ) (k : ℝ) (hk : 0 < k) :
    ‖z / (k : ℂ) - a‖ = ‖z - (k : ℂ) * a‖ / k := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hid : z / (k : ℂ) - a = (z - (k : ℂ) * a) / (k : ℂ) := by
    field_simp [hk']
    <;> ring
  rw [hid, norm_div]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]

end Erdos1041.Counterexample.S7Proof
