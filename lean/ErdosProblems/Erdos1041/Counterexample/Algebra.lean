/- STATEMENT DELTA: s1_alpha_ge adds T(y) = 0 because the interval-only assertion is false.
NAMESPACE DELTA: proofs live in Erdos1041.Counterexample.Algebra, avoiding imported stub collisions. -/
import ErdosProblems.Erdos1041.Counterexample.Defs
import Mathlib

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Formalisation of the algebraic identities and rational inequalities of §3 of
`ani_degree7_counterexample.tex`. -/

/-!
Proofs are developed in the nested namespace `Erdos1041.Counterexample.Algebra`
and re-exported at the end of this file at the nineteen contract names
`Erdos1041.Counterexample.s1_*`, each restated verbatim from the archived stub
interface so that any drift is a compile error rather than a silent weakening.

Verification status: elaborated and kernel-checked on the pinned toolchain
(Lean `v4.29.1`, Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`). Zero
errors, zero `sorry`; every obligation depends only on `propext`,
`Classical.choice`, `Quot.sound`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

noncomputable section
open scoped ComplexConjugate

namespace Erdos1041.Counterexample.Algebra

/-! ## Polynomial identities -/

private theorem rat_poly_ext {p q : Polynomial ℚ}
    (h : ∀ x : ℚ, p.eval x = q.eval x) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq p q
  have he : {x : ℚ | p.eval x = q.eval x} = Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact h x
  rw [he]
  exact Set.infinite_univ

theorem s1_derivative_factorisation' :
    Polynomial.derivative S
      = Polynomial.C 7 * (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C t) * T := by
  apply rat_poly_ext
  intro x
  norm_num [S, T, t, A_value, B_value, Cconst_value,
    Polynomial.derivative_add, Polynomial.derivative_C_mul,
    Polynomial.derivative_X_pow] <;> ring

theorem s1_value_factorisation' :
    S + Polynomial.C (t ^ 2 * (6 * t - 4))
      = (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C t) ^ 2 *
        (Polynomial.X ^ 3 - Polynomial.C 2 * Polynomial.X ^ 2
          + Polynomial.C (3 - 2 * t) * Polynomial.X + Polynomial.C (6 * t - 4)) := by
  apply rat_poly_ext
  intro x
  norm_num [S, T, t, A_value, B_value, Cconst_value] <;> ring

theorem s1_T_integral_form' :
    Polynomial.C (5600 : ℚ) * T
      = Polynomial.C 5600 * Polynomial.X ^ 4 - Polynomial.C 5600 * Polynomial.X ^ 3
        - Polynomial.C 52780 * Polynomial.X ^ 2 + Polynomial.C 111160 * Polynomial.X
        - Polynomial.C 55189 := by
  apply rat_poly_ext
  intro x
  norm_num [T, t] <;> ring

theorem s1_T_sign_table' :
    0 < T.eval (-18 / 5) ∧ T.eval (-7 / 2) < 0 ∧ T.eval (4 / 5) < 0 ∧
      0 < T.eval (5 / 6) ∧ 0 < T.eval (9 / 5) ∧ T.eval (11 / 6) < 0 ∧
      0 < T.eval 2 := by
  norm_num [T, t]

/-- A convenient real form; all its coefficients are exact rationals. -/
theorem T_eval_real (y : ℝ) :
    (T.map (algebraMap ℚ ℝ)).eval y
      = y ^ 4 - y ^ 3 - 377 / 40 * y ^ 2 + 397 / 20 * y - 55189 / 5600 := by
  norm_num [T, t, Polynomial.eval_map] <;> ring

theorem s1_root_y2' :
    ∃ y : ℝ, 4 / 5 < y ∧ y < 5 / 6 ∧ (T.map (algebraMap ℚ ℝ)).eval y = 0 := by
  have hc : ContinuousOn (fun y : ℝ => (T.map (algebraMap ℚ ℝ)).eval y)
      (Set.Icc (4 / 5) (5 / 6)) := by
    simp_rw [T_eval_real]
    fun_prop
  have hl : (T.map (algebraMap ℚ ℝ)).eval (4 / 5) < 0 := by
    rw [T_eval_real]; norm_num
  have hu : 0 < (T.map (algebraMap ℚ ℝ)).eval (5 / 6) := by
    rw [T_eval_real]; norm_num
  obtain ⟨y, hy, hzero⟩ := intermediate_value_Ioo
    (a := (4 / 5 : ℝ)) (b := (5 / 6 : ℝ))
    (f := fun y : ℝ => (T.map (algebraMap ℚ ℝ)).eval y)
    (by norm_num) hc
    (show (0 : ℝ) ∈ Set.Ioo ((T.map (algebraMap ℚ ℝ)).eval (4 / 5))
      ((T.map (algebraMap ℚ ℝ)).eval (5 / 6)) from ⟨hl, hu⟩)
  exact ⟨y, hy.1, hy.2, hzero⟩

/-! ## Exact interval certificates, avoiding a root-cardinality argument -/

/-- The degree-four Bernstein polynomial on the unit interval. -/
def bernstein4 (b0 b1 b2 b3 b4 x : ℝ) : ℝ :=
  b0 * (1 - x) ^ 4 + 4 * b1 * x * (1 - x) ^ 3
    + 6 * b2 * x ^ 2 * (1 - x) ^ 2 + 4 * b3 * x ^ 3 * (1 - x) + b4 * x ^ 4

private theorem bernstein4_pos (b0 b1 b2 b3 b4 x : ℝ)
    (h0 : 0 < b0) (h1 : 0 < b1) (h2 : 0 < b2) (h3 : 0 < b3) (h4 : 0 < b4)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 < bernstein4 b0 b1 b2 b3 b4 x := by
  by_cases he : x = 1
  · subst x
    simpa [bernstein4] using h4
  · have hxlt : x < 1 := (lt_or_eq_of_le hx1).resolve_right he
    have hmx : 0 < 1 - x := sub_pos.mpr hxlt
    unfold bernstein4
    positivity

theorem T_pos_left_tail (y : ℝ) (hy : y ≤ -18 / 5) :
    0 < (T.map (algebraMap ℚ ℝ)).eval y := by
  have hx : 0 ≤ -18 / 5 - y := by linarith
  have he : (T.map (algebraMap ℚ ℝ)).eval y =
      (-18 / 5 - y) ^ 4 + 77 / 5 * (-18 / 5 - y) ^ 3
        + 15827 / 200 * (-18 / 5 - y) ^ 2
        + 68897 / 500 * (-18 / 5 - y) + 1561619 / 140000 := by
    rw [T_eval_real]
    ring
  rw [he]
  positivity

theorem T_neg_zero_to_four_fifths (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 4 / 5) :
    (T.map (algebraMap ℚ ℝ)).eval y < 0 := by
  have hx0 : 0 ≤ 5 * y / 4 := by positivity
  have hx1 : 5 * y / 4 ≤ 1 := by linarith
  have hp := bernstein4_pos
    (55189 / 5600) (32957 / 5600) (245323 / 84000) (30497 / 28000)
    (15341 / 140000) (5 * y / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hx0 hx1
  have he : (T.map (algebraMap ℚ ℝ)).eval y =
      -bernstein4 (55189 / 5600) (32957 / 5600) (245323 / 84000)
        (30497 / 28000) (15341 / 140000) (5 * y / 4) := by
    rw [T_eval_real]
    unfold bernstein4
    ring
  linarith only [hp, he]

theorem T_pos_five_sixths_to_nine_fifths (y : ℝ)
    (hy0 : 5 / 6 ≤ y) (hy1 : y ≤ 9 / 5) :
    0 < (T.map (algebraMap ℚ ℝ)).eval y := by
  have hx0 : 0 ≤ (30 * y - 25) / 29 := by linarith
  have hx1 : (30 * y - 25) / 29 ≤ 1 := by linarith
  have hp := bernstein4_pos
    (10183 / 226800) (333167 / 302400) (1436851 / 1512000) (9869 / 84000)
    (479 / 140000) ((30 * y - 25) / 29)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hx0 hx1
  have he : (T.map (algebraMap ℚ ℝ)).eval y =
      bernstein4 (10183 / 226800) (333167 / 302400) (1436851 / 1512000)
        (9869 / 84000) (479 / 140000) ((30 * y - 25) / 29) := by
    rw [T_eval_real]
    unfold bernstein4
    ring
  linarith only [hp, he]

/-- This certificate justifies sharpening the bracket for an existing root,
not merely the existence of some root above a new sign-table endpoint. -/
theorem T_neg_four_fifths_to_823 (y : ℝ)
    (hy0 : 4 / 5 ≤ y) (hy1 : y ≤ 823 / 1000) :
    (T.map (algebraMap ℚ ℝ)).eval y < 0 := by
  have hx0 : 0 ≤ (1000 * y - 800) / 23 := by linarith
  have hx1 : (1000 * y - 800) / 23 ≤ 1 := by linarith
  have hp := bernstein4_pos
    (15341 / 140000) (1139811 / 14000000) (453226891 / 8400000000)
    (3807077691 / 140000000000) (7851124313 / 7000000000000)
    ((1000 * y - 800) / 23)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hx0 hx1
  have he : (T.map (algebraMap ℚ ℝ)).eval y =
      -bernstein4 (15341 / 140000) (1139811 / 14000000) (453226891 / 8400000000)
        (3807077691 / 140000000000) (7851124313 / 7000000000000)
        ((1000 * y - 800) / 23) := by
    rw [T_eval_real]
    unfold bernstein4
    ring
  linarith only [hp, he]

theorem root_y_gt_823 (y : ℝ)
    (hT : (T.map (algebraMap ℚ ℝ)).eval y = 0) (hlo : 4 / 5 < y) :
    823 / 1000 < y := by
  by_contra hn
  have hneg := T_neg_four_fifths_to_823 y hlo.le (le_of_not_gt hn)
  linarith only [hT, hneg]

/-! ## The first-order displacement -/

theorem s1_reG_imaginary_axis' (y : ℝ) :
    (G.eval ((y : ℂ) * Complex.I)).re = -y * (y + 18 / 5) * (y - 9 / 5) := by
  norm_num [G, pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem s1_reG_nonreal_critical' (σ : ℝ) (hσ : σ ^ 2 = (t : ℝ) - 1 / 4) :
    (G.eval ((σ : ℂ) - Complex.I / 2)).re = -41 / 80 := by
  have hs : σ ^ 2 = 407 / 40 := by
    norm_num [t] at hσ
    exact hσ
  norm_num [G, pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.normSq] <;> nlinarith only [hs]

theorem s1_reG_sign_at_critical_ordinates'
    (y : ℝ) (hT : (T.map (algebraMap ℚ ℝ)).eval y = 0) :
    (0 < (G.eval (q y)).re ↔ (4 / 5 < y ∧ y < 5 / 6)) := by
  change (0 < (G.eval ((y : ℂ) * Complex.I)).re ↔ _)
  rw [s1_reG_imaginary_axis']
  constructor
  · intro hg
    have hleft : -18 / 5 < y := by
      by_contra hn
      have hp := T_pos_left_tail y (le_of_not_gt hn)
      linarith only [hT, hp]
    have hypos : 0 < y := by
      by_contra hn
      have hy0 : y ≤ 0 := le_of_not_gt hn
      have ha : 0 ≤ -y * (y + 18 / 5) :=
        mul_nonneg (by linarith) (by linarith)
      have hb : y - 9 / 5 ≤ 0 := by linarith
      have hp := mul_nonpos_of_nonneg_of_nonpos ha hb
      linarith only [hg, hp]
    have hyupper : y < 9 / 5 := by
      by_contra hn
      have hy9 : 9 / 5 ≤ y := le_of_not_gt hn
      have ha : -y * (y + 18 / 5) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have hb : 0 ≤ y - 9 / 5 := by linarith
      have hp := mul_nonpos_of_nonpos_of_nonneg ha hb
      linarith only [hg, hp]
    constructor
    · by_contra hn
      have hp := T_neg_zero_to_four_fifths y hypos.le (le_of_not_gt hn)
      linarith only [hT, hp]
    · by_contra hn
      have hp := T_pos_five_sixths_to_nine_fifths y (le_of_not_gt hn) hyupper.le
      linarith only [hT, hp]
  · rintro ⟨hlo, hhi⟩
    have hypos : 0 < y := by linarith
    have hplus : 0 < y + 18 / 5 := by linarith
    have hminus : 0 < 9 / 5 - y := by linarith
    have hp := mul_pos (mul_pos hypos hplus) hminus
    nlinarith only [hp]

/-! ## Coefficient inequalities and seventh powers -/

theorem s1_K_gt_180' (y : ℝ) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) : 180 < Kfun y := by
  have h5 := pow_le_pow_left₀ (show (0 : ℝ) ≤ 4 / 5 by norm_num) hlo.le 5
  norm_num at h5
  norm_num [Kfun, A_value, B_value]
  nlinarith only [h5, hhi]

theorem s1_negL_gt_188' (y : ℝ) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) : 188 < -Lfun y := by
  have hy0 : 0 ≤ y := by linarith
  have h4 := pow_le_pow_left₀ hy0 hhi.le 4
  norm_num at h4
  norm_num [Lfun, A_value]
  nlinarith only [h4]

theorem s1_d3_pow_seven' : d3 ^ 7 = 278 - 29 * Complex.I := by
  apply Complex.ext <;> norm_num [d3, pow_succ, Complex.mul_re, Complex.mul_im]

theorem s1_d6_pow_seven' : d6 ^ 7 = 8 + 8 * Complex.I := by
  apply Complex.ext <;> norm_num [d6, pow_succ, Complex.mul_re, Complex.mul_im]

/-! ## The two explicit cofactors -/

/-- Expanded: `14*r*y^2 + 14*r*y + (2919/20)*r`. -/
def W3 (y r : ℝ) : ℝ := 14 * r * (y ^ 2 + y + 417 / 40)

/-- Expanded: `-7*r*y^2 - 7*r*y - (2919/40)*r`. -/
def W6 (y r : ℝ) : ℝ := -7 * r * (y ^ 2 + y + 417 / 40)

theorem ray_certificate_d3 (y r : ℝ) :
    (P.eval (q y + (r : ℂ) * d3)).re - r ^ 2 * R3 y r
      = (T.map (algebraMap ℚ ℝ)).eval y * W3 y r := by
  rw [T_eval_real]
  norm_num [P, q, d3, R3, Kfun, Lfun, W3, A_value, B_value, Cconst_value,
    pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem ray_certificate_d6 (y r : ℝ) :
    (P.eval (q y + (r : ℂ) * d6)).re - r ^ 2 * R6 y r
      = (T.map (algebraMap ℚ ℝ)).eval y * W6 y r := by
  rw [T_eval_real]
  norm_num [P, q, d6, R6, Kfun, Lfun, W6, A_value, B_value, Cconst_value,
    pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem s1_ray_identity_d3' (y r : ℝ)
    (hT : (T.map (algebraMap ℚ ℝ)).eval y = 0) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) :
    (P.eval (q y + (r : ℂ) * d3)).re = r ^ 2 * R3 y r := by
  have hc := ray_certificate_d3 y r
  rw [hT, zero_mul] at hc
  exact sub_eq_zero.mp hc

theorem s1_ray_identity_d6' (y r : ℝ)
    (hT : (T.map (algebraMap ℚ ℝ)).eval y = 0) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) :
    (P.eval (q y + (r : ℂ) * d6)).re = r ^ 2 * R6 y r := by
  have hc := ray_certificate_d6 y r
  rw [hT, zero_mul] at hc
  exact sub_eq_zero.mp hc

/-! ## Positivity of both ray polynomials -/

theorem s1_R3_pos' (y r : ℝ) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) (hr : 0 ≤ r) :
    0 < R3 y r := by
  have hy0 : 0 ≤ y := by linarith
  have h2 := pow_le_pow_left₀ hy0 hhi.le 2
  have h3 := pow_le_pow_left₀ hy0 hhi.le 3
  norm_num at h2 h3
  have hK := s1_K_gt_180' y hlo hhi
  have hL := s1_negL_gt_188' y hlo hhi
  have h0 : 0 < 4 * Kfun y - 720 := by linarith
  have h1 : 0 ≤ (-2 * Lfun y - 376) * r :=
    mul_nonneg (by linarith) hr
  have h2r : 0 ≤ (492 - 840 * y ^ 3) * r ^ 2 :=
    mul_nonneg (by nlinarith only [h3]) (sq_nonneg r)
  have h3r : 0 ≤ (556 - 798 * y ^ 2) * r ^ 3 :=
    mul_nonneg (by nlinarith only [h2]) (pow_nonneg hr 3)
  have h4r : 0 ≤ (308 * y - 246) * r ^ 4 :=
    mul_nonneg (by linarith) (pow_nonneg hr 4)
  have hminor :
      278 * r ^ 5 + 246 * r ^ 4 - 556 * r ^ 3 - 492 * r ^ 2 + 376 * r + 720
        < R3 y r := by
    unfold R3
    nlinarith only [h0, h1, h2r, h3r, h4r]
  have hsq : 0 ≤ (r ^ 2 - 1) ^ 2 * (278 * r + 246) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hpositive :
      0 < 278 * r ^ 5 + 246 * r ^ 4 - 556 * r ^ 3 - 492 * r ^ 2 + 376 * r + 720 := by
    nlinarith only [hsq, hr]
  linarith only [hminor, hpositive]

theorem s1_R6_pos' (y r : ℝ) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) (hr : 0 ≤ r) :
    0 < R6 y r := by
  have hy : 0 < y := by linarith
  have hK : 0 < Kfun y := by linarith [s1_K_gt_180' y hlo hhi]
  have hL : 0 < -2 * Lfun y := by linarith [s1_negL_gt_188' y hlo hhi]
  by_cases hr5 : r ≤ 5 * y
  · have h4 := pow_le_pow_left₀ hy.le hhi.le 4
    norm_num at h4
    have hcoef : 0 < -2 * (A : ℝ) - 420 * y ^ 4 := by
      norm_num [A_value]
      nlinarith only [h4]
    have hr2 := pow_le_pow_left₀ hr hr5 2
    have h25 : 0 ≤ 25 * y ^ 2 - r ^ 2 := by nlinarith only [hr2]
    have he : R6 y r =
        2 * Kfun y + r * (-2 * (A : ℝ) - 420 * y ^ 4)
          + 8 * r ^ 3 * (r - 7 / 2 * y) ^ 2
          + 14 * y ^ 2 * r * (25 * y ^ 2 - r ^ 2) := by
      unfold R6 Lfun
      ring
    rw [he]
    positivity
  · have hr5' : 0 ≤ r - 5 * y := by linarith
    have he : R6 y r =
        2 * Kfun y + (-2 * Lfun y) * r
          + 4 * r ^ 3 * (2 * (r - 5 * y) ^ 2 + 6 * y * (r - 5 * y) + y ^ 2) := by
      unfold R6
      ring
    rw [he]
    positivity

/-! ## Trigonometry: identities first, then rational enclosures -/

theorem s1_sin_identity' :
    Real.sin (6 * Real.pi / 7) + Real.sin (12 * Real.pi / 7)
      = Real.sin (Real.pi / 7) - Real.sin (2 * Real.pi / 7) := by
  have h6 : 6 * Real.pi / 7 = Real.pi - Real.pi / 7 := by ring
  have h12 : 12 * Real.pi / 7 = 2 * Real.pi - 2 * Real.pi / 7 := by ring
  rw [h6, h12, Real.sin_pi_sub, Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]
  ring

private theorem mul_bounds_nonneg (a b l u m v : ℝ)
    (hl : 0 ≤ l) (hm : 0 ≤ m) (ha : l ≤ a ∧ a ≤ u) (hb : m ≤ b ∧ b ≤ v) :
    l * m ≤ a * b ∧ a * b ≤ u * v := by
  have ha0 : 0 ≤ a := hl.trans ha.1
  have hb0 : 0 ≤ b := hm.trans hb.1
  exact ⟨mul_le_mul ha.1 hb.1 hm ha0,
    mul_le_mul ha.2 hb.2 hb0 (ha0.trans ha.2)⟩

private theorem double_sin_cos_bounds (x sl su cl cu : ℝ)
    (hsl : 0 ≤ sl) (hcl : 0 ≤ cl)
    (hs : sl ≤ Real.sin x ∧ Real.sin x ≤ su)
    (hc : cl ≤ Real.cos x ∧ Real.cos x ≤ cu) :
    (2 * sl * cl ≤ Real.sin (2 * x) ∧ Real.sin (2 * x) ≤ 2 * su * cu) ∧
    (2 * cl ^ 2 - 1 ≤ Real.cos (2 * x) ∧ Real.cos (2 * x) ≤ 2 * cu ^ 2 - 1) := by
  have hm := mul_bounds_nonneg (Real.sin x) (Real.cos x) sl su cl cu hsl hcl hs hc
  have hcl2 := pow_le_pow_left₀ hcl hc.1 2
  have hcu2 := pow_le_pow_left₀ (hcl.trans hc.1) hc.2 2
  simp only [Real.sin_two_mul, Real.cos_two_mul]
  constructor <;> constructor <;> nlinarith only [hm.1, hm.2, hcl2, hcu2]

/-- The v4.29.1 remainders are `|x|^4 * (5/96)`, not the sharper bound
available on a later Mathlib branch. Evaluate at pi/56, then double twice. -/
private theorem small_angle_bounds :
    (560699 / 10000000 ≤ Real.sin (Real.pi / 56) ∧
      Real.sin (Real.pi / 56) ≤ 56071 / 1000000) ∧
    (9984258 / 10000000 ≤ Real.cos (Real.pi / 56) ∧
      Real.cos (Real.pi / 56) ≤ 998427 / 1000000) := by
  let x : ℝ := Real.pi / 56
  have hpiL := Real.pi_gt_d6
  have hpiU := Real.pi_lt_d6
  norm_num at hpiL hpiU
  have hxL : (3141592 : ℝ) / 56000000 ≤ x := by
    dsimp [x]
    linarith only [hpiL]
  have hxU : x ≤ (3141593 : ℝ) / 56000000 := by
    dsimp [x]
    linarith only [hpiU]
  have hx0 : 0 ≤ x := by linarith only [hxL]
  have hxabs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    linarith only [hxU]
  have hs := Real.sin_bound hxabs
  have hc := Real.cos_bound hxabs
  rw [abs_of_nonneg hx0] at hs hc
  rcases abs_le.mp hs with ⟨hsL, hsU⟩
  rcases abs_le.mp hc with ⟨hcL, hcU⟩
  have h2L := pow_le_pow_left₀ (show (0 : ℝ) ≤ 3141592 / 56000000 by norm_num) hxL 2
  have h2U := pow_le_pow_left₀ hx0 hxU 2
  have h3L := pow_le_pow_left₀ (show (0 : ℝ) ≤ 3141592 / 56000000 by norm_num) hxL 3
  have h3U := pow_le_pow_left₀ hx0 hxU 3
  have h4U := pow_le_pow_left₀ hx0 hxU 4
  norm_num at h2L h2U h3L h3U h4U
  change (560699 / 10000000 ≤ Real.sin x ∧ Real.sin x ≤ 56071 / 1000000) ∧
    (9984258 / 10000000 ≤ Real.cos x ∧ Real.cos x ≤ 998427 / 1000000)
  constructor
  · constructor
    · nlinarith only [hsL, hxL, h3U, h4U]
    · nlinarith only [hsU, hxU, h3L, h4U]
  · constructor
    · nlinarith only [hcL, h2U, h4U]
    · nlinarith only [hcU, h2L, h4U]

private theorem angle_fourteen_bounds :
    (2225174 / 10000000 ≤ Real.sin (Real.pi / 14) ∧
      Real.sin (Real.pi / 14) ≤ 2225236 / 10000000) ∧
    (9749115 / 10000000 ≤ Real.cos (Real.pi / 14) ∧
      Real.cos (Real.pi / 14) ≤ 9749311 / 10000000) := by
  have h0 := small_angle_bounds
  have h1 := double_sin_cos_bounds (Real.pi / 56)
    (560699 / 10000000) (56071 / 1000000) (9984258 / 10000000) (998427 / 1000000)
    (by norm_num) (by norm_num) h0.1 h0.2
  rw [show 2 * (Real.pi / 56) = Real.pi / 28 by ring] at h1
  have h1s : 1119632 / 10000000 ≤ Real.sin (Real.pi / 28) ∧
      Real.sin (Real.pi / 28) ≤ 1119657 / 10000000 := by
    constructor <;> nlinarith only [h1.1.1, h1.1.2]
  have h1c : 9937081 / 10000000 ≤ Real.cos (Real.pi / 28) ∧
      Real.cos (Real.pi / 28) ≤ 993713 / 1000000 := by
    constructor <;> nlinarith only [h1.2.1, h1.2.2]
  have h2 := double_sin_cos_bounds (Real.pi / 28)
    (1119632 / 10000000) (1119657 / 10000000) (9937081 / 10000000) (993713 / 1000000)
    (by norm_num) (by norm_num) h1s h1c
  rw [show 2 * (Real.pi / 28) = Real.pi / 14 by ring] at h2
  constructor
  · constructor <;> nlinarith only [h2.1.1, h2.1.2]
  · constructor <;> nlinarith only [h2.2.1, h2.2.2]

/-- A small-angle polynomial expression for the sine difference. -/
theorem sin_difference_identity :
    Real.sin (2 * Real.pi / 7) - Real.sin (Real.pi / 7)
      = 2 * Real.sin (Real.pi / 14) * Real.cos (Real.pi / 14)
          * (1 - 4 * Real.sin (Real.pi / 14) ^ 2) := by
  have ha : 2 * Real.pi / 7 = 2 * (2 * (Real.pi / 14)) := by ring
  have hb : Real.pi / 7 = 2 * (Real.pi / 14) := by ring
  rw [ha, hb]
  simp only [Real.sin_two_mul, Real.cos_two_mul_eq_one_sub]
  ring

/-- A fully rational enclosure used both in the repaired theorem and in the
explicit disproof of the original interval-only interface. -/
theorem sin_difference_bounds :
    3479 / 10000 ≤ Real.sin (2 * Real.pi / 7) - Real.sin (Real.pi / 7) ∧
    Real.sin (2 * Real.pi / 7) - Real.sin (Real.pi / 7) ≤ 87 / 250 := by
  have h := angle_fourteen_bounds
  let s0 : ℝ := Real.sin (Real.pi / 14)
  let c0 : ℝ := Real.cos (Real.pi / 14)
  have hs : 2225174 / 10000000 ≤ s0 ∧ s0 ≤ 2225236 / 10000000 := h.1
  have hc : 9749115 / 10000000 ≤ c0 ∧ c0 ≤ 9749311 / 10000000 := h.2
  have hs0 : 0 ≤ s0 := by linarith only [hs.1]
  have hsqL := pow_le_pow_left₀
    (show (0 : ℝ) ≤ 2225174 / 10000000 by norm_num) hs.1 2
  have hsqU := pow_le_pow_left₀ hs0 hs.2 2
  have hf : 1 - 4 * (2225236 / 10000000 : ℝ) ^ 2 ≤ 1 - 4 * s0 ^ 2 ∧
      1 - 4 * s0 ^ 2 ≤ 1 - 4 * (2225174 / 10000000 : ℝ) ^ 2 := by
    constructor <;> nlinarith only [hsqL, hsqU]
  have hsc := mul_bounds_nonneg s0 c0
    (2225174 / 10000000) (2225236 / 10000000)
    (9749115 / 10000000) (9749311 / 10000000)
    (by norm_num) (by norm_num) hs hc
  have hprod := mul_bounds_nonneg (s0 * c0) (1 - 4 * s0 ^ 2)
    ((2225174 / 10000000) * (9749115 / 10000000))
    ((2225236 / 10000000) * (9749311 / 10000000))
    (1 - 4 * (2225236 / 10000000 : ℝ) ^ 2)
    (1 - 4 * (2225174 / 10000000 : ℝ) ^ 2)
    (by norm_num) (by norm_num) hsc hf
  rw [sin_difference_identity]
  change 3479 / 10000 ≤ 2 * s0 * c0 * (1 - 4 * s0 ^ 2) ∧
    2 * s0 * c0 * (1 - 4 * s0 ^ 2) ≤ 87 / 250
  constructor <;> nlinarith only [hprod.1, hprod.2]

/-- Corrected interface: the missing root hypothesis is explicit. -/
theorem s1_alpha_ge' (y : ℝ) (hlo : 4 / 5 < y) (hhi : y < 5 / 6)
    (hT : (T.map (algebraMap ℚ ℝ)).eval y = 0) :
    143 / 500 ≤ alpha y := by
  have hy := root_y_gt_823 y hT hlo
  have hd := sin_difference_bounds.1
  have hprod := mul_le_mul_of_nonneg_left hd (show 0 ≤ y by linarith)
  unfold alpha
  nlinarith only [hprod, hy]

/-- An alternative authorised by the packet: a weaker constant, with exactly
the original interval hypotheses. It is not silently substituted above. -/
theorem s1_alpha_ge_quarter' (y : ℝ) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) :
    1 / 4 ≤ alpha y := by
  have hd := sin_difference_bounds.1
  have hprod := mul_le_mul_of_nonneg_left hd (show 0 ≤ y by linarith)
  unfold alpha
  nlinarith only [hprod, hlo]

/-- A rational counterexample to the supplied interval-only conclusion. -/
theorem s1_alpha_original_counterexample' :
    (4 / 5 : ℝ) < 81 / 100 ∧ (81 / 100 : ℝ) < 5 / 6 ∧
      alpha (81 / 100) < 143 / 500 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have hd := sin_difference_bounds.2
  unfold alpha
  nlinarith only [hd]

private theorem u_im (j : ℕ) :
    (u j).im = Real.sin (2 * Real.pi * (j : ℝ) / 7) := by
  unfold u
  have he : 2 * (Real.pi : ℂ) * (j : ℂ) * Complex.I / 7
      = ((2 * Real.pi * (j : ℝ) / 7 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he]
  exact Complex.exp_ofReal_mul_I_im _

theorem s1_projection_exact' (y : ℝ) :
    (q y * (conj (u 3) + conj (u 6))).re = -alpha y := by
  have h3 : (u 3).im = Real.sin (6 * Real.pi / 7) := by
    rw [u_im]
    congr 1
    norm_num <;> ring
  have h6 : (u 6).im = Real.sin (12 * Real.pi / 7) := by
    rw [u_im]
    congr 1
    norm_num <;> ring
  calc
    (q y * (conj (u 3) + conj (u 6))).re
        = y * ((u 3).im + (u 6).im) := by
          simp [q, Complex.mul_re, Complex.mul_im] <;> ring
    _ = y * (Real.sin (6 * Real.pi / 7) + Real.sin (12 * Real.pi / 7)) := by rw [h3, h6]
    _ = -alpha y := by rw [s1_sin_identity']; unfold alpha; ring

end Erdos1041.Counterexample.Algebra

/-! ## Interface re-exports

The nineteen S1 obligations at their original fully qualified names
`Erdos1041.Counterexample.s1_*`.  Each statement is restated verbatim from the
archived stub interface, so any drift between the proofs above and the contract
is a compile error here rather than a silent weakening.  The single accepted
delta is `s1_alpha_ge`, which carries the root hypothesis `hT`; the original
interval-only form is refuted by `s1_alpha_original_counterexample` and the
interval-only weaker constant survives as `s1_alpha_ge_quarter`.
-/

namespace Erdos1041.Counterexample

theorem s1_derivative_factorisation :
    Polynomial.derivative S
      = Polynomial.C 7 * (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C t) * T :=
  Algebra.s1_derivative_factorisation'

theorem s1_value_factorisation :
    S + Polynomial.C (t ^ 2 * (6 * t - 4))
      = (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C t) ^ 2 *
        (Polynomial.X ^ 3 - Polynomial.C 2 * Polynomial.X ^ 2
          + Polynomial.C (3 - 2 * t) * Polynomial.X + Polynomial.C (6 * t - 4)) :=
  Algebra.s1_value_factorisation'

theorem s1_T_integral_form :
    Polynomial.C (5600 : ℚ) * T
      = Polynomial.C 5600 * Polynomial.X ^ 4 - Polynomial.C 5600 * Polynomial.X ^ 3
        - Polynomial.C 52780 * Polynomial.X ^ 2 + Polynomial.C 111160 * Polynomial.X
        - Polynomial.C 55189 :=
  Algebra.s1_T_integral_form'

theorem s1_T_sign_table :
    0 < T.eval (-18 / 5) ∧ T.eval (-7 / 2) < 0 ∧ T.eval (4 / 5) < 0 ∧
      0 < T.eval (5 / 6) ∧ 0 < T.eval (9 / 5) ∧ T.eval (11 / 6) < 0 ∧
      0 < T.eval 2 :=
  Algebra.s1_T_sign_table'

theorem s1_root_y2 :
    ∃ y : ℝ, 4 / 5 < y ∧ y < 5 / 6 ∧ (T.map (algebraMap ℚ ℝ)).eval y = 0 :=
  Algebra.s1_root_y2'

theorem s1_reG_imaginary_axis (y : ℝ) :
    (G.eval ((y : ℂ) * Complex.I)).re = -y * (y + 18 / 5) * (y - 9 / 5) :=
  Algebra.s1_reG_imaginary_axis' y

theorem s1_reG_nonreal_critical (σ : ℝ) (hσ : σ ^ 2 = (t : ℝ) - 1 / 4) :
    (G.eval ((σ : ℂ) - Complex.I / 2)).re = -41 / 80 :=
  Algebra.s1_reG_nonreal_critical' σ hσ

theorem s1_reG_sign_at_critical_ordinates
    (y : ℝ) (hT : (T.map (algebraMap ℚ ℝ)).eval y = 0) :
    (0 < (G.eval (q y)).re ↔ (4 / 5 < y ∧ y < 5 / 6)) :=
  Algebra.s1_reG_sign_at_critical_ordinates' y hT

theorem s1_K_gt_180 (y : ℝ) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) : 180 < Kfun y :=
  Algebra.s1_K_gt_180' y hlo hhi

theorem s1_negL_gt_188 (y : ℝ) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) : 188 < -Lfun y :=
  Algebra.s1_negL_gt_188' y hlo hhi

theorem s1_d3_pow_seven : d3 ^ 7 = 278 - 29 * Complex.I :=
  Algebra.s1_d3_pow_seven'

theorem s1_d6_pow_seven : d6 ^ 7 = 8 + 8 * Complex.I :=
  Algebra.s1_d6_pow_seven'

theorem s1_ray_identity_d3 (y r : ℝ)
    (hT : (T.map (algebraMap ℚ ℝ)).eval y = 0) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) :
    (P.eval (q y + (r : ℂ) * d3)).re = r ^ 2 * R3 y r :=
  Algebra.s1_ray_identity_d3' y r hT hlo hhi

theorem s1_ray_identity_d6 (y r : ℝ)
    (hT : (T.map (algebraMap ℚ ℝ)).eval y = 0) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) :
    (P.eval (q y + (r : ℂ) * d6)).re = r ^ 2 * R6 y r :=
  Algebra.s1_ray_identity_d6' y r hT hlo hhi

theorem s1_R3_pos (y r : ℝ) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) (hr : 0 ≤ r) :
    0 < R3 y r :=
  Algebra.s1_R3_pos' y r hlo hhi hr

theorem s1_R6_pos (y r : ℝ) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) (hr : 0 ≤ r) :
    0 < R6 y r :=
  Algebra.s1_R6_pos' y r hlo hhi hr

theorem s1_sin_identity :
    Real.sin (6 * Real.pi / 7) + Real.sin (12 * Real.pi / 7)
      = Real.sin (Real.pi / 7) - Real.sin (2 * Real.pi / 7) :=
  Algebra.s1_sin_identity'

/-- STATEMENT DELTA: the root hypothesis `hT` is added.  The interval-only form
is false; see `s1_alpha_original_counterexample`. -/
theorem s1_alpha_ge (y : ℝ) (hlo : 4 / 5 < y) (hhi : y < 5 / 6)
    (hT : (T.map (algebraMap ℚ ℝ)).eval y = 0) :
    143 / 500 ≤ alpha y :=
  Algebra.s1_alpha_ge' y hlo hhi hT

theorem s1_alpha_ge_quarter (y : ℝ) (hlo : 4 / 5 < y) (hhi : y < 5 / 6) :
    1 / 4 ≤ alpha y :=
  Algebra.s1_alpha_ge_quarter' y hlo hhi

theorem s1_alpha_original_counterexample :
    (4 / 5 : ℝ) < 81 / 100 ∧ (81 / 100 : ℝ) < 5 / 6 ∧
      alpha (81 / 100) < 143 / 500 :=
  Algebra.s1_alpha_original_counterexample'

theorem s1_projection_exact (y : ℝ) :
    (q y * (conj (u 3) + conj (u 6))).re = -alpha y :=
  Algebra.s1_projection_exact' y

end Erdos1041.Counterexample

