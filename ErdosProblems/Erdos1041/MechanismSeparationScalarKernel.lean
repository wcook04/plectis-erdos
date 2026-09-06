import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Erdős #1041: scalar kernels for two mechanism separations

Two returned negative results reduce to exact scalar inequalities.  This module
checks those decidable cores.  The analytic superstructure — arm-length
continuation on a saddle-connection wall, the exact petal-area integral, Jensen
against `∫_{-π/2}^{π/2} log (2 cos θ) dθ = 0`, and the Riemann–Hurwitz component
count — is **not** formalised here and is not asserted.

## What is refuted

* **Section A (saddle wall).**  On an open family of quartics with simple roots
  strictly inside the unit disc, separated critical rays, all critical values
  admissible, and a single admissible component, the *componentwise
  combined-charge inequality* `∑_{e ⊂ C} (D_e + K_e) ≥ 0` and the *full
  admissible-arc product* `∏_j q_j ≤ 1` are both **FALSE**.  The first-order
  defect is `-4 s_ρ κ ρ < 0` respectively `log ∏ q_j = 2 κ ρ > 0`, strictly,
  hence false on an open coefficient neighbourhood.  Refutation 3 extends this
  to *every* smooth symmetric monotone aggregate: the first-order perturbation
  vector `d = ((x₂+κ)/2, κ, (κ-x₂)/2)` has strictly positive coordinate sum `2κ`
  and a strictly negative coordinate, so any `C¹` permutation-invariant `Φ` with
  `∇Φ(1,1,1) = lam · (1,1,1)`, `lam > 0`, moves the wrong way.  The surviving
  candidate statistic must therefore be order-sensitive and non-smooth at the
  equality configuration.
* **Section B (merge-node Bergman).**  The *connected-cluster Bergman certificate
  itself remains CORRECT and is not touched*: whenever
  `𝓑(C,t) = α_C log ((1 + q_C^{2/k}) / (1 - q_C^{2/k})) ≤ 2` holds, it still
  produces a contained root-to-root curve of length at most `2 t^{1/n}` — that
  consumer is `ConnectedClusterBergman.length_le_two_of_cluster_certificate`.
  What is refuted is the **universal forcing claim** `∀ g, ∃ (C,t), 𝓑(C,t) ≤ 2`.
  On `z^n − r^n` at `r = 99/100` the barrier exceeds `2` with the uniform
  rational margin `2541/1250 = 2 + 41/1250`, at every regular level and in every
  degree.

## What is NOT refuted

Erdős #1041 (Erdős–Herzog–Piranian) is **open**, and nothing here bears on its
truth.  Both refuting families in fact **satisfy** the parent statement: the
saddle-wall quartics by the short selected arm (`q₃ < 1` with `|v₃| < 1` gives
`L₃ < 2 |v₃|^{1/4} < 2` inside `{|f| ≤ |v₃|} ⊆ {|f| < 1}`, and the trimmed pair
`q₂ q₃ < 1` still holds by the sharp slope bound below), and the `z^n − r^n`
family by the grouped lollipop lift of length `2r − 2(1 − π/n) s < 2`.  Refuting
a mechanism is not refuting the problem.  What these kernels retire is a *proof
strategy*: a componentwise or smooth-symmetric charge aggregate, and a one-node
(or two-node) completed-Bergman forcing argument.
-/

namespace ErdosProblems.Erdos1041.MechanismSeparationScalarKernel

noncomputable section

/-! ## A.1 The saddle-wall normal form -/

/-- Normalised upper-branch profile.  With `t = x₂`, `lam = 2 t²/a ∈ (0,1/3)`,
`b = 4 t³ (1-lam)/lam` and `x = t r`, the branch equation `y² = h(x)` becomes
`h (t r) = t² * wallH lam r`. -/
def wallH (lam r : ℝ) : ℝ := r ^ 2 - 1 / lam + (1 - lam) / (lam * r)

/-- The `r`-derivative of `wallH lam`, as an explicit rational function. -/
def wallH' (lam r : ℝ) : ℝ := 2 * r - (1 - lam) / (lam * r ^ 2)

/-- Numerator of `wallH' ^ 2 - 12 * wallH` after clearing `lam ^ 2 * r ^ 4 > 0`.
Nonnegativity of `wallN` is exactly the sharp slope bound `σ² ≤ 1/3`. -/
def wallN (lam r : ℝ) : ℝ :=
  1 + lam * (12 * r ^ 4 - 16 * r ^ 3 - 2) + lam ^ 2 * (-8 * r ^ 6 + 16 * r ^ 3 + 1)

/-- The auxiliary polynomial with `∂_lam (wallN lam r) = -2 * wallBaux lam r`. -/
def wallBaux (lam r : ℝ) : ℝ :=
  1 - 6 * r ^ 4 + 8 * r ^ 3 + lam * (8 * r ^ 6 - 16 * r ^ 3 - 1)

/-! ## A.2 The two polynomial factorisations -/

/-- Exact factorisation of `wallBaux` at the endpoint `lam = 1/3`. -/
theorem wallBaux_one_third_factor (r : ℝ) :
    wallBaux (1 / 3) r = 2 / 3 * (1 - r) ^ 2 * (2 * r + 1) * (2 * r ^ 3 + 3 * r ^ 2 + 1) := by
  simp only [wallBaux]
  ring

/-- Exact factorisation of `wallN` at the endpoint `lam = 1/3`. -/
theorem wallN_one_third_factor (r : ℝ) :
    wallN (1 / 3) r = 4 / 9 * (1 - r) ^ 3 * (2 * r ^ 3 + 6 * r ^ 2 + 3 * r + 1) := by
  simp only [wallN]
  ring

/-! ## A.3 The sharp slope bound -/

/-- The bracket multiplying `lam` in `wallBaux` is strictly negative on `[0,1]`,
which is what makes `wallBaux` antitone in `lam`. -/
theorem wall_bracket_neg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    8 * r ^ 6 - 16 * r ^ 3 - 1 < 0 := by
  have hs : 0 ≤ r ^ 3 := pow_nonneg hr0 3
  have hs1 : r ^ 3 ≤ 1 := pow_le_one₀ hr0 hr1
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1), hs]

/-- `wallBaux (1/3) ·` is nonnegative on `[0, ∞)`. -/
theorem wallBaux_one_third_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ wallBaux (1 / 3) r := by
  rw [wallBaux_one_third_factor]
  have h1 : (0 : ℝ) ≤ (1 - r) ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * r + 1 := by linarith
  have h3 : (0 : ℝ) ≤ 2 * r ^ 3 + 3 * r ^ 2 + 1 := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3

/-- `wallBaux lam r ≥ 0` for `0 < lam ≤ 1/3` and `0 < r ≤ 1`. -/
theorem wallBaux_nonneg {lam r : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 3)
    (hr0 : 0 < r) (hr1 : r ≤ 1) : 0 ≤ wallBaux lam r := by
  have hid : wallBaux lam r
      = wallBaux (1 / 3) r + (1 / 3 - lam) * -(8 * r ^ 6 - 16 * r ^ 3 - 1) := by
    simp only [wallBaux]
    ring
  have hneg := wall_bracket_neg hr0.le hr1
  have hbase := wallBaux_one_third_nonneg hr0.le
  have hprod : 0 ≤ (1 / 3 - lam) * -(8 * r ^ 6 - 16 * r ^ 3 - 1) :=
    mul_nonneg (by linarith) (by linarith)
  rw [hid]
  exact add_nonneg hbase hprod

/-- `wallN (1/3) ·` is nonnegative on `[0,1]`. -/
theorem wallN_one_third_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ wallN (1 / 3) r := by
  rw [wallN_one_third_factor]
  have h1 : (0 : ℝ) ≤ (1 - r) ^ 3 := pow_nonneg (by linarith) 3
  have h2 : (0 : ℝ) ≤ 2 * r ^ 3 + 6 * r ^ 2 + 3 * r + 1 := by
    nlinarith [pow_nonneg hr0 3, sq_nonneg r]
  exact mul_nonneg (mul_nonneg (by norm_num) h1) h2

/-- Exact midpoint identity replacing the derivative argument.  `wallN` is a
quadratic in `lam` with `∂_lam wallN = -2 * wallBaux`, so its increment between
`lam` and `1/3` is the step times the midpoint value of `-2 * wallBaux`. -/
theorem wallN_sub_one_third (lam r : ℝ) :
    wallN lam r - wallN (1 / 3) r
      = (1 / 3 - lam) * (2 * wallBaux ((lam + 1 / 3) / 2) r) := by
  simp only [wallN, wallBaux]
  ring

/-- **The sharp slope bound.**  `wallN lam r ≥ 0` for `0 < lam ≤ 1/3` and
`0 < r ≤ 1`; equivalently `wallH' lam r ^ 2 - 12 * wallH lam r ≥ 0`, i.e.
`σ² ≤ 1/3` for the curved arm leaving the middle saddle. -/
theorem wallN_nonneg {lam r : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 3)
    (hr0 : 0 < r) (hr1 : r ≤ 1) : 0 ≤ wallN lam r := by
  have hmid0 : 0 < (lam + 1 / 3) / 2 := by linarith
  have hmid : (lam + 1 / 3) / 2 ≤ 1 / 3 := by linarith
  have hB := wallBaux_nonneg hmid0 hmid hr0 hr1
  have hbase := wallN_one_third_nonneg hr0.le hr1
  have hprod : 0 ≤ (1 / 3 - lam) * (2 * wallBaux ((lam + 1 / 3) / 2) r) :=
    mul_nonneg (by linarith) (by linarith)
  have hid := wallN_sub_one_third lam r
  linarith

/-! ## A.4 `wallN` really is the cleared slope numerator -/

/-- `wallH' lam` is the derivative of `wallH lam` away from `r = 0`.  Stated
against the explicit `wallH'` rather than `deriv`, which is the honest form: the
`HasDerivAt` statement is proved here, no `deriv` rewriting is assumed. -/
theorem hasDerivAt_wallH {lam r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (wallH lam) (wallH' lam r) r := by
  have hfun : wallH lam = fun x : ℝ => x ^ 2 - 1 / lam + (1 - lam) / lam * x⁻¹ := by
    funext x
    simp only [wallH]
    ring
  have hval : wallH' lam r = 2 * r + (1 - lam) / lam * -(r ^ 2)⁻¹ := by
    simp only [wallH']
    ring
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have h2 : HasDerivAt (fun x : ℝ => x⁻¹) (-(r ^ 2)⁻¹) r := hasDerivAt_inv hr
  rw [hfun, hval]
  exact (h1.sub_const (1 / lam)).add (h2.const_mul ((1 - lam) / lam))

/-- The exact clearing identity: `wallN` is `lam ^ 2 * r ^ 4` times the slope
defect `wallH' ^ 2 - 12 * wallH`. -/
theorem wallN_eq_cleared_slope {lam r : ℝ} (hlam : lam ≠ 0) (hr : r ≠ 0) :
    wallN lam r = lam ^ 2 * r ^ 4 * (wallH' lam r ^ 2 - 12 * wallH lam r) := by
  simp only [wallN, wallH, wallH']
  field_simp
  ring

/-- Consequence: on the admissible parameter range the slope defect itself is
nonnegative, which is the statement `σ² = 4 H / H'² ≤ 1/3`. -/
theorem slope_defect_nonneg {lam r : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 3)
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    0 ≤ wallH' lam r ^ 2 - 12 * wallH lam r := by
  have hpos : 0 < lam ^ 2 * r ^ 4 := by positivity
  have hN := wallN_nonneg hlam0 hlam hr0 hr1
  rw [wallN_eq_cleared_slope (ne_of_gt hlam0) (ne_of_gt hr0)] at hN
  by_contra hcon
  push_neg at hcon
  nlinarith [hN, hpos, hcon]

/-! ## A.5 The curved-excess constant `2 - √3` -/

/-- `2 - √3 < 1/3`, i.e. `3 √3 > 5`. -/
theorem two_sub_sqrt_three_lt_one_third : 2 - Real.sqrt 3 < 1 / 3 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]

/-- Sharp linear majorant for the arclength excess on the slope range
`0 ≤ u ≤ 1/√3` produced by the sharp slope bound.  Equality holds at
`u = 1/√3`. -/
theorem sqrt_excess_le {u : ℝ} (hu : 0 ≤ u) (hu3 : u ≤ 1 / Real.sqrt 3) :
    Real.sqrt (1 + u ^ 2) - 1 ≤ (2 - Real.sqrt 3) * u := by
  have ht2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have htpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt (1 + u ^ 2) ^ 2 = 1 + u ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (1 + u ^ 2) := Real.sqrt_nonneg _
  set t := Real.sqrt 3 with hts
  set s := Real.sqrt (1 + u ^ 2) with hss
  have htlt : t < 2 := by nlinarith [ht2, htpos]
  have htgt : 5 / 3 < t := by nlinarith [ht2, htpos]
  have hut : t * u ≤ 1 := by
    have h : u * t ≤ 1 := (le_div_iff₀ htpos).mp hu3
    linarith [h]
  have hs1 : 1 ≤ s := by nlinarith [hs2, hs0, sq_nonneg u]
  have hc : 0 < 2 - t := by linarith
  have hstep : 0 ≤ ((2 - t) ^ 2 - 1) * u + 2 * (2 - t) := by
    have hfac : ((2 - t) ^ 2 - 1) * u + 2 * (2 - t) = 2 * (2 - t) * (1 - t * u) := by
      linear_combination (-u) * ht2
    rw [hfac]
    exact mul_nonneg (by linarith) (by linarith)
  have hcs : ((2 - t) * s) ^ 2 = (2 - t) ^ 2 * (1 + u ^ 2) := by
    rw [mul_pow, hs2]
  have hsq : (u - (2 - t)) ^ 2 ≤ ((2 - t) * s) ^ 2 := by
    rw [hcs]
    nlinarith [mul_nonneg hu hstep]
  have hcs0 : 0 ≤ (2 - t) * s := mul_nonneg hc.le hs0
  have hle : u - (2 - t) ≤ (2 - t) * s := by nlinarith [hsq, hcs0]
  have hA : u ≤ (2 - t) * (s + 1) := by nlinarith [hle]
  have hB : u * u ≤ (2 - t) * (s + 1) * u := mul_le_mul_of_nonneg_right hA hu
  have hs1pos : (0 : ℝ) < s + 1 := by linarith
  have hC : (s - 1) * (s + 1) ≤ (2 - t) * u * (s + 1) := by nlinarith [hs2, hB]
  exact le_of_mul_le_mul_right hC hs1pos

/-- The composed conclusion of the sharp slope bound: the curved-ray excess `κ`
satisfies `3 κ < x₂`, since `κ ≤ (2 - √3) x₂` and `2 - √3 < 1/3`. -/
theorem curved_excess_lt_third {x₂ κ : ℝ} (hx : 0 < x₂)
    (hκb : κ ≤ (2 - Real.sqrt 3) * x₂) : 3 * κ < x₂ := by
  nlinarith [hκb, two_sub_sqrt_three_lt_one_third, hx]

/-! ## A.6 The finite intercept algebra -/

/-- Renormalised intercept of the wall arm through the negative real stem. -/
def wallB₁ (x₂ κ : ℝ) : ℝ := -x₂ - κ

/-- Renormalised intercept of the doubly curved wall arm. -/
def wallB₂ (κ : ℝ) : ℝ := -2 * κ

/-- Renormalised intercept of the short selected arm. -/
def wallB₃ (x₂ κ : ℝ) : ℝ := x₂ - κ

/-- The positive and negative real stems cancel exactly, leaving four copies of
the curved excess. -/
theorem wall_intercept_sum (x₂ κ : ℝ) :
    wallB₁ x₂ κ + wallB₂ κ + wallB₃ x₂ κ = -4 * κ := by
  simp only [wallB₁, wallB₂, wallB₃]
  ring

/-- Discarding the single worst continuation restores a strict saving. -/
theorem wall_trimmed_intercept_sum (x₂ κ : ℝ) :
    wallB₂ κ + wallB₃ x₂ κ = x₂ - 3 * κ := by
  simp only [wallB₂, wallB₃]
  ring

/-- **The whole point.**  Under the separation `3 κ < x₂` supplied by the sharp
slope bound, the full three-edge aggregate is strictly negative while the
trimmed pair is strictly positive.  This is why every smooth symmetric monotone
aggregate of the three normalised arm ratios has the wrong first-order sign, and
why the surviving candidate must be order-sensitive. -/
theorem wall_sign_pattern {x₂ κ : ℝ} (hx : 0 < x₂) (hκ : 0 < κ) (hsep : 3 * κ < x₂) :
    wallB₁ x₂ κ < 0 ∧ wallB₂ κ < 0 ∧ 0 < wallB₃ x₂ κ ∧ 0 < wallB₂ κ + wallB₃ x₂ κ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [wallB₁, wallB₂, wallB₃] <;> linarith

/-! ## A.7 The tangent-cone obstruction -/

/-- The first-order perturbation vector of the normalised arm ratios,
`q_j = 1 + ρ * d_j + o(ρ)`. -/
def wallFirstOrder (x₂ κ : ℝ) : ℝ × ℝ × ℝ := ((x₂ + κ) / 2, κ, (κ - x₂) / 2)

@[simp] theorem wallFirstOrder_fst (x₂ κ : ℝ) :
    (wallFirstOrder x₂ κ).1 = (x₂ + κ) / 2 := rfl

@[simp] theorem wallFirstOrder_snd_fst (x₂ κ : ℝ) :
    (wallFirstOrder x₂ κ).2.1 = κ := rfl

@[simp] theorem wallFirstOrder_snd_snd (x₂ κ : ℝ) :
    (wallFirstOrder x₂ κ).2.2 = (κ - x₂) / 2 := rfl

/-- **Refutation 3, exact tangent-cone form.**  The coordinate sum of the
first-order vector is `2 κ > 0` while its last coordinate is strictly negative,
and the trimmed pair sums strictly negatively.  So the full product moves up
(`∏ q_j > 1`, refuting the admissible-arc product) while the trimmed pair moves
down (`q₂ q₃ < 1`, leaving the order-sensitive candidate alive). -/
theorem smooth_symmetric_aggregate_first_order_sign {x₂ κ : ℝ}
    (hκ : 0 < κ) (hsep : 3 * κ < x₂) :
    (wallFirstOrder x₂ κ).1 + (wallFirstOrder x₂ κ).2.1 + (wallFirstOrder x₂ κ).2.2 = 2 * κ ∧
      0 < (wallFirstOrder x₂ κ).1 + (wallFirstOrder x₂ κ).2.1 + (wallFirstOrder x₂ κ).2.2 ∧
      (wallFirstOrder x₂ κ).2.2 < 0 ∧
      (wallFirstOrder x₂ κ).2.1 + (wallFirstOrder x₂ κ).2.2 < 0 := by
  simp only [wallFirstOrder_fst, wallFirstOrder_snd_fst, wallFirstOrder_snd_snd]
  refine ⟨by ring, by linarith, by linarith, by linarith⟩

/-- Every `C¹` permutation-invariant `Φ` with `Φ (1,1,1) = 1` has
`∇Φ (1,1,1) = lam · (1,1,1)`, with `lam > 0` for a monotone mean.  Its
directional derivative along the first-order vector is `2 lam κ > 0`, so
`Φ (q₁,q₂,q₃) = 1 + 2 lam κ ρ + o(ρ) > 1` and the aggregate inequality fails.
This kills arithmetic, geometric, harmonic, power, elementary-symmetric and
log-sum-exp means simultaneously. -/
theorem symmetric_monotone_gradient_first_order_positive {x₂ κ lam : ℝ}
    (hκ : 0 < κ) (hlam : 0 < lam) :
    0 < lam * (wallFirstOrder x₂ κ).1 + lam * (wallFirstOrder x₂ κ).2.1
      + lam * (wallFirstOrder x₂ κ).2.2 := by
  have h : lam * (wallFirstOrder x₂ κ).1 + lam * (wallFirstOrder x₂ κ).2.1
      + lam * (wallFirstOrder x₂ κ).2.2 = 2 * lam * κ := by
    simp only [wallFirstOrder_fst, wallFirstOrder_snd_fst, wallFirstOrder_snd_snd]
    ring
  rw [h]
  positivity

/-! ## B.1 The rational logarithm certificate -/

/-- `log 2 > 56/81`.  Route used: mathlib's `Real.log_two_gt_d9`, which is
stronger than the truncated `artanh` series bound quoted by the return. -/
theorem log_two_gt_56_div_81 : (56 : ℝ) / 81 < Real.log 2 :=
  lt_of_lt_of_le (by norm_num) Real.log_two_gt_d9.le

/-- At `r = 99/100` the regular-level ratio `(1 + x₀)/(1 - x₀) = 19801/199`
exceeds `64`, because `64 * 199 = 12736 < 19801`. -/
theorem regular_ratio_gt_sixty_four :
    (64 : ℝ) < (1 + 9801 / 10000) / (1 - 9801 / 10000) := by
  norm_num

/-- `log 64 = 6 log 2 > 112/27`. -/
theorem log_sixty_four_gt : (112 : ℝ) / 27 < Real.log 64 := by
  have h : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [h]
  linarith [log_two_gt_56_div_81]

/-- **The exact rational margin.**  At `r = 99/100` the connected-cluster Bergman
barrier lower bound exceeds `2541/1250 = 2 + 41/1250 > 2`.  The bound is
degree-free and holds at every regular level `μ < t ≤ 1`, so the certificate
fails on this family with a uniform positive margin. -/
theorem rational_cluster_margin :
    (2541 : ℝ) / 1250 <
      9801 / 20000 * Real.log ((1 + 9801 / 10000) / (1 - 9801 / 10000)) := by
  have hlog : Real.log 64 < Real.log ((1 + 9801 / 10000) / (1 - 9801 / 10000)) :=
    Real.log_lt_log (by norm_num) regular_ratio_gt_sixty_four
  have h1 : (112 : ℝ) / 27 < Real.log ((1 + 9801 / 10000) / (1 - 9801 / 10000)) :=
    lt_trans log_sixty_four_gt hlog
  linarith

/-- The margin is strictly above the certificate threshold `2`. -/
theorem rational_cluster_margin_gt_two : (2 : ℝ) < 2541 / 1250 := by norm_num

/-! ## B.2 The barrier as a monotone scalar -/

/-- The connected-cluster Bergman barrier `𝓑(C,t) = α_C log ((1+q)/(1-q))` as a
scalar function of its two inputs. -/
def clusterBarrierScalar (α q : ℝ) : ℝ := α * Real.log ((1 + q) / (1 - q))

/-- The barrier logarithm is nonnegative on `[0,1)`. -/
theorem log_ratio_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ Real.log ((1 + q) / (1 - q)) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The barrier logarithm is monotone on `[0,1)`. -/
theorem log_ratio_mono {q₀ q : ℝ} (hq0 : 0 ≤ q₀) (hq : q₀ ≤ q) (hq1 : q < 1) :
    Real.log ((1 + q₀) / (1 - q₀)) ≤ Real.log ((1 + q) / (1 - q)) := by
  have h0' : (0 : ℝ) < 1 - q₀ := by linarith
  have h0 : (0 : ℝ) < 1 - q := by linarith
  have hratio : (1 + q₀) / (1 - q₀) ≤ (1 + q) / (1 - q) := by
    rw [div_le_div_iff₀ h0' h0]
    nlinarith
  exact Real.log_le_log (div_pos (by linarith) h0') hratio

/-- The barrier logarithm is strictly monotone on `[0,1)`. -/
theorem log_ratio_strictMono {q₀ q : ℝ} (hq0 : 0 ≤ q₀) (hq : q₀ < q) (hq1 : q < 1) :
    Real.log ((1 + q₀) / (1 - q₀)) < Real.log ((1 + q) / (1 - q)) := by
  have h0' : (0 : ℝ) < 1 - q₀ := by linarith
  have h0 : (0 : ℝ) < 1 - q := by linarith
  have hratio : (1 + q₀) / (1 - q₀) < (1 + q) / (1 - q) := by
    rw [div_lt_div_iff₀ h0' h0]
    nlinarith
  exact Real.log_lt_log (div_pos (by linarith) h0') hratio

/-- Lower bounds on the normalised area and on the modulus ratio push the barrier
up.  This is the composition step that turns the single rational certificate into
"every non-trivial node fails". -/
theorem clusterBarrierScalar_mono {α₀ α q₀ q : ℝ}
    (hα₀ : 0 ≤ α₀) (hα : α₀ ≤ α) (hq₀ : 0 ≤ q₀) (hq : q₀ ≤ q) (hq1 : q < 1) :
    clusterBarrierScalar α₀ q₀ ≤ clusterBarrierScalar α q := by
  have hL0 : 0 ≤ Real.log ((1 + q₀) / (1 - q₀)) := log_ratio_nonneg hq₀ (by linarith)
  have hLm : Real.log ((1 + q₀) / (1 - q₀)) ≤ Real.log ((1 + q) / (1 - q)) :=
    log_ratio_mono hq₀ hq hq1
  simp only [clusterBarrierScalar]
  exact mul_le_mul hα hLm hL0 (le_trans hα₀ hα)

/-- **Every non-trivial node fails.**  Any component whose normalised area is at
least `9801/20000` and whose modulus ratio is at least `9801/10000` has barrier
strictly above the certificate threshold `2`. -/
theorem clusterBarrier_gt_two_of_lower_bounds {α q : ℝ}
    (hα : (9801 : ℝ) / 20000 ≤ α) (hq : (9801 : ℝ) / 10000 ≤ q) (hq1 : q < 1) :
    2 < clusterBarrierScalar α q := by
  have hbase : clusterBarrierScalar (9801 / 20000) (9801 / 10000)
      ≤ clusterBarrierScalar α q :=
    clusterBarrierScalar_mono (by norm_num) hα (by norm_num) hq hq1
  have hmargin := rational_cluster_margin
  simp only [clusterBarrierScalar] at hbase
  simp only [clusterBarrierScalar]
  linarith

/-! ## B.3 The `x * artanh x` weight -/

/-- `x ↦ x * artanh x`, written in cleared logarithmic form.  This is the
degree-free lower bound `𝓑(C_t,t) ≥ x_t artanh x_t` produced by the exact petal
area and Jensen; the integral input itself is not formalised here. -/
def artanhWeight (x : ℝ) : ℝ := x / 2 * Real.log ((1 + x) / (1 - x))

/-- `artanhWeight` really is `x * artanh x`. -/
theorem artanhWeight_eq_mul_artanh {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    artanhWeight x = x * Real.artanh x := by
  simp only [artanhWeight]
  rw [Real.artanh_eq_half_log hx]
  ring

/-- `x ↦ x * artanh x` is strictly increasing on `[0,1)`.  This is the step that
carries `x_t ≥ r²` up to the barrier bound. -/
theorem artanhWeight_strictMonoOn : StrictMonoOn artanhWeight (Set.Ico (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hy1 : y < 1 := hy.2
  have hL : Real.log ((1 + x) / (1 - x)) < Real.log ((1 + y) / (1 - y)) :=
    log_ratio_strictMono hx0 hxy hy1
  have hLx : 0 ≤ Real.log ((1 + x) / (1 - x)) := log_ratio_nonneg hx0 hx.2
  simp only [artanhWeight]
  exact mul_lt_mul'' (by linarith) hL (by linarith) hLx

/-- `r = 99/100` gives `x₀ = r² = 9801/10000`. -/
theorem r_sq_value : ((99 : ℝ) / 100) ^ 2 = 9801 / 10000 := by norm_num

/-- The threshold is crossed at `r = 99/100`: `r² artanh (r²) > 2`, so the
connected-cluster Bergman certificate fails at every regular level of
`z^n − r^n`, in every degree. -/
theorem artanhWeight_r_sq_gt_two : (2 : ℝ) < artanhWeight (9801 / 10000) := by
  have hval : artanhWeight (9801 / 10000)
      = 9801 / 20000 * Real.log ((1 + 9801 / 10000) / (1 - 9801 / 10000)) := by
    simp only [artanhWeight]
    ring
  rw [hval]
  linarith [rational_cluster_margin]

end

end ErdosProblems.Erdos1041.MechanismSeparationScalarKernel
