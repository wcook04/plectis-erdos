import ErdosProblems.Erdos1041.PaperAnalyticTargets

/-!
# Erdős 1041: the scale-free low-critical corollaries

This file discharges, in full, the proofs the paper gives for

* `res:scaled-low-critical` (short paper, `paper/1041/erdos-1041-lemniscate-newton-flow.tex`
  line 191), both of its clauses;
* `res:low-critical-scale-free` (long paper, `paper/reasoning-parts/erdos1041/core.tex`
  line 242);
* `res:scaled-low-critical-path` (long paper, `core.tex` line 706),

from the theorem they cite, `res:low-critical-thirteen-twentyfifths`.  That
theorem is already recorded verbatim, and unproved, as the proposition
`ErdosProblems.Erdos1041.PaperAnalyticTargets.LowCriticalThirteenTwentyFifths`.
It is the single named hypothesis of the two main theorems below.  The paper
records that its own proof rests on the Riemann mapping theorem, the Bergman
kernel, the argument principle, the coarea formula and Pólya's area
inequality, none of which is in Mathlib v4.29.1; so the corollaries are proved
here modulo that one external input and nothing else.

Everything the corollaries add to it is proved outright:

* `rescale p σ` transcribes the paper's `g(z) = s^{-n} f(sz)` as a polynomial,
  and `rescale_monic`, `rescale_natDegree`, `rescale_squarefree`,
  `rescale_criticalMinimum` prove that it is monic of the same degree,
  squarefree, and has least critical-value modulus exactly `μ / s^n`;
* `connectedBelow_scale` transports an actual rectifiable connector through
  `z ↦ σ z`, scaling the containment level by `‖σ^n‖` and the extended
  variation by `‖σ‖` (no replacement of length by endpoint distance);
* `rpow_scale_step` is the paper's numerical step `(25/13)^{1/n} ≤ 5/4` for
  `n ≥ 3`, from `25/13 ≤ (5/4)^3`;
* the degree-two branch of both corollaries, and the degree-two branch of the
  parent theorem itself, are unconditional: for `f = (X - a)(X - b)` the
  diameter through the critical point `(a+b)/2` has exact extended variation
  `2‖(a-b)/2‖ = 2 μ^{1/2}` and exact modulus `(1 - u²)μ ≤ μ` along it.

Curve helpers are copied rather than imported: `PaperMetricScaling` has no
`.olean` in this checkout.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Set PaperCurve PaperAnalyticTargets
open scoped NNReal ENNReal

/-! ## 1. Transport of an actual rectifiable connector under `z ↦ σ z` -/

theorem scale_lipschitz (σ : ℂ) : LipschitzWith ‖σ‖₊ (fun z : ℂ => σ * z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have he : σ * z - σ * w = σ * (z - w) := by ring
  simp only [dist_eq_norm, he, norm_mul, coe_nnnorm]
  exact le_rfl

theorem scaled_variation_le (γ : ℝ → ℂ) (s : Set ℝ) (σ : ℂ) :
    eVariationOn (fun t => σ * γ t) s ≤ (‖σ‖₊ : ℝ≥0∞) * eVariationOn γ s := by
  have hl := (scale_lipschitz σ).lipschitzOnWith (s := (univ : Set ℂ))
  have hm : MapsTo γ s univ := fun _ _ => mem_univ _
  simpa only [Function.comp_def] using hl.comp_eVariationOn_le hm

/-- The paper's rescaling step at the level of curves: both the containment
level and the extended variation are transported, with their exact factors. -/
theorem connectedBelow_scale {f g : ℂ → ℂ} {R L : ℝ} {a b σ d : ℂ}
    (hσ : σ ≠ 0) (hd : d ≠ 0)
    (hid : ∀ z : ℂ, f (σ * z) = d * g z)
    (H : ConnectedBelow g R L a b) :
    ConnectedBelow f (‖d‖ * R) (‖σ‖ * L) (σ * a) (σ * b) := by
  obtain ⟨γ, hcont, h0, h2, hlevel, hrect, hlen⟩ := H
  have hcpos : (0 : ℝ≥0∞) < (‖σ‖₊ : ℝ≥0∞) := by
    exact_mod_cast (show (0 : ℝ) < ‖σ‖ from norm_pos_iff.mpr hσ)
  have hcfin : (‖σ‖₊ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hlen' : eVariationOn (fun t => σ * γ t) (Icc (0 : ℝ) 2) <
      ENNReal.ofReal (‖σ‖ * L) := by
    calc
      eVariationOn (fun t => σ * γ t) (Icc (0 : ℝ) 2)
          ≤ (‖σ‖₊ : ℝ≥0∞) * eVariationOn γ (Icc (0 : ℝ) 2) :=
        scaled_variation_le γ _ σ
      _ < (‖σ‖₊ : ℝ≥0∞) * ENNReal.ofReal L :=
        ENNReal.mul_lt_mul_right (ne_of_gt hcpos) hcfin hlen
      _ = ENNReal.ofReal (‖σ‖ * L) := by
        rw [ENNReal.ofReal_mul (norm_nonneg σ)]
        rw [show ENNReal.ofReal ‖σ‖ = (‖σ‖₊ : ℝ≥0∞) by simp [enorm_eq_nnnorm]]
  refine ⟨fun t => σ * γ t, ?_, ?_, ?_, ?_, ?_, hlen'⟩
  · exact continuousOn_const.mul hcont
  · simp [h0]
  · simp [h2]
  · intro t ht
    rw [hid, norm_mul]
    exact mul_lt_mul_of_pos_left (hlevel t ht) (norm_pos_iff.mpr hd)
  · change eVariationOn (fun t => σ * γ t) (Icc (0 : ℝ) 2) ≠ ⊤
    exact ne_of_lt (lt_of_lt_of_le hlen' le_top)

theorem connectedBelow_mono_length {f : ℂ → ℂ} {R L L' : ℝ} {a b : ℂ}
    (h : L ≤ L') (H : ConnectedBelow f R L a b) : ConnectedBelow f R L' a b := by
  obtain ⟨γ, hc, h0, h2, hlev, hrect, hlen⟩ := H
  exact ⟨γ, hc, h0, h2, hlev, hrect, lt_of_lt_of_le hlen (ENNReal.ofReal_le_ofReal h)⟩

theorem hasDistinctConnection_mono_length {p : ℂ[X]} {R L L' : ℝ}
    (h : L ≤ L') (H : HasDistinctConnection p R L) : HasDistinctConnection p R L' := by
  obtain ⟨a, b, hab, ha, hb, hconn⟩ := H
  exact ⟨a, b, hab, ha, hb, connectedBelow_mono_length h hconn⟩

/-! ## 2. The least critical-value modulus of a squarefree polynomial -/

theorem criticalMinimum_nonneg {p : ℂ[X]} {μ : ℝ} (h : CriticalMinimum p μ) : 0 ≤ μ := by
  obtain ⟨c, -, hc⟩ := h.1
  rw [hc]
  exact norm_nonneg _

/-- Squarefreeness gives `μ > 0`: a root at which the derivative also vanishes
would produce a square factor. -/
theorem criticalMinimum_pos {p : ℂ[X]} {μ : ℝ}
    (hsq : Squarefree p) (h : CriticalMinimum p μ) : 0 < μ := by
  rcases lt_or_eq_of_le (criticalMinimum_nonneg h) with h' | h'
  · exact h'
  · exfalso
    obtain ⟨c, hc, hval⟩ := h.1
    have hz : ‖p.eval c‖ = 0 := by rw [← hval, ← h']
    have hroot : p.eval c = 0 := by simpa using hz
    obtain ⟨q, hq⟩ : (X - C c) ∣ p := dvd_iff_isRoot.mpr hroot
    have hderiv : p.derivative = q + (X - C c) * q.derivative := by
      rw [hq, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
        one_mul]
    have hcc := hc
    rw [hderiv] at hcc
    have hq0 : q.eval c = 0 := by simpa using hcc
    obtain ⟨r, hr⟩ : (X - C c) ∣ q := dvd_iff_isRoot.mpr hq0
    have hdvd : (X - C c) * (X - C c) ∣ p := ⟨r, by rw [hq, hr]; ring⟩
    obtain ⟨u, -, huc⟩ := Polynomial.isUnit_iff.mp (hsq _ hdvd)
    have hnd := congrArg Polynomial.natDegree huc
    simp at hnd

/-! ## 3. The paper's rescaling `g(z) = s^{-n} f(sz)` -/

/-- `rescale p σ` is the paper's `s^{-n} f(sz)`, as an actual polynomial. -/
def rescale (p : ℂ[X]) (σ : ℂ) : ℂ[X] :=
  C (σ ^ p.natDegree)⁻¹ * p.comp (C σ * X)

theorem rescale_eval (p : ℂ[X]) (σ z : ℂ) :
    (rescale p σ).eval z = (σ ^ p.natDegree)⁻¹ * p.eval (σ * z) := by
  unfold rescale
  simp only [eval_mul, eval_C, eval_comp, eval_X]

theorem rescale_derivative (p : ℂ[X]) (σ : ℂ) :
    (rescale p σ).derivative
      = C (σ ^ p.natDegree)⁻¹ * (C σ * p.derivative.comp (C σ * X)) := by
  unfold rescale
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_comp,
    derivative_C_mul_X]

theorem rescale_derivative_eval (p : ℂ[X]) (σ z : ℂ) :
    (rescale p σ).derivative.eval z
      = (σ ^ p.natDegree)⁻¹ * (σ * p.derivative.eval (σ * z)) := by
  rw [rescale_derivative]
  simp only [eval_mul, eval_C, eval_comp, eval_X]

theorem rescale_natDegree {p : ℂ[X]} {σ : ℂ} (hσ : σ ≠ 0) :
    (rescale p σ).natDegree = p.natDegree := by
  have hu : (σ ^ p.natDegree)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hσ)
  have hlin : (C σ * X : ℂ[X]).natDegree = 1 := by
    rw [natDegree_C_mul hσ, natDegree_X]
  rw [rescale, natDegree_C_mul hu, natDegree_comp, hlin, mul_one]

theorem rescale_monic {p : ℂ[X]} {σ : ℂ} (hp : p.Monic) (hσ : σ ≠ 0) :
    (rescale p σ).Monic := by
  have hlinL : (C σ * X : ℂ[X]).leadingCoeff = σ := by
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one]
  have hlin : (C σ * X : ℂ[X]).natDegree ≠ 0 := by
    rw [natDegree_C_mul hσ, natDegree_X]
    exact one_ne_zero
  unfold Polynomial.Monic
  rw [rescale, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp hlin, hlinL,
    hp.leadingCoeff, one_mul]
  exact inv_mul_cancel₀ (pow_ne_zero _ hσ)

theorem comp_scale_comp_inv {σ : ℂ} (hσ : σ ≠ 0) (q : ℂ[X]) :
    (q.comp (C σ * X)).comp (C σ⁻¹ * X) = q := by
  rw [comp_assoc]
  have hXX : (C σ * X : ℂ[X]).comp (C σ⁻¹ * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hσ, C_1,
      one_mul]
  rw [hXX, comp_X]

theorem squarefree_comp_scale {p : ℂ[X]} {σ : ℂ} (hσ : σ ≠ 0) (hp : Squarefree p) :
    Squarefree (p.comp (C σ * X)) := by
  intro x hx
  obtain ⟨c, hc⟩ := hx
  have hdvd : (x.comp (C σ⁻¹ * X)) * (x.comp (C σ⁻¹ * X)) ∣ p := by
    refine ⟨c.comp (C σ⁻¹ * X), ?_⟩
    have h1 : (p.comp (C σ * X)).comp (C σ⁻¹ * X)
        = (x * x * c).comp (C σ⁻¹ * X) := by rw [hc]
    rw [comp_scale_comp_inv hσ, mul_comp, mul_comp] at h1
    exact h1
  obtain ⟨u, hu, huc⟩ := Polynomial.isUnit_iff.mp (hp _ hdvd)
  have hx' : x = C u := by
    have h1 : (C u).comp (C σ * X) = (x.comp (C σ⁻¹ * X)).comp (C σ * X) := by
      rw [huc]
    rw [C_comp] at h1
    have h2 := comp_scale_comp_inv (σ := σ⁻¹) (inv_ne_zero hσ) x
    rw [inv_inv] at h2
    rw [h2] at h1
    exact h1.symm
  rw [hx']
  exact hu.map C

theorem squarefree_C_mul {u : ℂ} (hu : u ≠ 0) {q : ℂ[X]} (hq : Squarefree q) :
    Squarefree (C u * q) := by
  intro x hx
  have h : C u * q * C u⁻¹ = q := by
    rw [mul_comm (C u) q, mul_assoc, ← C_mul, mul_inv_cancel₀ hu, C_1, mul_one]
  exact hq x (hx.trans ⟨C u⁻¹, h.symm⟩)

theorem rescale_squarefree {p : ℂ[X]} {σ : ℂ} (hσ : σ ≠ 0) (hp : Squarefree p) :
    Squarefree (rescale p σ) :=
  squarefree_C_mul (inv_ne_zero (pow_ne_zero _ hσ)) (squarefree_comp_scale hσ hp)

/-- The least critical-value modulus of `s^{-n} f(sz)` is exactly `μ / s^n`. -/
theorem rescale_criticalMinimum {p : ℂ[X]} {μ s : ℝ} (hs : 0 < s)
    (hμ : CriticalMinimum p μ) :
    CriticalMinimum (rescale p (s : ℂ)) (μ / s ^ p.natDegree) := by
  have hσ : ((s : ℂ)) ≠ 0 := by simpa using hs.ne'
  have hpow : ((s : ℂ) ^ p.natDegree) ≠ 0 := pow_ne_zero _ hσ
  have hnorm : ‖((s : ℂ) ^ p.natDegree)⁻¹‖ = (s ^ p.natDegree)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  constructor
  · obtain ⟨c, hc, hval⟩ := hμ.1
    have hback : (s : ℂ) * (c / (s : ℂ)) = c := by field_simp
    refine ⟨c / (s : ℂ), ?_, ?_⟩
    · rw [rescale_derivative_eval, hback, hc, mul_zero, mul_zero]
    · rw [rescale_eval, hback, norm_mul, hnorm, ← hval, div_eq_inv_mul]
  · rintro x ⟨c, hc, rfl⟩
    rw [rescale_derivative_eval] at hc
    have hc' : p.derivative.eval ((s : ℂ) * c) = 0 := by
      rcases mul_eq_zero.mp hc with h | h
      · exact absurd h (inv_ne_zero hpow)
      · rcases mul_eq_zero.mp h with h2 | h2
        · exact absurd h2 hσ
        · exact h2
    have hge : μ ≤ ‖p.eval ((s : ℂ) * c)‖ := hμ.2 ⟨(s : ℂ) * c, hc', rfl⟩
    rw [rescale_eval, norm_mul, hnorm, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hge (le_of_lt (inv_pos.mpr (pow_pos hs _)))

/-- The whole rescaling step of the corollaries' proofs, in one statement. -/
theorem hasDistinctConnection_of_rescale {p : ℂ[X]} {s L : ℝ} (hs : 0 < s)
    (H : HasDistinctConnection (rescale p (s : ℂ)) 1 L) :
    HasDistinctConnection p (s ^ p.natDegree) (s * L) := by
  obtain ⟨A, B, hAB, hA, hB, hconn⟩ := H
  have hσ : ((s : ℂ)) ≠ 0 := by simpa using hs.ne'
  have hpow : ((s : ℂ) ^ p.natDegree) ≠ 0 := pow_ne_zero _ hσ
  have hid : ∀ z : ℂ,
      p.eval ((s : ℂ) * z) = ((s : ℂ) ^ p.natDegree) * (rescale p (s : ℂ)).eval z := by
    intro z
    rw [rescale_eval, ← mul_assoc, mul_inv_cancel₀ hpow, one_mul]
  have hnσ : ‖((s : ℂ))‖ = s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hnd : ‖((s : ℂ) ^ p.natDegree)‖ = s ^ p.natDegree := by rw [norm_pow, hnσ]
  have hT := connectedBelow_scale (f := p.eval) (g := (rescale p (s : ℂ)).eval)
    hσ hpow hid hconn
  rw [hnσ, hnd, mul_one] at hT
  refine ⟨(s : ℂ) * A, (s : ℂ) * B, ?_, ?_, ?_, hT⟩
  · exact fun he => hAB (mul_left_cancel₀ hσ he)
  · rw [hid, hA, mul_zero]
  · rw [hid, hB, mul_zero]

/-! ## 4. The numerical step `(25/13)^{1/n} ≤ 5/4` for `n ≥ 3` -/

theorem rpow_scale_step {n : ℕ} (hn : 3 ≤ n) :
    ((25 / 13 : ℝ)) ^ (1 / (n : ℝ)) ≤ 5 / 4 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have hn0 : (0 : ℕ) < n := by omega
    exact_mod_cast hn0
  have hb : (25 / 13 : ℝ) ≤ ((5 / 4 : ℝ)) ^ (3 : ℕ) := by norm_num
  have h3 := Real.rpow_le_rpow (show (0 : ℝ) ≤ 25 / 13 by norm_num) hb
    (show (0 : ℝ) ≤ 1 / (n : ℝ) by positivity)
  have h4 : (((5 / 4 : ℝ)) ^ (3 : ℕ)) ^ (1 / (n : ℝ))
      = (5 / 4 : ℝ) ^ ((3 : ℝ) * (1 / (n : ℝ))) := by
    rw [← Real.rpow_natCast (5 / 4 : ℝ) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5 / 4)]
    norm_num
  have h5 : (3 : ℝ) * (1 / (n : ℝ)) ≤ 1 := by
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [mul_one_div, div_le_one hnpos]
    exact hn3
  have h6 : (5 / 4 : ℝ) ^ ((3 : ℝ) * (1 / (n : ℝ))) ≤ (5 / 4 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
  rw [Real.rpow_one] at h6
  rw [h4] at h3
  linarith

theorem two_scale_le_five_halves {μ : ℝ} (hμ : 0 < μ) {n : ℕ} (hn : 3 ≤ n) :
    2 * (((25 / 13 : ℝ) * μ) ^ (1 / (n : ℝ))) ≤ (5 / 2 : ℝ) * (μ ^ (1 / (n : ℝ))) := by
  have hpos : (0 : ℝ) ≤ μ ^ (1 / (n : ℝ)) := Real.rpow_nonneg hμ.le _
  rw [Real.mul_rpow (by norm_num) hμ.le, ← mul_assoc]
  nlinarith [mul_le_mul_of_nonneg_right (rpow_scale_step hn) hpos]

/-! ## 5. Degree two, unconditionally -/

theorem monic_degree_two_factor {p : ℂ[X]} (hmonic : p.Monic) (hdeg : p.natDegree = 2) :
    ∃ a b : ℂ, p = (X - C a) * (X - C b) := by
  have hdegp : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (by omega)
  obtain ⟨a, ha⟩ := Complex.exists_root hdegp
  obtain ⟨q, hq⟩ : (X - C a) ∣ p := dvd_iff_isRoot.mpr ha
  have hmq : q.Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [← hq]; exact hmonic)
  have hqdeg : q.natDegree = 1 := by
    have hsum : ((X - C a) * q).natDegree = 2 := by rw [← hq]; exact hdeg
    rw [natDegree_mul (X_sub_C_ne_zero a) hmq.ne_zero, natDegree_X_sub_C] at hsum
    omega
  obtain ⟨b, hb⟩ : ∃ b : ℂ, q = X - C b :=
    ⟨-(q.coeff 0), by rw [map_neg, sub_neg_eq_add]; exact hmq.eq_X_add_C hqdeg⟩
  exact ⟨a, b, by rw [hq, hb]⟩

theorem quad_eval (a b z : ℂ) :
    (((X - C a) * (X - C b) : ℂ[X])).eval z = (z - a) * (z - b) := by
  simp

theorem quad_derivative_eval (a b z : ℂ) :
    (((X - C a) * (X - C b) : ℂ[X])).derivative.eval z = 2 * z - a - b := by
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
    one_mul, mul_one, eval_add, eval_sub, eval_X, eval_C]
  ring

theorem quad_criticalMinimum (a b : ℂ) :
    CriticalMinimum ((X - C a) * (X - C b)) (‖(a - b) / 2‖ ^ 2) := by
  have hval : (((X - C a) * (X - C b) : ℂ[X])).eval ((a + b) / 2)
      = -(((a - b) / 2) ^ 2) := by
    rw [quad_eval]; ring
  have hnorm : ‖(((X - C a) * (X - C b) : ℂ[X])).eval ((a + b) / 2)‖
      = ‖(a - b) / 2‖ ^ 2 := by
    rw [hval, norm_neg, norm_pow]
  constructor
  · exact ⟨(a + b) / 2, by rw [quad_derivative_eval]; ring, hnorm.symm⟩
  · rintro x ⟨c, hc, rfl⟩
    rw [quad_derivative_eval] at hc
    have hceq : c = (a + b) / 2 := by linear_combination hc / 2
    exact le_of_eq (by rw [hceq]; exact hnorm.symm)

/-- The exact diameter of the degree-two lemniscate through its critical
point: modulus `(1 - u²)‖(a-b)/2‖²` along it, total variation `2‖(a-b)/2‖`. -/
theorem quad_connectedBelow (a b : ℂ) {R L : ℝ}
    (hR : ‖(a - b) / 2‖ ^ 2 < R) (hL : 2 * ‖(a - b) / 2‖ < L) :
    ConnectedBelow (((X - C a) * (X - C b) : ℂ[X])).eval R L a b := by
  have key : ∀ v : ℂ, ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (v = a - (a + b) / 2 ∨ v = b - (a + b) / 2) →
      ‖(((X - C a) * (X - C b) : ℂ[X])).eval ((a + b) / 2 + (u : ℂ) * v)‖ < R := by
    intro v u hu0 hu1 hv
    have he : (((X - C a) * (X - C b) : ℂ[X])).eval ((a + b) / 2 + (u : ℂ) * v)
        = ((u : ℂ) ^ 2 - 1) * ((a - b) / 2) ^ 2 := by
      rcases hv with hv | hv <;> rw [quad_eval, hv] <;> ring
    have hcast : ((u : ℂ) ^ 2 - 1) = (((u ^ 2 - 1 : ℝ)) : ℂ) := by push_cast; ring
    have hu2 : ‖((u : ℂ) ^ 2 - 1)‖ ≤ 1 := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by nlinarith : u ^ 2 - 1 ≤ 0)]
      nlinarith [sq_nonneg u]
    rw [he, norm_mul, norm_pow]
    calc ‖((u : ℂ) ^ 2 - 1)‖ * ‖(a - b) / 2‖ ^ 2
        ≤ 1 * ‖(a - b) / 2‖ ^ 2 := mul_le_mul_of_nonneg_right hu2 (by positivity)
      _ = ‖(a - b) / 2‖ ^ 2 := one_mul _
      _ < R := hR
  apply connectedBelow_of_spokes (h := (a + b) / 2)
  · intro u hu0 hu1
    exact key _ u hu0 hu1 (Or.inl rfl)
  · intro u hu0 hu1
    exact key _ u hu0 hu1 (Or.inr rfl)
  · have h1 : (a + b) / 2 - a = -((a - b) / 2) := by ring
    have h2 : b - (a + b) / 2 = -((a - b) / 2) := by ring
    rw [h1, h2, norm_neg]
    linarith

/-- Degree-two packaging: the two roots, their distinctness, and the exact
identity `μ = ‖(a-b)/2‖²`. -/
theorem degree_two_data {p : ℂ[X]} {μ : ℝ}
    (hmonic : p.Monic) (hsq : Squarefree p) (hdeg : p.natDegree = 2)
    (hμ : CriticalMinimum p μ) :
    ∃ a b : ℂ, p = (X - C a) * (X - C b) ∧ a ≠ b ∧ μ = ‖(a - b) / 2‖ ^ 2 ∧ 0 < μ := by
  obtain ⟨a, b, hab⟩ := monic_degree_two_factor hmonic hdeg
  have hpos : 0 < μ := criticalMinimum_pos hsq hμ
  have hμ' : CriticalMinimum ((X - C a) * (X - C b)) μ := by rw [← hab]; exact hμ
  have heq : μ = ‖(a - b) / 2‖ ^ 2 :=
    le_antisymm (hμ'.2 (quad_criticalMinimum a b).1) ((quad_criticalMinimum a b).2 hμ'.1)
  refine ⟨a, b, hab, ?_, heq, hpos⟩
  intro hne
  rw [hne] at heq
  simp at heq
  exact absurd heq.symm hpos.ne

theorem norm_half_pos {a b : ℂ} {μ : ℝ} (hpos : 0 < μ) (heq : μ = ‖(a - b) / 2‖ ^ 2) :
    0 < ‖(a - b) / 2‖ := by
  rw [heq] at hpos
  nlinarith [norm_nonneg ((a - b) / 2)]

/-- Degree two is unconditional even for the parent theorem: the diameter
through the critical point is the connector. -/
theorem lowCritical_degree_two {p : ℂ[X]} {μ : ℝ}
    (hmonic : p.Monic) (hsq : Squarefree p) (hdeg : p.natDegree = 2)
    (hμ : CriticalMinimum p μ) (hsmall : μ ≤ 13 / 25) :
    HasDistinctConnection p 1 2 := by
  obtain ⟨a, b, hab, hne, heq, hpos⟩ := degree_two_data hmonic hsq hdeg hμ
  have hr : 0 < ‖(a - b) / 2‖ := norm_half_pos hpos heq
  have hsq1 : ‖(a - b) / 2‖ ^ 2 < 1 := by rw [← heq]; linarith
  have hlt : ‖(a - b) / 2‖ < 1 := by
    nlinarith [hsq1, hr, sq_nonneg (‖(a - b) / 2‖ - 1)]
  refine ⟨a, b, hne, ?_, ?_, ?_⟩
  · rw [hab, quad_eval]; ring
  · rw [hab, quad_eval]; ring
  · rw [hab]
    exact quad_connectedBelow a b hsq1 (by linarith)

/-- Degree two needs no hypothesis at all: BOTH scale-free corollaries hold
outright at `n = 2`, by the paper's own degree-two argument (the diameter
through the critical point has total length `2 μ^{1/2}` and lies in the closed
level `μ`, inside the stated open level `(25/13)μ`).  The second conjunct is
not a consequence of the first, since `2(25/13)^{1/2} > 5/2`. -/
theorem scaled_degree_two {p : ℂ[X]} {μ : ℝ}
    (hmonic : p.Monic) (hsq : Squarefree p) (hdeg : p.natDegree = 2)
    (hμ : CriticalMinimum p μ) :
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
        (2 * (((25 / 13 : ℝ) * μ) ^ (1 / (p.natDegree : ℝ)))) ∧
      HasDistinctConnection p ((25 / 13 : ℝ) * μ)
        ((5 / 2 : ℝ) * (μ ^ (1 / (p.natDegree : ℝ)))) := by
  have hpos : 0 < μ := criticalMinimum_pos hsq hμ
  obtain ⟨a, b, hab, hne, heq, -⟩ := degree_two_data hmonic hsq hdeg hμ
  have hr : 0 < ‖(a - b) / 2‖ := norm_half_pos hpos heq
  have hexp : (1 : ℝ) / (p.natDegree : ℝ) = 1 / 2 := by rw [hdeg]; norm_num
  have hsqrt : μ ^ ((1 : ℝ) / (p.natDegree : ℝ)) = ‖(a - b) / 2‖ := by
    rw [hexp, ← Real.sqrt_eq_rpow, heq]
    exact Real.sqrt_sq (norm_nonneg _)
  have hsqrt2 : ((25 / 13 : ℝ) * μ) ^ ((1 : ℝ) / (p.natDegree : ℝ))
      = Real.sqrt ((25 / 13 : ℝ) * μ) := by
    rw [hexp, ← Real.sqrt_eq_rpow]
  have hroot : ‖(a - b) / 2‖ < Real.sqrt ((25 / 13 : ℝ) * μ) := by
    rw [← hsqrt, hexp, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_lt_sqrt hpos.le (by linarith)
  constructor
  · refine ⟨a, b, hne, ?_, ?_, ?_⟩
    · rw [hab, quad_eval]; ring
    · rw [hab, quad_eval]; ring
    · rw [hsqrt2, hab]
      refine quad_connectedBelow a b ?_ ?_
      · rw [← heq]; linarith
      · linarith
  · refine ⟨a, b, hne, ?_, ?_, ?_⟩
    · rw [hab, quad_eval]; ring
    · rw [hab, quad_eval]; ring
    · rw [hsqrt, hab]
      refine quad_connectedBelow a b ?_ ?_
      · rw [← heq]; linarith
      · linarith

/-! ## 6. The corollaries -/

/-- Short paper Corollary `res:scaled-low-critical`, first clause; long paper
Corollary `res:low-critical-scale-free`.  One named hypothesis: the paper's own
Theorem `res:low-critical-thirteen-twentyfifths`. -/
theorem scaledLowCritical_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCritical := by
  intro p μ hmonic hsq hdeg hμ
  have hpos : 0 < μ := criticalMinimum_pos hsq hμ
  have hn0 : p.natDegree ≠ 0 := by omega
  have hlev : (0 : ℝ) < 25 / 13 * μ := by linarith
  set s : ℝ := ((25 / 13 : ℝ) * μ) ^ (1 / (p.natDegree : ℝ)) with hsdef
  have hs : 0 < s := Real.rpow_pos_of_pos hlev _
  have hsn : s ^ p.natDegree = (25 / 13 : ℝ) * μ := by
    rw [hsdef, one_div]
    exact Real.rpow_inv_natCast_pow hlev.le hn0
  have hσ : ((s : ℂ)) ≠ 0 := by simpa using hs.ne'
  have hcm : CriticalMinimum (rescale p (s : ℂ)) (13 / 25) := by
    have h := rescale_criticalMinimum (p := p) hs hμ
    have hval : μ / s ^ p.natDegree = 13 / 25 := by
      rw [hsn, div_eq_iff hlev.ne']
      ring
    rwa [hval] at h
  have hparent : HasDistinctConnection (rescale p (s : ℂ)) 1 2 :=
    H (rescale p (s : ℂ)) (13 / 25) (rescale_monic hmonic hσ)
      (rescale_squarefree hσ hsq)
      (by rw [rescale_natDegree hσ]; exact hdeg) hcm le_rfl
  have hT := hasDistinctConnection_of_rescale (p := p) hs hparent
  rw [hsn] at hT
  have hmul : s * 2 = 2 * s := by ring
  rw [hmul] at hT
  exact hT

/-- Short paper Corollary `res:scaled-low-critical`, second clause; long paper
Corollary `res:scaled-low-critical-path`.  Degree two is unconditional; only
`n ≥ 3` consumes the named hypothesis. -/
theorem scaledLowCriticalFiveHalves_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCriticalFiveHalves := by
  intro p μ hmonic hsq hdeg hμ
  have hpos : 0 < μ := criticalMinimum_pos hsq hμ
  rcases eq_or_lt_of_le hdeg with hd2 | hd3
  · exact (scaled_degree_two hmonic hsq hd2.symm hμ).2
  · have hn3 : 3 ≤ p.natDegree := hd3
    have hbase := scaledLowCritical_of_lowCritical H p μ hmonic hsq hdeg hμ
    exact hasDistinctConnection_mono_length (two_scale_le_five_halves hpos hn3) hbase

#print axioms connectedBelow_scale
#print axioms criticalMinimum_pos
#print axioms rescale_monic
#print axioms rescale_squarefree
#print axioms rescale_natDegree
#print axioms rescale_criticalMinimum
#print axioms hasDistinctConnection_of_rescale
#print axioms rpow_scale_step
#print axioms two_scale_le_five_halves
#print axioms monic_degree_two_factor
#print axioms quad_criticalMinimum
#print axioms quad_connectedBelow
#print axioms degree_two_data
#print axioms lowCritical_degree_two
#print axioms scaled_degree_two
#print axioms scaledLowCritical_of_lowCritical
#print axioms scaledLowCriticalFiveHalves_of_lowCritical

end ErdosProblems.Erdos1041.PaperCompleteR21
