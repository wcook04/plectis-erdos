import Mathlib

/-!
# Erdős #1041: the hyperbolic law of cosines, and the two packing environments unconditionally

Second-pass file for the two environments of `paper/reasoning-parts/erdos1041/core.tex`
labelled `res:circle-slice-packing` (line 378) and `res:dual-arity-floor` (line 401).

The first pass (`HyperbolicCirclePacking.lean`, same directory) proved both statements
over an abstract pseudometric space `P` equipped with a map `pt : ℝ → ℝ → P` and **one**
named hypothesis, the hyperbolic law of cosines in geodesic polar coordinates,

  `hlaw : ∀ d₁ θ₁ d₂ θ₂, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
            = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂)`.

This file **discharges that hypothesis**, so both environments become unconditional in the
hyperbolic plane.

## What is new here

Mathlib (v4.29.1) has the upper half-plane `ℍ` with the Poincaré metric
(`UpperHalfPlane.dist_eq`, `UpperHalfPlane.cosh_dist`) but no disc model, no geodesic
polar coordinates and no law of cosines.  We supply the coordinates and the law:

* `polar d θ : ℍ` — the point of the hyperbolic plane at distance `|d|` from the centre
  `i` with argument `θ`.  It is the image under the Cayley transform
  `w ↦ i (1 + w) / (1 - w)` of the Poincaré-disc point `tanh (d/2) · e^{iθ}` used by the
  paper, simplified to the closed form
  `polar d θ = (-(sinh d · sin θ) + i) / (cosh d - sinh d · cos θ)`.
* `cosh_dist_polar` — **the hyperbolic law of cosines**, proved outright.
* `polar_zero_zero`, `dist_polar_I` — `polar 0 0 = i` and `dist (polar d θ) i = |d|`, so
  `d` really is the hyperbolic radius.
* `exists_polar` — every point of `ℍ` is `polar d θ` for some `d ≥ 0`, so these are
  genuine geodesic polar coordinates about the centre and the configurations quantified
  over below are *all* configurations of points of the hyperbolic plane.

The proof of the law of cosines is a computation: `UpperHalfPlane.cosh_dist` turns the
left-hand side into `1 + ((x₁-x₂)² + (y₁-y₂)²)/(2 y₁ y₂)`, and with
`R_j = cosh d_j - sinh d_j cos θ_j`, `A_j = sinh d_j sin θ_j`,
`x_j = -A_j/R_j`, `y_j = 1/R_j`, the required identity is the polynomial identity
`(A₂R₁ - A₁R₂)² + (R₁ - R₂)² = 2 R₁R₂ (cosh d₁ cosh d₂ - sinh d₁ sinh d₂ cos(θ₁-θ₂) - 1)`
modulo `cosh² - sinh² = 1` and `cos² + sin² = 1` (`core_identity`).

## Credit

`sliceHalfAngle`, `circle_slice_packing_abstract`, `lam`, `delta`, `le_of_lam_le` and
`dual_arity_floor_abstract` / `dual_arity_floor_sup_abstract` below are copied verbatim
(up to the fresh namespace) from the first-pass file
`ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicCirclePacking.lean`, which has no
`.olean` and therefore cannot be imported.  The angular-measure argument inside
`circle_slice_packing_abstract` is that worker's; only the law of cosines and the
unconditional instantiations at the end of this file are new.

## Endpoints for the two rows

* `circle_slice_packing` — `res:circle-slice-packing`, no external hypothesis.
* `dual_arity_floor`, `dual_arity_floor_sup` — `res:dual-arity-floor`; the law of cosines
  is gone, and the only remaining hypotheses are the paper's own `(eq:lc-separation)` and
  the two consequences `(eq:lc-radius-and-budget)` of the standing failure hypothesis
  (whose derivation needs the Riemann mapping theorem, Blaschke products and Pólya's area
  inequality, none of which are in Mathlib).
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic

open Real Set MeasureTheory
open scoped UpperHalfPlane

/-! ## Part 1 (new): geodesic polar coordinates and the hyperbolic law of cosines -/

/-- The denominator `R = cosh d - sinh d cos θ` of the polar parametrisation is positive,
because `|sinh d| < cosh d`. -/
theorem polarDen_pos (d θ : ℝ) : 0 < cosh d - sinh d * cos θ := by
  have hsq := Real.cosh_sq_sub_sinh_sq d
  have hpos := Real.cosh_pos d
  have habs : |sinh d| < cosh d := by
    nlinarith [sq_abs (sinh d), abs_nonneg (sinh d)]
  have h2 : sinh d * cos θ ≤ |sinh d| := by
    calc sinh d * cos θ ≤ |sinh d * cos θ| := le_abs_self _
      _ = |sinh d| * |cos θ| := abs_mul _ _
      _ ≤ |sinh d| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg _)
      _ = |sinh d| := mul_one _
  linarith

/-- **Geodesic polar coordinates on the hyperbolic plane.**  `polar d θ` is the point of the
upper half-plane at hyperbolic distance `|d|` from the centre `i` with argument `θ`: the
image of the Poincaré-disc point `tanh (d/2) e^{iθ}` (the paper's coordinates) under the
Cayley transform `w ↦ i(1+w)/(1-w)`, which is
`(-(sinh d sin θ) + i)/(cosh d - sinh d cos θ)`. -/
def polar (d θ : ℝ) : ℍ :=
  ⟨⟨-(sinh d * sin θ) / (cosh d - sinh d * cos θ), 1 / (cosh d - sinh d * cos θ)⟩,
    one_div_pos.mpr (polarDen_pos d θ)⟩

theorem polar_coe_re (d θ : ℝ) :
    (polar d θ : ℂ).re = -(sinh d * sin θ) / (cosh d - sinh d * cos θ) := rfl

theorem polar_coe_im (d θ : ℝ) :
    (polar d θ : ℂ).im = 1 / (cosh d - sinh d * cos θ) := rfl

theorem polar_re (d θ : ℝ) :
    (polar d θ).re = -(sinh d * sin θ) / (cosh d - sinh d * cos θ) := rfl

theorem polar_im (d θ : ℝ) :
    (polar d θ).im = 1 / (cosh d - sinh d * cos θ) := rfl

/-- The polynomial core of the law of cosines: with `R_j = P_j - Q_j c_j` and
`A_j = Q_j s_j`, one has
`(A₂R₁ - A₁R₂)² + (R₁ - R₂)² = 2 R₁R₂ (P₁P₂ - Q₁Q₂(c₁c₂+s₁s₂) - 1)`
whenever `P_j² - Q_j² = 1` and `c_j² + s_j² = 1`. -/
private theorem core_identity (P₁ Q₁ c₁ s₁ P₂ Q₂ c₂ s₂ : ℝ)
    (h₁ : P₁ ^ 2 - Q₁ ^ 2 = 1) (h₂ : P₂ ^ 2 - Q₂ ^ 2 = 1)
    (k₁ : c₁ ^ 2 + s₁ ^ 2 = 1) (k₂ : c₂ ^ 2 + s₂ ^ 2 = 1) :
    (Q₂ * s₂ * (P₁ - Q₁ * c₁) - Q₁ * s₁ * (P₂ - Q₂ * c₂)) ^ 2
        + ((P₁ - Q₁ * c₁) - (P₂ - Q₂ * c₂)) ^ 2
      = 2 * ((P₁ - Q₁ * c₁) * (P₂ - Q₂ * c₂))
          * (P₁ * P₂ - Q₁ * Q₂ * (c₁ * c₂ + s₁ * s₂) - 1) := by
  linear_combination ((P₂ - Q₂ * c₂) ^ 2 * Q₁ ^ 2) * k₁ + ((P₁ - Q₁ * c₁) ^ 2 * Q₂ ^ 2) * k₂
    - (P₂ - Q₂ * c₂) ^ 2 * h₁ - (P₁ - Q₁ * c₁) ^ 2 * h₂

/-- Clearing the denominators of `UpperHalfPlane.cosh_dist` at two polar points. -/
private theorem frac_eval (A₁ R₁ A₂ R₂ : ℝ) (h₁ : R₁ ≠ 0) (h₂ : R₂ ≠ 0) :
    ((-A₁ / R₁ - -A₂ / R₂) ^ 2 + (1 / R₁ - 1 / R₂) ^ 2) / (2 * (1 / R₁) * (1 / R₂))
      = ((A₂ * R₁ - A₁ * R₂) ^ 2 + (R₁ - R₂) ^ 2) / (2 * (R₁ * R₂)) := by
  field_simp
  try ring

private theorem cancel_aux (b y : ℝ) (hb : b ≠ 0) : 1 + b * (y - 1) / b = y := by
  have h : b * (y - 1) / b = y - 1 := by
    rw [mul_comm, mul_div_assoc, div_self hb, mul_one]
  rw [h]; ring

/-- **The hyperbolic law of cosines.**  For the geodesic polar coordinates `polar` about the
centre of the hyperbolic plane,
`cosh d(p₁,p₂) = cosh d₁ cosh d₂ - sinh d₁ sinh d₂ cos(θ₁ - θ₂)`.
This is the classical formula the paper invokes, and it is the single hypothesis that the
first pass had to assume. -/
theorem cosh_dist_polar (d₁ θ₁ d₂ θ₂ : ℝ) :
    cosh (dist (polar d₁ θ₁) (polar d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂) := by
  have hR₁ : (0 : ℝ) < cosh d₁ - sinh d₁ * cos θ₁ := polarDen_pos d₁ θ₁
  have hR₂ : (0 : ℝ) < cosh d₂ - sinh d₂ * cos θ₂ := polarDen_pos d₂ θ₂
  have hne₁ : (cosh d₁ - sinh d₁ * cos θ₁) ≠ 0 := ne_of_gt hR₁
  have hne₂ : (cosh d₂ - sinh d₂ * cos θ₂) ≠ 0 := ne_of_gt hR₂
  have hden : (2 : ℝ) * ((cosh d₁ - sinh d₁ * cos θ₁) * (cosh d₂ - sinh d₂ * cos θ₂)) ≠ 0 :=
    ne_of_gt (by nlinarith [mul_pos hR₁ hR₂])
  have key := core_identity (cosh d₁) (sinh d₁) (cos θ₁) (sin θ₁)
      (cosh d₂) (sinh d₂) (cos θ₂) (sin θ₂)
      (Real.cosh_sq_sub_sinh_sq d₁) (Real.cosh_sq_sub_sinh_sq d₂)
      (Real.cos_sq_add_sin_sq θ₁) (Real.cos_sq_add_sin_sq θ₂)
  rw [UpperHalfPlane.cosh_dist, Complex.dist_eq_re_im, Real.sq_sqrt (by positivity),
    Real.cos_sub]
  simp only [polar_coe_re, polar_coe_im, polar_im]
  rw [frac_eval (sinh d₁ * sin θ₁) (cosh d₁ - sinh d₁ * cos θ₁)
      (sinh d₂ * sin θ₂) (cosh d₂ - sinh d₂ * cos θ₂) hne₁ hne₂, key]
  exact cancel_aux _ _ hden

/-- The centre of the polar coordinates is `i`. -/
theorem polar_zero_zero : polar 0 0 = UpperHalfPlane.I :=
  UpperHalfPlane.ext_re_im (by rw [polar_re]; simp) (by rw [polar_im]; simp)

/-- `d` is the hyperbolic radius: `polar d θ` is at distance `|d|` from the centre. -/
theorem dist_polar_I (d θ : ℝ) : dist (polar d θ) UpperHalfPlane.I = |d| := by
  have h := cosh_dist_polar d θ 0 0
  rw [polar_zero_zero] at h
  simp only [Real.cosh_zero, Real.sinh_zero, mul_one, mul_zero, zero_mul, sub_zero] at h
  have h3 : |dist (polar d θ) UpperHalfPlane.I| = |d| :=
    le_antisymm (Real.cosh_le_cosh.mp h.le) (Real.cosh_le_cosh.mp h.ge)
  rwa [abs_of_nonneg dist_nonneg] at h3

/-- **These are genuine geodesic polar coordinates**: every point of the hyperbolic plane is
`polar d θ` for some radius `d ≥ 0` and argument `θ`.  Hence quantifying a configuration of
points by its polar coordinates, as the statements below do, is no restriction. -/
theorem exists_polar (z : ℍ) : ∃ d θ : ℝ, 0 ≤ d ∧ polar d θ = z := by
  by_cases hz : z = UpperHalfPlane.I
  · exact ⟨0, 0, le_rfl, by rw [polar_zero_zero, hz]⟩
  obtain ⟨x, y, hy, hxre, hyim⟩ : ∃ x y : ℝ, 0 < y ∧ z.re = x ∧ z.im = y :=
    ⟨z.re, z.im, z.im_pos, rfl, rfl⟩
  have hyne : y ≠ 0 := ne_of_gt hy
  -- `c₀` is `cosh` of the distance from the centre `i` to `z`
  obtain ⟨c₀, hc₀def⟩ : ∃ c : ℝ, c = (x ^ 2 + y ^ 2 + 1) / (2 * y) := ⟨_, rfl⟩
  have hne : ¬(x = 0 ∧ y = 1) := by
    rintro ⟨hx0, hy1⟩
    exact hz (UpperHalfPlane.ext_re_im (by rw [hxre, hx0]; simp) (by rw [hyim, hy1]; simp))
  have hxypos : 0 < x ^ 2 + (y - 1) ^ 2 := by
    rcases lt_or_eq_of_le (by positivity : (0 : ℝ) ≤ x ^ 2 + (y - 1) ^ 2) with h | h
    · exact h
    · exfalso
      have hx0 : x = 0 := by
        rcases lt_trichotomy x 0 with hlt | heq | hlt
        · exfalso; nlinarith [sq_nonneg (y - 1)]
        · exact heq
        · exfalso; nlinarith [sq_nonneg (y - 1)]
      have hy1 : y = 1 := by
        rcases lt_trichotomy y 1 with hlt | heq | hlt
        · exfalso; nlinarith [sq_nonneg x]
        · exact heq
        · exfalso; nlinarith [sq_nonneg x]
      exact hne ⟨hx0, hy1⟩
  have hc₀ : 1 < c₀ := by
    rw [hc₀def, lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * y)]
    nlinarith [hxypos]
  have hd0 : 0 ≤ arcosh c₀ := Real.arcosh_nonneg hc₀.le
  have hcd : cosh (arcosh c₀) = c₀ := Real.cosh_arcosh hc₀.le
  have hc₀sq : 0 < c₀ ^ 2 - 1 := by nlinarith
  have hSsq : sinh (arcosh c₀) ^ 2 = c₀ ^ 2 - 1 := by
    rw [Real.sinh_arcosh hc₀.le, Real.sq_sqrt hc₀sq.le]
  have hS : 0 < sinh (arcosh c₀) := by
    rw [Real.sinh_arcosh hc₀.le]
    exact Real.sqrt_pos.mpr hc₀sq
  have hSne : sinh (arcosh c₀) ≠ 0 := ne_of_gt hS
  have hkey : (c₀ - 1 / y) ^ 2 + (x / y) ^ 2 = c₀ ^ 2 - 1 := by
    rw [hc₀def]
    field_simp
    try ring
  -- the vector whose argument is the polar angle
  obtain ⟨W, hWre, hWim⟩ : ∃ W : ℂ, W.re = c₀ - 1 / y ∧ W.im = -(x / y) :=
    ⟨⟨c₀ - 1 / y, -(x / y)⟩, rfl, rfl⟩
  have hWnormsq : ‖W‖ ^ 2 = sinh (arcosh c₀) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hWre, hWim, hSsq]
    linear_combination hkey
  have hWnorm : ‖W‖ = sinh (arcosh c₀) := by
    have h := congrArg Real.sqrt hWnormsq
    rwa [Real.sqrt_sq (norm_nonneg W), Real.sqrt_sq hS.le] at h
  have hWne : W ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hWnorm
    exact hSne hWnorm.symm
  have hcos : sinh (arcosh c₀) * cos (Complex.arg W) = c₀ - 1 / y := by
    rw [Complex.cos_arg hWne, hWnorm, hWre]
    field_simp
  have hsin : sinh (arcosh c₀) * sin (Complex.arg W) = -(x / y) := by
    rw [Complex.sin_arg, hWnorm, hWim]
    field_simp
  have hR : cosh (arcosh c₀) - sinh (arcosh c₀) * cos (Complex.arg W) = 1 / y := by
    rw [hcos, hcd]; ring
  refine ⟨arcosh c₀, Complex.arg W, hd0, UpperHalfPlane.ext_re_im ?_ ?_⟩
  · rw [polar_re, hR, hsin, hxre]
    field_simp
  · rw [polar_im, hR, hyim]
    exact one_div_one_div y

/-! ## Part 2 (copied from `HyperbolicCirclePacking.lean`, first pass)

Everything in this section is the first-pass worker's, reproduced verbatim up to the fresh
namespace because that file has no `.olean` and cannot be imported. -/

/-- The paper's `w(d,r) = arccos (clamp ((cosh d cosh r - cosh (D/2))/(sinh d sinh r)))`,
the half-width of the arc cut from the hyperbolic circle of radius `r` about the centre by
the open hyperbolic ball of radius `D/2` about a point at distance `d` from the centre.
`clamp` truncates to `[-1,1]`. -/
def sliceHalfAngle (D d r : ℝ) : ℝ :=
  arccos (max (-1) (min 1 ((cosh d * cosh r - cosh (D / 2)) / (sinh d * sinh r))))

theorem sliceHalfAngle_nonneg (D d r : ℝ) : 0 ≤ sliceHalfAngle D d r :=
  arccos_nonneg _

theorem sliceHalfAngle_le_pi (D d r : ℝ) : sliceHalfAngle D d r ≤ π :=
  arccos_le_pi _

/-- An angle strictly inside the slice satisfies the strict law-of-cosines inequality that
defines the open ball. -/
private theorem cosh_expr_lt_of_abs_lt {D d r φ : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hφ : |φ| < sliceHalfAngle D d r) :
    cosh d * cosh r - sinh d * sinh r * cos φ < cosh (D / 2) := by
  have hprod : 0 < sinh d * sinh r :=
    mul_pos (sinh_pos_iff.mpr hd) (sinh_pos_iff.mpr hr)
  set X : ℝ := (cosh d * cosh r - cosh (D / 2)) / (sinh d * sinh r) with hXdef
  set c : ℝ := max (-1) (min 1 X) with hcdef
  have hw : sliceHalfAngle D d r = arccos c := by rw [hcdef, hXdef]; rfl
  have hc1 : c ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hc2 : (-1 : ℝ) ≤ c := le_max_left _ _
  rw [hw] at hφ
  have habs : |φ| ∈ Icc 0 π := ⟨abs_nonneg φ, le_trans hφ.le (arccos_le_pi c)⟩
  have harc : arccos c ∈ Icc 0 π := ⟨arccos_nonneg c, arccos_le_pi c⟩
  have hcos : cos (arccos c) < cos |φ| := strictAntiOn_cos habs harc hφ
  rw [cos_arccos hc2 hc1, cos_abs] at hcos
  have hXle : X ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have hc' : c = 1 := by
      rw [hcdef, min_eq_left hcon.le, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [hc', arccos_one] at hφ
    exact absurd hφ (not_lt.mpr (abs_nonneg φ))
  have hXc : X ≤ c := by
    rw [hcdef, min_eq_right hXle]
    exact le_max_right _ _
  have hXlt : X < cos φ := lt_of_le_of_lt hXc hcos
  rw [hXdef, div_lt_iff₀ hprod] at hXlt
  linarith

/-- The law of cosines turns the slice condition into membership of the open hyperbolic ball
of radius `D/2`. -/
private theorem dist_lt_half {P : Type*} [PseudoMetricSpace P] (pt : ℝ → ℝ → P)
    (hlaw : ∀ d₁ θ₁ d₂ θ₂ : ℝ, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂))
    {D d r θ₀ θ₁ φ : ℝ} (hD : 0 < D) (hd : 0 < d) (hr : 0 < r)
    (hφ : |φ| < sliceHalfAngle D d r) (hcos : cos φ = cos (θ₀ - θ₁)) :
    dist (pt r θ₀) (pt d θ₁) < D / 2 := by
  have hkey := cosh_expr_lt_of_abs_lt hd hr hφ
  rw [hcos] at hkey
  have hlt : cosh (dist (pt r θ₀) (pt d θ₁)) < cosh (D / 2) := by
    rw [hlaw r θ₀ d θ₁]
    linarith
  have habs := cosh_lt_cosh.mp hlt
  rwa [abs_of_nonneg dist_nonneg,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ D / 2)] at habs

/-- **`res:circle-slice-packing`, abstract form** (first pass).  If the `k` points at geodesic
polar coordinates `(d_j, θ_j)` are pairwise at hyperbolic distance at least `D`, then for
every radius `r > 0` the slice half-angles `w(d_j, r)` sum to at most `π`. -/
theorem circle_slice_packing_abstract {P : Type*} [PseudoMetricSpace P] (pt : ℝ → ℝ → P)
    (hlaw : ∀ d₁ θ₁ d₂ θ₂ : ℝ, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂))
    {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (pt (d i) (θ i)) (pt (d j) (θ j)))
    {r : ℝ} (hr : 0 < r) :
    ∑ j, sliceHalfAngle D (d j) r ≤ π := by
  classical
  have hpi : (0 : ℝ) < π := pi_pos
  obtain ⟨w, hwdef⟩ : ∃ w : Fin k → ℝ, ∀ j, w j = sliceHalfAngle D (d j) r :=
    ⟨fun j => sliceHalfAngle D (d j) r, fun _ => rfl⟩
  have hgoal : ∑ j, sliceHalfAngle D (d j) r = ∑ j, w j :=
    Finset.sum_congr rfl fun j _ => (hwdef j).symm
  rw [hgoal]
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j; rw [hwdef]; exact sliceHalfAngle_nonneg _ _ _
  have hwpi : ∀ j, w j ≤ π := by
    intro j; rw [hwdef]; exact sliceHalfAngle_le_pi _ _ _
  -- membership of the open ball, in the `2π`-shifted form
  have hmem : ∀ (j : Fin k) (y : ℝ) (m : ℤ), |y - (m : ℝ) * (2 * π) - θ j| < w j →
      dist (pt r y) (pt (d j) (θ j)) < D / 2 := by
    intro j y m hlt
    rw [hwdef] at hlt
    refine dist_lt_half pt hlaw hD (hd j) hr hlt ?_
    have hrw : y - (m : ℝ) * (2 * π) - θ j = (y - θ j) - (m : ℝ) * (2 * π) := by ring
    rw [hrw, cos_sub_int_mul_two_pi]
  -- disjointness: a test angle cannot lie in two slices
  have hdisj : ∀ i j : Fin k, i ≠ j → ∀ (y : ℝ) (m n : ℤ),
      |y - (m : ℝ) * (2 * π) - θ i| < w i → |y - (n : ℝ) * (2 * π) - θ j| < w j → False := by
    intro i j hij y m n hi hj
    have h1 := hmem i y m hi
    have h2 := hmem j y n hj
    have h3 := hsep i j hij
    have htri : dist (pt (d i) (θ i)) (pt (d j) (θ j))
        ≤ dist (pt (d i) (θ i)) (pt r y) + dist (pt r y) (pt (d j) (θ j)) :=
      dist_triangle _ _ _
    rw [dist_comm (pt (d i) (θ i)) (pt r y)] at htri
    linarith
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact hpi.le
  -- a uniform bound for the angles
  have hT0 : (0 : ℝ) ≤ ∑ j, |θ j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hTle : ∀ j, |θ j| ≤ ∑ j, |θ j| := fun j =>
    Finset.single_le_sum (f := fun j => |θ j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  -- the `N`-fold interval packing estimate
  have key : ∀ N : ℕ, 0 < N →
      2 * (N : ℝ) * (∑ j, w j) ≤ 2 * (∑ j, |θ j|) + 2 * π * (N : ℝ) + 2 * π := by
    intro N hN
    obtain ⟨I, hIdef⟩ : ∃ I : Fin k × Fin N → Set ℝ, ∀ q : Fin k × Fin N,
        I q = Ioo (θ q.1 + (q.2.val : ℝ) * (2 * π) - w q.1)
                  (θ q.1 + (q.2.val : ℝ) * (2 * π) + w q.1) := ⟨_, fun _ => rfl⟩
    have hImeas : ∀ q : Fin k × Fin N, MeasurableSet (I q) := by
      intro q; rw [hIdef]; exact measurableSet_Ioo
    have hIvol : ∀ q : Fin k × Fin N, volume (I q) = ENNReal.ofReal (2 * w q.1) := by
      intro q
      rw [hIdef, Real.volume_Ioo]
      congr 1
      ring
    have hIsub : ∀ q : Fin k × Fin N,
        I q ⊆ Icc (-(∑ j, |θ j|) - π) ((∑ j, |θ j|) + 2 * π * (N : ℝ) + π) := by
      intro q y hy
      rw [hIdef, mem_Ioo] at hy
      have habs := hTle q.1
      rw [abs_le] at habs
      have h4 := hw0 q.1
      have h5 := hwpi q.1
      have h6 : (0 : ℝ) ≤ (q.2.val : ℝ) * (2 * π) := by positivity
      have hq2 : ((q.2.val : ℕ) : ℝ) ≤ (N : ℝ) - 1 := by
        have hlt : (q.2.val : ℕ) + 1 ≤ N := q.2.isLt
        have hc := (Nat.cast_le (α := ℝ)).mpr hlt
        push_cast at hc
        linarith
      have h7 : (q.2.val : ℝ) * (2 * π) ≤ ((N : ℝ) - 1) * (2 * π) :=
        mul_le_mul_of_nonneg_right hq2 (by positivity)
      constructor
      · linarith [hy.1, habs.1]
      · linarith [hy.2, habs.2]
    have hpd : ((Finset.univ : Finset (Fin k × Fin N)) : Set (Fin k × Fin N)).PairwiseDisjoint I := by
      intro q₁ _ q₂ _ hne
      obtain ⟨i, m⟩ := q₁
      obtain ⟨j, n⟩ := q₂
      have hgoal2 : Disjoint (I (i, m)) (I (j, n)) := by
        rw [Set.disjoint_left]
        intro y hy₁ hy₂
        rw [hIdef, mem_Ioo] at hy₁
        rw [hIdef, mem_Ioo] at hy₂
        simp only at hy₁ hy₂
        by_cases hfst : i = j
        · have hsnd : m ≠ n := by
            intro h
            exact hne (by rw [hfst, h])
          subst hfst
          have hW := hwpi i
          have hlt1 : (m.val : ℝ) * (2 * π) < (n.val : ℝ) * (2 * π) + 2 * π := by
            linarith [hy₁.1, hy₂.2]
          have hlt2 : (n.val : ℝ) * (2 * π) < (m.val : ℝ) * (2 * π) + 2 * π := by
            linarith [hy₂.1, hy₁.2]
          have hu : (m.val : ℝ) < (n.val : ℝ) + 1 := by nlinarith [hlt1, hpi]
          have hv : (n.val : ℝ) < (m.val : ℝ) + 1 := by nlinarith [hlt2, hpi]
          have hmn : m.val = n.val := by
            have c1 : m.val < n.val + 1 := by exact_mod_cast hu
            have c2 : n.val < m.val + 1 := by exact_mod_cast hv
            omega
          exact hsnd (Fin.val_injective hmn)
        · refine hdisj i j hfst y (m.val : ℤ) (n.val : ℤ) ?_ ?_
          · rw [abs_lt]
            push_cast
            constructor <;> linarith [hy₁.1, hy₁.2]
          · rw [abs_lt]
            push_cast
            constructor <;> linarith [hy₂.1, hy₂.2]
      exact hgoal2
    have hunion : volume (⋃ q ∈ (Finset.univ : Finset (Fin k × Fin N)), I q)
        = ∑ q ∈ (Finset.univ : Finset (Fin k × Fin N)), volume (I q) :=
      measure_biUnion_finset hpd fun q _ => hImeas q
    have hsubset : (⋃ q ∈ (Finset.univ : Finset (Fin k × Fin N)), I q)
        ⊆ Icc (-(∑ j, |θ j|) - π) ((∑ j, |θ j|) + 2 * π * (N : ℝ) + π) := by
      intro y hy
      simp only [Set.mem_iUnion, exists_prop] at hy
      obtain ⟨q, _, hyq⟩ := hy
      exact hIsub q hyq
    have hbound : ∑ q ∈ (Finset.univ : Finset (Fin k × Fin N)), volume (I q)
        ≤ volume (Icc (-(∑ j, |θ j|) - π) ((∑ j, |θ j|) + 2 * π * (N : ℝ) + π)) := by
      rw [← hunion]
      exact measure_mono hsubset
    rw [Real.volume_Icc] at hbound
    simp only [hIvol] at hbound
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun q (_ : q ∈ (Finset.univ : Finset (Fin k × Fin N))) => by
        have := hw0 q.1; linarith)] at hbound
    have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hBA : (0 : ℝ) ≤ (∑ j, |θ j|) + 2 * π * (N : ℝ) + π - (-(∑ j, |θ j|) - π) := by
      nlinarith [hT0, hpi, hNR]
    rw [ENNReal.ofReal_le_ofReal_iff hBA] at hbound
    have hsumeq : ∑ q ∈ (Finset.univ : Finset (Fin k × Fin N)), 2 * w q.1
        = 2 * (N : ℝ) * ∑ j, w j := by
      rw [Fintype.sum_prod_type]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hsumeq] at hbound
    linarith
  -- let `N → ∞`
  by_contra hcon
  push_neg at hcon
  obtain ⟨N, hN⟩ := exists_nat_gt (((∑ j, |θ j|) + π) / ((∑ j, w j) - π))
  have hgap : 0 < (∑ j, w j) - π := by linarith
  have hNpos : 0 < N := by
    by_contra hz
    push_neg at hz
    interval_cases N
    · simp only [Nat.cast_zero] at hN
      have : (0 : ℝ) ≤ ((∑ j, |θ j|) + π) / ((∑ j, w j) - π) := by positivity
      linarith
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hkey := key N hNpos
  have hmul : (∑ j, |θ j|) + π < (N : ℝ) * ((∑ j, w j) - π) :=
    (div_lt_iff₀ hgap).mp hN
  nlinarith [hkey, hmul, hNR]

/-- The paper's `λ(d) = -log tanh(d/2)`. -/
def lam (d : ℝ) : ℝ := -log (tanh (d / 2))

/-- The paper's `δ(a) = -log(1 - e^{-1/a})`. -/
def delta (a : ℝ) : ℝ := -log (1 - exp (-(1 / a)))

private theorem hyp_tanh_strictMono : StrictMono tanh := by
  intro x y hxy
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh,
    div_lt_div_iff₀ (cosh_pos x) (cosh_pos y)]
  have h : 0 < sinh (y - x) := sinh_pos_iff.mpr (by linarith)
  rw [sinh_sub] at h
  linarith

private theorem hyp_tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < tanh x := by
  have h := hyp_tanh_strictMono hx
  rwa [tanh_zero] at h

private theorem lam_lt_lam {d₁ d₂ : ℝ} (h₁ : 0 < d₁) (h : d₁ < d₂) : lam d₂ < lam d₁ := by
  have ht1 : 0 < tanh (d₁ / 2) := hyp_tanh_pos_of_pos (by linarith)
  have ht : tanh (d₁ / 2) < tanh (d₂ / 2) := hyp_tanh_strictMono (by linarith)
  have hlog : log (tanh (d₁ / 2)) < log (tanh (d₂ / 2)) := log_lt_log ht1 ht
  unfold lam
  linarith

/-- `λ` is strictly decreasing on the positive axis, so the paper's radius bound
`λ(d_j) ≤ δ(a)/2 = λ(d_low(a))` is the statement `d_j ≥ d_low(a)`. -/
theorem le_of_lam_le {d₁ d₂ : ℝ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h : lam d₂ ≤ lam d₁) :
    d₁ ≤ d₂ := by
  by_contra hcon
  push_neg at hcon
  exact absurd h (not_le.mpr (lam_lt_lam h₂ hcon))

/-- **`res:dual-arity-floor`, abstract form** (first pass). -/
theorem dual_arity_floor_abstract {P : Type*} [PseudoMetricSpace P] (pt : ℝ → ℝ → P)
    (hlaw : ∀ d₁ θ₁ d₂ θ₂ : ℝ, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂))
    {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (pt (d i) (θ i)) (pt (d j) (θ j)))
    {p : ℕ} (r σ : Fin p → ℝ) (hr : ∀ i, 0 < r i) (hσ : ∀ i, 0 ≤ σ i)
    {a x dlow U : ℝ} (hdlow : 0 < dlow) (hdlowval : lam dlow = delta a / 2)
    (hrad : ∀ j, lam (d j) ≤ delta a / 2)
    (hbudget : x ≤ ∑ j, lam (d j))
    (hU : ∀ s : ℝ, dlow ≤ s → lam s - ∑ i, σ i * sliceHalfAngle D s (r i) ≤ U)
    (hUpos : 0 < U) :
    (x - π * ∑ i, σ i) / U ≤ (k : ℝ) := by
  classical
  have hdj : ∀ j, dlow ≤ d j := fun j =>
    le_of_lam_le hdlow (hd j) (by rw [hdlowval]; exact hrad j)
  have hsum1 : ∑ j, (lam (d j) - ∑ i, σ i * sliceHalfAngle D (d j) (r i)) ≤ (k : ℝ) * U := by
    calc ∑ j, (lam (d j) - ∑ i, σ i * sliceHalfAngle D (d j) (r i))
        ≤ ∑ _j : Fin k, U := Finset.sum_le_sum fun j _ => hU (d j) (hdj j)
      _ = (k : ℝ) * U := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpack : ∀ i, ∑ j, sliceHalfAngle D (d j) (r i) ≤ π := fun i =>
    circle_slice_packing_abstract pt hlaw d θ hd hD hsep (hr i)
  have hsum2 : ∑ j, ∑ i, σ i * sliceHalfAngle D (d j) (r i) ≤ π * ∑ i, σ i := by
    rw [Finset.sum_comm]
    calc ∑ i, ∑ j, σ i * sliceHalfAngle D (d j) (r i)
        = ∑ i, σ i * ∑ j, sliceHalfAngle D (d j) (r i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ i, σ i * π :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpack i) (hσ i)
      _ = π * ∑ i, σ i := by rw [← Finset.sum_mul]; ring
  have hsplit : ∑ j, (lam (d j) - ∑ i, σ i * sliceHalfAngle D (d j) (r i))
      = (∑ j, lam (d j)) - ∑ j, ∑ i, σ i * sliceHalfAngle D (d j) (r i) := by
    rw [Finset.sum_sub_distrib]
  rw [hsplit] at hsum1
  rw [div_le_iff₀ hUpos]
  linarith

/-! ## Part 3 (new): the paper's two environments, with no law-of-cosines hypothesis -/

/-- **`res:circle-slice-packing`** (`paper/reasoning-parts/erdos1041/core.tex`, line 378),
unconditionally, in the hyperbolic plane.

`k` points of the hyperbolic plane are given in geodesic polar coordinates `(d_j, θ_j)`
about the centre (`exists_polar`: every point has such coordinates).  Assuming
`(eq:lc-separation)`, i.e. that the points are pairwise at hyperbolic distance at least `D`,
the slice half-angles `w(d_j, r)` sum to at most `π` for every radius `r > 0`.

No external hypothesis: the hyperbolic law of cosines is `cosh_dist_polar`, proved above. -/
theorem circle_slice_packing {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (polar (d i) (θ i)) (polar (d j) (θ j)))
    {r : ℝ} (hr : 0 < r) :
    ∑ j, sliceHalfAngle D (d j) r ≤ π :=
  circle_slice_packing_abstract polar cosh_dist_polar d θ hd hD hsep hr

/-- **`res:dual-arity-floor`** (`paper/reasoning-parts/erdos1041/core.tex`, line 401), in the
hyperbolic plane with no law-of-cosines hypothesis.

Hypotheses are exactly the paper's: `(eq:lc-separation)` (`hsep`), and the two consequences
`(eq:lc-radius-and-budget)` of the standing failure hypothesis, namely the radius bound
`λ(d_j) ≤ δ(a)/2` (`hrad`, with `hdlowval : λ(d_low(a)) = δ(a)/2`) and the budget
`∑_j λ(d_j) ≥ x` (`hbudget`).  Nonnegative weights `σ_i` at radii `r_i > 0` with positive
deficit `U` then force `k ≥ (x - πΣ)/U`.  Here `U` is any upper bound for the paper's
supremand on `[d_low(a), ∞)`; `dual_arity_floor_sup` is the form with `U` the supremum. -/
theorem dual_arity_floor {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (polar (d i) (θ i)) (polar (d j) (θ j)))
    {p : ℕ} (r σ : Fin p → ℝ) (hr : ∀ i, 0 < r i) (hσ : ∀ i, 0 ≤ σ i)
    {a x dlow U : ℝ} (hdlow : 0 < dlow) (hdlowval : lam dlow = delta a / 2)
    (hrad : ∀ j, lam (d j) ≤ delta a / 2)
    (hbudget : x ≤ ∑ j, lam (d j))
    (hU : ∀ s : ℝ, dlow ≤ s → lam s - ∑ i, σ i * sliceHalfAngle D s (r i) ≤ U)
    (hUpos : 0 < U) :
    (x - π * ∑ i, σ i) / U ≤ (k : ℝ) :=
  dual_arity_floor_abstract polar cosh_dist_polar d θ hd hD hsep r σ hr hσ hdlow hdlowval
    hrad hbudget hU hUpos

/-- `res:dual-arity-floor` with `U` given exactly as the paper's supremum, and with no
law-of-cosines hypothesis. -/
theorem dual_arity_floor_sup {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (polar (d i) (θ i)) (polar (d j) (θ j)))
    {p : ℕ} (r σ : Fin p → ℝ) (hr : ∀ i, 0 < r i) (hσ : ∀ i, 0 ≤ σ i)
    {a x dlow U : ℝ} (hdlow : 0 < dlow) (hdlowval : lam dlow = delta a / 2)
    (hrad : ∀ j, lam (d j) ≤ delta a / 2)
    (hbudget : x ≤ ∑ j, lam (d j))
    (hU : IsLUB {y : ℝ | ∃ s : ℝ, dlow ≤ s ∧
      y = lam s - ∑ i, σ i * sliceHalfAngle D s (r i)} U)
    (hUpos : 0 < U) :
    (x - π * ∑ i, σ i) / U ≤ (k : ℝ) :=
  dual_arity_floor d θ hd hD hsep r σ hr hσ hdlow hdlowval hrad hbudget
    (fun s hs => hU.1 ⟨s, hs, rfl⟩) hUpos

#print axioms polarDen_pos
#print axioms cosh_dist_polar
#print axioms polar_zero_zero
#print axioms dist_polar_I
#print axioms exists_polar
#print axioms sliceHalfAngle_nonneg
#print axioms sliceHalfAngle_le_pi
#print axioms circle_slice_packing_abstract
#print axioms le_of_lam_le
#print axioms dual_arity_floor_abstract
#print axioms circle_slice_packing
#print axioms dual_arity_floor
#print axioms dual_arity_floor_sup

end ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic

end
