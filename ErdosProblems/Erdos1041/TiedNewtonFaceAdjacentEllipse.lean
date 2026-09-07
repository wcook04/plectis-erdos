import Mathlib.Tactic

/-!
# Erdős #1041: adjacent regular-polygon foci spend no metric excess

The angular sector of a radius-`R` disk between adjacent regular-polygon
vertices lies in the ellipse with those vertices as foci and major axis `2R`.
This module checks the algebraic kernel of that geometric covering.  Its
consumer is the tied Newton-face connector: once two adjacent arms are proved
contained and their hub lies in the cutoff disk, their broken-line length is
automatically at most `2R`.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceAdjacentEllipse

/-- Polar-sector data imply membership in the axis-aligned adjacent-focus
ellipse.  Here `(b, ±f)` are the foci, `R` is the semimajor axis, and
`(rho*u,rho*v)` is the point before translating the ellipse centre by `b`. -/
theorem sector_ellipse_quadratic
    {R b u v rho : ℝ}
    (hR : 0 < R)
    (hrho0 : 0 ≤ rho) (hrhoR : rho ≤ R)
    (huv : u ^ 2 + v ^ 2 = 1)
    (hleft : 0 ≤ R * u - b) (hright : R * u - b ≤ b * u) :
    R ^ 2 * (rho * u - b) ^ 2 + b ^ 2 * (rho * v) ^ 2 ≤
      R ^ 2 * b ^ 2 := by
  have hbu : 0 ≤ b * u := le_trans hleft hright
  have hsq : (R * u - b) ^ 2 ≤ (b * u) ^ 2 :=
    (sq_le_sq₀ hleft hbu).2 hright
  have ha : R ^ 2 * u ^ 2 + b ^ 2 * v ^ 2 ≤ 2 * R * u * b := by
    nlinarith
  have ha0 : 0 ≤ R ^ 2 * u ^ 2 + b ^ 2 * v ^ 2 := by positivity
  have hrhoa :
      rho * (R ^ 2 * u ^ 2 + b ^ 2 * v ^ 2) ≤
        R * (R ^ 2 * u ^ 2 + b ^ 2 * v ^ 2) :=
    mul_le_mul_of_nonneg_right hrhoR ha0
  have hRa :
      R * (R ^ 2 * u ^ 2 + b ^ 2 * v ^ 2) ≤
        R * (2 * R * u * b) :=
    mul_le_mul_of_nonneg_left ha hR.le
  have hrhobound :
      rho * (R ^ 2 * u ^ 2 + b ^ 2 * v ^ 2) ≤ 2 * R ^ 2 * u * b := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hrhobound hrho0
  nlinarith

/-- The elementary half-angle conditions used for a sector bracket imply the
right-hand inequality consumed by `sector_ellipse_quadratic`. -/
theorem bracket_right_inequality
    {R b u v : ℝ}
    (hb : 0 ≤ b) (hhalf : R ≤ 2 * b)
    (hu : 0 ≤ u) (huv : u ^ 2 + v ^ 2 = 1) :
    R * u - b ≤ b * u := by
  have hu_sq : u ^ 2 ≤ 1 := by nlinarith [sq_nonneg v]
  have hu_one : u ≤ 1 := (sq_le_sq₀ hu zero_le_one).1 (by simpa using hu_sq)
  have hRb : R - b ≤ b := by linarith
  have hmul : (R - b) * u ≤ b * u :=
    mul_le_mul_of_nonneg_right hRb hu
  have hbu : b * u ≤ b := by
    simpa using mul_le_mul_of_nonneg_left hu_one hb
  nlinarith

/-- Algebraic focus form of the ellipse theorem: ellipse membership forces
the sum of the two focal distances to be at most the major axis `2R`. -/
theorem ellipse_distance_sum_le_two_mul
    {R b f X Y d₁ d₂ : ℝ}
    (hR : 0 < R) (hb : 0 < b)
    (hpyth : R ^ 2 = b ^ 2 + f ^ 2)
    (hd₁0 : 0 ≤ d₁) (hd₂0 : 0 ≤ d₂)
    (hd₁ : d₁ ^ 2 = X ^ 2 + (Y - f) ^ 2)
    (hd₂ : d₂ ^ 2 = X ^ 2 + (Y + f) ^ 2)
    (hellipse : R ^ 2 * X ^ 2 + b ^ 2 * Y ^ 2 ≤ R ^ 2 * b ^ 2) :
    d₁ + d₂ ≤ 2 * R := by
  have hR_sq : 0 < R ^ 2 := sq_pos_of_pos hR
  have hb_sq : 0 < b ^ 2 := sq_pos_of_pos hb
  have hX : X ^ 2 ≤ b ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg Y)]
  have hY : Y ^ 2 ≤ R ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg R) (sq_nonneg X)]
  have hS : X ^ 2 + Y ^ 2 + f ^ 2 ≤ 2 * R ^ 2 := by
    nlinarith
  have hprod_sq :
      (d₁ * d₂) ^ 2 =
        (X ^ 2 + Y ^ 2 + f ^ 2) ^ 2 - 4 * f ^ 2 * Y ^ 2 := by
    rw [show (d₁ * d₂) ^ 2 = d₁ ^ 2 * d₂ ^ 2 by ring, hd₁, hd₂]
    ring
  have hgap :
      (2 * R ^ 2 - (X ^ 2 + Y ^ 2 + f ^ 2)) ^ 2 -
          (d₁ * d₂) ^ 2 =
        4 * (R ^ 2 * b ^ 2 - R ^ 2 * X ^ 2 - b ^ 2 * Y ^ 2) := by
    rw [hprod_sq]
    nlinarith
  have hprod_sq_le :
      (d₁ * d₂) ^ 2 ≤
        (2 * R ^ 2 - (X ^ 2 + Y ^ 2 + f ^ 2)) ^ 2 := by
    nlinarith
  have hprod0 : 0 ≤ d₁ * d₂ := mul_nonneg hd₁0 hd₂0
  have hbudget0 : 0 ≤ 2 * R ^ 2 - (X ^ 2 + Y ^ 2 + f ^ 2) := by
    linarith
  have hprod :
      d₁ * d₂ ≤ 2 * R ^ 2 - (X ^ 2 + Y ^ 2 + f ^ 2) :=
    (sq_le_sq₀ hprod0 hbudget0).1 hprod_sq_le
  have hsum_sq : (d₁ + d₂) ^ 2 ≤ (2 * R) ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ (add_nonneg hd₁0 hd₂0) (by positivity)).1 hsum_sq

/-- The complete finite kernel.  `R ≤ 2b` is exactly
`cos(delta) ≥ 1/2`, hence it holds for adjacent `n`-th-root directions when
`n ≥ 3`.  The inequality `b ≤ R*u` says the point's argument lies between the
two adjacent focus arguments. -/
theorem adjacent_sector_distance_sum_le_two_mul
    {R b f rho u v d₁ d₂ : ℝ}
    (hR : 0 < R) (hb : 0 < b)
    (hpyth : R ^ 2 = b ^ 2 + f ^ 2)
    (hhalf : R ≤ 2 * b)
    (hrho0 : 0 ≤ rho) (hrhoR : rho ≤ R)
    (hu : 0 ≤ u) (huv : u ^ 2 + v ^ 2 = 1)
    (hbracket : b ≤ R * u)
    (hd₁0 : 0 ≤ d₁) (hd₂0 : 0 ≤ d₂)
    (hd₁ : d₁ ^ 2 = (rho * u - b) ^ 2 + (rho * v - f) ^ 2)
    (hd₂ : d₂ ^ 2 = (rho * u - b) ^ 2 + (rho * v + f) ^ 2) :
    d₁ + d₂ ≤ 2 * R := by
  have hright : R * u - b ≤ b * u :=
    bracket_right_inequality hb.le hhalf hu huv
  have hellipse :
      R ^ 2 * (rho * u - b) ^ 2 + b ^ 2 * (rho * v) ^ 2 ≤
        R ^ 2 * b ^ 2 :=
    sector_ellipse_quadratic hR hrho0 hrhoR huv
      (sub_nonneg.mpr hbracket) hright
  apply ellipse_distance_sum_le_two_mul hR hb hpyth hd₁0 hd₂0 hd₁ hd₂
  simpa [mul_pow] using hellipse

end ErdosProblems.Erdos1041.TiedNewtonFaceAdjacentEllipse
