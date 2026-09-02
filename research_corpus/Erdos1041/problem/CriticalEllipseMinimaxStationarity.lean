import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Erdős #1041: algebraic kernels for critical-ellipse minimax stationarity

The companion note applies the standard Danskin/convex-Fermat rule to the
maximum of the two segment envelopes.  This module checks the algebraic
consumers after that analytic rule has produced a convex balance of active
gradients.  It does not formalize Danskin's theorem, the complex derivative,
or CE--GM itself.
-/

namespace ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity

/-- A strict two-contact convex balance makes the two real gradient vectors
oppositely directed, with the exact positive scale forced by the weight. -/
theorem twoContact_balance_opposed
    {weight ax ay bx byCoord : ℝ}
    (hweight : 0 < weight)
    (hx : weight * ax + (1 - weight) * bx = 0)
    (hy : weight * ay + (1 - weight) * byCoord = 0) :
    ax = -((1 - weight) / weight) * bx ∧
      ay = -((1 - weight) / weight) * byCoord := by
  have hne : weight ≠ 0 := ne_of_gt hweight
  constructor <;> field_simp [hne] <;> linarith

/-- Real-coordinate gradient convention used in the note: the dot product of
`(q.re,-q.im)` with a complex displacement is `Re(q*d)`. -/
theorem logarithmicGradient_dot (q d : ℂ) :
    q.re * d.re + (-q.im) * d.im = (q * d).re := by
  rw [Complex.mul_re]
  ring

/-- Two planar directions orthogonal to the same nonzero normal are parallel.
This is the algebraic core of the two-contact collapse. -/
theorem parallel_of_common_nonzero_normal
    {gx gy dax day dbx dby : ℝ}
    (hnormal : gx ≠ 0 ∨ gy ≠ 0)
    (ha : gx * dax + gy * day = 0)
    (hb : gx * dbx + gy * dby = 0) :
    dax * dby - day * dbx = 0 := by
  rcases hnormal with hgx | hgy
  · have hmul : gx * (dax * dby - day * dbx) = 0 := by
      calc
        gx * (dax * dby - day * dbx) =
            (gx * dax + gy * day) * dby - day * (gx * dbx + gy * dby) := by ring
        _ = 0 := by rw [ha, hb]; ring
    exact (mul_eq_zero.mp hmul).resolve_left hgx
  · have hmul : gy * (dax * dby - day * dbx) = 0 := by
      calc
        gy * (dax * dby - day * dbx) =
            dax * (gx * dbx + gy * dby) - (gx * dax + gy * day) * dbx := by ring
        _ = 0 := by rw [ha, hb]; ring
    exact (mul_eq_zero.mp hmul).resolve_left hgy

/-- At a noncritical two-contact balance on two distinct arms, tangent
stationarity forces the two hub-to-root directions to be parallel.  When both
contacts lie on the same arm this conclusion is tautological, so the geometric
consumer must retain the distinct-arm interpretation explicitly. -/
theorem twoContact_tangent_balance_forces_parallel
    {scale ax ay bx byCoord dax day dbx dby : ℝ}
    (hscale : 0 < scale)
    (hopposedX : ax = -scale * bx)
    (hopposedY : ay = -scale * byCoord)
    (hnormal : ax ≠ 0 ∨ ay ≠ 0)
    (htangentA : ax * dax + ay * day = 0)
    (htangentB : bx * dbx + byCoord * dby = 0) :
    dax * dby - day * dbx = 0 := by
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale
  have htangentB' : ax * dbx + ay * dby = 0 := by
    rw [hopposedX, hopposedY]
    calc
      -scale * bx * dbx + -scale * byCoord * dby =
          -scale * (bx * dbx + byCoord * dby) := by ring
      _ = 0 := by rw [htangentB]; ring
  exact parallel_of_common_nonzero_normal hnormal htangentA htangentB'

/-- Coefficients of a zero linear combination of two independent planar
directions both vanish. -/
theorem coefficients_zero_of_independent_balance
    {ux uy vx vy alpha beta : ℝ}
    (hindependent : ux * vy - uy * vx ≠ 0)
    (hx : alpha * ux + beta * vx = 0)
    (hy : alpha * uy + beta * vy = 0) :
    alpha = 0 ∧ beta = 0 := by
  have halphaMul : alpha * (ux * vy - uy * vx) = 0 := by
    calc
      alpha * (ux * vy - uy * vx) =
          (alpha * ux + beta * vx) * vy -
            (alpha * uy + beta * vy) * vx := by ring
      _ = 0 := by rw [hx, hy]; ring
  have hbetaMul : beta * (ux * vy - uy * vx) = 0 := by
    calc
      beta * (ux * vy - uy * vx) =
          ux * (alpha * uy + beta * vy) -
            uy * (alpha * ux + beta * vx) := by ring
      _ = 0 := by rw [hx, hy]; ring
  constructor
  · exact (mul_eq_zero.mp halphaMul).resolve_right hindependent
  · exact (mul_eq_zero.mp hbetaMul).resolve_right hindependent

/-- If two tangent gradients lie on one arm normal and a singleton tangent
gradient lies on an independent arm normal, a positive three-contact balance
forces the singleton's scalar gradient to vanish.  Analytically, that contact
is critical. -/
theorem twoPlusOne_independentNormals_forces_singletonScale_zero
    {nax nay nbx nby w₁ w₂ w₃ s₁ s₂ s₃ : ℝ}
    (hindependent : nax * nby - nay * nbx ≠ 0)
    (hw₃ : w₃ ≠ 0)
    (hx : (w₁ * s₁ + w₂ * s₂) * nax + (w₃ * s₃) * nbx = 0)
    (hy : (w₁ * s₁ + w₂ * s₂) * nay + (w₃ * s₃) * nby = 0) :
    s₃ = 0 := by
  have hcoeff := coefficients_zero_of_independent_balance hindependent hx hy
  exact (mul_eq_zero.mp hcoeff.2).resolve_left hw₃

/-- Real-coordinate logarithmic gradient at a point is `S * (h - B)` for its
inverse-square barycenter `B`.  This is the algebraic bridge from endpoint KKT
signs to the barycentric descent disc. -/
theorem inverseSquare_logGradient_dot
    {S hx hy mx my qx qy ux uy : ℝ}
    (hqx : qx = S * (hx - mx))
    (hqy : qy = S * (hy - my)) :
    qx * ux + qy * uy =
      S * ((hx - mx) * ux + (hy - my) * uy) := by
  rw [hqx, hqy]
  ring

/-- Squared-distance identity for a ray starting at a boundary point of the
disc centered at the inverse-square barycenter. -/
theorem descentDisc_ray_squaredDifference
    (dx dy ux uy s : ℝ) :
    (s * ux - dx) ^ 2 + (s * uy - dy) ^ 2 - (dx ^ 2 + dy ^ 2) =
      s * (s * (ux ^ 2 + uy ^ 2) - 2 * (dx * ux + dy * uy)) := by
  ring

/-- A unit ray from a boundary point remains in the descent disc for exactly
the projection-controlled initial interval used in the companion note. -/
theorem ray_mem_descentDisc_of_le_projection
    {dx dy ux uy s : ℝ}
    (hunit : ux ^ 2 + uy ^ 2 = 1)
    (hsnonneg : 0 ≤ s)
    (hsprojection : s ≤ 2 * (dx * ux + dy * uy)) :
    (s * ux - dx) ^ 2 + (s * uy - dy) ^ 2 ≤ dx ^ 2 + dy ^ 2 := by
  have hfactor :
      s * (s * (ux ^ 2 + uy ^ 2) - 2 * (dx * ux + dy * uy)) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos hsnonneg
    rw [hunit]
    linarith
  nlinarith [descentDisc_ray_squaredDifference dx dy ux uy s]

/-- For a strictly positive ray parameter the projection bound is also
necessary, so the descent-disc entry length is exact. -/
theorem ray_mem_descentDisc_iff_le_projection
    {dx dy ux uy s : ℝ}
    (hunit : ux ^ 2 + uy ^ 2 = 1)
    (hspos : 0 < s) :
    (s * ux - dx) ^ 2 + (s * uy - dy) ^ 2 ≤ dx ^ 2 + dy ^ 2 ↔
      s ≤ 2 * (dx * ux + dy * uy) := by
  rw [← sub_nonpos]
  rw [descentDisc_ray_squaredDifference]
  rw [hunit]
  constructor
  · intro hproduct
    by_contra hnot
    have hstrict : 2 * (dx * ux + dy * uy) < s := lt_of_not_ge hnot
    have hpositive :
        0 < s * (s * 1 - 2 * (dx * ux + dy * uy)) := by
      apply mul_pos hspos
      linarith
    linarith
  · intro hs
    apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hspos)
    linarith

/-- A strict projection bound gives strict entry into the descent disc. -/
theorem ray_mem_descentDisc_of_lt_projection
    {dx dy ux uy s : ℝ}
    (hunit : ux ^ 2 + uy ^ 2 = 1)
    (hspos : 0 < s)
    (hsprojection : s < 2 * (dx * ux + dy * uy)) :
    (s * ux - dx) ^ 2 + (s * uy - dy) ^ 2 < dx ^ 2 + dy ^ 2 := by
  have hinner :
      s * (ux ^ 2 + uy ^ 2) - 2 * (dx * ux + dy * uy) < 0 := by
    nlinarith [hunit]
  have hfactor :
      s * (s * (ux ^ 2 + uy ^ 2) - 2 * (dx * ux + dy * uy)) < 0 :=
    mul_neg_of_pos_of_neg hspos hinner
  nlinarith [descentDisc_ray_squaredDifference dx dy ux uy s]

/-- A three-contact coordinate balance has zero squared residual.  This is the
scalar kernel consumed after planar Carathéodory reduces the active set. -/
theorem threeContact_balance_residual
    {w₁ w₂ w₃ ax ay bx byCoord cx cy : ℝ}
    (hx : w₁ * ax + w₂ * bx + w₃ * cx = 0)
    (hy : w₁ * ay + w₂ * byCoord + w₃ * cy = 0) :
    (w₁ * ax + w₂ * bx + w₃ * cx) ^ 2 +
        (w₁ * ay + w₂ * byCoord + w₃ * cy) ^ 2 = 0 := by
  rw [hx, hy]
  norm_num

end ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity
