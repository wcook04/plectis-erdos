import Mathlib.Tactic

/-!
# Erdős #1041: algebraic kernels for the barycentric envelope

The companion note proves an exact union-of-discs representation of a
polynomial lemniscate and composes it with the existing sharp nearest-two-root
ellipse theorem at a critical point.  This file formalizes the completed-square
identity behind the new inverse-square descent disc and two elementary
downstream consumers of the already-landed two-radius budget.

It also checks the scalar variance factor and inequality transport used by the
linear-simplex arm certificate in `CriticalEllipseFreeHubLab.md`.

The weighted AM--GM and general one-variable monotonicity arguments remain in
the ordinary proof.  The full critical ellipse is already formalized as
`exists_two_roots_dist_sum_le_two_mul_geomMean` in
`CriticalTwoRootProximity.lean`; it is not re-claimed here.  This module does
not assert the unrestricted Erdős theorem.
-/

namespace ErdosProblems.Erdos1041.BarycentricEnvelope

/-- Real-coordinate form of the completed square in the descent-disc proof. -/
theorem inverseSquare_completedSquare
    {S hRe hIm pRe pIm : ℝ} (hS : S ≠ 0) :
    S * ((hRe - pRe / S) ^ 2 + (hIm - pIm / S) ^ 2) =
      S * (hRe ^ 2 + hIm ^ 2) - 2 * (hRe * pRe + hIm * pIm) +
        (pRe ^ 2 + pIm ^ 2) / S := by
  field_simp
  ring

/-- If both nearest radii are no larger than their geometric-mean scale, the
sharp `2*rho` ellipse budget is immediate. -/
theorem nearestTwo_sum_le_of_second_le_scale
    {r₁ r₂ rho : ℝ}
    (hr₁₂ : r₁ ≤ r₂) (hr₂rho : r₂ ≤ rho) :
    r₁ + r₂ ≤ 2 * rho := by
  linarith

/-- The spoke consumer once containment and the sharp radius budget are known. -/
theorem twoSpoke_length_le_two_mul_scale
    {r₁ r₂ rho scale : ℝ}
    (hradii : r₁ + r₂ ≤ 2 * rho)
    (hrho : rho ≤ scale) :
    r₁ + r₂ ≤ 2 * scale := by
  linarith

/-- Scalar factor in the variance formula for mixing a distribution with one
root vertex.  The geometric variance identity supplies the left side. -/
theorem linearMixture_variance_factor {s variance distance : ℝ} :
    (1 - s) * variance + s * (1 - s) * distance ^ 2 =
      (1 - s) * (variance + s * distance ^ 2) := by
  ring

/-- Once the divided linear-arm certificate is known, multiplication by its
nonnegative interpolation factor recovers the disc-radius inequality. -/
theorem linearArm_certificate_transport
    {s variance distance scale factor : ℝ}
    (hs : s ≤ 1)
    (hcertificate : variance + s * distance ^ 2 ≤ scale * factor) :
    (1 - s) * (variance + s * distance ^ 2) ≤
      (1 - s) * (scale * factor) := by
  exact mul_le_mul_of_nonneg_left hcertificate (sub_nonneg.mpr hs)

end ErdosProblems.Erdos1041.BarycentricEnvelope
