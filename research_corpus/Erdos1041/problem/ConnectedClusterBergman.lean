import Mathlib.Tactic

/-!
# Erdős #1041: scalar kernel for the connected-cluster Bergman certificate

The companion analytic proof uses Riemann--Hurwitz to show that the critical
sublevel of a degree-`k` Blaschke product is connected.  Covering it by
pseudohyperbolic discs of radius `r = q^(1/k)` gives two distinct zero locations
at distance at most `2*r/(1+r^2)`.  This file formalizes the exact defect
identity behind that conversion and the final certificate-to-length step.

The uniformization, connectedness, disc-intersection graph, and Bergman kernel
arguments remain in the ordinary proof.  No unrestricted Erdős theorem is
asserted here.
-/

namespace ErdosProblems.Erdos1041.ConnectedClusterBergman

/-- Exact complement of the pseudohyperbolic overlap bound. -/
theorem overlap_defect_identity {r : ℝ} (hden : 1 + r ^ 2 ≠ 0) :
    1 - (2 * r / (1 + r ^ 2)) ^ 2 =
      ((1 - r ^ 2) / (1 + r ^ 2)) ^ 2 := by
  field_simp
  ring

/-- The final scalar step in the connected-cluster certificate. -/
theorem length_le_two_of_cluster_certificate
    {length areaFactor logarithmicFactor : ℝ}
    (hgeodesic : length ^ 2 ≤ 2 * areaFactor * logarithmicFactor)
    (hcertificate : areaFactor * logarithmicFactor ≤ 2) :
    length ≤ 2 := by
  have hsquare : length ^ 2 ≤ 4 := by nlinarith
  nlinarith [sq_nonneg (length - 2)]

/-- Scaled form used at level `t`: divide length by `t^(1/n)` first. -/
theorem length_le_two_mul_scale_of_normalized_certificate
    {length scale areaFactor logarithmicFactor : ℝ}
    (hscale : 0 < scale)
    (hlength : 0 ≤ length)
    (hgeodesic : (length / scale) ^ 2 ≤
      2 * areaFactor * logarithmicFactor)
    (hcertificate : areaFactor * logarithmicFactor ≤ 2) :
    length ≤ 2 * scale := by
  have hnorm : 0 ≤ length / scale := div_nonneg hlength (le_of_lt hscale)
  have hnormle : length / scale ≤ 2 :=
    length_le_two_of_cluster_certificate hgeodesic hcertificate
  exact (div_le_iff₀ hscale).mp (by simpa [mul_comm] using hnormle)

end ErdosProblems.Erdos1041.ConnectedClusterBergman
