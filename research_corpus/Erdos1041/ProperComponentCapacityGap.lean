import Mathlib.Tactic

/-!
# Erdős #1041: scalar kernel for the proper-component capacity gap

The analytic companion note obtains `(r+1)/(r-1) < n` by evaluating one
exterior Poisson kernel at its peak.  This file checks the exact algebra that
separates the corresponding exterior root from the unit circle.  The exterior
factorization, boundary orientation, capacity identity, and Pólya inequality
remain in the ordinary proof.  No unrestricted Erdős theorem is asserted.
-/

namespace ErdosProblems.Erdos1041.ProperComponentCapacityGap

/-- The peak value of an exterior Poisson factor. -/
theorem exterior_poisson_peak_identity {r : ℝ} (hr : r ≠ 1) :
    (r ^ 2 - 1) / (r - 1) ^ 2 = (r + 1) / (r - 1) := by
  have hden : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  field_simp [hden]
  ring

/-- Positivity of the exterior angular derivative forces the exact gap. -/
theorem exterior_radius_gt_degree_gap
    {n r : ℝ} (hn : 1 < n) (hr : 1 < r)
    (hpeak : (r + 1) / (r - 1) < n) :
    (n + 1) / (n - 1) < r := by
  have hrden : 0 < r - 1 := sub_pos.mpr hr
  have hnden : 0 < n - 1 := sub_pos.mpr hn
  rw [div_lt_iff₀ hrden] at hpeak
  rw [div_lt_iff₀ hnden]
  nlinarith

/-- The normalized gap `q_n=(n-1)/(n+1)` lies strictly between zero and one. -/
theorem degree_gap_mem_unit_interval {n : ℝ} (hn : 1 < n) :
    0 < (n - 1) / (n + 1) ∧ (n - 1) / (n + 1) < 1 := by
  have hnum : 0 < n - 1 := by linarith
  have hden : 0 < n + 1 := by linarith
  constructor
  · exact div_pos hnum hden
  · apply (div_lt_one hden).2
    linarith

end ErdosProblems.Erdos1041.ProperComponentCapacityGap
