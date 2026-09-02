import ErdosProblems.Erdos1041.CriticalTwoRootProximity

/-!
# Erdős 1041: strict critical budget with an explicit slack certificate

This module consumes
`exists_two_roots_dist_sum_le_two_mul_geomMean` rather than reproving its
weaker unnormalised consequence.  If the geometric mean `r` of the root
distances at a non-root critical point is strictly below one, the selected pair
has total hub distance strictly below two.  The same proof records the usable
margin `2 * (1 - r)`.

This is a metric statement only.  It does not assert that either straight arm
or any connector of the same length lies in the unit lemniscate.
-/

namespace ErdosProblems.Erdos1041

open Finset in
/-- A critical value of geometric-mean modulus `r < 1` supplies two distinct
roots with strict total distance below `2`, together with the quantitative
slack inherited from the sharper `2*r` budget.

Consumes `exists_two_roots_dist_sum_le_two_mul_geomMean`.  The remaining
Erdős 1041 consumer must still produce lemniscate containment. -/
theorem exists_two_roots_dist_sum_lt_two_with_geomMean_slack
    {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℂ) (c : ℂ)
    (hne : ∀ k, c - z k ≠ 0)
    (hcrit : ∑ k, (c - z k)⁻¹ = 0)
    {r : ℝ} (hr : 0 < r) (hrlt : r < 1)
    (hrn : r ^ n = ∏ k, ‖c - z k‖) :
    ∃ i j : Fin n, i ≠ j ∧
      ‖c - z i‖ + ‖c - z j‖ < 2 ∧
      2 * (1 - r) ≤ 2 - (‖c - z i‖ + ‖c - z j‖) := by
  obtain ⟨i, j, hij, hbudget⟩ :=
    exists_two_roots_dist_sum_le_two_mul_geomMean hn z c hne hcrit hr hrn
  refine ⟨i, j, hij, lt_of_le_of_lt hbudget ?_, ?_⟩
  · linarith
  · linarith

end ErdosProblems.Erdos1041
