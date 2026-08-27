import Mathlib.Tactic

/-!
# Erdős #1041: scalar kernel for optimized first-merge Bergman selection

The analytic companion note proves that the first-merge cost decreases as the
regular level rises toward `min(beta₂,1)`.  This file checks the load-bearing
scalar sign and budget compositions.  The finite-Blaschke fibre identity,
Bergman geodesic estimate, and derivative formula remain in the ordinary
analytic proof.  No unrestricted Erdős theorem is asserted.

Consumes the scalar interfaces explained by
`ErdosProblems.Erdos1041.ExteriorBlaschkeFibreCapacityGap` and
`ErdosProblems.Erdos1041.ConnectedClusterBergman`; feeds the first-merge
sufficient regime for the Erdős 1041 target.
-/

namespace ErdosProblems.Erdos1041.FirstTwoCriticalOptimizedBergman

/-- Once the logarithmic barrier is below the rational derivative barrier,
the degree-`n` derivative bracket is strictly negative for `n>2`. -/
theorem derivativeBracket_neg
    {n logBarrier rationalBarrier : ℝ}
    (hn : 2 < n) (hlog : 0 < logBarrier)
    (hbarrier : logBarrier < rationalBarrier) :
    (2 / n) * logBarrier - rationalBarrier < 0 := by
  have hn0 : 0 < n := by linarith
  have hratio : 2 / n < 1 := (div_lt_one hn0).2 hn
  have hscaled : (2 / n) * logBarrier < logBarrier := by
    nlinarith
  linarith

/-- The connected-cluster bound has a factor `2`; a cost below `2` therefore
gives squared length below `4`. -/
theorem lengthSq_lt_four_of_cost_lt_two
    {areaScale logBarrier : ℝ}
    (hcost : areaScale * logBarrier < 2) :
    2 * areaScale * logBarrier < 4 := by
  nlinarith

/-- The optimized target-level cost strictly improves a returned cost bounded
by `2*R^2`; open-disc scaling has `R^2<1`. -/
theorem optimizedCost_lt_two_of_returnedBudget
    {optimizedCost returnedCost radiusSq : ℝ}
    (himprove : optimizedCost < returnedCost)
    (hreturned : returnedCost <= 2 * radiusSq)
    (hradius : radiusSq < 1) :
    optimizedCost < 2 := by
  linarith

/-- The exact first-merge component constant for `k=2` is `1/(n-1)`;
Lean's totalized division also makes the identity valid at `n=1`. -/
theorem twoRootFibreConstant {n : ℝ} :
    2 / (2 * n - 2) = 1 / (n - 1) := by
  field_simp

end ErdosProblems.Erdos1041.FirstTwoCriticalOptimizedBergman
