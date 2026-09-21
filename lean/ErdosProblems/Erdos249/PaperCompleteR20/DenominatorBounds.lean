import Erdos249257.MersenneShadowDenominatorGrowth

namespace ErdosProblems.Erdos249.PaperCompleteR20
open Erdos249257
open MersenneShadowCyclotomicNoncollapse MersenneShadowDenominatorGrowth
open scoped BigOperators

/-- Both inequalities of the long paper, for the finite rational shadow.
No conclusion about cancellation in a real tail is asserted. -/
theorem upper_half_product_denominator_bounds {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤ (∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p) ∧
    (∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p) ≤
      ((lcmHeight t : ℚ) * RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den := by
  exact ⟨upperHalfMersenneProduct_lower_bound ht,
    Nat.le_of_dvd (Rat.pos _) (lcmHeight_upperHalf_product_dvd_den ht)⟩

#print axioms upper_half_product_denominator_bounds
end ErdosProblems.Erdos249.PaperCompleteR20
