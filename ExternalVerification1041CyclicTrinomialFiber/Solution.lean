import Mathlib
import ErdosProblems.Erdos1041.CyclicTrinomialFiberCase

namespace Erdos249257.ExternalVerification1041CyclicTrinomialFiber

theorem trinomialRoot_spoke_factorization
    {m r : ℕ} {a c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c =
      ((1 - u ^ r : ℝ) : ℂ) * c -
        ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m :=
  ErdosProblems.Erdos1041.trinomialRoot_spoke_factorization hroot

theorem trinomialRoot_spoke_norm_lt_one_of_norm_lt_one
    {m r : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m) {a c w : ℂ}
    (hroot : w ^ m + a * w ^ r + c = 0)
    (hw : ‖w‖ < 1) (hc : ‖c‖ < 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c‖ < 1 :=
  ErdosProblems.Erdos1041.trinomialRoot_spoke_norm_lt_one_of_norm_lt_one
    hr hrm hroot hw hc hu0 hu1

theorem cyclicTrinomial_two_short_fiber_displacements {y₁ y₂ : ℂ}
    (hy₁ : ‖y₁‖ < 1) (hy₂ : ‖y₂‖ < 1) :
    ‖y₁‖ + ‖y₂‖ < 2 :=
  ErdosProblems.Erdos1041.cyclicTrinomial_two_short_fiber_displacements hy₁ hy₂

end Erdos249257.ExternalVerification1041CyclicTrinomialFiber
