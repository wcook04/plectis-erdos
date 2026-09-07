import Mathlib
namespace Erdos249257.ExternalVerification1041CyclicTrinomialFiber
theorem trinomialRoot_spoke_factorization
    (_extra : True) {m r : ℕ} {a c w : ℂ} {u : ℝ}
    (hroot : w ^ m + a * w ^ r + c = 0) :
    (u : ℂ) ^ m * w ^ m + a * (u : ℂ) ^ r * w ^ r + c =
      ((1 - u ^ r : ℝ) : ℂ) * c -
        ((u ^ r - u ^ m : ℝ) : ℂ) * w ^ m := by sorry
end Erdos249257.ExternalVerification1041CyclicTrinomialFiber
