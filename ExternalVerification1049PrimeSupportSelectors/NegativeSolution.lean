/- Deliberate mismatch: only the weakest finite collision interface is supplied. -/
import Mathlib

namespace Erdos249257.ExternalVerification1049PrimeSupportSelectors

theorem zeroDenominatorCoordinates_binaryCollision
    {N k : ℕ} [NeZero N]
    (w : Fin k → ZMod N × ZMod N)
    (hzero : ∀ i, (w i).2 = 0)
    (hcard : N < 2 ^ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  sorry

end Erdos249257.ExternalVerification1049PrimeSupportSelectors
