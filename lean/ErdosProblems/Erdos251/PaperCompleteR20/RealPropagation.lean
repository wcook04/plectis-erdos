import ErdosProblems.Erdos251.RealPrimeGapTail
import Mathlib

/-!
# Real integrality propagation for the Erdős 251 tail recurrence

This module supplies the exact real-valued propagation statement printed as
`long251:xr:propagate`.  It does not assume that the orbit is rational-valued.
-/

namespace ErdosProblems.Erdos251.PaperCompleteR20

/-- Integrality of one real tail shift is preserved at the next basepoint. -/
theorem realTailShift_integral_succ
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ)
    (hInt : RealIntegral (realTailShift T h N)) :
    RealIntegral (realTailShift T h (N + 1)) := by
  obtain ⟨z, hz⟩ := hInt
  refine ⟨2 * z - (g (N + h + 1) - g (N + 1)), ?_⟩
  rw [realTailShift_succ hrec h N, hz]
  push_cast
  ring

/-- Exact `long251:xr:propagate`: an integral fixed-length shift remains
integral at every later basepoint for an arbitrary real dyadic tail orbit. -/
theorem realTailShift_integral_add
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ)
    (hInt : RealIntegral (realTailShift T h N)) :
    ∀ k : ℕ, RealIntegral (realTailShift T h (N + k))
  | 0 => by simpa using hInt
  | k + 1 => by
      simpa only [Nat.add_assoc] using
        realTailShift_integral_succ hrec h (N + k)
          (realTailShift_integral_add hrec h N hInt k)

#print axioms realTailShift_integral_add

end ErdosProblems.Erdos251.PaperCompleteR20
