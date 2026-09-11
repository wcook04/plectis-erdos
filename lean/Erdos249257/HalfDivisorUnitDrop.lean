import Erdos249257.HalfCarrySelectedWindow

/-!
# Literal half-divisor bit gives the seam's unit coefficient drop

This is the smallest object-level producer for the residual
`RewindBaseUnitDropAt`: two adjacent ancestor words which share a parent and
take opposite terminal bits have next-double-row coefficients differing by
exactly one.
-/

namespace Erdos249257.HalfDivisorUnitDrop

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow

/-- At row `2(N+1)`, changing only exponent `N+1` from false to true adds
exactly the half-divisor incidence. -/
theorem supportCoeff_extend_true_eq_false_add_one_at_double
    {N : ℕ} (a : HalfWord N) :
    supportCoeff (wordSupport (extendHalfWord a true)) (2 * (N + 1)) =
      supportCoeff (wordSupport (extendHalfWord a false)) (2 * (N + 1)) + 1 := by
  rw [wordSupport_extendHalfWord, wordSupport_extendHalfWord]
  simp only [if_true]
  apply Erdos249257.HalfCylinderFiniteShadow.supportCoeff_insert_divisor
  · apply Nat.mem_divisors.mpr
    exact ⟨⟨2, by omega⟩, by omega⟩
  · intro hmem
    rcases hmem with ⟨hlt, -⟩
    omega

/-- Proof-irrelevant word equalities may be supplied by any concrete
adjacent-boundary construction. -/
theorem supportCoeff_boundaryPair_unitDrop_at_double
    {N : ℕ} (a : HalfWord N) (left right : HalfWord (N + 1))
    (hleft : left = extendHalfWord a true)
    (hright : right = extendHalfWord a false) :
    supportCoeff (wordSupport left) (2 * (N + 1)) =
      supportCoeff (wordSupport right) (2 * (N + 1)) + 1 := by
  rw [hleft, hright]
  exact supportCoeff_extend_true_eq_false_add_one_at_double a

#print axioms supportCoeff_extend_true_eq_false_add_one_at_double
#print axioms supportCoeff_boundaryPair_unitDrop_at_double

end Erdos249257.HalfDivisorUnitDrop
