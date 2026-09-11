import Erdos249257.BooleanMobiusCofinalExactRows

/-!
# A concrete seed for the exact Boolean--Möbius row producer

At endpoint six, the support `{2, 3, 6}` has quotient contributions
`21`, `9`, and `1`.  Their sum is `31 = 2^5 - 1`, giving the first explicit
exact local half row used by the extension lane.
-/

namespace Erdos249257

/-- The concrete support underlying the endpoint-six seed. -/
def exactRowSixSupport : Finset ℕ := {2, 3, 6}

theorem exactRowSixSupport_bounds :
    ∀ d ∈ exactRowSixSupport, 2 ≤ d ∧ d ≤ 6 := by
  intro d hd
  simp only [exactRowSixSupport, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl <;> omega

theorem exactRowSixSupport_quotient :
    localPrefixQuotient exactRowSixSupport 6 = 2 ^ (6 - 1) - 1 := by
  norm_num [exactRowSixSupport, localPrefixQuotient, localMersenneQuotient]

/-- The seed is on the strict below-half side, so it can enter the literal
row-doubling constructor. -/
theorem exactRowSixSupport_value_lt_half :
    localMersennePrefixValue exactRowSixSupport < (1 / 2 : ℚ) := by
  norm_num [exactRowSixSupport, localMersennePrefixValue, mersenneWeightRat]

/-- The support `{2, 3, 6}` is an exact local Mersenne half row at endpoint
six. -/
theorem exactLocalMersenneHalfRow_six : ExactLocalMersenneHalfRow 6 := by
  exact ⟨exactRowSixSupport, exactRowSixSupport_bounds,
    exactRowSixSupport_quotient⟩

end Erdos249257
