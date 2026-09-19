import Mathlib

/-!
# Elementary signed bounds used by the round-8 candidates

These constructor proofs avoid depending on the explicit/implicit argument
conventions of the core integer absolute-value lemmas. Uncompiled.
-/
namespace ErdosProblems.Erdos243.PaperCompleteR8

theorem integer_abs_bounds (z : ℤ) :
    -(z.natAbs : ℤ) ≤ z ∧ z ≤ (z.natAbs : ℤ) := by
  cases z with
  | ofNat n =>
      change -(n : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) ≤ (n : ℤ)
      exact ⟨by omega, le_rfl⟩
  | negSucc n =>
      change -((n + 1 : ℕ) : ℤ) ≤ -((n + 1 : ℕ) : ℤ) ∧
        -((n + 1 : ℕ) : ℤ) ≤ ((n + 1 : ℕ) : ℤ)
      exact ⟨le_rfl, by omega⟩

end ErdosProblems.Erdos243.PaperCompleteR8
