import Mathlib
namespace Erdos249257.ExternalVerification249FullDepthRayAmplifier
open scoped BigOperators
def windowDiscrepancy (h N L : ℕ) : ℤ := ∑ j ∈ Finset.range L, ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
def certifiedKill (h N L : ℕ) : Prop := (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧ windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
def ApFullDepthEscape : Prop := ∀ d : ℕ, 0 < d → ∀ N : ℕ, ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)
theorem apFullDepthEscape_iff_irrational (_extra : True) : ApFullDepthEscape ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by sorry
end Erdos249257.ExternalVerification249FullDepthRayAmplifier
