import Mathlib
namespace Erdos249257.ExternalVerification249CanonicalMersenneFrontier
open scoped BigOperators
def totientBlock (H N : ℕ) : ℤ := ∑ j ∈ Finset.range H, (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)
def fullMersenneBlockResidue (H N M : ℕ) : ℤ := (-totientBlock H N) % (M : ℤ)
def FullMersenneCenteredResidueGap (H N M : ℕ) : Prop := let B : ℤ := N + H + 1; B < fullMersenneBlockResidue H N M ∧ fullMersenneBlockResidue H N M < (M : ℤ) - B
def FullMersenneCanonicalBasepointResidueGapSupply : Prop := ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v → ∃ H M : ℕ, 0 < H ∧ Nat.totient v ∣ H ∧ v * M = 2 ^ H - 1 ∧ FullMersenneCenteredResidueGap H c M
theorem fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational (_extra : True) : FullMersenneCanonicalBasepointResidueGapSupply ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by sorry
end Erdos249257.ExternalVerification249CanonicalMersenneFrontier
