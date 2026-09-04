import Mathlib
import ErdosProblems.Erdos249.CyclotomicAnchoredKill

namespace Erdos249257.ExternalVerification249CanonicalMersenneFrontier

open scoped BigOperators

def deltaTotient (h n : ℕ) : ℤ :=
  (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)

def totientBlock (H N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range H,
    (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)

def fullMersenneBlockResidue (H N M : ℕ) : ℤ :=
  (-totientBlock H N) % (M : ℤ)

def FullMersenneCenteredResidueGap (H N M : ℕ) : Prop :=
  let B : ℤ := N + H + 1
  B < fullMersenneBlockResidue H N M ∧
    fullMersenneBlockResidue H N M < (M : ℤ) - B

def FullMersenneCenteredResidueGapSupply : Prop :=
  ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v →
    ∀ N₀ : ℕ, ∃ H N M : ℕ,
      0 < H ∧ Nat.totient v ∣ H ∧ max c N₀ ≤ N ∧
      v * M = 2 ^ H - 1 ∧ FullMersenneCenteredResidueGap H N M

def FullMersenneCanonicalBasepointResidueGapSupply : Prop :=
  ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v →
    ∃ H M : ℕ,
      0 < H ∧ Nat.totient v ∣ H ∧ v * M = 2 ^ H - 1 ∧
      FullMersenneCenteredResidueGap H c M

theorem fullMersenneBlockResidue_succ
    {H N M : ℕ} (hM : M ∣ 2 ^ H - 1) :
    fullMersenneBlockResidue H (N + 1) M =
      (2 * fullMersenneBlockResidue H N M -
        deltaTotient H (N + 1)) % (M : ℤ) := by
  simpa [fullMersenneBlockResidue, totientBlock, deltaTotient,
    ErdosProblems.Erdos249.fullMersenneBlockResidue,
    ErdosProblems.Erdos249.totientBlock,
    Erdos257PeriodNoncollapse.deltaTotient] using
    ErdosProblems.Erdos249.fullMersenneBlockResidue_succ hM

theorem fullMersenneCenteredResidueGapSupply_of_canonicalBasepoint
    (hsupply : FullMersenneCanonicalBasepointResidueGapSupply) :
    FullMersenneCenteredResidueGapSupply := by
  simpa [FullMersenneCanonicalBasepointResidueGapSupply,
    FullMersenneCenteredResidueGapSupply,
    FullMersenneCenteredResidueGap, fullMersenneBlockResidue, totientBlock,
    ErdosProblems.Erdos249.FullMersenneCanonicalBasepointResidueGapSupply,
    ErdosProblems.Erdos249.FullMersenneCenteredResidueGapSupply,
    ErdosProblems.Erdos249.FullMersenneCenteredResidueGap,
    ErdosProblems.Erdos249.fullMersenneBlockResidue,
    ErdosProblems.Erdos249.totientBlock] using
    ErdosProblems.Erdos249.fullMersenneCenteredResidueGapSupply_of_canonicalBasepoint
      hsupply

theorem fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational :
    FullMersenneCanonicalBasepointResidueGapSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  simpa [FullMersenneCanonicalBasepointResidueGapSupply,
    FullMersenneCenteredResidueGap, fullMersenneBlockResidue, totientBlock,
    ErdosProblems.Erdos249.FullMersenneCanonicalBasepointResidueGapSupply,
    ErdosProblems.Erdos249.FullMersenneCenteredResidueGap,
    ErdosProblems.Erdos249.fullMersenneBlockResidue,
    ErdosProblems.Erdos249.totientBlock] using
    ErdosProblems.Erdos249.fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational

end Erdos249257.ExternalVerification249CanonicalMersenneFrontier
