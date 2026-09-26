import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The finite-prime weighted support criterion

These are the canonical definitions used by the analytic support theorem.
Their small import boundary also permits arithmetic constructions to use
the same weights without importing the displacement proof.
-/

noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR7

/-- The full prime-power part determined by a finite set of primes. -/
def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p

/-- The literal weighted term at an integer base. -/
def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))

/-- The weighted hypothesis, not its irrationality conclusion. -/
def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (primeWeightedTerm b P))

end ErdosProblems.Erdos257.PaperCompleteR7
end
