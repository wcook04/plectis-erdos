import Erdos249257.TotientParityCoboundaryCountermodel

/-! The coefficient properties of the rational example (`prop:b7` of the long
#249 manuscript).  The rational comparison sequence of `prop:parity` is
uniformly bounded, satisfies `c(n) ≤ n`, agrees with `φ(n)` modulo `2` at
every index, and carries the stated separated-carry form of aperiodicity, and
its dyadic series is rational.  Hence those four properties alone cannot imply
irrationality of a dyadic series. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open Erdos249257.TotientParityCoboundaryCountermodel

/-- The four asserted coefficient properties of a sequence `c : ℕ → ℕ`:
uniform boundedness, `c(n) ≤ n`, parity agreement with `φ` at every index,
and the separated-carry form of aperiodicity together with genuine
non-eventual-periodicity. -/
def ParityComparisonProperties (c : ℕ → ℕ) : Prop :=
  (∀ n, c n ≤ 6) ∧ (∀ n, c n ≤ n) ∧ (∀ n, c n % 2 = Nat.totient n % 2) ∧
    (∀ N G K : ℕ, ∃ k : ℕ, N < 2 ^ (k + 3) ∧
      ∀ i : ℕ, i < K →
        2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
        c (2 ^ (k + i + 3)) = 6 ∧ c (2 ^ (k + i + 3) + 1) = 0) ∧
    (¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → c (n + p) = c n)

/-- **The rational example has all four properties** (`prop:b7`, first
sentence). -/
theorem exists_rational_parityComparison :
    ∃ c : ℕ → ℕ, ParityComparisonProperties c ∧
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n) := by
  obtain ⟨c, hcarry, hsix, hself, hpar, hper, hrat⟩ :=
    exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel
  exact ⟨c, ⟨hsix, hself, hpar, hcarry, hper⟩, hrat⟩

/-- **Consequently those properties alone cannot imply irrationality**
(`prop:b7`, second sentence). -/
theorem parityComparisonProperties_do_not_imply_irrational :
    ¬ ∀ c : ℕ → ℕ, ParityComparisonProperties c →
        Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n) := by
  intro h
  obtain ⟨c, hprops, hrat⟩ := exists_rational_parityComparison
  exact hrat (h c hprops)

#print axioms exists_rational_parityComparison
#print axioms parityComparisonProperties_do_not_imply_irrational
end ErdosProblems.Erdos249.PaperCompleteR21
