import Erdos249257.CertificateKernel

/-!
# Periodic supports whose periodicity starts at the first positive exponent

For `b ≥ 2`, `m ≥ 1` and a support `A` with a positive member and
`n + m ∈ A ↔ n ∈ A` for every positive `n`, the series
`∑_{a ∈ A} 1/(b^a - 1)` is irrational
(`irrational_erdosSupportSeries_positivePeriodic`).  This is Theorem
`thm:periodic-support` of the #257 long record, whose hypotheses concern
positive indices only.

`Erdos249257.irrational_erdosSupportSeries_periodic` assumes the equivalence for
every `n`, including `n = 0`, where it reads `m ∈ A ↔ 0 ∈ A`; a positive support
containing `m` satisfies that only after `0` is added to it.  Here an arithmetic
progression inside `A` shows that `A` is infinite, and the eventually-periodic
theorem then applies with threshold one.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR20

open Erdos249257

/-- A support with a positive member and a positive period on positive indices
contains an infinite arithmetic progression, whatever its membership at zero. -/
theorem infinite_of_positive_periodic_support (m : ℕ) (A : Set ℕ)
    (hm : 0 < m)
    (hper : ∀ n : ℕ, 0 < n → (n + m ∈ A ↔ n ∈ A))
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) : A.Infinite := by
  obtain ⟨a, ha, haA⟩ := hpos
  have hseq : ∀ k : ℕ, a + k * m ∈ A := by
    intro k
    induction k with
    | zero => simpa using haA
    | succ k ih =>
        have hstep := (hper (a + k * m) (by omega)).mpr ih
        simpa [Nat.add_mul, Nat.add_assoc] using hstep
  have hinj : Function.Injective (fun k : ℕ => a + k * m) := by
    intro i j hij
    exact mul_right_cancel₀ hm.ne' (Nat.add_left_cancel hij)
  exact (Set.infinite_range_of_injective hinj).mono (by
    rintro n ⟨k, rfl⟩
    exact hseq k)

/-- **`thm:periodic-support`** (#257 long record).  For `b ≥ 2`, `m ≥ 1` and a
support `A` with a positive member and `n + m ∈ A ↔ n ∈ A` for every positive
`n`, the series `∑_{a ∈ A} 1/(b^a - 1)` is irrational.  The hypotheses concern
positive indices only, and the infinitude of `A` is derived. -/
theorem irrational_erdosSupportSeries_positivePeriodic
    (b m : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, 0 < n → (n + m ∈ A ↔ n ∈ A))
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    Irrational (erdosSupportSeries b A) := by
  exact irrational_erdosSupportSeries_eventuallyPeriodic b m 1 A hb hm
    (fun n hn => hper n hn) (infinite_of_positive_periodic_support m A hm hper hpos)

#print axioms irrational_erdosSupportSeries_positivePeriodic

end ErdosProblems.Erdos257.PaperCompleteR20
