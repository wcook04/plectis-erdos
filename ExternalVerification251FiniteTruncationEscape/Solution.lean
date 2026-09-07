/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperTailBoundsR7

/-!
# Source transport for the finite-truncation escape criterion in Erdős #251

Every definition below unfolds to the corresponding source definition, so the
two compared theorems are transports of
`ErdosProblems.Erdos251.PaperR7.cofinal_escape_of_finite_truncation` and
`ErdosProblems.Erdos251.PaperR7.irrational_prime_series_of_finite_truncation`.
-/

open ErdosProblems.Erdos251
open ErdosProblems.Erdos251.PaperR7

namespace Erdos249257.ExternalVerification251FiniteTruncationEscape

noncomputable def gap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

noncomputable def tail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (gap (N + j + 1) : ℝ) / 2 ^ (j + 1)

noncomputable def shift (h N : ℕ) : ℝ :=
  tail (N + h) - tail N

def IsIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z

noncomputable def window (h N L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L,
    ((gap (N + h + j + 1) : ℝ) - gap (N + j + 1)) / 2 ^ (j + 1)

noncomputable def remainderTerm (M : ℕ → ℝ) (h N L j : ℕ) : ℝ :=
  (M (N + h + L + j + 1) + M (N + L + j + 1)) / 2 ^ (L + j + 1)

noncomputable def remainder (M : ℕ → ℝ) (h N L : ℕ) : ℝ :=
  ∑' j : ℕ, remainderTerm M h N L j

noncomputable def intDist (x : ℝ) : ℝ :=
  Metric.infDist x (Set.range (fun z : ℤ => (z : ℝ)))

theorem gap_eq (n : ℕ) : gap n = primeGap0 n := rfl

theorem tail_eq (N : ℕ) : tail N = realPrimeGapTail N := by
  rw [realPrimeGapTail_eq_tsum_shifted_gaps]
  rfl

theorem shift_eq (h N : ℕ) : shift h N = realTailShift realPrimeGapTail h N := by
  rw [shift, realTailShift, tail_eq, tail_eq]

theorem window_eq (h N L : ℕ) : window h N L = signedWindow h N L := rfl

theorem remainderTerm_eq (M : ℕ → ℝ) (h N L : ℕ) :
    remainderTerm M h N L = majorantRemainderTerm M h N L := rfl

theorem remainder_eq (M : ℕ → ℝ) (h N L : ℕ) :
    remainder M h N L = majorantRemainder M h N L := rfl

theorem intDist_eq (x : ℝ) : intDist x = integerDistance x := rfl

theorem cofinal_escape_of_finite_truncation (M : ℕ → ℝ)
    (hM : ∀ n, (gap n : ℝ) ≤ M n)
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N L : ℕ,
      N₀ ≤ N ∧ 1 ≤ L ∧ Summable (remainderTerm M h N L) ∧
      remainder M h N L < intDist (window h N L)) :
    ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ ¬ IsIntegral (shift h N) := by
  have hsource : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ¬ RealIntegral (realTailShift realPrimeGapTail h N) :=
    PaperR7.cofinal_escape_of_finite_truncation M hM hsupply
  intro h hh N₀
  obtain ⟨N, hN, hnot⟩ := hsource h hh N₀
  refine ⟨N, hN, ?_⟩
  rw [shift_eq]
  exact hnot

theorem irrational_prime_series_of_finite_truncation (M : ℕ → ℝ)
    (hM : ∀ n, (gap n : ℝ) ≤ M n)
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N L : ℕ,
      N₀ ≤ N ∧ 1 ≤ L ∧ Summable (remainderTerm M h N L) ∧
      remainder M h N L < intDist (window h N L)) :
    Irrational (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) / 2 ^ (n + 1)) :=
  PaperR7.irrational_prime_series_of_finite_truncation M hM hsupply

end Erdos249257.ExternalVerification251FiniteTruncationEscape
