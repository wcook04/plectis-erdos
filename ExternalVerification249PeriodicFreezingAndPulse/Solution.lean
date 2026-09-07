/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.PaperCompleteR7.PeriodicAndPulse

/-!
# Source transport: coefficient freezing and the bounded isolated pulse

Both declarations transport the live source theorems without strengthening a
hypothesis or weakening a conclusion. The statements are token-identical to
the trusted challenge.
-/

namespace Erdos249257.ExternalVerification249PeriodicFreezingAndPulse

theorem periodic_freezing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i)
    (w : ι → ℕ → ℚ)
    (hperiodic : ∀ i, ∃ q : ℕ, 0 < q ∧ ∀ n, w i (n + q) = w i n)
    (hrel : ∃ N₀, ∀ n, N₀ ≤ n →
      ∑ i, w i n * (Nat.totient (a i * n + b i) : ℚ) = 0) :
    ∀ i n, w i n = 0 :=
  ErdosProblems.Erdos249.PaperCompleteR7.periodic_freezing
    a b ha hcross w hperiodic hrel

theorem bounded_isolated_pulse
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L₀ : ℕ, ∃ L N : ℕ, L₀ ≤ L ∧ L < N ∧ a N ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (N - j) = 0 ∧ a (N + j) = 0) :
    Irrational (∑' n : ℕ, (a (n + 1) : ℝ) / 2 ^ (n + 1)) :=
  ErdosProblems.Erdos249.PaperCompleteR7.bounded_isolated_pulse a C hC hpulse

end Erdos249257.ExternalVerification249PeriodicFreezingAndPulse
