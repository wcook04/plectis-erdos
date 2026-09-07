/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge: coefficient freezing and the bounded isolated pulse

Two statements from the binary totient note for Erdős #249.

`periodic_freezing` is the rigidity statement for the totient kernel: a
rational relation among sections `n ↦ φ (a i * n + b i)` of pairwise
nonproportional positive-slope affine forms, with coefficients that are
eventually periodic in `n` and each carrying its own positive period, forces
every coefficient to vanish identically. The relation is assumed only for all
sufficiently large `n`.

`bounded_isolated_pulse` is the Diophantine criterion in the shape used by the
note: a bounded integer sequence carrying, above every height, a nonzero
letter flanked by a block of zeros on both sides has irrational binary value
`∑_{n ≥ 1} a n / 2 ^ n`.

Neither statement concerns `∑_{n ≥ 1} φ n / 2 ^ n`, and neither settles
Erdős Problem 249, which remains open.
-/

namespace Erdos249257.ExternalVerification249PeriodicFreezingAndPulse

/-- **Freezing periodic coefficients.** Pairwise nonproportional positive-slope
affine forms admit no nontrivial eventual relation with periodic rational
coefficients. -/
theorem periodic_freezing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i)
    (w : ι → ℕ → ℚ)
    (hperiodic : ∀ i, ∃ q : ℕ, 0 < q ∧ ∀ n, w i (n + q) = w i n)
    (hrel : ∃ N₀, ∀ n, N₀ ≤ n →
      ∑ i, w i n * (Nat.totient (a i * n + b i) : ℚ) = 0) :
    ∀ i n, w i n = 0 := by
  sorry

/-- **A bounded isolated pulse.** Cofinally many two-sided isolated nonzero
letters in a bounded integer sequence force irrationality of its binary value
over the positive indices. -/
theorem bounded_isolated_pulse
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L₀ : ℕ, ∃ L N : ℕ, L₀ ≤ L ∧ L < N ∧ a N ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (N - j) = 0 ∧ a (N + j) = 0) :
    Irrational (∑' n : ℕ, (a (n + 1) : ℝ) / 2 ^ (n + 1)) := by
  sorry

end Erdos249257.ExternalVerification249PeriodicFreezingAndPulse
