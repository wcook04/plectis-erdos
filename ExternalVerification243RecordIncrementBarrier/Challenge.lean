/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for true-record-increment rigidity in Erdős #243

The theorem is the true-record-increment consequence of the weighted-record
octuple's `r01` return: under a division-free cocycle with arbitrary
cancellation, a nearest-integer centring bound, division-free normalized
vanishing, a unit bound on the growth of the running maximum of the
primitive numerator, and a fresh large prime-power supply recurring at
arbitrarily late indices, the multipliers eventually satisfy the exact
Sylvester recurrence.

The theorem is conditional on its explicit hypotheses, in particular the
unit-increment bound `hinc` and the prime-power supply `hsupply`, neither of
which is derived from the underlying dynamics here. It does not show that
every orbit in Erdős #243 satisfies them, and the unrestricted problem
remains open.
-/

namespace Erdos249257.ExternalVerification243RecordIncrementBarrier

/-- The Sylvester successor map. -/
def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

/-- The running maximum of a natural-valued sequence. -/
def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

/-- **True-record-increment rigidity, conditional on the fresh prime-power
supply.** Along a dynamically reduced primitive reciprocal tail with
arbitrary cancellation, if the nearest-integer normalisation holds
eventually, the normalised error vanishes, the running maximum increases by
at most one at every late step, and fresh prime powers recur at arbitrarily
late indices dominating the current record, then the multipliers eventually
satisfy the exact Sylvester recurrence. -/
theorem recordIncrementOne_sylvesterNext_eventually
    (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (N : ℕ)
    (hvpos : ∀ n, N ≤ n → 0 < v n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hw : ∀ n, N ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, N ≤ n → 0 < w n)
    (hnum : ∀ n, N ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, N ≤ n → a n * v n = hc n * v (n + 1))
    (he : ∀ n, N ≤ n → e n = (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ))
    (hcentre : ∀ n, N ≤ n → 2 * (e n).natAbs < u n)
    (hvanish : ∀ K, ∃ M, ∀ n, M ≤ n → K * (e n).natAbs < u n)
    (hinc : ∀ n, N ≤ n → runningMax u (n + 1) ≤ runningMax u n + 1)
    (hsupply : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ 1 ≤ l ∧
      p ^ l ∣ v s ∧ runningMax u s + 3 ≤ p ^ l) :
    ∃ M, ∀ n, M ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry

end Erdos249257.ExternalVerification243RecordIncrementBarrier
