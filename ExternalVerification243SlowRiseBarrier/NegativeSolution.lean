/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Deliberately incomplete result for the #243 slow-rise package

This same-named declaration retains the full hypothesis list but replaces the
contradiction with the unrelated, strictly weaker claim that the numerator
vanishes at the block index. Comparator must reject this as a type mismatch
against `Challenge.lean`.
-/
namespace Erdos249257.ExternalVerification243SlowRiseBarrier

theorem no_slowRise_reducedTail
    (a u v : ℕ → ℕ) (N B : ℕ)
    (ha : ∀ n, N ≤ n → 1 < a n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hu : ∀ n, N ≤ n → u (n + 1) + v n = a n * u n)
    (hv : ∀ n, N ≤ n → v (n + 1) = a n * v n)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop)
    (hstart : u (N + B) < ∏ i : Fin B, a (N + i.1))
    (hrise : ∀ n, N + B ≤ n → u n < 2 * ∏ i : Fin B, a (N + i.1) →
      u (n + 1) ≤ u n + B) :
    u (N + B) = 0 := by
  sorry

end Erdos249257.ExternalVerification243SlowRiseBarrier
