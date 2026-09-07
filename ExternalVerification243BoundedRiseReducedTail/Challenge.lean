/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for bounded-rise exclusion on the reduced tail in Erdős #243

The three endpoints expose the checked bounded-rise mechanism: a general
impossibility theorem for a natural state that rises slowly while permanently
avoiding an infinite pairwise-coprime modulus family, its specialisation to an
exact reduced tail, and the eventual form of that specialisation.

The statements use Mathlib vocabulary only.  The hypotheses are explicit.  The
exact reduced recurrence, the multiplier lower bound, the uniform rise bound
and the divergence of the numerator are assumed rather than produced, and the
unrestricted parent problem remains open.
-/

namespace Erdos249257.ExternalVerification243BoundedRiseReducedTail

/-- A sequence tending to infinity cannot have uniformly bounded upward
increments while permanently avoiding infinitely many fresh pairwise-coprime
moduli. -/
theorem no_boundedRise_of_tailAvoidance
    (u m : ℕ → ℕ) (N B : ℕ)
    (hB : 0 < B)
    (hm : ∀ n, N ≤ n → 1 < m n)
    (hpair : ∀ {i j : ℕ}, N ≤ i → N ≤ j → i ≠ j →
      Nat.Coprime (m i) (m j))
    (havoid : ∀ {i t : ℕ}, N ≤ i → i < t →
      Nat.Coprime (m i) (u t))
    (hrise : ∀ n, N ≤ n → u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  sorry

/-- There is no infinite reduced exact tail whose numerator tends to infinity
but has a uniformly bounded upward increment. -/
theorem no_boundedRise_reducedTail
    (a u v : ℕ → ℕ) (B : ℕ)
    (hB : 0 < B)
    (ha : ∀ n, 1 < a n)
    (hred : ∀ n, Nat.Coprime (u n) (v n))
    (hu : ∀ n, u (n + 1) + v n = a n * u n)
    (hv : ∀ n, v (n + 1) = a n * v n)
    (hrise : ∀ n, u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  sorry

/-- Eventual form of `no_boundedRise_reducedTail`, obtained by shifting to the
first reduced exact index. -/
theorem no_eventuallyBoundedRise_reducedTail
    (a u v : ℕ → ℕ) (N B : ℕ)
    (hB : 0 < B)
    (ha : ∀ n, N ≤ n → 1 < a n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hu : ∀ n, N ≤ n → u (n + 1) + v n = a n * u n)
    (hv : ∀ n, N ≤ n → v (n + 1) = a n * v n)
    (hrise : ∀ n, N ≤ n → u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  sorry

end Erdos249257.ExternalVerification243BoundedRiseReducedTail
