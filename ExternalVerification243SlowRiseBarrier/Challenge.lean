/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for slow-rise exclusion on reduced reciprocal tails

One source-independent proposition.  A *reduced exact tail* is a pair of
sequences `u, v : ℕ → ℕ` with multipliers `a : ℕ → ℕ`, all `a n > 1` from an
index `N`, satisfying the two cocycle equations `u (n+1) + v n = a n * u n`
and `v (n+1) = a n * v n`, with `u n` and `v n` coprime at every late index.

The theorem excludes such a tail whose numerator tends to infinity and which,
for some block length `B`, starts below the product `P` of the `B` multipliers
`a N, …, a (N+B-1)` and then rises by at most `B` per step *for as long as it
stays below `2P`*.

The rise budget is required only on the finite window `u n < 2P`, not
uniformly.  That is the whole strengthening: a uniform rise bound `B`
everywhere is a special case.

Boundary.  The block-start hypothesis `hstart` and the windowed rise bound
`hrise` are hypotheses; neither is derived from the underlying dynamics.  The
analytic transfer that supplies them on the canonical Erdős #243 orbit is an
ordinary proof and is not formalised.  Unrestricted Erdős #243 remains open.
-/

namespace Erdos249257.ExternalVerification243SlowRiseBarrier

/-- **Slow-rise exclusion for reduced exact tails.**  No reduced exact tail
with multipliers exceeding one and numerator tending to infinity can start,
for some block length `B`, below the product of its first `B` multipliers and
then rise by at most `B` at every index while the numerator is below twice
that product. -/
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
    False := by
  sorry

end Erdos249257.ExternalVerification243SlowRiseBarrier
