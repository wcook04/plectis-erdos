/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.SlowRiseBarrier

/-!
# Source transport for slow-rise exclusion on reduced reciprocal tails

The source theorem `ErdosProblems.Erdos243.no_slowRise_reducedTail` is already
stated in Mathlib-only vocabulary, so the transport is the identity: the
Challenge statement is the source statement with no reinterpretation.
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
    False :=
  ErdosProblems.Erdos243.no_slowRise_reducedTail a u v N B ha hred hu hv huTop
    hstart hrise

end Erdos249257.ExternalVerification243SlowRiseBarrier
