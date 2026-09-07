/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for gcd stabilisation along an exact reciprocal-tail orbit

One source-independent proposition, in pure `Nat`/`Int` vocabulary.

Let `a C D : ℕ → ℕ` satisfy the exact product-cleared dynamics
`C (n+1) + D n = a n * C n` and `D (n+1) = a n * D n`, and let `E : ℕ → ℤ` be
the centred error `E n = D n - (a n - 1) * C n`. Suppose the negative errors
have a single bound `B` along a cofinal set of indices: for every `N` there is
a `t ≥ N` with `E t < 0` and `-B ≤ E t`.

Then `gcd (C n) (D n)` is eventually a constant positive `g`, and dividing by
`g` produces a genuine reduced exact tail: the quotients stay positive, become
coprime, and satisfy both original recurrences.

The conclusion is a single tuple, so the stable value, the positivity, the
coprimality and both quotient recurrences are all part of the statement rather
than named informally.

Boundary. This is one arithmetic ingredient of the rigidity argument for
Erdős #243. It supplies the reduction step only, and no part of it bounds the
negative errors of an arbitrary orbit or settles the parent problem, which
remains open.
-/

namespace Erdos249257.ExternalVerification243GcdStabilisation

/-- The centred error `E n = D n - (a n - 1) * C n`, over the integers. -/
def centred (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

/-- **Gcd stabilisation and reduction.** Cofinally bounded negative errors make
the tail gcd eventually constant, and division by it yields a reduced exact
tail. -/
theorem gcd_stabilises_and_reduces
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centred (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hnegative : ∃ B : ℕ, ∀ N, ∃ t,
      N ≤ t ∧ E t < 0 ∧ -(B : ℤ) ≤ E t) :
    ∃ N g : ℕ, 0 < g ∧
      (∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) ∧
      (∀ n, N ≤ n → 0 < C n / g) ∧
      (∀ n, N ≤ n → Nat.Coprime (C n / g) (D n / g)) ∧
      (∀ n, N ≤ n → C (n + 1) / g + D n / g = a n * (C n / g)) ∧
      (∀ n, N ≤ n → D (n + 1) / g = a n * (D n / g)) := by
  sorry

end Erdos249257.ExternalVerification243GcdStabilisation
