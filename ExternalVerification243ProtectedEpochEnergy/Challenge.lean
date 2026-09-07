/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for protected-epoch record energy in Erdős #243

One source-independent proposition.  Along a dynamically reduced primitive
orbit with *arbitrary* cancellation factors, a single odd prime power
`Q = p ^ l` dividing one denominator state is charged against the whole family
of odd multiples of `p` in the window from `p * Q / 4` to `p * Q / 2`.  The
conclusion is a lower bound on record energy inside that one protected epoch:
an explicit finite set of charged steps, each a global record, cancellation
free, and jumping by at least three, whose count and excess satisfy an
inequality linear in `p * Q`.

No product of moduli appears: one divisibility is reused across roughly `Q / 8`
independent barriers.

Boundary.  What is proved is a *lower* bound on record energy per protected
epoch.  The matching upper bound, that a bounded-negative-part or summable
orbit has finite total energy so infinitely many protected epochs are
impossible, is not proved here and is the open parent.  Erdős #243 remains
open.
-/

namespace Erdos249257.ExternalVerification243ProtectedEpochEnergy

/-- The running maximum of a natural-valued sequence. -/
def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

/-- **Protected-epoch record energy.**  One odd prime power dividing a single
denominator state forces an explicit lower bound on the record energy spent
before the numerator reaches half of `p * Q`, uniformly in the cancellation
factors. -/
theorem protected_epoch_energy_integer
    (a u v w hc : ℕ → ℕ) (p l s τ : ℕ)
    (hp : p.Prime)
    (hpodd : Odd p)
    (hl : 1 ≤ l)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hprot : p ^ l ∣ v s)
    (hQ : 16 ≤ p ^ l)
    (hRs : 4 * runningMax u s < p * p ^ l)
    (hsτ : s < τ)
    (hτ : p * p ^ l ≤ 2 * u τ) :
    ∃ J : Finset ℕ,
      (∀ n ∈ J, s ≤ n ∧ n < τ ∧ runningMax u n < u (n + 1) ∧
          u n + 3 ≤ u (n + 1) ∧ hc n = 1) ∧
      p * p ^ l ≤ (8 * p + 8) * J.card
        + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by
  sorry

end Erdos249257.ExternalVerification243ProtectedEpochEnergy
