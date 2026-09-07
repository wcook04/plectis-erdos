/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR7.Reduction

/-!
# Source transport for gcd stabilisation along an exact reciprocal-tail orbit

The local `centred` repeats the corpus `centeredState` verbatim, so the two
agree by `rfl` and the challenge statement transports directly.
-/

namespace Erdos249257.ExternalVerification243GcdStabilisation

/-- The centred error `E n = D n - (a n - 1) * C n`, over the integers. -/
def centred (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

theorem centred_eq (a D C : ℤ) :
    centred a D C = ErdosProblems.Erdos243.centeredState a D C :=
  rfl

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
      (∀ n, N ≤ n → D (n + 1) / g = a n * (D n / g)) :=
  ErdosProblems.Erdos243.PaperCompleteR7.gcd_stabilises_and_reduces
    a C D E hC hD (fun n ↦ (hE n).trans (centred_eq _ _ _)) hnegative

end Erdos249257.ExternalVerification243GcdStabilisation
