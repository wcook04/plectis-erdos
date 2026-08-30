-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Erdos249257
import ExternalVerification.Solution

/-!
# Erdős #243: external recovery consumers

This downstream module packages two distinct, conditional #243 endpoints from
the advertised external-verification interface.

* `bounded_negative_part_recovery` turns an exact centered-state system,
  a uniform lower bound on its signed defect, and normalized vanishing into
  eventual vanishing of that defect.
* `summable_negative_mass_sylvester_recovery` uses the stronger finite
  normalized negative-mass hypothesis to recover the Sylvester recurrence
  eventually.

Neither hypothesis bundle is produced for an unrestricted reciprocal-tail
orbit here.  In particular, this module does not claim a solution of Erdős
#243.  The defect identity, zero-absorption lemma, and fresh-modulus
bounded-rise obstruction below are mechanisms supporting these routes, not
additional endpoint claims.
-/

namespace ExternalVerificationPortfolio.Problem243

open Erdos249257

/-! ## Public endpoints -/

#check Erdos249257.ExternalVerification.boundedNegativePart_eventually_zero
#check Erdos249257.ExternalVerification.sylvesterNext_eventually_of_summable_negativeRelativeMass

/-- A source-faithful external wrapper for the signed centered-state endpoint.

The conclusion is eventual zero of the centered defect.  It is conditional on
the displayed dynamics, strict centering, uniform lower bound, and
division-free normalized vanishing; it does not assert that arbitrary #243
data provide them. -/
theorem bounded_negative_part_recovery
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (B : ℕ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = Erdos249257.ExternalVerification.centeredState
      (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hcentered : ∀ n, Int.natAbs (E n) < C n)
    (hbound : ∀ n, -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 :=
  Erdos249257.ExternalVerification.boundedNegativePart_eventually_zero
    a C D E B ha hCpos hC hD hE hcentered hbound hvanish

/-- A source-faithful external wrapper for the finite negative-mass endpoint.

Finite normalized negative mass is an explicit premise.  Under the exact
state update and normalized vanishing it yields eventual Sylvester recurrence,
not an unconditional recurrence theorem for reciprocal-tail data. -/
theorem summable_negative_mass_sylvester_recovery
    (a D : ℕ → ℤ) (C : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) =
      Erdos249257.ExternalVerification.nextDenState (a n) (D n))
    (hC : ∀ n, C (n + 1) =
      Erdos249257.ExternalVerification.nextTailState (a n) (D n) (C n))
    (hCpos : ∀ n, 0 < C n)
    (hstep : ∀ n, (C (n + 1) : ℤ) =
      (C n : ℤ) - Erdos249257.ExternalVerification.centeredState
        (a n) (D n) (C n))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (Erdos249257.ExternalVerification.centeredState
        (a n) (D n) (C n)) < C n)
    (hsum : Summable
      (Erdos249257.ExternalVerification.negativeRelativeMass C
        (fun n ↦ Erdos249257.ExternalVerification.centeredState
          (a n) (D n) (C n)))) :
    ∃ N, ∀ n, N ≤ n →
      a (n + 1) = Erdos249257.ExternalVerification.sylvesterNext (a n) :=
  Erdos249257.ExternalVerification.sylvesterNext_eventually_of_summable_negativeRelativeMass
    a D C hD hC hCpos hstep hvanish hsum

/-! ## Supporting mechanisms (not additional endpoints) -/

#check ErdosProblems.Erdos243.sylvesterDefect_mul_nextTailState
#check ErdosProblems.Erdos243.centeredState_zero_absorbing
#check ErdosProblems.Erdos243.no_boundedRise_of_tailAvoidance

end ExternalVerificationPortfolio.Problem243
