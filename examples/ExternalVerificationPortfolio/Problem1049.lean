-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Erdos249257
import ExternalVerification.Solution

/-!
# Erdős #1049: two rational-base obstruction interfaces

This downstream module exposes two distinct, source-current Comparator
interfaces for Erdős #1049:

* `rational_base_cleared_tail_recurrence` is the exact rational-base tail
  recurrence, including the denominator-base factor `s^(N+1)`.
* `rectangular_hp_classical_threshold_iff` is the sharp equality
  classification for one explicit rectangular two-function Hermite--Padé
  exponent model.

The first is reusable dynamics; the second is a model-specific no-go. Neither
constructs the primitive-normalized coefficient family and controlled analytic
remainder needed for the actual base-`3/2` Lambert series. This module proves
no #1049 irrationality statement and makes no novelty or priority claim.
-/

namespace ExternalVerificationPortfolio.Problem1049

/-! ## Rational-base cleared-tail dynamics -/

#check ErdosProblems.Erdos1049.rationalBaseClearedTailQ
#check ErdosProblems.Erdos1049.rationalBaseClearedTailQ_succ
#check Erdos249257.ExternalVerification.rationalBaseClearedTailQ_succ

/-- Source-faithful reuse of the exact rational-base recurrence.

For a putative rational value, the exact cleared-tail recurrence is
`U_(N+1) = r * U_N - B * c(N+1) * s^(N+1)`.  The factor `s^(N+1)` is the
denominator-base tax that disappears only for an integer base.  The consumer
keeps the coefficient and nonzero-numerator hypothesis explicit: the
identity is reusable dynamics, not a rationality contradiction or an
irrationality conclusion at `3/2`. -/
theorem rational_base_cleared_tail_recurrence
    {r s B F : ℚ} {coeff : ℕ → ℚ} (hr : r ≠ 0) (N : ℕ) :
    Erdos249257.ExternalVerification.rationalBaseClearedTailQ
        r s B F coeff (N + 1) =
      r * Erdos249257.ExternalVerification.rationalBaseClearedTailQ
        r s B F coeff N -
        B * coeff (N + 1) * s ^ (N + 1) :=
  Erdos249257.ExternalVerification.rationalBaseClearedTailQ_succ hr N

/-! ## Rectangular Hermite--Padé threshold: sharp model-specific no-go -/

#check ErdosProblems.Erdos1049.hpClearedGap_expansion
#check ErdosProblems.Erdos1049.hpClearedGap_nonpos
#check ErdosProblems.Erdos1049.rectangular_hp_threshold_eq_classical_iff
#check Erdos249257.ExternalVerification.rectangular_hp_threshold_eq_classical_iff

/-- Source-faithful reuse of the sharp threshold classification in the stated
rectangular model.

The explicit rectangular two-function exponent model has threshold
`hpThreshold rho sigma` in the admissible region `0 ≤ rho` and
`1 + rho ≤ sigma`.  Writing `sigma = 1 + rho + u` with `u ≥ 0` expands the
cleared difference into nonpositive terms; equality forces `rho = u = 0`,
which is exactly `rho = 0` and `sigma = 1`.  The hard step is this sign and
unique-zero calculation.  The source constructs no approximating polynomials
or remainders, is not a universal Padé/Hermite--Padé no-go, and proves no
irrationality at `3/2`; Erdős #1049 remains open and no novelty or priority
claim is made. -/
theorem rectangular_hp_classical_threshold_iff
    (rho sigma : ℝ) (hrho : 0 ≤ rho)
    (hsigma : 1 + rho ≤ sigma) :
    Erdos249257.ExternalVerification.hpThreshold rho sigma =
        1 / 2 - 1 / Real.pi ^ 2 ↔
      rho = 0 ∧ sigma = 1 :=
  Erdos249257.ExternalVerification.rectangular_hp_threshold_eq_classical_iff
    rho sigma hrho hsigma

/-! ## Supporting scoped no-go (not a third headline) -/

#check ErdosProblems.Erdos1049.CoordinatewiseCorridor
#check Erdos249257.ExternalVerification.threeHalves_no_coordinatewiseCorridor

end ExternalVerificationPortfolio.Problem1049
