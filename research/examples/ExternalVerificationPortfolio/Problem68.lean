-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Erdos249257
import ExternalVerification.Solution

/-!
# Erdős #68 external verification consumer

This module records two equivalent public coordinates for the exact remaining
endpoint of Erdős #68 and one coefficient-free producer for them.  None proves
the required cofinal input: finite strict-factorial-top misses, finite nonunit
carry computations, or isolated complementary-residue bounds do not establish
the universally quantified supplies below.

The pointwise bridge is
`factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat`: for `m ≥ 3`, the
rounding carry is one exactly when `m` divides the strict factorial-top integer
of the exact rational prefix.  Thus the two endpoint theorems are equivalent
views of one producer boundary, not independent irrationality proofs.
-/

namespace ExternalVerificationPortfolio.Problem68

#check ErdosProblems.Erdos68.factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat
#check Erdos249257.ExternalVerification.irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses
#check Erdos249257.ExternalVerification.irrational_factorialGapSeries_iff_cofinal_nonunit_carries

/-- Exact divisor-miss characterization.  Its right-hand side remains an
unproved cofinal supply for the actual factorial-gap prefixes. -/
theorem strict_factorial_top_divisor_characterization :
    Irrational Erdos249257.ExternalVerification.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧
          ¬(m : ℤ) ∣
            Erdos249257.ExternalVerification.strictFacTopRat
              (Erdos249257.ExternalVerification.factorialGapPrefix m) m :=
  Erdos249257.ExternalVerification.irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses

/-- Exact carry characterization.  Its right-hand side remains an unproved
cofinal supply of strict-successor carries different from one. -/
theorem nonunit_carry_characterization :
    Irrational Erdos249257.ExternalVerification.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧
          Erdos249257.ExternalVerification.factorialGapStepCarry m ≠ 1 :=
  Erdos249257.ExternalVerification.irrational_factorialGapSeries_iff_cofinal_nonunit_carries

/-! ## Coefficient-free global complementary residue -/

#check Erdos249257.ExternalVerification.irrational_factorialGapSeries_of_cofinal_global_complementaryTail

/-- A cofinal lower bound on the one global complementary residue of each
selected factorial block feeds the nonunit-carry characterization and hence
irrationality.  The certificate is an explicit premise: this example does not
produce the required cofinal private-modulus or residue-size bounds. -/
theorem irrational_of_cofinal_global_complementary_residue
    (hcert :
      Erdos249257.ExternalVerification.CofinalGlobalComplementaryTailCertificate) :
    Irrational Erdos249257.ExternalVerification.factorialGapSeries :=
  Erdos249257.ExternalVerification.irrational_factorialGapSeries_of_cofinal_global_complementaryTail
    hcert

end ExternalVerificationPortfolio.Problem68
