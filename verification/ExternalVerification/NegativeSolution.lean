/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification.Statements

/-!
# Deliberately mismatched Comparator fixture

This module is expected to fail Comparator.  The extra hypothesis and altered
right-hand side make the named declaration easy to prove while ensuring that
it is not the trusted challenge statement.  CI treats Comparator acceptance of
this fixture as a security-regression failure.
-/

namespace Erdos249257.ExternalVerification

open Module

theorem finrank_totientKernelThroughLevelFamily_eq (e : ℕ) (_he : 1 ≤ e)
    (mismatch :
      finrank ℚ
        (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
          2 ^ e + 2) :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 2 := mismatch

end Erdos249257.ExternalVerification
