/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification.Statements

/-!
# Deliberately mismatched weighted-support interface

The extra hypothesis makes this declaration trivial while changing its type.
Comparator must reject it against the independently stated weighted theorem.
-/

namespace Erdos249257.ExternalVerification

theorem divisibilityWeightedClaim (assumed : DivisibilityWeightedClaim) :
    DivisibilityWeightedClaim := assumed

end Erdos249257.ExternalVerification
