/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification257TwentyOneFatalBranch.Challenge

/-!
# Deliberate negative fixture

This file intentionally fails to implement the trusted five-theorem module:
the exact membership/fatal-branch equivalence is omitted.  Comparator should
reject the module because its declaration surface does not match the
challenge.
-/

namespace Erdos249257.ExternalVerification257TwentyOneFatalBranch

noncomputable section

theorem negative_only_closed_state
    (hsupply : TwentyOneClosedLowerStateSupply) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  exact one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates hsupply

end

end Erdos249257.ExternalVerification257TwentyOneFatalBranch
