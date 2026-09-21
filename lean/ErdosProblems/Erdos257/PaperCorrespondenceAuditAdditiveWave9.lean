-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

import Erdos249257.HalfCylinderLargestSkipInduction
import Erdos249257.HalfCylinderHalfMembershipClassification
import Erdos249257.MersenneShadowDenominatorGrowth
import Erdos249257.HalfUpperResetCriticalBand

/-!
# Ninth additive Erdos 257 paper-correspondence audit

This source-current audit batches the late largest-skip mechanism, Mersenne
channel denominator growth, and the exact upper-reset charge record. It adds no
theorem and changes no mathematical claim.
-/

#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket
#print axioms Erdos249257.largestSkipLateAt_fourteen
#print axioms Erdos249257.seamGreedy_terminal_false_iff_upperOrMiddle
#print axioms Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_lower_bound
#print axioms Erdos249257.MersenneShadowDenominatorGrowth.upperHalfMersenneProduct_lower_bound
#print axioms Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_exact
#print axioms Erdos249257.seamUpperBranch_remainder_add_resetCharge_eq
#print axioms Erdos249257.HalfUpperResetCriticalBand.seamUpperResetCharge_le
