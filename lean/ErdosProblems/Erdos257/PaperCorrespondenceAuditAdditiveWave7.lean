-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCylinderMiddleCarryLowerBound
import Erdos249257.HalfUpperResetCriticalBand

/-!
# Seventh additive Erdos 257 paper-correspondence audit

This source-current audit batches the two-channel cap, the two middle-transition
results, and the critical dyadic-band reduction added after the sixth additive
audit was frozen. It adds no theorem and changes no mathematical claim.
-/

#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_skipped_twoChannelCap
#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_skipped_dyadicCap
#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerCardEscape
#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerRowEscape
#print axioms Erdos249257.middleProducer_allRight_forces_carry_lt_tail
#print axioms Erdos249257.middleProducer_allRight_forces_rational_skip
#print axioms Erdos249257.producerCarry_insert_seamBelowSupport_eq_middleCoordinate
#print axioms Erdos249257.binaryCoeffTail_nonneg
#print axioms Erdos249257.binaryCoeffTail_supportCoeff_coe_finset_le_card
#print axioms Erdos249257.HalfUpperResetCriticalBand.exists_criticalDyadicBandIndex
#print axioms Erdos249257.HalfUpperResetCriticalBand.dyadicBandEscape_iff_exists_critical
#print axioms Erdos249257.HalfUpperResetCriticalBand.seamUpperResetCriticalBandEscape_iff
