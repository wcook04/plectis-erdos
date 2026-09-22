-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

import Erdos249257.BooleanMobiusCriticalCapacityCofinal
import Erdos249257.BooleanMobiusSkipRow

/-!
# Twelfth additive Erdos 257 paper-correspondence audit

This source-current audit batches the actual-orbit quotient socket, the two
finite-lookahead skip mechanisms, and the sharp skipped-core fill with its
exact-row projection. It adds no theorem and changes no mathematical claim.
-/

#print axioms Erdos249257.HalfGreedySkippedCriticalQuotientSupply
#print axioms Erdos249257.skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped
#print axioms Erdos249257.halfGreedy_precriticalSuffix_lt_of_next_skip
#print axioms Erdos249257.halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix
#print axioms Erdos249257.halfGreedySkippedPrecriticalSuffixSupply_iff_preTake
#print axioms Erdos249257.halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock
#print axioms Erdos249257.precriticalCrossingTax_of_futureThreshold
#print axioms Erdos249257.sub_two_le_two_pow_sub_four
#print axioms Erdos249257.exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity
#print axioms Erdos249257.exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity
