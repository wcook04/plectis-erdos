-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

import Erdos249257.HalfCylinderFullShellSeamBridge
import Erdos249257.HalfCylinderFinalMiddleCellEscape
import Erdos249257.HalfCylinderSkippedEndpointClassifier

/-!
# Eighth additive Erdos 257 paper-correspondence audit

This source-current audit batches the frozen-margin equivalences, the excluded
final-middle cell, and the skipped-endpoint trichotomy added after the seventh
additive audit was frozen. It adds no theorem and changes no mathematical claim.
-/

#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
#print axioms Erdos249257.skippedSeamAlignmentZero_iff_skippedFullShellNonnegative
#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamEscape
#print axioms Erdos249257.finalMiddleCell_neg_three_not_last
#print axioms Erdos249257.mobiusCenteredHalfCarry_add_two
#print axioms Erdos249257.halfGreedy_skipped_endpoint_trichotomy
