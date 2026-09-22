-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

import Erdos249257.AdelicHeightObstruction
import Erdos249257.CertificateKernel
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCylinderHalfMembershipClassification
import Erdos249257.HalfCylinderIntegerGreedy
import Erdos249257.HalfDivisorUnitDrop
import Erdos249257.HalfGapMass
import Erdos249257.HalfTrappingReturnCarry
import Erdos249257.MaximalOmegaLayer

/-!
# Second additive Erdos 257 paper-correspondence audit

This source-current audit covers the declaration endpoints added after
`PaperCorrespondenceAudit.lean` and `PaperCorrespondenceAuditAdditive.lean`
were frozen. It adds no theorem and changes no mathematical claim.
-/

#print axioms Erdos249257.mersenneGap_pos
#print axioms Erdos249257.summable_mersenneGap_succ
#print axioms Erdos249257.mersenneGap_tail_le
#print axioms Erdos249257.tendsto_mersenneGap_tail_zero
#print axioms Erdos249257.MaximalOmegaLayer.primePowerLayer_comm
#print axioms Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo_supportCoeffInt
#print axioms Erdos249257.HalfCylinderIntegerGreedy.supportCoeff_insert_eq_add_indicator
#print axioms Erdos249257.HalfDivisorUnitDrop.supportCoeff_extend_true_eq_false_add_one_at_double
#print axioms Erdos249257.irrational_erdosSupportSeries_residueClass
#print axioms Erdos249257.seamGreedy_terminal_false_iff_upperOrMiddle
#print axioms Erdos249257.AdelicHeightObstruction.linearDescender_eq_smul_eval
#print axioms Erdos249257.HalfTrappingReturnCarry.relationInvariantLinearChannels_det_eq_zero
#print axioms Erdos249257.greedy_survives_of_mem_mersenneAchievementSet
#print axioms Erdos249257.mem_mersenneAchievementSet_of_greedy_survival
