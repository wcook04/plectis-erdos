import ErdosProblems.Skip.Wire1

open Erdos249257 Erdos249257.Wire1

#print axioms Erdos249257.Wire1.half_not_mem_of_rightTail
#print axioms Erdos249257.Wire1.allRight_half_not_mem
#print axioms Erdos249257.Wire1.allRight_branch_disjunction_collapse
#print axioms Erdos249257.Wire1.allRight_branch_resolved_iff_false
#print axioms Erdos249257.Wire1.not_largestSkipLateStepSocket_of_rightTail
#print axioms Erdos249257.Wire1.isLargestFalseRank_frozen
#print axioms Erdos249257.Wire1.largestSkipLateAt_of_frozen
#print axioms Erdos249257.Wire1.ratchetWindow_all_late
#print axioms Erdos249257.Wire1.finalMiddleCell_ratchetWindow_all_late
#print axioms Erdos249257.Wire1.cofRanks_subset_of_rightTail
#print axioms Erdos249257.Wire1.allRight_landingExcess_two_impossible_of_earlyRightTail
#print axioms Erdos249257.Wire1.rightTail_threshold_gt_producer
#print axioms Erdos249257.Wire1.earlyRightTail_never_at_producer
#print axioms Erdos249257.Wire1.cofactor_certification_gap
#print axioms Erdos249257.Wire1.exists_cofSkip_in_window
#print axioms Erdos249257.Wire1.allRight_landingExcess_two_forces_large_frozen_skip
#print axioms Erdos249257.Wire1.allRight_landingExcess_two_forces_two_large_skips
#print axioms Erdos249257.Wire1.allRight_branch_status
#print axioms Erdos249257.Wire1.allRight_branch_resolved
#print axioms Erdos249257.Wire1.finalMiddleCell_neg_two_impossible_of_earlyRightTail
#print axioms Erdos249257.Wire1.finalMiddleCell_defeats_earlyRightTail

-- upstream lemmas the file leans on
#print axioms Erdos249257.seamGreedyEventuallyRight_iff_half_not_mem
#print axioms Erdos249257.AngleB2.allRight_landingExcess_two_impossible

-- statements, in full
set_option pp.all false in
#check @Erdos249257.Wire1.allRight_branch_resolved
#check @Erdos249257.AngleB2.allRight_landingExcess_two_impossible
#check @Erdos249257.seamGreedyEventuallyRight_iff_half_not_mem
#check @Erdos249257.SeamGreedyUpperOrMiddleAt
#check @Erdos249257.AngleB2.cofRanks
#check @Erdos249257.LargestSkipLateAt
#check @Erdos249257.LargestSkipLateStepSocket
