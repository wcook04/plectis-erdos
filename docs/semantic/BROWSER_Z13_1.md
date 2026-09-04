# Z13_1: Half-cylinder integer seam: greedy remainder, floor-error resets and the fatal-gap / right-tail classification

[All problems and zones](BROWSER.md)

<a id="node-64ee0481167c5f3c"></a>
## abstract_greedy_optimality_and_small_defect_equivalence

For any list of weights that is gap dominating with a positive gap, distinct Boolean subset sums differ by at least the gap; descending greedy realises the maximal subset sum below a capacity; and for any window B strictly below the gap, some Boolean word leaves a positive defect at most B exactly when the descending greedy remainder itself lies in that window, in which case that word is the greedy word.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [integerGreedyBits_maximal](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L534)
- Lean declaration: [exists_smallPositiveDefect_iff_integerGreedyRemainder](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L578)
- Lean declaration: [smallPositiveDefect_bits_eq_integerGreedyBits](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L415)

- incoming **specialises**: [Z13::first_wrap_defect_reduction_to_one_integer_remainder](BROWSER_Z13_1.md#node-f942af3456eb9342). The seam reduction is the abstract small-defect equivalence instantiated at the truncated Mersenne weights with B = halfStripBound (2s).
- incoming **specialises**: [Z13::skipped_endpoint_trichotomy](BROWSER_Z13_2.md#node-b0a9f7595464c220). Uniqueness of the small-defect bit word is what forces alignment in the negative cell.

<a id="node-c1a58e98f65e57f9"></a>
## actual_seam_hole_equals_integer_subset_sum_defect

For every finite Boolean stem supported on proper ranks 2,...,s-1 and not containing s, the actual first-wrap seam hole (twice the integer half carry at depth 2s-2 minus the divisor coefficient at row 2s) equals the seam subset target minus the selected truncated weight sum. The finite divisor/multiple incidence swap needed for this is discharged unconditionally.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [stemIncidenceSwap](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L863)
- Lean declaration: [actualSeamHole_eq_target_sub_stemTruncatedSum_unconditional](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L1079)

- incoming **equivalent_to**: [Z13::full_shell_margin_equals_integer_seam_defect](BROWSER_Z13_1.md#node-287d59e425cc9ca6). At the full first shell the analytic frozen margin and the integer seam hole are the same signed quantity.
- incoming **implies**: [Z13::truncated_mersenne_weight_closed_forms](BROWSER_Z13_2.md#node-5f7575629a24a895). The divisor-indicator form of the weight is what makes the finite incidence swap unconditional.

<a id="node-d83a2249c9dda725"></a>
## adjacent_cut_three_branch_recurrence

In any perturbed family whose pulse cap is below the separation gap, the maximal admissible word after one row perturbation is either the old maximal word or its immediate successor, and the next residual obeys an exact three-branch recurrence: gap minus four times the overshoot minus the above pulse when the successor carries; four times the remainder plus gap minus the below pulse when it does not and that value is under the terminal weight; and that value minus the terminal weight otherwise.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [prefixChoice_maximal](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L1390)
- Lean declaration: [nextRemainder_trichotomy](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L1463)

- incoming **specialises**: [Z13::concrete_seam_greedy_one_step_recurrence](BROWSER_Z13_1.md#node-ee25eb717dc7da27). The concrete seam family is a PerturbedFamily, so its next residual is the abstract three-branch recurrence.
- incoming **implies**: [Z13::seam_row_perturbation_affine_recurrence](BROWSER_Z13_2.md#node-d0e2aef10d6d2237). The affine row recurrence supplies the newSum = 4*oldSum + pulse structure that the abstract packet requires.

<a id="node-4b7b4075983286bd"></a>
## aligned_positive_skip_forces_next_take

If at row s (at least five) the real greedy orbit for 1/2 skips rank s, the actual seam word coincides with the integer seam greedy word, and the integer greedy remainder is positive, then the real greedy decision at rank s+1 is a take. Combined with the skipped-endpoint trichotomy this says the negative-margin endpoint cell cannot occur at two consecutive rows.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [alignedPositiveSkip_forces_next_take](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L1220)
- Lean declaration: [seamTakeThreshold_le_greedyFloorZ_of_card_add_two_le](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L1033)
- Lean declaration: [mersenneWeightRat_le_seamGreedyRemainder_of_card_add_two_le](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L1062)

- outgoing **specialises**: [Z13::skipped_endpoint_trichotomy](BROWSER_Z13_2.md#node-b0a9f7595464c220). Its hypotheses are exactly the first cell of the trichotomy, so it says that cell cannot recur at consecutive rows.

<a id="node-ee25eb717dc7da27"></a>
## concrete_seam_greedy_one_step_recurrence

The finite seam words at row s form a concrete perturbed family whose adjacent cut at the seam target has remainder equal to the integer greedy remainder at row s and next residual equal to the integer greedy remainder at row s+1; the cut's successor word is literally the seam greedy word at row s+1, and the three branch conditions identify it as the above word extended by false, the below word extended by false, or the below word extended by true.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamAdjacentCut_remainder](../../Erdos249257/HalfCylinderConcreteSeamAdapter.lean#L375)
- Lean declaration: [seamAdjacentCut_nextRemainder](../../Erdos249257/HalfCylinderConcreteSeamAdapter.lean#L699)
- Lean declaration: [seamCutNextWord_eq_greedyWord_succ](../../Erdos249257/HalfCylinderConcreteSeamAdapter.lean#L667)
- Lean declaration: [seamGreedyWord_succ_eq_upperBranch](../../Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L289)
- Lean declaration: [seamGreedyWord_succ_eq_middleBranch](../../Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L306)
- Lean declaration: [seamGreedyWord_succ_eq_rightBranch](../../Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L338)

- outgoing **specialises**: [Z13::adjacent_cut_three_branch_recurrence](BROWSER_Z13_1.md#node-d83a2249c9dda725). The concrete seam family is a PerturbedFamily, so its next residual is the abstract three-branch recurrence.
- incoming **reformulates**: [Z14::producer_carry_concrete_seam_coordinates](BROWSER_Z14_1.md#node-58512ec8c409376b). producerCarry_insert_seamBelowSupport_eq_middleCoordinate and _seamAboveSupport_eq_neg_upperCoordinate identify the producer carry of the adjacent-cut words with the middle and upper coordinates of the seam cut defined by seamAdjacentCut_remainder / seamAdjacentCut_nextRemainder.

<a id="node-d3989be3bc2bd747"></a>
## deficit_run_length_law

For rows s >= 5 with rem(s) <= 2^s, if the doubled-scale deficit satisfies 2^s <= 2^k * (2^s - rem(s)) then an upper or middle branch occurs at some row between s and s+k. Contrapositively, an all-right run of length k from row s forces rem(s) to lie within 2^(s-k) of the half point 2^s. The hypothesis rem(s) <= 2^s is present in the Lean statement and is not discharged there.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [upperOrMiddle_within_of_two_pow_deficit](../../Erdos249257/HalfCylinderResetDeficitEscape.lean#L261)

- outgoing **specialises**: [Z13::right_branch_remainder_recurrence](BROWSER_Z13_1.md#node-ab61c6e40afd5d3d). The run law is the iterated right-branch recurrence compared with the quarter-point middle trigger.

<a id="node-45b4e991db0c37aa"></a>
## exact_late_rank_adjacent_gap

In the late range 2s < 3d the truncated Mersenne weight is exactly 2^(2s-d) + 4^(s-d), the strict suffix weights telescope, and the adjacent lower and upper words with any common lower prefix satisfy the division-free identity 3*lowerWeight + (3*2^(s+1) + 2*4^(s-d) + 4) = 3*upperWeight, that is a gap of 2^(s+1) + (2*4^(s-d)+4)/3.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank](../../Erdos249257/HalfCylinderLargestSkipGap.lean#L118)
- Lean declaration: [three_mul_tailWeight_add_exactLateGap_eq_three_mul_headWeight](../../Erdos249257/HalfCylinderLargestSkipGap.lean#L230)
- Lean declaration: [three_mul_largestSkipLowerWeight_add_exactLateGap_eq_upperWeight](../../Erdos249257/HalfCylinderLargestSkipGap.lean#L259)

- incoming **depends_on_open**: [Z13::right_branch_remainder_window](BROWSER_Z13_1.md#node-015a003e6df09663). The window bounds are read off the division-free late adjacent-gap identity.

<a id="node-84eab96a9c382e8c"></a>
## fatal_gap_eventual_right_classification

Four statements are proved equivalent: the integer seam greedy word eventually extends by a true terminal bit at every row; a finite fatal half gap exists (a finite prefix whose value plus the whole remaining Mersenne tail is below 1/2 while the prefix plus the next weight is above it); 1/2 is not in the Mersenne achievement set; and the real greedy orbit for 1/2 has a last skipped exponent. The hard direction builds the fatal gap from the largest missing rank of a base row, using two limit endpoint kills.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamGreedyEventuallyRight_iff_existsFatalHalfGap](../../Erdos249257/HalfCylinderFatalGapRightTail.lean#L781)
- Lean declaration: [seamGreedyEventuallyRight_iff_half_not_mem](../../Erdos249257/HalfCylinderFatalGapRightTail.lean#L787)
- Lean declaration: [seamGreedyEventuallyRight_iff_exists_isLastHalfGreedySkip](../../Erdos249257/HalfCylinderFatalGapRightTail.lean#L802)
- Lean declaration: [existsFatalHalfGap_of_seamGreedyEventuallyRight](../../Erdos249257/HalfCylinderFatalGapRightTail.lean#L757)

- incoming **equivalent_to**: [Z13::unbounded_skipped_ranks_give_half_membership](BROWSER_Z13_2.md#node-0c099e1977615cd1). The supply antecedent is the negation of eventual-right, which the classification proves equivalent to the conclusion; hence this consumer is a restatement.
- incoming **reformulates**: [Z13::half_membership_iff_every_skip_survives](BROWSER_Z13_1.md#node-31f5cf394cc9250d). Both restate half-membership; the fixed-tail form is the rank-local version of the last-skip clause.
- outgoing **equivalent_to**: [Z12::half_membership_seam_equivalence_ring](BROWSER_Z12_1.md#node-c98bead16d978fce). seamGreedyEventuallyRight_iff_half_not_mem (HalfCylinderFatalGapRightTail.lean) and half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight (HalfCylinderHalfMembershipClassification.lean) are complementary halves of one equivalence about the integer seam.
- outgoing **equivalent_to**: [Z12::fatal_half_gap_dichotomy](BROWSER_Z12_1.md#node-5736eac8e3dd6fae). seamGreedyEventuallyRight_iff_existsFatalHalfGap composed with existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet (HalfCutLocator.lean) makes the two nodes the same dichotomy in seam and cut-locator coordinates.
- outgoing **equivalent_to**: [Z12::last_skip_iff_finite_skips](BROWSER_Z12_2.md#node-275fc9b423c4c20c). seamGreedyEventuallyRight_iff_exists_isLastHalfGreedySkip and exists_isLastHalfGreedySkip_iff_skippedSupport_finite are the same last-skip characterisation in seam and greedy coordinates.
- incoming **equivalent_to**: [Z12::shift_window_zero_endpoint_restatement](BROWSER_Z12_2.md#node-592c2020744fdf2f). shiftWindowZero_iff_half_mem_mersenneAchievementSet and seamGreedyEventuallyRight_iff_half_not_mem land on the same endpoint, so the shifted-window interface and the eventual-right seam classification are two names for one open proposition.
- incoming **depends_on_open**: [Z12::last_skip_shift_geometry](BROWSER_Z12_2.md#node-842347b882d96c73). this classification proves 'a last greedy skip exists' equivalent to '1/2 is not in the Mersenne achievement set'; the hypothesis is therefore one branch of the open endpoint and has no producer.
- incoming **depends_on_open**: [Z14::final_middle_producer_must_violate_tail_inequality](BROWSER_Z14_1.md#node-ebba9d2041f7e4d5). the all-right / eventually-right suffix hypothesis is proved by this classification to be equivalent to '1/2 is not in the Mersenne achievement set'; it is the negation of the open endpoint, assumed only for contradiction, so it has no producer and the conclusion is vacuous if 1/2 is achieved.
- incoming **depends_on_open**: [Z14::middle_then_allright_fatal_gap_and_landing_window](BROWSER_Z14_1.md#node-0dc309f47c5d501b). the all-right / eventually-right suffix hypothesis is proved by this classification to be equivalent to '1/2 is not in the Mersenne achievement set'; it is the negation of the open endpoint, assumed only for contradiction, so it has no producer and the conclusion is vacuous if 1/2 is achieved.
- incoming **depends_on_open**: [Z14::eventual_right_tail_positive_excess](BROWSER_Z14_1.md#node-74f3147f9b2cd1a2). the all-right / eventually-right suffix hypothesis is proved by this classification to be equivalent to '1/2 is not in the Mersenne achievement set'; it is the negation of the open endpoint, assumed only for contradiction, so it has no producer and the conclusion is vacuous if 1/2 is achieved.
- incoming **depends_on_open**: [Z14::final_middle_neg_two_phase_sieve](BROWSER_Z14_1.md#node-fc1fd4c59765a70d). the all-right / eventually-right suffix hypothesis is proved by this classification to be equivalent to '1/2 is not in the Mersenne achievement set'; it is the negation of the open endpoint, assumed only for contradiction, so it has no producer and the conclusion is vacuous if 1/2 is achieved.
- incoming **depends_on_open**: [Z14::last_false_terminal_exists_for_eventual_right](BROWSER_Z14_1.md#node-3e8c0e7754812bff). the all-right / eventually-right suffix hypothesis is proved by this classification to be equivalent to '1/2 is not in the Mersenne achievement set'; it is the negation of the open endpoint, assumed only for contradiction, so it has no producer and the conclusion is vacuous if 1/2 is achieved.
- outgoing **alias_of**: [Z12::half_membership_seam_equivalence_ring](BROWSER_Z12_1.md#node-c98bead16d978fce). Z13's `seamGreedyEventuallyRight_iff_half_not_mem` and Z12's `half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight` are the same equivalence up to negation; both rings pivot on (1/2 : R) in mersenneAchievementSet and both carry the last-skip and fatal-gap coordinates.

<a id="node-b672d53f73e0ea3c"></a>
## finite_shadow_square_root_strip

Every admissible finite half word at depth N has its Mersenne support sum within (4*sqrt(N)+8)/2^N of one half, via the exact identity that the discrepancy equals the terminal integer half carry minus the future-multiple coefficient tail scaled by 2^N; the coefficient tail itself is below 2*sqrt(N)+3.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [halfStripAdmissible_residual_eq](../../Erdos249257/HalfCylinderFiniteShadow.lean#L55)
- Lean declaration: [halfStripAdmissible_abs_residual_le](../../Erdos249257/HalfCylinderFiniteShadow.lean#L549)
- Lean declaration: [binaryCoeffTail_supportCoeff_lt_two_natSqrt_add_three](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L43)

- outgoing **implies**: [Z13::skipped_endpoint_trichotomy](BROWSER_Z13_2.md#node-b0a9f7595464c220). The square-root strip bound is what confines the negative-cell seam remainder to halfStripBound (2n).
- outgoing **reformulates**: [Z12::integer_half_carry_calculus](BROWSER_Z12_1.md#node-59e84eab60406093). halfStripAdmissible_residual_eq is the same discrepancy identity read on admissible finite words: terminal integer half carry minus the scaled future-multiple coefficient tail.
- outgoing **specialises**: [Z12::terminal_only_strip_error_bound](BROWSER_Z12_2.md#node-49a575b75a3059eb). Z12's `dist_half_erdosSupportSeries_wordSupport_le_carry_add_tail` (TerminalOnlyScaledVanishing.lean:24) bounds |1/2 - value| by (|terminal carry| + 2 sqrt M + 4)/2^M using the terminal carry alone; Z13's `halfStripAdmissible_abs_residual_le` (HalfCylinderFiniteShadow.lean:532) is that bound under the strictly stronger HalfStripAdmissible hypothesis, which pins every prefix carry.

<a id="node-01e83e38a5f70b05"></a>
## finite_window_reduction_of_raw_half_residual

For any support avoiding one, a finite divisor-incidence inequality at depth n (the centered half carry lies below the first J rows of the analytic tail) forces the normalised distance of the support value from 1/2 to be at most one; the finite window is a strict truncation of the complete tail, and for frozen prefixes the inequality is exactly the future-skip coverage condition.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hwindow : (mobiusCenteredHalfCarry A (n - 1) : R) <= finiteCoeffWindow A n J -- no proof that this holds on every actual greedy prefix"]

- Lean declaration: [scaledHalfResidual_le_one_of_finiteCoeffWindow](../../Erdos249257/HalfCylinderFiniteShadow.lean#L128)
- Lean declaration: [rawHalfSlack_nonneg_of_finiteCoeffWindow](../../Erdos249257/HalfCylinderFiniteShadow.lean#L145)
- Lean declaration: [scaledPrefixHalfResidual_le_one_of_terminal_le_skipCapacity](../../Erdos249257/HalfCylinderFiniteShadow.lean#L527)

- outgoing **depends_on_open**: [Z13::future_skip_capacity_factorization](BROWSER_Z13_1.md#node-ed5b66275f261817). The sufficient window hypothesis is exactly future-skip coverage for frozen prefixes.
- outgoing **depends_on_open**: [Z12::greedy_mobius_carry_nonneg](BROWSER_Z12_1.md#node-8167d9ef9c6a66a9). the only unconditional control on the actual greedy Moebius-centred carry; it supplies the LOWER half of the strip, while the hypothesis needs the upper bound (carry below the finite coefficient window), which that node explicitly records as open.

<a id="node-4a9ba5a6aa98cb82"></a>
## first_feedback_child_carry_algebra

Given two boundary parents with carries delta and delta+1 whose first feedback coefficients at row 2s are c+1 and c, the four zero/one children have carries H-1, H-2, H+2 and H+1 where H = 2*delta - c; and these hypotheses can themselves be supplied from the pre-feedback gauge data.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [firstFeedbackChildCarries](../../Erdos249257/HalfCylinderFiniteShadow.lean#L674)
- Lean declaration: [firstFeedbackChildCarries_of_preFeedbackGauge](../../Erdos249257/HalfCylinderFiniteShadow.lean#L718)

- incoming **barrier_for**: [Z13::pre_feedback_gauge_symmetry_barrier](BROWSER_Z13_1.md#node-eb676d955c172503). The corpus reads pre-feedback gauge symmetry as the informal reason to seek a contradiction at or beyond the first feedback row that the second node computes; the non-derivability itself is not formalised, so the first node is recorded as an unconditional carry identity rather than a barrier.

<a id="node-f942af3456eb9342"></a>
## first_wrap_defect_reduction_to_one_integer_remainder

For every row s at least three, some Boolean divisor incidence word produces a first-wrap seam defect inside the square-root half-carry strip if and only if the single deterministic descending-greedy remainder at that row is positive and inside that strip. The search over exponentially many words collapses to one integer sequence.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seam_smallPositiveDefect_iff_integerGreedyRemainder](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L654)

- outgoing **specialises**: [Z13::abstract_greedy_optimality_and_small_defect_equivalence](BROWSER_Z13_1.md#node-64ee0481167c5f3c). The seam reduction is the abstract small-defect equivalence instantiated at the truncated Mersenne weights with B = halfStripBound (2s).
- outgoing **depends_on_open**: [Z13::seam_weight_gap_domination](BROWSER_Z13_2.md#node-ebf525fa9d65a41e). The instantiation needs the quantitative 2^(s+1) domination gap, which is the preceding node.

<a id="node-d2f322ed79845969"></a>
## frozen_margin_first_passage_iff_negative_dyadic_excess

At every positive depth k the frozen margin recurrence eventually becomes nonnegative for some horizon J if and only if the landed dyadic excess numerator at k is strictly negative. The horizon supplied is not bounded by the first shell k+1.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [exists_greedyHalfFrozenMargin_nonneg_iff_excess_neg](../../Erdos249257/HalfCylinderFiniteShadow.lean#L1229)

- outgoing **barrier_for**: [Z13::half_membership_from_frozen_margin_sockets](BROWSER_Z13_1.md#node-0b364ae5b3109540). Unconditional first passage is proved but with an unbounded horizon, while the governed socket demands horizon at most k+1; the gap between the two is the open content.

<a id="node-bfe65dfecdb51085"></a>
## frozen_margin_integer_recurrence

The frozen margin M(k,J) is a purely integer recurrence M(k,J+1) = 2*M(k,J) + (divisor count of row k+J+2 in the frozen greedy prefix) started at minus the centered half carry; after normalisation it equals 2^J times (finite coefficient window minus centered carry), it is nonnegative exactly when that window covers the carry, nonnegativity persists once reached, and at an actual skipped rank inside the first shell it equals actual future-skip capacity minus the actual terminal carry.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [greedyHalfFrozenMargin_succ](../../Erdos249257/HalfCylinderFiniteShadow.lean#L1054)
- Lean declaration: [greedyHalfFrozenMargin_cast_eq_pow_mul_window_sub_carry](../../Erdos249257/HalfCylinderFiniteShadow.lean#L1065)
- Lean declaration: [greedyHalfFrozenMargin_nonneg_iff_window_covers](../../Erdos249257/HalfCylinderFiniteShadow.lean#L1090)
- Lean declaration: [greedyHalfFrozenMargin_eq_actual_skip_margin](../../Erdos249257/HalfCylinderFiniteShadow.lean#L1120)

- incoming **reformulates**: [Z13::future_skip_capacity_factorization](BROWSER_Z13_1.md#node-ed5b66275f261817). The frozen margin is the integer form of future-skip capacity minus terminal carry at an actual skipped rank.

<a id="node-287d59e425cc9ca6"></a>
## full_shell_margin_equals_integer_seam_defect

At the full first shell J = n, the frozen margin is exactly the signed integer seam subset-sum defect: selected truncated weight sum minus seam subset target. In analytic form it is the amplified dyadic safety slack minus the coefficient tail still pending after row 2(k+1). This identifies the analytic and integer coordinates exactly.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [frozenMargin_fullShell_eq_stemTruncatedSum_sub_target](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L151)
- Lean declaration: [greedyHalfFrozenMargin_fullShell_eq_stemTruncatedSum_sub_target](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L240)
- Lean declaration: [greedyHalfFrozenMargin_fullShell_cast_eq_slack_sub_tail](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L252)
- Lean declaration: [greedyHalfFrozenMargin_fullShell_eq_actualOldSum_sub_target](../../Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L110)

- outgoing **equivalent_to**: [Z13::actual_seam_hole_equals_integer_subset_sum_defect](BROWSER_Z13_1.md#node-c1a58e98f65e57f9). At the full first shell the analytic frozen margin and the integer seam hole are the same signed quantity.
- incoming **depends_on_open**: [Z13::skipped_endpoint_trichotomy](BROWSER_Z13_2.md#node-b0a9f7595464c220). The trichotomy is read off the full-shell identity together with gap domination.

<a id="node-ed5b66275f261817"></a>
## future_skip_capacity_factorization

Freezing the support at depth n, the weighted frozen incidence surplus over any window J at most n equals exactly the binary capacity of the actual future skips minus the actual centered carry at the end of the window; hence window coverage is exactly terminal-carry coverage by the skip word, is exactly the reduced tail-tax inequality in reduced coordinates (E,D), persists at every later time inside the first shell, and one sufficiently early actual skip already establishes it.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [futureSkipCapacity_factorization](../../Erdos249257/HalfCylinderFiniteShadow.lean#L228)
- Lean declaration: [finiteCoeffWindow_covers_iff_terminal_le_skipCapacity](../../Erdos249257/HalfCylinderFiniteShadow.lean#L299)
- Lean declaration: [futureSkipCapacityMargin_eq_reducedTailTax](../../Erdos249257/HalfCylinderFiniteShadow.lean#L361)
- Lean declaration: [futureSkipCoverage_persistent](../../Erdos249257/HalfCylinderFiniteShadow.lean#L468)
- Lean declaration: [finiteCoeffWindow_covers_of_one_future_skip](../../Erdos249257/HalfCylinderFiniteShadow.lean#L509)

- outgoing **reformulates**: [Z13::frozen_margin_integer_recurrence](BROWSER_Z13_1.md#node-bfe65dfecdb51085). The frozen margin is the integer form of future-skip capacity minus terminal carry at an actual skipped rank.
- incoming **depends_on_open**: [Z13::finite_window_reduction_of_raw_half_residual](BROWSER_Z13_1.md#node-01e83e38a5f70b05). The sufficient window hypothesis is exactly future-skip coverage for frozen prefixes.

<a id="node-0b364ae5b3109540"></a>
## half_membership_from_frozen_margin_sockets

Four named but unproved propositions each imply that 1/2 lies in the Mersenne achievement set: a governed frozen-margin producer (first nonnegative margin by horizon k+1 at every skipped rank), full-shell nonnegativity at every skipped rank, seam-alignment-zero at every skipped aligned rank, and skip-conditioned seam escape (integer greedy remainder above the square-root strip at every skipped rank). Seam escape implies full-shell nonnegativity, which is equivalent to alignment-zero, which implies the governed producer.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["HalfGreedyGovernedFrozenMarginProducer : forall k, not (mersenneWeight (k+1) <= greedyMersenneRemainder (1/2) k) -> exists J <= k+1, 0 <= greedyHalfFrozenMargin k J", "HalfGreedySkippedFullShellNonnegative : forall n >= 3, not (mersenneWeight n <= greedyMersenneRemainder (1/2) (n-1)) -> 0 <= greedyHalfFrozenMargin (n-1) n", "HalfGreedySkippedSeamAlignmentZero : forall n >= 3, skip at n -> stemBits n (halfGreedyPrefixSupport (n-1)) = integerGreedyBits (seamWeights n) (seamSubsetTarget n) -> seamIntegerGreedyRemainder n = 0", "HalfGreedySkippedSeamEscape : forall n >= 3, skip at n -> halfStripBound (2*n) < seamIntegerGreedyRemainder n"]

- Lean declaration: [half_mem_mersenneAchievementSet_of_governedFrozenMarginProducer](../../Erdos249257/HalfCylinderFiniteShadow.lean#L1275)
- Lean declaration: [half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L633)
- Lean declaration: [half_mem_mersenneAchievementSet_of_skippedSeamAlignmentZero](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L678)
- Lean declaration: [half_mem_mersenneAchievementSet_of_skippedSeamEscape](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L722)
- Lean declaration: [governedFrozenMarginProducer_of_skippedSeamEscape](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L695)

- outgoing **depends_on_open**: [Z13::skipped_endpoint_trichotomy](BROWSER_Z13_2.md#node-b0a9f7595464c220). Every socket in the node is the demand that the negative-margin cell of the trichotomy never occurs at an actual skip.
- incoming **alias_of**: [Z13::seam_alignment_zero_iff_full_shell_nonnegative](BROWSER_Z13_1.md#node-10cecc60d9d40bec). Two of the four sockets are proved to be the same proposition, so they are not independent routes.
- incoming **barrier_for**: [Z13::take_forces_negative_full_shell_margin](BROWSER_Z13_2.md#node-7bc36910131bf033). It supplies only the easy direction of the sign dichotomy; the socket is precisely the unproved converse.
- incoming **barrier_for**: [Z13::frozen_margin_first_passage_iff_negative_dyadic_excess](BROWSER_Z13_1.md#node-d2f322ed79845969). Unconditional first passage is proved but with an unbounded horizon, while the governed socket demands horizon at most k+1; the gap between the two is the open content.
- outgoing **transport_of**: [Z12::channel_cap_skip_transport](BROWSER_Z12_1.md#node-3b04a5f99d781f94). half_mem_mersenneAchievementSet_of_governedFrozenMarginProducer routes the frozen-margin first passage into the same dyadic-cap consumer; greedyHalfFrozenMargin_nonneg_iff_window_covers is the integer coordinate of that cap inequality.

<a id="node-31f5cf394cc9250d"></a>
## half_membership_iff_every_skip_survives

A skipped rank is the last skipped rank exactly when its post-decision residual already exceeds the entire remaining Mersenne tail; therefore 1/2 lies in the Mersenne achievement set if and only if at every actual skipped rank the greedy residual stays at or below the complete remaining tail.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [isLastHalfGreedySkip_iff_skip_and_fatal](../../Erdos249257/HalfCylinderFixedTailSocket.lean#L22)
- Lean declaration: [no_lastHalfGreedySkip_iff_every_skip_survives](../../Erdos249257/HalfCylinderFixedTailSocket.lean#L57)
- Lean declaration: [half_mem_iff_every_actual_skip_survives](../../Erdos249257/HalfCylinderFixedTailSocket.lean#L73)

- outgoing **reformulates**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). Both restate half-membership; the fixed-tail form is the rank-local version of the last-skip clause.
- outgoing **equivalent_to**: [Z12::half_membership_iff_infinite_greedy_skips](BROWSER_Z12_1.md#node-f4d02068c1837778). half_mem_iff_every_actual_skip_survives (HalfCylinderFixedTailSocket.lean) and half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite (GreedyAchievementSet.lean) are two iffs with the same left side, linked by isLastHalfGreedySkip_iff_skip_and_fatal.
- outgoing **alias_of**: [Z12::half_membership_iff_infinite_greedy_skips](BROWSER_Z12_1.md#node-f4d02068c1837778). Z13's `no_lastHalfGreedySkip_iff_every_skip_survives` plus `half_mem_iff_every_actual_skip_survives` and Z12's `half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite` characterise the same membership through the same greedy orbit; Z12's `half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip` supplies the identification of the two coordinates.

<a id="node-7dcf61556232a9ef"></a>
## largest_false_rank_branch_transport

Having a named largest false rank is exactly the decomposition into a fixed lower prefix plus the filled interval above it; appending false makes the old terminal rank the new largest false rank, appending true preserves the existing one; and on the concrete seam the upper and middle branches reset the largest false rank to the old terminal rank while the right branch preserves it.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix](../../Erdos249257/HalfCylinderLargestSkipGap.lean#L42)
- Lean declaration: [seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle](../../Erdos249257/HalfCylinderLargestSkipGap.lean#L328)
- Lean declaration: [IsLargestFalseRank.seamGreedyWord_succ_of_rightBranch](../../Erdos249257/HalfCylinderLargestSkipGap.lean#L339)

- incoming **finite_instance_of**: [Z13::row_fourteen_late_base_computation](BROWSER_Z13_1.md#node-347c0456ef74af05). It exhibits one concrete row satisfying the late largest-false-rank invariant that the branch transport propagates.
- incoming **generalises**: [Z13::seam_word_adjacency_and_missing_rank_normal_form](BROWSER_Z13_2.md#node-b294bb7301a2e56c). The named largest-false-rank invariant is the parameterised form of the maximal-missing-rank decomposition.

<a id="node-396ba5097ca2833b"></a>
## largest_skip_late_step_socket_fan_in

If a late largest false rank can never cross the two-thirds boundary of the row without the concrete successor taking an upper or middle branch, then every row from fourteen onward has a late largest false rank, which supplies cofinal skipped seam ranks tending to infinity and therefore puts 1/2 in the Mersenne achievement set. The crossing statement itself is left unproved.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["LargestSkipLateStepSocket : forall s d, 14 <= s -> IsLargestFalseRank (seamGreedyWord s) d -> 2*s < 3*d -> 2*(s+1) < 3*d or SeamGreedyUpperOrMiddleAt s"]

- Lean declaration: [largestSkipLateAt_of_stepSocket](../../Erdos249257/HalfCylinderLargestSkipInduction.lean#L120)
- Lean declaration: [seamGreedyUnboundedSkippedRanksAlong_of_largestSkipLateStepSocket](../../Erdos249257/HalfCylinderLargestSkipInduction.lean#L130)
- Lean declaration: [half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket](../../Erdos249257/HalfCylinderLargestSkipInduction.lean#L167)

- outgoing **implies**: [Z13::unbounded_skipped_ranks_give_half_membership](BROWSER_Z13_2.md#node-0c099e1977615cd1). The late-invariant induction produces exactly the cofinal skipped-rank supply consumed there.
- outgoing **depends_on_open**: [Z13::row_fourteen_late_base_computation](BROWSER_Z13_1.md#node-347c0456ef74af05). The induction is anchored at the verified row-fourteen late base.
- incoming **barrier_for**: [Z13::right_branch_remainder_window](BROWSER_Z13_1.md#node-015a003e6df09663). It pins the remainder window a right branch would need, but does not prove that window empty; emptiness for the actual orbit is the socket.
- outgoing **depends_on_open**: [Z14::late_row_small_forces_middle_branch](BROWSER_Z14_1.md#node-dac65f9337a25754). the nearest unconditional law giving the socket's disjunct SeamGreedyUpperOrMiddleAt: a late row whose remainder is below its row index cannot take the upper branch and so takes the middle. It fires only under the row-small precondition, which is what the socket would itself have to establish, so it does not produce the socket.

<a id="node-62155a27fbeef138"></a>
## late_boundary_pulse_normalisation

Above a late largest skipped rank every filled suffix rank is too large to divide either new incidence index, so it has zero row pulse and the entire word pulse is carried by the prefix below d; at the first row where the late inequality fails, either 3d = 2s+1 with row pulse two, or 3d = 2s+2 with row pulse one.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [rowPulse_eq_zero_of_late_strictSuffix](../../Erdos249257/HalfCylinderBoundaryPulse.lean#L75)
- Lean declaration: [exists_lowerPrefix_wordPulse_eq_of_largestFalse_late](../../Erdos249257/HalfCylinderBoundaryPulse.lean#L85)
- Lean declaration: [rowPulse_boundary_of_late_firstCrossing](../../Erdos249257/HalfCylinderBoundaryPulse.lean#L150)

- outgoing **depends_on_open**: [Z13::right_branch_remainder_window](BROWSER_Z13_1.md#node-015a003e6df09663). The pulse budget in the carry threshold uses the fact that the filled late suffix is pulse invisible.

<a id="node-eb676d955c172503"></a>
## pre_feedback_gauge_symmetry_barrier

If two coefficient words agree up to the carry immediately before row s, the left word has one extra coefficient at row s, and the right word has one extra coefficient at every later row through n, then their integer half carries differ by exactly one at every row from s through n.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: RECLASSIFIED from barrier_no_go by adversarial audit: the Lean statement (preFeedbackGaugeSymmetry, HalfCylinderFiniteShadow.lean:588) is a positive carry identity and contains no non-derivability content. It does not state, in any form, that no contradiction can be derived from the local equations; that reading exists only in the docstring ('a contradiction must use information not represented by those local equations'). The theorem also shows carries are DETERMINED (they differ by exactly one), not underdetermined, and it exhibits no pair of realisable divisor supports both meeting the pattern - set-level divisor realisability is explicitly not addressed here (see first_feedback_child_carry_algebra). Even read informally the no-go covers only the interval from s to n under the carry recurrence plus the coefficient-difference pattern; it says nothing about divisor realisability, about rows beyond n, or about the first feedback row 2s, which is computed separately and is not gauge symmetric.

- Lean declaration: [preFeedbackGaugeSymmetry](../../Erdos249257/HalfCylinderFiniteShadow.lean#L605)

- outgoing **barrier_for**: [Z13::first_feedback_child_carry_algebra](BROWSER_Z13_1.md#node-4a9ba5a6aa98cb82). The corpus reads pre-feedback gauge symmetry as the informal reason to seek a contradiction at or beyond the first feedback row that the second node computes; the non-derivability itself is not formalised, so the first node is recorded as an unconditional carry identity rather than a barrier.

<a id="node-addccc13b529221f"></a>
## quarter_band_endpoint_cell_normal_forms

Arithmetic normal forms for the two non-carry branches: failure of the next-row upper bound on the middle branch is exactly occupancy of a unique multiple-of-four pulse cell at remainder H + k, and on the terminal-reset branch exactly occupancy of a 3H + k cell inside an interval fixed by the adjacent separation and the two pulses. The concrete seam specialisations take H = 2^(s-1).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [middleUpperFailure_iff_exists_pulseCell](../../Erdos249257/HalfCylinderQuarterBandEndpoints.lean#L21)
- Lean declaration: [rightUpperFailure_iff_exists_correctedPulseCell](../../Erdos249257/HalfCylinderQuarterBandEndpoints.lean#L62)
- Lean declaration: [seamAdjacentCut_middleNextUpperFailure_iff_pulseCell](../../Erdos249257/HalfCylinderQuarterBandEndpoints.lean#L153)
- Lean declaration: [seamAdjacentCut_rightNextUpperFailure_iff_pulseCell](../../Erdos249257/HalfCylinderQuarterBandEndpoints.lean#L175)

- outgoing **reformulates**: [Z13::quarter_band_escape_equivalence](BROWSER_Z13_1.md#node-74dbdf2575cb532c). Both describe when the updated residual fails to clear the target strip; the endpoint node names the failure cells explicitly.

<a id="node-74dbdf2575cb532c"></a>
## quarter_band_escape_equivalence

Under the middle-branch separation hypothesis, the two pulse-correlated quarter-band clauses are not merely sufficient for the updated residual to exceed a target bound: they are exactly equivalent to it.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [quarterBandEscape_iff_bound_lt_nextRemainder](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L1528)

- incoming **reformulates**: [Z13::quarter_band_endpoint_cell_normal_forms](BROWSER_Z13_1.md#node-addccc13b529221f). Both describe when the updated residual fails to clear the target strip; the endpoint node names the failure cells explicitly.

<a id="node-a81c11f42592eccc"></a>
## rational_take_comparison_in_floor_coordinates

Change of coordinates between the exact rational greedy state and the integer seam state: the signed defect of a word equals 4^s times its rational remainder minus 2^s plus its floor error, the corrected coordinate floorZ = defect minus floor error satisfies exact extension laws under appending a false or a true bit, and the real greedy take decision at rank s holds exactly when floorZ reaches the threshold 2^s/(2^s - 1).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [wordDefect_eq_scaledRemainder_sub_pow_add_floorError](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L836)
- Lean declaration: [seamWord_take_iff_floorZ](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L855)
- Lean declaration: [seamWordFloorZ_extend_false](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L972)
- Lean declaration: [seamWordFloorZ_extend_true](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L983)
- Lean declaration: [seamGreedyFloorZ_eq_remainder_sub_error](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L1006)

- outgoing **depends_on_open**: [Z13::seam_floor_error_envelope](BROWSER_Z13_2.md#node-36d0fd3cb8f527aa). The corrected coordinate is only usable because the floor error is bounded by the envelope node.
- incoming **specialises**: [Z13::reset_sockets_in_output_floor_coordinates](BROWSER_Z13_1.md#node-1809f7f4db0e4a61). The reset sockets are the take comparison applied to the three concrete successor branches.
- outgoing **reformulates**: [Z10::greedy_take_predicate_equals_block_take_predicate](BROWSER_Z10_1.md#node-e3ae02f4c5975be1). seamWord_take_iff_floorZ (HalfCylinderFloorErrorReset.lean) states the same rank-s take decision in the corrected floor coordinate floorZ = defect - floor error; both are exact recoordinatisations of one greedy step.
- incoming **equivalent_to**: [Z14::tail_escape_equals_rational_take_decision](BROWSER_Z14_2.md#node-e2e6eddcff985890). middleProducer_carry_sub_tail_eq_four_mul_floorZ_sub_threshold and middleProducer_tail_lt_carry_iff_rational_take (HalfCylinderMiddleCarryLowerBound.lean) show the producer carry-minus-tail margin is four times the floorZ distance above exactly the take threshold of seamWord_take_iff_floorZ.

<a id="node-105d9051e0bb7665"></a>
## raw_dyadic_safety_does_not_force_seam_escape

An explicit witness shows that raw block-dyadic safety does not imply half-cylinder seam escape: the greedy state after taking rank three (support {2,3}, residual 1/42) is block-dyadically safe at the last predecessor before rank six, yet its scalar seam hole H=3 lies inside the strip of half width eight and is not even-seam reachable.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: A single low-rank witness. It rules out only the implication 'raw block-dyadic safety at a predecessor implies seam escape' as a general lemma. It does not show raw safety fails at large ranks, does not show the seam route is unusable, and gives no cofinal family of counterexamples. Additional audit caveat: the seam side of the witness enters as numeric literals. rankThree_rawSafe_but_seamNotEscaped asserts BlockDyadicSafeAt 1 21 5 (which is tied to the fixture residual 1/42) together with facts about the literals delta=2, c=1, k=3; no theorem in the corpus evaluates integerHalfCarry / supportCoeff on the actual {2,3} greedy state to those values (depth14_evenSeam_three_not_reachable is itself stated on the bare literals). The identification of the scalar seam data with the rank-three greedy state is therefore documentation-level, not machine-checked - it is arithmetically correct (integerHalfCarry {2,3} 4 = 2, supportCoeff {2} 6 = 1, so H = 2*2-1 = 3) but that check is not in Lean.

- Lean declaration: [greedyHalf_rankThree_prefix_fixture](../../Erdos249257/HalfCylinderFiniteShadow.lean#L837)
- Lean declaration: [rankThree_rawSafe_but_seamNotEscaped](../../Erdos249257/HalfCylinderFiniteShadow.lean#L862)

- outgoing **barrier_for**: [Z13::seam_hole_scalar_normal_forms](BROWSER_Z13_2.md#node-e36262c887b04903). The witness shows the scalar seam-escape criterion is strictly stronger than raw block-dyadic safety.
- incoming **repair_of**: [Z16::in_strip_two_sheet_split](BROWSER_Z16_1.md#node-31d4c25c3644fda8). The barrier's witness has scalar seam hole H = 3 lying inside the strip of half width eight, i.e. exactly the crossing case where the hole fails to escape. CylinderStage.feedbackAdvance_or_inStripTwoSheet proves that when the crossing hole stays inside the next strip the live words split into two exact endpoint cylinders rather than dying, so seam escape is not needed for the stage to survive.

<a id="node-dadf7a74f8a35d6f"></a>
## real_to_rational_greedy_prefix_bridge

The primitive prefix of the real greedy Mersenne support at depth n is exactly the finite rational greedy prefix at n; if the next real greedy decision is a skip the prefix does not change; hence at an actual skipped half-greedy rank the real support through k+1 is the landed rational support through k.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [primitivePrefix_greedyMersenneSupport_eq_prefixRat](../../Erdos249257/HalfCylinderFiniteShadow.lean#L915)
- Lean declaration: [primitivePrefix_greedyHalf_eq_halfGreedyPrefixSupport_of_skip](../../Erdos249257/HalfCylinderFiniteShadow.lean#L968)

- outgoing **depends_on_open**: [Z13::seam_word_support_and_actual_word_representation](BROWSER_Z13_2.md#node-1ee49acd5a2193bb). Both identify the actual real greedy orbit with a finite rational object usable by the seam machinery.
- outgoing **reformulates**: [Z12::greedy_rational_exactness](BROWSER_Z12_1.md#node-a57ea44d67021816). primitivePrefix_greedyMersenneSupport_eq_prefixRat is the set-level form of rational_greedy_take_iff_real: the real greedy prefix support at depth n is the finite rational greedy prefix.

<a id="node-1809f7f4db0e4a61"></a>
## reset_sockets_in_output_floor_coordinates

The upper and right greedy floor coordinates at row s+1 have exact closed forms in terms of row-s data, and consequently the two named but unproved reset inequalities SeamResetUAt and SeamResetRAt are equivalent to the same inequalities stated directly about the row-(s+1) corrected coordinate. Neither reset inequality is asserted.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamGreedyFloorZ_succ_upper](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L1095)
- Lean declaration: [seamGreedyFloorZ_succ_right](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L1131)
- Lean declaration: [seamResetUAt_iff_output_floorZ](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L1171)
- Lean declaration: [seamResetRAt_iff_output_floorZ](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L1185)

- outgoing **specialises**: [Z13::rational_take_comparison_in_floor_coordinates](BROWSER_Z13_1.md#node-a81c11f42592eccc). The reset sockets are the take comparison applied to the three concrete successor branches.

<a id="node-ab61c6e40afd5d3d"></a>
## right_branch_remainder_recurrence

On a right branch the seam greedy remainder obeys the exact recurrence rem(s+1) + 2^(s+1) + belowPulse(s) + 4 = 4*rem(s).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [rightBranch_remainder_succ_eq](../../Erdos249257/HalfCylinderResetDeficitEscape.lean#L218)

- incoming **specialises**: [Z13::deficit_run_length_law](BROWSER_Z13_1.md#node-d3989be3bc2bd747). The run law is the iterated right-branch recurrence compared with the quarter-point middle trigger.

<a id="node-015a003e6df09663"></a>
## right_branch_remainder_window

Two unconditional triggers pin the greedy remainder at a late largest-false-rank row: a remainder below a quarter of the doubled gap forces an upper or middle successor (this trigger needs no lateness hypothesis), and twelve times the remainder reaching the explicit gap-and-pulse budget forces the successor to carry. Together, a right branch at a row whose largest false rank d is late (2s < 3d) forces the remainder into one explicit interval bounded below by (2^(s+1)+4)/4 and above by the carry threshold. In addition, at any such late largest-false-rank row the remainder lies strictly below the exact late adjacent gap.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Three of the four evidence theorems (successorCarries_of_twelve_mul_remainder_ge, three_mul_remainder_lt_exactLateGap, rightBranch_remainder_window) carry the hypotheses IsLargestFalseRank (seamGreedyWord s) d and 2*s < 3*d. That regime hypothesis is a property of the ACTUAL deterministic seam word and is proved unconditionally only at s = 14 (row_fourteen_late_base_computation); for every s >= 15 it is supplied only by the unproved LargestSkipLateStepSocket via largestSkipLateAt_of_stepSocket. So the pinned window is an unconditional theorem about rows in the late regime, but the corpus does not prove that any row above fourteen is in that regime. Only upperOrMiddle_of_four_mul_remainder_lt applies at every row s >= 5.

- Lean declaration: [upperOrMiddle_of_four_mul_remainder_lt](../../Erdos249257/HalfCylinderResetDeficitEscape.lean#L79)
- Lean declaration: [successorCarries_of_twelve_mul_remainder_ge](../../Erdos249257/HalfCylinderResetDeficitEscape.lean#L150)
- Lean declaration: [three_mul_remainder_lt_exactLateGap](../../Erdos249257/HalfCylinderResetDeficitEscape.lean#L117)
- Lean declaration: [rightBranch_remainder_window](../../Erdos249257/HalfCylinderResetDeficitEscape.lean#L200)

- outgoing **depends_on_open**: [Z13::exact_late_rank_adjacent_gap](BROWSER_Z13_1.md#node-45b4e991db0c37aa). The window bounds are read off the division-free late adjacent-gap identity.
- outgoing **barrier_for**: [Z13::largest_skip_late_step_socket_fan_in](BROWSER_Z13_1.md#node-396ba5097ca2833b). It pins the remainder window a right branch would need, but does not prove that window empty; emptiness for the actual orbit is the socket.
- incoming **depends_on_open**: [Z13::late_boundary_pulse_normalisation](BROWSER_Z13_1.md#node-62155a27fbeef138). The pulse budget in the carry threshold uses the fact that the filled late suffix is pulse invisible.

<a id="node-347c0456ef74af05"></a>
## row_fourteen_late_base_computation

Verified computation at row fourteen: the twelve truncated Mersenne weights, the target 134201344, and the descending greedy bit word [T,T,F,F,T,T,F,F,F,F,F,F], from which the terminal rank thirteen is false and row fourteen has a late largest false rank.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [largestSkipLateAt_fourteen](../../Erdos249257/HalfCylinderLargestSkipInduction.lean#L73)
- Lean declaration: [integerGreedyBits_fourteen](../../Erdos249257/HalfCylinderLargestSkipInduction.lean#L65)

- incoming **depends_on_open**: [Z13::largest_skip_late_step_socket_fan_in](BROWSER_Z13_1.md#node-396ba5097ca2833b). The induction is anchored at the verified row-fourteen late base.
- outgoing **finite_instance_of**: [Z13::largest_false_rank_branch_transport](BROWSER_Z13_1.md#node-7dcf61556232a9ef). It exhibits one concrete row satisfying the late largest-false-rank invariant that the branch transport propagates.
- incoming **equivalent_to**: [Z14::seam_base_row_certificates](BROWSER_Z14_1.md#node-eec681960426ae88). lastProducer_integerGreedyBits_fourteen / lastProducer_seamWeights_fourteen and integerGreedyBits_fourteen certify the same row-14 evaluation: twelve truncated weights, target 134201344 and the descending greedy bit word.
- outgoing **finite_instance_of**: [Z14::forced_seam_ranks_two_three_six](BROWSER_Z14_1.md#node-0441fc71def3d138). the certified row-14 greedy word [T,T,F,F,T,T,F,F,F,F,F,F] over ranks 2..13 has ranks 2 and 3 taken, 4 and 5 skipped and 6 taken - the bottom forcing law evaluated at s = 14.
- outgoing **finite_instance_of**: [Z14::forced_seam_ranks_seven_through_twentysix](BROWSER_Z14_1.md#node-78e85936547e9667). the same certified word has rank 7 selected, which is exactly the law's first clause 'rank 7 is taken from row 14'; the computation is that clause's base instance.

<a id="node-10cecc60d9d40bec"></a>
## seam_alignment_zero_iff_full_shell_nonnegative

The word-level condition that an aligned skipped seam word has vanishing integer greedy remainder is exactly equivalent to the condition that the full-shell frozen margin is nonnegative at every genuine skipped rank. Both sides are unproved.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Both sides are unproved sockets: a grep over Erdos249257/ and ErdosProblems/ shows each Prop occurs only as a definition and as a theorem hypothesis, never as a conclusion. The iff therefore transports no unconditional content; it shows the two sockets are interchangeable, which is a reduction of the socket inventory, not progress on the object. Flagged is_restatement_of_open_problem in the same sense as Z06 endpoint_certificate_completeness (both sides unresolved). Note the weaker precise fact: neither side is known to be equivalent to Erdos #257 or to half-membership - each is only known to imply half-membership (see half_membership_from_frozen_margin_sockets), so this is a restatement at socket level, not a restatement of the open problem itself.

Open hypotheses: ["HalfGreedySkippedSeamAlignmentZero : forall n >= 3, (skip at n) -> stemBits n (halfGreedyPrefixSupport (n-1)) = integerGreedyBits (seamWeights n) (seamSubsetTarget n) -> seamIntegerGreedyRemainder n = 0 -- defined Erdos249257/HalfCylinderFullShellSeamBridge.lean:593, never discharged anywhere in the corpus", "HalfGreedySkippedFullShellNonnegative : forall n >= 3, (skip at n) -> 0 <= greedyHalfFrozenMargin (n-1) n -- defined Erdos249257/HalfCylinderFullShellSeamBridge.lean:604, never discharged anywhere in the corpus"]

- Lean declaration: [skippedSeamAlignmentZero_iff_skippedFullShellNonnegative](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L671)

- outgoing **alias_of**: [Z13::half_membership_from_frozen_margin_sockets](BROWSER_Z13_1.md#node-0b364ae5b3109540). Two of the four sockets are proved to be the same proposition, so they are not independent routes.

