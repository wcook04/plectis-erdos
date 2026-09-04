# Z14_1: Last-producer analysis: middle and upper carries, the final -2 cell and its phase sieve

[All problems and zones](BROWSER.md)

<a id="node-bc7d00b295f0c906"></a>
## centered_half_carry_nonnegativity_and_cofinite_obstruction

Two centred half-carry steps combine into one base-four step with forcing 2*supportCoeff(N+2) + supportCoeff(N+3) - 3, with an explicit finite closed form. Any support strictly below one half has nonnegative Mobius-centred carry at every level. A cofinite support supplies at least two forced divisors at row 2D+4, so a zero centred endpoint at row 2D+1 becomes strictly negative within two rows and hence cannot occur below one half.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half](../../Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L94)
- Lean declaration: [cofiniteRightTail_ne_zero_centeredEndpoint](../../Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L547)

- outgoing **implies**: [Z14::final_middle_cell_neg_three_impossible](BROWSER_Z14_1.md#node-ac791258420a5c17). The cofinite zero-endpoint obstruction is the engine of the -3 exclusion.

<a id="node-181ede821d8a3386"></a>
## dyadic_band_producer_gives_row_escape

If no upper reset charge at or after row thirteen ever lies in one of the linear-width bands below the relevant dyadic powers, then no endpoint after an upper reset and a right run is row-small, hence every seam remainder from row thirteen on is at least its row index, which is exactly the row-scale middle producer socket, and therefore one half lies in the Mersenne achievement set.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The only certified instance of the antecedent is row thirteen (seamUpperResetDyadicBandEscape_at_thirteen), and that certificate itself presupposes an unproved hypothesis, namely that row thirteen is an upper transition. No row of the cofinal range d >= 13 is verified.

Open hypotheses: ["SeamUpperResetDyadicBandEscape: for all d >= 13 with (seamAdjacentCut d).successorCarries and all j <= d, either 2^(d-j+1) < 4*overshoot + abovePulse or 4*overshoot + abovePulse + 2*(d+j) <= 2^(d-j+1)"]

- Lean declaration: [SeamUpperResetDyadicBandEscape.not_rowSmall_after_upperRightRun](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4579)
- Lean declaration: [SeamUpperResetDyadicBandEscape.remainder_ge_row](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4641)
- Lean declaration: [SeamUpperResetDyadicBandEscape.toMiddleProducerRowEscape](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4781)

- outgoing **implies**: [Z14::producer_socket_implication_ladder](BROWSER_Z14_1.md#node-0e3bca8eecce4759). The band hypothesis yields SeamMiddleProducerRowEscape, the strongest rung of the ladder.
- incoming **implies**: [Z14::exponential_barrier_propagation](BROWSER_Z14_1.md#node-07d76efcc486659d). Supplies the middle-ancestor half of the last-ancestor fan-in.
- incoming **implies**: [Z14::row_small_endpoint_reverse_classification](BROWSER_Z14_1.md#node-4b8cbfe162ed4daf). Supplies the upper-ancestor half: a row-small endpoint forces the reset charge into a danger band.
- incoming **finite_instance_of**: [Z14::upper_reset_band_escape_row_thirteen](BROWSER_Z14_2.md#node-e6113688d6d6369d). Verifies the unproved band hypothesis at the single row d = 13.
- incoming **implies**: [Z14::upper_reset_dyadic_band_geometry](BROWSER_Z14_2.md#node-5f0b5ebcc8e203ed). Reduces the band hypothesis to a quarter-scale overshoot exclusion with explicit linear pulse loss.
- incoming **finite_instance_of**: [Z13::upper_reset_band_escape_rows_13_to_30](BROWSER_Z13_2.md#node-f9a0ade9be7e30ef). the computation verifies, for d = 13..30 and all j <= d, precisely the disjunction SeamUpperResetDyadicBandEscape that this conditional assumes for all d >= 13; it is that hypothesis at eighteen bounded rows.
- outgoing **depends_on_open**: [Z13::upper_reset_band_escape_rows_13_to_30](BROWSER_Z13_2.md#node-f9a0ade9be7e30ef). the only producer of SeamUpperResetDyadicBandEscape anywhere: it verifies the disjunction for rows d = 13..30 and all j <= d, and stops there; the hypothesis quantifies over all d >= 13.

<a id="node-74f3147f9b2cd1a2"></a>
## eventual_right_tail_positive_excess

A row whose seam remainder is smaller than its row index must take a non-right branch. A right-only tail cannot start at or below its dyadic half point, so every row of an eventual right-extension tail satisfies 2^s < remainder; the signed excess above the dyadic half point then follows the exact base-four affine recurrence with the below pulse as its charge, and stays strictly positive.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Reclassified from unconditional_object_theorem on adversarial review: three of the four evidence declarations (allRightTail_forces_twoPow_lt_remainder, eventualRightTail_forces_twoPow_lt_remainder, eventualRightTail_positive_affineExcess) assume an all-right tail and are vacuous without it. Only seamRowSmall_upperOrMiddle (a row whose remainder is below its row index must take a non-right branch) is an unconditional fact about the actual seam.

Open hypotheses: ["all-right tail from a row S: for all s >= S, seamGreedyWord (s+1) = (seamGreedyWord s).extend true (equivalently, no upper or middle transition at any t >= s). Unproved for every S; it is the negation of the open endpoint remaining_open.half_value_membership."]

- Lean declaration: [seamRowSmall_upperOrMiddle](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2427)
- Lean declaration: [allRightTail_forces_twoPow_lt_remainder](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2439)
- Lean declaration: [eventualRightTail_forces_twoPow_lt_remainder](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2479)
- Lean declaration: [eventualRightTail_positive_affineExcess](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2515)

- outgoing **implies**: [Z14::middle_then_allright_fatal_gap_and_landing_window](BROWSER_Z14_1.md#node-0dc309f47c5d501b). Positivity of the signed excess anchors the landing-excess window.
- outgoing **depends_on_open**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). the all-right / eventually-right suffix hypothesis is proved by this classification to be equivalent to '1/2 is not in the Mersenne achievement set'; it is the negation of the open endpoint, assumed only for contradiction, so it has no producer and the conclusion is vacuous if 1/2 is achieved.

<a id="node-07d76efcc486659d"></a>
## exponential_barrier_propagation

A middle branch always sends the next remainder to at least the next row index, and if the source remainder is already at least its row it sends it above the exponential barrier 2^(s+1) + (s+1). Every subsequent right branch preserves that barrier, so a row-scale middle producer followed by any finite run of right successors can never end in a remainder smaller than its row.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [seamMiddleBranch_nextRemainder_ge_row](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2655)
- Lean declaration: [seamMiddleBranch_nextRemainder_ge_expBarrier](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2680)
- Lean declaration: [seamRightBranch_preserves_expBarrier](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2707)
- Lean declaration: [seamRightRun_preserves_expBarrier](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2742)
- Lean declaration: [seamMiddleThenRightRun_expBarrier](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2768)

- outgoing **implies**: [Z14::dyadic_band_producer_gives_row_escape](BROWSER_Z14_1.md#node-181ede821d8a3386). Supplies the middle-ancestor half of the last-ancestor fan-in.

<a id="node-ac791258420a5c17"></a>
## final_middle_cell_neg_three_impossible

A genuine middle transition at row D at least 13 whose signed coordinate 4*remainder - belowPulse - 4 equals -3 cannot be the last non-right transition of an eventually right seam: after completing every rank above D the Mobius-centred half carry is zero at row 2D+1, and two further cofinite coefficient rows drive it strictly negative, contradicting the nonnegativity forced by a value below one half.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Conclusion is False, so this is the unconditional negative fact that no row D >= 13 is simultaneously a genuine middle transition with coordinate -3 and followed only by right extensions; it is not vacuous. Scope: exactly one of the three exceptional middle cells. Cells -2 and -1, and the pure right-tail branch, are untouched, so no branch of the search is closed by it.

- Lean declaration: [middleProducer_neg_three_not_last](../../Erdos249257/HalfCylinderLastProducerContradiction.lean#L364)
- Lean declaration: [finalMiddleCell_neg_three_not_last](../../Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L587)

- incoming **implies**: [Z14::centered_half_carry_nonnegativity_and_cofinite_obstruction](BROWSER_Z14_1.md#node-bc7d00b295f0c906). The cofinite zero-endpoint obstruction is the engine of the -3 exclusion.
- incoming **implies**: [Z14::lazy_cofinite_tail_carry_translation](BROWSER_Z14_1.md#node-348aa5ef233f8e5b). Translates the finite -3 producer cell into centred carry zero at row 2D+1.

<a id="node-93a72faa00a660ff"></a>
## final_middle_cell_tail_thresholds

A support strictly below one half has future coefficient tail strictly below its integer carry at every level. For a lazy cofinite support with D at least 3 the tail is strictly below the finite producer charge plus four, so a final producer cell of -2 forces the lazy future coefficient tail below two and a cell of -1 forces it below three.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [binaryCoeffTail_union_Ioi_lt_producerCarry_add_four](../../Erdos249257/HalfCylinderFinalMiddleTailSocket.lean#L40)
- Lean declaration: [binaryCoeffTail_union_Ioi_lt_two_of_producerCarry_eq_neg_two](../../Erdos249257/HalfCylinderFinalMiddleTailSocket.lean#L56)
- Lean declaration: [binaryCoeffTail_union_Ioi_lt_three_of_producerCarry_eq_neg_one](../../Erdos249257/HalfCylinderFinalMiddleTailSocket.lean#L74)

- outgoing **specialises**: [Z14::lazy_cofinite_tail_carry_translation](BROWSER_Z14_1.md#node-348aa5ef233f8e5b). Quantitative projection of the same translation at the surviving cells -2 and -1.
- outgoing **implies**: [Z14::final_middle_neg_two_phase_sieve](BROWSER_Z14_1.md#node-fc1fd4c59765a70d). The tail-below-two threshold is exactly what the forced-rank divisor incidence contradicts.

<a id="node-fc1fd4c59765a70d"></a>
## final_middle_neg_two_phase_sieve

Given the forced ranks, four rows of the lazy support already outweigh charge two unless the last producer depth is 2 modulo 3, so a final middle -2 cell forces D = 2 mod 3. Using the forced ranks 2, 3, 6, 7 and 14 the depth is confined to five of the twenty-one joint 3-and-7 phases; rank 20 removes seven of the fifty 210-classes; rank 21 removes the whole phase 8 mod 21, leaving thirty-five classes modulo 210; rank 26 removes every class with D = 11 mod 13 and the 11-mod-21 slice of D = 10 mod 13.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: candidate_new_statement.

Scope: Reclassified from unconditional_object_theorem on adversarial review: every sieve step assumes both the all-right suffix and the -2 cell, so the modular constraints describe a hypothetical configuration and are vacuous if no such D exists. Row thresholds are not uniform: mod 3 and mod 21 need D >= 13, the first phase refinement D >= 20, the rank-21 refinement D >= 26 and the rank-26 refinement D >= 27. It restricts and does not eliminate the -2 cell (412 of 2730 residue classes survive), and it says nothing about the -1 cell or the pure right-tail branch.

Open hypotheses: ["all-right suffix hypothesis hright: for all s >= D+1, seamGreedyWord (s+1) = (seamGreedyWord s).extend true. Nothing in the corpus proves this for any D. By half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight it is the negation of the open proposition remaining_open.half_value_membership, so it is assumed only for contradiction and nobody intends to prove it; but the conclusion below is a statement about a hypothetical configuration and is vacuous if the seam is not eventually right. Here the hypothesis is joined by hcell (the final middle coordinate equals -2), which is likewise a property of a hypothetical last producer and is not known to hold at any row."]

- Lean declaration: [two_lt_binaryCoeffTail_union_Ioi_of_forced_two_three_six](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L67)
- Lean declaration: [finalMiddleCell_neg_two_forces_mod_three_two](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L698)
- Lean declaration: [finalMiddleCell_neg_two_forces_mod_twenty_one](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L1255)
- Lean declaration: [finalMiddleCell_neg_two_forces_phase_refinement](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L1400)
- Lean declaration: [finalMiddleCell_neg_two_forces_phase_refinement_through_twentyOne](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L1538)
- Lean declaration: [finalMiddleCell_neg_two_forces_phase_refinement_through_twentySix](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L1622)

- incoming **implies**: [Z14::final_middle_cell_tail_thresholds](BROWSER_Z14_1.md#node-93a72faa00a660ff). The tail-below-two threshold is exactly what the forced-rank divisor incidence contradicts.
- incoming **implies**: [Z14::forced_seam_ranks_seven_through_twentysix](BROWSER_Z14_1.md#node-78e85936547e9667). Each newly forced rank removes further residue classes from the sieve.
- incoming **implies**: [Z14::phase_indexed_below_pulse_lower_bounds](BROWSER_Z14_1.md#node-012adbedd84a85bc). The phase-indexed pulse lower bounds are the arithmetic content of each residue exclusion.
- incoming **finite_instance_of**: [Z14::final_middle_neg_two_survivor_count](BROWSER_Z14_1.md#node-b9aa63b7a3e101c3). Counts the joint residue classes left by the rank-26 refinement.
- outgoing **depends_on_open**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). the all-right / eventually-right suffix hypothesis is proved by this classification to be equivalent to '1/2 is not in the Mersenne achievement set'; it is the negation of the open endpoint, assumed only for contradiction, so it has no producer and the conclusion is vacuous if 1/2 is achieved.

<a id="node-b9aa63b7a3e101c3"></a>
## final_middle_neg_two_survivor_count

The residue classes surviving the rank-26 final-middle sieve, defined by D mod 21 in {11,14,17,20}, D mod 10 not 8, not (D mod 10 = 7 and D mod 21 = 11), D mod 13 not 11, and not (D mod 13 = 10 and D mod 21 = 11), number exactly 412 out of 2730.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: A pure Finset.range 2730 decision procedure, so unconditional as a count. It counts only the modular constraints of final_middle_neg_two_phase_sieve, which themselves hold only for a hypothetical last middle -2 producer at D >= 27 with an all-right suffix. Roughly one seventh of phases survive, so the sieve is far from empty.

- Lean declaration: [finalMiddleTwentySixPhaseSurvivors_card](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L1759)

- outgoing **finite_instance_of**: [Z14::final_middle_neg_two_phase_sieve](BROWSER_Z14_1.md#node-fc1fd4c59765a70d). Counts the joint residue classes left by the rank-26 refinement.

<a id="node-ebba9d2041f7e4d5"></a>
## final_middle_producer_must_violate_tail_inequality

If a genuine middle transition at row D at least 13 is followed only by right extensions, then its producer carry is strictly smaller than its complete future divisor-incidence tail, equivalently its corrected floor coordinate is strictly below the rational take threshold, equivalently the below word strictly skips its terminal Mersenne weight in the exact rational model. The strict reverse inequality is therefore the exact arithmetic signature that any hypothetical final middle producer must satisfy.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: candidate_new_statement.

Scope: Reclassified from unconditional_object_theorem on adversarial review: every evidence declaration carries hright, and unlike the *_not_last theorems the conclusion is not False, so the statement is about a hypothetical configuration and is vacuous unless the seam really is eventually right. Read correctly it is still the sharpest sceptical fact in the zone: in the only surviving scenario the tail-escape inequality is false at the last false row, so the sockets of half_membership_conditional_endpoints are not analytic slack conditions that a better majorant could reach. But it is not itself a barrier theorem: it does not show any socket unprovable, because in the complementary world (1/2 in the achievement set) its hypothesis never holds.

Open hypotheses: ["all-right suffix hypothesis hright: for all s >= D+1, seamGreedyWord (s+1) = (seamGreedyWord s).extend true. Nothing in the corpus proves this for any D. By half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight it is the negation of the open proposition remaining_open.half_value_membership, so it is assumed only for contradiction and nobody intends to prove it; but the conclusion below is a statement about a hypothetical configuration and is vacuous if the seam is not eventually right."]

- Lean declaration: [middleProducer_allRight_forces_carry_lt_tail](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1814)
- Lean declaration: [middleProducer_allRight_forces_floorZ_lt_takeThreshold](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1869)
- Lean declaration: [middleProducer_allRight_forces_rational_skip](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1888)

- outgoing **implies**: [Z14::tail_escape_equals_rational_take_decision](BROWSER_Z14_2.md#node-e2e6eddcff985890). Consumes the exact tail formula to give the reverse strict inequality at a hypothetical final middle producer.
- incoming **depends_on_open**: [Z14::half_membership_conditional_endpoints](BROWSER_Z14_1.md#node-c86b42e6bb40f03f). The socket is needed only at the single last-false row, where this unconditional theorem shows it is precisely the negation of the surviving configuration.
- incoming **implies**: [Z14::middle_then_allright_fatal_gap_and_landing_window](BROWSER_Z14_1.md#node-0dc309f47c5d501b). The same all-right limit strictly below one half gives both conclusions.
- incoming **depends_on_open**: [Z14::finite_prefix_cardinality_tail_socket](BROWSER_Z14_1.md#node-5ec892de64e49f7c). Failure of the cardinality inequality forces remainder < row, the same row-small regime the reverse classification then has to handle.
- outgoing **depends_on_open**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). the all-right / eventually-right suffix hypothesis is proved by this classification to be equivalent to '1/2 is not in the Mersenne achievement set'; it is the negation of the open endpoint, assumed only for contradiction, so it has no producer and the conclusion is vacuous if 1/2 is achieved.

<a id="node-5ec892de64e49f7c"></a>
## finite_prefix_cardinality_tail_socket

For a finite support F, each coefficient row counts at most card F divisors of F, so the whole normalised future divisor-incidence tail is at most card F. Hence the strict natural-number inequality card(below support) + belowPulse + 5 < 4*remainder says exactly that the producer carry exceeds the cardinality of the terminal-augmented support, and its failure forces the seam remainder to be strictly smaller than its row index.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [binaryCoeffTail_supportCoeff_coe_finset_le_card](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L222)
- Lean declaration: [middleProducer_card_lt_carry](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L292)
- Lean declaration: [middleProducer_not_cardEscape_forces_remainder_lt_row](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1747)

- outgoing **implies**: [Z14::producer_socket_implication_ladder](BROWSER_Z14_1.md#node-0e3bca8eecce4759). The cardinality tail bound is exactly what makes the cardinality socket imply the complete-tail socket.
- outgoing **depends_on_open**: [Z14::final_middle_producer_must_violate_tail_inequality](BROWSER_Z14_1.md#node-ebba9d2041f7e4d5). Failure of the cardinality inequality forces remainder < row, the same row-small regime the reverse classification then has to handle.

<a id="node-78e85936547e9667"></a>
## forced_seam_ranks_seven_through_twentysix

The forced initial segment extends: rank 7 is taken from row 14, ranks 8-13 skipped and rank 14 taken from row 20, ranks 15-19 skipped and rank 20 taken from row 21, rank 21 taken from row 26, ranks 22-25 skipped and rank 26 taken from row 27. Each step rests on an exact rational excess or deficit against one half with the dyadic side term fitting inside it.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [seamGreedyBits_head2367](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L552)
- Lean declaration: [seven_mem_seamGreedySupport](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L569)
- Lean declaration: [seamGreedy_postSeven_decisions_through_fourteen](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L151)
- Lean declaration: [seamGreedyBits_head2367_14](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L323)
- Lean declaration: [fourteen_mem_seamGreedySupport](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L347)
- Lean declaration: [seamGreedy_postFourteen_decisions_through_twenty](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L360)
- Lean declaration: [seamGreedyBits_head2367_14_20](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L544)
- Lean declaration: [twenty_mem_seamGreedySupport](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L569)
- Lean declaration: [seamGreedy_postTwenty_decision_twentyOne](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L581)
- Lean declaration: [seamGreedyBits_head2367_14_20_21](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L669)
- Lean declaration: [twentyOne_mem_seamGreedySupport](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L687)
- Lean declaration: [seamGreedy_postTwentyOne_decisions_through_twentySix](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L699)
- Lean declaration: [seamGreedyBits_head2367_14_20_21_26](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L899)
- Lean declaration: [twentySix_mem_seamGreedySupport](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L925)

- outgoing **generalises**: [Z14::forced_seam_ranks_two_three_six](BROWSER_Z14_1.md#node-0441fc71def3d138). Extends the forced initial segment from 2,3,6 to 2,3,6,7,14,20,21,26 at successively higher row thresholds.
- outgoing **implies**: [Z14::final_middle_neg_two_phase_sieve](BROWSER_Z14_1.md#node-fc1fd4c59765a70d). Each newly forced rank removes further residue classes from the sieve.
- incoming **finite_instance_of**: [Z13::row_fourteen_late_base_computation](BROWSER_Z13_1.md#node-347c0456ef74af05). the same certified word has rank 7 selected, which is exactly the law's first clause 'rank 7 is taken from row 14'; the computation is that clause's base instance.

<a id="node-0441fc71def3d138"></a>
## forced_seam_ranks_two_three_six

From row thirteen onward the descending greedy seam decisions are forced at the bottom: ranks 2 and 3 are taken, ranks 4 and 5 are skipped, rank 6 is taken. So ranks 2, 3 and 6 lie in every concrete seam word support from row thirteen on.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [seamGreedy_head236_decisions](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L398)
- Lean declaration: [seamGreedyBits_head236](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L487)
- Lean declaration: [two_three_six_mem_seamGreedySupport](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L596)

- incoming **generalises**: [Z14::forced_seam_ranks_seven_through_twentysix](BROWSER_Z14_1.md#node-78e85936547e9667). Extends the forced initial segment from 2,3,6 to 2,3,6,7,14,20,21,26 at successively higher row thresholds.
- incoming **finite_instance_of**: [Z13::row_fourteen_late_base_computation](BROWSER_Z13_1.md#node-347c0456ef74af05). the certified row-14 greedy word [T,T,F,F,T,T,F,F,F,F,F,F] over ranks 2..13 has ranks 2 and 3 taken, 4 and 5 skipped and 6 taken - the bottom forcing law evaluated at s = 14.

<a id="node-c86b42e6bb40f03f"></a>
## half_membership_conditional_endpoints

Each of the five unproved middle-producer sockets, and separately the unproved dyadic upper-reset band hypothesis, implies that one half lies in the Mersenne achievement set, which would refute universal Erdos #257.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: None of the six sockets is proved anywhere in the corpus, so no endpoint is established. Two sharpenings from this zone: (a) by tail_escape_equals_rational_take_decision the weakest socket is not an analytic majorant but exactly the rational greedy take decision at each late middle row, so no improvement of the tail majorants (square root, cardinality) can reach it; (b) by final_middle_producer_must_violate_tail_inequality every one of the six is false at the last false row in the eventual-right world, which is only the contrapositive of the reductions themselves and therefore adds no independent leverage. The five middle sockets are ordered Row => Card => Tail => ExceptNegThree and Sqrt => Tail, and the band socket implies Row, so each is at least as strong as the weakest one. Do not read this node as partial progress toward deciding half-membership.

Open hypotheses: ["SeamMiddleProducerTailEscape: for all s >= 13, at a genuine middle transition, binaryCoeffTail (supportCoeff (insert s belowSupport)) (2s+2) < producerCarry (insert s belowSupport) s", "SeamMiddleProducerTailEscapeExceptNegThree: the same, additionally assuming 4*remainder - belowPulse - 4 is not -3", "SeamMiddleProducerSqrtEscape: for all s >= 13, at a genuine middle transition, 2*sqrt(2s+2) + 4 < producerCarry (insert s belowSupport) s", "SeamMiddleProducerCardEscape: for all s >= 13, at a genuine middle transition, card(belowSupport) + belowPulse + 5 < 4*remainder", "SeamMiddleProducerRowEscape: for all s >= 13, at a genuine middle transition, s <= remainder", "SeamUpperResetDyadicBandEscape: for all d >= 13 with successorCarries and all j <= d, 2^(d-j+1) < 4*overshoot + abovePulse or 4*overshoot + abovePulse + 2*(d+j) <= 2^(d-j+1)"]

- Lean declaration: [half_mem_mersenneAchievementSet_of_middleProducerCardEscape](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2364)
- Lean declaration: [half_mem_mersenneAchievementSet_of_middleProducerRowEscape](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2371)
- Lean declaration: [half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4790)
- Lean declaration: [half_mem_mersenneAchievementSet_of_middleProducerTailEscapeExceptNegThree](../../Erdos249257/HalfCylinderLastProducerContradiction.lean#L436)
- Lean declaration: [half_mem_mersenneAchievementSet_of_middleProducerTailEscape](../../Erdos249257/HalfCylinderLastProducerContradiction.lean#L451)
- Lean declaration: [half_mem_mersenneAchievementSet_of_middleProducerSqrtEscape](../../Erdos249257/HalfCylinderLastProducerContradiction.lean#L458)

- outgoing **depends_on_open**: [Z14::final_middle_producer_must_violate_tail_inequality](BROWSER_Z14_1.md#node-ebba9d2041f7e4d5). The socket is needed only at the single last-false row, where this unconditional theorem shows it is precisely the negation of the surviving configuration.
- incoming **implies**: [Z14::producer_socket_implication_ladder](BROWSER_Z14_1.md#node-0e3bca8eecce4759). The ladder collapses all five middle sockets onto the same half-membership endpoint.
- incoming **implies**: [Z14::last_false_terminal_exists_for_eventual_right](BROWSER_Z14_1.md#node-3e8c0e7754812bff). Supplies the row D at which the upper / -3 / remaining-middle case split runs.
- outgoing **transport_of**: [Z12::half_membership_seam_equivalence_ring](BROWSER_Z12_1.md#node-c98bead16d978fce). The six middle-producer / band sockets are converted to the endpoint by last-false-terminal extraction against half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight; every one of them lands on that single open proposition.
- outgoing **depends_on_open**: [Z13::upper_reset_band_escape_rows_13_to_30](BROWSER_Z13_2.md#node-f9a0ade9be7e30ef). of the six sockets only SeamUpperResetDyadicBandEscape has any producer, and that producer verifies it for rows d = 13..30 only; the five middle-producer sockets have no producer anywhere.

<a id="node-3e8c0e7754812bff"></a>
## last_false_terminal_exists_for_eventual_right

If the integer seam is eventually right, then it has a last false terminal row D at least 13, with every strictly later terminal bit true and every later word a plain right extension. Row thirteen supplies the required false terminal.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Reclassified from unconditional_object_theorem on adversarial review: the hypothesis is a free unproved Prop. The only unconditional content is the base certificate that row thirteen has a false terminal (node seam_base_row_certificates).

Open hypotheses: ["SeamGreedyEventuallyRight: there is S >= 5 with seamGreedyWord (s+1) = (seamGreedyWord s).extend true for all s >= S. Unproved and unrefuted; it is exactly the negation of the open proposition remaining_open.half_value_membership, assumed for contradiction. The conclusion (existence of a last false terminal row D >= 13) is vacuous without it."]

- Lean declaration: [exists_last_false_terminal_of_eventuallyRight](../../Erdos249257/HalfCylinderLastProducerContradiction.lean#L227)

- outgoing **implies**: [Z14::half_membership_conditional_endpoints](BROWSER_Z14_1.md#node-c86b42e6bb40f03f). Supplies the row D at which the upper / -3 / remaining-middle case split runs.
- incoming **finite_instance_of**: [Z14::seam_base_row_certificates](BROWSER_Z14_1.md#node-eec681960426ae88). The row-13 and row-14 certificates supply the base false terminal that makes the bad set nonempty.
- outgoing **depends_on_open**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). the all-right / eventually-right suffix hypothesis is proved by this classification to be equivalent to '1/2 is not in the Mersenne achievement set'; it is the negation of the open endpoint, assumed only for contradiction, so it has no producer and the conclusion is vacuous if 1/2 is achieved.

<a id="node-2c026764d2f2a698"></a>
## late_gap_reset_middle_balance

In the late largest-false regime the upper reset charge E and the signed middle coordinate M satisfy the exact non-tautological balance E + M = 4G + rowPulse(s,d) - 4 with 3G = 3*2^(s+1) + 2*4^(s-d) + 4; at the first two-thirds crossing the offset is exactly 4G-2 or 4G-3 according to the parity cell. The signed distance of the reset charge from any dyadic boundary is a completely explicit affine expression in the remainder, the largest-false correction and the above pulse.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The late-regime hypotheses (IsLargestFalseRank (seamGreedyWord s) d together with 2*s < 3*d) are not known to hold cofinally: they are supplied only by the unproved LargestSkipLateStepSocket in Erdos249257/HalfCylinderLargestSkipInduction.lean, which no declaration in the corpus discharges. Each statement here is therefore an exact fact about any row that happens to be in the late regime, not a fact known to apply to cofinally many rows.

- Lean declaration: [exists_exactLateGap_upperResetCharge_add_middleCoordinate](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3062)
- Lean declaration: [exists_exactLateGap_upperResetCharge_add_middleCoordinate_firstCrossing](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3107)
- Lean declaration: [exists_exactLateGap_upperResetCharge_coordinate](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3236)
- Lean declaration: [three_mul_upperResetCharge_signedDistance_to_dyadic](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3255)
- Lean declaration: [upperResetCharge_signedDistance_eq_remainderBoundary](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3283)

- outgoing **specialises**: [Z14::late_largest_false_adjacent_cut_identification](BROWSER_Z14_1.md#node-f409d3c2bdc507ab). The same exact gap rewritten as an upper-reset / middle-coordinate charge balance.

<a id="node-f409d3c2bdc507ab"></a>
## late_largest_false_adjacent_cut_identification

At a late largest false rank d (2s < 3d) with the greedy support of the stated shape, the explicit largest-skip upper word is the actual minimal word above the seam target, its pulse is the below pulse plus the boundary row pulse, and the adjacent gap is exact: 3*(remainder + overshoot) = 3*2^(s+1) + 2*4^(s-d) + 4.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The late-regime hypotheses (IsLargestFalseRank (seamGreedyWord s) d together with 2*s < 3*d) are not known to hold cofinally: they are supplied only by the unproved LargestSkipLateStepSocket in Erdos249257/HalfCylinderLargestSkipInduction.lean, which no declaration in the corpus discharges. Each statement here is therefore an exact fact about any row that happens to be in the late regime, not a fact known to apply to cofinally many rows.

- Lean declaration: [seamAdjacentCut_above_eq_largestSkipUpperWord_of_support](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2858)
- Lean declaration: [seamAdjacentCut_abovePulse_eq_belowPulse_add_rowPulse_of_largestFalse_late](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2904)
- Lean declaration: [three_mul_remainder_add_overshoot_eq_exactLateGap](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2938)

- outgoing **implies**: [Z14::late_row_small_forces_middle_branch](BROWSER_Z14_1.md#node-dac65f9337a25754). The exact late adjacent gap is what excludes the upper branch at a row-small row.
- incoming **specialises**: [Z14::late_gap_reset_middle_balance](BROWSER_Z14_1.md#node-2c026764d2f2a698). The same exact gap rewritten as an upper-reset / middle-coordinate charge balance.

<a id="node-dac65f9337a25754"></a>
## late_row_small_forces_middle_branch

In the late largest-false regime a row whose remainder is smaller than its row index cannot take the upper branch, since the exact gap gives 2^(s+1) < remainder + overshoot while an upper carry would force both 4*remainder < 2^(s+1) and 4*overshoot at most 2^(s+1). It therefore takes the middle branch, and its successor's largest false rank resets to the old terminal rank, which is again late.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The late-regime hypotheses (IsLargestFalseRank (seamGreedyWord s) d together with 2*s < 3*d) are not known to hold cofinally: they are supplied only by the unproved LargestSkipLateStepSocket in Erdos249257/HalfCylinderLargestSkipInduction.lean, which no declaration in the corpus discharges. Each statement here is therefore an exact fact about any row that happens to be in the late regime, not a fact known to apply to cofinally many rows.

- Lean declaration: [seamRowSmall_not_successorCarries_of_largestFalse_late](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3138)
- Lean declaration: [seamRowSmall_middleBranch_of_largestFalse_late](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3167)
- Lean declaration: [largestSkipLateAt_succ_of_rowSmall](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3220)

- incoming **implies**: [Z14::late_largest_false_adjacent_cut_identification](BROWSER_Z14_1.md#node-f409d3c2bdc507ab). The exact late adjacent gap is what excludes the upper branch at a row-small row.
- incoming **depends_on_open**: [Z13::largest_skip_late_step_socket_fan_in](BROWSER_Z13_1.md#node-396ba5097ca2833b). the nearest unconditional law giving the socket's disjunct SeamGreedyUpperOrMiddleAt: a late row whose remainder is below its row index cannot take the upper branch and so takes the middle. It fires only under the row-small precondition, which is what the socket would itself have to establish, so it does not produce the socket.

<a id="node-348aa5ef233f8e5b"></a>
## lazy_cofinite_tail_carry_translation

Replacing the selected last rank D by the complete open right tail changes the producer-aligned integer carry by exactly four, and the Mobius-centred carry by exactly three; the lazy support value is the finite lower word's value plus the complete Mersenne tail above D. This transports the three finite middle cells to the cofinite centred-carry endpoint.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [integerHalfCarry_union_Ioi_eq_producerCarry_add_four](../../Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L270)
- Lean declaration: [mobiusCenteredHalfCarry_union_Ioi_eq_producerCarry_add_three](../../Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L468)
- Lean declaration: [positiveMersenneSupportValue_union_Ioi_eq_add_tail](../../Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L480)

- outgoing **implies**: [Z14::final_middle_cell_neg_three_impossible](BROWSER_Z14_1.md#node-ac791258420a5c17). Translates the finite -3 producer cell into centred carry zero at row 2D+1.
- incoming **specialises**: [Z14::final_middle_cell_tail_thresholds](BROWSER_Z14_1.md#node-93a72faa00a660ff). Quantitative projection of the same translation at the surviving cells -2 and -1.

<a id="node-8a3f9cd8c2c98051"></a>
## middle_cell_floor_absorption_bounds

In a middle cell 4*remainder = belowPulse + c the pulse part is already absorbed by the exact floor error, so 4*Z is at most c; on an actual middle transition this bounds the scaled rational residual of the successor word by 2^(s+2) + c.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamMiddleCell_four_mul_floorZ_le](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4142)
- Lean declaration: [seamMiddleCell_scaledRationalRemainder_le](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4167)

- outgoing **specialises**: [Z14::middle_landing_floor_error_identities](BROWSER_Z14_1.md#node-7ef6b806a805fdb9). Cell-labelled form of the same pulse absorption into the exact floor error.

<a id="node-7ef6b806a805fdb9"></a>
## middle_landing_floor_error_identities

The signed middle landing splits exactly as four times the corrected floor coordinate plus the next-row floor slack, and the complete divisor-incidence tail of the terminal-augmented below support equals the floor error of the false extension plus the terminal rank's own floor error. Both are identities, not majorants.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [middleLandingSignedExcess_eq_four_floorZ_add_nextFloorError](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L617)
- Lean declaration: [binaryCoeffTail_insert_seamBelowSupport_eq_nextFloorError](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1363)

- incoming **specialises**: [Z14::middle_cell_floor_absorption_bounds](BROWSER_Z14_1.md#node-8a3f9cd8c2c98051). Cell-labelled form of the same pulse absorption into the exact floor error.
- incoming **implies**: [Z14::pulse_and_floor_error_calculus](BROWSER_Z14_1.md#node-0908e622d22c1c87). Supplies the floor-error majorants used in the landing identity.

<a id="node-0dc309f47c5d501b"></a>
## middle_then_allright_fatal_gap_and_landing_window

A genuine middle landing at row D at least 13 followed by an all-right suffix has limiting lazy value strictly below one half, and its exact rational remainder is trapped strictly between the complete Mersenne tail above D and the single Mersenne weight at D. In the corrected floor coordinate the lower wall is 4^D*mersenneTail(D) - 2^D, whose exact value is 1/3 plus a positive higher-channel tail. Consequently the integer landing excess is at least two, and it is strictly below 2*sqrt(2D+2) + 8.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: candidate_new_statement.

Scope: Reclassified from unconditional_object_theorem on adversarial review: all five evidence declarations assume hright and conclude non-trivial inequalities, so the whole landing window is a description of a hypothetical surviving configuration and is vacuous if the seam is not eventually right. It narrows and does not empty the window, so it is not a barrier.

Open hypotheses: ["all-right suffix hypothesis hright: for all s >= D+1, seamGreedyWord (s+1) = (seamGreedyWord s).extend true. Nothing in the corpus proves this for any D. By half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight it is the negation of the open proposition remaining_open.half_value_membership, so it is assumed only for contradiction and nobody intends to prove it; but the conclusion below is a statement about a hypothetical configuration and is vacuous if the seam is not eventually right."]

- Lean declaration: [middleThenAllRight_limit_lt_half](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2175)
- Lean declaration: [middleThenAllRight_rationalRemainder_fatalGap](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2205)
- Lean declaration: [middleThenAllRight_floorZ_fatalGap](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2244)
- Lean declaration: [middleThenAllRight_landingExcess_two_le](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2319)
- Lean declaration: [middleProducer_allRight_landingExcess_window](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2547)

- incoming **implies**: [Z14::middle_then_allright_orbit_closed_forms](BROWSER_Z14_1.md#node-c83c4216cfe8468c). The closed forms are evaluated in the limit to produce the fatal gap.
- outgoing **implies**: [Z14::final_middle_producer_must_violate_tail_inequality](BROWSER_Z14_1.md#node-ebba9d2041f7e4d5). The same all-right limit strictly below one half gives both conclusions.
- incoming **implies**: [Z14::eventual_right_tail_positive_excess](BROWSER_Z14_1.md#node-74f3147f9b2cd1a2). Positivity of the signed excess anchors the landing-excess window.
- outgoing **depends_on_open**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). the all-right / eventually-right suffix hypothesis is proved by this classification to be equivalent to '1/2 is not in the Mersenne achievement set'; it is the negation of the open endpoint, assumed only for contradiction, so it has no producer and the conclusion is vacuous if 1/2 is achieved.

<a id="node-c83c4216cfe8468c"></a>
## middle_then_allright_orbit_closed_forms

Along an all-right suffix, and after a genuine middle landing, the exact rational residual, the corrected floor coordinate and the finite prefix value all have explicit closed forms: the residual loses exactly the consecutive Mersenne partial tail, the floor coordinate satisfies a base-four affine recurrence whose accumulated charge closes against 4^k times the initial value, and the finite value gains exactly the corresponding partial Mersenne tail.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Every closed form here assumes the all-right suffix hright (unproved, and the negation of the open endpoint); the identities are exact but describe an orbit that may not exist. Kept as representation_normalisation because they assert no new inequality.

- Lean declaration: [eventualRightTail_rationalRemainder_add_eq](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1938)
- Lean declaration: [eventualRightTail_floorZ_add_charge_eq](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1971)
- Lean declaration: [eventualRightTail_floorZ_add_eq_partialTail](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1998)
- Lean declaration: [middleThenAllRight_rationalRemainder_add_eq](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2026)
- Lean declaration: [middleThenAllRight_floorZ_add_charge_eq](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2055)
- Lean declaration: [middleThenAllRight_floorZ_eq_partialTail](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2078)
- Lean declaration: [middleThenAllRight_finiteValue_add_eq](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2105)

- outgoing **implies**: [Z14::middle_then_allright_fatal_gap_and_landing_window](BROWSER_Z14_1.md#node-0dc309f47c5d501b). The closed forms are evaluated in the limit to produce the fatal gap.

<a id="node-012adbedd84a85bc"></a>
## phase_indexed_below_pulse_lower_bounds

Explicit lower bounds for the below pulse of the adjacent cut in named residue classes: at least one always (from the permanently selected rank 2); at least two when s = 12 mod 13 or s = 9 mod 10; at least three when s = 1 or 2 mod 3, or s = 3 or 6 mod 7; at least six in the joint phases (1 mod 3, 9 mod 10, 3 or 6 mod 7) and (1 mod 3, 6 mod 7, 12 mod 13); at least seven when s = 10 mod 21.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [three_le_belowPulse_of_mod_three_one](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L59)
- Lean declaration: [three_le_belowPulse_of_mod_three_two](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L80)
- Lean declaration: [three_le_belowPulse_of_mod_seven_three](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L121)
- Lean declaration: [two_le_belowPulse_of_mod_thirteen_twelve](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L935)
- Lean declaration: [six_le_belowPulse_of_joint_phase_thirteen](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L961)
- Lean declaration: [two_le_belowPulse_of_mod_ten_nine](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L1026)
- Lean declaration: [one_le_belowPulse](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L1050)
- Lean declaration: [seven_le_belowPulse_of_mod_twentyOne_ten](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L1064)
- Lean declaration: [six_le_belowPulse_of_joint_phase](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L1119)
- Lean declaration: [three_le_belowPulse_of_mod_seven_six](../../Erdos249257/HalfFinalMiddlePhaseSieve.lean#L1208)

- outgoing **implies**: [Z14::final_middle_neg_two_phase_sieve](BROWSER_Z14_1.md#node-fc1fd4c59765a70d). The phase-indexed pulse lower bounds are the arithmetic content of each residue exclusion.

<a id="node-58512ec8c409376b"></a>
## producer_carry_concrete_seam_coordinates

Adjoining the terminal rank s to a concrete seam row word turns its signed integer subset-sum defect into the producer carry, equal to 4*(wordDefect - 1) - wordPulse. At the actual adjacent cut this is 4*remainder - belowPulse - 4 for the below word and -(4*overshoot + abovePulse + 4) for the above word.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [producerCarry_insert_seamWordSupport_eq](../../Erdos249257/HalfCylinderProducerLowerBound.lean#L105)
- Lean declaration: [producerCarry_insert_seamBelowSupport_eq_middleCoordinate](../../Erdos249257/HalfCylinderProducerLowerBound.lean#L150)
- Lean declaration: [producerCarry_insert_seamAboveSupport_eq_neg_upperCoordinate](../../Erdos249257/HalfCylinderProducerLowerBound.lean#L183)

- outgoing **specialises**: [Z14::producer_carry_exact_half_criterion](BROWSER_Z14_1.md#node-abd85fefcd4526c8). The abstract producer carry evaluated at the concrete adjacent-cut below and above supports.
- outgoing **reformulates**: [Z13::concrete_seam_greedy_one_step_recurrence](BROWSER_Z13_1.md#node-ee25eb717dc7da27). producerCarry_insert_seamBelowSupport_eq_middleCoordinate and _seamAboveSupport_eq_neg_upperCoordinate identify the producer carry of the adjacent-cut words with the middle and upper coordinates of the seam cut defined by seamAdjacentCut_remainder / seamAdjacentCut_nextRemainder.

<a id="node-abd85fefcd4526c8"></a>
## producer_carry_exact_half_criterion

For a support A of positive integers with 1 not in A and every element at most d, the distance of its Mersenne value from one half is exactly the producer-aligned integer carry minus the complete future divisor-incidence tail, divided by 2^(2d+2). Consequently the value lies strictly below one half exactly when that integer carry exceeds the tail, and strictly above exactly when the carry falls below the tail.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [producerCarry_residual_identity](../../Erdos249257/HalfCylinderProducerCarrySocket.lean#L27)
- Lean declaration: [producerCarry_gt_tail_iff_supportSeries_lt_half](../../Erdos249257/HalfCylinderProducerCarrySocket.lean#L48)
- Lean declaration: [producerCarry_lt_tail_iff_half_lt_supportSeries](../../Erdos249257/HalfCylinderProducerCarrySocket.lean#L78)

- incoming **specialises**: [Z14::producer_carry_concrete_seam_coordinates](BROWSER_Z14_1.md#node-58512ec8c409376b). The abstract producer carry evaluated at the concrete adjacent-cut below and above supports.
- incoming **reformulates**: [Z14::tail_escape_equals_rational_take_decision](BROWSER_Z14_2.md#node-e2e6eddcff985890). Rewrites the carry-versus-tail comparison in corrected floor coordinates and then as a rational greedy take decision.
- outgoing **reformulates**: [Z12::integer_half_carry_calculus](BROWSER_Z12_1.md#node-59e84eab60406093). producerCarry_residual_identity (HalfCylinderProducerCarrySocket.lean) and integerHalfCarry_eq_scaled_residual_add_tail (HalfCarryReachability.lean) are the same exact identity dist(value, 1/2) = (integer carry - coefficient tail)/2^depth at two depth normalisations (2d+2 vs N+1).
- outgoing **specialises**: [Z12::integer_half_carry_calculus](BROWSER_Z12_1.md#node-59e84eab60406093). `producerCarry A d` (HalfCylinderProducerCarrySocket.lean:20) and `integerHalfCarry A` (HalfCarryReachability.lean:36) are the same `affineBinaryOrbit (fun n => supportCoeff A (n+1)) 1`, so `producerCarry_residual_identity` is `integerHalfCarry_eq_scaled_residual_add_tail` at N = 2d+1 under the extra hypothesis A subset Iic d.

<a id="node-34ca9821b1e8f14e"></a>
## producer_carry_negative_forces_above_half

A negative producer carry forces the prefix value strictly above one half. A carry of at most -8 forces it above one half by more than a full Mersenne gap at rank d (for d at least 2), and hence replacing the top weight by the entire later Mersenne tail still leaves the value above one half.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [producerCarry_neg_forces_half_lt_supportSeries](../../Erdos249257/HalfCylinderProducerCarrySocket.lean#L145)
- Lean declaration: [producerCarry_le_neg_eight_forces_gap_margin](../../Erdos249257/HalfCylinderProducerCarrySocket.lean#L190)
- Lean declaration: [producerCarry_le_neg_eight_forces_belowTail_gt_half](../../Erdos249257/HalfCylinderProducerCarrySocket.lean#L234)

- outgoing **implies**: [Z14::upper_last_producer_impossible](BROWSER_Z14_2.md#node-adac92563d1572b8). The carry-at-most--8 Mersenne-gap margin is exactly the engine of the upper exclusion.

<a id="node-9abf5118817671e3"></a>
## producer_carry_positive_sufficient_conditions

If the producer carry of such a prefix exceeds 2*sqrt(2d+2) + 4, or (for d at least 1) exceeds 2d + 6, then the prefix value is strictly below one half.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The carry hypotheses (2*sqrt(2d+2)+4 < producerCarry, or 2d+6 < producerCarry) are explicit numerical side conditions on the given finite prefix, not corpus-level sockets, so the theorems are genuinely unconditional implications. But they are the pointwise form of SeamMiddleProducerSqrtEscape, and the corpus does not verify either inequality at a single late seam row.

- Lean declaration: [producerCarry_sqrt_sufficient](../../Erdos249257/HalfCylinderProducerCarrySocket.lean#L109)
- Lean declaration: [producerCarry_linear_sufficient](../../Erdos249257/HalfCylinderProducerCarrySocket.lean#L124)

- outgoing **implies**: [Z14::producer_socket_implication_ladder](BROWSER_Z14_1.md#node-0e3bca8eecce4759). The square-root socket enters the ladder through this sufficient condition.

<a id="node-0e3bca8eecce4759"></a>
## producer_socket_implication_ladder

The unproved middle-producer sockets are ordered: row-scale escape implies cardinality escape, which implies the exact complete-tail escape, which implies the tail escape away from the -3 cell; and the square-root escape also implies the exact tail escape. Each is a cofinal statement about every late genuine middle transition.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [SeamMiddleProducerRowEscape.toCardEscape](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1779)
- Lean declaration: [SeamMiddleProducerCardEscape.toTailEscape](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1790)
- Lean declaration: [SeamMiddleProducerTailEscape.toExceptNegThree](../../Erdos249257/HalfCylinderLastProducerContradiction.lean#L76)
- Lean declaration: [SeamMiddleProducerSqrtEscape.toTailEscape](../../Erdos249257/HalfCylinderLastProducerContradiction.lean#L98)

- incoming **implies**: [Z14::finite_prefix_cardinality_tail_socket](BROWSER_Z14_1.md#node-5ec892de64e49f7c). The cardinality tail bound is exactly what makes the cardinality socket imply the complete-tail socket.
- incoming **implies**: [Z14::producer_carry_positive_sufficient_conditions](BROWSER_Z14_1.md#node-9abf5118817671e3). The square-root socket enters the ladder through this sufficient condition.
- outgoing **implies**: [Z14::half_membership_conditional_endpoints](BROWSER_Z14_1.md#node-c86b42e6bb40f03f). The ladder collapses all five middle sockets onto the same half-membership endpoint.
- incoming **implies**: [Z14::dyadic_band_producer_gives_row_escape](BROWSER_Z14_1.md#node-181ede821d8a3386). The band hypothesis yields SeamMiddleProducerRowEscape, the strongest rung of the ladder.

<a id="node-0908e622d22c1c87"></a>
## pulse_and_floor_error_calculus

The accumulated pulse of a finite seam word is at most twice its number of selected ranks and at most four times its floor error, each row pulse being at most four times that rank's fractional floor error. The joint floor slack of the forced ranks 2, 3, 6 is exactly 31/63, 61/63 or 55/63 according to the row modulo three, and it is a lower bound for the false-extension slack; in the class s+1 = 0 mod 3 the total pulse is exactly three plus the pulse of the remaining ranks.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [wordPulse_le_two_mul_supportCard](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L330)
- Lean declaration: [wordPulse_le_four_mul_seamWordFloorError](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L364)
- Lean declaration: [seamRankFloorError_two_three_six_eq](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L645)
- Lean declaration: [wordPulse_eq_three_add_seamResidualPulse236](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L737)

- outgoing **implies**: [Z14::middle_landing_floor_error_identities](BROWSER_Z14_1.md#node-7ef6b806a805fdb9). Supplies the floor-error majorants used in the landing identity.

<a id="node-acdf5992da565f9f"></a>
## pure_half_prefix_normal_form

Running the descending integer greedy on the same seam weights at the unshifted half capacity 2^(2s-1) gives a single coordinate equal to 2^s - overshoot below the upper midpoint and 2^s + remainder above it; the two-sided dyadic bound is exactly the statement that this single coordinate is at most 2^(s+1).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamPureHalfPrefixRemainder_eq_ite](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4238)
- Lean declaration: [seamPureHalfPrefixRemainder_le_iff_twoSided](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4356)

- outgoing **reformulates**: [Z14::two_sided_dyadic_invariant_branch_propagation](BROWSER_Z14_2.md#node-e42073fa443bf061). Single-coordinate normal form of the same two-sided dyadic bound.

<a id="node-4b8cbfe162ed4daf"></a>
## row_small_endpoint_reverse_classification

After an upper reset and a run of k right steps, the endpoint remainder is smaller than its row index exactly when the base-four weighted reset-and-pulse charge sits in one explicit top window below the dyadic capacity. That forces an exponential lower bound on the upper reset charge itself, 2^(d-k+1) < 4*overshoot + abovePulse + 2*(d+k), and the same scaling identifies the scaled dyadic gap with the terminal middle coordinate plus the full affine pulse charge, so no congruence information is lost.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamUpperThenRightRun_scaledDyadicGap_eq_middleCoordinate_add_charge](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3672)
- Lean declaration: [seamUpperThenRightRun_rowSmall_forces_resetCylinder](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3771)
- Lean declaration: [seamUpperThenRightRun_rowSmall_iff_resetCylinderWindow](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3816)
- Lean declaration: [seamUpperThenRightRun_rowSmall_forces_resetCharge_lower](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3848)

- outgoing **implies**: [Z14::dyadic_band_producer_gives_row_escape](BROWSER_Z14_1.md#node-181ede821d8a3386). Supplies the upper-ancestor half: a row-small endpoint forces the reset charge into a danger band.
- incoming **implies**: [Z14::upper_reset_right_run_exact_cylinder](BROWSER_Z14_2.md#node-e0ae925f8e970c59). The exact dyadic cylinder identity is what turns row-smallness into a charge window.

<a id="node-eec681960426ae88"></a>
## seam_base_row_certificates

Explicit certified values at the base rows: the twelve seam weights and subset target at row 14, the greedy bit list at row 14, the false terminal at row 13, rank 13 not selected at row 14, the row-thirteen remainder at least 13, and the two-sided dyadic cut at row 5.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamTwoSidedDyadicAt_five](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4431)
- Lean declaration: [seamIntegerGreedyRemainder_thirteen_ge](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4627)
- Lean declaration: [thirteen_not_mem_seamGreedyWord_fourteen](../../Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4633)
- Lean declaration: [lastProducer_seamWeights_fourteen](../../Erdos249257/HalfCylinderLastProducerContradiction.lean#L135)
- Lean declaration: [lastProducer_seamSubsetTarget_fourteen](../../Erdos249257/HalfCylinderLastProducerContradiction.lean#L155)
- Lean declaration: [lastProducer_integerGreedyBits_fourteen](../../Erdos249257/HalfCylinderLastProducerContradiction.lean#L159)
- Lean declaration: [terminal_false_thirteen](../../Erdos249257/HalfCylinderLastProducerContradiction.lean#L216)

- outgoing **finite_instance_of**: [Z14::last_false_terminal_exists_for_eventual_right](BROWSER_Z14_1.md#node-3e8c0e7754812bff). The row-13 and row-14 certificates supply the base false terminal that makes the bad set nonempty.
- outgoing **equivalent_to**: [Z13::row_fourteen_late_base_computation](BROWSER_Z13_1.md#node-347c0456ef74af05). lastProducer_integerGreedyBits_fourteen / lastProducer_seamWeights_fourteen and integerGreedyBits_fourteen certify the same row-14 evaluation: twelve truncated weights, target 134201344 and the descending greedy bit word.
- outgoing **finite_instance_of**: [Z13::truncated_mersenne_weight_closed_forms](BROWSER_Z13_2.md#node-5f7575629a24a895). the twelve certified seam weights and subset target at row 14 are the closed-form truncated Mersenne integers 4^s/(2^d - 1) evaluated at s = 14 and d = 2..13.

