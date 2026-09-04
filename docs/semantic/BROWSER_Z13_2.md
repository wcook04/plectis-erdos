# Z13_2: Half-cylinder integer seam: greedy remainder, floor-error resets and the fatal-gap / right-tail classification

[All problems and zones](BROWSER.md)

<a id="node-36d0fd3cb8f527aa"></a>
## seam_floor_error_envelope

The rational error hidden by flooring each Mersenne weight is nonnegative, below one per rank, at most four sevenths per rank from rank two, and the total over an entire even truncation is at most sixty forty-ninths times sqrt(2h)-1, hence strictly below 2*sqrt(2h)+4; the floor error of any seam word is below the row width.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamRankFloorError_le_four_sevenths](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L285)
- Lean declaration: [evenTruncationFloorErrorEnvelope_le_sqrtCellBound](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L632)
- Lean declaration: [evenTruncationFloorErrorEnvelope_lt_two_sqrt_add_four](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L662)
- Lean declaration: [seamWordFloorError_lt_width](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L760)

- incoming **depends_on_open**: [Z13::rational_take_comparison_in_floor_coordinates](BROWSER_Z13_1.md#node-a81c11f42592eccc). The corrected coordinate is only usable because the floor error is bounded by the envelope node.

<a id="node-e36262c887b04903"></a>
## seam_hole_scalar_normal_forms

Scalar normal forms for the first-wrap endpoint: every fixed-coefficient child numerator is the affine expression 2T - c - k; the raw endpoint splits into an extended prefix boundary plus the seam hole 2*delta - c; for an actual Boolean stem the seam hole is one more than the row-2s carry of the left boundary word; an in-strip hole is a shifted zero-child carry; and full scalar reachability of the integer strip holds exactly when the hole misses the strip on one side.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [fixedCoeffNumeratorReachable_iff_endpoint](../../Erdos249257/HalfCylinderFiniteShadow.lean#L762)
- Lean declaration: [firstWrap_rawEndpoint_decomposition](../../Erdos249257/HalfCylinderFiniteShadow.lean#L776)
- Lean declaration: [actualFirstWrap_hole_eq_leftZeroCarry_add_one](../../Erdos249257/HalfCylinderFiniteShadow.lean#L786)
- Lean declaration: [evenSeam_fullIntegerStrip_iff_escape](../../Erdos249257/HalfCylinderFiniteShadow.lean#L824)

- incoming **barrier_for**: [Z13::raw_dyadic_safety_does_not_force_seam_escape](BROWSER_Z13_1.md#node-105d9051e0bb7665). The witness shows the scalar seam-escape criterion is strictly stronger than raw block-dyadic safety.
- incoming **depends_on_open**: [Z13::seam_hole_to_producer_carry_alignment](BROWSER_Z13_2.md#node-f46baf7bd8ad9f67). It advances the seam hole two coefficient rows into the producer-aligned carry coordinate.
- outgoing **reformulates**: [Z12::even_seam_one_hole_theorem](BROWSER_Z12_1.md#node-faa46a4f5d916b2a). evenSeam_fullIntegerStrip_iff_escape and fixedCoeffNumeratorReachable_iff_endpoint are the scalar normal forms of evenSeamReachable_iff / evenSeamReachable_in_strip_iff, with the same single hole 2*delta - c.

<a id="node-f46baf7bd8ad9f67"></a>
## seam_hole_to_producer_carry_alignment

For a left boundary support obtained by inserting the seam rank s into a stem, the producer-aligned carry equals four times the shifted seam hole minus the explicit paired incidence pulse at rows 2s+1 and 2s+2.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [producerCarry_insert_eq_four_mul_shiftedHole_sub_pulse](../../Erdos249257/HalfCylinderSeamProducerAlignment.lean#L24)

- outgoing **depends_on_open**: [Z13::seam_hole_scalar_normal_forms](BROWSER_Z13_2.md#node-e36262c887b04903). It advances the seam hole two coefficient rows into the producer-aligned carry coordinate.

<a id="node-d0e2aef10d6d2237"></a>
## seam_row_perturbation_affine_recurrence

Advancing the seam by one row is exactly affine: each old truncated weight quadruples plus its row pulse, the target quadruples plus 2^(s+1), the new terminal rank has weight 2^(s+2)+4, and hence the signed defect of any Boolean word satisfies defect(s+1) = 4*defect(s) + 2^(s+1) - pulse(s) - (terminal weight if the new bit is set).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [truncatedMersenneWeight_succ](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L1096)
- Lean declaration: [seamSubsetTarget_succ](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L1138)
- Lean declaration: [truncatedMersenneWeight_newRank](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L1154)
- Lean declaration: [wordDefect_succ](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L1225)

- outgoing **implies**: [Z13::adjacent_cut_three_branch_recurrence](BROWSER_Z13_1.md#node-d83a2249c9dda725). The affine row recurrence supplies the newSum = 4*oldSum + pulse structure that the abstract packet requires.

<a id="node-ebf525fa9d65a41e"></a>
## seam_weight_gap_domination

For s at least two the truncated Mersenne weights at row s are strictly superincreasing with an explicit margin: each weight exceeds the sum of all smaller weights by at least 2^(s+1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [truncatedMersenneWeight_dominanceGap](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L362)
- Lean declaration: [seamWeights_gapDominates](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L420)

- incoming **depends_on_open**: [Z13::first_wrap_defect_reduction_to_one_integer_remainder](BROWSER_Z13_1.md#node-f942af3456eb9342). The instantiation needs the quantitative 2^(s+1) domination gap, which is the preceding node.

<a id="node-b294bb7301a2e56c"></a>
## seam_word_adjacency_and_missing_rank_normal_form

In a gap-dominating word the two Boolean words prefix-false-all-true and prefix-true-all-false are adjacent in weighted-sum order, every equal-length word lying on one closed side; every seam greedy word from row five onward omits some rank (else the first three ranks alone exceed the target); and each such support is a finite prefix below its largest missing rank together with the completely filled interval above it.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [weightedBoolSum_adjacent_cut](../../Erdos249257/HalfCylinderFatalGapRightTail.lean#L52)
- Lean declaration: [seamGreedyWord_exists_false](../../Erdos249257/HalfCylinderFatalGapRightTail.lean#L138)
- Lean declaration: [exists_maximal_missing_rank_support_decomposition](../../Erdos249257/HalfCylinderFatalGapRightTail.lean#L194)

- outgoing **generalises**: [Z13::largest_false_rank_branch_transport](BROWSER_Z13_1.md#node-7dcf61556232a9ef). The named largest-false-rank invariant is the parameterised form of the maximal-missing-rank decomposition.
- incoming **reformulates**: [Z16::boundary_words_binary_consecutive](BROWSER_Z16_1.md#node-4f7bd3fd6e31ca03). ProfiledGapStage.boundaryWordsAdjacent and weightedBoolSum_adjacent_cut are the same adjacency statement for prefix-false-all-true versus prefix-true-all-false, one in binary-numeral order and one in weighted-sum order.

<a id="node-1ee49acd5a2193bb"></a>
## seam_word_support_and_actual_word_representation

Encoding lemmas for finite seam words: the support of a word, its behaviour under appending a false or true bit, the identification of the actual half seam word's support with the rational greedy prefix support, membership of a rank being exactly a true coordinate, and the fact that the actual word evolves by appending precisely the real greedy take/skip decision at the terminal coordinate.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamWordSupport_halfActualSeamWord](../../Erdos249257/HalfCylinderFloorErrorReset.lean#L115)
- Lean declaration: [halfActualSeamWord_succ](../../Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L79)
- Lean declaration: [self_mem_halfGreedyPrefixSupport_iff_take](../../Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L66)

- incoming **depends_on_open**: [Z13::real_to_rational_greedy_prefix_bridge](BROWSER_Z13_1.md#node-dadf7a74f8a35d6f). Both identify the actual real greedy orbit with a finite rational object usable by the seam machinery.

<a id="node-b0a9f7595464c220"></a>
## skipped_endpoint_trichotomy

At any genuinely skipped rank s at least five, exactly one of three cells holds: the full-shell frozen margin is negative, in which case the actual seam word equals the integer seam greedy word and the margin is minus a positive integer greedy remainder confined to the square-root strip; the margin is zero, with the same alignment and zero remainder; or the margin is positive, in which case the actual word is the minimal word above the target and the margin is its overshoot. Moreover an aligned skip stays aligned exactly on the middle branch, and its next full-shell margin is always strictly negative.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [halfGreedy_skipped_endpoint_trichotomy](../../Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L246)
- Lean declaration: [skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L569)
- Lean declaration: [alignedSkip_next_alignment_iff_middle](../../Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L368)
- Lean declaration: [alignedSkip_nextMargin_neg](../../Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L472)

- outgoing **depends_on_open**: [Z13::full_shell_margin_equals_integer_seam_defect](BROWSER_Z13_1.md#node-287d59e425cc9ca6). The trichotomy is read off the full-shell identity together with gap domination.
- outgoing **specialises**: [Z13::abstract_greedy_optimality_and_small_defect_equivalence](BROWSER_Z13_1.md#node-64ee0481167c5f3c). Uniqueness of the small-defect bit word is what forces alignment in the negative cell.
- incoming **depends_on_open**: [Z13::half_membership_from_frozen_margin_sockets](BROWSER_Z13_1.md#node-0b364ae5b3109540). Every socket in the node is the demand that the negative-margin cell of the trichotomy never occurs at an actual skip.
- incoming **specialises**: [Z13::aligned_positive_skip_forces_next_take](BROWSER_Z13_1.md#node-4b7b4075983286bd). Its hypotheses are exactly the first cell of the trichotomy, so it says that cell cannot recur at consecutive rows.
- incoming **implies**: [Z13::finite_shadow_square_root_strip](BROWSER_Z13_1.md#node-b672d53f73e0ea3c). The square-root strip bound is what confines the negative-cell seam remainder to halfStripBound (2n).

<a id="node-7bc36910131bf033"></a>
## take_forces_negative_full_shell_margin

If the real greedy orbit takes rank n then the full-shell frozen margin at n is strictly negative; equivalently, a nonnegative full-shell margin at n forces the orbit to skip rank n. The converse implication is not proved.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [greedyHalfFrozenMargin_fullShell_neg_of_take](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L442)
- Lean declaration: [skip_of_fullShell_margin_nonneg](../../Erdos249257/HalfCylinderFullShellSeamBridge.lean#L476)

- outgoing **barrier_for**: [Z13::half_membership_from_frozen_margin_sockets](BROWSER_Z13_1.md#node-0b364ae5b3109540). It supplies only the easy direction of the sign dichotomy; the socket is precisely the unproved converse.

<a id="node-5f7575629a24a895"></a>
## truncated_mersenne_weight_closed_forms

The integer 4^s divided by 2^d - 1 has three equal closed forms: a power of two times a geometric sum in 2^d, a descending sum of powers of two at the multiples of d, and the sum over rows j of the indicator that d divides row j+2 weighted by 2^(2s-2-j).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [truncatedMersenneWeight_eq_geometricCore](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L29)
- Lean declaration: [truncatedMersenneWeight_eq_divisorIndicatorSum](../../Erdos249257/HalfCylinderIntegerGreedy.lean#L197)

- outgoing **implies**: [Z13::actual_seam_hole_equals_integer_subset_sum_defect](BROWSER_Z13_1.md#node-c1a58e98f65e57f9). The divisor-indicator form of the weight is what makes the finite incidence swap unconditional.
- incoming **finite_instance_of**: [Z14::seam_base_row_certificates](BROWSER_Z14_1.md#node-eec681960426ae88). the twelve certified seam weights and subset target at row 14 are the closed-form truncated Mersenne integers 4^s/(2^d - 1) evaluated at s = 14 and d = 2..13.

<a id="node-0c099e1977615cd1"></a>
## unbounded_skipped_ranks_give_half_membership

A false coordinate of the integer seam greedy word bounds the row remainder by that coordinate's truncated weight, so cofinal rows carrying skipped ranks that tend to infinity make the normalised remainder vanish and force 1/2 into the Mersenne achievement set. Equivalent supply forms are cofinal false successor terminal bits and false terminal bits beyond every bound.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["SeamGreedyUnboundedSkippedRanksAlong rows : a choice of one false seam coordinate per cofinal row whose Mersenne rank tends to infinity", "hterminal : forall N, exists p >= N with 5 <= p and SeamRowWord.terminal (seamGreedyWord (p+1)) = false"]

- Lean declaration: [half_mem_mersenneAchievementSet_of_unboundedSkippedRanks](../../Erdos249257/HalfCylinderSkippedRankLimit.lean#L142)
- Lean declaration: [half_mem_mersenneAchievementSet_of_cofinalTerminalFalse](../../Erdos249257/HalfCylinderFalseBitSupply.lean#L47)
- Lean declaration: [half_mem_mersenneAchievementSet_of_unboundedTerminalFalse](../../Erdos249257/HalfCylinderFalseBitSupply.lean#L64)
- Lean declaration: [seamIntegerGreedyRemainder_lt_truncatedWeight_of_false](../../Erdos249257/HalfCylinderSkippedRankLimit.lean#L58)

- outgoing **equivalent_to**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). The supply antecedent is the negation of eventual-right, which the classification proves equivalent to the conclusion; hence this consumer is a restatement.
- incoming **implies**: [Z13::largest_skip_late_step_socket_fan_in](BROWSER_Z13_1.md#node-396ba5097ca2833b). The late-invariant induction produces exactly the cofinal skipped-rank supply consumed there.
- outgoing **equivalent_to**: [Z12::half_membership_seam_equivalence_ring](BROWSER_Z12_1.md#node-c98bead16d978fce). Both nodes cite half_mem_mersenneAchievementSet_of_unboundedTerminalFalse and _of_cofinalTerminalFalse (HalfCylinderFalseBitSupply.lean); Z12 closes the ring with unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite, so the supplies are the same proposition.
- outgoing **depends_on_open**: [Z12::half_membership_seam_equivalence_ring](BROWSER_Z12_1.md#node-c98bead16d978fce). the equivalence ring proves cofinal false terminal bits / unbounded skipped seam ranks equivalent to half-membership itself, so this node's antecedent is the open proposition in different coordinates and no weaker producer can exist.

<a id="node-f9a0ade9be7e30ef"></a>
## upper_reset_band_escape_rows_13_to_30

Kernel-verified finite computation: for every row d from thirteen to thirty at which the seam successor carries, the upper reset charge avoids every linear-width danger band below the relevant dyadic powers, for all band indices j at most d. The verification proceeds by evaluating the exact seam integer greedy remainder at each row (seamIntegerGreedyRemainder 14 = 392, seamIntegerGreedyRemainder 21 = 100251, seamIntegerGreedyRemainder 30 = 1583742700).

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamUpperResetDyadicBandEscape_through_thirty](../../Erdos249257/HalfCylinderUpperResetBandCertificates.lean#L78)

- outgoing **finite_instance_of**: [Z13::upper_reset_floor_coordinate_bridge](BROWSER_Z13_2.md#node-01dafaef986509fb). The verified rows instantiate the reset-charge coordinate the bridge provides.
- outgoing **finite_instance_of**: [Z14::dyadic_band_producer_gives_row_escape](BROWSER_Z14_1.md#node-181ede821d8a3386). the computation verifies, for d = 13..30 and all j <= d, precisely the disjunction SeamUpperResetDyadicBandEscape that this conditional assumes for all d >= 13; it is that hypothesis at eighteen bounded rows.
- incoming **depends_on_open**: [Z14::half_membership_conditional_endpoints](BROWSER_Z14_1.md#node-c86b42e6bb40f03f). of the six sockets only SeamUpperResetDyadicBandEscape has any producer, and that producer verifies it for rows d = 13..30 only; the five middle-producer sockets have no producer anywhere.
- incoming **depends_on_open**: [Z14::dyadic_band_producer_gives_row_escape](BROWSER_Z14_1.md#node-181ede821d8a3386). the only producer of SeamUpperResetDyadicBandEscape anywhere: it verifies the disjunction for rows d = 13..30 and all j <= d, and stops there; the hypothesis quantifies over all d >= 13.
- incoming **specialises**: [Z14::upper_reset_band_escape_row_thirteen](BROWSER_Z14_2.md#node-e6113688d6d6369d). `seamUpperResetDyadicBandEscape_at_thirteen` (HalfCylinderMiddleCarryLowerBound.lean:3512) is the d = 13 instance of `seamUpperResetDyadicBandEscape_through_thirty` (HalfCylinderUpperResetBandCertificates.lean:78): identical conclusion for all j <= d, with d fixed to 13.

<a id="node-01dafaef986509fb"></a>
## upper_reset_floor_coordinate_bridge

On an upper transition the next greedy floor error absorbs exactly the pulse of the old above word, so the rationally corrected upper charge is the integer reset charge plus the next floor error, and distance from any dyadic boundary translates exactly into a statement about the corrected coordinate floorZ at row s+1.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamUpperBranch_nextFloorError_add_abovePulse_eq](../../Erdos249257/HalfCylinderUpperResetBandCertificates.lean#L25)
- Lean declaration: [seamUpperBranch_correctedCharge_eq_resetCharge_add_nextFloorError](../../Erdos249257/HalfCylinderUpperResetBandCertificates.lean#L44)
- Lean declaration: [seamUpperBranch_correctedDyadicDistance_eq_floorZ](../../Erdos249257/HalfCylinderUpperResetBandCertificates.lean#L61)

- incoming **finite_instance_of**: [Z13::upper_reset_band_escape_rows_13_to_30](BROWSER_Z13_2.md#node-f9a0ade9be7e30ef). The verified rows instantiate the reset-charge coordinate the bridge provides.

