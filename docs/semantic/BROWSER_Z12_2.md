# Z12_2: Mersenne achievement set: greedy geometry, fat-Cantor structure, and the 1/2 membership question

[All problems and zones](BROWSER.md)

<a id="node-d973a0832877504d"></a>
## konig_prefix_closed_branch

A family of predicates on finite Boolean words that is closed under restriction and nonempty at every length admits an infinite Boolean sequence all of whose finite restrictions satisfy it; specialised, cofinally many strip-admissible finite words give an infinite strip-admissible branch.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [exists_bool_sequence_of_prefix_closed_finite_words](../../Erdos249257/HalfCarryReachability.lean#L389)
- Lean declaration: [exists_infinite_halfStripBranch](../../Erdos249257/HalfCarryReachability.lean#L429)

- incoming **implies**: [Z12::half_strip_admissible_word_system](BROWSER_Z12_1.md#node-5a97937c528b1bfe). prefix closure of admissibility is the hypothesis Konig's lemma consumes
- outgoing **implies**: [Z12::cofinal_admissibility_yields_257_counterexample](BROWSER_Z12_1.md#node-25b0e23ee881e72f). the compactness step is what turns cofinal finite words into an infinite branch

<a id="node-275fc9b423c4c20c"></a>
## last_skip_iff_finite_skips

A last greedy skip exists exactly when the skipped support of the greedy run at 1/2 is finite, and exactly when a fatal half gap exists. All three conditions are equivalent to 1/2 not lying in the Mersenne achievement set.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["exists M, IsLastHalfGreedySkip M -- equivalently (1/2 : R) not in mersenneAchievementSet; undecided"]

- Lean declaration: [exists_isLastHalfGreedySkip_iff_skippedSupport_finite](../../Erdos249257/CampbellShiftSynchronization.lean#L359)
- Lean declaration: [existsFatalHalfGap_iff_exists_isLastHalfGreedySkip](../../Erdos249257/CampbellShiftSynchronization.lean#L384)

- outgoing **equivalent_to**: [Z12::fatal_half_gap_dichotomy](BROWSER_Z12_1.md#node-5736eac8e3dd6fae). existence of a last greedy skip is proved equivalent to existence of a fatal half gap
- incoming **equivalent_to**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). seamGreedyEventuallyRight_iff_exists_isLastHalfGreedySkip and exists_isLastHalfGreedySkip_iff_skippedSupport_finite are the same last-skip characterisation in seam and greedy coordinates.

<a id="node-842347b882d96c73"></a>
## last_skip_shift_geometry

Assuming a final skipped exponent M for the greedy run at 1/2, the finite Mersenne shift of the skipped prefix satisfies exact relations: 1/2 plus the shift minus the Erdos-Borwein constant equals the residual minus the tail at M, lies strictly in the one-sided fatal interval (0, g(M)), the centred shadow at M-1 is within g(M) of the constant, and for M at least 3 the constant minus the shift lies in the dyadic window (1/2 - 4^-M, 1/2).

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hlast : IsLastHalfGreedySkip M -- existence of a final skipped exponent, which is itself equivalent to (1/2 : R) not in mersenneAchievementSet and is not proved"]

- Lean declaration: [lastHalfSkip_shiftDelta_eq_remainder_sub_tail](../../Erdos249257/CampbellShiftSynchronization.lean#L107)
- Lean declaration: [lastHalfSkip_shift_fatalInterval](../../Erdos249257/CampbellShiftSynchronization.lean#L211)
- Lean declaration: [lastHalfSkip_shadow_mem_gap](../../Erdos249257/CampbellShiftSynchronization.lean#L231)
- Lean declaration: [lastHalfSkip_shifted_mem_dyadicCylinder](../../Erdos249257/CampbellShiftSynchronization.lean#L283)

- outgoing **implies**: [Z12::shift_window_zero_endpoint_restatement](BROWSER_Z12_2.md#node-592c2020744fdf2f). the dyadic window (1/2 - 4^-M, 1/2) derived under a last skip is exactly what GreedyShiftWindowZero negates
- outgoing **depends_on_open**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). this classification proves 'a last greedy skip exists' equivalent to '1/2 is not in the Mersenne achievement set'; the hypothesis is therefore one branch of the open endpoint and has no producer.

<a id="node-708dff30a57dbf0e"></a>
## mersenne_achievement_set_cantor_geometry

The Mersenne achievement set is compact, closed, perfect, totally disconnected and nowhere dense in the reals.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [isCompact_mersenneAchievementSet](../../Erdos249257/GreedyAchievementSet.lean#L656)
- Lean declaration: [perfect_mersenneAchievementSet](../../Erdos249257/GreedyAchievementSet.lean#L1656)
- Lean declaration: [isTotallyDisconnected_mersenneAchievementSet](../../Erdos249257/GreedyAchievementSet.lean#L1672)
- Lean declaration: [isNowhereDense_mersenneAchievementSet](../../Erdos249257/GreedyAchievementSet.lean#L1681)

- incoming **implies**: [Z12::mersenne_strict_superincreasing_tail](BROWSER_Z12_2.md#node-807aad871f9d65e8). the strict tail inequality is exactly the Kakeya-type condition that makes the value set totally disconnected and nowhere dense
- outgoing **transport_of**: [Z12::mersenne_support_coding_normalisation](BROWSER_Z12_2.md#node-6dea3c442e2bc9d4). the topological statements are transported along the continuous injective digit coding
- incoming **complements**: [Z12::mersenne_achievement_set_measure_one](BROWSER_Z12_2.md#node-5b58066178611b00). the measure-one theorem and the separately evidenced nowhere-dense topology theorem are the two independent halves of the fat Cantor conclusion

<a id="node-5b58066178611b00"></a>
## mersenne_achievement_set_measure_one

The depth-d cylinder stage is a disjoint union of 2^d translated copies of an interval of length T(d), hence has Lebesgue measure exactly 2^d * T(d); the stages are nested with intersection equal to the achievement set, and 2^d * T(d) tends to 1. Therefore the achievement set has Lebesgue measure exactly one.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: This node owns the measure calculation only. Combined with the separately evidenced nowhere-dense topology node, it gives the fat Cantor conclusion.

- Lean declaration: [volume_mersenneCylinderStageFrom](../../Erdos249257/GreedyAchievementSet.lean#L879)
- Lean declaration: [volume_mersenneCylinderStage](../../Erdos249257/GreedyAchievementSet.lean#L906)
- Lean declaration: [mersenneAchievementSet_eq_iInter_cylinderStage](../../Erdos249257/GreedyAchievementSet.lean#L844)
- Lean declaration: [volume_mersenneAchievementSet](../../Erdos249257/GreedyAchievementSet.lean#L996)

- outgoing **complements**: [Z12::mersenne_achievement_set_cantor_geometry](BROWSER_Z12_2.md#node-708dff30a57dbf0e). the measure-one theorem and the separately evidenced nowhere-dense topology theorem are the two independent halves of the fat Cantor conclusion

<a id="node-aaaea584bbabda94"></a>
## mersenne_gap_two_channel_asymptotic

Each Mersenne weight splits exactly as 2^-n + 4^-n plus a positive remainder bounded by 2*8^-n, so the tail splits as 2^-n + (1/3)4^-n plus a remainder tail lying strictly between (1/7)8^-n and (2/7)8^-n. Consequently the gap w(n) - T(n) equals (2/3)4^-n up to an error of norm at most 3*8^-n, and is big-O of 8^-n at infinity.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [mersenneWeight_eq_two_channels_add_remainder](../../Erdos249257/GreedyAchievementSet.lean#L207)
- Lean declaration: [mersenneTail_eq_two_channels_add_remainderTail](../../Erdos249257/GreedyAchievementSet.lean#L401)
- Lean declaration: [mersenneGap_sub_main_eq_remainder_sub_tail](../../Erdos249257/GreedyAchievementSet.lean#L438)
- Lean declaration: [mersenneGap_asymptotic_bound](../../Erdos249257/GreedyAchievementSet.lean#L448)
- Lean declaration: [mersenneGap_isBigOWith](../../Erdos249257/GreedyAchievementSet.lean#L473)

- outgoing **implies**: [Z12::correction_tail_one_bit_window](BROWSER_Z12_1.md#node-6547d3092f58f8f5). the (1/3)4^-n channel and the (1/7,2/7)8^-n remainder bracket are what pin the correction tail between 2^-(2m+2) and 2^-(2m+1)
- outgoing **implies**: [Z12::second_channel_phase_separation](BROWSER_Z12_2.md#node-84f746a828ad3d71). the explicit constants 2/7 and 3/8 in the separation threshold come from the remainder-tail bounds

<a id="node-541f3045e1e0e512"></a>
## mersenne_sliver_coordinate_dynamics

In the rational sliver coordinate a selected greedy step acts by the exact affine map x maps to (4 + 2/(2^n-1))x - 1, and in the doubled sharp coordinate by 4x - 2 plus a 2/(2^n-1) correction. So the greedy dynamics on the sliver is an explicitly perturbed times-four map.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [mersenneSliverCoordinateRat_selected_step](../../Erdos249257/GreedyAchievementSet.lean#L1093)
- Lean declaration: [sharpMersenneSliverCoordinateRat_selected_step](../../Erdos249257/GreedyAchievementSet.lean#L1113)

- outgoing **implies**: [Z12::two_thirds_escape_fixtures](BROWSER_Z12_3.md#node-0794cec8c83c05de). the fixtures are evaluations of the sliver coordinate step map

<a id="node-807aad871f9d65e8"></a>
## mersenne_strict_superincreasing_tail

For every positive exponent n the Mersenne weight 1/(2^n-1) strictly exceeds the total remaining mass of all later weights, and that remaining mass is at most twice the next weight and tends to zero. This strict superincreasing property is what makes the value set a Cantor-type set instead of an interval.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [mersenneTail_lt_weight](../../Erdos249257/GreedyAchievementSet.lean#L180)
- Lean declaration: [two_mul_mersenneWeight_succ_lt](../../Erdos249257/GreedyAchievementSet.lean#L125)
- Lean declaration: [mersenneTail_le_two_mul_weight](../../Erdos249257/GreedyAchievementSet.lean#L155)
- Lean declaration: [mersenneTail_lt_two_mul_weight](../../Erdos249257/GreedyAchievementSet.lean#L186)

- outgoing **implies**: [Z12::mersenne_achievement_set_cantor_geometry](BROWSER_Z12_2.md#node-708dff30a57dbf0e). the strict tail inequality is exactly the Kakeya-type condition that makes the value set totally disconnected and nowhere dense
- incoming **generalises**: [Z12::hereditary_strict_superincreasing_subseries](BROWSER_Z12_1.md#node-b2e6722a9197358a). the same strict inequality with an arbitrary set of future offsets deleted

<a id="node-6dea3c442e2bc9d4"></a>
## mersenne_support_coding_normalisation

The Mersenne support value of a set of positive exponents coincides with the generic erdosSupportSeries at base 2, the achievement set is exactly the range of the continuous binary digit map, and that map is injective, so distinct normalized supports have distinct values.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [positiveMersenneSupportValue_eq_erdosSupportSeries](../../Erdos249257/GreedyAchievementSet.lean#L554)
- Lean declaration: [range_positiveMersenneDigitValue_eq](../../Erdos249257/GreedyAchievementSet.lean#L636)
- Lean declaration: [positiveMersenneSupportValue_injective_normalized](../../Erdos249257/GreedyAchievementSet.lean#L1563)
- Lean declaration: [erdosSupportSeries_two_injective_normalized](../../Erdos249257/GreedyAchievementSet.lean#L1572)
- Lean declaration: [positiveMersenneDigitValue_injective](../../Erdos249257/GreedyAchievementSet.lean#L1582)

- incoming **transport_of**: [Z12::mersenne_achievement_set_cantor_geometry](BROWSER_Z12_2.md#node-708dff30a57dbf0e). the topological statements are transported along the continuous injective digit coding
- outgoing **reformulates**: [Z01::support_coefficient_representation](BROWSER_Z01_2.md#node-950d0bc2e85796ab). positiveMersenneSupportValue_eq_erdosSupportSeries (GreedyAchievementSet.lean:554) identifies the achievement-set value map with erdosSupportSeries at base 2, whose coefficient form is erdosSupportSeries_eq_tsum_supportCoeff.
- outgoing **specialises**: [Z01::support_coefficient_representation](BROWSER_Z01_2.md#node-950d0bc2e85796ab). `positiveMersenneSupportValue_eq_erdosSupportSeries : positiveMersenneSupportValue A = erdosSupportSeries 2 A` (GreedyAchievementSet.lean:554) identifies the Mersenne coding with the base b = 2 case of the generic support series that Z01 defines and normalises.

<a id="node-f4856da5bcdafc98"></a>
## mobius_centered_carry_coboundary

Recentring the integer half carry by the signed Mobius baseline gives a carry whose coboundary is exactly the support coefficient minus the divisor-sum baseline: a_{N+2} minus the divisor sum equals 2*C_N minus C_{N+1}.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [mobiusCenteredHalfCarry_coboundary](../../Erdos249257/HalfCarryReachability.lean#L708)
- Lean declaration: [boolean_sub_signedMobiusBaseline_eq_centeredCoboundary](../../Erdos249257/HalfCarryReachability.lean#L717)

- incoming **implies**: [Z12::signed_mobius_baseline_divisor_identity](BROWSER_Z12_2.md#node-d9a6e783afb20753). the divisor-sum identity is what makes the recentred carry a coboundary of the support bit
- outgoing **implies**: [Z12::tempered_mobius_carry_yields_half](BROWSER_Z12_2.md#node-c0baa14342623c9d). the coboundary presentation is the coordinate in which temperedness is stated
- outgoing **reformulates**: [Z11::affine_carry_fixed_depth_reset](BROWSER_Z11_1.md#node-1ce1b5ef053ed69d). mobiusCenteredHalfCarry_coboundary is the affine recentring of the input-driven binary orbit u(n+1) = 2u(n) - a(n+1) that affineBinaryOrbit_sub describes, with the signed Moebius baseline as the shift.

<a id="node-64bb333686e394b6"></a>
## overlapping_reverse_carry_two_adic_spacing

Two reverse-carry presentations that share a coefficient word, differ at a single 1/0 seam, and agree on the following overlap of length L have terminal carry difference equal to 2^L times an odd integer; if both terminal carries are nonnegative and bounded by a common real bound, then 2^L is at most that bound. Specialised to overlapping midpoint returns at depth 2N with seam at M, the exponent is 2N - M - 1.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd](../../Erdos249257/HalfTrappingReturnCarry.lean#L124)
- Lean declaration: [twoPow_le_realBound_of_carryDifference_eq_twoPow_mul_odd](../../Erdos249257/HalfTrappingReturnCarry.lean#L153)
- Lean declaration: [overlappingReverseCarryWords_twoPow_le_realBound](../../Erdos249257/HalfTrappingReturnCarry.lean#L191)
- Lean declaration: [overlappingMidpointReturns_carryDifference_eq_twoPow_mul_odd](../../Erdos249257/HalfTrappingReturnCarry.lean#L220)
- Lean declaration: [overlappingMidpointReturns_twoPow_le_realBound](../../Erdos249257/HalfTrappingReturnCarry.lean#L244)

- incoming **barrier_for**: [Z12::relation_invariant_channel_determinant_barrier](BROWSER_Z12_2.md#node-0bf69d60c69b92a2). the determinant route is closed at all ranks, which is why the same module falls back on 2-adic carry spacing

<a id="node-72c6fa3ca8098c3b"></a>
## post_take_unsafe_band_characterisation

For a residual written as 1/R after a take at rank b with q = 2^b - 1, and next take at rank c with m = 2^(c-1), the last intervening skip fails the dyadic safety test exactly when R lies strictly in (q(m-1)/(q+m-1), qm/(q+m)), an interval of exact width q^2/((q+m)(q+m-1)). For a single intervening skip this is the two-thirds band, of width below 1/9 and contained in (2q/3, 2q/3 + 2/9), where an unsafe skip forces 2q < 3R < 2q + 2/3.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [postTakeUnsafeAt_iff_band](../../Erdos249257/HalfGreedyTwoThirdsBand.lean#L88)
- Lean declaration: [band_width_general](../../Erdos249257/HalfGreedyTwoThirdsBand.lean#L104)
- Lean declaration: [singletonUnsafe_iff_twoThirdsBand](../../Erdos249257/HalfGreedyTwoThirdsBand.lean#L127)
- Lean declaration: [band_width](../../Erdos249257/HalfGreedyTwoThirdsBand.lean#L154)
- Lean declaration: [three_mul_mem_of_twoThirdsBand](../../Erdos249257/HalfGreedyTwoThirdsBand.lean#L169)

- outgoing **implies**: [Z12::two_thirds_band_arithmetic_exclusions](BROWSER_Z12_3.md#node-d88c983df9c61dfd). the exclusions are congruence consequences of the single-skip band pinning
- incoming **finite_instance_of**: [Z12::two_thirds_escape_fixtures](BROWSER_Z12_3.md#node-0794cec8c83c05de). the fixtures show the relaxed and doubled band tests are not equivalent to actual greedy survival

<a id="node-fe0fcd0cf10b44ae"></a>
## rank_gap_excludes_all_supports

If a target t sits strictly above a support prefix plus the tail after rank d+1 and strictly below that prefix plus the weight at d+1, then no support agreeing with the prefix through rank d can have value t. The exclusion is global over supports, not merely about the greedy branch.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [positiveMersenneSupportValue_ne_of_rank_gap](../../Erdos249257/HalfCutLocator.lean#L380)
- Lean declaration: [half_ne_of_prefix_gap](../../Erdos249257/HalfCutLocator.lean#L513)

- outgoing **implies**: [Z12::fatal_half_gap_dichotomy](BROWSER_Z12_1.md#node-5736eac8e3dd6fae). the global exclusion is the nonmembership direction of the dichotomy

<a id="node-0bf69d60c69b92a2"></a>
## relation_invariant_channel_determinant_barrier

If a family of rational-linear channels each annihilates every vector killed by scalar evaluation, and evaluation is surjective, then the evaluation matrix has rank at most one, so every square minor indexed by a type with at least two elements has determinant zero. This is an abstract linear-algebra fact about an arbitrary channel family satisfying the kernel hypothesis; read informally it says that a determinant route built from relation-invariant channels fails at every rank rather than only at the experimentally tested ranks two through four, but see the scope caveat for what the Lean does and does not instantiate.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Rules out only determinant-based separation built from channels that annihilate the kernel of scalar evaluation, i.e. channels factoring through evaluation, and only for index types with at least two elements (Nontrivial iota); a single-channel 1x1 determinant is untouched. It does not rule out: channels that fail that invariance (any channel sensitive to a nontrivial zero-valued formal relation); nonlinear or non-rational channels; height or adelic obstructions established by means other than a nonvanishing minor; or the reverse-carry 2-adic spacing route in the same module. It says nothing about whether 1/2 is in the achievement set. IMPORTANT, added on adversarial review: the theorem is stated for an arbitrary V, ev and channel family, and no declaration anywhere in the corpus defines the concrete shifted channels used in the experiments or proves that they satisfy hker. So the reading 'this closes the raw shifted-channel determinant route' (module docstring, HalfTrappingReturnCarry.lean:11-15) is an informal application, not a formalised one; the formal content is the abstract rank-one minor vanishing. Any published claim that a method family is closed must either instantiate the channels in Lean or state the gap.

- Lean declaration: [relationInvariantLinearChannels_det_eq_zero](../../Erdos249257/HalfTrappingReturnCarry.lean#L42)

- outgoing **barrier_for**: [Z12::overlapping_reverse_carry_two_adic_spacing](BROWSER_Z12_2.md#node-64bb333686e394b6). the determinant route is closed at all ranks, which is why the same module falls back on 2-adic carry spacing
- outgoing **transport_of**: [Z09::scalar_localisation_height_barrier](BROWSER_Z09_2.md#node-e79c79b3968927cf). Both nodes are the rank-one collapse of relation-invariant linear channels: Z09 states it for a single scalar localiser (linearDescender_eq_smul_eval, AdelicHeightObstruction.lean) and Z12 for a family indexed by iota (relationInvariantLinearChannels_det_eq_zero, HalfTrappingReturnCarry.lean), the multi-channel instance of the same descender.

<a id="node-11a8403d1942daa3"></a>
## scaled_uncentred_carry_antitone

For every support the uncentred integer half carry divided by 2^N is antitone in N, because each step subtracts a nonnegative support coefficient after rescaling.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [scaled_integerHalfCarry_antitone](../../Erdos249257/CofinalStripReturn.lean#L23)

- outgoing **implies**: [Z12::cofinal_strip_return_yields_half](BROWSER_Z12_1.md#node-0019f92e625c9459). antitonicity is the fan-in that upgrades cofinal returns into a limit

<a id="node-34a6eea19a93dd72"></a>
## seam_gap_bound_yields_half

If the integer seam remainder is below 2^(s+1) for every row s at least 6 -- an exponential bound observed by exact replay but not proved -- then the seam values approach 1/2 with error at most 3*2^-s and 1/2 belongs to the Mersenne achievement set.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hgap : SeamGreedyRemainderGapBound, i.e. forall s >= 6, seamIntegerGreedyRemainder s < 2^(s+1)"]

- Lean declaration: [half_mem_mersenneAchievementSet_of_seamRemainderGapBound](../../Erdos249257/HalfCylinderSeamLimit.lean#L303)
- Lean declaration: [tendsto_seamGreedyFiniteValue_half](../../Erdos249257/HalfCylinderSeamLimit.lean#L278)

- incoming **generalises**: [Z12::seam_subquadratic_along_yields_half](BROWSER_Z12_2.md#node-73d45b5a6f11f565). a cofinal subquadratic condition is weaker than the uniform exponential gap bound
- outgoing **depends_on_open**: [Z14::two_sided_dyadic_invariant_under_cell_escape](BROWSER_Z14_2.md#node-a7d5bd16039a80ba). the nearest statement bounding the seam remainder by a dyadic power at every row; it delivers only min(remainder, overshoot) <= 2^s and is itself gated on the unproved SeamTwoSidedDyadicCellEscape, so it does not produce the one-sided bound rem(s) < 2^(s+1).

<a id="node-0dd00b03425be74c"></a>
## seam_greedy_finite_values_in_achievement_set

Each integer-greedy seam word codes a normalized finite exponent set, so its Mersenne value lies in the achievement set and equals the cast of an exact rational seam sum.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [seamGreedyFiniteValue_mem_achievementSet](../../Erdos249257/HalfCylinderSeamLimit.lean#L36)
- Lean declaration: [seamGreedyFiniteValue_eq_cast_rationalSum](../../Erdos249257/HalfCylinderSeamLimit.lean#L41)

- outgoing **implies**: [Z12::seam_subquadratic_along_yields_half](BROWSER_Z12_2.md#node-73d45b5a6f11f565). closedness of the achievement set applies because every seam value is already a member

<a id="node-39ee38823a46ddbe"></a>
## seam_greedy_general_error_bound

For every seam row s at least 5 the exact rational seam remainder is nonnegative and at most 2^-s plus the integer seam remainder divided by 4^s; equivalently the seam value approaches 1/2 from below with error at most 2^-s plus the normalized integer remainder.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [seamGreedyRationalRemainder_general_bounds](../../Erdos249257/HalfCylinderSeamLimit.lean#L62)
- Lean declaration: [seamGreedyFiniteValue_general_error_bounds](../../Erdos249257/HalfCylinderSeamLimit.lean#L116)

- outgoing **implies**: [Z12::seam_subquadratic_along_yields_half](BROWSER_Z12_2.md#node-73d45b5a6f11f565). the general bound is what the subquadratic hypothesis is plugged into

<a id="node-73d45b5a6f11f565"></a>
## seam_subquadratic_along_yields_half

If along some sequence of rows tending to infinity the integer seam remainder divided by 4^s tends to zero, then the seam values converge to 1/2 and, by closedness, 1/2 belongs to the Mersenne achievement set. No such row sequence is exhibited.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hrows : SeamGreedyRemainderSubquadraticAlong rows, i.e. rows tends to infinity and seamGreedyNormalizedRemainder (rows j) tends to zero"]

- Lean declaration: [tendsto_seamGreedyFiniteValue_half_of_subquadraticAlong](../../Erdos249257/HalfCylinderSeamLimit.lean#L142)
- Lean declaration: [half_mem_mersenneAchievementSet_of_subquadraticAlong](../../Erdos249257/HalfCylinderSeamLimit.lean#L179)

- incoming **implies**: [Z12::seam_greedy_general_error_bound](BROWSER_Z12_2.md#node-39ee38823a46ddbe). the general bound is what the subquadratic hypothesis is plugged into
- outgoing **generalises**: [Z12::seam_gap_bound_yields_half](BROWSER_Z12_2.md#node-34a6eea19a93dd72). a cofinal subquadratic condition is weaker than the uniform exponential gap bound
- incoming **implies**: [Z12::seam_greedy_finite_values_in_achievement_set](BROWSER_Z12_2.md#node-0dd00b03425be74c). closedness of the achievement set applies because every seam value is already a member

<a id="node-7a48a1adceb60ab3"></a>
## seam_terminal_false_local_classifier

At a fixed seam row at least 5, the successor terminal bit is false exactly when the row is in the upper-or-middle arithmetic case (the old successor carries to the upper word, or there is no carry and the new terminal weight exceeds the explicit prefix remainder); unbounded occurrence of the two conditions therefore coincide.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Flagged as a restatement on adversarial review. The node bundles two statements of different status. seamGreedy_terminal_false_iff_upperOrMiddle (line 57) is per-row, decidable, and genuinely unconditional. unboundedTerminalFalse_iff_unboundedUpperOrMiddle (line 98) is an equivalence both of whose sides are equivalent to the open half-membership question, and belongs to the same restatement ring as half_membership_seam_equivalence_ring; it renames the open problem rather than reducing it. The restatement flag is set because of the second declaration only.

Open hypotheses: ["SeamGreedyUnboundedUpperOrMiddle -- and equally its partner SeamGreedyUnboundedTerminalFalse. By half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse (HalfCylinderHalfMembershipClassification.lean:126) the latter is provably equivalent to (1 / 2 : R) in mersenneAchievementSet, so both sides of unboundedTerminalFalse_iff_unboundedUpperOrMiddle are open and neither has a positive producer anywhere in the corpus."]

- Lean declaration: [seamGreedy_terminal_false_iff_upperOrMiddle](../../Erdos249257/HalfCylinderHalfMembershipClassification.lean#L57)
- Lean declaration: [unboundedTerminalFalse_iff_unboundedUpperOrMiddle](../../Erdos249257/HalfCylinderHalfMembershipClassification.lean#L98)

- outgoing **implies**: [Z12::half_membership_seam_equivalence_ring](BROWSER_Z12_1.md#node-c98bead16d978fce). the row-local classifier is the arithmetic content that the unbounded quantifier is wrapped around

<a id="node-84f746a828ad3d71"></a>
## second_channel_phase_separation

If for every positive n the second-channel phase 4^n * (residual at 1/2) stays at distance at least 1/6 + (37/56)2^-n from 1/3, then 1/2 belongs to the Mersenne achievement set; equivalently it suffices that the decidable rational separation predicate holds for every n at least 7. The separation hypothesis is not proved for any n beyond the checked range.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hseparate : forall n, 0 < n -> (1/6 : R) + (37/56) * (1/2)^n <= |greedyMersenneSecondChannelPhase n - 1/3|", "hseparate : forall n, 7 <= n -> HalfSecondChannelSeparatedRat n"]

- Lean declaration: [half_mem_mersenneAchievementSet_of_secondChannelSeparation](../../Erdos249257/GreedyAchievementSet.lean#L3118)
- Lean declaration: [half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven](../../Erdos249257/GreedyAchievementSet.lean#L3151)
- Lean declaration: [halfGreedy_next_survives_of_secondChannelSeparation](../../Erdos249257/GreedyAchievementSet.lean#L3057)

- incoming **implies**: [Z12::mersenne_gap_two_channel_asymptotic](BROWSER_Z12_2.md#node-aaaea584bbabda94). the explicit constants 2/7 and 3/8 in the separation threshold come from the remainder-tail bounds
- incoming **generalises**: [Z12::channel_cap_skip_transport](BROWSER_Z12_1.md#node-3b04a5f99d781f94). the second-channel separation socket is the rescaled and sharpened form of the two-channel cap socket
- incoming **finite_instance_of**: [Z12::second_channel_separation_low_rank_instances](BROWSER_Z12_2.md#node-c712f1c7cd9b9d3b). ranks 1 through 6 of the required separation are decided; the socket needs all ranks at least 7
- incoming **implies**: [Z12::signed_balance_step_survival_criterion](BROWSER_Z12_2.md#node-5e46605191fd558e). the separation producer is obtained by multiplying the signed-balance criterion by 4^n

<a id="node-c712f1c7cd9b9d3b"></a>
## second_channel_separation_low_rank_instances

The decidable rational second-channel separation predicate holds at every rank n with 1 <= n <= 6, checked by exact rational arithmetic.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [halfSecondChannelSeparatedRat_of_pos_le_six](../../Erdos249257/GreedyAchievementSet.lean#L2973)

- outgoing **finite_instance_of**: [Z12::second_channel_phase_separation](BROWSER_Z12_2.md#node-84f746a828ad3d71). ranks 1 through 6 of the required separation are decided; the socket needs all ranks at least 7

<a id="node-592c2020744fdf2f"></a>
## shift_window_zero_endpoint_restatement

The proposed shifted-window interface -- under a putative last skip M at least 3, the Erdos-Borwein constant minus the finite skipped shift is at most 1/2 - 4^-M -- is logically equivalent to infinitude of the greedy skipped support at 1/2, and hence to 1/2 belonging to the Mersenne achievement set. It is therefore an endpoint restatement, not an independent producer: assuming it assumes the conclusion. Any future Campbell-style input must be nonvacuous, for example a window theorem without the last-skip guard.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["GreedyShiftWindowZero -- equivalent to (1/2 : R) in mersenneAchievementSet, i.e. the open problem itself"]

- Lean declaration: [shiftWindowZero_iff_greedyMersenneSkippedSupport_infinite](../../Erdos249257/CampbellShiftSynchronization.lean#L471)
- Lean declaration: [shiftWindowZero_iff_half_mem_mersenneAchievementSet](../../Erdos249257/CampbellShiftSynchronization.lean#L488)
- Lean declaration: [half_mem_mersenneAchievementSet_of_shiftWindowZero](../../Erdos249257/CampbellShiftSynchronization.lean#L480)

- outgoing **alias_of**: [Z12::half_membership_iff_infinite_greedy_skips](BROWSER_Z12_1.md#node-f4d02068c1837778). GreedyShiftWindowZero is proved equivalent to half membership, so it is the endpoint under another name
- incoming **barrier_for**: [Z12::campbell_agp_parameter_barrier](BROWSER_Z12_1.md#node-f2341acfc3d000a7). the barrier removes the AGP parameter route that was meant to supply the shifted-window interface, and the restatement shows the interface would have been vacuous anyway
- incoming **implies**: [Z12::last_skip_shift_geometry](BROWSER_Z12_2.md#node-842347b882d96c73). the dyadic window (1/2 - 4^-M, 1/2) derived under a last skip is exactly what GreedyShiftWindowZero negates
- outgoing **equivalent_to**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). shiftWindowZero_iff_half_mem_mersenneAchievementSet and seamGreedyEventuallyRight_iff_half_not_mem land on the same endpoint, so the shifted-window interface and the eventual-right seam classification are two names for one open proposition.

<a id="node-5e46605191fd558e"></a>
## signed_balance_step_survival_criterion

Given that the greedy residual survives at level n, the next level survives if and only if the rank gap g(n+1) is at most the absolute signed balance at n; and when it does survive, the new absolute signed balance is |(old absolute balance) - w(n+1)|. This is an exact one-step dynamical law for the survival question.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [greedyMersenne_next_survives_iff_gap_le_abs_signedBalance](../../Erdos249257/GreedyAchievementSet.lean#L2379)
- Lean declaration: [abs_greedyMersenneSignedBalance_succ](../../Erdos249257/GreedyAchievementSet.lean#L2428)

- outgoing **reformulates**: [Z12::half_greedy_shadow_reformulation](BROWSER_Z12_1.md#node-8e23f659f64726ae). the shadow minus the Erdos-Borwein constant is definitionally the signed balance
- outgoing **implies**: [Z12::second_channel_phase_separation](BROWSER_Z12_2.md#node-84f746a828ad3d71). the separation producer is obtained by multiplying the signed-balance criterion by 4^n
- incoming **reformulates**: [Z12::half_greedy_self_trapping_interval_criterion](BROWSER_Z12_1.md#node-2c0deef7cb552dc1). interval containment at depth n is rewritten as a two-sided bound on the signed balance

<a id="node-d9a6e783afb20753"></a>
## signed_mobius_baseline_divisor_identity

The signed Mobius baseline has divisor sums equal to 0 at n = 1 and 1 at every other positive n.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [sum_divisors_signedMobiusBaseline](../../Erdos249257/HalfCarryReachability.lean#L662)

- outgoing **implies**: [Z12::mobius_centered_carry_coboundary](BROWSER_Z12_2.md#node-f4856da5bcdafc98). the divisor-sum identity is what makes the recentred carry a coboundary of the support bit

<a id="node-ae588a53cf09b158"></a>
## straddle_prefix_membership_criterion

A finite exponent word straddles a target t at depth d when its Mersenne value is at most t and t is at most that value plus the tail at d. If straddling words exist at every depth then t belongs to the Mersenne achievement set -- compactness replaces any nested-chain or coinductive interface. A straddling word at depth d either still straddles at d+1, or straddles after adjoining d+1, or exposes a fatal rank gap; straddles also restrict downward by erasing the top exponent.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [mem_mersenneAchievementSet_of_straddle_all_depths](../../Erdos249257/HalfCutLocator.lean#L173)
- Lean declaration: [isStraddlePrefix_step_trichotomy](../../Erdos249257/HalfCutLocator.lean#L205)
- Lean declaration: [IsStraddlePrefix.erase_top](../../Erdos249257/HalfCutLocator.lean#L334)

- outgoing **specialises**: [Z12::fatal_half_gap_dichotomy](BROWSER_Z12_1.md#node-5736eac8e3dd6fae). the general all-depth straddle criterion specialised to t = 1/2 gives the membership branch
- incoming **finite_instance_of**: [Z12::initial_half_straddle_instances](BROWSER_Z12_1.md#node-0bfb870feae2b431). the empty word is the base straddle at depths 0 and 1

<a id="node-0e98feddc11597cf"></a>
## strip_admissible_branch_forces_half

IF an infinite Boolean branch all of whose finite prefixes are strip admissible exists, THEN its support omits 0 and 1, is infinite, and has support series exactly 1/2; so a single such branch would be a counterexample to universal Erdos #257. The Lean theorems take the branch as a free hypothesis (hbranch : forall N, HalfStripAdmissible N (a restricted to N)); no branch is constructed anywhere in the corpus.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Conditional on an object of unknown existence. The theorem constrains no actual orbit: it says only what a strip-admissible branch would have to be worth, not that one exists. Contrast straddle_prefix_membership_criterion, whose hypothesis has known instances (e.g. t = 0, and the depth-0/depth-1 half straddles of initial_half_straddle_instances); the strip-admissible-branch hypothesis has none.

Open hypotheses: ["hbranch : forall N : Nat, HalfStripAdmissible N (fun i => a i) -- existence of even one infinite strip-admissible Boolean branch. Nothing in the corpus produces one: exists_infinite_halfStripBranch (HalfCarryReachability.lean:429) needs hfinite : forall N, exists a : HalfWord N, HalfStripAdmissible N a, which is exactly the unproved HalfCarryCofinalAdmissibility of node cofinal_admissibility_yields_257_counterexample. If such a branch existed, universal Erdos #257 would be refuted, so the antecedent is at least as hard as the open problem."]

- Lean declaration: [support_half_of_infinite_halfStripBranch](../../Erdos249257/HalfCarryReachability.lean#L531)
- Lean declaration: [boolSupport_infinite_of_halfStripBranch](../../Erdos249257/HalfCarryReachability.lean#L965)

- incoming **implies**: [Z12::integer_half_carry_calculus](BROWSER_Z12_1.md#node-59e84eab60406093). the scaled-residual identity is what converts a bounded carry into closeness of the support series to 1/2
- outgoing **implies**: [Z12::full_strip_reachability_yields_257_counterexample](BROWSER_Z12_1.md#node-aa3bcec65c302faf). the branch theorem is the unconditional core; the full-strip hypothesis only supplies the branch
- outgoing **depends_on_open**: [Z16::certified_cylinder_run_to_depth_52](BROWSER_Z16_1.md#node-bf9e1a5ea4c4344d). an infinite strip-admissible branch would follow by Koenig from admissibility at every level; the run supplies levels up to 52 only, so the branch hypothesis has no producer.

<a id="node-38ddb9d9557d7760"></a>
## strip_envelope_subexponential

The square-root strip envelope divided by the binary place value tends to zero, both at index M and at the successor index M+1.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tendsto_halfStripBound_div_pow_zero](../../Erdos249257/TerminalOnlyScaledVanishing.lean#L99)
- Lean declaration: [tendsto_two_sqrt_add_four_div_pow_zero](../../Erdos249257/TerminalOnlyScaledVanishing.lean#L63)
- Lean declaration: [tendsto_halfStripBound_succ_div_pow_zero](../../Erdos249257/CofinalStripReturn.lean#L42)

- outgoing **implies**: [Z12::terminal_only_strip_error_bound](BROWSER_Z12_2.md#node-49a575b75a3059eb). the strip envelope divided by the binary place value must vanish for the error bound to be useful

<a id="node-f84d07ab3840f960"></a>
## supported_mersenne_digit_injectivity

For any prescribed offset set J, the Mersenne digit map restricted to digit strings supported in J is injective, so distinct J-supported digit strings give distinct achievement values.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [supportedMersenneDigitValue_injective](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L54)

- incoming **implies**: [Z12::hereditary_strict_superincreasing_subseries](BROWSER_Z12_1.md#node-b2e6722a9197358a). injectivity of the J-supported digit map is proved from the hereditary inequality

<a id="node-c0baa14342623c9d"></a>
## tempered_mobius_carry_yields_half

If the Mobius-centred half carry of a normalized support divided by 2^N tends to zero, then that support has Mersenne sum exactly 1/2 and is infinite; a pointwise bound by 2*sqrt(N)+4 is a sufficient concrete producer, and applied to the greedy support at 1/2 it would give a counterexample to universal Erdos #257. No such temperedness or square-root bound is proved.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["htempered : Tendsto (fun N => (mobiusCenteredHalfCarry A N : R) / 2^N) atTop (nhds 0)", "hbound : forall N, (mobiusCenteredHalfCarry (greedyMersenneSupport (1/2)) N : R) <= 2 * sqrt N + 4"]

- Lean declaration: [support_half_of_mobiusCenteredHalfCarry_tempered](../../Erdos249257/HalfCarryReachability.lean#L731)
- Lean declaration: [infinite_support_half_of_mobiusCenteredHalfCarry_tempered](../../Erdos249257/HalfCarryReachability.lean#L778)
- Lean declaration: [greedy_half_infinite_of_mobiusCenteredHalfCarry_tempered](../../Erdos249257/HalfCarryReachability.lean#L795)
- Lean declaration: [infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound](../../Erdos249257/HalfCarryReachability.lean#L817)
- Lean declaration: [greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound](../../Erdos249257/HalfCarryReachability.lean#L953)

- incoming **generalises**: [Z12::cofinal_strip_return_yields_half](BROWSER_Z12_1.md#node-0019f92e625c9459). cofinal returns of the uncentred carry are weaker than an all-level square-root bound on the Mobius-centred carry
- incoming **implies**: [Z12::mobius_centered_carry_coboundary](BROWSER_Z12_2.md#node-f4856da5bcdafc98). the coboundary presentation is the coordinate in which temperedness is stated
- incoming **implies**: [Z12::greedy_mobius_carry_nonneg](BROWSER_Z12_1.md#node-8167d9ef9c6a66a9). nonnegativity supplies the lower half of the square-root strip hypothesis for the actual greedy orbit, leaving only the upper bound open
- outgoing **transport_of**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). support_half_of_mobiusCenteredHalfCarry_tempered is the Moebius-recentred instance of the tempered-orbit criterion at c = supportCoeff A with target value 1/2; the temperedness hypothesis is the same o(2^N) condition.

<a id="node-f8810011b82ac702"></a>
## terminal_only_cofinal_yields_half

If normalized finite words with terminal carry inside the square-root strip exist at cofinally many depths, then 1/2 belongs to the Mersenne achievement set and there is an infinite set with Mersenne sum 1/2. The cofinal terminal-witness supply is not proved.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hcofinal : HalfCarryCofinalTerminalOnlyStrip, i.e. forall N, exists M >= max N 1 with a normalized HalfWord M whose terminal carry has absolute value at most halfStripBound M"]

- Lean declaration: [half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip](../../Erdos249257/TerminalOnlyCofinal.lean#L134)
- Lean declaration: [exists_infinite_support_half_of_cofinalTerminalOnlyStrip](../../Erdos249257/TerminalOnlyCofinal.lean#L192)

- outgoing **generalises**: [Z12::cofinal_admissibility_yields_257_counterexample](BROWSER_Z12_1.md#node-25b0e23ee881e72f). terminal-only witnesses drop both coherence between depths and all earlier-row carry control
- incoming **generalises**: [Z12::terminal_scaled_vanishing_yields_half](BROWSER_Z12_3.md#node-acd42d13a4214f3a). a named constructor maps every cofinal square-root-strip family into the scaled-vanishing interface, so the latter is strictly weaker
- incoming **implies**: [Z12::terminal_only_strip_error_bound](BROWSER_Z12_2.md#node-49a575b75a3059eb). the (4M+12)/2^M distance bound plus closedness is the whole proof of the cofinal consumer
- incoming **transport_of**: [Z16::cofinal_stages_conditional_export](BROWSER_Z16_1.md#node-8553dd45a9fd93a3). cofinalTerminalOnlyStrip_of_cofinalCylinderStages (SuffixCylinderTerminalOnlyBridge.lean) converts cofinal full-strip cylinder stages into the cofinal terminal-only strip supply consumed by exists_infinite_support_half_of_cofinalTerminalOnlyStrip (TerminalOnlyCofinal.lean).
- incoming **transport_of**: [Z16::terminal_only_projection](BROWSER_Z16_2.md#node-c949624af282f482). CylinderStage.halfTerminalOnlyStripWitness and halfTerminalOnlyStripWitness_of_protectedEvenSeamRealizedAt are the forgetting maps into HalfTerminalOnlyStripWitness, exactly the object quantified in HalfCarryCofinalTerminalOnlyStrip.
- incoming **finite_instance_of**: [Z16::certified_terminal_witnesses_51_52](BROWSER_Z16_1.md#node-4412dd0ecc306fff). the depth-51 and depth-52 stages project to normalized finite words with terminal carry inside the square-root strip, i.e. the HalfCarryCofinalTerminalOnlyStrip witness at exactly two depths.
- outgoing **depends_on_open**: [Z16::terminal_only_projection](BROWSER_Z16_2.md#node-c949624af282f482). the projection is the general route producing terminal-only strip witnesses from windows, stages and realized seams; it converts whatever stage supply exists into this antecedent, but produces witnesses only at depths already reached, so it discharges nothing on its own.
- incoming **specialises**: [Z16::cofinal_stages_conditional_export](BROWSER_Z16_1.md#node-8553dd45a9fd93a3). `cofinalTerminalOnlyStrip_of_cofinalCylinderStages` (SuffixCylinderTerminalOnlyBridge.lean:125) derives `HalfCarryCofinalTerminalOnlyStrip` from cofinal full cylinder stages; that predicate is the antecedent of Z12's `half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip`, and the conclusions agree.

<a id="node-49a575b75a3059eb"></a>
## terminal_only_strip_error_bound

A normalized finite half word of depth M with terminal carry in the square-root strip has support series within (4M+12)/2^M of 1/2; more generally the distance is at most (absolute terminal carry plus 2*sqrt(M)+4) divided by 2^M. No coherence between depths and no bound on earlier carries is needed.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [dist_half_erdosSupportSeries_wordSupport_le_of_terminalOnlyWitness](../../Erdos249257/TerminalOnlyCofinal.lean#L68)
- Lean declaration: [dist_half_erdosSupportSeries_wordSupport_le_carry_add_tail](../../Erdos249257/TerminalOnlyScaledVanishing.lean#L24)

- incoming **implies**: [Z12::integer_half_carry_calculus](BROWSER_Z12_1.md#node-59e84eab60406093). the same identity, used at a single terminal row rather than along a branch
- outgoing **implies**: [Z12::terminal_only_cofinal_yields_half](BROWSER_Z12_2.md#node-f8810011b82ac702). the (4M+12)/2^M distance bound plus closedness is the whole proof of the cofinal consumer
- incoming **implies**: [Z12::strip_envelope_subexponential](BROWSER_Z12_2.md#node-38ddb9d9557d7760). the strip envelope divided by the binary place value must vanish for the error bound to be useful
- incoming **specialises**: [Z13::finite_shadow_square_root_strip](BROWSER_Z13_1.md#node-b672d53f73e0ea3c). Z12's `dist_half_erdosSupportSeries_wordSupport_le_carry_add_tail` (TerminalOnlyScaledVanishing.lean:24) bounds |1/2 - value| by (|terminal carry| + 2 sqrt M + 4)/2^M using the terminal carry alone; Z13's `halfStripAdmissible_abs_residual_le` (HalfCylinderFiniteShadow.lean:532) is that bound under the strictly stronger HalfStripAdmissible hypothesis, which pins every prefix carry.

