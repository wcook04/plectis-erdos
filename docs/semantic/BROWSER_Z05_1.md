# Z05_1: Diagonal pincer bridge: foreign defect, full-target enclosures and the power-of-two margin socket

[All problems and zones](BROWSER.md)

<a id="node-0356de4599681438"></a>
## actual_correction_envelope_is_sub_edge

At every power-of-two endpoint with a >= 2, the actual odd-depth correction obeys the explicit three-letter envelope |correction| <= 8 H + 8n + 11, its integral half is bounded by 4H + 4n + 5, and at the odd-guarded canonical rank the sharpened envelope 4H + 2(2q+1) - 1 is *strictly smaller* than the final 1/32 edge 4^q/32. The next two corrections after the canonical rank are each below twice that edge. Hence every sub-edge hypothesis used downstream is automatic rather than assumed.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [abs_powerTwoOddDepthCorrection_le](../../Erdos249257/DiagonalFreshLossBridge.lean#L3730)
- Lean declaration: [abs_actualOddHalfCorrection_le](../../Erdos249257/DiagonalFreshLossBridge.lean#L4685)
- Lean declaration: [abs_actualOddHalfCorrection_le_canonicalEnvelope](../../Erdos249257/DiagonalFreshLossBridge.lean#L4707)
- Lean declaration: [canonicalActualOddHalfCorrectionEnvelope_lt_edge](../../Erdos249257/DiagonalFreshLossBridge.lean#L4725)
- Lean declaration: [abs_actualOddHalfCorrection_lt_canonicalHalfEdge](../../Erdos249257/DiagonalFreshLossBridge.lean#L4809)
- Lean declaration: [abs_actualOddHalfCorrection_next_two_lt_two_canonicalEdge](../../Erdos249257/DiagonalFlexibleOddWindowSupply.lean#L146)
- Lean declaration: [fourPow_pred_eq_eight_mul_edge](../../Erdos249257/DiagonalFreshLossBridge.lean#L4902)
- Lean declaration: [fourPow_eq_thirtyTwo_mul_edge](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L64)
- Lean declaration: [edge_succ](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L77)
- Lean declaration: [edge_add_two](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L88)
- Lean declaration: [edge_pos](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L95)

- incoming **depends_on_open**: [Z05::power_two_halfword_pointwise_equivalences](BROWSER_Z05_1.md#node-9e7d0d28856aad73). The unwrapping steps require the actual corrections to be sub-edge, which that node proves unconditionally.

<a id="node-d538933dca48abd4"></a>
## adjacent_gap_forces_certificate

If the modular displacement between the suffixes at two adjacent cuts exceeds the sum of the two edge widths in both circular directions - in particular if the residue sits inside a fixed 1/32 central band while the width inequality 32(3H + 2(J+m+3)) < 2^m holds - then at least one of the two cuts yields a full-depth fresh-loss certificate, hence a full-target miss.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap_sharp](../../Erdos249257/DiagonalFreshLossBridge.lean#L1670)
- Lean declaration: [diagonalFreshLossResidueCert_or_of_adjacent_suffix_gap](../../Erdos249257/DiagonalFreshLossBridge.lean#L1814)
- Lean declaration: [diagonalFreshLossResidueCert_or_of_adjacent_dyadic_gap](../../Erdos249257/DiagonalFreshLossBridge.lean#L1827)
- Lean declaration: [diagonalFreshLossResidueCert_or_of_powerTwo_oddGuard_halfWordBand](../../Erdos249257/DiagonalFreshLossBridge.lean#L4137)
- Lean declaration: [diagonalAdjacentSuffixGapWitness_of_powerTwoOddHalfWordBandAt](../../Erdos249257/DiagonalFlexibleOddWindowSupply.lean#L63)

- outgoing **specialises**: [Z05::sliding_suffix_transference](BROWSER_Z05_2.md#node-5bf8a0edc6b1c78f). The adjacent-cut gap argument is the sliding-suffix mechanism applied to the two cuts J and J+1.
- incoming **implies**: [Z05::canonical_depth_width_is_automatic](BROWSER_Z05_1.md#node-ec9305ffc247e670). It discharges the width hypothesis of the adjacent-gap consumer uniformly for t >= 3.

<a id="node-f06b3cca1e123141"></a>
## adjacent_suffix_raw_block_cocycle

The unreduced adjacent-suffix block satisfies an exact depth cocycle - growing by one binary place doubles the block, removes one copy of the terminal increment and appends the next - with a base-four two-step form; the adjacent residue is exactly that block modulo 2^m, and the residue-level cocycle is parity-free and independent of any LCM-jump hypothesis.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [diagonalAdjacentSuffixRawBlock_succ_depth](../../Erdos249257/DiagonalFreshLossBridge.lean#L1554)
- Lean declaration: [diagonalAdjacentSuffixRawBlock_add_two](../../Erdos249257/DiagonalFreshLossBridge.lean#L1589)
- Lean declaration: [diagonalAdjacentSuffixResidue_eq_rawBlock](../../Erdos249257/DiagonalFreshLossBridge.lean#L1602)
- Lean declaration: [diagonalAdjacentSuffixResidue_succ_depth](../../Erdos249257/DiagonalFreshLossBridge.lean#L1613)
- Lean declaration: [diagonalAdjacentSuffixResidue_target_depth](../../Erdos249257/DiagonalFreshLossBridge.lean#L1655)

- incoming **specialises**: [Z05::odd_depth_half_word_normal_form](BROWSER_Z05_1.md#node-3a3ab32cf446e183). It is the general raw-block cocycle restricted to power-of-two endpoints and odd depths.
- outgoing **specialises**: [Z05::sliding_suffix_transference](BROWSER_Z05_2.md#node-5bf8a0edc6b1c78f). The raw block is the unreduced form of the sliding-suffix residue at adjacent cuts.

<a id="node-7cfbca3d206afacd"></a>
## affine_scale_transport_of_diagonal

The diagonal at scale H equals C_H times the #249 constant plus an integer, with C_H = 2^H (2^H - 1). Along every ray H -> kH the coefficient multiplies by the explicit natural quotient Q_k(H) = 2^{(k-1)H} sum_{i<k} 2^{iH}, these quotients compose, and the diagonal transports affinely with an integer inhomogeneous term.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [scaleDiagonalTailDifference_eq](../../Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L45)
- Lean declaration: [diagonalCoefficient_mul](../../Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L76)
- Lean declaration: [scaleDiagonalTailDifference_mul](../../Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L109)
- Lean declaration: [diagonalScaleQuotient_comp](../../Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L226)
- Lean declaration: [diagonalCoefficient_pos](../../Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L69)

- incoming **depends_on_open**: [Z05::prime_adjunction_diamond_no_go](BROWSER_Z05_1.md#node-c04ac2655286fd3f). Upward propagation of hits is read off the affine transport formula; the barrier is its immediate consequence.
- incoming **specialises**: [Z05::explicit_shadow_transport_has_zero_diamond_curvature](BROWSER_Z05_1.md#node-0366082ca886326f). The curvature computation is the composition law for the scale quotients applied to the shadow coboundary.
- outgoing **transport_of**: [Z06::period_ray_telescoping](BROWSER_Z06_1.md#node-95058e2cbf8f7f44). scaleDiagonalTailDifference_mul / diagonalCoefficient_mul express the tail difference along the ray H -> kH with an explicit affine coefficient; tail_diff_mul is the same ray telescoping in unscaled coordinates.

<a id="node-36b1946fd772e79d"></a>
## canonical_centrality_pointwise_reductions

At a fixed LCM height, canonical 1/32 centrality of the adjacent-suffix residue is equivalent to the two literal unwrapped inequalities on twice the penultimate residue plus the signed one-step correction, and is implied by the penultimate residue occupying the stronger 1/16 band or by an explicit doubled-margin condition. The two band inequalities collapse to the sign of a single integer slack, which depends only on the LCM height and is therefore constant along every plateau between strict jumps.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Only two of the six evidence theorems are unconditional equivalences (central_iff_penultimate_exact, central_iff_slack_nonneg); the remaining ones (central_of_penultimate_strongBand, central_of_penultimate_margin, powerTwo_oddDepth_central_of_correction_bounds) are implications whose pointwise hypotheses - a stronger 1/16 band, a doubled-margin inequality, two-sided correction bounds - are not proved at any height in this corpus. Nothing here establishes centrality at even a single height; the node converts one unproved pointwise condition into another. Reclassified from unconditional_object_theorem for this reason.

- Lean declaration: [canonicalAdjacentSuffixResidue_central_iff_penultimate_exact](../../Erdos249257/DiagonalFreshLossBridge.lean#L2072)
- Lean declaration: [canonicalAdjacentSuffixResidue_central_of_penultimate_strongBand](../../Erdos249257/DiagonalFreshLossBridge.lean#L2163)
- Lean declaration: [canonicalAdjacentSuffixResidue_central_of_penultimate_margin](../../Erdos249257/DiagonalFreshLossBridge.lean#L2190)
- Lean declaration: [canonicalAdjacentSuffixCentral_iff_slack_nonneg](../../Erdos249257/DiagonalFreshLossBridge.lean#L2667)
- Lean declaration: [canonicalAdjacentSuffixCentralSlack_eq_of_periodLcm_eq](../../Erdos249257/DiagonalFreshLossBridge.lean#L2658)
- Lean declaration: [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_of_correction_bounds](../../Erdos249257/DiagonalFreshLossBridge.lean#L2613)

- outgoing **specialises**: [Z05::dyadic_centrality_calculus](BROWSER_Z05_1.md#node-e41c8d561c28e422). Each pointwise reduction instantiates a generic base-two or base-four centrality lemma at the canonical depth.
- incoming **generalises**: [Z05::centrality_supply_ladder_equivalences](BROWSER_Z05_1.md#node-e1fc2dd9e38f6da4). The supply relations are the pointwise reductions lifted over the cofinal quantifier.

<a id="node-ec9305ffc247e670"></a>
## canonical_depth_width_is_automatic

With ten guard bits beyond the binary scale of the LCM height, the analytic gap width inequality 32(3H + 2(m+3)) < 2^m holds automatically for every t >= 3, survives one extra parity guard bit and every later binary rank, and the elementary one-step correction envelope 3H + 2m + 1 is strictly smaller than the resulting 1/32 edge. All magnitude obligations of the adjacent-gap consumer are therefore discharged uniformly, leaving only an arithmetic centrality question.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [canonicalAdjacentSuffixDepth_width](../../Erdos249257/DiagonalFreshLossBridge.lean#L1875)
- Lean declaration: [canonicalAdjacentSuffixDepth_ten_le](../../Erdos249257/DiagonalFreshLossBridge.lean#L4039)
- Lean declaration: [canonicalAdjacentSuffixDepth_succ_width](../../Erdos249257/DiagonalFreshLossBridge.lean#L4045)
- Lean declaration: [oddGuardedCanonicalAdjacentSuffixDepth_width](../../Erdos249257/DiagonalFreshLossBridge.lean#L4108)
- Lean declaration: [adjacentDyadicWidth_succ](../../Erdos249257/DiagonalFlexibleOddWindowSupply.lean#L20)
- Lean declaration: [adjacentDyadicWidth_add_two](../../Erdos249257/DiagonalFlexibleOddWindowSupply.lean#L44)
- Lean declaration: [abs_diagonalHeightIncrement_le](../../Erdos249257/DiagonalFreshLossBridge.lean#L254)
- Lean declaration: [abs_diagonalWindowIncrement_le](../../Erdos249257/DiagonalFreshLossBridge.lean#L266)
- Lean declaration: [abs_diagonalTargetDepthCorrection_le](../../Erdos249257/DiagonalFreshLossBridge.lean#L279)
- Lean declaration: [diagonalTargetDepthCorrectionEnvelope_lt_canonical_edge](../../Erdos249257/DiagonalFreshLossBridge.lean#L1958)
- Lean declaration: [abs_diagonalTargetDepthCorrection_lt_canonical_edge](../../Erdos249257/DiagonalFreshLossBridge.lean#L1984)

- outgoing **implies**: [Z05::adjacent_gap_forces_certificate](BROWSER_Z05_1.md#node-d538933dca48abd4). It discharges the width hypothesis of the adjacent-gap consumer uniformly for t >= 3.
- incoming **implies**: [Z05::periodLcm_doubling_bound_via_central_binomial](BROWSER_Z05_1.md#node-04602213719d398e). The twelve-bit LCM saving is what keeps the canonical depth (plus one guard bit) below 2t.

<a id="node-e1fc2dd9e38f6da4"></a>
## centrality_supply_ladder_equivalences

A ladder of logical relations between the unproved cofinal sockets: the canonical central supply is equivalent to its exact penultimate-coordinate form, the strict-jump central supply is equivalent to the scalar slack supply, the power-of-two post-jump supply implies the general post-jump supply which transports across the plateau to the strict-jump supply, the penultimate strong-band supply implies the margin supply which implies canonical centrality, and canonical centrality supplies the adjacent-gap and projection sockets. Every proposition on both sides of every one of these relations is open.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["CanonicalAdjacentSuffixCentralSupply", "CanonicalAdjacentSuffixPenultimateExactSupply", "CanonicalAdjacentSuffixPenultimateMarginSupply", "CanonicalAdjacentSuffixPenultimateStrongBandSupply", "CanonicalAdjacentSuffixJumpCentralSupply", "CanonicalAdjacentSuffixJumpSlackSupply", "CanonicalAdjacentSuffixPostJumpSlackSupply", "CanonicalAdjacentSuffixPowerTwoPostJumpSlackSupply", "DiagonalAdjacentSuffixGapSupply", "DiagonalFreshLossProjectionSupply"]

- Lean declaration: [canonicalAdjacentSuffixCentralSupply_iff_penultimateExact](../../Erdos249257/DiagonalFreshLossBridge.lean#L2775)
- Lean declaration: [canonicalAdjacentSuffixJumpCentralSupply_iff_slackSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2757)
- Lean declaration: [canonicalAdjacentSuffixCentralSupply_of_penultimateMargin](../../Erdos249257/DiagonalFreshLossBridge.lean#L2796)
- Lean declaration: [canonicalAdjacentSuffixPenultimateMarginSupply_of_strongBand](../../Erdos249257/DiagonalFreshLossBridge.lean#L2809)
- Lean declaration: [canonicalAdjacentSuffixCentralSupply_of_penultimateStrongBand](../../Erdos249257/DiagonalFreshLossBridge.lean#L2835)
- Lean declaration: [canonicalAdjacentSuffixCentralSupply_of_jump](../../Erdos249257/DiagonalFreshLossBridge.lean#L2848)
- Lean declaration: [canonicalAdjacentSuffixPostJumpSlackSupply_of_powerTwo](../../Erdos249257/DiagonalFreshLossBridge.lean#L2699)
- Lean declaration: [canonicalAdjacentSuffixJumpSlackSupply_of_postJump](../../Erdos249257/DiagonalFreshLossBridge.lean#L2723)
- Lean declaration: [diagonalAdjacentSuffixGapSupply_of_canonical](../../Erdos249257/DiagonalFreshLossBridge.lean#L2857)
- Lean declaration: [diagonalFreshLossProjectionSupply_of_adjacentSuffixGapSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2870)

- outgoing **generalises**: [Z05::canonical_centrality_pointwise_reductions](BROWSER_Z05_1.md#node-36b1946fd772e79d). The supply relations are the pointwise reductions lifted over the cofinal quantifier.
- incoming **depends_on_open**: [Z05::supply_conditional_irrationality](BROWSER_Z05_2.md#node-e04cec5031f38bd6). Every rung of the ladder is an unproved proposition; the closures consume them as hypotheses.

<a id="node-58d9ee1fa2b10ca0"></a>
## channel_projected_pincer

For every prime p, integrality of the actual diagonal is equivalent to the residual obtained by splitting the selected u/(2^p - 1) channel representative off the explicit shadow, rescaling by the Mersenne modulus 2^p - 1, and asking it to hit -u modulo 2^p - 1. The selected upper-half channel target is a genuine unit, so the projected pincer cannot degenerate to a zero channel.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Restatement, not progress. Same private generic lemma diagonal_int_iff_hit_generic as the full-target pincer, with the modulus instantiated at 2^p - 1. The unit theorem lcmChannelTarget_isUnit only prevents the channel from degenerating; it decides nothing about the diagonal.

Open hypotheses: ["Both sides are open: the left side is integrality of the actual diagonal at height t; the right side is built from the same defect (defined as diagonal minus explicit shadow) by splitting off one computable channel representative and rescaling, so it is the same open condition in different coordinates."]

- Lean declaration: [diagonal_int_iff_renormalizedDefect_hits_freshTarget](../../Erdos249257/DiagonalPincerDecomposition.lean#L249)
- Lean declaration: [diagonal_not_int_iff_renormalizedDefect_misses_freshTarget](../../Erdos249257/DiagonalPincerDecomposition.lean#L264)
- Lean declaration: [lcmChannelTarget_isUnit](../../Erdos249257/DiagonalPincerDecomposition.lean#L128)

- outgoing **specialises**: [Z05::exact_full_target_pincer](BROWSER_Z05_1.md#node-faace0186be92bf5). Both are the same generic rational-lattice split; the channel form instantiates the modulus at 2^p - 1 instead of the reduced denominator d_t.
- outgoing **transport_of**: [Z04::upper_half_unit_target_is_unit](BROWSER_Z04_2.md#node-2f1139144e87b8b3). lcmChannelNumerator / lcmChannelTarget_isUnit (DiagonalPincerDecomposition.lean:119-147) instantiate upperHalfUnitTarget (lcmScale t) (lcmRadical t / p) p (jordanTotientTwo ...) and are closed by upperHalfUnitTarget_isUnit_of_primeFactors_le.
- outgoing **transport_of**: [Z04::upper_half_channel_survives_scaled_denominator](BROWSER_Z04_2.md#node-12d3b49c3ef22e0b). The projected pincer splits off the channel representative u/(2^p-1) at p in upperHalfPrimes t and rescales by channelModulus p = mersenne p, which is the T4 channel whose survival in the reduced denominator upperHalfChannel_survivorProduct_dvd_den establishes.

<a id="node-9f3918d03e2e3d48"></a>
## controlled_projection_miss_is_conditional

If the difference between the actual foreign defect and the finite projected foreign state is inside the closed geometric budget, and the finite rational state is farther from every integer than that budget, then the full target is missed at that scale. The first hypothesis is not proved anywhere in the corpus.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hcontrol : ControlledForeignProjection H D, i.e. |scaleForeignDefect H - projectedForeignDefect H D| <= foreignComplementBound H D"]

- Lean declaration: [scaleFullTarget_miss_of_projected_separation](../../Erdos249257/ActualForeignResidueProjection.lean#L414)
- Lean declaration: [scaleFullTarget_miss_of_abs_sub_le_of_forall_int](../../Erdos249257/ActualForeignResidueProjection.lean#L435)

- outgoing **depends_on_open**: [Z05::foreign_residue_kernel_geometric_budget](BROWSER_Z05_1.md#node-bd4881781ae08e83). The budget bounds windows of the posited kernel; controlling the actual complement by it is the unproved hypothesis.
- incoming **implies**: [Z05::tail_limit_supplies_controlled_projection](BROWSER_Z05_2.md#node-09a688c7b68b7c4b). The tail-limit hypothesis discharges ControlledForeignProjection and hence feeds the miss consumer.

<a id="node-e41c8d561c28e422"></a>
## dyadic_centrality_calculus

A calculus of exact re-expressions of dyadic centrality: modular centrality after a base-two step equals two literal integer inequalities when the appended correction is sub-edge; it is implied by an old 1/16 band or by an explicit envelope margin; it is decided by the top bit of the penultimate residue, with an exact carry/edge-alignment normal form for failure; a base-four step preserves the band under exact two-sided correction bounds; and for the centred lift, centrality is exactly the affine exclusion e <= |4u + c|.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [baseTwoTargetResidue_central_iff_unwrapped](../../Erdos249257/DiagonalFreshLossBridge.lean#L1997)
- Lean declaration: [baseTwoTargetResidue_central_of_strongBand](../../Erdos249257/DiagonalFreshLossBridge.lean#L2099)
- Lean declaration: [baseTwoTargetResidue_central_of_envelope](../../Erdos249257/DiagonalFreshLossBridge.lean#L2134)
- Lean declaration: [baseFourResidue_central_of_correction_bounds](../../Erdos249257/DiagonalFreshLossBridge.lean#L2575)
- Lean declaration: [baseTwoTargetResidue_central_iff_topBit](../../Erdos249257/DiagonalFreshLossBridge.lean#L2999)
- Lean declaration: [baseTwoTargetResidue_noncentral_iff_carryEdgeAlignment](../../Erdos249257/DiagonalFreshLossBridge.lean#L3046)
- Lean declaration: [emod_central_of_abs_between](../../Erdos249257/DiagonalFreshLossBridge.lean#L3403)
- Lean declaration: [baseFour_actual_central_iff_affineExclusion](../../Erdos249257/DiagonalFreshLossBridge.lean#L4823)
- Lean declaration: [baseFour_actual_central_of_sharpSignFreeMargin](../../Erdos249257/DiagonalFreshLossBridge.lean#L4864)
- Lean declaration: [baseFour_actual_central_iff_signedMargin](../../Erdos249257/DiagonalFreshLossBridge.lean#L5090)
- Lean declaration: [actualAffineExclusion_iff_signedMargin](../../Erdos249257/DiagonalFreshLossBridge.lean#L5038)
- Lean declaration: [baseFour_positiveWrap_ediv_succ](../../Erdos249257/DiagonalFreshLossBridge.lean#L4342)

- incoming **specialises**: [Z05::canonical_centrality_pointwise_reductions](BROWSER_Z05_1.md#node-36b1946fd772e79d). Each pointwise reduction instantiates a generic base-two or base-four centrality lemma at the canonical depth.
- incoming **reformulates**: [Z05::edge_cylinder_rank_pullback](BROWSER_Z05_1.md#node-ca55aca7270649b3). Edge-cylinder occupation and centrality are complementary descriptions of the same dyadic residue.

<a id="node-ca55aca7270649b3"></a>
## edge_cylinder_rank_pullback

Occupation of a width-e edge cylinder about a multiple of M is exactly the two edge intervals of the Euclidean residue, its witness multiple is unique, and two consecutive edge occupations force the intervening base-four correction into a four-times-wider cylinder about a multiple of the new modulus. At dyadic scale M = 32e, two (resp. three) future edge ranks are equivalent to two (resp. three) literal inequalities in one lifted old base-four cell.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [nearMultiple_iff_emod_edge](../../Erdos249257/DiagonalFreshLossBridge.lean#L3659)
- Lean declaration: [nearMultiple_correction_of_twoRank](../../Erdos249257/DiagonalFreshLossBridge.lean#L3698)
- Lean declaration: [powerTwoOddDepthCorrection_nearMultiple_of_twoRank](../../Erdos249257/DiagonalFreshLossBridge.lean#L3712)
- Lean declaration: [nearMultiple_witness_unique](../../Erdos249257/DiagonalFreshLossBridge.lean#L4420)
- Lean declaration: [twoFutureEdgeRanks_iff_oldStateCrossing](../../Erdos249257/DiagonalFreshLossBridge.lean#L4438)
- Lean declaration: [threeFutureEdgeRanks_iff_oldStateCrossing](../../Erdos249257/DiagonalFreshLossBridge.lean#L4514)
- Lean declaration: [baseFour_edge_iff_centered_tube](../../Erdos249257/DiagonalFreshLossBridge.lean#L4363)

- incoming **finite_instance_of**: [Z05::finite_fixtures_and_boundary_evaluations](BROWSER_Z05_1.md#node-dac5156479470d86). The a = 7, q = 91..93 fixture instantiates the old-cell crossing inequalities and shows the third one failing.
- outgoing **reformulates**: [Z05::dyadic_centrality_calculus](BROWSER_Z05_1.md#node-e41c8d561c28e422). Edge-cylinder occupation and centrality are complementary descriptions of the same dyadic residue.

<a id="node-af8734c12d7019a3"></a>
## enclosure_to_full_target_miss_consumer

A producer-independent consumer: any centre q and proved radius eps with |diagonal - q| <= eps and eps < |q - z| for every integer z forces a miss of the full reduced target at that scale. Specialised to the squared-Mersenne centre, exact rational separation of the computable centre suffices.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [scaleFullTarget_miss_of_enclosure](../../Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L171)
- Lean declaration: [scaleFullTarget_miss_of_lambert_projected_separation](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L426)

- outgoing **depends_on_open**: [Z05::squared_mersenne_enclosure_of_actual_diagonal](BROWSER_Z05_2.md#node-b188d68d0d565e58). The consumer is vacuous without a proved radius; the squared-Mersenne enclosure supplies the only unconditional one in this zone.

<a id="node-fbb671e409a6e203"></a>
## endpoint_fresh_deficit_decomposition

Adding prime support cannot raise Euler's density: g | n implies phi(n) g <= n phi(g), so the old-prime endpoint mass at kH + s always dominates the actual totient and every endpoint fresh deficit is nonnegative. The endpoint mass is affine in k with slope the old Mobius increment, so the actual diagonal height increment is exactly the old increment plus the lower endpoint deficit minus the upper one, and the literal foreign channel equals the difference of the two deficits. Applying one or two discrete curvature operators gives the coefficient rows [-2,1,1] and [-8,4,2,1,1], and nonnegativity of the deficits makes the displayed adverse weighted deficit the only loss from the old-prime margin.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [totient_mul_le_mul_totient_of_dvd](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L45)
- Lean declaration: [totient_le_div_mul_totient_of_dvd](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L78)
- Lean declaration: [endpointFreshDeficit_nonneg](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L91)
- Lean declaration: [oldPrimeEndpointMass_eq_affine](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L137)
- Lean declaration: [oldPrimeEndpointMass_two_sub_one](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L162)
- Lean declaration: [diagonalHeightIncrement_eq_old_add_endpointFreshDeficits](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L171)
- Lean declaration: [finiteForeignChannelIncrement_eq_endpointFreshDeficit_sub](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L184)
- Lean declaration: [fourCurvaturePlusShift_eq_fivePoint](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L205)
- Lean declaration: [offsetCurvature_diagonalHeightIncrement_eq_old_add_deficits](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L216)
- Lean declaration: [fourCurvaturePlusShift_diagonalHeightIncrement_eq_old_add_deficits](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L229)
- Lean declaration: [oldCurvature_sub_firstBranchAdverseDeficit_le_actual](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L255)
- Lean declaration: [oldFivePoint_sub_secondBranchAdverseDeficit_le_actual](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L269)

- outgoing **reformulates**: [Z05::old_foreign_channel_split_of_totient_increment](BROWSER_Z05_1.md#node-03192a64d50a7b93). It rewrites the same literal foreign channel as the difference of two nonnegative endpoint deficits.

<a id="node-a158017228125ba8"></a>
## envelope_only_no_go

A correction-envelope-only strategy cannot force edge escape. Zero correction keeps a signed sub-edge state inside the scaled tube at every base-four rank; more generally the zero-start affine orbit driven by any corrections of magnitude below 2e stays strictly inside 4^j e for every j; and two nonzero sub-edge corrections are compatible with three consecutive edge tubes when the old state sits at the zero lift. Any cofinal escape theorem must therefore use an arithmetic relation between the actual state and its corrections, not their magnitudes alone, and cannot be rescued by inspecting more ranks.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rules out only proofs whose sole input about the corrections is a uniform magnitude envelope (|c| < 2e, or c = 0), for any number of inspected base-four ranks. It does NOT rule out: arguments using the sign, congruence class, or arithmetic correlation between the actual state and its corrections; arguments using the specific structure of powerTwoOddDepthCorrection (parity, foreign-pulse sparsity, prime confinement) already available in this zone; arguments at a different rank family or modulus; or a proof that the actual orbit never sits at the zero lift. The witness is a *constructed* orbit, not the actual #249 orbit, so no statement about the actual state follows.

- Lean declaration: [baseFour_zeroCorrection_centered_tube_forever](../../Erdos249257/DiagonalFreshLossBridge.lean#L4413)
- Lean declaration: [zeroAffineOrbit_geometric_bound](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L199)
- Lean declaration: [zeroAffineOrbit_stays_in_scaled_edge](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L225)
- Lean declaration: [threeEdgeWindow_feasible_at_zero_of_subedge](../../Erdos249257/DiagonalFlexibleOddWindowSupply.lean#L203)

- outgoing **barrier_for**: [Z05::power_two_supply_ladder_equivalences](BROWSER_Z05_1.md#node-cb014211c50cacf6). It shows the three-scale affine escape supply cannot be obtained from correction magnitudes alone, at any number of ranks.
- incoming **specialises**: [Z05::three_rank_window_core_no_go](BROWSER_Z05_2.md#node-a899ca2488ea67cb). Same obstruction made quantitative for the three-rank window actually used by the flexible producer.

<a id="node-faace0186be92bf5"></a>
## exact_full_target_pincer

Write the LCM-diagonal tail difference as the exact reduced rational shadow a_t/d_t plus a foreign defect defined as the remainder. Then the diagonal is an integer if and only if d_t times the foreign defect is congruent to -a_t modulo d_t. The same equivalence holds verbatim at an arbitrary positive scale H, where the full-target hit predicate is literally integrality of the diagonal, so the lattice witness is not an independent state variable.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Restatement, not progress. The equivalence is the elementary fact x in Z iff d(x - a/d) = -a mod d, applied to a defect defined as the diagonal minus a computable rational. Neither side is decided at any height by this node; the only unconditional non-integrality in the zone (t = 7) is imported, not produced here. The same remark applies to scaleFullTargetHit_iff_integral, whose own docstring states the lattice witness is not an independent state variable.

Open hypotheses: ["Both sides are open and definitionally interchangeable: the left side is integrality of the actual diagonal at height t (cofinal non-integrality of which is exactly the pre-existing open input of the landed completeness theorem), and foreignDiagonalDefect t is *defined* as diagonalTailDifference t - explicitLcmShadow t, so the right side carries no independent information."]

- Lean declaration: [diagonal_int_iff_foreignDiagonalDefect_hits_fullTarget](../../Erdos249257/DiagonalPincerDecomposition.lean#L215)
- Lean declaration: [diagonal_int_iff_exists_fullTarget_lattice](../../Erdos249257/DiagonalPincerDecomposition.lean#L233)
- Lean declaration: [diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget](../../Erdos249257/DiagonalPincerDecomposition.lean#L241)
- Lean declaration: [scaleFullTargetHit_iff_integral](../../Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L139)
- Lean declaration: [diagonalTailDifference_eq_explicit_add_foreign](../../Erdos249257/DiagonalPincerDecomposition.lean#L104)
- Lean declaration: [explicitLcmShadow_eq_num_div_den](../../Erdos249257/DiagonalPincerDecomposition.lean#L92)
- Lean declaration: [lcmShadowNumerator_coprime_denominator](../../Erdos249257/DiagonalPincerDecomposition.lean#L87)

- incoming **specialises**: [Z05::channel_projected_pincer](BROWSER_Z05_1.md#node-58d9ee1fa2b10ca0). Both are the same generic rational-lattice split; the channel form instantiates the modulus at 2^p - 1 instead of the reduced denominator d_t.
- incoming **depends_on_open**: [Z05::supply_conditional_irrationality](BROWSER_Z05_2.md#node-e04cec5031f38bd6). Its weakest antecedent is, by the pincer, literally cofinal non-integrality of the actual diagonal, which is unproved.
- incoming **finite_instance_of**: [Z05::t_seven_finite_full_target_miss](BROWSER_Z05_2.md#node-7cc8cb692e7c3423). It is the pincer's miss side verified at the single height t = 7.
- incoming **alias_of**: [Z05::lcm_height_implementations_agree](BROWSER_Z05_1.md#node-9fda23c35c99c591). It reconciles the two definitions of the LCM height used on either side of the pincer.
- outgoing **equivalent_to**: [Z06::endpoint_certificate_completeness](BROWSER_Z06_1.md#node-2151751ccfb38f8d). foreignDiagonalDefect t is defined as diagonalTailDifference t - explicitLcmShadow t (DiagonalPincerDecomposition.lean), so diagonal_int_iff_foreignDiagonalDefect_hits_fullTarget is integrality of R_{2H_t}-R_{H_t}, exactly the cell decided by periodLcm_diagonal_kill_iff_tail_diff_notMem_int.
- outgoing **transport_of**: [Z04::lcm_height_exact_denominator](BROWSER_Z04_1.md#node-6f532b908aa314db). explicitLcmShadowRat t is defined as (lcmHeight t) * numericMobiusShadow (lcmHeight t) (DiagonalPincerDecomposition.lean:69), so the pincer modulus d_t = lcmShadowDenominator t is exactly the reduced denominator computed by lcmHeight_scaledMobiusShadow_den_exact.
- incoming **equivalent_to**: [Z08::window_separated_pairs_equivalent_to_249](BROWSER_Z08_2.md#node-c5d275f2b251a636). Chaining dtwWindowSeparatedPairs_iff_irrational_totient_series with irrational_totient_series_iff_lcm_diagonal_certificate_supply and periodLcm_diagonal_kill_iff_tail_diff_notMem_int puts the geometric separated-pairs socket and the diagonal full-target predicate on the same open proposition.

<a id="node-0366082ca886326f"></a>
## explicit_shadow_transport_has_zero_diamond_curvature

Transporting the actual foreign defect along a scale ray produces an inhomogeneous term that is exactly the endpoint coboundary Q_k(H) E_H - E_{kH} of the explicit shadow. Its two-prime diamond curvature vanishes identically, so the complete state built from explicit-shadow fibres has zero holonomy on such diagrams.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Only the correction built from the *explicit shadow* is shown to be a coboundary with vanishing (p,q) diamond curvature. It does not rule out positive holonomy for an independently defined projection of the actual foreign state accompanied by a theorem controlling the discarded complement - which is precisely the route attempted by the residue-projection and squared-Mersenne enclosure nodes in this zone. It also says nothing about non-abelian or higher-arity diagrams, or about curvature of the diagonal at non-multiplicative scale families.

- Lean declaration: [scaleForeignDefect_mul](../../Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L215)
- Lean declaration: [foreignTransportCorrection_primeAdjunction_flat](../../Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L247)

- outgoing **specialises**: [Z05::affine_scale_transport_of_diagonal](BROWSER_Z05_1.md#node-7cfbca3d206afacd). The curvature computation is the composition law for the scale quotients applied to the shadow coboundary.
- incoming **repair_of**: [Z05::squared_mersenne_enclosure_of_actual_diagonal](BROWSER_Z05_2.md#node-b188d68d0d565e58). The zero-curvature barrier asks for an independently defined projection with a controlled complement; the squared-Mersenne centre plus its explicit radius is exactly such a projection.

<a id="node-dac5156479470d86"></a>
## finite_fixtures_and_boundary_evaluations

Kernel-checked finite evaluations used to pin interfaces: the signed-split safety data at power-of-two endpoints a = 2,...,7; the exact integer geometry of the a = 7 edge pair showing the old-cell literals hold at q = 91, 92, fail at q = 93, and that q = 93 is central; and small boundary numerals for the LCM height and channel modulus.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [canonical_a2_to_a7_signedSplitSafe_fixture](../../Erdos249257/DiagonalFreshLossBridge.lean#L3632)
- Lean declaration: [powerTwo_a7_q91_q93_oldCell_integer_fixture](../../Erdos249257/DiagonalFreshLossBridge.lean#L4592)
- Lean declaration: [periodLcm_eq_lcmHeight_five](../../Erdos249257/DiagonalPincerDecomposition.lean#L340)
- Lean declaration: [channelModulus_three](../../Erdos249257/DiagonalPincerDecomposition.lean#L343)

- outgoing **finite_instance_of**: [Z05::signed_split_recombination](BROWSER_Z05_2.md#node-613e62cde5372a10). The a = 2..7 fixture is the only supply of signed representatives satisfying the safety condition.
- outgoing **finite_instance_of**: [Z05::edge_cylinder_rank_pullback](BROWSER_Z05_1.md#node-ca55aca7270649b3). The a = 7, q = 91..93 fixture instantiates the old-cell crossing inequalities and shows the third one failing.

<a id="node-e8cab0f11b8bfa7b"></a>
## foreign_pulse_sparsity_and_prime_confinement

Every nonzero foreign Mobius phase term has a squarefree index which divides exactly one of the two endpoints, and at an LCM height every such index exceeds the scale t. Distinct endpoint hits of one channel are at least d offsets apart, so inside a window shorter than 2t a foreign channel hits each endpoint at most twice and a channel with d >= 2t at most once; a squarefree channel repeating a hit inside such a window is forced to be an actual prime, with exactly two support representatives and explicitly computed quotients. At every power-of-two scale a >= 4 the odd-guarded canonical window is short enough for this confinement to apply.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [foreign_endpoint_support_disjoint](../../Erdos249257/DiagonalFreshLossBridge.lean#L852)
- Lean declaration: [foreignChannelPhaseTerm_ne_zero_support](../../Erdos249257/DiagonalFreshLossBridge.lean#L894)
- Lean declaration: [squarefree_of_foreignChannelPhaseTerm_ne_zero](../../Erdos249257/DiagonalFreshLossBridge.lean#L909)
- Lean declaration: [foreignChannelPhaseTerm_eq_neg_of_low](../../Erdos249257/DiagonalFreshLossBridge.lean#L920)
- Lean declaration: [foreignChannelPhaseTerm_eq_of_top](../../Erdos249257/DiagonalFreshLossBridge.lean#L930)
- Lean declaration: [foreignChannelPhaseTerm_low_double_echo](../../Erdos249257/DiagonalFreshLossBridge.lean#L941)
- Lean declaration: [foreignChannelPhaseTerm_weighted_low_double_echo](../../Erdos249257/DiagonalFreshLossBridge.lean#L961)
- Lean declaration: [dvd_offset_sub_of_two_low_supports](../../Erdos249257/DiagonalFreshLossBridge.lean#L975)
- Lean declaration: [channel_le_offset_sub_of_two_low_supports](../../Erdos249257/DiagonalFreshLossBridge.lean#L984)
- Lean declaration: [dvd_offset_sub_of_two_top_supports](../../Erdos249257/DiagonalFreshLossBridge.lean#L993)
- Lean declaration: [channel_le_offset_sub_of_two_top_supports](../../Erdos249257/DiagonalFreshLossBridge.lean#L1002)
- Lean declaration: [lt_of_not_dvd_periodLcm](../../Erdos249257/DiagonalFreshLossBridge.lean#L1011)
- Lean declaration: [prime_of_squarefree_not_dvd_periodLcm_lt_two_mul](../../Erdos249257/DiagonalFreshLossBridge.lean#L1019)
- Lean declaration: [repeated_low_support_primePow_of_short_periodLcm_window](../../Erdos249257/DiagonalFreshLossBridge.lean#L1035)
- Lean declaration: [prime_of_squarefree_repeated_low_support_in_short_periodLcm_window](../../Erdos249257/DiagonalFreshLossBridge.lean#L1053)
- Lean declaration: [repeated_top_support_primePow_of_short_periodLcm_window](../../Erdos249257/DiagonalFreshLossBridge.lean#L1070)
- Lean declaration: [prime_of_squarefree_repeated_top_support_in_short_periodLcm_window](../../Erdos249257/DiagonalFreshLossBridge.lean#L1087)
- Lean declaration: [not_three_low_supports_of_short_foreign_window](../../Erdos249257/DiagonalFreshLossBridge.lean#L1211)
- Lean declaration: [not_three_top_supports_of_short_foreign_window](../../Erdos249257/DiagonalFreshLossBridge.lean#L1224)
- Lean declaration: [not_two_low_supports_of_squarefree_tail_window](../../Erdos249257/DiagonalFreshLossBridge.lean#L1238)
- Lean declaration: [not_two_top_supports_of_squarefree_tail_window](../../Erdos249257/DiagonalFreshLossBridge.lean#L1249)
- Lean declaration: [eq_or_eq_add_of_modEq_of_pos_le_two_mul](../../Erdos249257/DiagonalFreshLossBridge.lean#L1261)
- Lean declaration: [prime_lower_support_iff_eq_base_or_add](../../Erdos249257/DiagonalFreshLossBridge.lean#L1288)
- Lean declaration: [prime_top_base_eq](../../Erdos249257/DiagonalFreshLossBridge.lean#L1312)
- Lean declaration: [prime_top_support_iff_eq_base_or_add](../../Erdos249257/DiagonalFreshLossBridge.lean#L1330)
- Lean declaration: [prime_lower_support_quotient](../../Erdos249257/DiagonalFreshLossBridge.lean#L1341)
- Lean declaration: [prime_top_support_quotient](../../Erdos249257/DiagonalFreshLossBridge.lean#L1359)
- Lean declaration: [finiteForeignChannelRawPulse_eq_zero_of_dvd](../../Erdos249257/DiagonalFreshLossBridge.lean#L1378)
- Lean declaration: [squarefree_of_finiteForeignChannelRawPulse_ne_zero](../../Erdos249257/DiagonalFreshLossBridge.lean#L1385)
- Lean declaration: [lt_of_finiteForeignChannelRawPulse_periodLcm_ne_zero](../../Erdos249257/DiagonalFreshLossBridge.lean#L1396)
- Lean declaration: [prime_of_squarefree_repeated_low_support_powerTwo_oddGuarded](../../Erdos249257/DiagonalFreshLossBridge.lean#L3992)
- Lean declaration: [prime_of_squarefree_repeated_top_support_powerTwo_oddGuarded](../../Erdos249257/DiagonalFreshLossBridge.lean#L4008)

- incoming **implies**: [Z05::periodLcm_doubling_bound_via_central_binomial](BROWSER_Z05_1.md#node-04602213719d398e). Shortness of the canonical window relative to 2t is the hypothesis of the prime-confinement theorems.
- outgoing **depends_on_open**: [Z05::old_foreign_channel_split_of_totient_increment](BROWSER_Z05_1.md#node-03192a64d50a7b93). The pulses whose support it counts are the summands produced by the channel swap.

<a id="node-bd4881781ae08e83"></a>
## foreign_residue_kernel_geometric_budget

For a *defined* per-channel Mobius residue kernel, every channel above the stable threshold 2H < d contributes mu(d) C_H times a fixed Mersenne factor bounded by 2/2^d + 4/4^d; hence every finite window of omitted channels beyond a cutoff D >= 2H is bounded in absolute value by the closed budget C_H (2/2^D + 4/(3 4^D)). The finite state splits exactly into the retained foreign projection and a divisor part equal to the literal truncated Mobius shadow. The identification of this kernel with the actual totient tail is NOT proved anywhere in the zone.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Not about phi(n)/2^n. Every theorem in this node is about the *defined* function foreignResidueKernel and the finite sums built from it; nothing in this zone (or, as the module docstring concedes, anywhere yet) proves that this kernel sums to the actual totient tail, nor that projectedForeignDefect approximates scaleForeignDefect. The class 'unconditional_object_theorem' here means only that the Lean statements carry no unproved hypothesis; it must NOT be read as a result about the actual #249 objects. Do not count this node as progress on #249 until the kernel identity is supplied; the consumers that would use it (controlled_projection_miss_is_conditional, tail_limit_supplies_controlled_projection, renormalized_residue_agreement_is_conditional) are all explicitly conditional.

- Lean declaration: [foreignResidueKernel_of_lt](../../Erdos249257/ActualForeignResidueProjection.lean#L60)
- Lean declaration: [residueIncrement_of_dvd](../../Erdos249257/ActualForeignResidueProjection.lean#L88)
- Lean declaration: [residueIncrement_of_twice_lt](../../Erdos249257/ActualForeignResidueProjection.lean#L108)
- Lean declaration: [stableResidueFactor_nonneg](../../Erdos249257/ActualForeignResidueProjection.lean#L124)
- Lean declaration: [stableResidueFactor_le_geometric](../../Erdos249257/ActualForeignResidueProjection.lean#L131)
- Lean declaration: [abs_residueIncrement_le_geometric](../../Erdos249257/ActualForeignResidueProjection.lean#L162)
- Lean declaration: [abs_foreignTailWindow_le_geometric_sum](../../Erdos249257/ActualForeignResidueProjection.lean#L195)
- Lean declaration: [geometric_window_le_closed_complement](../../Erdos249257/ActualForeignResidueProjection.lean#L222)
- Lean declaration: [abs_foreignTailWindow_le_foreignComplementBound](../../Erdos249257/ActualForeignResidueProjection.lean#L276)
- Lean declaration: [finiteResidueDiagonal_eq_projectedForeign_add_divisor](../../Erdos249257/ActualForeignResidueProjection.lean#L308)
- Lean declaration: [projectedDivisorChannels_eq_truncated_mobius](../../Erdos249257/ActualForeignResidueProjection.lean#L320)
- Lean declaration: [residueOffset_eq_sub_of_lt](../../Erdos249257/ActualForeignResidueProjection.lean#L32)
- Lean declaration: [positiveResidueIncrement_coe](../../Erdos249257/ActualForeignResidueProjection.lean#L81)

- incoming **depends_on_open**: [Z05::controlled_projection_miss_is_conditional](BROWSER_Z05_1.md#node-9f3918d03e2e3d48). The budget bounds windows of the posited kernel; controlling the actual complement by it is the unproved hypothesis.

<a id="node-9fda23c35c99c591"></a>
## lcm_height_implementations_agree

The recursive universal-period LCM and the finite-LCM definition used by the channel family are the same natural number at every index.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [periodLcm_eq_lcmHeight](../../Erdos249257/DiagonalPincerDecomposition.lean#L41)

- outgoing **alias_of**: [Z05::exact_full_target_pincer](BROWSER_Z05_1.md#node-faace0186be92bf5). It reconciles the two definitions of the LCM height used on either side of the pincer.

<a id="node-3a3ab32cf446e183"></a>
## odd_depth_half_word_normal_form

At a power-of-two endpoint every diagonal increment at positive offset is even, so every odd-depth correction is even and the odd-depth adjacent-suffix residue equals exactly twice the integral base-four half-correction word reduced modulo 4^q; the even seed contributes nothing. For q >= 3 the 1/32 centrality band of the residue is therefore literally the band 4^q <= 32 (halfword mod 4^q) <= 31 4^q, its top bit is the parity of the quotient of the correction word, and the normalised half-word is a telescoping sum of base-four digits, i.e. the non-seed part of the normalised raw window.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [powerTwoOddCorrectionWord_succ](../../Erdos249257/DiagonalFreshLossBridge.lean#L3135)
- Lean declaration: [diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_closed](../../Erdos249257/DiagonalFreshLossBridge.lean#L3165)
- Lean declaration: [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_closed](../../Erdos249257/DiagonalFreshLossBridge.lean#L3182)
- Lean declaration: [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_lowBits](../../Erdos249257/DiagonalFreshLossBridge.lean#L3193)
- Lean declaration: [diagonalWindowIncrement_even_of_two_le_periodLcm](../../Erdos249257/DiagonalFreshLossBridge.lean#L3217)
- Lean declaration: [diagonalWindowIncrement_even_of_two_le_offset](../../Erdos249257/DiagonalFreshLossBridge.lean#L3232)
- Lean declaration: [powerTwoOddDepthCorrection_even](../../Erdos249257/DiagonalFreshLossBridge.lean#L3249)
- Lean declaration: [diagonalAdjacentSuffixRawBlock_powerTwo_zero_one_even](../../Erdos249257/DiagonalFreshLossBridge.lean#L3269)
- Lean declaration: [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_eq_correctionWord](../../Erdos249257/DiagonalFreshLossBridge.lean#L3284)
- Lean declaration: [powerTwoOddHalfCorrectionWord_succ](../../Erdos249257/DiagonalFreshLossBridge.lean#L3310)
- Lean declaration: [powerTwoOddCorrectionWord_eq_two_mul_halfWord](../../Erdos249257/DiagonalFreshLossBridge.lean#L3317)
- Lean declaration: [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_eq_two_mul_halfWord](../../Erdos249257/DiagonalFreshLossBridge.lean#L3335)
- Lean declaration: [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_iff_halfWordBand](../../Erdos249257/DiagonalFreshLossBridge.lean#L3352)
- Lean declaration: [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_topBit_iff](../../Erdos249257/DiagonalFreshLossBridge.lean#L4288)
- Lean declaration: [int_emod_two_mul_ge_iff_odd_ediv](../../Erdos249257/DiagonalFreshLossBridge.lean#L4250)
- Lean declaration: [powerTwoOddHalfCorrectionWord_normalized_step](../../Erdos249257/DiagonalFreshLossBridge.lean#L4304)
- Lean declaration: [powerTwoOddHalfCorrectionWord_normalized_eq_sum](../../Erdos249257/DiagonalFreshLossBridge.lean#L4316)
- Lean declaration: [powerTwoOddHalfCorrectionWord_eq_raw_sub_seed](../../Erdos249257/DiagonalFreshLossBridge.lean#L4330)
- Lean declaration: [diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_half_emod](../../Erdos249257/DiagonalFreshLossBridge.lean#L3537)
- Lean declaration: [diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_even](../../Erdos249257/DiagonalFreshLossBridge.lean#L3558)
- Lean declaration: [actualCenteredLift_modEq](../../Erdos249257/DiagonalFreshLossBridge.lean#L4652)
- Lean declaration: [abs_actualCenteredLift_le_half](../../Erdos249257/DiagonalFreshLossBridge.lean#L4887)
- Lean declaration: [actualOddHalfCenteredLift_modEq_halfCorrectionWord](../../Erdos249257/DiagonalFreshLossBridge.lean#L4659)
- Lean declaration: [actualOddHalf_affine_modEq_halfCorrectionWord_succ](../../Erdos249257/DiagonalFreshLossBridge.lean#L4670)
- Lean declaration: [halfWordBandAt_iff_state_abs](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L120)
- Lean declaration: [centeredBand_iff_abs](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L102)

- outgoing **specialises**: [Z05::power_two_even_seam_inheritance](BROWSER_Z05_1.md#node-068d049d6c516229). The closed odd-depth orbit is the even-seam cocycle iterated in base four.
- outgoing **specialises**: [Z05::adjacent_suffix_raw_block_cocycle](BROWSER_Z05_1.md#node-f06b3cca1e123141). It is the general raw-block cocycle restricted to power-of-two endpoints and odd depths.
- incoming **depends_on_open**: [Z05::power_two_halfword_pointwise_equivalences](BROWSER_Z05_1.md#node-9e7d0d28856aad73). The half-word band predicate they re-express is defined by the odd-depth normal form.

<a id="node-03192a64d50a7b93"></a>
## old_foreign_channel_split_of_totient_increment

Under one common finite Mobius cutoff, the actual diagonal height increment phi(2H+s) - phi(H+s) is the sum of all totalized channel differences, and splits exactly into the divisor ('old') part - which equals (H / rad H) times the positive gcd-word coefficient at the same offset - plus the literal sum over channels not dividing H. The same split holds for the binary-reversed raw blocks, and after a global channel swap the actual reversed numerator is one fixed gcd-word block plus a finite sum of sparse foreign raw pulses.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [oldMobiusIncrement_eq_sum_forwardDifference_channel](../../Erdos249257/DiagonalFreshLossBridge.lean#L625)
- Lean declaration: [oldMobiusIncrement_eq_scale_gcdWordCoeff](../../Erdos249257/DiagonalFreshLossBridge.lean#L653)
- Lean declaration: [totient_eq_boundedMobiusChannelSum](../../Erdos249257/DiagonalFreshLossBridge.lean#L737)
- Lean declaration: [diagonalHeightIncrement_eq_sum_channelDifferences](../../Erdos249257/DiagonalFreshLossBridge.lean#L762)
- Lean declaration: [boundedOldChannelSum_eq_oldMobiusIncrement](../../Erdos249257/DiagonalFreshLossBridge.lean#L791)
- Lean declaration: [diagonalHeightIncrement_eq_oldMobius_add_finiteForeign](../../Erdos249257/DiagonalFreshLossBridge.lean#L829)
- Lean declaration: [finiteForeignChannelIncrement_eq_phaseSum](../../Erdos249257/DiagonalFreshLossBridge.lean#L881)
- Lean declaration: [forwardDifference_mobiusTotientChannel_of_not_dvd](../../Erdos249257/DiagonalFreshLossBridge.lean#L863)
- Lean declaration: [finiteForeignChannelIncrement_eq_enlarged_phaseSum](../../Erdos249257/DiagonalFreshLossBridge.lean#L1406)
- Lean declaration: [oldMobiusRawBlock_eq_scale_gcdWordRawBlock](../../Erdos249257/DiagonalFreshLossBridge.lean#L1121)
- Lean declaration: [diagonalAdjacentSuffixRawBlock_eq_oldMobius_add_finiteForeign](../../Erdos249257/DiagonalFreshLossBridge.lean#L1138)
- Lean declaration: [diagonalAdjacentSuffixRawBlock_sub_oldMobius_eq_finiteForeign](../../Erdos249257/DiagonalFreshLossBridge.lean#L1153)
- Lean declaration: [finiteForeignChannelRawBlock_eq_sum_rawPulses](../../Erdos249257/DiagonalFreshLossBridge.lean#L1434)
- Lean declaration: [diagonalAdjacentSuffixRawBlock_eq_scaledGcdWord_add_sum_foreignRawPulses](../../Erdos249257/DiagonalFreshLossBridge.lean#L1537)
- Lean declaration: [squarefree_dvd_squarefreeKernel](../../Erdos249257/DiagonalFreshLossBridge.lean#L641)
- Lean declaration: [oldMobiusIncrement_eq_div_gcd_mul_totient](../../Erdos249257/FreshPrimeDeficitDecomposition.lean#L113)

- incoming **reformulates**: [Z05::endpoint_fresh_deficit_decomposition](BROWSER_Z05_1.md#node-fbb671e409a6e203). It rewrites the same literal foreign channel as the difference of two nonnegative endpoint deficits.
- incoming **depends_on_open**: [Z05::foreign_pulse_sparsity_and_prime_confinement](BROWSER_Z05_1.md#node-e8cab0f11b8bfa7b). The pulses whose support it counts are the summands produced by the channel swap.
- incoming **specialises**: [Z05::signed_split_recombination](BROWSER_Z05_2.md#node-613e62cde5372a10). It recombines exactly the old and foreign halves produced by the split.

<a id="node-3f458ba5562cd213"></a>
## one_bit_lift_arithmetic

Elementary 2-adic lifting: after cancelling a nonzero common factor, one extra factor of two is exactly parity of the remaining cofactor; so given 2^k | z, divisibility by 2^{k+1} is equivalent to evenness of z / 2^k, a congruence modulo 2^k has exactly the two lifts x = y and x = y + 2^k modulo 2^{k+1}, and the offset class is equivalent to failure of the lift. Concretely at the 16-to-32 scale, fifth-bit agreement is parity of the signed fourth-bit quotient.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [mul_two_dvd_mul_iff_even](../../Erdos249257/PowerTwoBitLift.lean#L27)
- Lean declaration: [two_pow_succ_dvd_iff_quotient_even](../../Erdos249257/PowerTwoBitLift.lean#L34)
- Lean declaration: [two_pow_succ_modEq_iff_quotient_even](../../Erdos249257/PowerTwoBitLift.lean#L47)
- Lean declaration: [two_pow_succ_modEq_or_offset](../../Erdos249257/PowerTwoBitLift.lean#L56)
- Lean declaration: [thirtyTwo_dvd_iff_even_sixteen_cofactor](../../Erdos249257/PowerTwoBitLift.lean#L82)
- Lean declaration: [thirtyTwo_dvd_iff_sixteen_quotient_even](../../Erdos249257/PowerTwoBitLift.lean#L90)
- Lean declaration: [modEq_thirtyTwo_iff_sixteen_quotient_even](../../Erdos249257/PowerTwoBitLift.lean#L97)
- Lean declaration: [not_modEq_thirtyTwo_iff_sixteen_quotient_odd](../../Erdos249257/PowerTwoBitLift.lean#L103)
- Lean declaration: [modEq_thirtyTwo_iff_even_difference_cofactor](../../Erdos249257/PowerTwoBitLift.lean#L111)
- Lean declaration: [modEq_thirtyTwo_or_offset_sixteen](../../Erdos249257/PowerTwoBitLift.lean#L122)
- Lean declaration: [not_modEq_thirtyTwo_iff_offset_sixteen](../../Erdos249257/PowerTwoBitLift.lean#L129)

- incoming **barrier_for**: [Z05::parity_does_not_decide_margin_socket](BROWSER_Z05_1.md#node-ebb3abeaf7833c41). The bit-lift lane reduces the fifth-bit question to a parity check; this shows parity alone cannot decide the reduced margin socket.
- incoming **reformulates**: [Z05::signed_margin_socket_is_failure_of_next_lift](BROWSER_Z05_1.md#node-606c1c148c6cc5cb). It transports the divisibility-lift statements into the centred-lift and signed-margin coordinates the #249 socket actually uses.

<a id="node-ebb3abeaf7833c41"></a>
## parity_does_not_decide_margin_socket

For an even modulus m = 2r and an integral radius A with 16 < A < 8m - 16, each parity class of the reduced quotient contains both a point inside the reduced margin socket (distance below A/16 of a multiple of m) and a point outside it - the hits 0 and 1, the misses r and r+1. Hence knowing only the parity bit of the quotient cannot decide the socket. The power-of-two specialisation applies to a modulus 2^k.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rules out only a decision of the socket from the single parity bit of the quotient, and only in the numerical regime 16 < A < 8m - 16. It does not rule out deciding the socket from two or more bits, from the residue modulo a higher power of two, from sign information, or from any non-bitwise arithmetic input. It is stated for an abstract (m, A) pair: the actual t = 827 margin constant is not exposed in this library, so the theorem is not instantiated at the real row and does not by itself close the t = 827 fifth-bit lane.

- Lean declaration: [not_reducedMarginSocket_midpoint](../../Erdos249257/Totient827ParitySocketCeiling.lean#L27)
- Lean declaration: [not_reducedMarginSocket_midpoint_add_one](../../Erdos249257/Totient827ParitySocketCeiling.lean#L48)
- Lean declaration: [reducedMarginSocket_not_decided_by_parity](../../Erdos249257/Totient827ParitySocketCeiling.lean#L73)
- Lean declaration: [powerTwo_reducedMarginSocket_not_decided_by_parity](../../Erdos249257/Totient827ParitySocketCeiling.lean#L110)

- outgoing **barrier_for**: [Z05::one_bit_lift_arithmetic](BROWSER_Z05_1.md#node-3f458ba5562cd213). The bit-lift lane reduces the fifth-bit question to a parity check; this shows parity alone cannot decide the reduced margin socket.

<a id="node-04602213719d398e"></a>
## periodLcm_doubling_bound_via_central_binomial

Every positive index up to 2n divides lcm(1..n) times the central binomial coefficient C(2n,n) - new indices are prime powers whose last prime is supplied by a Kummer carry - hence lcm(1..2n) <= lcm(1..n) 4^n. Starting from the exact base lcm(1..16) < 2^20, the doubling estimate preserves a twelve-bit saving, giving lcm(1..2^a) < 2^{2^{a+1} - 12} for a >= 4, which is exactly what makes the canonical depth (and one extra guard bit) shorter than 2t.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [periodLcm_dvd_of_forall_pos_le](../../Erdos249257/DiagonalFreshLossBridge.lean#L3794)
- Lean declaration: [one_le_factorization_centralBinom_of_prime_pow_window](../../Erdos249257/DiagonalFreshLossBridge.lean#L3810)
- Lean declaration: [prime_dvd_centralBinom_of_prime_pow_window](../../Erdos249257/DiagonalFreshLossBridge.lean#L3828)
- Lean declaration: [periodLcm_two_mul_dvd_periodLcm_mul_centralBinom](../../Erdos249257/DiagonalFreshLossBridge.lean#L3842)
- Lean declaration: [periodLcm_two_mul_le_periodLcm_mul_centralBinom](../../Erdos249257/DiagonalFreshLossBridge.lean#L3883)
- Lean declaration: [periodLcm_two_mul_le_periodLcm_mul_four_pow](../../Erdos249257/DiagonalFreshLossBridge.lean#L3892)
- Lean declaration: [periodLcm_sixteen_lt_two_pow_twenty](../../Erdos249257/DiagonalFreshLossBridge.lean#L3904)
- Lean declaration: [periodLcm_pow_two_lt_two_pow_guardTwelve](../../Erdos249257/DiagonalFreshLossBridge.lean#L3911)
- Lean declaration: [canonicalAdjacentSuffixDepth_powerTwo_succ_lt_two_mul](../../Erdos249257/DiagonalFreshLossBridge.lean#L3942)
- Lean declaration: [canonicalAdjacentSuffixDepth_powerTwo_lt_two_mul](../../Erdos249257/DiagonalFreshLossBridge.lean#L3973)
- Lean declaration: [oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_lt_two_mul](../../Erdos249257/DiagonalFreshLossBridge.lean#L3982)

- outgoing **implies**: [Z05::canonical_depth_width_is_automatic](BROWSER_Z05_1.md#node-ec9305ffc247e670). The twelve-bit LCM saving is what keeps the canonical depth (plus one guard bit) below 2t.
- outgoing **implies**: [Z05::foreign_pulse_sparsity_and_prime_confinement](BROWSER_Z05_1.md#node-e8cab0f11b8bfa7b). Shortness of the canonical window relative to 2t is the hypothesis of the prime-confinement theorems.

<a id="node-4f1dfa64497467e2"></a>
## periodLcm_strict_jump_classification

lcm(1..t) increases at t+1 exactly when t+1 does not already divide it; beyond t >= 2 that happens exactly at prime-power endpoints, and then the height gains exactly one factor of that prime. Every endpoint 2^a with a >= 2 is such a jump and doubles the height exactly, strict jumps occur beyond every index, and a power-of-two jump adds exactly one canonical guard bit.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [periodLcm_strict_jump_iff_succ_not_dvd](../../Erdos249257/DiagonalFreshLossBridge.lean#L2298)
- Lean declaration: [succ_eq_prime_pow_of_periodLcm_strict_jump](../../Erdos249257/DiagonalFreshLossBridge.lean#L2319)
- Lean declaration: [periodLcm_succ_eq_prime_mul_of_strict_jump](../../Erdos249257/DiagonalFreshLossBridge.lean#L2332)
- Lean declaration: [periodLcm_factorization_two_lt_of_lt_pow_two](../../Erdos249257/DiagonalFreshLossBridge.lean#L2395)
- Lean declaration: [periodLcm_pow_two_strict_jump](../../Erdos249257/DiagonalFreshLossBridge.lean#L2416)
- Lean declaration: [periodLcm_pow_two_eq_two_mul](../../Erdos249257/DiagonalFreshLossBridge.lean#L2434)
- Lean declaration: [exists_periodLcm_strict_jump_ge](../../Erdos249257/DiagonalFreshLossBridge.lean#L2635)
- Lean declaration: [canonicalAdjacentSuffixDepth_powerTwo_jump](../../Erdos249257/DiagonalFreshLossBridge.lean#L3083)

- incoming **depends_on_open**: [Z05::power_two_even_seam_inheritance](BROWSER_Z05_1.md#node-068d049d6c516229). The seam statements are conditioned on the exact doubling of the LCM height at a power-of-two jump.
- outgoing **reformulates**: [Z06::lcm_ray_divisibility_skeleton](BROWSER_Z06_1.md#node-190e1b1c4523c82a). periodLcm_strict_jump_iff_succ_not_dvd and periodLcm_succ_eq_prime_mul_of_strict_jump sharpen the ray skeleton facts periodLcm_dvd_periodLcm and periodLcm_strict_jump_sub_ge to an exact prime-power jump classification of the same object.

<a id="node-068d049d6c516229"></a>
## power_two_even_seam_inheritance

Across a power-of-two LCM jump the height doubles, and then every even post-jump offset is inherited from the old height: the increment doubles when the reduced offset is even and is copied unchanged when it is odd. Consequently the only post-jump increment outside the even-inheritance seam at each odd-depth base-four step is the single new odd terminal offset, and the odd-depth residue step depends only on the previous residue and one exact correction.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [diagonalHeightIncrement_two_mul_even](../../Erdos249257/DiagonalFreshLossBridge.lean#L308)
- Lean declaration: [diagonalHeightIncrement_two_mul_odd](../../Erdos249257/DiagonalFreshLossBridge.lean#L323)
- Lean declaration: [diagonalWindowIncrement_evenSeam_even](../../Erdos249257/DiagonalFreshLossBridge.lean#L338)
- Lean declaration: [diagonalWindowIncrement_evenSeam_odd](../../Erdos249257/DiagonalFreshLossBridge.lean#L348)
- Lean declaration: [diagonalWindowIncrement_powerTwoJump_even](../../Erdos249257/DiagonalFreshLossBridge.lean#L2462)
- Lean declaration: [diagonalWindowIncrement_powerTwoJump_odd](../../Erdos249257/DiagonalFreshLossBridge.lean#L2472)
- Lean declaration: [diagonalWindowIncrement_powerTwoJump_even_offset](../../Erdos249257/DiagonalFreshLossBridge.lean#L2504)
- Lean declaration: [diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_step](../../Erdos249257/DiagonalFreshLossBridge.lean#L2517)
- Lean declaration: [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_step](../../Erdos249257/DiagonalFreshLossBridge.lean#L2537)
- Lean declaration: [diagonalTargetDepthCorrection_powerTwo_of_even_predepth](../../Erdos249257/DiagonalFreshLossBridge.lean#L3096)
- Lean declaration: [diagonalTargetDepthCorrection_powerTwo_of_odd_predepth](../../Erdos249257/DiagonalFreshLossBridge.lean#L3113)
- Lean declaration: [diagonalWindowIncrement_eq_heightIncrement](../../Erdos249257/DiagonalFreshLossBridge.lean#L247)

- outgoing **depends_on_open**: [Z05::periodLcm_strict_jump_classification](BROWSER_Z05_1.md#node-4f1dfa64497467e2). The seam statements are conditioned on the exact doubling of the LCM height at a power-of-two jump.
- incoming **specialises**: [Z05::odd_depth_half_word_normal_form](BROWSER_Z05_1.md#node-3a3ab32cf446e183). The closed odd-depth orbit is the even-seam cocycle iterated in base four.

<a id="node-9e7d0d28856aad73"></a>
## power_two_halfword_pointwise_equivalences

At the odd-guarded canonical rank of a power-of-two endpoint, the half-word central band is exactly the actual penultimate signed-margin condition on the centred predecessor state and its correction, and is implied by a single scalar margin inequality. Under the automatic sub-edge correction bounds, the disjunction of the three half-word bands at consecutive base-four ranks is exactly one three-scale affine escape disjunction in the actual state, and failure of the three-rank band is literally three consecutive edge occupations.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [powerTwoOddGuardHalfWordBand_iff_actualPenultimateSignedMargin](../../Erdos249257/DiagonalFreshLossBridge.lean#L5102)
- Lean declaration: [powerTwoOddGuardHalfWordBand_of_actualPenultimateMargin](../../Erdos249257/DiagonalFreshLossBridge.lean#L4937)
- Lean declaration: [threeRankBandAt_iff_threeScaleAffineEscapeAt](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L325)
- Lean declaration: [threeRankBandAt_iff_threeScaleAffineEscapeAt_of_shortCorrections](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L236)
- Lean declaration: [not_three_consecutive_edge_iff_threeRankBand](../../Erdos249257/DiagonalFlexibleOddWindowSupply.lean#L187)
- Lean declaration: [state_succ_eq_affine_of_abs_lt_half](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L146)
- Lean declaration: [state_succ_eq_affine_of_edge_of_shortCorrection](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L170)
- Lean declaration: [eq_of_modEq_of_centered_bounds](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L42)

- incoming **generalises**: [Z05::power_two_supply_ladder_equivalences](BROWSER_Z05_1.md#node-cb014211c50cacf6). The supply equivalences are the pointwise half-word/signed-margin equivalences quantified cofinally.
- outgoing **depends_on_open**: [Z05::odd_depth_half_word_normal_form](BROWSER_Z05_1.md#node-3a3ab32cf446e183). The half-word band predicate they re-express is defined by the odd-depth normal form.
- outgoing **depends_on_open**: [Z05::actual_correction_envelope_is_sub_edge](BROWSER_Z05_1.md#node-0356de4599681438). The unwrapping steps require the actual corrections to be sub-edge, which that node proves unconditionally.
- incoming **reformulates**: [Z05::signed_margin_socket_is_failure_of_next_lift](BROWSER_Z05_1.md#node-606c1c148c6cc5cb). Both describe the same ActualPenultimateSignedMargin predicate, one in divisibility coordinates and one in half-word coordinates.

<a id="node-cb014211c50cacf6"></a>
## power_two_supply_ladder_equivalences

At the cofinal-supply level, the actual penultimate signed-margin supply is *equivalent* to the odd-guard half-word band supply, the envelope-margin supply implies it, the half-word band supply and the flexible three-rank band supply both supply the adjacent-gap socket, and the three-rank band supply is equivalent to the three-scale affine escape supply. Both sides of every equivalence here are open.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["PowerTwoActualPenultimateSignedMarginSupply", "PowerTwoOddGuardHalfWordBandSupply", "PowerTwoActualPenultimateEnvelopeMarginSupply", "PowerTwoOddGuardThreeRankBandSupply", "ThreeScaleAffineEscapeSupply", "DiagonalAdjacentSuffixGapSupply"]

- Lean declaration: [powerTwoActualPenultimateSignedMarginSupply_iff_halfWordBandSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L5172)
- Lean declaration: [powerTwoOddGuardHalfWordBandSupply_of_actualPenultimateEnvelopeMargin](../../Erdos249257/DiagonalFreshLossBridge.lean#L5000)
- Lean declaration: [diagonalAdjacentSuffixGapSupply_of_powerTwoOddGuardHalfWordBand](../../Erdos249257/DiagonalFreshLossBridge.lean#L4210)
- Lean declaration: [diagonalAdjacentSuffixGapSupply_of_powerTwoOddGuardThreeRankBand](../../Erdos249257/DiagonalFlexibleOddWindowSupply.lean#L93)
- Lean declaration: [powerTwoOddGuardThreeRankBandSupply_iff_threeScaleAffineEscapeSupply](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L349)

- outgoing **generalises**: [Z05::power_two_halfword_pointwise_equivalences](BROWSER_Z05_1.md#node-9e7d0d28856aad73). The supply equivalences are the pointwise half-word/signed-margin equivalences quantified cofinally.
- incoming **barrier_for**: [Z05::envelope_only_no_go](BROWSER_Z05_1.md#node-a158017228125ba8). It shows the three-scale affine escape supply cannot be obtained from correction magnitudes alone, at any number of ranks.
- incoming **barrier_for**: [Z05::three_rank_window_core_no_go](BROWSER_Z05_2.md#node-a899ca2488ea67cb). It fixes the exact central core that any no-three-consecutive-edge theorem must exclude by other means.

<a id="node-c04ac2655286fd3f"></a>
## prime_adjunction_diamond_no_go

Because a full-target hit at H forces a full-target hit at every multiple kH, the conjunction of the four hits at H, pH, qH and pqH is logically equivalent to the single hit at H. The proposed two-prime full-target adjunction square therefore carries no information beyond its bottom vertex and cannot be an obstruction route.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Closes only the four-hit square built from ScaleFullTargetHit at H, pH, qH, pqH, and only because hits propagate upward. It does not rule out: an obstruction at a single scale; downward (divisor-direction) arguments; scale families that are not multiplicative rays; diagrams of arity other than two; or any route that works with a projection of the actual foreign state rather than with the hit predicate itself. No primality or freshness of p, q is used or needed, so it also says nothing specific about fresh primes.

- Lean declaration: [scaleFullTargetHit_mul](../../Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L184)
- Lean declaration: [fullTarget_primeAdjunction_diamond_iff_root](../../Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L196)

- outgoing **depends_on_open**: [Z05::affine_scale_transport_of_diagonal](BROWSER_Z05_1.md#node-7cfbca3d206afacd). Upward propagation of hits is read off the affine transport formula; the barrier is its immediate consequence.

<a id="node-4e3095a52f116a67"></a>
## renormalized_residue_agreement_is_conditional

If the corrected residue presentation of the projected diagonal agrees with the canonical squared-Mersenne rational centre, then separation of the corrected residue projection from the integer lattice forces a full-target miss. The agreement is a stated obligation, not a theorem.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hagrees : RenormalizedResidueAgreement H D, i.e. renormalizedResidueProjection H D = lambertProjectedDiagonal H D"]

- Lean declaration: [scaleFullTarget_miss_of_renormalized_residue_separation](../../Erdos249257/ActualForeignResidueProjection.lean#L468)

- outgoing **reformulates**: [Z05::squared_mersenne_enclosure_of_actual_diagonal](BROWSER_Z05_2.md#node-b188d68d0d565e58). It routes the residue projection into the already-proved squared-Mersenne separation consumer, conditional on agreement of the two presentations.

<a id="node-606c1c148c6cc5cb"></a>
## signed_margin_socket_is_failure_of_next_lift

For M > 0 with M | z, a sub-edge correction |c| < e and the midpoint budget e + |c| <= 4M, the centred lift of z modulo 2M is 0 when z/M is even and the positive midpoint M when it is odd; the zero state can never satisfy the signed-margin socket and the midpoint state always does. Hence the actual penultimate signed-margin socket at the centred lift is *equivalent to failure* of the next divisibility lift, i.e. to 2M not dividing z - not to its success. At the concrete 16-to-32 scale it is exactly oddness of z/16, equivalently 32 not dividing z.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [actualCenteredLift_mul_eq_zero_of_even](../../Erdos249257/PowerTwoCenteredBitLift.lean#L26)
- Lean declaration: [actualCenteredLift_mul_eq_midpoint_of_odd](../../Erdos249257/PowerTwoCenteredBitLift.lean#L40)
- Lean declaration: [actualCenteredLift_of_dvd_eq_ite_even](../../Erdos249257/PowerTwoCenteredBitLift.lean#L56)
- Lean declaration: [not_actualPenultimateSignedMargin_zero](../../Erdos249257/PowerTwoCenteredBitLift.lean#L72)
- Lean declaration: [actualPenultimateSignedMargin_midpoint](../../Erdos249257/PowerTwoCenteredBitLift.lean#L82)
- Lean declaration: [actualPenultimateSignedMargin_centeredLift_iff_quotient_odd](../../Erdos249257/PowerTwoCenteredBitLift.lean#L103)
- Lean declaration: [actualPenultimateSignedMargin_centeredLift_iff_not_twice_dvd](../../Erdos249257/PowerTwoCenteredBitLift.lean#L121)
- Lean declaration: [actualPenultimateSignedMargin_centeredThirtyTwo_iff_quotient_odd](../../Erdos249257/PowerTwoCenteredBitLift.lean#L147)
- Lean declaration: [actualPenultimateSignedMargin_centeredThirtyTwo_iff_not_thirtyTwo_dvd](../../Erdos249257/PowerTwoCenteredBitLift.lean#L159)

- outgoing **reformulates**: [Z05::one_bit_lift_arithmetic](BROWSER_Z05_1.md#node-3f458ba5562cd213). It transports the divisibility-lift statements into the centred-lift and signed-margin coordinates the #249 socket actually uses.
- outgoing **reformulates**: [Z05::power_two_halfword_pointwise_equivalences](BROWSER_Z05_1.md#node-9e7d0d28856aad73). Both describe the same ActualPenultimateSignedMargin predicate, one in divisibility coordinates and one in half-word coordinates.

