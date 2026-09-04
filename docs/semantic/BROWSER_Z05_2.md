# Z05_2: Diagonal pincer bridge: foreign defect, full-target enclosures and the power-of-two margin socket

[All problems and zones](BROWSER.md)

<a id="node-613e62cde5372a10"></a>
## signed_split_recombination

If signed representatives x, y of the halved old-Mobius and halved literal-foreign blocks satisfy an explicit same-direction / opposite-direction safety condition modulo M = 32e, then their recombination avoids both width-e edge cylinders, so the actual halved reversed numerator is central. Specialised to a power-of-two odd depth this yields exactly the half-word band consumed downstream. The evenness of the old block, and the signed representative data, are hypotheses supplied only by finite fixtures.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [abs_add_between_of_signedSplitSafe](../../Erdos249257/DiagonalFreshLossBridge.lean#L3428)
- Lean declaration: [signedSplitSafe_emod_central](../../Erdos249257/DiagonalFreshLossBridge.lean#L3484)
- Lean declaration: [add_ediv_two_of_even](../../Erdos249257/DiagonalFreshLossBridge.lean#L3495)
- Lean declaration: [diagonalAdjacentSuffixRawBlock_half_central_of_signedSplit](../../Erdos249257/DiagonalFreshLossBridge.lean#L3512)
- Lean declaration: [powerTwoOddHalfWordBand_of_signedSplit](../../Erdos249257/DiagonalFreshLossBridge.lean#L3586)
- Lean declaration: [diagonalAdjacentSuffixResidue_powerTwo_oddDepth_central_of_signedSplit](../../Erdos249257/DiagonalFreshLossBridge.lean#L3611)
- Lean declaration: [finiteForeignChannelRawBlock_powerTwo_oddDepth_even_of_old](../../Erdos249257/DiagonalFreshLossBridge.lean#L3571)

- outgoing **specialises**: [Z05::old_foreign_channel_split_of_totient_increment](BROWSER_Z05_1.md#node-03192a64d50a7b93). It recombines exactly the old and foreign halves produced by the split.
- incoming **finite_instance_of**: [Z05::finite_fixtures_and_boundary_evaluations](BROWSER_Z05_1.md#node-dac5156479470d86). The a = 2..7 fixture is the only supply of signed representatives satisfying the safety condition.

<a id="node-5bf8a0edc6b1c78f"></a>
## sliding_suffix_transference

The depth-(J+m) binary window numerator splits as 2^m times its depth-J prefix plus the translated depth-m window, so the depth-(J+m) diagonal residue reduces modulo 2^m to the sliding-suffix residue at cut J, which is the dyadically weighted sum of the signed window increments after the cut. Consequently centrality of the last m bits alone already yields the full-depth asymmetric certificate: no estimate of the J-bit prefix is required.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [windowNumerator_prefix_suffix](../../Erdos249257/DiagonalFreshLossBridge.lean#L225)
- Lean declaration: [diagonalSuffixResidue_eq_increment_sum](../../Erdos249257/DiagonalFreshLossBridge.lean#L368)
- Lean declaration: [diagonalWindowResidue_mod_suffix](../../Erdos249257/DiagonalFreshLossBridge.lean#L386)
- Lean declaration: [diagonalFreshLossResidueCert_of_suffix_central](../../Erdos249257/DiagonalFreshLossBridge.lean#L409)
- Lean declaration: [diagonalSuffixResidue_succ_cut](../../Erdos249257/DiagonalFreshLossBridge.lean#L531)
- Lean declaration: [diagonalAdjacentSuffixResidue_eq_terminal_corrected](../../Erdos249257/DiagonalFreshLossBridge.lean#L589)

- outgoing **implies**: [Z05::two_vertex_certificate_forces_full_target_miss](BROWSER_Z05_2.md#node-54adf16238fe95fb). Centrality of the last m bits alone yields the full-depth residue certificate consumed by the pincer.
- incoming **specialises**: [Z05::adjacent_gap_forces_certificate](BROWSER_Z05_1.md#node-d538933dca48abd4). The adjacent-cut gap argument is the sliding-suffix mechanism applied to the two cuts J and J+1.
- incoming **specialises**: [Z05::adjacent_suffix_raw_block_cocycle](BROWSER_Z05_1.md#node-f06b3cca1e123141). The raw block is the unreduced form of the sliding-suffix residue at adjacent cuts.

<a id="node-b188d68d0d565e58"></a>
## squared_mersenne_enclosure_of_actual_diagonal

For every scale H and every cutoff D, the actual diagonal lies within an explicit radius 4 C_H / (3 (2^{D+1} - 1)^2) of the exactly computable rational centre Z_H + C_H (1/2 + sum_{d<=D} mu(d)/(2^d - 1)^2). No residue split and no 2H <= D condition is used. Consequently any exact rational separation of that centre from the integer lattice forces a genuine full-target miss.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The enclosure itself is unconditional and effective, but no height in this zone is ever verified to satisfy the separation hypothesis of the consumer, so the enclosure yields zero unconditional full-target misses here. The radius is proportional to C_H = 2^H(2^H - 1), so a usable separation requires a cutoff D growing with H and an exact rational computation that this zone does not perform. The underlying identity sum phi(n)/2^n = 1/2 + sum_d mu(d)/(2^d-1)^2 is imported classical mathematics, not new content.

- Lean declaration: [scaleDiagonalTailDifference_sub_lambertProjectedDiagonal](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L138)
- Lean declaration: [abs_mobiusSquareTail_le](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L167)
- Lean declaration: [abs_scaleDiagonalTailDifference_sub_lambertProjectedDiagonal_le](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L408)
- Lean declaration: [mobius_square_series_eq_partial_add_tail](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L94)
- Lean declaration: [mersenne_shift_lower_bound](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L151)
- Lean declaration: [totientSeries_eq_pnat_half_pow](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L72)

- outgoing **repair_of**: [Z05::explicit_shadow_transport_has_zero_diamond_curvature](BROWSER_Z05_1.md#node-0366082ca886326f). The zero-curvature barrier asks for an independently defined projection with a controlled complement; the squared-Mersenne centre plus its explicit radius is exactly such a projection.
- incoming **depends_on_open**: [Z05::enclosure_to_full_target_miss_consumer](BROWSER_Z05_1.md#node-af8734c12d7019a3). The consumer is vacuous without a proved radius; the squared-Mersenne enclosure supplies the only unconditional one in this zone.
- incoming **reformulates**: [Z05::renormalized_residue_agreement_is_conditional](BROWSER_Z05_1.md#node-4e3095a52f116a67). It routes the residue projection into the already-proved squared-Mersenne separation consumer, conditional on agreement of the two presentations.
- outgoing **transport_of**: [Z07::moebius_square_lens_of_249](BROWSER_Z07_1.md#node-a9f26d2d7d41fdbc). The enclosure centre Z_H + C_H(1/2 + sum_{d<=D} mu(d)/(2^d-1)^2) is the finite truncation of totientSeries_eq_pnat_half_pow, the same identity Z07 proves as tsum_totient_half_pow_eq_half_add_moebius_sq.

<a id="node-e04cec5031f38bd6"></a>
## supply_conditional_irrationality

Eighteen theorems of the shape: if some cofinal supply of finite avoidance/centrality events exists, then the sum of phi(n)/2^n is irrational. Every one of them is an implication with an unproved antecedent; none of them proves irrationality. By the exact full-target pincer the weakest antecedent (a cofinal supply of full-target misses) is literally cofinal non-integrality of the actual diagonal, which is exactly the pre-existing open input of the landed completeness theorem, so this family re-dresses the open problem rather than reducing it.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: None of the eighteen antecedents is proved anywhere in this corpus (no theorem in Erdos249257/ or ErdosProblems/ concludes any *Supply predicate without assuming one). The count of eighteen also overstates the number of distinct routes: by the pincer, FullTargetAvoidanceSupply, UpperHalfChannelAvoidanceSupply and FreshPrimeChannelAvoidanceSupply are all literally cofinal non-integrality of the actual diagonal, and the remaining fifteen form a single implication lattice of progressively stronger sufficient conditions for that same target (see centrality_supply_ladder_equivalences and power_two_supply_ladder_equivalences, both already flagged as restatements). The zone therefore contains one open target, not eighteen partial results.

Open hypotheses: ["FullTargetAvoidanceSupply : forall t0, exists t, t0 <= t and not ForeignDiagonalDefectHitsFullTarget t", "UpperHalfChannelAvoidanceSupply : forall t0, exists t >= t0, 5 <= t and exists p in upperHalfPrimes t, not RenormalizedDefectHitsFreshTarget t p", "FreshPrimeChannelAvoidanceSupply : forall p0, exists prime p >= max p0 5, not RenormalizedDefectHitsFreshTarget p p", "DiagonalFreshLossProjectionSupply (cofinal firing of the [1,2] cone certificate)", "DiagonalAdjacentSuffixGapSupply (cofinal adjacent-suffix dyadic gap witness)", "CanonicalAdjacentSuffixCentralSupply (cofinal centrality at the canonical depth)", "CanonicalAdjacentSuffixPenultimateExactSupply", "CanonicalAdjacentSuffixPenultimateMarginSupply", "CanonicalAdjacentSuffixPenultimateStrongBandSupply", "CanonicalAdjacentSuffixJumpCentralSupply", "CanonicalAdjacentSuffixJumpSlackSupply", "CanonicalAdjacentSuffixPostJumpSlackSupply", "CanonicalAdjacentSuffixPowerTwoPostJumpSlackSupply", "PowerTwoOddGuardHalfWordBandSupply", "PowerTwoActualPenultimateEnvelopeMarginSupply", "PowerTwoActualPenultimateSignedMarginSupply", "PowerTwoOddGuardThreeRankBandSupply", "ThreeScaleAffineEscapeSupply"]

- Lean declaration: [irrational_totientSeries_of_full_target_avoidance_supply](../../Erdos249257/DiagonalPincerDecomposition.lean#L290)
- Lean declaration: [irrational_totientSeries_of_upper_half_channel_avoidance_supply](../../Erdos249257/DiagonalPincerDecomposition.lean#L316)
- Lean declaration: [irrational_totientSeries_of_fresh_prime_channel_avoidance_supply](../../Erdos249257/DiagonalPincerDecomposition.lean#L328)
- Lean declaration: [irrational_totientSeries_of_diagonalFreshLossProjectionSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L202)
- Lean declaration: [irrational_totientSeries_of_diagonalAdjacentSuffixGapSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2882)
- Lean declaration: [irrational_totientSeries_of_canonicalAdjacentSuffixCentralSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2890)
- Lean declaration: [irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateExactSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2898)
- Lean declaration: [irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateMarginSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2907)
- Lean declaration: [irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateStrongBandSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2916)
- Lean declaration: [irrational_totientSeries_of_canonicalAdjacentSuffixJumpCentralSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2924)
- Lean declaration: [irrational_totientSeries_of_canonicalAdjacentSuffixJumpSlackSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2932)
- Lean declaration: [irrational_totientSeries_of_canonicalAdjacentSuffixPostJumpSlackSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2941)
- Lean declaration: [irrational_totientSeries_of_canonicalAdjacentSuffixPowerTwoPostJumpSlackSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2948)
- Lean declaration: [irrational_totientSeries_of_powerTwoOddGuardHalfWordBandSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L4242)
- Lean declaration: [irrational_totientSeries_of_actualPenultimateEnvelopeMarginSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L5020)
- Lean declaration: [irrational_totientSeries_of_actualPenultimateSignedMarginSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L5193)
- Lean declaration: [irrational_totientSeries_of_powerTwoOddGuardThreeRankBandSupply](../../Erdos249257/DiagonalFlexibleOddWindowSupply.lean#L137)
- Lean declaration: [irrational_totientSeries_of_threeScaleAffineEscapeSupply](../../Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L366)

- outgoing **depends_on_open**: [Z05::exact_full_target_pincer](BROWSER_Z05_1.md#node-faace0186be92bf5). Its weakest antecedent is, by the pincer, literally cofinal non-integrality of the actual diagonal, which is unproved.
- outgoing **depends_on_open**: [Z05::centrality_supply_ladder_equivalences](BROWSER_Z05_1.md#node-e1fc2dd9e38f6da4). Every rung of the ladder is an unproved proposition; the closures consume them as hypotheses.
- outgoing **equivalent_to**: [Z06::reduction_lcm_diagonal_supply](BROWSER_Z06_1.md#node-9bc987ebd91ed7a5). diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget unfolds FullTargetAvoidanceSupply into cofinal non-integrality of the lcm diagonal, which is verbatim the hypothesis of irrational_totient_series_of_lcm_diagonal_nonintegrality_supply.
- outgoing **alias_of**: [Z06::reduction_lcm_diagonal_supply](BROWSER_Z06_1.md#node-9bc987ebd91ed7a5). `diagonal_int_iff_foreignDiagonalDefect_hits_fullTarget` (DiagonalPincerDecomposition.lean:215) proves ForeignDiagonalDefectHitsFullTarget t is literally integrality of diagonalTailDifference t, so Z05's weakest socket FullTargetAvoidanceSupply is verbatim the cofinal diagonal non-integrality hypothesis of `irrational_totient_series_of_lcm_diagonal_nonintegrality_supply`; the eighteen-theorem family re-dresses that pre-existing supply rather than weakening it.

<a id="node-7cc8cb692e7c3423"></a>
## t_seven_finite_full_target_miss

At the single LCM height t = 7 the foreign diagonal defect provably misses the full reduced target. Three independent finite routes establish it: the imported non-integrality certificate, the depth-13 two-vertex projection certificate, and the cut J=1 / length m=12 sliding-suffix certificate.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [foreignDiagonalDefect_misses_fullTarget_seven](../../Erdos249257/DiagonalPincerDecomposition.lean#L275)
- Lean declaration: [foreignDiagonalDefect_misses_fullTarget_seven_via_projection](../../Erdos249257/DiagonalFreshLossBridge.lean#L2971)
- Lean declaration: [foreignDiagonalDefect_misses_fullTarget_seven_via_suffix](../../Erdos249257/DiagonalFreshLossBridge.lean#L2988)
- Lean declaration: [diagonalFreshLossProjectionCell_seven](../../Erdos249257/DiagonalFreshLossBridge.lean#L2959)
- Lean declaration: [diagonalFreshLossResidueCell_seven](../../Erdos249257/DiagonalFreshLossBridge.lean#L2965)
- Lean declaration: [diagonalSuffixCell_seven](../../Erdos249257/DiagonalFreshLossBridge.lean#L2980)

- outgoing **finite_instance_of**: [Z05::exact_full_target_pincer](BROWSER_Z05_1.md#node-faace0186be92bf5). It is the pincer's miss side verified at the single height t = 7.
- outgoing **finite_instance_of**: [Z05::two_vertex_certificate_forces_full_target_miss](BROWSER_Z05_2.md#node-54adf16238fe95fb). The depth-13 projection cell and the J=1/m=12 suffix cell instantiate the certificate consumers.
- outgoing **reformulates**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). By diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget, foreignDiagonalDefect_misses_fullTarget_seven is non-integrality of R_{2H_7}-R_{H_7}, which is totient_tail_period_lcm_diagonal_not_int_at_seven_and_eight.
- outgoing **finite_instance_of**: [Z01::erdos249_cone_supply_restatement](BROWSER_Z01_1.md#node-4007efd56b0e194f). by exact_full_target_pincer a full-target miss at height t is exactly non-integrality of the LCM-diagonal tail difference at t, which is this node's second supply clause ('diagonal non-integrality supply'); the t=7 miss is that clause at one scale.
- outgoing **finite_instance_of**: [Z06::reduction_cone_nonflat_menu_supply](BROWSER_Z06_1.md#node-83d97029da15536b). one of the three routes is the depth-13 two-vertex projection certificate, and two_vertex_certificate_forces_full_target_miss identifies the [1,2] menu with the generic cone non-flatness certificate; so this is a firing coneNonflatCert (periodLcm 7) 13 [1,2] cell of the menu supply.
- outgoing **specialises**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). `foreignDiagonalDefect_misses_fullTarget_seven` (DiagonalPincerDecomposition.lean:275) is proved as `tail_diff_not_int_periodLcm_diagonal_seven_eight.1` transported through the definitional pincer iff `diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget` (:215); it is the t = 7 cell of Z01's `totient_tail_period_lcm_diagonal_not_int_at_seven_and_eight`.

<a id="node-09a688c7b68b7c4b"></a>
## tail_limit_supplies_controlled_projection

If the finite foreign residue windows converge to the omitted part of the actual foreign defect, then the uniform finite-window estimate passes to the limit and the projection is controlled; hence exact projected separation gives a full-target miss. The convergence hypothesis is the whole unproved analytic content.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["htail : ForeignResidueTailLimit H D, i.e. Tendsto (fun L => foreignTailWindow H D L) atTop (nhds (scaleForeignDefect H - projectedForeignDefect H D))"]

- Lean declaration: [controlledForeignProjection_of_tail_limit](../../Erdos249257/LambertDiagonalEnclosure.lean#L31)
- Lean declaration: [scaleFullTarget_miss_of_tail_limit](../../Erdos249257/LambertDiagonalEnclosure.lean#L46)
- Lean declaration: [scaleFullTarget_miss_of_tail_limit_of_forall_int](../../Erdos249257/LambertDiagonalEnclosure.lean#L55)

- outgoing **implies**: [Z05::controlled_projection_miss_is_conditional](BROWSER_Z05_1.md#node-9f3918d03e2e3d48). The tail-limit hypothesis discharges ControlledForeignProjection and hence feeds the miss consumer.

<a id="node-a899ca2488ea67cb"></a>
## three_rank_window_core_no_go

Quantitative core version of the same obstruction: in a three-rank window with corrections below e (resp. below 2e), every state with 2|s| < e (resp. 8|s| < 3e) is forced to occupy all three edge tubes. Any no-three-edge theorem obtained in this window must therefore separately exclude that central core; relaxing the old radius-e obstruction to the flexible three-rank producer does not turn the problem into a correction-only argument.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Bounds only the radius-e/2 and radius-3e/8 cores under the stated correction envelopes, and only for the three inspected ranks. It does not rule out excluding that core by arithmetic means, does not apply once the corrections are known more precisely than by magnitude, and says nothing about windows of four or more ranks or about states outside the core, for which the three-rank producer may well fire. Additionally: both theorems are stated for universally quantified integers e, s, C, F and are never instantiated at the actual power-of-two state; no theorem in this zone shows that the actual centred state ever lies in the radius-e/2 or radius-3e/8 core, so this node constrains a proof strategy, not the objects. It also does not close the equivalent ThreeScaleAffineEscapeSupply engine (see power_two_supply_ladder_equivalences), which remains open in exactly the same way as the three-rank band it is equivalent to.

- Lean declaration: [threeEdgeWindow_forced_of_halfEdgeCore](../../Erdos249257/DiagonalFlexibleOddWindowSupply.lean#L226)
- Lean declaration: [threeEdgeWindow_forced_of_threeEighthCore](../../Erdos249257/DiagonalFlexibleOddWindowSupply.lean#L259)

- outgoing **specialises**: [Z05::envelope_only_no_go](BROWSER_Z05_1.md#node-a158017228125ba8). Same obstruction made quantitative for the three-rank window actually used by the flexible producer.
- outgoing **barrier_for**: [Z05::power_two_supply_ladder_equivalences](BROWSER_Z05_1.md#node-cb014211c50cacf6). It fixes the exact central core that any no-three-consecutive-edge theorem must exclude by other means.

<a id="node-54adf16238fe95fb"></a>
## two_vertex_certificate_forces_full_target_miss

On the two-vertex menu [1,2] the generic cone non-flatness certificate at depth L is exactly the asymmetric safe-interval test H_t + L + 2 < residue < 2^L - (2H_t + L + 2) on the signed binary window residue, and either form alone already implies that the foreign defect misses the full reduced target at that height.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [diagonalFreshLossResidueCert_iff_projectionCert](../../Erdos249257/DiagonalFreshLossBridge.lean#L72)
- Lean declaration: [foreignDiagonalDefect_misses_fullTarget_of_projectionCert](../../Erdos249257/DiagonalFreshLossBridge.lean#L149)
- Lean declaration: [foreignDiagonalDefect_misses_fullTarget_of_residueCert](../../Erdos249257/DiagonalFreshLossBridge.lean#L184)

- incoming **finite_instance_of**: [Z05::t_seven_finite_full_target_miss](BROWSER_Z05_2.md#node-7cc8cb692e7c3423). The depth-13 projection cell and the J=1/m=12 suffix cell instantiate the certificate consumers.
- incoming **implies**: [Z05::sliding_suffix_transference](BROWSER_Z05_2.md#node-5bf8a0edc6b1c78f). Centrality of the last m bits alone yields the full-depth residue certificate consumed by the pincer.

