# Z12_1: Mersenne achievement set: greedy geometry, fat-Cantor structure, and the 1/2 membership question

[All problems and zones](BROWSER.md)

<a id="node-f2341acfc3d000a7"></a>
## campbell_agp_parameter_barrier

Campbell's use of the Alford-Granville-Pomerance estimate fixes exponent 1/4, so at prime-search height P the progression modulus d must satisfy d^4 <= P. In the proposed last-skip synchronization the requirements 2 <= d, t <= d, P <= 4t and d^4 <= P are jointly inconsistent, and so is the phase-freeze variant with window inequality P*q0^2 <= 2M+2 and M <= t*q0^2. Hence that synchronization cannot be made to work at those parameters.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rules out only the specific parameter conjunction arising from the delta = 1/4 choice: 2 <= d, t <= d, P <= 4t, d^4 <= P (and its phase-freeze variant). It does not rule out a Campbell-style prime-progression input with a different exponent, a different window-to-period relation, a larger admissible modulus, or any other route to infinitely many greedy skips; and it does not touch the half-membership question itself.

- Lean declaration: [campbellQuarterExponent_periodFreeze_noSync](../../Erdos249257/CampbellShiftSynchronization.lean#L299)
- Lean declaration: [campbellPhaseFreeze_parameters_impossible](../../Erdos249257/CampbellShiftSynchronization.lean#L320)

- outgoing **barrier_for**: [Z12::shift_window_zero_endpoint_restatement](BROWSER_Z12_2.md#node-592c2020744fdf2f). the barrier removes the AGP parameter route that was meant to supply the shifted-window interface, and the restatement shows the interface would have been vacuous anyway

<a id="node-809811770b153c81"></a>
## canonical_even_seam_supply_route

If at every sufficiently large even depth the actual reachability set is described by a canonical scalar seam, and every such seam's hole escapes the strip, then full strip reachability holds at those even depths, cofinal admissibility follows, and hence an infinite set with Mersenne sum 1/2 exists. Adding an odd-level reachability hypothesis and a depth-20 admissible base word gives the same conclusion. Neither the seam-supply nor the seam-escape hypothesis is proved.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hcanonical : HalfCarryCanonicalEvenSeamSupply, i.e. forall d >= 10, exists delta c, IsCanonicalEvenSeam d delta c", "hescape : HalfCarryEvenSeamEscape, i.e. forall d >= 10 and every canonical seam, 2*delta - c < 1 or halfStripBound (2d) < 2*delta - c", "hodd : forall d >= 10, HalfCarryFullStripReachabilityAt (2d+1)", "hbase : exists a : HalfWord 20, HalfStripAdmissible 20 a"]

- Lean declaration: [fullStripAt_even_of_canonicalSeam_escape](../../Erdos249257/HalfCarryReachability.lean#L361)
- Lean declaration: [fullStripAt_even_of_evenSeamSupply_escape](../../Erdos249257/HalfCarryReachability.lean#L376)
- Lean declaration: [cofinalAdmissibility_of_canonicalEvenSeamSupply](../../Erdos249257/HalfCarryReachability.lean#L1028)
- Lean declaration: [exists_infinite_support_half_of_canonicalEvenSeamSupply](../../Erdos249257/HalfCarryReachability.lean#L1056)
- Lean declaration: [exists_infinite_support_half_of_evenSeamSupply_escape](../../Erdos249257/HalfCarryReachability.lean#L1067)

- incoming **implies**: [Z12::even_seam_one_hole_theorem](BROWSER_Z12_1.md#node-faa46a4f5d916b2a). a hole outside the strip restores full terminal reachability at that even depth
- incoming **implies**: [Z12::even_seam_numerator_two_sheets](BROWSER_Z12_1.md#node-ea4fb74ad57193fc). the two-sheet description is the numerator-level form of the recylindrification used by the route
- outgoing **implies**: [Z12::cofinal_admissibility_yields_257_counterexample](BROWSER_Z12_1.md#node-25b0e23ee881e72f). the seam route discharges cofinal admissibility and then reuses its conclusion
- outgoing **depends_on_open**: [Z15::history_alternative_needs_canonical_seam_bridge](BROWSER_Z15_1.md#node-38ee19ceeb12b902). the only route in the corpus toward an ACTUAL canonical one-hole even seam; it delivers one only after assuming the seam bridge from a scalar seam pair, itself unproved, so the canonical-seam supply has no unconditional producer.

<a id="node-0c46f6d52d1ee5b9"></a>
## certified_greedy_death_soundness

If at some level the greedy residual strictly exceeds the remaining tail then the point is not in the achievement set; and a purely rational certificate, comparing an exact rational upper enclosure of the tail with the exact rational residual, soundly implies the same nonmembership. The certificate is one-sided: failing to find one, or surviving to any finite depth, proves nothing about membership.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [greedyMersenneDeath_not_mem](../../Erdos249257/GreedyAchievementSet.lean#L1747)
- Lean declaration: [certifiedGreedyMersenneDeath_not_mem](../../Erdos249257/GreedyAchievementSet.lean#L1762)

- outgoing **implies**: [Z12::three_fourths_excluded](BROWSER_Z12_3.md#node-df685f4f83c123aa). 3/4 is excluded by a level-one instance of the certificate
- incoming **implies**: [Z12::greedy_rational_exactness](BROWSER_Z12_1.md#node-a57ea44d67021816). the rational/real agreement is what makes the exact rational certificate sound

<a id="node-3b04a5f99d781f94"></a>
## channel_cap_skip_transport

If at every rank the greedy run started at 1/2 has residual at most the two-channel cap 2^-(n+1) + (1/3)4^-(n+1) whenever it skips that rank, then 1/2 belongs to the Mersenne achievement set; the same holds with the smaller dyadic cap 2^-(n+1). Neither skip-branch cap hypothesis is proved anywhere.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hskip : forall n, not (mersenneWeight (n+1) <= greedyMersenneRemainder (1/2) n) -> greedyMersenneRemainder (1/2) n <= halfTwoChannelCap (n+1)", "hskip : forall n, not (mersenneWeight (n+1) <= greedyMersenneRemainder (1/2) n) -> greedyMersenneRemainder (1/2) n <= halfDyadicCap (n+1)"]

- Lean declaration: [half_mem_mersenneAchievementSet_of_skipped_twoChannelCap](../../Erdos249257/GreedyAchievementSet.lean#L1425)
- Lean declaration: [half_mem_mersenneAchievementSet_of_skipped_dyadicCap](../../Erdos249257/GreedyAchievementSet.lean#L1444)

- outgoing **generalises**: [Z12::second_channel_phase_separation](BROWSER_Z12_2.md#node-84f746a828ad3d71). the second-channel separation socket is the rescaled and sharpened form of the two-channel cap socket
- incoming **implies**: [Z12::forced_return_threshold_calculus](BROWSER_Z12_1.md#node-45e85b8742cbb440). the forced-return threshold is what shows a residual under the two-channel cap must return under the dyadic cap within about m/2 blocks
- incoming **reformulates**: [Z10::greedy_decisions_are_sign_conditions_on_excess_numerator](BROWSER_Z10_1.md#node-a94679449d4350eb). greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos and greedyHalfRemainder_le_twoChannelCap_iff_excess are exactly the two skip-branch cap hypotheses of half_mem_mersenneAchievementSet_of_skipped_dyadicCap / _twoChannelCap, restated as sign conditions on one integer excess numerator.
- incoming **transport_of**: [Z10::half_membership_from_skipped_excess_bound](BROWSER_Z10_2.md#node-24557a20c8c5dc51). HalfGreedySkippedExcessBound is the integer excess-numerator form of the analytic two-channel cap hypothesis of half_mem_mersenneAchievementSet_of_skipped_twoChannelCap, via greedyHalfRemainder_le_twoChannelCap_iff_excess.
- incoming **transport_of**: [Z13::half_membership_from_frozen_margin_sockets](BROWSER_Z13_1.md#node-0b364ae5b3109540). half_mem_mersenneAchievementSet_of_governedFrozenMarginProducer routes the frozen-margin first passage into the same dyadic-cap consumer; greedyHalfFrozenMargin_nonneg_iff_window_covers is the integer coordinate of that cap inequality.
- outgoing **depends_on_open**: [Z10::unsafe_skip_forces_long_forced_take_block](BROWSER_Z10_2.md#node-c29d8d1929d4f3b7). the nearest law bearing on the skip-branch cap: it converts a cap-violating skip into a forced take run of 2n+4 ranks, but it consumes the cap violation rather than producing the cap, and forced_take_block_depth_is_sharp shows the extracted block cannot be lengthened; so no cap hypothesis is produced.
- incoming **specialises**: [Z10::half_membership_from_actual_block_safety](BROWSER_Z10_2.md#node-6cf216bc1ead238e). `greedyHalfRemainder_le_nextDyadic_of_BlockSafe` (DyadicPrefixCompression.lean:2759) turns block dyadic safety at a skipped rank into `greedyMersenneRemainder (1/2) n <= halfDyadicCap (n+1)`, which is verbatim the dyadic-cap branch hypothesis of Z12's node; both conclude 1/2 in mersenneAchievementSet.

<a id="node-25b0e23ee881e72f"></a>
## cofinal_admissibility_yields_257_counterexample

Much less than full-strip reachability suffices: if strip-admissible finite words merely exist at cofinally many levels, then there is an infinite set A whose Mersenne sum is exactly 1/2. The cofinal-existence hypothesis is not proved.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hcofinal : HalfCarryCofinalAdmissibility, i.e. forall N, exists M >= N and a : HalfWord M with HalfStripAdmissible M a"]

- Lean declaration: [exists_infinite_support_half_of_cofinalAdmissibility](../../Erdos249257/HalfCarryReachability.lean#L1013)

- incoming **implies**: [Z12::konig_prefix_closed_branch](BROWSER_Z12_2.md#node-d973a0832877504d). the compactness step is what turns cofinal finite words into an infinite branch
- outgoing **generalises**: [Z12::full_strip_reachability_yields_257_counterexample](BROWSER_Z12_1.md#node-aa3bcec65c302faf). cofinal existence of admissible words is a strictly weaker antecedent than full-strip reachability at every level
- incoming **implies**: [Z12::canonical_even_seam_supply_route](BROWSER_Z12_1.md#node-809811770b153c81). the seam route discharges cofinal admissibility and then reuses its conclusion
- incoming **generalises**: [Z12::terminal_only_cofinal_yields_half](BROWSER_Z12_2.md#node-f8810011b82ac702). terminal-only witnesses drop both coherence between depths and all earlier-row carry control
- incoming **transport_of**: [Z15::selected_window_cofinal_consumer](BROWSER_Z15_1.md#node-c8d8cb0761e11f61). cofinalAdmissibility_of_selectedHalfWindows (HalfCarrySelectedWindow.lean) is a formal theorem converting a cofinal selected-window supply into HalfCarryCofinalAdmissibility, the antecedent of exists_infinite_support_half_of_cofinalAdmissibility.
- incoming **transport_of**: [Z15::cofinal_protected_seam_consumer](BROWSER_Z15_1.md#node-8914ed1068ade432). cofinalAdmissibility_of_cofinalProtectedEvenSeamRealization (HalfCarryProtectedSeamConsumer.lean) converts the cofinal localized one-hole seam supply into the same cofinal admissibility antecedent.
- incoming **finite_instance_of**: [Z15::depth18_selected_window_base](BROWSER_Z15_1.md#node-7dc33561132cdf17). the twelve certified representatives are strip-admissible finite words at depth 18, one level of the cofinal-admissibility hypothesis.
- incoming **finite_instance_of**: [Z15::depth26_two_carry_window_and_step](BROWSER_Z15_1.md#node-457242e6650bec54). the depth-26 and derived depth-27 tables give strip-admissible words at those two levels; note it is a window on carries 1 and 2 ONLY, so it instantiates cofinal admissibility but NOT full-strip reachability.
- outgoing **depends_on_open**: [Z16::certified_cylinder_run_to_depth_52](BROWSER_Z16_1.md#node-bf9e1a5ea4c4344d). admissible finite words are produced at every depth up to 52 by this run and nowhere beyond, so cofinal admissibility is unproduced.
- incoming **specialises**: [Z15::selected_window_cofinal_consumer](BROWSER_Z15_1.md#node-c8d8cb0761e11f61). `cofinalAdmissibility_of_selectedHalfWindows` (HalfCarrySelectedWindow.lean:831) derives `HalfCarryCofinalAdmissibility` from the cofinal-selected-window hypothesis; that predicate is exactly the antecedent of Z12's `exists_infinite_support_half_of_cofinalAdmissibility` (HalfCarryReachability.lean:984) and the conclusions coincide, so Z15's theorem is the hypothesis-strengthened form.
- incoming **specialises**: [Z15::cofinal_protected_seam_consumer](BROWSER_Z15_1.md#node-8914ed1068ade432). `cofinalAdmissibility_of_cofinalProtectedEvenSeamRealization` (HalfCarryProtectedSeamConsumer.lean:31) derives the same `HalfCarryCofinalAdmissibility` antecedent from the cofinal localized-seam hypothesis; identical conclusion.
- incoming **specialises**: [Z15::mixed_cofinal_window_or_seam_consumer](BROWSER_Z15_1.md#node-e5cf1d1a8c038506). `cofinalAdmissibility_of_cofinalSelectedWindowOrProtectedSeam` derives `HalfCarryCofinalAdmissibility` from the disjunctive cofinal producer; Z12's node is the weakest socket both branches factor through.

<a id="node-0019f92e625c9459"></a>
## cofinal_strip_return_yields_half

If the actual greedy half carry returns to the square-root strip beyond every index, then antitonicity forces the whole scaled carry to zero, the greedy support at 1/2 is infinite with Mersenne sum exactly 1/2, and 1/2 belongs to the achievement set. The cofinal return hypothesis is not proved.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hreturn : GreedyHalfCarryCofinalStripReturn, i.e. forall N, exists M >= N with integerHalfCarry (greedyMersenneSupport (1/2)) M <= halfStripBound (M+1)"]

- Lean declaration: [half_mem_mersenneAchievementSet_of_cofinalStripReturn](../../Erdos249257/CofinalStripReturn.lean#L157)
- Lean declaration: [greedy_half_infinite_of_cofinalStripReturn](../../Erdos249257/CofinalStripReturn.lean#L130)
- Lean declaration: [greedy_integerHalfCarry_scaled_tendsto_zero_of_cofinalStripReturn](../../Erdos249257/CofinalStripReturn.lean#L84)

- incoming **implies**: [Z12::scaled_uncentred_carry_antitone](BROWSER_Z12_2.md#node-11a8403d1942daa3). antitonicity is the fan-in that upgrades cofinal returns into a limit
- outgoing **generalises**: [Z12::tempered_mobius_carry_yields_half](BROWSER_Z12_2.md#node-c0baa14342623c9d). cofinal returns of the uncentred carry are weaker than an all-level square-root bound on the Mobius-centred carry

<a id="node-6547d3092f58f8f5"></a>
## correction_tail_one_bit_window

For every positive m the correction tail (the Mersenne tail minus its dyadic channel) is pinned strictly between 2^-(2m+2) and 2^-(2m+1), so the sharp uniform window depth is 2m+1, and the rank gap decomposes exactly as (w(n) - 2^-n) minus the correction tail at n.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [mersenneCorrectionTail_lt_doubleDepth](../../Erdos249257/HalfCutLocator.lean#L55)
- Lean declaration: [doubleDepth_succ_lt_mersenneCorrectionTail](../../Erdos249257/HalfCutLocator.lean#L80)
- Lean declaration: [mersenneGap_eq_weightCorrection_sub_correctionTail](../../Erdos249257/HalfCutLocator.lean#L95)

- incoming **implies**: [Z12::mersenne_gap_two_channel_asymptotic](BROWSER_Z12_2.md#node-aaaea584bbabda94). the (1/3)4^-n channel and the (1/7,2/7)8^-n remainder bracket are what pin the correction tail between 2^-(2m+2) and 2^-(2m+1)
- incoming **implies**: [Z12::dyadic_boundary_crossing_uniqueness](BROWSER_Z12_1.md#node-b18be132c08a8f68). the window width below one binary cell is what makes the dyadic crossing unique

<a id="node-1d996dcdd3abd2ed"></a>
## depth14_even_seam_nonreachable_instance

At the scalar parameters delta = 2, c = 1 the terminal carry 3 is not even-seam reachable, so the hole can genuinely fall inside the strip at small depth.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [depth14_evenSeam_three_not_reachable](../../Erdos249257/HalfCarryReachability.lean#L326)

- outgoing **finite_instance_of**: [Z12::even_seam_one_hole_theorem](BROWSER_Z12_1.md#node-faa46a4f5d916b2a). a concrete parameter choice where the hole lies inside the strip, which is why seam escape must be assumed

<a id="node-b18be132c08a8f68"></a>
## dyadic_boundary_crossing_uniqueness

An interval of length at most one contains at most one integer, so at most one dyadic rational of depth 2m+1 can lie inside a correction window of width the correction tail at m; combined with the exact cancellation of powers of two in dyadic boundaries this pins the crossing depth.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [integer_crossing_unique](../../Erdos249257/GreedyAchievementSet.lean#L3322)
- Lean declaration: [correctionWindow_dyadic_crossing_unique](../../Erdos249257/HalfCutLocator.lean#L104)
- Lean declaration: [dyadicBoundary_cancel_powTwo](../../Erdos249257/GreedyAchievementSet.lean#L3339)
- Lean declaration: [crossedBoundary_forceDepth_gt_iff](../../Erdos249257/GreedyAchievementSet.lean#L3354)

- outgoing **implies**: [Z12::correction_tail_one_bit_window](BROWSER_Z12_1.md#node-6547d3092f58f8f5). the window width below one binary cell is what makes the dyadic crossing unique

<a id="node-e28c693fde9f6a98"></a>
## erdos_borwein_constant_irrational

The Erdos-Borwein constant, the sum of 1/(2^n-1) over all positive n, is irrational; it is also the total tail mass T(0), and it splits as the greedy support value plus the skipped support value for any starting point.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [irrational_erdosBorweinMersenneConstant](../../Erdos249257/GreedyAchievementSet.lean#L2469)
- Lean declaration: [erdosBorweinMersenneConstant_eq_greedy_add_skipped](../../Erdos249257/GreedyAchievementSet.lean#L2476)
- Lean declaration: [erdosBorweinMersenneConstant_eq_prefix_add_tail](../../Erdos249257/GreedyAchievementSet.lean#L2614)

- outgoing **implies**: [Z12::finite_support_never_half](BROWSER_Z12_1.md#node-babddd6819ddf0d6). irrationality of the total tail kills the lazy boundary case prefix plus tail equals 1/2
- outgoing **implies**: [Z12::half_straddle_canonicality](BROWSER_Z12_1.md#node-489b8a26bf7b420c). the same irrationality kills the lazy endpoint of the half straddle step
- outgoing **equivalent_to**: [Z01::erdos_borwein_full_support_irrationality](BROWSER_Z01_1.md#node-79ab550ed10b5c4b). irrational_erdosBorweinMersenneConstant is the achievement-set-coordinate name of irrational_erdosSum_full_support / irrational_erdosSupportSeries_univ, tied by erdosSupportSeries_univ_eq_erdosSum_full_support and positiveMersenneSupportValue_eq_erdosSupportSeries.
- outgoing **specialises**: [Z01::erdos_borwein_full_support_irrationality](BROWSER_Z01_1.md#node-79ab550ed10b5c4b). `irrational_erdosBorweinMersenneConstant` (GreedyAchievementSet.lean:2433) is `irrational_erdosBorwein_series` (CertificateKernel.lean:8007), which is in turn `irrational_erdosSum_full_support 2`; Z01 states the same conclusion for every integer base b >= 2.

<a id="node-ea4fb74ad57193fc"></a>
## even_seam_numerator_two_sheets

With numerators tracked, even-seam reachability splits into exactly two sheets: below the hole the numerator is 2T - c - 1 - k, above it 2T - c - k. Hence when the hole lies below the strip the whole strip recylindrifies on the upper sheet, and when it lies above the strip the whole strip recylindrifies on the lower sheet.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [evenSeamNumeratorReachable_iff_twoSheets](../../Erdos249257/HalfCarryReachability.lean#L268)
- Lean declaration: [evenSeam_recylindrifies_of_hole_below_strip](../../Erdos249257/HalfCarryReachability.lean#L306)
- Lean declaration: [evenSeam_recylindrifies_of_hole_above_strip](../../Erdos249257/HalfCarryReachability.lean#L316)

- outgoing **implies**: [Z12::canonical_even_seam_supply_route](BROWSER_Z12_1.md#node-809811770b153c81). the two-sheet description is the numerator-level form of the recylindrification used by the route

<a id="node-faa46a4f5d916b2a"></a>
## even_seam_one_hole_theorem

Every integer has a unique fixed-coefficient parent, and under a half-divisor coefficient change at parent delta the reachable terminal carries are exactly all integers other than the single value 2*delta - c. Inside a bounded strip this becomes: k is reachable iff k lies in the strip and k is not 2*delta - c. Uniqueness of the parent persists when the parent is required to lie inside the previous strip.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [evenSeamReachable_iff](../../Erdos249257/HalfCarryReachability.lean#L235)
- Lean declaration: [evenSeamReachable_in_strip_iff](../../Erdos249257/HalfCarryReachability.lean#L332)
- Lean declaration: [fixedCoeffChild_existsUnique](../../Erdos249257/HalfCarryReachability.lean#L179)
- Lean declaration: [fixedCoeffChild_existsUnique_parent_in_pred_strip](../../Erdos249257/HalfCarryReachability.lean#L209)

- outgoing **implies**: [Z12::canonical_even_seam_supply_route](BROWSER_Z12_1.md#node-809811770b153c81). a hole outside the strip restores full terminal reachability at that even depth
- incoming **finite_instance_of**: [Z12::depth14_even_seam_nonreachable_instance](BROWSER_Z12_1.md#node-1d996dcdd3abd2ed). a concrete parameter choice where the hole lies inside the strip, which is why seam escape must be assumed
- incoming **reformulates**: [Z13::seam_hole_scalar_normal_forms](BROWSER_Z13_2.md#node-e36262c887b04903). evenSeam_fullIntegerStrip_iff_escape and fixedCoeffNumeratorReachable_iff_endpoint are the scalar normal forms of evenSeamReachable_iff / evenSeamReachable_in_strip_iff, with the same single hole 2*delta - c.
- incoming **transport_of**: [Z16::in_strip_two_sheet_split](BROWSER_Z16_1.md#node-31d4c25c3644fda8). InStripTwoSheetStage carries the scalar seam coordinates whose one-hole predicate is the complement of its hole (halfTerminalReachable_of_ne_hole, InStripTwoSheetStage.protectedEvenSeamRealizedAt): the object-level realisation of the scalar one-hole reachability theorem.

<a id="node-5736eac8e3dd6fae"></a>
## fatal_half_gap_dichotomy

Either 1/2 belongs to the Mersenne achievement set or some finite exponent word exhibits a fatal half gap, and these alternatives are exclusive: the existence of a fatal half gap is logically equivalent to 1/2 not belonging to the achievement set. Which branch holds is exactly the open question; the corpus decides neither.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["ExistsFatalHalfGap -- equivalently (1/2 : R) not in mersenneAchievementSet; neither branch is proved"]

- Lean declaration: [half_mem_mersenneAchievementSet_or_exists_fatal_gap](../../Erdos249257/HalfCutLocator.lean#L623)
- Lean declaration: [existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet](../../Erdos249257/HalfCutLocator.lean#L643)
- Lean declaration: [half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap](../../Erdos249257/HalfCutLocator.lean#L654)
- Lean declaration: [half_not_mem_mersenneAchievementSet_of_exists_fatal_gap](../../Erdos249257/HalfCutLocator.lean#L538)
- Lean declaration: [half_mem_mersenneAchievementSet_of_no_fatal_gap](../../Erdos249257/HalfCutLocator.lean#L600)

- incoming **equivalent_to**: [Z12::half_membership_iff_infinite_greedy_skips](BROWSER_Z12_1.md#node-f4d02068c1837778). fatal gap existence, finite skipped support and half nonmembership are the same statement in cut-locator and greedy coordinates
- incoming **equivalent_to**: [Z12::last_skip_iff_finite_skips](BROWSER_Z12_2.md#node-275fc9b423c4c20c). existence of a last greedy skip is proved equivalent to existence of a fatal half gap
- incoming **implies**: [Z12::half_straddle_canonicality](BROWSER_Z12_1.md#node-489b8a26bf7b420c). canonicality is what upgrades a branch-local gap into an exclusion of every support, giving the dichotomy
- incoming **implies**: [Z12::rank_gap_excludes_all_supports](BROWSER_Z12_2.md#node-fe0fcd0cf10b44ae). the global exclusion is the nonmembership direction of the dichotomy
- incoming **specialises**: [Z12::straddle_prefix_membership_criterion](BROWSER_Z12_2.md#node-ae588a53cf09b158). the general all-depth straddle criterion specialised to t = 1/2 gives the membership branch
- incoming **equivalent_to**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). seamGreedyEventuallyRight_iff_existsFatalHalfGap composed with existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet (HalfCutLocator.lean) makes the two nodes the same dichotomy in seam and cut-locator coordinates.

<a id="node-4f4d512124db1541"></a>
## fatal_level_forces_cofinite_takes

Once the greedy run at some level has residual strictly above the remaining tail, that condition persists and every later exponent is taken, so the skipped support is finite. Contrapositively, for any nonnegative x whose greedy run skips infinitely many exponents, x belongs to the achievement set.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [finite_greedyMersenneSkippedSupport_of_fatalAt](../../Erdos249257/GreedyAchievementSet.lean#L1513)
- Lean declaration: [mem_mersenneAchievementSet_of_greedySkippedSupport_infinite](../../Erdos249257/GreedyAchievementSet.lean#L1528)

- incoming **implies**: [Z12::greedy_survival_characterisation](BROWSER_Z12_1.md#node-2ea8d25af1d0144e). the fatal-level notion is the negation of the survival inequality at one level
- outgoing **specialises**: [Z12::half_membership_iff_infinite_greedy_skips](BROWSER_Z12_1.md#node-f4d02068c1837778). the general infinite-skip criterion at x = 1/2 gives one direction of the pivot equivalence

<a id="node-babddd6819ddf0d6"></a>
## finite_support_never_half

No finite normalized set of positive exponents has Mersenne support value 1/2, and no finite support value plus a full tail equals 1/2 either. Hence if 1/2 is in the achievement set the witnessing support is automatically infinite, and its existence would refute universal Erdos #257.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [positiveMersenneSupportValue_coe_finset_ne_half](../../Erdos249257/HalfCutLocator.lean#L243)
- Lean declaration: [half_ne_coe_finset_add_mersenneTail](../../Erdos249257/HalfCutLocator.lean#L263)
- Lean declaration: [finite_boolSupport_ne_half](../../Erdos249257/HalfCarryReachability.lean#L589)

- outgoing **implies**: [Z12::half_membership_iff_infinite_greedy_skips](BROWSER_Z12_1.md#node-f4d02068c1837778). excluding finite supports is what makes half membership automatically produce an infinite witness
- incoming **implies**: [Z12::erdos_borwein_constant_irrational](BROWSER_Z12_1.md#node-e28c693fde9f6a98). irrationality of the total tail kills the lazy boundary case prefix plus tail equals 1/2

<a id="node-45e85b8742cbb440"></a>
## forced_return_threshold_calculus

The forced-return threshold at (m, J) equals T(m) minus the correction tail at m+J; a residual r satisfies r minus the next J Mersenne weights at most 2^-(m+J) exactly when r is at most that threshold. The threshold is strictly increasing in J with limit T(m), so any residual strictly below T(m) forcibly returns under the dyadic cap after finitely many blocks, and any residual at most the two-channel cap returns after at most about m/2 blocks.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [mersenneForcedReturnThreshold_eq_tail_sub_correction](../../Erdos249257/GreedyAchievementSet.lean#L2091)
- Lean declaration: [forcedBlock_le_dyadic_iff_le_returnThreshold](../../Erdos249257/GreedyAchievementSet.lean#L2100)
- Lean declaration: [exists_forcedBlock_return_of_lt_tail](../../Erdos249257/GreedyAchievementSet.lean#L2147)
- Lean declaration: [exists_forcedBlock_return_of_le_twoChannelCap](../../Erdos249257/GreedyAchievementSet.lean#L2225)
- Lean declaration: [forcedBlock_return_of_le_twoChannelCap_ceilingHalf](../../Erdos249257/GreedyAchievementSet.lean#L2210)

- outgoing **implies**: [Z12::channel_cap_skip_transport](BROWSER_Z12_1.md#node-3b04a5f99d781f94). the forced-return threshold is what shows a residual under the two-channel cap must return under the dyadic cap within about m/2 blocks

<a id="node-aa3bcec65c302faf"></a>
## full_strip_reachability_yields_257_counterexample

If every terminal carry in the square-root strip is reachable by some strip-admissible finite word at every level (or at every level beyond some base level with an admissible base word), then there is an infinite set A with the sum of 1/(2^a-1) over A equal to 1/2. The full-strip reachability hypothesis is not proved at any level beyond finite search.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hfull : forall N, 1 <= N -> HalfCarryFullStripReachabilityAt N", "hfull : forall N, N0 <= N -> HalfCarryFullStripReachabilityAt N, together with hbase : exists a : HalfWord N0, HalfStripAdmissible N0 a"]

- Lean declaration: [exists_infinite_support_half_of_fullStrip](../../Erdos249257/HalfCarryReachability.lean#L979)
- Lean declaration: [exists_infinite_support_half_of_eventualFullStrip](../../Erdos249257/HalfCarryReachability.lean#L992)

- incoming **implies**: [Z12::strip_admissible_branch_forces_half](BROWSER_Z12_2.md#node-0e98feddc11597cf). the branch theorem is the unconditional core; the full-strip hypothesis only supplies the branch
- incoming **generalises**: [Z12::cofinal_admissibility_yields_257_counterexample](BROWSER_Z12_1.md#node-25b0e23ee881e72f). cofinal existence of admissible words is a strictly weaker antecedent than full-strip reachability at every level
- incoming **finite_instance_of**: [Z15::depth18_selected_window_base](BROWSER_Z15_1.md#node-7dc33561132cdf17). the depth-18 kernel-reflected table realises every terminal carry up to halfStripBound 18 = 12, i.e. HalfCarryFullStripReachabilityAt 18 - the predicate this conditional needs at every level, supplied here at exactly one level.
- incoming **finite_instance_of**: [Z16::pre_feedback_run_to_depth_27](BROWSER_Z16_1.md#node-ca287b00ab093584). the run produces a full protected selected window on the whole square-root strip at every depth 18..27, i.e. HalfCarryFullStripReachabilityAt N for ten consecutive N and no more.
- incoming **finite_instance_of**: [Z16::first_feedback_promotion_depth_27_to_29](BROWSER_Z16_1.md#node-dc4415c505244611). admissible words exist for every terminal carry of the strip at depths 28 and 29, i.e. full-strip reachability at two further levels.
- outgoing **depends_on_open**: [Z16::certified_cylinder_run_to_depth_52](BROWSER_Z16_1.md#node-bf9e1a5ea4c4344d). the certified run is the deepest producer of full-strip reachability, reaching depth 52; beyond that the continuation is gated on the unproved NextArithmetic cell of the profiled gap step, so reachability at every level is not produced.

<a id="node-8167d9ef9c6a66a9"></a>
## greedy_mobius_carry_nonneg

For the actual greedy run at 1/2 the Mobius-centred half carry is nonnegative at every level. This is the lower half of the square-root strip, proved unconditionally for the real orbit; only the upper bound remains open.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [greedy_mobiusCenteredHalfCarry_nonneg](../../Erdos249257/HalfCarryReachability.lean#L919)

- outgoing **implies**: [Z12::tempered_mobius_carry_yields_half](BROWSER_Z12_2.md#node-c0baa14342623c9d). nonnegativity supplies the lower half of the square-root strip hypothesis for the actual greedy orbit, leaving only the upper bound open
- incoming **depends_on_open**: [Z13::finite_window_reduction_of_raw_half_residual](BROWSER_Z13_1.md#node-01e83e38a5f70b05). the only unconditional control on the actual greedy Moebius-centred carry; it supplies the LOWER half of the strip, while the hypothesis needs the upper bound (carry below the finite coefficient window), which that node explicitly records as open.

<a id="node-a57ea44d67021816"></a>
## greedy_rational_exactness

For rational inputs the exact rational greedy recursion takes a term at rank n+1 exactly when the real greedy recursion does, the rational prefix is the audited finite Erdos sum of the selected exponents, and for a rational value already known to be in the achievement set the membership bits of its support are computed by the rational greedy test. So the digits of a rational achievement point are decidable at every finite depth.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [rational_greedy_take_iff_real](../../Erdos249257/GreedyAchievementSet.lean#L1849)
- Lean declaration: [rational_member_support_bit_iff](../../Erdos249257/GreedyAchievementSet.lean#L1868)
- Lean declaration: [greedyMersenneRemainderRat_eq_sub_finiteErdosSum](../../Erdos249257/GreedyAchievementSet.lean#L1839)

- outgoing **implies**: [Z12::certified_greedy_death_soundness](BROWSER_Z12_1.md#node-0c46f6d52d1ee5b9). the rational/real agreement is what makes the exact rational certificate sound
- incoming **reformulates**: [Z10::greedy_take_predicate_equals_block_take_predicate](BROWSER_Z10_1.md#node-e3ae02f4c5975be1). greedyHalf_take_iff_BlockTakeAt (DyadicPrefixCompression.lean) and rational_greedy_take_iff_real (GreedyAchievementSet.lean) both identify the analytic greedy take test at a rank with an exact arithmetic test on the displayed numerator and prefix denominator.
- incoming **reformulates**: [Z13::real_to_rational_greedy_prefix_bridge](BROWSER_Z13_1.md#node-dadf7a74f8a35d6f). primitivePrefix_greedyMersenneSupport_eq_prefixRat is the set-level form of rational_greedy_take_iff_real: the real greedy prefix support at depth n is the finite rational greedy prefix.

<a id="node-2ea8d25af1d0144e"></a>
## greedy_survival_characterisation

A real x lies in the Mersenne achievement set if and only if x is nonnegative and the greedy residual after every finite number of steps is at most the remaining tail. Moreover the greedy run applied to the value of a normalized support recovers exactly that support, and the greedy residual at level n equals the suffix value of the support.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [mem_mersenneAchievementSet_iff_greedy_survival](../../Erdos249257/GreedyAchievementSet.lean#L1458)
- Lean declaration: [greedySupport_supportValue_eq](../../Erdos249257/GreedyAchievementSet.lean#L1361)
- Lean declaration: [greedyMersenneRemainder_supportValue](../../Erdos249257/GreedyAchievementSet.lean#L1315)

- outgoing **implies**: [Z12::fatal_level_forces_cofinite_takes](BROWSER_Z12_1.md#node-4f4d512124db1541). the fatal-level notion is the negation of the survival inequality at one level

<a id="node-2c0deef7cb552dc1"></a>
## half_greedy_self_trapping_interval_criterion

For the greedy run at 1/2 the correction interval at depth n is contained in the complementary dyadic cell exactly when the residual lies between the correction tail and 2^-n, and that two-sided condition is exactly the bound |signed balance| <= 2^-n minus the correction tail.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [halfGreedyCorrectionInterval_subset_complementInterval_iff](../../Erdos249257/GreedyAchievementSet.lean#L2299)
- Lean declaration: [halfGreedy_selfTrapping_iff_abs_signedBalance_le](../../Erdos249257/GreedyAchievementSet.lean#L2353)

- outgoing **reformulates**: [Z12::signed_balance_step_survival_criterion](BROWSER_Z12_2.md#node-5e46605191fd558e). interval containment at depth n is rewritten as a two-sided bound on the signed balance

<a id="node-8e23f659f64726ae"></a>
## half_greedy_shadow_reformulation

The greedy shadow at depth n minus the Erdos-Borwein constant equals the signed balance, so one-step survival at 1/2 is equivalent to the rank gap being at most the distance from the shadow to that constant; moreover any competing prefix separated from the greedy prefix by more than the tail is strictly further from the constant.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [halfGreedyMersenneShadow_sub_constant_eq_signedBalance](../../Erdos249257/GreedyAchievementSet.lean#L2622)
- Lean declaration: [halfGreedy_next_survives_iff_shadow_separated](../../Erdos249257/GreedyAchievementSet.lean#L2686)
- Lean declaration: [halfGreedyShadow_closer_of_prefix_separation](../../Erdos249257/GreedyAchievementSet.lean#L2637)

- incoming **reformulates**: [Z12::signed_balance_step_survival_criterion](BROWSER_Z12_2.md#node-5e46605191fd558e). the shadow minus the Erdos-Borwein constant is definitionally the signed balance

<a id="node-f4d02068c1837778"></a>
## half_membership_iff_infinite_greedy_skips

The value 1/2 belongs to the Mersenne achievement set if and only if the canonical greedy run started at 1/2 skips infinitely many exponents. Both sides of this equivalence are open: nothing in the corpus decides either.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["(greedyMersenneSkippedSupport (1 / 2 : R)).Infinite -- equivalently (1 / 2 : R) in mersenneAchievementSet; neither is proved anywhere in the corpus"]

- Lean declaration: [half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite](../../Erdos249257/GreedyAchievementSet.lean#L2583)
- Lean declaration: [infinite_greedyMersenneSkippedSupport_of_half_mem](../../Erdos249257/GreedyAchievementSet.lean#L2547)

- incoming **specialises**: [Z12::fatal_level_forces_cofinite_takes](BROWSER_Z12_1.md#node-4f4d512124db1541). the general infinite-skip criterion at x = 1/2 gives one direction of the pivot equivalence
- incoming **implies**: [Z12::finite_support_never_half](BROWSER_Z12_1.md#node-babddd6819ddf0d6). excluding finite supports is what makes half membership automatically produce an infinite witness
- outgoing **equivalent_to**: [Z12::fatal_half_gap_dichotomy](BROWSER_Z12_1.md#node-5736eac8e3dd6fae). fatal gap existence, finite skipped support and half nonmembership are the same statement in cut-locator and greedy coordinates
- outgoing **equivalent_to**: [Z12::half_membership_seam_equivalence_ring](BROWSER_Z12_1.md#node-c98bead16d978fce). the seam classification ring closes back onto infinitude of the greedy skipped support
- incoming **alias_of**: [Z12::shift_window_zero_endpoint_restatement](BROWSER_Z12_2.md#node-592c2020744fdf2f). GreedyShiftWindowZero is proved equivalent to half membership, so it is the endpoint under another name
- incoming **finite_instance_of**: [Z12::half_orbit_exact_rational_fixtures](BROWSER_Z12_1.md#node-370f9ffbb079ae6b). exponent 4 is a verified skip, so the skipped support is nonempty; nothing shows it infinite
- incoming **equivalent_to**: [Z10::half_value_iff_canonical_affine_carry_tempered](BROWSER_Z10_2.md#node-6b727b8f4e070ab3). mem_mersenneAchievementSet_iff_greedy_survival and greedySupport_supportValue_eq make membership of 1/2 the existence of a normalised support with value 1/2, which is the left side of support_half_iff_affineBinaryOrbit_tempered.
- incoming **equivalent_to**: [Z13::half_membership_iff_every_skip_survives](BROWSER_Z13_1.md#node-31f5cf394cc9250d). half_mem_iff_every_actual_skip_survives (HalfCylinderFixedTailSocket.lean) and half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite (GreedyAchievementSet.lean) are two iffs with the same left side, linked by isLastHalfGreedySkip_iff_skip_and_fatal.
- incoming **depends_on_open**: [Z10::half_value_forces_residual_reciprocal_mass_bound](BROWSER_Z10_2.md#node-2240732fc236082d). the hypothesis is that some support has value exactly 1/2; this equivalence pins that to infinitude of the greedy skipped support at 1/2 and states that neither side is decided anywhere, so the antecedent has no producer.
- incoming **alias_of**: [Z13::half_membership_iff_every_skip_survives](BROWSER_Z13_1.md#node-31f5cf394cc9250d). Z13's `no_lastHalfGreedySkip_iff_every_skip_survives` plus `half_mem_iff_every_actual_skip_survives` and Z12's `half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite` characterise the same membership through the same greedy orbit; Z12's `half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip` supplies the identification of the two coordinates.

<a id="node-c98bead16d978fce"></a>
## half_membership_seam_equivalence_ring

Membership of 1/2 in the Mersenne achievement set is equivalent to each of: the integer seam not being eventually right-extending; false successor terminal bits occurring beyond every bound; such bits occurring along one cofinal sequence; some cofinal seam sequence with skipped ranks tending to infinity; infinitude of the skipped support of the real greedy half orbit; and the nonexistence of a last greedy skip. All of these are the same open statement in different coordinates.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["SeamGreedyUnboundedTerminalFalse -- equivalently (1/2 : R) in mersenneAchievementSet; no positive producer for any member of the ring is proved"]

- Lean declaration: [half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse](../../Erdos249257/HalfCylinderHalfMembershipClassification.lean#L126)
- Lean declaration: [half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse](../../Erdos249257/HalfCylinderHalfMembershipClassification.lean#L203)
- Lean declaration: [half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong](../../Erdos249257/HalfCylinderHalfMembershipClassification.lean#L213)
- Lean declaration: [unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite](../../Erdos249257/HalfCylinderHalfMembershipClassification.lean#L228)
- Lean declaration: [half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip](../../Erdos249257/HalfCylinderHalfMembershipClassification.lean#L235)
- Lean declaration: [half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight](../../Erdos249257/HalfCylinderHalfMembershipClassification.lean#L112)

- incoming **equivalent_to**: [Z12::half_membership_iff_infinite_greedy_skips](BROWSER_Z12_1.md#node-f4d02068c1837778). the seam classification ring closes back onto infinitude of the greedy skipped support
- incoming **implies**: [Z12::seam_terminal_false_local_classifier](BROWSER_Z12_2.md#node-7a48a1adceb60ab3). the row-local classifier is the arithmetic content that the unbounded quantifier is wrapped around
- incoming **equivalent_to**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). seamGreedyEventuallyRight_iff_half_not_mem (HalfCylinderFatalGapRightTail.lean) and half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight (HalfCylinderHalfMembershipClassification.lean) are complementary halves of one equivalence about the integer seam.
- incoming **equivalent_to**: [Z13::unbounded_skipped_ranks_give_half_membership](BROWSER_Z13_2.md#node-0c099e1977615cd1). Both nodes cite half_mem_mersenneAchievementSet_of_unboundedTerminalFalse and _of_cofinalTerminalFalse (HalfCylinderFalseBitSupply.lean); Z12 closes the ring with unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite, so the supplies are the same proposition.
- incoming **transport_of**: [Z14::half_membership_conditional_endpoints](BROWSER_Z14_1.md#node-c86b42e6bb40f03f). The six middle-producer / band sockets are converted to the endpoint by last-false-terminal extraction against half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight; every one of them lands on that single open proposition.
- incoming **depends_on_open**: [Z13::unbounded_skipped_ranks_give_half_membership](BROWSER_Z13_2.md#node-0c099e1977615cd1). the equivalence ring proves cofinal false terminal bits / unbounded skipped seam ranks equivalent to half-membership itself, so this node's antecedent is the open proposition in different coordinates and no weaker producer can exist.
- incoming **alias_of**: [Z13::fatal_gap_eventual_right_classification](BROWSER_Z13_1.md#node-84eab96a9c382e8c). Z13's `seamGreedyEventuallyRight_iff_half_not_mem` and Z12's `half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight` are the same equivalence up to negation; both rings pivot on (1/2 : R) in mersenneAchievementSet and both carry the last-skip and fatal-gap coordinates.

<a id="node-370f9ffbb079ae6b"></a>
## half_orbit_exact_rational_fixtures

Exact rational facts about the actual greedy orbit at 1/2 and its correction tail: 1/2 minus the Mersenne sum over {2,3,6,7} is 1/16002; over {2,3,6,7,14} it is 1/688086; the correction tail at 1 is at most 5/42 and 3/8 < 1/2 minus it; exponent 2 is taken and exponent 4 is skipped by the greedy run at 1/2.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [half_sub_four_term_prefix_eq](../../Erdos249257/HalfCutLocator.lean#L664)
- Lean declaration: [half_sub_five_term_prefix_eq](../../Erdos249257/GreedyAchievementSet.lean#L1886)
- Lean declaration: [mersenneCorrectionTail_one_le](../../Erdos249257/HalfCutLocator.lean#L670)
- Lean declaration: [three_eighths_lt_half_sub_mersenneCorrectionTail_one](../../Erdos249257/HalfCutLocator.lean#L679)
- Lean declaration: [two_mem_greedyMersenneSupport_half](../../Erdos249257/HalfCarryReachability.lean#L905)
- Lean declaration: [four_mem_greedyMersenneSkippedSupport_half](../../Erdos249257/CampbellShiftSynchronization.lean#L351)

- outgoing **finite_instance_of**: [Z12::half_membership_iff_infinite_greedy_skips](BROWSER_Z12_1.md#node-f4d02068c1837778). exponent 4 is a verified skip, so the skipped support is nonempty; nothing shows it infinite
- outgoing **finite_instance_of**: [Z10::finite_fragment_residual_transport](BROWSER_Z10_1.md#node-cc4b29d2ebadd1ad). the exact residuals 1/2 - sum over {2,3,6,7} = 1/16002 and over {2,3,6,7,14} = 1/688086 are two instances of subtracting the exact rational finite Mersenne sum of a fragment F from a value, with the odd reduced denominators the transport predicts.

<a id="node-87b879a2ecf55fd1"></a>
## half_prefix_forcing_chain_criterion

If a normalized support carries a prefix forcing chain -- correction and complement values trapped in a common family of dyadic cells whose depths tend to infinity -- then the two values coincide and 1/2 belongs to the Mersenne achievement set. No such chain is constructed anywhere in the corpus.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["chain : HalfPrefixForcingChain A -- existence of a normalized A whose correction and complement values are trapped in dyadic cells of unbounded depth"]

- Lean declaration: [HalfPrefixForcingChain.correction_eq_complement](../../Erdos249257/GreedyAchievementSet.lean#L3274)
- Lean declaration: [half_mem_mersenneAchievementSet_of_prefixForcingChain](../../Erdos249257/GreedyAchievementSet.lean#L3311)

- incoming **implies**: [Z12::half_value_correction_complement_equivalence](BROWSER_Z12_1.md#node-d85d3e5dd775a717). the forcing chain proves the correction and complement values equal, which is the criterion for value 1/2

<a id="node-489b8a26bf7b420c"></a>
## half_straddle_canonicality

For the target 1/2 both straddle boundary equalities are impossible, so every half straddle is strict; the rank step is the strict dichotomy 'refine or expose a fatal gap'; and any half-straddling finite word agrees with the actual greedy support at 1/2 on all ranks up to its depth. The cut-locator coordinate is therefore canonical, not branch-dependent.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [IsStraddlePrefix.half_strict](../../Erdos249257/HalfCutLocator.lean#L287)
- Lean declaration: [IsStraddlePrefix.half_step_forced](../../Erdos249257/HalfCutLocator.lean#L301)
- Lean declaration: [IsStraddlePrefix.half_agrees_greedy](../../Erdos249257/HalfCutLocator.lean#L442)

- incoming **implies**: [Z12::erdos_borwein_constant_irrational](BROWSER_Z12_1.md#node-e28c693fde9f6a98). the same irrationality kills the lazy endpoint of the half straddle step
- outgoing **implies**: [Z12::fatal_half_gap_dichotomy](BROWSER_Z12_1.md#node-5736eac8e3dd6fae). canonicality is what upgrades a branch-local gap into an exclusion of every support, giving the dichotomy

<a id="node-5a97937c528b1bfe"></a>
## half_strip_admissible_word_system

Finite Boolean half words, their supports, and strip admissibility (bits 0 and 1 false, and every prefix carry inside 1 <= K <= 2*sqrt(n)+4) form a prefix-closed system: admissibility is preserved by restriction to shorter words. Terminal reachability and full-strip reachability at a level are the derived search predicates.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [HalfStripAdmissible.restrict](../../Erdos249257/HalfCarryReachability.lean#L147)

- outgoing **implies**: [Z12::konig_prefix_closed_branch](BROWSER_Z12_2.md#node-d973a0832877504d). prefix closure of admissibility is the hypothesis Konig's lemma consumes
- incoming **reformulates**: [Z15::executable_word_carry_bridge](BROWSER_Z15_1.md#node-b7a7186174fa836e). wordCarry_eq_integerHalfCarry and wordCoeff_eq_supportCoeff_wordSupport (HalfCarrySelectedWindowBase.lean) identify the executable Boolean-word carry with the Set-based integerHalfCarry on which HalfStripAdmissible is defined.

<a id="node-d85d3e5dd775a717"></a>
## half_value_correction_complement_equivalence

A normalized support has Mersenne value exactly 1/2 if and only if its correction value (the Mersenne minus dyadic discrepancy over the support) equals its complement value (the dyadic mass of the complementary exponents beyond one). Both sides are open for any candidate support.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["halfCorrectionValue A = halfComplementValue A for some normalized A -- equivalent to positiveMersenneSupportValue A = 1/2, i.e. the open half-membership question"]

- Lean declaration: [positiveMersenneSupportValue_eq_half_iff_correction_eq_complement](../../Erdos249257/GreedyAchievementSet.lean#L3240)

- outgoing **implies**: [Z12::half_prefix_forcing_chain_criterion](BROWSER_Z12_1.md#node-87b879a2ecf55fd1). the forcing chain proves the correction and complement values equal, which is the criterion for value 1/2
- incoming **equivalent_to**: [Z10::half_value_iff_canonical_affine_carry_tempered](BROWSER_Z10_2.md#node-6b727b8f4e070ab3). support_half_iff_affineBinaryOrbit_tempered (BooleanMobiusCarry.lean:526) and positiveMersenneSupportValue_eq_half_iff_correction_eq_complement (GreedyAchievementSet.lean:2990) are two iff-characterisations of the same proposition 'value = 1/2', identified by positiveMersenneSupportValue_eq_erdosSupportSeries.

<a id="node-b2e6722a9197358a"></a>
## hereditary_strict_superincreasing_subseries

Strict superincreasingness of the Mersenne weights is hereditary: for any set J of future offsets and any positive n, the sum of the selected future weights is still strictly less than w(n). So every Mersenne subseries inherits the Cantor-type rigidity.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [selectedMersenneTail_lt_weight](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L30)

- outgoing **generalises**: [Z12::mersenne_strict_superincreasing_tail](BROWSER_Z12_2.md#node-807aad871f9d65e8). the same strict inequality with an arbitrary set of future offsets deleted
- outgoing **implies**: [Z12::supported_mersenne_digit_injectivity](BROWSER_Z12_2.md#node-f84d07ab3840f960). injectivity of the J-supported digit map is proved from the hereditary inequality

<a id="node-0bfb870feae2b431"></a>
## initial_half_straddle_instances

The empty word straddles the target 1/2 at depths 0 and 1, so the cut-locator search is nonvacuous at its base.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [initial_half_straddle_zero](../../Erdos249257/HalfCutLocator.lean#L561)
- Lean declaration: [initial_half_straddle](../../Erdos249257/HalfCutLocator.lean#L576)

- outgoing **finite_instance_of**: [Z12::straddle_prefix_membership_criterion](BROWSER_Z12_2.md#node-ae588a53cf09b158). the empty word is the base straddle at depths 0 and 1

<a id="node-59e84eab60406093"></a>
## integer_half_carry_calculus

The integer half carry K_N (K_0 = 1, K_{N+1} = 2K_N minus the support coefficient at N+2) satisfies the exact identity K_N = 2^(N+1)(1/2 minus the support series) plus the binary coefficient tail at N+1, and depends only on the support below level N+1, so it is unchanged by restricting or by inserting exponents at least two levels ahead.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [integerHalfCarry_eq_scaled_residual_add_tail](../../Erdos249257/HalfCarryReachability.lean#L871)
- Lean declaration: [integerHalfCarry_inter_Iic_eq_of_succ_le](../../Erdos249257/HalfCarryReachability.lean#L49)

- outgoing **implies**: [Z12::strip_admissible_branch_forces_half](BROWSER_Z12_2.md#node-0e98feddc11597cf). the scaled-residual identity is what converts a bounded carry into closeness of the support series to 1/2
- outgoing **implies**: [Z12::terminal_only_strip_error_bound](BROWSER_Z12_2.md#node-49a575b75a3059eb). the same identity, used at a single terminal row rather than along a branch
- incoming **reformulates**: [Z11::binary_tail_shift_identity](BROWSER_Z11_1.md#node-51b4e0f463db1e09). integerHalfCarry_eq_scaled_residual_add_tail writes the half carry as 2^(N+1)(1/2 - value) + binaryCoeffTail at N+1: the affine recentring at target 1/2 of the generic shift identity binaryCoeffTail_succ.
- incoming **reformulates**: [Z14::producer_carry_exact_half_criterion](BROWSER_Z14_1.md#node-abd85fefcd4526c8). producerCarry_residual_identity (HalfCylinderProducerCarrySocket.lean) and integerHalfCarry_eq_scaled_residual_add_tail (HalfCarryReachability.lean) are the same exact identity dist(value, 1/2) = (integer carry - coefficient tail)/2^depth at two depth normalisations (2d+2 vs N+1).
- incoming **reformulates**: [Z13::finite_shadow_square_root_strip](BROWSER_Z13_1.md#node-b672d53f73e0ea3c). halfStripAdmissible_residual_eq is the same discrepancy identity read on admissible finite words: terminal integer half carry minus the scaled future-multiple coefficient tail.
- incoming **specialises**: [Z14::producer_carry_exact_half_criterion](BROWSER_Z14_1.md#node-abd85fefcd4526c8). `producerCarry A d` (HalfCylinderProducerCarrySocket.lean:20) and `integerHalfCarry A` (HalfCarryReachability.lean:36) are the same `affineBinaryOrbit (fun n => supportCoeff A (n+1)) 1`, so `producerCarry_residual_identity` is `integerHalfCarry_eq_scaled_residual_add_tail` at N = 2d+1 under the extra hypothesis A subset Iic d.

