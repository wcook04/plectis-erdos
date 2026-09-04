# Z39_1: Dyadic prefix compression: primitive coordinates, block margins, and unsafe-skip barriers

[All problems and zones](BROWSER.md)

<a id="node-650d3cfda412e4f3"></a>
## actual_prefix_cancellation_gcd_scales_raw_and_primitive_coordinates

PROVED EXACT CANCELLATION LAW: the common-to-reduced scale of the actual finite half-greedy prefix is precisely its numerator-denominator gcd. This same positive gcd multiplies both the raw residual numerator and the raw next-dyadic excess, so all sign and strict cap comparisons survive reduction; at a taken rank the new residual numerator satisfies a division-free recurrence with the exact take-step gcd.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Cancellation invariance makes the finite tests honest; it supplies no inequality forcing all actual skipped ranks to be safe.

- Lean declaration: [halfGreedyPrefixReductionFactor_eq_gcd](../../Erdos249257/DyadicPrefixCompression.lean#L1928)
- Lean declaration: [halfGreedyRawResidualNumerator_eq_gcd_mul_displayed](../../Erdos249257/DyadicPrefixCompression.lean#L2046)
- Lean declaration: [halfGreedyRawNextDyadicExcessNumerator_eq_gcd_mul_reduced](../../Erdos249257/DyadicPrefixCompression.lean#L2057)
- Lean declaration: [reducedTakeStep_residualNumerator](../../Erdos249257/DyadicPrefixCompression.lean#L2463)
- Lean declaration: [halfGreedy_takenRank_residualCancellation](../../Erdos249257/DyadicPrefixCompression.lean#L2788)

- outgoing **generated_by**: [Z39::odd_prefix_denominator_survives_dyadic_subtraction](BROWSER_Z39_1.md#node-3538be37239197d1). Odd-denominator survival identifies the primitive residual display, while the exact gcd measures the remaining raw-to-reduced scaling.
- outgoing **specialises**: [Z39::common_reduction_factors_cancel_from_the_successor_block_margin](BROWSER_Z39_1.md#node-c955249f7a94934e). The actual half-greedy prefix instantiates the abstract common-factor cancellation used by the gcd-free successor-block theorem.
- incoming **complements**: [Z39::actual_take_skip_recurrences_preserve_exact_prefix_coordinates](BROWSER_Z39_1.md#node-cc8f2d12a575f687). The gcd law explains taken-rank reduction, while the take/skip recurrences give the exact state evolution on both branches.

<a id="node-cc8f2d12a575f687"></a>
## actual_take_skip_recurrences_preserve_exact_prefix_coordinates

PROVED ACTUAL-ORBIT RECURRENCES: a taken rank adds exactly its Mersenne unit fraction to the reduced prefix, while a skipped rank leaves that prefix and both displayed coordinates unchanged. Consequently the excess on a skip obeys E(n+1)=2E(n)+D with no hidden cancellation factor, and every displayed residual numerator remains nonnegative.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The recurrences expose the finite state update but do not establish an asymptotic orbit invariant or infinitely many safe skips.

- Lean declaration: [halfGreedyPrefixRat_succ_of_take](../../Erdos249257/DyadicPrefixCompression.lean#L2589)
- Lean declaration: [halfGreedyPrefixRat_succ_of_skip](../../Erdos249257/DyadicPrefixCompression.lean#L2601)
- Lean declaration: [halfGreedyNextDyadicExcessNumerator_succ_of_skip](../../Erdos249257/DyadicPrefixCompression.lean#L2632)
- Lean declaration: [halfGreedyResidualDisplayedNumerator_nonneg](../../Erdos249257/DyadicPrefixCompression.lean#L2896)
- Lean declaration: [halfGreedy_coordinates_add_of_all_skips](../../Erdos249257/DyadicPrefixCompression.lean#L3164)

- outgoing **complements**: [Z39::actual_prefix_cancellation_gcd_scales_raw_and_primitive_coordinates](BROWSER_Z39_1.md#node-650d3cfda412e4f3). The gcd law explains taken-rank reduction, while the take/skip recurrences give the exact state evolution on both branches.

<a id="node-9295ee5fc0a396bd"></a>
## cap_violation_forces_a_long_take_block_without_creating_tail_escape

PROVED FORCED-BLOCK GEOMETRY: if a residual exceeds the two-channel cap at depth m>0, every one of the next 2m+2 Mersenne weights is greedily selected. Sharp higher-channel bounds place the remaining tails below explicit 8-adic and triple-depth thresholds, while exact subtraction shows that consecutive takes preserve signed distance from the full tail separatrix.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: A forced take block is not itself a contradiction: the residual and the true tail lose the same prefix. No cofinal safe-skip or achievement witness follows.

Open hypotheses: ["a cap violation at a specified depth; the theorem describes its finite consequence and does not assert that such violations occur cofinally"]

- Lean declaration: [greedyMersenne_forcedBlock_selected](../../Erdos249257/DyadicPrefixCompression.lean#L1106)
- Lean declaration: [forcedBlock_tailExcess_eq](../../Erdos249257/DyadicPrefixCompression.lean#L1153)
- Lean declaration: [mersenneWeightRemainder_le_four_thirds](../../Erdos249257/DyadicPrefixCompression.lean#L1162)
- Lean declaration: [mersenneWeightRemainderTail_le_four_twentyone](../../Erdos249257/DyadicPrefixCompression.lean#L1179)
- Lean declaration: [remainderTail_lt_tripleDyadic](../../Erdos249257/DyadicPrefixCompression.lean#L1206)
- Lean declaration: [capViolation_forces_threeDepthBlock](../../Erdos249257/DyadicPrefixCompression.lean#L1246)
- Lean declaration: [tripleDepthTail_lt_thirdChannel](../../Erdos249257/DyadicPrefixCompression.lean#L1260)

- outgoing **generated_by**: [Z39::two_channel_cap_is_an_exact_integer_excess_bound](BROWSER_Z39_1.md#node-08f4b180b3a963ff). The exact cap violation supplies the strict mass inequality that forces selection of the next 2m+2 weights.

<a id="node-c955249f7a94934e"></a>
## common_reduction_factors_cancel_from_the_successor_block_margin

PROVED GCD-FREE TRANSPORT: if the raw post-take coordinates (H,B) reduce by any positive common factor to the next displayed state, safety of every intervening skip is equivalent to the raw inequality H*2^(c-1)<=2B. Expanding H and B removes the gcd completely, adjacent takes inherit the margin automatically, and a gcd-scaled predecessor overshoot always implies the raw bound.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem identifies the right primitive obligation and closes adjacent takes only. Nonadjacent successor blocks still require new orbit arithmetic.

- Lean declaration: [reduced_nextBlock_all_skips_safe_iff_gcdFree](../../Erdos249257/DyadicPrefixCompression.lean#L451)
- Lean declaration: [reduced_nextBlock_gcdFree_margin_expanded](../../Erdos249257/DyadicPrefixCompression.lean#L463)
- Lean declaration: [rawTakenResidual_adjacent_margin_of_predecessor_safe](../../Erdos249257/DyadicPrefixCompression.lean#L496)
- Lean declaration: [rawPredecessorOvershoot_of_gcdScaled](../../Erdos249257/DyadicPrefixCompression.lean#L3435)

- outgoing **transport_of**: [Z39::constant_residual_skip_block_compresses_to_its_last_margin](BROWSER_Z39_1.md#node-70508bfd50d4a1c7). The reduced-state last-margin criterion is transported back to raw post-take coordinates by cancelling their common positive factor.
- incoming **specialises**: [Z39::actual_prefix_cancellation_gcd_scales_raw_and_primitive_coordinates](BROWSER_Z39_1.md#node-650d3cfda412e4f3). The actual half-greedy prefix instantiates the abstract common-factor cancellation used by the gcd-free successor-block theorem.
- incoming **barrier_for**: [Z39::finite_prefix_fixtures_expose_noninductive_margin_behaviour](BROWSER_Z39_1.md#node-b35eee3ea45309be). The finite examples show that denominator saturation and a strong current predecessor margin do not inductively supply the next nonadjacent raw margin.
- incoming **complements**: [Z39::unsafe_skip_forces_two_adjacent_mersenne_gcd_deficits](BROWSER_Z39_1.md#node-e599853c56b3f27c). The gcd-free margin states the sufficient raw inequality; its failure on a skipped rank yields the adjacent-gcd deficit necessary condition.

<a id="node-70508bfd50d4a1c7"></a>
## constant_residual_skip_block_compresses_to_its_last_margin

PROVED BLOCK COMPRESSION: between a take at rank a and the next take at b, dyadic safety is monotone across the unchanged-residual skips. All intermediate skips are safe exactly when the block is adjacent or its final skip satisfies the single margin p*2^(b-1)<=2D; minimality alone yields only the strictly weaker predecessor bound p(2^(b-1)-1)<2D.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Compression reduces a block to one inequality; it does not prove that inequality for every actual successor block.

- Lean declaration: [all_intermediate_BlockDyadicSafeAt_iff_last](../../Erdos249257/DyadicPrefixCompression.lean#L337)
- Lean declaration: [firstBlockTake_predecessor_open_bound](../../Erdos249257/DyadicPrefixCompression.lean#L358)
- Lean declaration: [firstBlockTake_all_skips_safe_iff_last_margin](../../Erdos249257/DyadicPrefixCompression.lean#L366)

- outgoing **generated_by**: [Z39::fixed_denominator_skip_excess_has_exact_affine_dynamics](BROWSER_Z39_1.md#node-44dd24fbc71f9b72). During an intervening skip block the displayed fraction is constant and the affine excess is monotone, leaving only the last skip to check.
- incoming **transport_of**: [Z39::common_reduction_factors_cancel_from_the_successor_block_margin](BROWSER_Z39_1.md#node-c955249f7a94934e). The reduced-state last-margin criterion is transported back to raw post-take coordinates by cancelling their common positive factor.

<a id="node-b35eee3ea45309be"></a>
## finite_prefix_fixtures_expose_noninductive_margin_behaviour

PROVED FINITE FIXTURE SUPPORT: the second noninductivity example has denominator equal to the lcm of all Mersenne denominators through rank seven, and in the factor-eleven example ranks six through eight skip before rank nine becomes the first subsequent take. These exact facts support counterexamples showing that saturation or a strong predecessor margin does not propagate automatically.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The fixtures refute particular proposed inductive invariants only. They neither refute Erdős #257 nor establish behavior beyond the displayed finite states.

- Lean declaration: [mersenneLcm_through_seven_eq](../../Erdos249257/DyadicPrefixCompression.lean#L638)
- Lean declaration: [firstTake_rank9_after_rank5_fixture](../../Erdos249257/DyadicPrefixCompression.lean#L3460)

- outgoing **barrier_for**: [Z39::common_reduction_factors_cancel_from_the_successor_block_margin](BROWSER_Z39_1.md#node-c955249f7a94934e). The finite examples show that denominator saturation and a strong current predecessor margin do not inductively supply the next nonadjacent raw margin.

<a id="node-44dd24fbc71f9b72"></a>
## fixed_denominator_skip_excess_has_exact_affine_dynamics

PROVED AFFINE SKIP DYNAMICS: for a displayed residual p/(2L) whose numerator and denominator do not change during a skip run, the dyadic excess satisfies E(n+1)=2E(n)+L and hence E(n+k)=2^k E(n)+(2^k-1)L. The rational distance from the next dyadic point is exactly E divided by 2^(n+1)L.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The recurrence describes a run after its take/skip pattern is fixed. It does not prove that the actual orbit has arbitrarily long, safe, or cofinal skip runs.

- Lean declaration: [nextDyadicExcessIntNumerator_succ](../../Erdos249257/DyadicPrefixCompression.lean#L161)
- Lean declaration: [nextDyadicExcessIntNumerator_add](../../Erdos249257/DyadicPrefixCompression.lean#L169)
- Lean declaration: [divInt_sub_nextDyadic_eq_excess_divInt](../../Erdos249257/DyadicPrefixCompression.lean#L183)

- incoming **generated_by**: [Z39::one_integer_excess_classifies_safe_skip_take_and_forbidden_sliver](BROWSER_Z39_1.md#node-484e65cfe782cc99). The exact affine excess coordinate is the integer quantity whose sign and comparison with p classify every next-rank decision.
- incoming **generated_by**: [Z39::constant_residual_skip_block_compresses_to_its_last_margin](BROWSER_Z39_1.md#node-70508bfd50d4a1c7). During an intervening skip block the displayed fraction is constant and the affine excess is monotone, leaving only the last skip to check.

<a id="node-3538be37239197d1"></a>
## odd_prefix_denominator_survives_dyadic_subtraction

PROVED DENOMINATOR TRANSPORT: subtracting a reduced odd-denominator fraction from a dyadic fraction cannot cancel any odd factor of the denominator. For the actual finite half-greedy prefix, the prefix denominator is odd, the residual has an exact p/(2D) display, and finite support sums agree under the rational-to-real cast.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Odd-part survival excludes cancellation and boundary ties, but it neither supplies infinitely many safe skips nor proves that one half belongs to the Mersenne achievement set.

- Lean declaration: [dyadicResidualNumerator_coprime_oddDenominator](../../Erdos249257/DyadicPrefixCompression.lean#L98)
- Lean declaration: [greedyHalfRemainderRat_eq_displayed_divInt](../../Erdos249257/DyadicPrefixCompression.lean#L732)
- Lean declaration: [finiteErdosSum_den_odd](../../Erdos249257/DyadicPrefixCompression.lean#L1513)
- Lean declaration: [halfGreedyPrefixDenominator_odd](../../Erdos249257/DyadicPrefixCompression.lean#L1521)
- Lean declaration: [erdosSupportSeries_finset_eq_cast_finiteErdosSum](../../Erdos249257/DyadicPrefixCompression.lean#L1539)

- incoming **generated_by**: [Z39::actual_prefix_cancellation_gcd_scales_raw_and_primitive_coordinates](BROWSER_Z39_1.md#node-650d3cfda412e4f3). Odd-denominator survival identifies the primitive residual display, while the exact gcd measures the remaining raw-to-reduced scaling.

<a id="node-484e65cfe782cc99"></a>
## one_integer_excess_classifies_safe_skip_take_and_forbidden_sliver

PROVED EXACT DECISION CLASSIFIER: for p/(2L), E<=0 is exactly the safe side of the next dyadic boundary, 2E<p is exactly a greedy skip, and 0<E with 2E<p is exactly the skipped-but-dyadically-unsafe Mersenne sliver. The decision defect 2E-p gives the same safe, strengthened-take, and open negative-unit-window trichotomy without division.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The classifier locates an unsafe skip if one occurs; it does not rule out unsafe skips in the actual half-greedy orbit.

- Lean declaration: [divInt_le_nextDyadic_iff_excess_nonpos](../../Erdos249257/DyadicPrefixCompression.lean#L198)
- Lean declaration: [mersenneWeightRat_succ_le_divInt_iff_excess](../../Erdos249257/DyadicPrefixCompression.lean#L212)
- Lean declaration: [divInt_lt_mersenneWeightRat_succ_iff_excess](../../Erdos249257/DyadicPrefixCompression.lean#L252)
- Lean declaration: [divInt_mem_nextMersenneDyadicSliver_iff_excess](../../Erdos249257/DyadicPrefixCompression.lean#L262)
- Lean declaration: [nextMersenneDecisionDefect_eq_two_excess_sub](../../Erdos249257/DyadicPrefixCompression.lean#L282)
- Lean declaration: [nextMersenneDecisionDefect_le_neg_iff_excess_nonpos](../../Erdos249257/DyadicPrefixCompression.lean#L293)
- Lean declaration: [le_nextMersenneDecisionDefect_iff_le_excess](../../Erdos249257/DyadicPrefixCompression.lean#L302)
- Lean declaration: [nextMersenneDecisionDefect_mem_neg_unit_window_iff](../../Erdos249257/DyadicPrefixCompression.lean#L311)

- outgoing **generated_by**: [Z39::fixed_denominator_skip_excess_has_exact_affine_dynamics](BROWSER_Z39_1.md#node-44dd24fbc71f9b72). The exact affine excess coordinate is the integer quantity whose sign and comparison with p classify every next-rank decision.
- incoming **specialises**: [Z39::two_channel_cap_is_an_exact_integer_excess_bound](BROWSER_Z39_1.md#node-08f4b180b3a963ff). The two-channel test refines the same excess coordinate by comparing the first positive dyadic excess with the explicit 4-adic correction.
- incoming **generated_by**: [Z39::unsafe_skip_forces_two_adjacent_mersenne_gcd_deficits](BROWSER_Z39_1.md#node-e599853c56b3f27c). The forbidden-sliver inequalities are exactly the unsafe Mersenne sandwich used to bound both adjacent gcds.

<a id="node-08f4b180b3a963ff"></a>
## two_channel_cap_is_an_exact_integer_excess_bound

PROVED CAP GEOMETRY: comparison of p/(2L) with the next two-channel cap is exactly 3*2^(n+1)E<=L. On the actual half-greedy orbit, positivity of E detects landing above the dyadic boundary, 2E<p detects a skip, and the reverse strict cap inequality detects violation of the two-channel producer.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The equivalence does not prove the cap inequality at every skipped rank. That universal producer remains an open antecedent in the downstream membership theorem.

- Lean declaration: [divInt_le_nextTwoChannelCap_iff_excess](../../Erdos249257/DyadicPrefixCompression.lean#L668)
- Lean declaration: [nextDyadic_lt_greedyHalfRemainder_iff_excess_pos](../../Erdos249257/DyadicPrefixCompression.lean#L1004)
- Lean declaration: [greedyHalfRemainder_lt_mersenneWeight_iff_excess](../../Erdos249257/DyadicPrefixCompression.lean#L1013)
- Lean declaration: [twoChannelCap_lt_greedyHalfRemainder_iff_excess](../../Erdos249257/DyadicPrefixCompression.lean#L1057)

- outgoing **specialises**: [Z39::one_integer_excess_classifies_safe_skip_take_and_forbidden_sliver](BROWSER_Z39_1.md#node-484e65cfe782cc99). The two-channel test refines the same excess coordinate by comparing the first positive dyadic excess with the explicit 4-adic correction.
- incoming **generated_by**: [Z39::cap_violation_forces_a_long_take_block_without_creating_tail_escape](BROWSER_Z39_1.md#node-9295ee5fc0a396bd). The exact cap violation supplies the strict mass inequality that forces selection of the next 2m+2 weights.

<a id="node-e599853c56b3f27c"></a>
## unsafe_skip_forces_two_adjacent_mersenne_gcd_deficits

PROVED UNSAFE-SKIP BARRIER: if p is odd and p(2^c-1)<2D<p2^c, then both gcd(D,2^c-1) and gcd(D,2^(c+1)-1) are strictly smaller than p. Therefore every putative dyadically unsafe skip in the actual half-greedy orbit forces consecutive Mersenne gcd deficits below the current displayed residual numerator.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: candidate_new_statement.

Scope: This is a necessary consequence of an unsafe skip, not a contradiction: no theorem here supplies a lower bound forcing either adjacent gcd to reach p. It does not solve #257.

- Lean declaration: [unsafeSandwich_consecutive_gcd_lt](../../Erdos249257/DyadicPrefixCompression.lean#L4298)
- Lean declaration: [greedyHalf_unsafeSkip_consecutive_gcd_lt](../../Erdos249257/DyadicPrefixCompression.lean#L4373)

- outgoing **complements**: [Z39::common_reduction_factors_cancel_from_the_successor_block_margin](BROWSER_Z39_1.md#node-c955249f7a94934e). The gcd-free margin states the sufficient raw inequality; its failure on a skipped rank yields the adjacent-gcd deficit necessary condition.
- outgoing **generated_by**: [Z39::one_integer_excess_classifies_safe_skip_take_and_forbidden_sliver](BROWSER_Z39_1.md#node-484e65cfe782cc99). The forbidden-sliver inequalities are exactly the unsafe Mersenne sandwich used to bound both adjacent gcds.

