# Z10_2: Support-coefficient calculus for #257: divisor incidence, dilation, sunflowers and the squarefree barrier

[All problems and zones](BROWSER.md)

<a id="node-6cf216bc1ead238e"></a>
## half_membership_from_actual_block_safety

If at every rank the actual greedy run for 1/2 skips, the displayed state is block dyadically safe at the next rank, then 1/2 lies in the Mersenne achievement set - that is, some support of exponents has sum of 1/(2^a - 1) equal to exactly 1/2, which for an infinite support would be a counterexample to Erdos #257. This is the base supply socket that every other half-membership node in this zone factors through.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsafe : for all n, if the actual greedy run skips rank n+1 (that is, mersenneWeight (n+1) is not at most greedyMersenneRemainder (1/2) n) then BlockDyadicSafeAt (halfGreedyResidualDisplayedNumerator n).natAbs (halfGreedyPrefixDenominator n) (n+1). The hypothesis is written inline rather than as a named predicate, which is why it escaped the ledger; no declaration in the corpus proves it, no finite computation can, and safe_bracket_plus_numerator_monotone_is_not_inductive refutes the obvious induction that would have produced it."]

- Lean declaration: [half_mem_mersenneAchievementSet_of_actualBlockSafe](../../Erdos249257/DyadicPrefixCompression.lean#L2944)

- incoming **specialises**: [Z10::half_membership_from_raw_block_margin_supply](BROWSER_Z10_2.md#node-5d104a681bbe0d26). half_mem_mersenneAchievementSet_of_skippedRawBlockMarginSupply and its two siblings all discharge their conclusion by applying half_mem_mersenneAchievementSet_of_actualBlockSafe (DyadicPrefixCompression.lean lines 3219 and 3240); the raw margin is one way of supplying that node's hypothesis.
- incoming **specialises**: [Z10::half_membership_from_gcd_overshoot_supply](BROWSER_Z10_2.md#node-3425e915369370cb). half_mem_mersenneAchievementSet_of_unsafeSkipGcdOvershootSupply applies half_mem_mersenneAchievementSet_of_actualBlockSafe (DyadicPrefixCompression.lean line 3424); the gcd-scaled overshoot is a second way of supplying the same hypothesis.
- outgoing **depends_on_open**: [Z10::greedy_take_predicate_equals_block_take_predicate](BROWSER_Z10_1.md#node-e3ae02f4c5975be1). The conditional consumes greedyHalfRemainder_le_nextDyadic_of_BlockSafe to turn arithmetic block safety at a skipped rank into the analytic dyadic-cap bound.
- incoming **barrier_for**: [Z10::safe_bracket_plus_numerator_monotone_is_not_inductive](BROWSER_Z10_2.md#node-d7bbf09469c1dee7). The fixture refutes safe bracketing plus numerator monotonicity as an inductive route to the hsafe hypothesis at specific states; it leaves the hypothesis unproved rather than refuted, and says nothing about whether the greedy run for 1/2 reaches those states.
- outgoing **specialises**: [Z12::channel_cap_skip_transport](BROWSER_Z12_1.md#node-3b04a5f99d781f94). `greedyHalfRemainder_le_nextDyadic_of_BlockSafe` (DyadicPrefixCompression.lean:2759) turns block dyadic safety at a skipped rank into `greedyMersenneRemainder (1/2) n <= halfDyadicCap (n+1)`, which is verbatim the dyadic-cap branch hypothesis of Z12's node; both conclude 1/2 in mersenneAchievementSet.

<a id="node-3425e915369370cb"></a>
## half_membership_from_gcd_overshoot_supply

If at every putatively unsafe skipped rank the gcd of the prefix denominator with 2^(n+1) - 1, times the displayed numerator, is at most the predecessor overshoot, then no unsafe skip exists and 1/2 lies in the Mersenne achievement set. The gcd-scaled and primitive-quotient forms of this supply are exactly equivalent, and an eleven-fold strengthening also suffices.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : HalfGreedyUnsafeSkipGcdOvershootSupply - at every skipped and not-already-safe rank n, gcd(D(n), 2^(n+1) - 1) * |num(n)| <= 2 D(n) - |num(n)| (2^(n+1) - 1); unproved", "hsupply : HalfGreedyUnsafeSkipPrimitiveOvershootSupply - the equivalent primitive-quotient form; unproved", "hsupply : HalfGreedyUnsafeSkipElevenGcdOvershootSupply - the eleven-fold strengthening; unproved"]

- Lean declaration: [half_mem_mersenneAchievementSet_of_unsafeSkipGcdOvershootSupply](../../Erdos249257/DyadicPrefixCompression.lean#L4479)
- Lean declaration: [unsafeSkipGcdOvershootSupply_iff_primitive](../../Erdos249257/DyadicPrefixCompression.lean#L4521)
- Lean declaration: [half_mem_mersenneAchievementSet_of_unsafeSkipPrimitiveOvershootSupply](../../Erdos249257/DyadicPrefixCompression.lean#L4562)
- Lean declaration: [half_mem_mersenneAchievementSet_of_unsafeSkipElevenGcdOvershootSupply](../../Erdos249257/DyadicPrefixCompression.lean#L4595)

- outgoing **specialises**: [Z10::half_membership_from_actual_block_safety](BROWSER_Z10_2.md#node-6cf216bc1ead238e). half_mem_mersenneAchievementSet_of_unsafeSkipGcdOvershootSupply applies half_mem_mersenneAchievementSet_of_actualBlockSafe (DyadicPrefixCompression.lean line 3424); the gcd-scaled overshoot is a second way of supplying the same hypothesis.
- outgoing **depends_on_open**: [Z10::raw_dyadic_safety_is_predecessor_overshoot](BROWSER_Z10_2.md#node-d20a79c3f7242c31). The supply is the gcd-scaled form of the overshoot inequality that characterises safety.
- incoming **barrier_for**: [Z10::raw_dyadic_safety_is_strictly_weaker_than_gcd_overshoot](BROWSER_Z10_2.md#node-7ce5d720dc52fe34). An explicit state that is raw-safe but fails the gcd-scaled bound shows that lane cannot be obtained from raw safety alone; it does not refute the supply.

<a id="node-5d104a681bbe0d26"></a>
## half_membership_from_raw_block_margin_supply

If every skipped rank of the greedy run for 1/2 is bracketed by consecutive actual takes whose source-coordinate raw margin inequality holds, then that skip is block-dyadically safe, and 1/2 lies in the Mersenne achievement set. It suffices to supply the witness only at skips that are not already safe.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : HalfGreedySkippedActualRawMarginSupply - at every skipped rank, existence of a HalfGreedySkippedActualRawMarginWitness, i.e. a bracketing pair of actual takes with (num * (2^b - 1) - 2D) * 2^(c-1) <= 2 D (2^b - 1); unproved", "hsupply : HalfGreedySkippedRawBlockMarginSupply and hsupply : HalfGreedyUnsafeSkipActualRawMarginSupply - the same obligation in raw-block and minimal unsafe-skip form; unproved"]

- Lean declaration: [half_mem_mersenneAchievementSet_of_skippedActualRawMarginSupply](../../Erdos249257/DyadicPrefixCompression.lean#L3381)
- Lean declaration: [half_mem_mersenneAchievementSet_of_skippedRawBlockMarginSupply](../../Erdos249257/DyadicPrefixCompression.lean#L3371)
- Lean declaration: [half_mem_mersenneAchievementSet_of_unsafeSkipActualRawMarginSupply](../../Erdos249257/DyadicPrefixCompression.lean#L3393)
- Lean declaration: [halfGreedy_rawBlockWitness_of_actualRawMarginWitness](../../Erdos249257/DyadicPrefixCompression.lean#L3249)
- Lean declaration: [halfGreedy_BlockSafe_of_rawBlockWitness](../../Erdos249257/DyadicPrefixCompression.lean#L3360)

- outgoing **depends_on_open**: [Z10::greedy_take_predicate_equals_block_take_predicate](BROWSER_Z10_1.md#node-e3ae02f4c5975be1). The raw block witness delivers block dyadic safety, which is what the greedy consumer needs.
- outgoing **specialises**: [Z10::half_membership_from_actual_block_safety](BROWSER_Z10_2.md#node-6cf216bc1ead238e). half_mem_mersenneAchievementSet_of_skippedRawBlockMarginSupply and its two siblings all discharge their conclusion by applying half_mem_mersenneAchievementSet_of_actualBlockSafe (DyadicPrefixCompression.lean lines 3219 and 3240); the raw margin is one way of supplying that node's hypothesis.
- outgoing **depends_on_open**: [Z10::block_take_and_safety_predicates_are_gcd_invariant](BROWSER_Z10_1.md#node-f409427eedd8d532). Scale invariance is what lets the witness be stated in raw uncancelled coordinates.
- incoming **barrier_for**: [Z10::safe_bracket_plus_numerator_monotone_is_not_inductive](BROWSER_Z10_2.md#node-d7bbf09469c1dee7). It kills the obvious induction that would have produced the raw margin witnesses, leaving the supply unproved rather than refuted.

<a id="node-24557a20c8c5dc51"></a>
## half_membership_from_skipped_excess_bound

If at every skipped rank the integer excess satisfies 3 * 2^(n+1) * E(n) <= D(n), then 1/2 lies in the Mersenne achievement set, that is, some support of exponents has sum of 1/(2^a - 1) equal to exactly 1/2.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hbound : HalfGreedySkippedExcessBound, i.e. for every n, if the greedy run skips rank n+1 then 3 * ((2 ^ (n+1)) * halfGreedyNextDyadicExcessNumerator n) <= halfGreedyPrefixDenominator n. No declaration in the corpus proves this, and no finite computation can establish it."]

- Lean declaration: [half_mem_mersenneAchievementSet_of_skipped_excessBound](../../Erdos249257/DyadicPrefixCompression.lean#L1078)

- incoming **equivalent_to**: [Z10::half_membership_from_take_run_excess_bounds](BROWSER_Z10_2.md#node-835c9dff117dcdd9). halfGreedyThreeDepthTakeRunExcessBound_iff_skippedExcessBound proves the two antecedents equivalent.
- outgoing **depends_on_open**: [Z10::half_value_iff_canonical_affine_carry_tempered](BROWSER_Z10_2.md#node-6b727b8f4e070ab3). Both concern the same open question, whether 1/2 is the value of some exponent support; the carry equivalence is its coordinate-free form.
- outgoing **transport_of**: [Z12::channel_cap_skip_transport](BROWSER_Z12_1.md#node-3b04a5f99d781f94). HalfGreedySkippedExcessBound is the integer excess-numerator form of the analytic two-channel cap hypothesis of half_mem_mersenneAchievementSet_of_skipped_twoChannelCap, via greedyHalfRemainder_le_twoChannelCap_iff_excess.

<a id="node-835c9dff117dcdd9"></a>
## half_membership_from_take_run_excess_bounds

The skipped-rank excess bound need only be assumed on skips followed by a full forced take run: requiring it after a run of 2n+4 takes is already sufficient, and is in fact equivalent to the unrestricted bound; the weaker n+2 take-run form is also sufficient.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hthree : HalfGreedyThreeDepthTakeRunExcessBound - the excess inequality at every skipped rank whose next 2n+4 ranks are all taken; unproved", "hlong : HalfGreedyLongTakeRunExcessBound - the same with n+2 forced takes; unproved"]

- Lean declaration: [halfGreedyThreeDepthTakeRunExcessBound_iff_skippedExcessBound](../../Erdos249257/DyadicPrefixCompression.lean#L2176)
- Lean declaration: [halfGreedySkippedExcessBound_of_threeDepthTakeRun](../../Erdos249257/DyadicPrefixCompression.lean#L1443)
- Lean declaration: [half_mem_mersenneAchievementSet_of_threeDepthTakeRunExcessBound](../../Erdos249257/DyadicPrefixCompression.lean#L1461)
- Lean declaration: [halfGreedySkippedExcessBound_of_longTakeRun](../../Erdos249257/DyadicPrefixCompression.lean#L1481)
- Lean declaration: [half_mem_mersenneAchievementSet_of_longTakeRunExcessBound](../../Erdos249257/DyadicPrefixCompression.lean#L1503)

- outgoing **equivalent_to**: [Z10::half_membership_from_skipped_excess_bound](BROWSER_Z10_2.md#node-24557a20c8c5dc51). halfGreedyThreeDepthTakeRunExcessBound_iff_skippedExcessBound proves the two antecedents equivalent.
- outgoing **depends_on_open**: [Z10::unsafe_skip_forces_long_forced_take_block](BROWSER_Z10_2.md#node-c29d8d1929d4f3b7). The run compression is legitimate only because a cap-violating skip forces the displayed take run.

<a id="node-2240732fc236082d"></a>
## half_value_forces_residual_reciprocal_mass_bound

If a support containing {2,3} (respectively {2,3,6,7,14}) has value exactly 1/2 and its residual above that fragment is nonempty, then the residual's reciprocal sum diverges or exceeds the wrap ratio attached to the fragment's lcm.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hwhole : erdosSupportSeries 2 A = 1 / 2 - the open hypothesis that some support sums to exactly 1/2, which for infinite A would refute Erdos #257"]

- Lean declaration: [two_three_residual_reciprocalMassDivergesOrAtLeast](../../Erdos249257/DyadicPrefixCompression.lean#L1715)
- Lean declaration: [five_term_residual_reciprocalMassDivergesOrAtLeast](../../Erdos249257/DyadicPrefixCompression.lean#L1740)

- outgoing **finite_instance_of**: [Z10::finite_fragment_residual_transport](BROWSER_Z10_1.md#node-cc4b29d2ebadd1ad). The two named fragments instantiate the generic compression certificate.
- outgoing **depends_on_open**: [Z12::half_membership_iff_infinite_greedy_skips](BROWSER_Z12_1.md#node-f4d02068c1837778). the hypothesis is that some support has value exactly 1/2; this equivalence pins that to infinitude of the greedy skipped support at 1/2 and states that neither side is decided anywhere, so the antecedent has no producer.

<a id="node-6b727b8f4e070ab3"></a>
## half_value_iff_canonical_affine_carry_tempered

A support sums to exactly 1/2 if and only if its canonical affine denominator-two carry orbit is tempered; the scaled residual 2^N (1/2 - value) equals that carry halved minus the incidence tail, and for a finite prefix through N+1 the residual is (integer affine carry minus finite tail) over 2^(N+1).

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["whether any support has value exactly 1/2 is open; both sides of this equivalence are undecided in the corpus"]

- Lean declaration: [support_half_iff_affineBinaryOrbit_tempered](../../Erdos249257/BooleanMobiusCarry.lean#L527)
- Lean declaration: [halfSupportSeries_residual_scaled_eq_affineCarry_sub_tail](../../Erdos249257/BooleanMobiusCarry.lean#L549)
- Lean declaration: [halfFinitePrefix_residual_eq_pow_mul_integerCarry_sub_finiteTail](../../Erdos249257/BooleanMobiusCarry.lean#L645)

- outgoing **specialises**: [Z10::rationality_iff_tempered_support_carry_orbit](BROWSER_Z10_2.md#node-dd2d02eb2e53e47f). Denominator two with the existential orbit removed by recurrence uniqueness.
- incoming **depends_on_open**: [Z10::half_membership_from_skipped_excess_bound](BROWSER_Z10_2.md#node-24557a20c8c5dc51). Both concern the same open question, whether 1/2 is the value of some exponent support; the carry equivalence is its coordinate-free form.
- incoming **barrier_for**: [Z10::mobius_sign_truncation_overshoots_one_half](BROWSER_Z10_2.md#node-5310e365367dca64). It removes the negative-Mobius support as a candidate solution of the value-one-half question and nothing more.
- outgoing **equivalent_to**: [Z12::half_value_correction_complement_equivalence](BROWSER_Z12_1.md#node-d85d3e5dd775a717). support_half_iff_affineBinaryOrbit_tempered (BooleanMobiusCarry.lean:526) and positiveMersenneSupportValue_eq_half_iff_correction_eq_complement (GreedyAchievementSet.lean:2990) are two iff-characterisations of the same proposition 'value = 1/2', identified by positiveMersenneSupportValue_eq_erdosSupportSeries.
- outgoing **equivalent_to**: [Z12::half_membership_iff_infinite_greedy_skips](BROWSER_Z12_1.md#node-f4d02068c1837778). mem_mersenneAchievementSet_iff_greedy_survival and greedySupport_supportValue_eq make membership of 1/2 the existence of a normalised support with value 1/2, which is the left side of support_half_iff_affineBinaryOrbit_tempered.

<a id="node-079ff9668b18c90e"></a>
## mixed_prime_power_layer_algebra

Prime-power layer operators commute as integer finite differences, and the composite of two layers at distinct primes extracts the iterated exact-valuation pullback at arguments coprime to the product of those primes.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [primePowerLayer_comm](../../Erdos249257/MaximalOmegaLayer.lean#L29)
- Lean declaration: [mixedPrimePowerLayerTwo_supportCoeffInt](../../Erdos249257/MaximalOmegaLayer.lean#L39)

- outgoing **specialises**: [Z10::exact_prime_power_valuation_layer](BROWSER_Z10_1.md#node-eb34f91e4ca619b3). Two-fold iteration of the single-prime layer identity at distinct primes.

<a id="node-34ed548cbedf7039"></a>
## mobius_inversion_of_support_coefficient

For any support A the divisor-incidence coefficient equals the Dirichlet convolution of the normalised support indicator with zeta, and the Mobius transform inverts it: mu * sc_A is the indicator of A on positive integers, and equals A exactly as a set once 0 is excluded from A.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [positiveSupportBitAF_mul_zeta](../../Erdos249257/BooleanMobiusCarry.lean#L77)
- Lean declaration: [moebius_mul_supportCoeffAF](../../Erdos249257/BooleanMobiusCarry.lean#L95)
- Lean declaration: [mobius_supportCoeff_eq_one_iff](../../Erdos249257/BooleanMobiusCarry.lean#L112)
- Lean declaration: [mobius_supportCoeff_boolean](../../Erdos249257/BooleanMobiusCarry.lean#L118)
- Lean declaration: [mobius_supportCoeff_recovers_support](../../Erdos249257/BooleanMobiusCarry.lean#L128)

- incoming **reformulates**: [Z10::boolean_mobius_transform_characterises_support_coefficients](BROWSER_Z10_1.md#node-5cfdf4fb93485caf). The converse direction is the same Dirichlet inversion read as a characterisation of which arithmetic functions are support incidences.
- outgoing **reformulates**: [Z01::support_coefficient_representation](BROWSER_Z01_2.md#node-950d0bc2e85796ab). mobius_supportCoeff_recovers_support inverts the coefficient construction of erdosSupportSeries_eq_tsum_supportCoeff: the support and its divisor-incidence coefficient are interchangeable data on positive integers.

<a id="node-5310e365367dca64"></a>
## mobius_sign_truncation_overshoots_one_half

Splitting the signed identity sum over d of mu(d)/(2^d - 1) = 1/2 by sign gives that the Boolean support {d : mu(d) = -1} sums to 1/2 plus the entire positive-Mobius tail from d = 2 onwards; that tail contains the term 1/63 at d = 6, so the negative-Mobius support sums to strictly more than 1/2, in fact at least 1/2 + 1/63.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rules out exactly one route: taking the negative-Mobius indices as a Boolean support in the hope of realising 1/2. It does not decide whether some other infinite Boolean support sums to 1/2, it does not touch the greedy Mersenne route, it says nothing about the irrationality of the negative-Mobius value itself, and it is specific to base 2 and to the target 1/2.

- Lean declaration: [tsum_negativeMobius_eq_half_add_positiveMobiusTail](../../Erdos249257/MobiusSignSupportNoGo.lean#L111)
- Lean declaration: [half_add_one_div_sixty_three_le_tsum_negativeMobius](../../Erdos249257/MobiusSignSupportNoGo.lean#L150)
- Lean declaration: [half_lt_tsum_negativeMobius](../../Erdos249257/MobiusSignSupportNoGo.lean#L164)

- outgoing **barrier_for**: [Z10::half_value_iff_canonical_affine_carry_tempered](BROWSER_Z10_2.md#node-6b727b8f4e070ab3). It removes the negative-Mobius support as a candidate solution of the value-one-half question and nothing more.
- outgoing **barrier_for**: [Z07::lambert_rung_moebius_rational](BROWSER_Z07_1.md#node-76e8be10a56dc445). tsum_negativeMobius_eq_half_add_positiveMobiusTail is literally the sign split of tsum_moebius_div_two_pow_sub_one_eq_half (sum mu(d)/(2^d - 1) = 1/2); half_lt_tsum_negativeMobius then shows the negative-Mobius Boolean truncation exceeds 1/2 by at least 1/63, so the rational Lambert rung cannot be converted into a Boolean Mersenne support realising 1/2.
- outgoing **barrier_for**: [Z01::lambert_ladder_rational_rungs](BROWSER_Z01_1.md#node-4d6cc8cc64c5cf91). Same sign split applied to the L(mu) = 1/2 rung recorded in this node: the Boolean-support reading of that rung overshoots its own value by at least 1/63 (half_add_one_div_sixty_three_le_tsum_negativeMobius), so the rung is not a route into the Mersenne achievement set.

<a id="node-1a10899dcf610d9a"></a>
## multiplicative_order_of_two_mod_odd

For odd v > 1 the multiplicative order of 2 modulo v exists, is positive, is a doubling period, and the wrap count over one full order is positive.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [pow_oddDoublingOrder_mod_eq_one](../../Erdos249257/RationalSupportCarrySkeleton.lean#L441)
- Lean declaration: [oddDoublingOrder_isPeriod](../../Erdos249257/RationalSupportCarrySkeleton.lean#L465)
- Lean declaration: [oddOrder_doublingWrapCount_pos](../../Erdos249257/RationalSupportCarrySkeleton.lean#L472)


<a id="node-8a6ef15977d14203"></a>
## no_block_certificate_at_squarefree_support

At the squarefree support and every even base b >= 2, the two block-certificate engines that impose a FIRST-BLOCK DIVISIBILITY condition - the digitwise one and the carry-aware one - have no instance: already at precision q = b^2 no tuple (N, K, L, C) satisfies either schema. Blocks of length K >= 1 die by parity, because the carried first block forces b to divide an odd coefficient, and K <= 1 dies by density, because the incidence is at least 1 from n = 2 on and the middle block alone exhausts the budget b^L. Both steps consume the divisibility hypothesis, so the argument does not extend to the divisibility-free low-carry engine (see scope_caveat).

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Does NOT rule out: (1) THE LOW-CARRY RESIDUE-BAND ENGINE. irrational_coeff_series_of_weighted_coeff_low_carry_block_certificates (Erdos249257/CertificateKernel.lean:14707) is a third, strictly weaker arbitrary-coefficient engine, and it is NOT closed here. It imposes no divisibility condition on the first block at all - only the height inequality q * (V * b^(L-K) + C + (N+L+2)) < b^L with V = (sum over r in Icc 1 K of c(N+r) * b^(K-r)) mod b^K - so dvd_last_of_carry_block has nothing to attack, the parity of 2^omega(n) - 1 is irrelevant to it, and the K <= 1 density step never triggers because K is no longer forced down. It reaches the squarefree support by exactly the two steps the other two engines use (erdosSupportSeries_eq_tsum_supportCoeff plus supportCoeff_le_self), so the absence of an erdosSupportSeries-level wrapper is bookkeeping, not scope. This is the same third-engine gap that was nearly published once; do not restate this barrier as closing the block-certificate family. (2) The irrationality of the squarefree-support value itself, which is open and untouched. (3) Odd bases - the hypothesis hbeven : 2 divides b is used essentially. (4) The shifted support obtained by adjoining 1, which has the same irrationality question and does admit full digitwise opening blocks of every length (see adjoining_one_is_value_free_and_repairs_the_parity). (5) Any irrationality engine outside the block-certificate schemas - in particular the lcm-gap engine irrational_erdosSum_of_lcm_gap, the near-integer engine, and the periodic/residue-class specialisations of CertificateKernel are entirely unaffected. (6) Universal Erdos #257, since the argument is about one specific support. The obstruction is a property of the coefficient normalisation 2^omega(n) - 1, not of the support.

- Lean declaration: [no_carry_block_certificate](../../ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L222)
- Lean declaration: [not_exists_carry_certificates_squarefreeSupport](../../ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L274)
- Lean declaration: [not_exists_digitwise_certificates_squarefreeSupport](../../ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L292)

- outgoing **barrier_for**: [Z10::sunflower_conditional_irrationality](BROWSER_Z10_2.md#node-369dbe6f906c9180). The refuted hypothesis is literally SunflowerForcedCarrySupply at b = 2 instantiated at the squarefree support, so that lane is closed at that one support and nowhere else.
- outgoing **depends_on_open**: [Z10::carry_block_forces_base_divides_last_coefficient](BROWSER_Z10_1.md#node-fc322bda4fc679b7). The parity half of the barrier is exactly the last-coefficient divisibility lemma.
- outgoing **depends_on_open**: [Z10::squarefree_incidence_is_two_pow_omega_minus_one](BROWSER_Z10_2.md#node-956b8639c5ba1ed3). Both the parity and the density halves are read off the exact incidence 2^omega(n) - 1.
- incoming **repair_of**: [Z10::adjoining_one_is_value_free_and_repairs_the_parity](BROWSER_Z10_1.md#node-056b46367312b353). Adjoining 1 keeps the irrationality question and restores satisfiable digitwise opening blocks of every length, so the barrier is a statement about the normalisation.
- outgoing **barrier_for**: [Z01::generic_coefficient_certificate_engine](BROWSER_Z01_1.md#node-347d00f05c4a588d). not_exists_digitwise_certificates_squarefreeSupport: at the squarefree support and every even base b, no tuple (N,K,L,C) satisfies the digitwise weighted-coefficient block schema already at precision q = b^2; that schema is exactly the hypothesis consumed by irrational_coeff_series_of_weighted_coeff_block_certificates / irrational_erdosSupportSeries_of_weighted_coeff_certificates, the evidence of this engine node.
- outgoing **barrier_for**: [Z01::carry_aware_certificate_engine](BROWSER_Z01_1.md#node-85bdec04dff8f727). not_exists_carry_certificates_squarefreeSupport, via no_carry_block_certificate: the carried first block forces b to divide the last first-block coefficient (carry_block_forces_base_divides_last_coefficient), but the squarefree incidence is 2^omega(n) - 1, odd at every n >= 2 (squarefree_incidence_is_two_pow_omega_minus_one), so the aggregate divisibility hypothesis of irrational_coeff_series_of_weighted_coeff_carry_block_certificates has no instance at even b.

<a id="node-1dc753b317ffad9e"></a>
## odd_tail_state_residue_excess_decomposition

Given an odd-denominator tail state for a support - an integer sequence u with u(n) = v times the binary incidence tail and u(n) congruent to p*2^n modulo v - the tail splits exactly as residue/v plus a nonnegative integer excess, the excess obeys sc_A(N+1) + excess(N+1) = wrap digit + 2 excess(N), and summing over one doubling period gives wrap count plus the summed excess.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [oddSupportTail_eq_residue_div_add_excess](../../Erdos249257/RationalSupportCarrySkeleton.lean#L509)
- Lean declaration: [sum_supportTail_block_eq_wrapCount_add_excess](../../Erdos249257/RationalSupportCarrySkeleton.lean#L532)
- Lean declaration: [supportCoeff_add_oddTailExcess_succ_eq_wrap_add_two_excess](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1653)
- Lean declaration: [shiftedOddSupportTail_eq_residue_div_add_excess](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1850)

- incoming **depends_on_open**: [Z10::wrap_ratio_lower_bounds_reciprocal_mass](BROWSER_Z10_3.md#node-d2c3c4382da7aea9). The decomposition supplies the residue/excess split whose means are taken.
- outgoing **depends_on_open**: [Z10::rational_value_constructs_odd_tail_state](BROWSER_Z10_2.md#node-ded6e5d67b309122). The tail state only exists under the rational-value hypothesis.

<a id="node-96a828a2b1fff4d1"></a>
## one_wrap_cycle_classification_node

A closed doubling cycle of length h with numerator coprime to the modulus and exactly one wrap forces the modulus to be the Mersenne number 2^h - 1 and the starting residue to be a power of two below h. The same classification holds for the actual multiplicative order of 2.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [one_wrap_cycle_classification](../../Erdos249257/RationalSupportCarrySkeleton.lean#L355)
- Lean declaration: [one_doublingWrap_classification](../../Erdos249257/RationalSupportCarrySkeleton.lean#L417)
- Lean declaration: [one_oddOrder_doublingWrap_classification](../../Erdos249257/RationalSupportCarrySkeleton.lean#L481)

- incoming **finite_instance_of**: [Z10::order_wrap_finite_validation_table](BROWSER_Z10_2.md#node-c43af9689717ee75). The twelve rows check both directions of the one-wrap classification over 446 coprime starts.
- outgoing **depends_on_open**: [Z10::binary_repetend_wrap_sum_identity](BROWSER_Z10_1.md#node-e6354cb23ec20f7a). The classification unrolls the same carry recurrence whose period sum is the wrap identity.

<a id="node-c43af9689717ee75"></a>
## order_wrap_finite_validation_table

Exact computable validation of the wrap calculus on twelve modulus/order rows covering 446 coprime starting residues: every start has positive wrap count, the one-wrap condition holds exactly when the modulus is Mersenne and the start is a power of two, and the recorded minimum wrap counts for moduli 3, 5, 7, 15, 31 are attained.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [orderWrapValidation446_passes](../../Erdos249257/RationalSupportCarrySkeleton.lean#L2460)
- Lean declaration: [orderWrapValidatedStartCount_eq_446](../../Erdos249257/RationalSupportCarrySkeleton.lean#L2456)
- Lean declaration: [orderWrap_minima_table_passes](../../Erdos249257/RationalSupportCarrySkeleton.lean#L2466)
- Lean declaration: [carryOrbit23_common_multiple_bound_validation66](../../Erdos249257/RationalSupportCarrySkeleton.lean#L2407)

- outgoing **finite_instance_of**: [Z10::one_wrap_cycle_classification_node](BROWSER_Z10_2.md#node-96a828a2b1fff4d1). The twelve rows check both directions of the one-wrap classification over 446 coprime starts.

<a id="node-8f336665f6f7e739"></a>
## orthogonal_petal_bouquet_reduced_modulus

In a finite-core orthogonal petal bouquet the rays are pairwise distinct and disjoint from the exceptional frame, the support is infinite, a foreign ray dividing a dilated argument forces its own petal to divide the undilated argument, and after any finite frame enlargement the gcd of an unselected ray with the frame is exactly its core, so its reduced modulus stays its full petal. A uniform petal rank ceiling R gives support Omega at most Omega(Q) + R.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [gcd_ray_frameStep](../../Erdos249257/SupportSunflowerDichotomy.lean#L183)
- Lean declaration: [ray_div_gcd_frameStep](../../Erdos249257/SupportSunflowerDichotomy.lean#L192)
- Lean declaration: [cardFactors_le_of_mem](../../Erdos249257/SupportSunflowerDichotomy.lean#L219)
- Lean declaration: [petal_dvd_of_ray_dvd](../../Erdos249257/SupportSunflowerDichotomy.lean#L141)
- Lean declaration: [ray_injective](../../Erdos249257/SupportSunflowerDichotomy.lean#L96)
- Lean declaration: [infinite](../../Erdos249257/SupportSunflowerDichotomy.lean#L152)

- incoming **depends_on_open**: [Z10::bouquet_composite_defect_budget](BROWSER_Z10_1.md#node-f9a69fc885c12742). The injection into petal divisors uses ray injectivity and the orthogonality of petals.
- incoming **finite_instance_of**: [Z10::explicit_two_core_bounded_omega_bouquet](BROWSER_Z10_1.md#node-2f0f69ed077ae769). An explicit witness that the bouquet interface is non-vacuous with bounded Omega.
- incoming **depends_on_open**: [Z10::sunflower_selector_to_carry_supply_reduction](BROWSER_Z10_2.md#node-1a9ca9cd2f44ed7f). The positivity clause of the carry supply is discharged by the bouquet's ray membership.
- incoming **depends_on_open**: [Z10::reduced_modulus_progression_incidence](BROWSER_Z10_2.md#node-12708a4ed9fb98fd). The persistent reduced modulus is what makes the progression count usable with the petal as modulus.

<a id="node-b3e2380b66c3f43c"></a>
## positive_rational_gap_lower_bound

A positive difference of two rationals is at least the reciprocal of the product of their reduced denominators.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [positive_rational_difference_lower_bound](../../Erdos249257/PrimitiveRationalGapSupply.lean#L31)

- incoming **depends_on_open**: [Z10::denominator_shell_pressure_from_analytic_tail_bound](BROWSER_Z10_1.md#node-1630e5ef2f14794e). The rational-gap lemma supplies the lower bound clause of the pressure inequality.

<a id="node-da59425e27f6fe8d"></a>
## prime_power_layer_fixtures

Kernel-checked instances of the valuation layer: the third 2-adic layer of the singleton {8} contributes one new divisor at residual argument 1, and the mixed 2^2/3 layer of {12} contributes exactly one.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [supportCoeffInt_prime_power_layer_fixture](../../Erdos249257/SupportSunflowerDichotomy.lean#L718)
- Lean declaration: [mixedPrimePowerLayerTwo_twelve_fixture](../../Erdos249257/MaximalOmegaLayer.lean#L65)

- outgoing **finite_instance_of**: [Z10::exact_prime_power_valuation_layer](BROWSER_Z10_1.md#node-eb34f91e4ca619b3). The singleton fixtures {8} and {12} evaluate the layer at prescribed valuations.

<a id="node-ded6e5d67b309122"></a>
## rational_value_constructs_odd_tail_state

If the value of the support series equals p/(2^c v) with v positive, then the scaled tails from level c onwards form a positive integer state congruent to p*2^n modulo v, with numerator p positive; hence every consequence of the odd tail state applies under a rational-value assumption.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hvalue : erdosSupportSeries 2 A = (p : R) / ((2 ^ c * v : N) : R) - i.e. the support series takes a rational value. For infinite A this is precisely what Erdos #257 asserts is impossible, and nothing in the corpus proves or refutes it."]

- Lean declaration: [exists_shifted_odd_tail_nat_states_of_support_fraction](../../Erdos249257/RationalSupportCarrySkeleton.lean#L671)
- Lean declaration: [exists_shifted_odd_tail_states_of_support_fraction](../../Erdos249257/RationalSupportCarrySkeleton.lean#L599)
- Lean declaration: [numerator_pos_of_support_fraction](../../Erdos249257/RationalSupportCarrySkeleton.lean#L579)
- Lean declaration: [support_fraction_wrapCount_le_tail_block](../../Erdos249257/RationalSupportCarrySkeleton.lean#L770)

- incoming **depends_on_open**: [Z10::odd_tail_state_residue_excess_decomposition](BROWSER_Z10_2.md#node-1dc753b317ffad9e). The tail state only exists under the rational-value hypothesis.
- incoming **depends_on_open**: [Z10::carry_state_unbounded_at_common_multiples](BROWSER_Z10_1.md#node-2195d2fe55e6ff39). The unbounded state is the state constructed from the rational value.
- incoming **transport_of**: [Z11::rational_support_zero_window_lower_bound](BROWSER_Z11_1.md#node-46b1e212e1d31fe2). Both carry the identical antecedent erdosSupportSeries 2 A = p/(2^c*v) and speak of the same doubling state, produced by exists_shifted_odd_tail_nat_states_of_support_fraction (RationalSupportCarrySkeleton.lean:668).
- outgoing **depends_on_open**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). the free hypothesis is rationality of the #257 support series; instantiated at c = supportCoeff A this equivalence shows that is exactly existence of a tempered integer carry orbit, and it records that both sides are equally open. No producer exists.

<a id="node-3845be9631e85dab"></a>
## rational_value_forces_order_wrap_ratio_bound

If the support series equals p/(2^c v) with v odd and greater than one, then either the reciprocal sum over A diverges or it is at least the wrap ratio of p modulo v over the multiplicative order of 2 modulo v; when the numerator is coprime to v this gives the lower bound 1 over that order.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hvalue : erdosSupportSeries 2 A = (p : R) / ((2 ^ c * v : N) : R) - the open rationality hypothesis of Erdos #257 for infinite A"]

- Lean declaration: [support_fraction_oddOrder_wrapRatio_le_reciprocalMass](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1456)
- Lean declaration: [one_div_oddOrder_le_reciprocalMass_of_support_fraction](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1480)
- Lean declaration: [support_fraction_oddOrder_wrapRatio_reciprocalMassDivergesOrAtLeast](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1503)
- Lean declaration: [support_fraction_one_div_oddOrder_reciprocalMassDivergesOrAtLeast](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1519)

- outgoing **specialises**: [Z10::wrap_ratio_lower_bounds_reciprocal_mass](BROWSER_Z10_3.md#node-d2c3c4382da7aea9). The fraction-facing form instantiates the general wrap-ratio bound at the multiplicative order of 2.
- incoming **depends_on_open**: [Z10::finite_fragment_residual_transport](BROWSER_Z10_1.md#node-cc4b29d2ebadd1ad). The certificate's wrapBound clause is the T9 conclusion transported to the residual support.
- incoming **transport_of**: [Z11::sublogarithmic_zero_window_bound](BROWSER_Z11_1.md#node-d8afdc3d1b1800f5). The two nodes convert one and the same open rationality antecedent, through the same odd-denominator tail state, into two different structural consequences for A: a zero-window length bound and a reciprocal-mass lower bound.
- outgoing **depends_on_open**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). the free hypothesis is rationality of the #257 support series; instantiated at c = supportCoeff A this equivalence shows that is exactly existence of a tempered integer carry orbit, and it records that both sides are equally open. No producer exists.

<a id="node-dd2d02eb2e53e47f"></a>
## rationality_iff_tempered_support_carry_orbit

The value of the sum of 1/(2^a - 1) over A is rational if and only if the incidence sequence admits a tempered integer carry orbit; for a displayed fraction p/q the orbit is unique with multiplier q and initial value p.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Open hypotheses: ["neither side is decided: for infinite A, that the left side fails is exactly Erdos #257, and no theorem in the corpus excludes a tempered carry orbit for an arbitrary infinite support"]

- Lean declaration: [erdosSupportSeries_rational_iff_exists_temperedCarry](../../Erdos249257/BooleanMobiusCarry.lean#L384)
- Lean declaration: [support_fraction_iff_exists_temperedCarry](../../Erdos249257/BooleanMobiusCarry.lean#L467)
- Lean declaration: [exists_temperedCarry_of_support_fraction](../../Erdos249257/BooleanMobiusCarry.lean#L395)
- Lean declaration: [support_fraction_of_temperedCarry](../../Erdos249257/BooleanMobiusCarry.lean#L453)

- incoming **specialises**: [Z10::boolean_mobius_carry_certificate_equivalence](BROWSER_Z10_1.md#node-987e0047786a6728). The certificate equivalence is the fixed-fraction carry equivalence with the support variable eliminated by Boolean Mobius inversion.
- incoming **specialises**: [Z10::half_value_iff_canonical_affine_carry_tempered](BROWSER_Z10_2.md#node-6b727b8f4e070ab3). Denominator two with the existential orbit removed by recurrence uniqueness.
- incoming **equivalent_to**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). erdosSupportSeries_two_eq_binaryCoeffSeries (BooleanMobiusCarry.lean:376) identifies the base-2 support series with binaryCoeffSeries (supportCoeff A), so erdosSupportSeries_rational_iff_exists_temperedCarry is binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit at c = supportCoeff A.
- incoming **depends_on_open**: [Z11::rational_support_zero_window_lower_bound](BROWSER_Z11_1.md#node-46b1e212e1d31fe2). the hypothesis erdosSupportSeries 2 A = p/(2^c v) is the left side of this equivalence; for infinite A its failure is exactly Erdos #257, and the equivalence shows the only route to it would be a tempered incidence carry orbit, which nothing constructs.
- incoming **depends_on_open**: [Z11::sublogarithmic_zero_window_bound](BROWSER_Z11_1.md#node-d8afdc3d1b1800f5). same rationality hypothesis; the equivalence identifies it with existence of a tempered incidence carry orbit, undecided for every infinite support in the corpus.
- outgoing **specialises**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). `erdosSupportSeries_rational_iff_exists_temperedCarry` (BooleanMobiusCarry.lean:383) is the c := supportCoeff A instance of `binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit` (GenericTailOrbitRigidity.lean:425), the growth side condition c n <= n discharged by `supportCoeff_le_self`.

<a id="node-d20a79c3f7242c31"></a>
## raw_dyadic_safety_is_predecessor_overshoot

Block dyadic safety at rank k is exactly the unscaled predecessor overshoot inequality p <= 2D - p(2^k - 1); the gcd of D with 2^k - 1 always divides that overshoot, the gcd-scaled form is equivalent to a primitive-quotient comparison, and the gcd-scaled form implies safety.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [blockDyadicSafeAt_iff_rawPredecessorOvershoot](../../Erdos249257/DyadicPrefixCompression.lean#L3405)
- Lean declaration: [gcd_dvd_predecessorOvershoot](../../Erdos249257/DyadicPrefixCompression.lean#L3496)
- Lean declaration: [gcdScaled_predecessorOvershoot_iff_primitiveQuotient](../../Erdos249257/DyadicPrefixCompression.lean#L4409)
- Lean declaration: [blockDyadicSafeAt_of_gcdScaled_predecessorOvershoot](../../Erdos249257/DyadicPrefixCompression.lean#L4422)

- incoming **depends_on_open**: [Z10::half_membership_from_gcd_overshoot_supply](BROWSER_Z10_2.md#node-3425e915369370cb). The supply is the gcd-scaled form of the overshoot inequality that characterises safety.

<a id="node-7ce5d720dc52fe34"></a>
## raw_dyadic_safety_is_strictly_weaker_than_gcd_overshoot

Raw dyadic safety does not imply the gcd-scaled predecessor overshoot: the state 7/15 at rank 2 is safe and satisfies the raw overshoot bound while failing the gcd-scaled one, and an explicit factor-eleven state 39/539 shows the same at rank 5 with first take at rank 9.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Shows only that the gcd-scaled overshoot supply is strictly stronger than raw safety at particular states, so a proof of raw safety cannot be routed through the gcd-scaled criterion. It does not refute either supply, and it does not show these states occur on the actual greedy orbit for 1/2.

- Lean declaration: [rawSafe_but_not_gcdScaled_fixture](../../Erdos249257/DyadicPrefixCompression.lean#L3450)
- Lean declaration: [factorEleven_predecessorOvershoot_not_inductive_fixture](../../Erdos249257/DyadicPrefixCompression.lean#L3472)

- outgoing **barrier_for**: [Z10::half_membership_from_gcd_overshoot_supply](BROWSER_Z10_2.md#node-3425e915369370cb). An explicit state that is raw-safe but fails the gcd-scaled bound shows that lane cannot be obtained from raw safety alone; it does not refute the supply.

<a id="node-4fa295e3d086bcf9"></a>
## raw_versus_reduced_greedy_prefix_coordinates

The raw common-denominator coordinates of the greedy prefix differ from the reduced ones by exactly the gcd reduction factor, and every excess inequality in raw coordinates is equivalent to the corresponding inequality in reduced coordinates; membership in the greedy prefix support at rank a is the take test at that rank.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [halfGreedyPrefixCommonDenominator_eq_reduced_mul_factor](../../Erdos249257/DyadicPrefixCompression.lean#L1910)
- Lean declaration: [halfGreedyRawExcessBound_iff_reduced](../../Erdos249257/DyadicPrefixCompression.lean#L2065)
- Lean declaration: [halfGreedyRawSupportExcessBound_iff](../../Erdos249257/DyadicPrefixCompression.lean#L2107)
- Lean declaration: [mem_halfGreedyPrefixSupport_iff](../../Erdos249257/DyadicPrefixCompression.lean#L2147)


<a id="node-12708a4ed9fb98fd"></a>
## reduced_modulus_progression_incidence

Divisibility by a along the progression My + c occupies at most one residue class modulo the reduced modulus a/gcd(a,M), giving at most Y/(a/gcd(a,M)) + 1 hits in a window of length Y; and if the frame divides one distinguished slot, any later hit is spaced from it by at least gcd(a,M).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [card_filter_dvd_progression_le_reduced](../../Erdos249257/SupportSunflowerDichotomy.lean#L551)
- Lean declaration: [gcd_le_offset_sub_of_dvd_progression](../../Erdos249257/SupportSunflowerDichotomy.lean#L631)
- Lean declaration: [gcd_dvd_offset_sub_of_dvd_progression](../../Erdos249257/SupportSunflowerDichotomy.lean#L612)

- outgoing **depends_on_open**: [Z10::orthogonal_petal_bouquet_reduced_modulus](BROWSER_Z10_2.md#node-8f336665f6f7e739). The persistent reduced modulus is what makes the progression count usable with the petal as modulus.

<a id="node-d7bbf09469c1dee7"></a>
## safe_bracket_plus_numerator_monotone_is_not_inductive

Safe bracketing together with nondecrease of the displayed numerator is not an inductive invariant of the greedy orbit: the state 7/(2*17) takes rank 3, producing 15/(2*119) with numerator increased, yet rank 4 is an unsafe skip with exact excess 1. The same failure survives lcm saturation over the Mersenne numbers through 127.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Refutes only the specific proposed induction (safe bracket plus numerator monotonicity), at specific states. It does not rule out a stronger inductive invariant, does not rule out the raw block margin or gcd overshoot supplies, and says nothing about whether the greedy run for 1/2 actually reaches these states.

- Lean declaration: [safeBracket_and_numeratorMonotone_not_inductive_fixture](../../Erdos249257/DyadicPrefixCompression.lean#L622)
- Lean declaration: [lcmSaturated_safeBracket_not_inductive_fixture](../../Erdos249257/DyadicPrefixCompression.lean#L647)

- outgoing **barrier_for**: [Z10::half_membership_from_actual_block_safety](BROWSER_Z10_2.md#node-6cf216bc1ead238e). The fixture refutes safe bracketing plus numerator monotonicity as an inductive route to the hsafe hypothesis at specific states; it leaves the hypothesis unproved rather than refuted, and says nothing about whether the greedy run for 1/2 reaches those states.
- outgoing **barrier_for**: [Z10::half_membership_from_raw_block_margin_supply](BROWSER_Z10_2.md#node-5d104a681bbe0d26). It kills the obvious induction that would have produced the raw margin witnesses, leaving the supply unproved rather than refuted.

<a id="node-c3b0087aaae4cbee"></a>
## safety_margin_iff_reciprocal_floor_not_mersenne

For a first take after a gap, the predecessor safety margin holds if and only if the reciprocal floor floor(2D/p) is not the Mersenne number 2^(b-1) - 1; the same criterion holds in raw and in reduced taken-block coordinates.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [firstBlockTake_margin_iff_reciprocalFloor_ne_mersenne](../../Erdos249257/DyadicPrefixCompression.lean#L544)
- Lean declaration: [takenBlock_rawMargin_iff_reciprocalFloor_ne_mersenne](../../Erdos249257/DyadicPrefixCompression.lean#L579)
- Lean declaration: [takenBlock_rawMargin_iff_reducedReciprocalFloor_ne_mersenne](../../Erdos249257/DyadicPrefixCompression.lean#L599)

- outgoing **specialises**: [Z10::block_take_and_safety_predicates_are_gcd_invariant](BROWSER_Z10_1.md#node-f409427eedd8d532). The reciprocal-floor criterion is the margin condition of the invariance theorems made explicit.

<a id="node-956b8639c5ba1ed3"></a>
## squarefree_incidence_is_two_pow_omega_minus_one

A nonzero n has exactly 2^omega(n) squarefree divisors, so the divisor incidence of the support of squarefree integers at least two is 2^omega(n) - 1; this is odd at every n >= 2 and never zero there.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [card_squarefreeDivisors](../../ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L94)
- Lean declaration: [squarefreeIncidence_eq](../../ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L111)
- Lean declaration: [odd_squarefreeIncidence](../../ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L140)
- Lean declaration: [one_le_squarefreeIncidence](../../ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L157)

- incoming **depends_on_open**: [Z10::no_block_certificate_at_squarefree_support](BROWSER_Z10_2.md#node-8a6ef15977d14203). Both the parity and the density halves are read off the exact incidence 2^omega(n) - 1.

<a id="node-369dbe6f906c9180"></a>
## sunflower_conditional_irrationality

If a support satisfies the forced-slot tail selector - for every K > 0 there is an N with 2^K dividing the carried first block and binary incidence tail at N+K at most 16 - then the sum of 1/(2^a - 1) over that support is irrational. In particular this holds for any orthogonal petal bouquet satisfying the selector.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hselection : SunflowerForcedSlotTailSelection A, i.e. for all K > 0 there exists N with 2^K dividing the sum over r in Icc 1 K of supportCoeff A (N+r) * 2^(K-r), and binaryCoeffTail (supportCoeff A) (N+K) <= 16. No declaration in the corpus proves this for any infinite support, and the file names it as the remaining analytic obligation.", "hsupply : SunflowerForcedCarrySupply A, the same obligation in its carry-supply form"]

- Lean declaration: [irrational_erdosSupportSeries_of_sunflower_forcedCarry_supply](../../Erdos249257/SupportSunflowerDichotomy.lean#L381)
- Lean declaration: [irrational_erdosSupportSeries_of_orthogonalPetalBouquet](../../Erdos249257/SupportSunflowerDichotomy.lean#L540)

- outgoing **depends_on_open**: [Z10::sunflower_selector_to_carry_supply_reduction](BROWSER_Z10_2.md#node-1a9ca9cd2f44ed7f). The headline is the composite of the selector reduction with the carry-aware engine.
- incoming **barrier_for**: [Z10::no_block_certificate_at_squarefree_support](BROWSER_Z10_2.md#node-8a6ef15977d14203). The refuted hypothesis is literally SunflowerForcedCarrySupply at b = 2 instantiated at the squarefree support, so that lane is closed at that one support and nowhere else.
- outgoing **transport_of**: [Z01::carry_aware_certificate_engine](BROWSER_Z01_1.md#node-85bdec04dff8f727). forcedSlotCarrySelection_of_tailSelection and sunflowerForcedCarrySupply_of_forcedSlotCarrySelection restate the carry-aware block-certificate supply of irrational_erdosSupportSeries_of_weighted_coeff_carry_certificates as a forced-slot selector on an orthogonal petal bouquet; the obligation is the same certificate supply in support coordinates.
- outgoing **depends_on_open**: [Z11::support_coefficient_subpower_envelope](BROWSER_Z11_1.md#node-c4e55b27c24c8597). the selector needs binaryCoeffTail (supportCoeff A) (N+K) <= 16, a CONSTANT bound. The nearest existing control is this uniform envelope T(M) <= 2*k^(2^k)*(M+1)^(1/k), which is unbounded in M for every k, so it cannot produce the selector; nothing else in the corpus bounds the incidence tail by a constant on any infinite support.

<a id="node-1a9ca9cd2f44ed7f"></a>
## sunflower_selector_to_carry_supply_reduction

A uniform real bound of 16 on the binary incidence tail after a divisibility-certified slot pays every finite middle-window budget, and a forced-slot carry selector composes unconditionally into the carry-aware certificate supply once the support has one positive member. For an orthogonal petal bouquet the positivity clause is automatic.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [forcedSlotCarrySelection_of_tailSelection](../../Erdos249257/SupportSunflowerDichotomy.lean#L415)
- Lean declaration: [sunflowerForcedCarrySupply_of_forcedSlotCarrySelection](../../Erdos249257/SupportSunflowerDichotomy.lean#L483)
- Lean declaration: [sunflowerForcedCarrySupply_of_orthogonalPetalBouquet](../../Erdos249257/SupportSunflowerDichotomy.lean#L531)

- incoming **depends_on_open**: [Z10::sunflower_conditional_irrationality](BROWSER_Z10_2.md#node-369dbe6f906c9180). The headline is the composite of the selector reduction with the carry-aware engine.
- outgoing **depends_on_open**: [Z10::orthogonal_petal_bouquet_reduced_modulus](BROWSER_Z10_2.md#node-8f336665f6f7e739). The positivity clause of the carry supply is discharged by the bouquet's ray membership.

<a id="node-a4d7972fa4b13a06"></a>
## support23_period_six_carry_fixture

The support {2,3} has value 10/21 and its denominator-21 carry orbit is exactly the purely period-six cycle 10,20,19,17,13,26; the orbit is tempered, its differences are divisible by 21, its carry quotient recovers the incidence coefficient, and the Mobius transform of that quotient recovers the set {2,3}.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [erdosSupportSeries_support23_eq_ten_div_twenty_one](../../Erdos249257/BooleanMobiusCarry.lean#L1055)
- Lean declaration: [carryOrbit23_isTempered](../../Erdos249257/BooleanMobiusCarry.lean#L1104)
- Lean declaration: [mobius_carryOrbit23_recovers_support](../../Erdos249257/BooleanMobiusCarry.lean#L1141)

- outgoing **finite_instance_of**: [Z10::boolean_mobius_carry_certificate_equivalence](BROWSER_Z10_1.md#node-987e0047786a6728). The {2,3} six-cycle instantiates every clause of the carry certificate at q = 21.
- outgoing **finite_instance_of**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). the exhibited period-six orbit 10,20,19,17,13,26 with all differences divisible by 21 is a concrete tempered integer carry orbit with multiplier v=21 for c = supportCoeff {2,3}, realising the right-hand side of the equivalence at the rational value 10/21.
- outgoing **finite_instance_of**: [Z01::finite_period_noncollapse](BROWSER_Z01_1.md#node-ed84a74576eddd3a). the fixture records reduced denominator 21 for the finite support {2,3} with carry orbit of exact period 6 = lcm{2,3}: the multiplicative order of 2 modulo the reduced denominator equals the lcm of the exponent set, at one finite F.

<a id="node-c29d8d1929d4f3b7"></a>
## unsafe_skip_forces_long_forced_take_block

The Mersenne mass through twice the current depth is already below the current dyadic cap, and through 2m+2 further ranks below the two-channel cap; hence a dyadically unsafe skip forces every one of the next n+2 ranks to be taken, and a cap-violating skip forces the next 2n+4 ranks to be taken.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [greedyHalf_unsafeSkip_forces_doubleBlock](../../Erdos249257/DyadicPrefixCompression.lean#L1381)
- Lean declaration: [greedyHalf_capViolationSkip_forces_threeDepthBlock](../../Erdos249257/DyadicPrefixCompression.lean#L1407)
- Lean declaration: [mersennePrefix_doubleDepth_lt_halfDyadicCap](../../Erdos249257/DyadicPrefixCompression.lean#L1091)
- Lean declaration: [mersennePrefix_threeDepth_add_two_lt_halfTwoChannelCap](../../Erdos249257/DyadicPrefixCompression.lean#L1225)

- incoming **depends_on_open**: [Z10::half_membership_from_take_run_excess_bounds](BROWSER_Z10_2.md#node-835c9dff117dcdd9). The run compression is legitimate only because a cap-violating skip forces the displayed take run.
- incoming **barrier_for**: [Z10::forced_take_block_depth_is_sharp](BROWSER_Z10_1.md#node-050b30a047d1f9cb). It shows the forced block cannot be lengthened by the same tail-mass comparison.
- incoming **depends_on_open**: [Z12::channel_cap_skip_transport](BROWSER_Z12_1.md#node-3b04a5f99d781f94). the nearest law bearing on the skip-branch cap: it converts a cap-violating skip into a forced take run of 2n+4 ranks, but it consumes the cap violation rather than producing the cap, and forced_take_block_depth_is_sharp shows the extracted block cannot be lengthened; so no cap hypothesis is produced.

