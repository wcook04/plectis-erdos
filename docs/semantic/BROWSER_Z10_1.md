# Z10_1: Support-coefficient calculus for #257: divisor incidence, dilation, sunflowers and the squarefree barrier

[All problems and zones](BROWSER.md)

<a id="node-056b46367312b353"></a>
## adjoining_one_is_value_free_and_repairs_the_parity

Adjoining 1 to the squarefree support adds the rational 1/(b - 1), so irrationality of the squarefree-support value holds IF AND ONLY IF irrationality of the shifted-support value holds; the shifted incidence is 2^omega(n), which is even at every n >= 2, and for every block length K there is a position at which the full digitwise opening condition of the base-2 engine holds. The parity obstruction therefore does not survive the shift. The headline is an iff between two statements NEITHER of which is decided anywhere in the corpus, so it transports an open question rather than settling one; the decided content is the coefficient identity and the Chinese-remainder block existence.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["Both sides of irrational_erdosSupportSeries_squarefreeSupport_iff_shifted are open: Irrational (erdosSupportSeries b squarefreeSupport) is undecided (the module docstring says so explicitly), and Irrational (erdosSupportSeries b squarefreeShiftedSupport) is undecided for the same reason. The iff is proved, but it establishes nothing about either value."]

- Lean declaration: [irrational_erdosSupportSeries_squarefreeSupport_iff_shifted](../../ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L335)
- Lean declaration: [supportCoeff_squarefreeShiftedSupport](../../ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L314)
- Lean declaration: [exists_digitwise_block_squarefreeShiftedSupport](../../ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L485)

- outgoing **repair_of**: [Z10::no_block_certificate_at_squarefree_support](BROWSER_Z10_2.md#node-8a6ef15977d14203). Adjoining 1 keeps the irrationality question and restores satisfiable digitwise opening blocks of every length, so the barrier is a statement about the normalisation.
- outgoing **depends_on_open**: [Z10::arbitrarily_long_prescribed_omega_blocks](BROWSER_Z10_1.md#node-958b912def239eb0). The CRT omega-block construction is what makes the shifted opening condition satisfiable.

<a id="node-958b912def239eb0"></a>
## arbitrarily_long_prescribed_omega_blocks

For every K there is a positive N with omega(N + r) >= r for all 1 <= r <= K, by reserving disjoint blocks of r fresh primes for each shift r and applying the Chinese remainder theorem.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [exists_omega_ge_block](../../ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L441)

- incoming **depends_on_open**: [Z10::adjoining_one_is_value_free_and_repairs_the_parity](BROWSER_Z10_1.md#node-056b46367312b353). The CRT omega-block construction is what makes the shifted opening condition satisfiable.
- incoming **depends_on_open**: [Z01::erdos249_certificate_supply_restatement](BROWSER_Z01_1.md#node-fe5e91cb1960ad1c). the divisibility half of the block certificate is producible: this construction gives, for every K, an N with omega(N+r) >= r for r <= K, which with the first-block hinge forces 2^r | phi(N+r). The remaining half - a middle-window budget C with q*(C + (N+L+2)) < 2^L - has no producer anywhere, so the supply stays open.

<a id="node-e6354cb23ec20f7a"></a>
## binary_repetend_wrap_sum_identity

Over one closed doubling cycle the least positive residues sum to the odd modulus times the number of wraps; equivalently, the sum of residues of p*2^j over a full period is v times the wrap count.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [sum_eq_modulus_mul_wrapCount_of_closed_cycle](../../Erdos249257/RationalSupportCarrySkeleton.lean#L158)
- Lean declaration: [sum_doublingResidue_eq_mul_wrapCount](../../Erdos249257/RationalSupportCarrySkeleton.lean#L173)

- incoming **depends_on_open**: [Z10::one_wrap_cycle_classification_node](BROWSER_Z10_2.md#node-96a828a2b1fff4d1). The classification unrolls the same carry recurrence whose period sum is the wrap identity.

<a id="node-f409427eedd8d532"></a>
## block_take_and_safety_predicates_are_gcd_invariant

The block take, dyadic safety and first-take-after predicates are invariant under multiplying numerator and denominator by a common positive factor, so they may be evaluated in raw uncancelled coordinates; all skips between a take and the next take are safe exactly when the block is adjacent or the last margin inequality holds.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [blockTakeAt_commonFactor_iff](../../Erdos249257/DyadicPrefixCompression.lean#L384)
- Lean declaration: [blockDyadicSafeAt_commonFactor_iff](../../Erdos249257/DyadicPrefixCompression.lean#L405)
- Lean declaration: [firstBlockTakeAfter_commonFactor_iff](../../Erdos249257/DyadicPrefixCompression.lean#L427)
- Lean declaration: [takenBlock_all_next_skips_safe_iff_raw_margin](../../Erdos249257/DyadicPrefixCompression.lean#L476)

- incoming **depends_on_open**: [Z10::half_membership_from_raw_block_margin_supply](BROWSER_Z10_2.md#node-5d104a681bbe0d26). Scale invariance is what lets the witness be stated in raw uncancelled coordinates.
- incoming **depends_on_open**: [Z10::exact_reduced_take_step_cancellation](BROWSER_Z10_1.md#node-a4c985e2d684310b). The cancellation factor is exactly the common factor the invariance theorems allow to be ignored.
- incoming **specialises**: [Z10::safety_margin_iff_reciprocal_floor_not_mersenne](BROWSER_Z10_2.md#node-c3b0087aaae4cbee). The reciprocal-floor criterion is the margin condition of the invariance theorems made explicit.

<a id="node-bac1cfc90124cb4f"></a>
## boolean_collision_surplus

If F is a finite subset of A whose members all divide n, then the incidence at n is at least the cardinality of F, and the odd tail excess just before n is at least the collision surplus ceil((|F| - 1)/2). The bound holds in both the unshifted and the shifted normalisation.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hstate : IsOddSupportTailState A p v u (or its shifted form) - available only under the open rationality hypothesis"]

- Lean declaration: [booleanCollisionSurplus_le_oddTailExcess](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1705)
- Lean declaration: [booleanCollisionSurplus_le_shiftedOddTailExcess](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1920)
- Lean declaration: [card_le_supportCoeff_of_forced_divisors](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1618)
- Lean declaration: [booleanCollisionSurplus_le_of_supportCoeff_carry](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1639)

- incoming **depends_on_open**: [Z10::common_multiple_collision_strengthens_wrap_bound](BROWSER_Z10_1.md#node-260e0b210929ac12). The periodic spike used in the improved bound is the collision surplus at multiples of the finite subset's lcm.

<a id="node-987e0047786a6728"></a>
## boolean_mobius_carry_certificate_equivalence

Normalised nonempty supports with value p/q correspond, at the level of existence, to quotient-only Boolean Mobius carry certificates: positive integer orbits inside the square-root strip whose successive differences are divisible by q and whose carry quotient has Boolean Mobius transform. The support is reconstructed from the certificate rather than assumed.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["existence of a Boolean Mobius carry certificate for a given p/q is not decided anywhere in the corpus; for infinite supports its non-existence is exactly Erdos #257"]

- Lean declaration: [exists_normalized_support_fraction_iff_exists_booleanMobiusCarry](../../Erdos249257/BooleanMobiusCarry.lean#L949)
- Lean declaration: [exists_booleanMobiusCarry_of_support_fraction](../../Erdos249257/BooleanMobiusCarry.lean#L836)
- Lean declaration: [support_fraction_of_booleanMobiusCarry](../../Erdos249257/BooleanMobiusCarry.lean#L859)
- Lean declaration: [BooleanMobiusCarryCertificate.reconstructsSupport](../../Erdos249257/BooleanMobiusCarry.lean#L895)

- outgoing **specialises**: [Z10::rationality_iff_tempered_support_carry_orbit](BROWSER_Z10_2.md#node-dd2d02eb2e53e47f). The certificate equivalence is the fixed-fraction carry equivalence with the support variable eliminated by Boolean Mobius inversion.
- outgoing **depends_on_open**: [Z10::divisor_pair_square_root_envelope](BROWSER_Z10_1.md#node-1d5f5df7a851affd). The certificate's sqrtBound field is exactly the square-root strip; without it the tempered limit is not recoverable.
- incoming **finite_instance_of**: [Z10::support23_period_six_carry_fixture](BROWSER_Z10_2.md#node-a4d7972fa4b13a06). The {2,3} six-cycle instantiates every clause of the carry certificate at q = 21.

<a id="node-5cfdf4fb93485caf"></a>
## boolean_mobius_transform_characterises_support_coefficients

An integer-valued arithmetic function is the divisor-incidence coefficient of some support if and only if its Mobius transform takes only the values 0 and 1 on positive integers; the support is then recovered as the set where that transform equals 1.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [eq_supportCoeffAF_booleanMobiusSupport_of_boolean](../../Erdos249257/BooleanMobiusCarry.lean#L181)
- Lean declaration: [moebius_mul_eq_positiveSupportBitAF_of_boolean](../../Erdos249257/BooleanMobiusCarry.lean#L149)

- outgoing **reformulates**: [Z10::mobius_inversion_of_support_coefficient](BROWSER_Z10_2.md#node-34ed548cbedf7039). The converse direction is the same Dirichlet inversion read as a characterisation of which arithmetic functions are support incidences.

<a id="node-c6b1c98db3e57585"></a>
## bounded_omega_pullback_annihilation

If every element of A has at most K prime factors counted with multiplicity, then pulling A back by any list of more than K primes gives identically zero incidence, so the corresponding iterated dilation difference vanishes at every argument coprime to the product.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [supportCoeff_iteratedSupportPullback_eq_zero_of_cardFactors_le](../../Erdos249257/SupportDilationDifferences.lean#L225)
- Lean declaration: [iteratedDilationDifference_eq_zero_of_cardFactors_le](../../Erdos249257/SupportDilationDifferences.lean#L250)

- incoming **finite_instance_of**: [Z10::dilation_layer_fixtures](BROWSER_Z10_1.md#node-1dc0de6f9549558a). Two coprime prime differences annihilate {2,3} exactly because Omega = 1 there.
- outgoing **depends_on_open**: [Z10::dilation_difference_is_pullback_coefficient](BROWSER_Z10_1.md#node-f64d37d580e12dd4). The annihilation is read off the pullback identity; without it the difference has no support-side meaning.

<a id="node-f9a69fc885c12742"></a>
## bouquet_composite_defect_budget

In an orthogonal petal bouquet every composite dilation defect at a ray is either an exceptional finite-frame element or comes from a unique foreign ray whose petal already divides the undilated argument; hence the defect is at most the exceptional cardinality plus the incidence of the petal range at that argument.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [compositeDilationDefect_le_exceptional_add_petalCoeff](../../Erdos249257/CompositeDilationDefect.lean#L151)
- Lean declaration: [mem_compositeDilationDefect_bouquet_imp_exceptional_or_petal_dvd](../../Erdos249257/CompositeDilationDefect.lean#L133)

- outgoing **specialises**: [Z10::composite_dilation_defect_identity](BROWSER_Z10_1.md#node-4596626eab0c52aa). The bouquet budget bounds the defect term that the composite identity isolates.
- outgoing **depends_on_open**: [Z10::orthogonal_petal_bouquet_reduced_modulus](BROWSER_Z10_2.md#node-8f336665f6f7e739). The injection into petal divisors uses ray injectivity and the orthogonality of petals.

<a id="node-fc322bda4fc679b7"></a>
## carry_block_forces_base_divides_last_coefficient

For any coefficient sequence, if the base-b carried aggregate of the first block of length K >= 1 is divisible by b^K, then b divides the coefficient at the last position of that block, because every other term carries a positive power of b.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [dvd_last_of_carry_block](../../ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L188)

- incoming **depends_on_open**: [Z10::no_block_certificate_at_squarefree_support](BROWSER_Z10_2.md#node-8a6ef15977d14203). The parity half of the barrier is exactly the last-coefficient divisibility lemma.

<a id="node-2195d2fe55e6ff39"></a>
## carry_state_unbounded_at_common_multiples

For an infinite support with a rational value p/(2^c v), the tail state is unbounded: at any common multiple L of a finite subset F of A the state satisfies 1 + v|F| <= 2 u(L - c - 1), and since F may be taken arbitrarily large the state exceeds every bound.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hvalue : erdosSupportSeries 2 A = (p : R) / ((2 ^ c * v : N) : R) - the open rationality hypothesis for an infinite support"]

- Lean declaration: [exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction](../../Erdos249257/RationalSupportCarrySkeleton.lean#L2383)
- Lean declaration: [shifted_state_unbounded_of_infinite_support](../../Erdos249257/RationalSupportCarrySkeleton.lean#L2327)
- Lean declaration: [exists_shifted_odd_tail_nat_state_with_common_multiple_bound_of_support_fraction](../../Erdos249257/RationalSupportCarrySkeleton.lean#L2302)

- outgoing **depends_on_open**: [Z10::rational_value_constructs_odd_tail_state](BROWSER_Z10_2.md#node-ded6e5d67b309122). The unbounded state is the state constructed from the rational value.
- outgoing **depends_on_open**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). the free hypothesis is rationality of the #257 support series; instantiated at c = supportCoeff A this equivalence shows that is exactly existence of a tempered integer carry orbit, and it records that both sides are equally open. No producer exists.

<a id="node-b2d5cd6a8b764d3b"></a>
## cesaro_tail_mean_equals_reciprocal_mass

If the reciprocal sum over A converges, the Cesaro mean of the binary incidence tails converges to that reciprocal mass, as does the mean of the partial sums of the incidence coefficients; the same holds after any finite shift.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tendsto_supportCoeff_mean_reciprocalMass](../../Erdos249257/RationalSupportCarrySkeleton.lean#L948)
- Lean declaration: [tendsto_binaryCoeffTail_supportCoeff_mean_reciprocalMass](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1039)
- Lean declaration: [tendsto_shifted_binaryCoeffTail_supportCoeff_mean_reciprocalMass](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1419)

- incoming **depends_on_open**: [Z10::wrap_ratio_lower_bounds_reciprocal_mass](BROWSER_Z10_3.md#node-d2c3c4382da7aea9). The excess-mean identity is the Cesaro limit of the tails minus the Cesaro limit of the normalised residues.

<a id="node-260e0b210929ac12"></a>
## common_multiple_collision_strengthens_wrap_bound

At a common multiple L of a finite subset F of A the periodic excess spike improves the wrap-ratio bound: the reciprocal mass is at least the wrap ratio plus the collision surplus of F divided by L, or the reciprocal sum diverges.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hstate : IsOddSupportTailState A p v u (or IsShiftedOddSupportTailState) - available only under the open rationality hypothesis"]

- Lean declaration: [booleanCollision_wrap_bound_of_common_multiple](../../Erdos249257/RationalSupportCarrySkeleton.lean#L2044)
- Lean declaration: [shiftedBooleanCollision_wrap_bound_of_common_multiple](../../Erdos249257/RationalSupportCarrySkeleton.lean#L1968)
- Lean declaration: [wrapRatio_add_collisionSurplus_div_le_reciprocalMass](../../Erdos249257/RationalSupportCarrySkeleton.lean#L2019)

- outgoing **depends_on_open**: [Z10::boolean_collision_surplus](BROWSER_Z10_1.md#node-bac1cfc90124cb4f). The periodic spike used in the improved bound is the collision surplus at multiples of the finite subset's lcm.
- outgoing **generalises**: [Z10::wrap_ratio_lower_bounds_reciprocal_mass](BROWSER_Z10_3.md#node-d2c3c4382da7aea9). It adds a collision term to the same wrap-ratio inequality.
- incoming **specialises**: [Z10::dyadic_denominator_forces_reciprocal_mass_above_one](BROWSER_Z10_1.md#node-3f4c27e9053d57d5). The dyadic case v = 1 with two distinct members gives excess spikes of size at least two.

<a id="node-8d0527115497ed1d"></a>
## composite_defect_fixtures

The smallest composite-defect witness: dilating by 6 on the support {2,6} creates both the distinguished member 6 and the lower-rank divisor 2, so the defect is exactly 1 and the exact identity records the extra term.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [compositeDilationDefect_two_six_fixture](../../Erdos249257/CompositeDilationDefect.lean#L218)
- Lean declaration: [supportCoeff_mul_eq_add_defect_two_six_fixture](../../Erdos249257/CompositeDilationDefect.lean#L224)

- outgoing **finite_instance_of**: [Z10::composite_dilation_defect_identity](BROWSER_Z10_1.md#node-4596626eab0c52aa). The {2,6} witness realises a nonzero defect term.

<a id="node-4596626eab0c52aa"></a>
## composite_dilation_defect_identity

For a in A and x positive, the incidence of A at a*x equals its incidence at x, plus one when a does not already divide x, plus the composite dilation defect - the number of members of A dividing a*x that neither divide x nor equal a. On a support consisting only of primes the defect vanishes, recovering the prime-dilation formula.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [supportCoeff_mul_eq_add_defect](../../Erdos249257/CompositeDilationDefect.lean#L30)
- Lean declaration: [compositeDilationDefect_eq_zero_of_prime_support](../../Erdos249257/CompositeDilationDefect.lean#L103)
- Lean declaration: [supportCoeff_mul_prime_support](../../Erdos249257/CompositeDilationDefect.lean#L119)

- incoming **specialises**: [Z10::bouquet_composite_defect_budget](BROWSER_Z10_1.md#node-f9a69fc885c12742). The bouquet budget bounds the defect term that the composite identity isolates.
- incoming **finite_instance_of**: [Z10::composite_defect_fixtures](BROWSER_Z10_1.md#node-8d0527115497ed1d). The {2,6} witness realises a nonzero defect term.

<a id="node-1630e5ef2f14794e"></a>
## denominator_shell_pressure_from_analytic_tail_bound

If a positive residual is at least 1/(qD) while its first dyadic shell and geometric far tail contribute at most K/2^X + 2/2^(2X), then 2^X <= qD(K+1); the same elementary pressure gives 2^m <= 4qD from a bound of 4/2^m. When the residual is a positive difference of two rationals the lower bound is supplied by the product of the actual reduced denominators.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hupper : beta <= (K : R) / 2 ^ X + 2 / 2 ^ (2 * X) - a denominator-uniform analytic shell-plus-far-tail upper bound on the actual residual. The module docstring itself records that deriving denominator-uniform pressure from the analytic estimates remains the new global bottleneck; nothing in the corpus supplies this hypothesis.", "hupper : beta <= 4 / 2 ^ m in the next-support variant"]

- Lean declaration: [prefixDenominator_shell_power_bound](../../Erdos249257/PrimitiveSupportBridge.lean#L213)
- Lean declaration: [nextSupport_power_bound](../../Erdos249257/PrimitiveSupportBridge.lean#L242)
- Lean declaration: [prefixDenominator_shell_power_bound_of_rational_difference](../../Erdos249257/PrimitiveRationalGapSupply.lean#L46)
- Lean declaration: [nextSupport_power_bound_of_rational_difference](../../Erdos249257/PrimitiveRationalGapSupply.lean#L61)

- outgoing **depends_on_open**: [Z10::positive_rational_gap_lower_bound](BROWSER_Z10_2.md#node-b3e2380b66c3f43c). The rational-gap lemma supplies the lower bound clause of the pressure inequality.
- outgoing **depends_on_open**: [Z10::first_shell_divisor_shadow_is_primitive_bit](BROWSER_Z10_1.md#node-d1780bc7c4537075). The residual whose size is bounded is the cross-carry residual isolated on the first shell.
- outgoing **depends_on_open**: [Z11::subpower_tail_envelope_from_coefficient_bound](BROWSER_Z11_1.md#node-74c62382f3340c5b). the missing hypothesis is a denominator-uniform shell-plus-far-tail bound beta <= K/2^X + 2/2^(2X); this is the corpus's only unconditional binary-tail envelope and it is neither denominator-uniform nor of that shape, which is what the module docstring calls the global bottleneck.

<a id="node-f64d37d580e12dd4"></a>
## dilation_difference_is_pullback_coefficient

For a prime p and n coprime to p, the incidence of A at pn equals its incidence at n plus the incidence at n of the pullback {a : pa in A}; iterating along a pairwise-coprime list of primes gives the incidence of the product pullback at arguments coprime to the product.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [supportCoeff_mul_prime](../../Erdos249257/SupportDilationDifferences.lean#L113)
- Lean declaration: [dilationDifference_supportCoeffInt](../../Erdos249257/SupportDilationDifferences.lean#L131)
- Lean declaration: [iteratedDilationDifference_supportCoeffInt](../../Erdos249257/SupportDilationDifferences.lean#L162)

- incoming **depends_on_open**: [Z10::bounded_omega_pullback_annihilation](BROWSER_Z10_1.md#node-c6b1c98db3e57585). The annihilation is read off the pullback identity; without it the difference has no support-side meaning.
- incoming **generalises**: [Z10::exact_prime_power_valuation_layer](BROWSER_Z10_1.md#node-eb34f91e4ca619b3). The valuation layer repairs the repeated-prime case that the distinct-prime dilation identity cannot reach.

<a id="node-1dc0de6f9549558a"></a>
## dilation_layer_fixtures

Kernel-checked instances of the dilation calculus: one difference on {2,3} extracts the multiples of 2, and two coprime prime differences annihilate {2,3} because its elements have Omega = 1.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [dilationDifference_supportTwoThree_fixture](../../Erdos249257/SupportDilationDifferences.lean#L269)
- Lean declaration: [iteratedDilationDifference_supportTwoThree_fixture](../../Erdos249257/SupportDilationDifferences.lean#L279)

- outgoing **finite_instance_of**: [Z10::bounded_omega_pullback_annihilation](BROWSER_Z10_1.md#node-c6b1c98db3e57585). Two coprime prime differences annihilate {2,3} exactly because Omega = 1 there.

<a id="node-1d5f5df7a851affd"></a>
## divisor_pair_square_root_envelope

The number of divisors of n is at most twice the integer square root of n; consequently every support incidence coefficient is at most 2*sqrt(n) and the scaled binary tail of the incidence sequence is at most 2*sqrt(N) + 4.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [card_divisors_le_two_mul_sqrt](../../Erdos249257/BooleanMobiusCarry.lean#L209)
- Lean declaration: [supportCoeff_le_two_mul_sqrt](../../Erdos249257/BooleanMobiusCarry.lean#L271)
- Lean declaration: [binaryCoeffTail_supportCoeff_le_two_sqrt_add_four](../../Erdos249257/BooleanMobiusCarry.lean#L290)

- incoming **depends_on_open**: [Z10::boolean_mobius_carry_certificate_equivalence](BROWSER_Z10_1.md#node-987e0047786a6728). The certificate's sqrtBound field is exactly the square-root strip; without it the tempered limit is not recoverable.
- incoming **reformulates**: [Z11::support_coefficient_subpower_envelope](BROWSER_Z11_1.md#node-c4e55b27c24c8597). supportCoeff_le_two_mul_sqrt and supportCoeff_le_divisorSubpowerConst_mul_rpow are the same envelope f_A <= tau at two exponents (1/2 and 1/k), and both are pushed to the binary tail by the same geometric majorant.
- incoming **depends_on_open**: [Z16::profiled_gap_advance](BROWSER_Z16_1.md#node-98206c2f8a389f38). the only unconditional control available for the NextArithmetic cell; it bounds each next-row coefficient by 2*sqrt(n) but says nothing about gap width, and gap_width_recurrence shows the child gap doubles each row while halfStripBound grows like 2*sqrt(N), so childHiStrip cannot be produced from it.

<a id="node-fcb893830eee6309"></a>
## doubling_residue_wrap_coordinates

The least residue of p*2^n modulo v satisfies the exact carry identity 2 r(n) = v w(n) + r(n+1) with wrap digit w(n) in {0,1}, is periodic along any doubling period, and shifts by absorbing 2^N into the starting numerator.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [doublingResidue_carry](../../Erdos249257/RationalSupportCarrySkeleton.lean#L94)


<a id="node-3f4c27e9053d57d5"></a>
## dyadic_denominator_forces_reciprocal_mass_above_one

If an infinite support has a dyadic rational value p/2^c, then either its reciprocal sum diverges or that sum exceeds 1; the mechanism is that any two distinct positive members force the excess to be at least 2 on a periodic set of positions.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hvalue : erdosSupportSeries 2 A = (p : R) / ((2 ^ c : N) : R) - the open hypothesis that an infinite support has a dyadic rational value"]

- Lean declaration: [dyadic_support_fraction_reciprocalMass_diverges_or_gt_one](../../Erdos249257/RationalSupportCarrySkeleton.lean#L2210)
- Lean declaration: [one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem](../../Erdos249257/RationalSupportCarrySkeleton.lean#L2124)

- outgoing **specialises**: [Z10::common_multiple_collision_strengthens_wrap_bound](BROWSER_Z10_1.md#node-260e0b210929ac12). The dyadic case v = 1 with two distinct members gives excess spikes of size at least two.
- outgoing **depends_on_open**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). the free hypothesis is rationality of the #257 support series; instantiated at c = supportCoeff A this equivalence shows that is exactly existence of a tempered integer carry orbit, and it records that both sides are equally open. No producer exists.

<a id="node-e66868b5312099b9"></a>
## dyadic_prefix_fixtures

Exact fixtures for the compression: the fragment {2,3} has reduced sum 10/21, order 6, wrap count 2 and residual 1/42; the fragment {2,3,6,7,14} has reduced sum 172021/344043, order 42 and wrap count 13.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [two_three_dyadicPrefix_fixture](../../Erdos249257/DyadicPrefixCompression.lean#L1679)
- Lean declaration: [five_term_dyadicPrefix_fixture](../../Erdos249257/DyadicPrefixCompression.lean#L1696)

- outgoing **finite_instance_of**: [Z10::finite_fragment_residual_transport](BROWSER_Z10_1.md#node-cc4b29d2ebadd1ad). Exact reduced sums, orders and wrap counts for the two fragments.
- outgoing **finite_instance_of**: [Z01::finite_period_noncollapse](BROWSER_Z01_1.md#node-ed84a74576eddd3a). both fixtures instantiate the sharp order statement: order 6 = lcm{2,3} at reduced denominator 21, and order 42 = lcm{2,3,6,7,14} at reduced denominator 344043.
- outgoing **finite_instance_of**: [Z01::rational_denominator_bridge](BROWSER_Z01_2.md#node-cb8ae7db72537740). the reduced sums 10/21 and 172021/344043 are Rat denominators of finite Mersenne partial sums, exhibiting in two cases what the bridge asserts in general (odd, coprime to 2, dividing 2^lcm - 1).

<a id="node-f72c02d402375a21"></a>
## dyadic_prefix_residual_denominator_sandwich

Subtracting a fraction r/D with D odd from a dyadic rational p/2^c leaves a numerator coprime to D, so the reduced denominator of the residual is divisible by D and divides 2^c D: the odd part of the prefix denominator cannot cancel.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [dyadicResidualIntNumerator_coprime_oddDenominator](../../Erdos249257/DyadicPrefixCompression.lean#L35)
- Lean declaration: [dyadicResidualInt_denominator_sandwich](../../Erdos249257/DyadicPrefixCompression.lean#L57)
- Lean declaration: [dyadicResidual_denominator_sandwich](../../Erdos249257/DyadicPrefixCompression.lean#L118)

- incoming **depends_on_open**: [Z10::finite_fragment_residual_transport](BROWSER_Z10_1.md#node-cc4b29d2ebadd1ad). The certificate's denominator clause is the sandwich applied to the actual reduced prefix denominator.

<a id="node-eb34f91e4ca619b3"></a>
## exact_prime_power_valuation_layer

For p prime, e >= 1 and n coprime to p, the incidence of A at p^e n minus its incidence at p^(e-1) n is exactly the incidence at n of the exact-valuation pullback {d coprime to p : p^e d in A}.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [supportCoeff_prime_power_layer](../../Erdos249257/SupportSunflowerDichotomy.lean#L655)
- Lean declaration: [supportCoeffInt_prime_power_layer](../../Erdos249257/SupportSunflowerDichotomy.lean#L702)

- outgoing **generalises**: [Z10::dilation_difference_is_pullback_coefficient](BROWSER_Z10_1.md#node-f64d37d580e12dd4). The valuation layer repairs the repeated-prime case that the distinct-prime dilation identity cannot reach.
- incoming **specialises**: [Z10::mixed_prime_power_layer_algebra](BROWSER_Z10_2.md#node-079ff9668b18c90e). Two-fold iteration of the single-prime layer identity at distinct primes.
- incoming **finite_instance_of**: [Z10::prime_power_layer_fixtures](BROWSER_Z10_2.md#node-da59425e27f6fe8d). The singleton fixtures {8} and {12} evaluate the layer at prescribed valuations.

<a id="node-a4c985e2d684310b"></a>
## exact_reduced_take_step_cancellation

A take step of the reduced greedy state has an exact closed form: the new numerator and denominator are given by explicit polynomials in the old ones, the coprimality is preserved, the residual numerator and the exact cancellation factor are computed, and the actual greedy orbit realises this step, so a raw taken residual reduces to the next displayed state by a positive factor.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [reducedTakeStep_eq](../../Erdos249257/DyadicPrefixCompression.lean#L2413)
- Lean declaration: [reducedTakeStep_coprime](../../Erdos249257/DyadicPrefixCompression.lean#L2379)
- Lean declaration: [reducedTakeStep_residual_gcd](../../Erdos249257/DyadicPrefixCompression.lean#L2500)
- Lean declaration: [halfGreedy_takenRank_reducedTakeStep](../../Erdos249257/DyadicPrefixCompression.lean#L2661)
- Lean declaration: [halfGreedy_take_raw_reduces_to_next](../../Erdos249257/DyadicPrefixCompression.lean#L3023)

- outgoing **depends_on_open**: [Z10::block_take_and_safety_predicates_are_gcd_invariant](BROWSER_Z10_1.md#node-f409427eedd8d532). The cancellation factor is exactly the common factor the invariance theorems allow to be ignored.

<a id="node-2f0f69ed077ae769"></a>
## explicit_two_core_bounded_omega_bouquet

There is an explicit infinite orthogonal petal bouquet with two genuinely different fixed cores: frame Q = 6, cores alternating between 2 and 3, petals the squares of the primes from the third onwards. Every member has exactly three prime factors with multiplicity, so the interface is non-vacuous on a bounded-Omega support.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [alternatingPrimeSquareSupport_infinite](../../Erdos249257/SupportSunflowerDichotomy.lean#L337)
- Lean declaration: [alternatingPrimeSquareSupport_cardFactors_eq_three](../../Erdos249257/SupportSunflowerDichotomy.lean#L343)
- Lean declaration: [alternatingPrimeSquareBouquet_uses_two_cores](../../Erdos249257/SupportSunflowerDichotomy.lean#L360)

- outgoing **finite_instance_of**: [Z10::orthogonal_petal_bouquet_reduced_modulus](BROWSER_Z10_2.md#node-8f336665f6f7e739). An explicit witness that the bouquet interface is non-vacuous with bounded Omega.

<a id="node-cc4b29d2ebadd1ad"></a>
## finite_fragment_residual_transport

Removing a finite fragment F from a support subtracts the exact rational finite Mersenne sum from the value; that rational has odd reduced denominator whose multiplicative order of 2 is exactly the lcm of F. Combining with the denominator sandwich gives a certificate carrying the exact residual value, the exact period, and the transported wrap-ratio lower bound on the residual's reciprocal mass.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [finiteFragment_dyadicPrefixCompression](../../Erdos249257/DyadicPrefixCompression.lean#L1636)
- Lean declaration: [finiteFragment_residual_value](../../Erdos249257/DyadicPrefixCompression.lean#L1591)
- Lean declaration: [oddDoublingOrder_finiteErdosSum_den_eq_lcm](../../Erdos249257/DyadicPrefixCompression.lean#L1530)
- Lean declaration: [erdosSupportSeries_diff_finset](../../Erdos249257/DyadicPrefixCompression.lean#L1558)

- outgoing **depends_on_open**: [Z10::dyadic_prefix_residual_denominator_sandwich](BROWSER_Z10_1.md#node-f72c02d402375a21). The certificate's denominator clause is the sandwich applied to the actual reduced prefix denominator.
- outgoing **depends_on_open**: [Z10::rational_value_forces_order_wrap_ratio_bound](BROWSER_Z10_2.md#node-3845be9631e85dab). The certificate's wrapBound clause is the T9 conclusion transported to the residual support.
- incoming **finite_instance_of**: [Z10::half_value_forces_residual_reciprocal_mass_bound](BROWSER_Z10_2.md#node-2240732fc236082d). The two named fragments instantiate the generic compression certificate.
- incoming **finite_instance_of**: [Z10::dyadic_prefix_fixtures](BROWSER_Z10_1.md#node-e66868b5312099b9). Exact reduced sums, orders and wrap counts for the two fragments.
- incoming **finite_instance_of**: [Z01::concrete_period_noncollapse_instances](BROWSER_Z01_1.md#node-779bda153125d283). the transport's exact-period clause says a removed finite fragment F leaves a rational with odd reduced denominator whose order of 2 is exactly lcm F; the fixtures verify that at F = {2},{6},{10},{30} with denominators 3, 63, 1023 and 2^30-1 and orders 2, 6, 10, 30.
- incoming **finite_instance_of**: [Z12::half_orbit_exact_rational_fixtures](BROWSER_Z12_1.md#node-370f9ffbb079ae6b). the exact residuals 1/2 - sum over {2,3,6,7} = 1/16002 and over {2,3,6,7,14} = 1/688086 are two instances of subtracting the exact rational finite Mersenne sum of a fragment F from a value, with the odd reduced denominators the transport predicts.

<a id="node-d1780bc7c4537075"></a>
## first_shell_divisor_shadow_is_primitive_bit

The incidence of A splits exactly into the incidences of its prefix through X and of its residual above X; on the first dyadic shell X < n <= 2X the residual incidence equals the plain membership bit, because a divisor of n exceeding X must be n itself. Subtracting the prefix carry scaled by q from the full carry scaled by D leaves exactly qD times the residual tail, whose forcing digit on that shell is therefore the membership bit.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [supportCoeff_primitiveResidual_first_shell](../../Erdos249257/PrimitiveSupportBridge.lean#L65)
- Lean declaration: [supportCoeff_eq_primitivePrefix_add_residual](../../Erdos249257/PrimitiveSupportBridge.lean#L99)
- Lean declaration: [primitiveCrossCarry_eq_residualTail](../../Erdos249257/PrimitiveSupportBridge.lean#L172)
- Lean declaration: [primitiveCrossCarry_first_shell_recurrence](../../Erdos249257/PrimitiveSupportBridge.lean#L184)

- incoming **depends_on_open**: [Z10::denominator_shell_pressure_from_analytic_tail_bound](BROWSER_Z10_1.md#node-1630e5ef2f14794e). The residual whose size is bounded is the cross-carry residual isolated on the first shell.

<a id="node-050b30a047d1f9cb"></a>
## forced_take_block_depth_is_sharp

The forced-take block extracted from a cap violation cannot be extended by one more rank: the two-channel cap is strictly below the Mersenne prefix mass through 2m+3 ranks, and there is a real residual violating the cap whose remainder after the 2m+2 forced takes is already below the next weight.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Only shows that this particular tail-mass comparison cannot force a longer block. Longer forced blocks may still follow from a different estimate or from the actual greedy state; the sharpness witness is a relaxed real residual, not a residual known to occur on the greedy orbit for 1/2.

- Lean declaration: [halfTwoChannelCap_lt_mersennePrefix_threeDepth_add_three](../../Erdos249257/DyadicPrefixCompression.lean#L1324)
- Lean declaration: [exists_relaxed_capViolation_exact_block](../../Erdos249257/DyadicPrefixCompression.lean#L1341)

- outgoing **barrier_for**: [Z10::unsafe_skip_forces_long_forced_take_block](BROWSER_Z10_2.md#node-c29d8d1929d4f3b7). It shows the forced block cannot be lengthened by the same tail-mass comparison.

<a id="node-a94679449d4350eb"></a>
## greedy_decisions_are_sign_conditions_on_excess_numerator

Every greedy decision for the target 1/2 against the Mersenne weights - take, skip, dyadic safety, two-channel cap violation, membership in the Mersenne/dyadic sliver - is equivalent to an explicit sign or window condition on a single integer excess numerator obeying E(n+1) = 2E(n) + L, with no real analysis left in the criterion.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos](../../Erdos249257/DyadicPrefixCompression.lean#L961)
- Lean declaration: [greedyHalfRemainder_le_twoChannelCap_iff_excess](../../Erdos249257/DyadicPrefixCompression.lean#L912)
- Lean declaration: [greedyHalf_mem_nextMersenneDyadicSliver_iff_excess](../../Erdos249257/DyadicPrefixCompression.lean#L1044)
- Lean declaration: [greedyHalf_badSkipCapViolation_iff_primitiveLattice](../../Erdos249257/DyadicPrefixCompression.lean#L2188)

- incoming **reformulates**: [Z10::greedy_take_predicate_equals_block_take_predicate](BROWSER_Z10_1.md#node-e3ae02f4c5975be1). Both replace the analytic greedy test by an arithmetic predicate on the displayed state.
- incoming **reformulates**: [Z10::greedy_remainder_in_support_coefficient_coordinates](BROWSER_Z10_1.md#node-fe60cd4db042c44a). The same window condition expressed in support-incidence tail coordinates.
- outgoing **reformulates**: [Z12::channel_cap_skip_transport](BROWSER_Z12_1.md#node-3b04a5f99d781f94). greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos and greedyHalfRemainder_le_twoChannelCap_iff_excess are exactly the two skip-branch cap hypotheses of half_mem_mersenneAchievementSet_of_skipped_dyadicCap / _twoChannelCap, restated as sign conditions on one integer excess numerator.

<a id="node-fe60cd4db042c44a"></a>
## greedy_remainder_in_support_coefficient_coordinates

The greedy remainder for 1/2 equals (an integer carry minus the binary incidence tail of the finite prefix support) over 2^(n+1); the support tail gap equals the excess numerator over the prefix denominator; and the bad-skip cap violation is exactly a two-sided window condition on that support-coefficient tail gap.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [greedyHalfRemainder_eq_integerCarry_sub_coeffTail_div_pow](../../Erdos249257/DyadicPrefixCompression.lean#L2244)
- Lean declaration: [halfGreedyPrefixSupportTailGap_eq_excess_div_denominator](../../Erdos249257/DyadicPrefixCompression.lean#L2281)
- Lean declaration: [greedyHalf_badSkipCapViolation_iff_supportCoeffTailGap](../../Erdos249257/DyadicPrefixCompression.lean#L2319)

- outgoing **reformulates**: [Z10::greedy_decisions_are_sign_conditions_on_excess_numerator](BROWSER_Z10_1.md#node-a94679449d4350eb). The same window condition expressed in support-incidence tail coordinates.

<a id="node-e3ae02f4c5975be1"></a>
## greedy_take_predicate_equals_block_take_predicate

The analytic greedy take test at rank n+1 is exactly the arithmetic BlockTakeAt predicate on the actual displayed numerator and prefix denominator, and block dyadic safety at a skipped rank forces the greedy remainder below the next dyadic cap. Both statements are unconditional identities between an analytic and an arithmetic test; neither asserts anything about the value 1/2.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [greedyHalf_take_iff_BlockTakeAt](../../Erdos249257/DyadicPrefixCompression.lean#L2959)
- Lean declaration: [greedyHalfRemainder_le_nextDyadic_of_BlockSafe](../../Erdos249257/DyadicPrefixCompression.lean#L2914)

- outgoing **reformulates**: [Z10::greedy_decisions_are_sign_conditions_on_excess_numerator](BROWSER_Z10_1.md#node-a94679449d4350eb). Both replace the analytic greedy test by an arithmetic predicate on the displayed state.
- incoming **depends_on_open**: [Z10::half_membership_from_raw_block_margin_supply](BROWSER_Z10_2.md#node-5d104a681bbe0d26). The raw block witness delivers block dyadic safety, which is what the greedy consumer needs.
- incoming **depends_on_open**: [Z10::half_membership_from_actual_block_safety](BROWSER_Z10_2.md#node-6cf216bc1ead238e). The conditional consumes greedyHalfRemainder_le_nextDyadic_of_BlockSafe to turn arithmetic block safety at a skipped rank into the analytic dyadic-cap bound.
- outgoing **reformulates**: [Z12::greedy_rational_exactness](BROWSER_Z12_1.md#node-a57ea44d67021816). greedyHalf_take_iff_BlockTakeAt (DyadicPrefixCompression.lean) and rational_greedy_take_iff_real (GreedyAchievementSet.lean) both identify the analytic greedy take test at a rank with an exact arithmetic test on the displayed numerator and prefix denominator.
- incoming **reformulates**: [Z13::rational_take_comparison_in_floor_coordinates](BROWSER_Z13_1.md#node-a81c11f42592eccc). seamWord_take_iff_floorZ (HalfCylinderFloorErrorReset.lean) states the same rank-s take decision in the corrected floor coordinate floorZ = defect - floor error; both are exact recoordinatisations of one greedy step.

