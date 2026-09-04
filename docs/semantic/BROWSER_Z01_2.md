# Z01_2: Certificate kernel: irrationality engines, block certificates and the wave chain

[All problems and zones](BROWSER.md)

<a id="node-63152823758282cd"></a>
## lcm_gap_support_instances

Instances of the lcm-gap theorem: for every base b at least 2 the series over factorial exponents and the series over powers of two are irrational, and in particular the base-2 members of the Erdos #257 statement family for factorial support and for power-of-two support are irrational.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [irrational_erdosSum_factorial_support](../../Erdos249257/CertificateKernel.lean#L6035)
- Lean declaration: [irrational_erdosSum_two_pow_support](../../Erdos249257/CertificateKernel.lean#L6059)
- Lean declaration: [erdos257_family_factorial_instance](../../Erdos249257/CertificateKernel.lean#L6082)
- Lean declaration: [erdos257_family_two_pow_instance](../../Erdos249257/CertificateKernel.lean#L6090)

- outgoing **specialises**: [Z01::lcm_gap_irrationality_theorem](BROWSER_Z01_1.md#node-df3ac7a0b39aeae8). factorial and power-of-two supports satisfy the gap hypothesis

<a id="node-74e2b93b64962549"></a>
## lcm_ray_window_structure

Structure of the lcm ray: below twice the scale every window index divides the period except bare prime powers strictly between t and 2t, and for a clean divisor of the period the window totient factorises exactly as phi(j) times phi of the reduced ray point.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [period_lcm_window_index_prime_pow_of_not_dvd](../../Erdos249257/CertificateKernel.lean#L18941)
- Lean declaration: [totient_period_lcm_ray_factorisation](../../Erdos249257/CertificateKernel.lean#L18950)

- outgoing **depends_on_open**: [Z01::erdos249_cone_supply_restatement](BROWSER_Z01_1.md#node-4007efd56b0e194f). describes the arithmetic of the ray on which the missing supply would live
- outgoing **equivalent_to**: [Z06::lcm_ray_window_structure](BROWSER_Z06_1.md#node-4451a0a51d2089ac). period_lcm_window_index_prime_pow_of_not_dvd and eq_prime_pow_of_not_dvd_periodLcm are the same classification: below 2t every window index divides lcm(1..t) except bare prime powers exceeding t.
- outgoing **alias_of**: [Z06::lcm_ray_window_structure](BROWSER_Z06_1.md#node-4451a0a51d2089ac). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18613 `period_lcm_window_index_prime_pow_of_not_dvd := TotientTailPeriodKiller.eq_prime_pow_of_not_dvd_periodLcm` (owned at LcmDiagonalReduction.lean:137); same statement, shared node id.
- outgoing **alias_of**: [Z06::lcm_ray_totient_factorisation](BROWSER_Z06_1.md#node-422ae61aee562243). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18622 `totient_period_lcm_ray_factorisation := TotientTailPeriodKiller.totient_periodLcm_ray_split`; the second conjunct of the Z01 node is exactly Z06's ray-factorisation node.

<a id="node-2060d63596cd0fe1"></a>
## lifting_the_exponent_calculus

Exact valuations of b^(d k) - 1 at a prime q whose order for b is d: for odd q the q-valuation is the valuation of b^d - 1 plus that of k, and for q = 2 with b odd the 2-adic valuation splits by the parity of the exponent into the classical (b-1), (b+1) and exponent contributions. The normalised quotients are computed and shown to be q-units.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [odd_prime_order_padicVal_pow_sub_one](../../Erdos249257/CertificateKernel.lean#L340)
- Lean declaration: [odd_prime_order_factorization_pow_sub_one](../../Erdos249257/CertificateKernel.lean#L378)
- Lean declaration: [two_adic_pow_sub_one_factorization_even](../../Erdos249257/CertificateKernel.lean#L2328)
- Lean declaration: [two_adic_pow_sub_one_factorization_odd](../../Erdos249257/CertificateKernel.lean#L2350)
- Lean declaration: [odd_prime_order_normalized_pow_sub_one_modEq](../../Erdos249257/CertificateKernel.lean#L814)
- Lean declaration: [odd_prime_order_residue_formula](../../Erdos249257/CertificateKernel.lean#L1032)

- outgoing **implies**: [Z01::exact_order_prime_power_witness_supply](BROWSER_Z01_1.md#node-16390fae0f7684fc). the exponent laws are what lift a cyclotomic prime to a prime power of exact order

<a id="node-8d1006a691c6be51"></a>
## local_layer_certificate_engine

If the common numerator is a finite sum of terms all divisible by q^m whose q^m-quotients sum to a q-unit, then the numerator has q-valuation exactly m; whenever m is below the q-valuation of the component quotient this supplies a prime-component witness and blocks the corresponding period drop. Minimal-layer, singleton-row, maximal-weight-row and component-term-row variants are all instances of the same certificate.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [LocalLayerCertificate.sum_factorization](../../Erdos249257/CertificateKernel.lean#L1479)
- Lean declaration: [local_layer_certificate_supplies_PrimeComponentWitness](../../Erdos249257/CertificateKernel.lean#L1610)
- Lean declaration: [local_layer_sum_certificate_supplies_PrimeComponentWitness](../../Erdos249257/CertificateKernel.lean#L1618)
- Lean declaration: [minimal_layer_decomposition_supplies_PrimeComponentWitness](../../Erdos249257/CertificateKernel.lean#L1659)
- Lean declaration: [primitive_witness_blocks_collapse](../../Erdos249257/CertificateKernel.lean#L1888)
- Lean declaration: [local_layer_witness_family_implies_period_noncollapse](../../Erdos249257/CertificateKernel.lean#L4325)
- Lean declaration: [local_layer_decomposition_family_implies_period_noncollapse](../../Erdos249257/CertificateKernel.lean#L4363)
- Lean declaration: [minimal_layer_decomposition_family_implies_period_noncollapse](../../Erdos249257/CertificateKernel.lean#L4408)

- outgoing **specialises**: [Z01::period_noncollapse_witness_reduction](BROWSER_Z01_2.md#node-9c0398d7b79861e9). local layer certificates are an alternative witness source for the same reduction

<a id="node-f9f70d124b7b25b4"></a>
## low_carry_certificate_engine

The residue-band weakening of the block certificate: the packed first block need not be integral but may leave the residue V = carrySum mod b^K, provided the height inequality q*(V*b^(L-K) + C + N + L + 2) < b^L absorbs it. This still yields a near-integer witness and irrationality of the coefficient series.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [near_int_witness_of_weighted_coeff_low_carry_block_certificate](../../Erdos249257/CertificateKernel.lean#L14834)
- Lean declaration: [irrational_coeff_series_of_weighted_coeff_low_carry_block_certificates](../../Erdos249257/CertificateKernel.lean#L15035)
- Lean declaration: [coeff_series_shifted_ne_int_div_of_low_carry_certificate](../../Erdos249257/CertificateKernel.lean#L15331)

- outgoing **generalises**: [Z01::carry_aware_certificate_engine](BROWSER_Z01_1.md#node-85bdec04dff8f727). the residue band contains the exact-carry case as its zero-residue point
- incoming **generalises**: [Z01::gap_certificate_engine](BROWSER_Z01_1.md#node-d3d303b78be4b97c). the low-carry certificate is the j = 0 case of the gap certificate

<a id="node-95967a6c8d05ed40"></a>
## menu_refuter_exactness_and_monotonicity

The menu refuter fires exactly when the menu arcs share no common point; a common point at depth L+1 descends to depth L, so a firing certificate keeps firing at every deeper depth and at every larger menu, and a firing certificate lifts along both refinements simultaneously.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [totient_tail_cone_nonflat_cert_iff_no_common_point](../../Erdos249257/CertificateKernel.lean#L19228)
- Lean declaration: [totient_tail_cone_common_point_halving_descent](../../Erdos249257/CertificateKernel.lean#L19236)
- Lean declaration: [totient_tail_cone_nonflat_cert_depth_monotone](../../Erdos249257/CertificateKernel.lean#L19246)
- Lean declaration: [totient_tail_cone_nonflat_cert_supermenu](../../Erdos249257/CertificateKernel.lean#L19258)
- Lean declaration: [totient_tail_cone_nonflat_cert_seed_lift](../../Erdos249257/CertificateKernel.lean#L19269)

- outgoing **reformulates**: [Z01::cone_nonflat_menu_refuter](BROWSER_Z01_1.md#node-18a57855d478e08e). characterises exactly when the refuter fires and shows firing persists at greater depth and larger menus
- outgoing **equivalent_to**: [Z06::menu_refuter_exactness](BROWSER_Z06_1.md#node-543ed242df18c023). totient_tail_cone_nonflat_cert_iff_no_common_point and coneNonflatCert_iff_no_common_point are the same argmin exactness statement for the cone non-flatness menu certificate.
- outgoing **alias_of**: [Z06::menu_refuter_exactness](BROWSER_Z06_1.md#node-543ed242df18c023). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18900 re-exports `coneNonflatCert_iff_no_common_point`; the exactness half of the Z01 node is Z06's node.
- outgoing **alias_of**: [Z06::menu_refuter_monotonicity_and_seed_lift](BROWSER_Z06_1.md#node-eead6993cd5ea533). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18908/18918/18930/18941 re-export `coneCommonPoint_of_succ`, `coneNonflatCert_mono_of_le`, `..._supermenu`, `..._seed_lift`; the monotonicity half of the Z01 node is Z06's node.

<a id="node-879ace93eae03ce4"></a>
## multiples_support_irrationality

For every base b at least 2 and every d at least 1 the support series over the multiples of d equals the full-support series at base b^d, hence is irrational; equivalently the sum over k of 1/(b^(d(k+1)) - 1) is irrational.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [erdosSupportSeries_multiples_eq_pow_base_full_support](../../Erdos249257/CertificateKernel.lean#L9054)
- Lean declaration: [irrational_erdosSupportSeries_multiples](../../Erdos249257/CertificateKernel.lean#L9103)
- Lean declaration: [irrational_erdosSum_multiples_support](../../Erdos249257/CertificateKernel.lean#L9113)

- outgoing **specialises**: [Z01::erdos_borwein_full_support_irrationality](BROWSER_Z01_1.md#node-79ab550ed10b5c4b). the multiples support is the full support at base b^d

<a id="node-d00fae1092f3f7c6"></a>
## near_integer_irrationality_criterion

A real number is irrational if for every precision q there is an integer multiplier (respectively a power of the base b) whose product with the number is at nonzero distance below 1/q from an integer; a rational-prefix variant allows the prefix denominator to be absorbed into the precision.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [irrational_of_int_mul_near_int](../../Erdos249257/CertificateKernel.lean#L6120)
- Lean declaration: [irrational_of_pow_mul_near_int](../../Erdos249257/CertificateKernel.lean#L6149)
- Lean declaration: [irrational_of_rat_prefix_tail_near_int_witnesses](../../Erdos249257/CertificateKernel.lean#L9500)

- incoming **specialises**: [Z01::full_support_near_int_reduction](BROWSER_Z01_1.md#node-84f534afd83c7e7d). applies the near-integer criterion to the divisor-count series through the Lambert identity

<a id="node-a0ff08f73ac85616"></a>
## omega_bigomega_support_bridge

The support coefficient of the primes is the number of distinct prime factors and the support coefficient of the prime powers is the number of prime factors with multiplicity, so the prime and prime-power support series are the omega and big-Omega coefficient series.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [supportCoeff_primes_eq_card_primeFactors](../../Erdos249257/CertificateKernel.lean#L9656)
- Lean declaration: [supportCoeff_primePowers_eq_sum_factorization](../../Erdos249257/CertificateKernel.lean#L9670)
- Lean declaration: [erdosSupportSeries_primes_eq_tsum_omega](../../Erdos249257/CertificateKernel.lean#L9726)
- Lean declaration: [erdosSupportSeries_primePowers_eq_tsum_bigOmega](../../Erdos249257/CertificateKernel.lean#L9734)

- outgoing **specialises**: [Z01::support_coefficient_representation](BROWSER_Z01_2.md#node-950d0bc2e85796ab). the prime and prime-power supports name their coefficients as omega and big-Omega

<a id="node-6cc55d9d294a0368"></a>
## pairwise_coprime_support_irrationality

For every base b at least 2 and every infinite pairwise-coprime support whose reciprocals are summable, the support series is irrational. Certificates are supplied by disjoint blocks of pairwise-coprime support elements together with the reciprocal-tail bound.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [irrational_erdosSupportSeries_pairwise_coprime](../../Erdos249257/CertificateKernel.lean#L10776)
- Lean declaration: [exists_weighted_coeff_certificates_supportCoeff_pairwise_coprime](../../Erdos249257/CertificateKernel.lean#L9902)

- outgoing **implies**: [Z01::generic_coefficient_certificate_engine](BROWSER_Z01_1.md#node-347d00f05c4a588d). disjoint coprime blocks supply the certificates for that support class

<a id="node-0725e83257a45bb2"></a>
## period_four_sign_weight_zero_progression

For the period-four sign weight 1, 0, -1, 0 the signed divisor coefficient vanishes identically on every n congruent to 3 modulo 4, because the divisor involution pairs opposite signs. Zero sets of periodic signed coefficients can therefore contain whole arithmetic progressions.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Rules out only steering the certificate frame onto nonzero cofactor residues by residue selection alone, and only for this one period-four sign weight. It does not show the series for that weight is rational, does not obstruct the protected-block engine at other residues or other weights, and does not bear on the mixed-sign irrationality question itself.

- Lean declaration: [intWeightedCoeff_periodFourSignWeight_eq_zero_of_mod_four_eq_three](../../Erdos249257/CertificateKernel.lean#L14226)

- outgoing **barrier_for**: [Z01::signed_protected_block_engine](BROWSER_Z01_2.md#node-eed4f03deb5e41b2). shows residue selection alone cannot steer the protected-block frame onto nonzero cofactor residues for the period-four sign weight

<a id="node-9c0398d7b79861e9"></a>
## period_noncollapse_witness_reduction

The period of the reduced denominator equals the lcm of the exponents as soon as, for each prime p dividing the lcm, some prime q has strictly larger valuation in the component quotient (b^L-1)/(b^(L/p)-1) than in the common numerator. Several equivalent certificate dresses of this same reduction are given: raw valuation witnesses, modular-order witnesses, per-prime residue shapes, finite row tables, generated row tables and an emitted certificate-table structure.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [no_prime_drop_implies_eq](../../Erdos249257/CertificateKernel.lean#L37)
- Lean declaration: [valuation_witnesses_imply_no_prime_drop](../../Erdos249257/CertificateKernel.lean#L84)
- Lean declaration: [witness_certificate_implies_period_noncollapse](../../Erdos249257/CertificateKernel.lean#L1271)
- Lean declaration: [witness_existence_implies_period_noncollapse](../../Erdos249257/CertificateKernel.lean#L1385)
- Lean declaration: [finite_period_noncollapse_from_witness_route](../../Erdos249257/CertificateKernel.lean#L2944)
- Lean declaration: [finite_period_noncollapse_from_residue_shapes](../../Erdos249257/CertificateKernel.lean#L2977)
- Lean declaration: [finite_period_noncollapse_from_generated_finite_rows](../../Erdos249257/CertificateKernel.lean#L3010)
- Lean declaration: [finite_period_noncollapse_from_emitted_certificate_table](../../Erdos249257/CertificateKernel.lean#L3101)
- Lean declaration: [finite_period_noncollapse_from_emitted_generated_row_table](../../Erdos249257/CertificateKernel.lean#L3117)

- outgoing **implies**: [Z01::finite_period_noncollapse](BROWSER_Z01_1.md#node-ed84a74576eddd3a). the reduction discharged by the canonical selector and cyclotomic supply is exactly what proves the unconditional theorem
- incoming **specialises**: [Z01::canonical_witness_selector_reduction](BROWSER_Z01_1.md#node-9a3634435b900811). the selector row is one concrete way of producing the per-prime witness the general reduction demands
- incoming **specialises**: [Z01::local_layer_certificate_engine](BROWSER_Z01_2.md#node-8d1006a691c6be51). local layer certificates are an alternative witness source for the same reduction

<a id="node-c998de19d061f2c2"></a>
## periodic_support_irrationality

For every base b at least 2 the support series is irrational for every eventually periodic support containing a positive element, in particular for residue classes, for the odd numbers and for the multiples of any d. The engine is a periodic divisor-orbit sieve: at a prime of exact valuation b*phi(m)-1 not dividing the period, Euler cycles split every divisor ray into complete residue cycles repeated a multiple of b times, so b divides the support coefficient.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [irrational_erdosSupportSeries_periodic](../../Erdos249257/CertificateKernel.lean#L11590)
- Lean declaration: [irrational_erdosSupportSeries_eventuallyPeriodic](../../Erdos249257/CertificateKernel.lean#L11604)
- Lean declaration: [irrational_erdosSupportSeries_residueClass](../../Erdos249257/CertificateKernel.lean#L11672)
- Lean declaration: [irrational_erdosSupportSeries_odd](../../Erdos249257/CertificateKernel.lean#L11686)
- Lean declaration: [irrational_erdosSupportSeries_multiples_via_periodic](../../Erdos249257/CertificateKernel.lean#L11698)
- Lean declaration: [bpow_dvd_supportCoeff_of_periodic_exact_block](../../Erdos249257/CertificateKernel.lean#L11095)
- Lean declaration: [exists_weighted_coeff_certificates_supportCoeff_periodic](../../Erdos249257/CertificateKernel.lean#L11400)

- outgoing **implies**: [Z01::generic_coefficient_certificate_engine](BROWSER_Z01_1.md#node-347d00f05c4a588d). the periodic orbit sieve supplies the certificates the generic engine consumes
- incoming **generalises**: [Z01::periodic_weight_irrationality](BROWSER_Z01_2.md#node-18f0bd817a8cbf0e). indicator supports are the zero-one valued weights, by the layer-cake identity

<a id="node-18f0bd817a8cbf0e"></a>
## periodic_weight_irrationality

For every base b at least 2, every eventually periodic natural-number weight with a positive value in its periodic region gives an irrational weighted series sum of w(a)/(b^a - 1); the same holds for nonnegative rational eventually periodic coefficient sequences, and for the concrete weight a mod m with m at least 2. Bounded weights are handled as finite stacks of periodic indicator layers.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [irrational_weightedErdosSeries_periodic](../../Erdos249257/CertificateKernel.lean#L12698)
- Lean declaration: [irrational_weightedErdosSeries_eventuallyPeriodic](../../Erdos249257/CertificateKernel.lean#L12725)
- Lean declaration: [irrational_ratWeightSeries_eventuallyPeriodic](../../Erdos249257/CertificateKernel.lean#L12811)
- Lean declaration: [irrational_weightedErdosSeries_mod](../../Erdos249257/CertificateKernel.lean#L12903)
- Lean declaration: [bpow_dvd_weightedCoeff_of_periodic_exact_block](../../Erdos249257/CertificateKernel.lean#L11879)
- Lean declaration: [exists_weighted_coeff_certificates_weightedCoeff_periodic](../../Erdos249257/CertificateKernel.lean#L12492)

- outgoing **generalises**: [Z01::periodic_support_irrationality](BROWSER_Z01_2.md#node-c998de19d061f2c2). indicator supports are the zero-one valued weights, by the layer-cake identity
- incoming **generalises**: [Z01::signed_weight_dichotomy](BROWSER_Z01_2.md#node-70067b8f2d9c9efe). lifts the periodic weight theorem to integer weights at the cost of a terminating alternative

<a id="node-cb8ae7db72537740"></a>
## rational_denominator_bridge

The rational partial sum of 1/(b^n - 1) over a finite exponent set has Rat denominator exactly the natural-number reduced denominator built from the common numerator and b^lcm - 1, and that denominator is coprime to b and divides b^lcm - 1.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [finiteErdosSum_den_eq_reducedDenominator](../../Erdos249257/CertificateKernel.lean#L5212)
- Lean declaration: [coprime_base_den_finiteErdosSum](../../Erdos249257/CertificateKernel.lean#L5221)
- Lean declaration: [finiteErdosSum_eq_commonNumerator_div_commonDenominator](../../Erdos249257/CertificateKernel.lean#L5142)
- Lean declaration: [den_finiteErdosSum_dvd](../../Erdos249257/CertificateKernel.lean#L5397)

- outgoing **reformulates**: [Z01::finite_period_noncollapse](BROWSER_Z01_1.md#node-ed84a74576eddd3a). identifies the Nat reduced denominator with the Rat denominator of the same partial sum
- incoming **finite_instance_of**: [Z10::dyadic_prefix_fixtures](BROWSER_Z10_1.md#node-e66868b5312099b9). the reduced sums 10/21 and 172021/344043 are Rat denominators of finite Mersenne partial sums, exhibiting in two cases what the bridge asserts in general (odd, coprime to 2, dividing 2^lcm - 1).

<a id="node-06ed6d0b0890515b"></a>
## rationality_forces_tail_period

Contrapositive reduction for #249: under the free hypothesis hrat : not Irrational (sum phi(n)/2^n) -- the negation of the open problem, proved nowhere -- there exist a positive shift h and a threshold N0 such that for every N at least N0 the tail difference R_{N+h} - R_N is an integer. Refuting that integrality at a single (h, N) therefore proves irrationality; the theorem asserts nothing unconditional about the constant.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Produces no kill and no non-integrality: it says only what rationality would force. The supply side is the separate restatement node erdos249_period_kill_supply_restatement.

- Lean declaration: [rational_totient_series_forces_eventual_tail_period](../../Erdos249257/CertificateKernel.lean#L18783)

- incoming **implies**: [Z01::totient_tail_shift_and_period_law](BROWSER_Z01_2.md#node-f148b27a710470c2). the carry recurrence and the telescoping identity are the unconditional inputs the rationality argument consumes
- outgoing **implies**: [Z01::lcm_cone_flatness_law](BROWSER_Z01_1.md#node-ae87c97d6ef2cef3). the eventual tail period is specialised to the lcm cone to give fractional flatness of the whole cone
- outgoing **implies**: [Z01::window_kill_completeness](BROWSER_Z01_2.md#node-82033994a112e164). the contrapositive of the tail period law is exactly what turns a non-integral tail difference, and hence a window kill, into irrationality
- outgoing **equivalent_to**: [Z06::tail_period_law_from_rationality](BROWSER_Z06_2.md#node-2b462b01c608150a). rational_totient_series_forces_eventual_tail_period and eventual_period_of_not_irrational are the same contrapositive reduction: non-irrationality forces an eventual integral shifted tail difference.
- outgoing **alias_of**: [Z06::tail_period_law_from_rationality](BROWSER_Z06_2.md#node-2b462b01c608150a). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18455 `rational_totient_series_forces_eventual_tail_period := TotientTailPeriodKiller.eventual_period_of_not_irrational`; identical hypothesis (not Irrational S) and conclusion.

<a id="node-eed4f03deb5e41b2"></a>
## signed_protected_block_engine

For integer-valued coefficients a protected-block certificate leaves one designated slot congruent to a nonzero value modulo b^s while all other first-block slots are divisible, and the resulting nonzero fractional residue gives a near-integer witness; at exact valuation M*phi(m) the signed divisor coefficient is congruent modulo any modulus M, which supplies protected residues at arbitrary precision.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [near_int_witness_of_int_coeff_protected_block_certificate](../../Erdos249257/CertificateKernel.lean#L13351)
- Lean declaration: [irrational_int_coeff_series_of_protected_block_certificates](../../Erdos249257/CertificateKernel.lean#L13579)
- Lean declaration: [irrational_intWeightedErdosSeries_of_protected_block_certificates](../../Erdos249257/CertificateKernel.lean#L13687)
- Lean declaration: [intWeightedCoeff_modEq_of_periodic_extra_orbit_bpow](../../Erdos249257/CertificateKernel.lean#L13093)
- Lean declaration: [bpow_dvd_intWeightedCoeff_of_periodic_exact_block](../../Erdos249257/CertificateKernel.lean#L13038)

- incoming **barrier_for**: [Z01::period_four_sign_weight_zero_progression](BROWSER_Z01_2.md#node-0725e83257a45bb2). shows residue selection alone cannot steer the protected-block frame onto nonzero cofactor residues for the period-four sign weight
- outgoing **generalises**: [Z01::generic_coefficient_certificate_engine](BROWSER_Z01_1.md#node-347d00f05c4a588d). extends the certificate interface from natural to integer coefficients via a protected slot

<a id="node-70067b8f2d9c9efe"></a>
## signed_weight_dichotomy

For every base b at least 2 and every periodic integer weight, the signed series sum of w(a)/(b^a - 1) is either irrational or has some power of b times its value equal to an integer; equivalently, excluding the terminating alternative implies irrationality. The full-block certificate supply for periodic integer weights that this rests on is proved unconditionally.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic](../../Erdos249257/CertificateKernel.lean#L14175)
- Lean declaration: [irrational_intWeightedErdosSeries_periodic_of_bpow_mul_ne_intCast](../../Erdos249257/CertificateKernel.lean#L14200)
- Lean declaration: [int_coeff_series_irrational_or_bpow_mul_eq_intCast_of_full_block_certificates](../../Erdos249257/CertificateKernel.lean#L13934)
- Lean declaration: [exists_full_block_certificates_intWeightedCoeff_periodic](../../Erdos249257/CertificateKernel.lean#L13980)

- outgoing **generalises**: [Z01::periodic_weight_irrationality](BROWSER_Z01_2.md#node-18f0bd817a8cbf0e). lifts the periodic weight theorem to integer weights at the cost of a terminating alternative
- incoming **repair_of**: [Z01::coefficient_nonnegative_signed_irrationality](BROWSER_Z01_1.md#node-777841e3f0e5f4e5). closes the terminating alternative of the dichotomy for one-signed divisor coefficients

<a id="node-95bba30642ae44bd"></a>
## stern_brocot_run_geometry

Run-length geometry of the Stern-Brocot tree: an alternating word with r nonempty runs has height at least the (r+3)rd Fibonacci number, with equality on the all-unit spine; two-run heights and the small run masses are computed exactly. The module states explicitly that these facts create Fibonacci analytic pressure without supplying a denominator surplus and do not prove #249.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [stern_brocot_run_height_fib_lower](../../Erdos249257/CertificateKernel.lean#L18719)
- Lean declaration: [stern_brocot_unit_run_height_eq_fib](../../Erdos249257/CertificateKernel.lean#L18727)
- Lean declaration: [stern_brocot_two_run_height](../../Erdos249257/CertificateKernel.lean#L18733)
- Lean declaration: [stern_brocot_pair_of_run_lengths](../../Erdos249257/CertificateKernel.lean#L18708)
- Lean declaration: [stern_brocot_natural_run_denominator_exponent_add_two](../../Erdos249257/CertificateKernel.lean#L18749)

- outgoing **depends_on_open**: [Z01::gcd_moment_squared_lambert](BROWSER_Z01_1.md#node-1e4f5f5eeed01a3b). run geometry measures the Fibonacci pressure inside the gcd-moment cylinders without supplying a denominator surplus
- outgoing **reformulates**: [Z07::fibonacci_height_floor](BROWSER_Z07_1.md#node-caa09694be865178). stern_brocot_run_height_fib_lower / stern_brocot_unit_run_height_eq_fib and runHeight_fib_lower / runHeight_replicate_one are the same Fibonacci run-height floor with equality on the all-unit spine.
- outgoing **alias_of**: [Z07::fibonacci_height_floor](BROWSER_Z07_1.md#node-caa09694be865178). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18391/18399 re-export `SternBrocotRunGeometry.runHeight_fib_lower` and `runHeight_replicate_one`; identical Fibonacci floor and spine equality.
- outgoing **alias_of**: [Z07::induced_run_layer_masses](BROWSER_Z07_1.md#node-2f90e778c640aa02). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18405/18411/18415 re-export `SternBrocotRunGeometry.runHeight_pair`, `zeroRunMass_eq_quarter`, `oneRunMass_eq_half`.
- outgoing **alias_of**: [Z07::fibonacci_partial_sum_denominator_scale](BROWSER_Z07_1.md#node-c0e53492ea173d95). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18421 `stern_brocot_natural_run_denominator_exponent_add_two := SternBrocotRunGeometry.naturalRunDenominatorExponent_add_two`.
- outgoing **alias_of**: [Z07::run_coordinate_normalisation](BROWSER_Z07_1.md#node-669163a5d938cf84). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18380 `stern_brocot_pair_of_run_lengths := SternBrocotRunGeometry.sbPair_runWord`; the run/tree coordinate identification the Z01 node quotes is Z07's node.

<a id="node-a2a137e4aa310f92"></a>
## stray_divisor_finite_calculus

Exact finite arithmetic for support coefficients: the coefficient splits over an intersection with a finite set and its complement, equals the cardinality of a forced block when no stray support divisors occur, and reciprocal-tail and density bounds control the stray contributions.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [supportCoeff_eq_inter_add_diff](../../Erdos249257/CertificateKernel.lean#L9555)
- Lean declaration: [supportCoeff_eq_card_of_forced_of_no_strays](../../Erdos249257/CertificateKernel.lean#L9578)
- Lean declaration: [card_le_mul_sum_inv](../../Erdos249257/CertificateKernel.lean#L9598)
- Lean declaration: [exists_tail_bound_of_summable](../../Erdos249257/CertificateKernel.lean#L9627)

- outgoing **specialises**: [Z01::support_coefficient_representation](BROWSER_Z01_2.md#node-950d0bc2e85796ab). exact finite arithmetic for the same coefficient

<a id="node-950d0bc2e85796ab"></a>
## support_coefficient_representation

Definition and basic calculus of the support coefficient f_A(n) = #{d | n : d in A} and the support series sum over a in A of 1/(b^a - 1): the support series equals the coefficient series, the full support recovers the divisor count and the classical Erdos-Borwein shape, and the Nat-weighted and integer-weighted coefficients specialise to it.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [supportCoeff_univ_eq_card_divisors](../../Erdos249257/CertificateKernel.lean#L8874)
- Lean declaration: [erdosSupportSeries_eq_tsum_supportCoeff](../../Erdos249257/CertificateKernel.lean#L8952)
- Lean declaration: [erdosSupportSeries_univ_eq_erdosSum_full_support](../../Erdos249257/CertificateKernel.lean#L8937)
- Lean declaration: [weightedCoeff_indicator_eq_supportCoeff](../../Erdos249257/CertificateKernel.lean#L11782)
- Lean declaration: [intWeightedCoeff_natCast](../../Erdos249257/CertificateKernel.lean#L12979)
- Lean declaration: [weightedErdosSeries_eq_tsum_weightedCoeff](../../Erdos249257/CertificateKernel.lean#L12378)
- Lean declaration: [intWeightedErdosSeries_eq_tsum_intWeightedCoeff](../../Erdos249257/CertificateKernel.lean#L13628)

- outgoing **reformulates**: [Z01::lambert_divisor_identity](BROWSER_Z01_1.md#node-9f4a9661ab62e636). the support series is rewritten as a coefficient series by the same divisor rearrangement
- incoming **reformulates**: [Z01::finite_prefix_and_rational_prefix_calculus](BROWSER_Z01_1.md#node-9716dc225759669c). splits a support at a height cut into a rational prefix and a tail support
- incoming **specialises**: [Z01::omega_bigomega_support_bridge](BROWSER_Z01_2.md#node-a0ff08f73ac85616). the prime and prime-power supports name their coefficients as omega and big-Omega
- incoming **specialises**: [Z01::stray_divisor_finite_calculus](BROWSER_Z01_2.md#node-a2a137e4aa310f92). exact finite arithmetic for the same coefficient
- incoming **reformulates**: [Z12::mersenne_support_coding_normalisation](BROWSER_Z12_2.md#node-6dea3c442e2bc9d4). positiveMersenneSupportValue_eq_erdosSupportSeries (GreedyAchievementSet.lean:554) identifies the achievement-set value map with erdosSupportSeries at base 2, whose coefficient form is erdosSupportSeries_eq_tsum_supportCoeff.
- incoming **reformulates**: [Z10::mobius_inversion_of_support_coefficient](BROWSER_Z10_2.md#node-34ed548cbedf7039). mobius_supportCoeff_recovers_support inverts the coefficient construction of erdosSupportSeries_eq_tsum_supportCoeff: the support and its divisor-incidence coefficient are interchangeable data on positive integers.
- incoming **transport_of**: [Z07::lambert_positive_lift_of_249](BROWSER_Z07_1.md#node-31acef136518144f). tsum_primWeight_div_two_pow_sub_one puts S = sum_d A(d)/(2^d-1) with A = phi*mu >= 0, i.e. relocates #249 into the weighted Erdos-series family weightedErdosSeries_eq_tsum_weightedCoeff that Z01 normalises; the weight A is unbounded (primWeight_not_bounded), so it escapes the settled periodic/bounded-weight members.
- incoming **specialises**: [Z12::mersenne_support_coding_normalisation](BROWSER_Z12_2.md#node-6dea3c442e2bc9d4). `positiveMersenneSupportValue_eq_erdosSupportSeries : positiveMersenneSupportValue A = erdosSupportSeries 2 A` (GreedyAchievementSet.lean:554) identifies the Mersenne coding with the base b = 2 case of the generic support series that Z01 defines and normalises.

<a id="node-78e11eccc7fdd413"></a>
## tau_block_certificate_supply

For every base b at least 2 and every precision q a weighted divisor block certificate exists. The middle window is controlled because divisor counts average polylogarithmically along the frame, so a pigeonhole selection of the progression parameter crushes the middle mass below the height budget; near-integer witnesses and arbitrarily strong zero-block witnesses for the full-support series follow.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [exists_weighted_block_certificates](../../Erdos249257/CertificateKernel.lean#L8187)
- Lean declaration: [selected_weighted_middle_of_supported_frame](../../Erdos249257/CertificateKernel.lean#L8030)
- Lean declaration: [exists_first_block_progression_with_selected_weighted_middle](../../Erdos249257/CertificateKernel.lean#L7574)
- Lean declaration: [near_int_witnesses_erdosSum_full_support](../../Erdos249257/CertificateKernel.lean#L8708)
- Lean declaration: [zero_block_witnesses_erdosSum_full_support](../../Erdos249257/CertificateKernel.lean#L8732)
- Lean declaration: [certificate_param_arithmetic](../../Erdos249257/CertificateKernel.lean#L8054)

- outgoing **implies**: [Z01::divisor_block_certificate_engine](BROWSER_Z01_1.md#node-82d682802aaa267c). supplies the certificates the engine consumes, at every precision
- incoming **implies**: [Z01::bounded_crt_exact_valuation_frame](BROWSER_Z01_1.md#node-9f94182cfe2c39ce). the frame is what makes the first-block divisibility condition satisfiable
- outgoing **implies**: [Z01::erdos_borwein_full_support_irrationality](BROWSER_Z01_1.md#node-79ab550ed10b5c4b). certificates at every precision close the full-support theorem unconditionally

<a id="node-4d900bc1a4e58804"></a>
## totient_carry_field_recurrences

The totient carry residue field V_K(N), the residue of the packed window sum modulo 2^K, advances by the same affine doubling map in the shift and window directions; a top-band entry at one step forces the next window residue below the head totient, and that event yields a full low-carry certificate whenever the height budget allows.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [totient_carry_residue_succ_shift](../../Erdos249257/CertificateKernel.lean#L15226)
- Lean declaration: [totient_carry_residue_succ_window](../../Erdos249257/CertificateKernel.lean#L15249)
- Lean declaration: [totient_carry_residue_top_band_step](../../Erdos249257/CertificateKernel.lean#L15275)
- Lean declaration: [totient_low_carry_full_block_certificate_of_top_band](../../Erdos249257/CertificateKernel.lean#L15297)

- outgoing **depends_on_open**: [Z01::erdos249_certificate_supply_restatement](BROWSER_Z01_1.md#node-fe5e91cb1960ad1c). the recurrences describe the field in which the missing certificate supply would have to be found

<a id="node-ba5ac6fac81df5f1"></a>
## totient_denominator_exclusion_ladder

Unconditional bounded-denominator exclusions for the Erdos #249 constant: the sum of phi(n)/2^n has no rational representation with denominator at most 4838, then at most 4194304, then at most 248672326362367909, then at most 79639646646701375323355774875831053 (about 7.96 times 10^34). The same records transfer to the primitive-conductor Lambert form, and halved to the Moebius-square and visible-coprime-pair forms. This is a lower bound on any rational representation, not a proof of irrationality.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: prior_art_found.

- Lean declaration: [tsum_totient_div_pow_two_ne_ratCast_of_den_le_4838](../../Erdos249257/CertificateKernel.lean#L15675)
- Lean declaration: [tsum_totient_div_pow_two_ne_int_div_of_den_le_4194304](../../Erdos249257/CertificateKernel.lean#L18348)
- Lean declaration: [tsum_totient_div_pow_two_ne_ratCast_of_den_le_248672326362367909](../../Erdos249257/CertificateKernel.lean#L18337)
- Lean declaration: [tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053](../../Erdos249257/CertificateKernel.lean#L18384)
- Lean declaration: [tsum_primWeight_div_two_pow_sub_one_ne_int_div_of_den_le_79639646646701375323355774875831053](../../Erdos249257/CertificateKernel.lean#L18473)
- Lean declaration: [tsum_moebius_div_two_pow_sub_one_sq_ne_int_div_of_den_le_39819823323350687661677887437915526](../../Erdos249257/CertificateKernel.lean#L18487)
- Lean declaration: [tsum_visible_coprime_pairs_ne_int_div_of_den_le_39819823323350687661677887437915526](../../Erdos249257/CertificateKernel.lean#L18572)

- outgoing **finite_instance_of**: [Z01::gap_certificate_engine](BROWSER_Z01_1.md#node-d3d303b78be4b97c). each rung is the gap engine run at one verified window, giving one bounded denominator range
- incoming **implies**: [Z01::generated_gap_window_checkers](BROWSER_Z01_1.md#node-1e796f279b3072ef). the kernel-verified checker run is what discharges the 4194304 rung
- incoming **implies**: [Z01::totient_value_tables](BROWSER_Z01_2.md#node-19cf1055bec95e30). the tabulated totient values are what make the window residues computable in the kernel
- outgoing **transport_of**: [Z01::visible_lattice_coprimality](BROWSER_Z01_2.md#node-b0d79ae7dbb72785). the denominator record transfers along the coordinate change, halved for the shifted constant

<a id="node-ad9192dc2c50f6d6"></a>
## totient_first_block_hinge

A block of r distinct odd prime divisors of n forces 2^r to divide phi(n), with no exact valuation needed; consequently there is an arithmetic progression along which 2^r divides phi of the r-th first-block slot for every r up to K. The index shift identifying the sum over n at least 0 with the sum over n at least 1 is also recorded.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [two_pow_card_dvd_totient_of_odd_prime_block](../../Erdos249257/CertificateKernel.lean#L14704)
- Lean declaration: [exists_totient_first_block_divisibility_progression](../../Erdos249257/CertificateKernel.lean#L14730)
- Lean declaration: [tsum_totient_div_pow_eq_shifted](../../Erdos249257/CertificateKernel.lean#L14749)


<a id="node-b089feaf4597b079"></a>
## totient_series_moebius_square_lens

The Erdos #249 constant equals 1/2 plus the sum over d of mu(d)/(2^d - 1)^2, and equals the Lambert value of the nonnegative primitive-conductor weight phi * mu. The problem is thereby placed one Dirichlet convolution from a rational value and one from the machine-checked irrational Erdos-Borwein constant. No irrationality of the constant is claimed.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [totient_series_eq_half_add_moebius_mersenne_square](../../Erdos249257/CertificateKernel.lean#L18454)
- Lean declaration: [totient_series_eq_half_add_mobius_mersenne_square](../../Erdos249257/CertificateKernel.lean#L18463)
- Lean declaration: [tsum_primWeight_div_two_pow_sub_one_eq_totient_series](../../Erdos249257/CertificateKernel.lean#L18445)
- Lean declaration: [tsum_totient_div_pow_two_eq_pnat_half_pow](../../Erdos249257/CertificateKernel.lean#L18415)

- outgoing **reformulates**: [Z01::lambert_ladder_rational_rungs](BROWSER_Z01_1.md#node-4d6cc8cc64c5cf91). places the open constant one Dirichlet convolution from the rational rungs
- incoming **reformulates**: [Z01::visible_lattice_coprimality](BROWSER_Z01_2.md#node-b0d79ae7dbb72785). the same constant read as a coprime-pair probability on the visible lattice
- incoming **barrier_for**: [Z07::primitive_euler_index_no_lift_barrier](BROWSER_Z07_1.md#node-0913ec3431f6b924). This node presents #249 as the Lambert value of the primitive-conductor weight A = phi * mu; no_fixed_integral_primitive_euler_index shows no horizon-independent positive integer clears the normalised coordinates A(n)/n, since every odd prime p <= N and every p^2 <= N must divide it. Any denominator-clearing attack mounted on that presentation must therefore be horizon-dependent. Scope: only the ordinary integral Euler/Witt normalisation is closed.
- outgoing **equivalent_to**: [Z07::moebius_square_lens_of_249](BROWSER_Z07_1.md#node-a9f26d2d7d41fdbc). totient_series_eq_half_add_moebius_mersenne_square and tsum_totient_half_pow_eq_half_add_moebius_sq are the same identity S = 1/2 + sum_d mu(d)/(2^d-1)^2, so irrationality of S and of the squared-Mersenne Moebius series are interchangeable.
- outgoing **equivalent_to**: [Z07::lambert_positive_lift_of_249](BROWSER_Z07_1.md#node-31acef136518144f). Shared declaration tsum_primWeight_div_two_pow_sub_one_eq_totient_series: S = sum_d (phi*mu)(d)/(2^d-1), the positive Erdos-Borwein-shaped lift of #249.

<a id="node-4bdd060dc42777bf"></a>
## totient_series_rational_exclusions_from_kills

From the certified kills: the sum of phi(n)/2^n differs from every rational whose denominator divides 2^12 times 2^h - 1 for 1 <= h <= 8, and from every rational whose denominator divides 2^14 times 2^h - 1 for 1 <= h <= 16.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [totient_series_ne_rat_of_den_dvd_pow_two_mul_mersenne](../../Erdos249257/CertificateKernel.lean#L18807)
- Lean declaration: [totient_series_ne_rat_of_den_dvd_pow_two_mul_mersenne_upto_sixteen](../../Erdos249257/CertificateKernel.lean#L18890)

- outgoing **implies**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). the fixture kills exclude exactly the rationals whose denominator has the corresponding Mersenne shape
- outgoing **equivalent_to**: [Z06::unconditional_denominator_exclusion](BROWSER_Z06_2.md#node-a7dd11b48fa35258). Shared declarations totient_series_ne_rat_of_den_dvd and totient_series_ne_rat_of_den_dvd_upto_sixteen: the same two unconditional denominator exclusions at (N,h) = (12, <=8) and (14, <=16).
- outgoing **alias_of**: [Z06::unconditional_denominator_exclusion](BROWSER_Z06_2.md#node-a7dd11b48fa35258). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18479/18562 re-export `totient_series_ne_rat_of_den_dvd` and `..._upto_sixteen`; identical bounded-denominator exclusions.

<a id="node-f148b27a710470c2"></a>
## totient_tail_shift_and_period_law

Writing 2^N times the #249 constant as an integer prefix plus the local totient tail R_N, the tail obeys the carry recurrence R_{M+1} = 2 R_M - phi(M+1) and tail differences telescope along multiples of any shift. All three statements are identities, unconditional and free of hypotheses about the constant.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [two_pow_mul_totient_series_eq_prefix_add_tail](../../Erdos249257/CertificateKernel.lean#L18766)
- Lean declaration: [totient_tail_carry_recurrence](../../Erdos249257/CertificateKernel.lean#L18825)
- Lean declaration: [totient_tail_diff_multiple_telescope](../../Erdos249257/CertificateKernel.lean#L18841)

- outgoing **implies**: [Z01::erdos249_period_kill_supply_restatement](BROWSER_Z01_1.md#node-091f2dbf4dfd2e47). the tail-period law is what turns a kill supply into irrationality
- outgoing **implies**: [Z01::rationality_forces_tail_period](BROWSER_Z01_2.md#node-06ed6d0b0890515b). the carry recurrence and the telescoping identity are the unconditional inputs the rationality argument consumes
- outgoing **reformulates**: [Z06::shift_identity_totient_tail](BROWSER_Z06_2.md#node-0cce8442c93a2c03). two_pow_mul_totient_series_eq_prefix_add_tail and two_pow_mul_totient_series_eq are the same prefix/tail split 2^N S = Phi_N + R_N, and totient_tail_carry_recurrence is totientTail_succ.
- outgoing **alias_of**: [Z06::shift_identity_totient_tail](BROWSER_Z06_2.md#node-0cce8442c93a2c03). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18438 `two_pow_mul_totient_series_eq_prefix_add_tail := TotientTailPeriodKiller.two_pow_mul_totient_series_eq`; same identity 2^N*S = Phi_N + R_N. The Z01 node bundles this with two further re-exports, edged separately.
- outgoing **alias_of**: [Z06::tail_strip_and_carry_recurrence](BROWSER_Z06_2.md#node-1bb6df87e4fcba59). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18497 `totient_tail_carry_recurrence := TotientTailPeriodKiller.totientTail_succ`; identical carry recurrence R_{M+1} = 2R_M - phi(M+1). Z06 additionally owns the strip bound.
- outgoing **alias_of**: [Z06::period_ray_telescoping](BROWSER_Z06_1.md#node-95058e2cbf8f7f44). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18513 `totient_tail_diff_multiple_telescope := TotientTailPeriodKiller.tail_diff_mul`; the same telescoping of the period-mh difference.

<a id="node-19cf1055bec95e30"></a>
## totient_value_tables

Machine-checked totient values at the window positions used by the certificates: the 34 slots of the window at 763 and the 240 slots of the windows at 1, each proved from the prime factorisation of the argument.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [phi_4838_0](../../Erdos249257/CertificateKernel.lean#L15383)
- Lean declaration: [phi_w17_0](../../Erdos249257/CertificateKernel.lean#L16387)
- Lean declaration: [phi_w240_239](../../Erdos249257/CertificateKernel.lean#L18301)
- Lean declaration: [totient_low_carry_full_block_certificate_4838](../../Erdos249257/CertificateKernel.lean#L15652)

- outgoing **implies**: [Z01::totient_denominator_exclusion_ladder](BROWSER_Z01_2.md#node-ba5ac6fac81df5f1). the tabulated totient values are what make the window residues computable in the kernel

<a id="node-b0d79ae7dbb72785"></a>
## visible_lattice_coprimality

The #249 constant minus 1/2 equals the probability that two independent fair-coin waiting times are coprime, because phi(n) counts the visible lattice points on the line a + b = n; the gcd layers of that distribution sum to exactly 1, which is the probabilistic content of the rational rung L(phi) = 2. The coordinate change relocates the problem, it does not solve it.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [tsum_visible_coprime_pairs_eq_totient_series](../../Erdos249257/CertificateKernel.lean#L18544)
- Lean declaration: [totient_series_eq_half_add_visible_coprime_pairs](../../Erdos249257/CertificateKernel.lean#L18557)
- Lean declaration: [tsum_visible_coprime_gcd_layers_eq_one](../../Erdos249257/CertificateKernel.lean#L18597)
- Lean declaration: [tsum_totient_div_pow_two_eq_nat_half_pow](../../Erdos249257/CertificateKernel.lean#L18534)

- outgoing **reformulates**: [Z01::totient_series_moebius_square_lens](BROWSER_Z01_2.md#node-b089feaf4597b079). the same constant read as a coprime-pair probability on the visible lattice
- incoming **generalises**: [Z01::gcd_moment_squared_lambert](BROWSER_Z01_1.md#node-1e4f5f5eeed01a3b). the squared Lambert transform is the divisor calculus of the gcd of the same two waiting times
- incoming **transport_of**: [Z01::totient_denominator_exclusion_ladder](BROWSER_Z01_2.md#node-ba5ac6fac81df5f1). the denominator record transfers along the coordinate change, halved for the shifted constant
- outgoing **equivalent_to**: [Z07::coprime_pair_mass_bridge](BROWSER_Z07_1.md#node-0c4e3b1e6a2be76d). totient_series_eq_half_add_visible_coprime_pairs and tsum_pos_coprime_pair_pow both state S - 1/2 = base-2 mass of coprime pairs, via card_antidiagonal_filter_pos_coprime.
- outgoing **specialises**: [Z07::coprime_pair_mass_bridge](BROWSER_Z07_1.md#node-0c4e3b1e6a2be76d). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18229 `totient_series_eq_half_add_visible_coprime_pairs := GeometricCoprimality.tsum_pos_coprime_pair_pow`; Z07 states the coprime-pair mass identity for every 0 <= r < 1, Z01 keeps only the r = 1/2 instance.
- outgoing **specialises**: [Z07::gcd_layer_normalisation](BROWSER_Z07_1.md#node-6cd68e0a2e072191). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18269 `tsum_visible_coprime_gcd_layers_eq_one := GeometricCoprimality.tsum_gcd_layer_pos_coprime_half_eq_one`; Z07 owns the general-r gcd-layer identity of which this is the r = 1/2 evaluation.

<a id="node-82033994a112e164"></a>
## window_kill_completeness

The window kill certificate is complete as well as sound: a kill of some depth exists for a shift h at a position N if and only if the corresponding totient tail difference is not an integer.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Completeness of the certificate does not make it effective: it says a kill exists exactly when the tail difference is non-integral, not that any such kill can be found or that the difference can be decided.

- Lean declaration: [totient_tail_window_kill_exists_iff_tail_diff_not_int](../../Erdos249257/CertificateKernel.lean#L19025)

- outgoing **equivalent_to**: [Z01::certified_kill_soundness](BROWSER_Z01_1.md#node-ce3a6b8b2b87a632). completeness plus soundness make certificate existence and non-integrality the same predicate
- incoming **implies**: [Z01::rationality_forces_tail_period](BROWSER_Z01_2.md#node-06ed6d0b0890515b). the contrapositive of the tail period law is exactly what turns a non-integral tail difference, and hence a window kill, into irrationality
- outgoing **equivalent_to**: [Z06::endpoint_certificate_completeness](BROWSER_Z06_1.md#node-2151751ccfb38f8d). totient_tail_window_kill_exists_iff_tail_diff_not_int (CertificateKernel.lean:18697) and exists_certifiedKill_iff_tail_diff_notMem_int (LcmConeFlatness.lean:316) are the same iff: a kill of some depth exists at (h,N) exactly when R_{N+h}-R_N is not an integer.
- outgoing **alias_of**: [Z06::endpoint_certificate_completeness](BROWSER_Z06_1.md#node-2151751ccfb38f8d). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18697 `totient_tail_window_kill_exists_iff_tail_diff_not_int := TotientTailPeriodKiller.exists_certifiedKill_iff_tail_diff_notMem_int`; the same iff.

