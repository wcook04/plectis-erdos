# Z34_1: Certificate-kernel analytic, arithmetic, and finite-instance families

[All problems and zones](BROWSER.md)

<a id="node-923980c7ebbd3931"></a>
## bounded_eventually_periodic_weight_calculus

PROVED: bounded natural weights give W*tau(n) and W*n coefficient bounds while retaining the self weight; eventual periodicity folds every value into one finite prefix-plus-period window and therefore supplies a global bound; and a bounded weighted divisor coefficient is the sum of its indicator-layer filtered divisor counts.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The calculus is restricted to bounded eventually periodic natural weights. It does not provide an aperiodic certificate producer.

- Lean declaration: [weightedCoeff_le_mul_card_divisors](../../Erdos249257/CertificateKernel.lean#L11754)
- Lean declaration: [weightedCoeff_le_mul_self](../../Erdos249257/CertificateKernel.lean#L11766)
- Lean declaration: [weight_le_weightedCoeff](../../Erdos249257/CertificateKernel.lean#L11774)
- Lean declaration: [eventually_periodic_add_mul](../../Erdos249257/CertificateKernel.lean#L11793)
- Lean declaration: [eventually_periodic_fold](../../Erdos249257/CertificateKernel.lean#L11807)
- Lean declaration: [eventually_periodic_weight_bound](../../Erdos249257/CertificateKernel.lean#L11830)
- Lean declaration: [weightedCoeff_eq_sum_card_filter](../../Erdos249257/CertificateKernel.lean#L11845)

- incoming **generated_by**: [Z34::one_extra_orbit_preserves_nat_weight_residue](BROWSER_Z34_1.md#node-ef467ce0172bb237). The weighted residue theorem lifts the predicate-level one-extra-orbit count through the layer-cake decomposition.

<a id="node-30576ada661eb121"></a>
## bounded_weight_mersenne_terms_are_summable

PROVED: at every integer base b>=2, a uniformly bounded natural weight produces a summable weighted Mersenne reciprocal term sequence.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: Summability alone does not decide rationality or irrationality and supplies no arithmetic certificate.

- Lean declaration: [summable_weightedErdos_term](../../Erdos249257/CertificateKernel.lean#L12340)


<a id="node-4361c3f9c742b378"></a>
## coprime_progression_divisor_average

PROVED: modulus support above a window makes the construction modulus coprime to every middle shift; along a coprime progression each divisor occupies at most one residue class, divisor pairing reduces to divisors up to sqrt(X), and the resulting total divisor count is bounded by twice the corresponding floor-sum.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The theorem family averages a supplied finite progression. It does not by itself choose certificate parameters or give a cofinal family of good frames.

- Lean declaration: [coprime_middle_of_first_block_support](../../Erdos249257/CertificateKernel.lean#L7283)
- Lean declaration: [card_filter_dvd_progression_le](../../Erdos249257/CertificateKernel.lean#L7305)
- Lean declaration: [card_divisors_le_two_mul_card_small_divisors](../../Erdos249257/CertificateKernel.lean#L7352)
- Lean declaration: [sum_card_divisors_progression_le](../../Erdos249257/CertificateKernel.lean#L7407)

- incoming **generated_by**: [Z34::weighted_middle_progression_total](BROWSER_Z34_1.md#node-3cf1febd75f5add7). The weighted total combines the progression divisor average with the geometric sum of window weights.

<a id="node-718cff587a049636"></a>
## divisor_count_series_carry_and_far_tail

PROVED: for b>=2 the divisor-count series and its shifted tails are summable; multiplying the series by b^N splits it into an integer prefix plus a shifted tail, whose portion beyond L is at most (N+L+2)/b^L.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: This is analytic and algebraic infrastructure. It does not manufacture the first- or middle-window arithmetic certificate required for irrationality.

- Lean declaration: [summable_divisor_count_term](../../Erdos249257/CertificateKernel.lean#L6161)
- Lean declaration: [summable_divisor_count_shift_tail](../../Erdos249257/CertificateKernel.lean#L6337)
- Lean declaration: [bpow_mul_divisor_count_series_eq_int_add_tail](../../Erdos249257/CertificateKernel.lean#L6357)
- Lean declaration: [divisor_count_far_tail_le](../../Erdos249257/CertificateKernel.lean#L6434)

- outgoing **generated_by**: [Z34::linear_geometric_envelope_exact_bound](BROWSER_Z34_1.md#node-0ccbe66280ebf953). The divisor-count far-tail bound uses tau(n)<=n and the linear-times-geometric envelope.

<a id="node-e5de60ee9c422d4b"></a>
## factorial_and_power_two_prefix_lcm_exact

PROVED FINITE FAMILIES: for every positive prefix length k, the LCM of {1!,...,k!} is k!, and the LCM of {2^0,...,2^(k-1)} is 2^(k-1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: These exact prefix formulas concern two special sparse supports. They do not imply the universal support statement in Erdős #257.

- Lean declaration: [lcm_image_factorial_succ](../../Erdos249257/CertificateKernel.lean#L5999)
- Lean declaration: [lcm_image_two_pow](../../Erdos249257/CertificateKernel.lean#L6016)

- outgoing **specialises**: [Z34::strict_support_mersenne_tail_package](BROWSER_Z34_1.md#node-bfcc70596e127520). The two exact LCM families are concrete sparse supports to which the generic strict-support analytic package applies.

<a id="node-4b822ff8dcb32b90"></a>
## finite_totient_denominator_exclusion_instances

PROVED FINITE INSTANCES: the binary totient series differs from every integer quotient with denominator at most 4838, 248672326362367909, and 79639646646701375323355774875831053; in rational-cast form, any rational with reduced denominator at most 4194304 is also excluded.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Every bound is finite. Even the largest value is not an unbounded denominator supply and does not prove irrationality of the totient series.

- Lean declaration: [tsum_totient_div_pow_two_ne_int_div_of_den_le_4838](../../Erdos249257/CertificateKernel.lean#L15664)
- Lean declaration: [tsum_totient_div_pow_two_ne_int_div_of_den_le_248672326362367909](../../Erdos249257/CertificateKernel.lean#L18324)
- Lean declaration: [tsum_totient_div_pow_two_ne_ratCast_of_den_le_4194304](../../Erdos249257/CertificateKernel.lean#L18357)
- Lean declaration: [tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053](../../Erdos249257/CertificateKernel.lean#L18371)

- outgoing **generated_by**: [Z34::totient_carry_window_exact_recurrences](BROWSER_Z34_1.md#node-e27725845e1b2fc9). The bounded exclusions are finite certificate instances evaluated through the exact binary totient carry field.
- outgoing **generated_by**: [Z34::gap_band_real_sandwich](BROWSER_Z34_1.md#node-6de655e78c4b0acf). The larger Farey-gap windows use the real sandwich as the final strict-between-integers consumer.
- outgoing **finite_instance_of**: [Z34::linear_growth_coefficient_near_integer_consumer](BROWSER_Z34_1.md#node-a475c7c536f760c3). Each numerical denominator bound is a bounded instantiation of the generic three-window near-integer certificate architecture, not a cofinal supply.

<a id="node-6de655e78c4b0acf"></a>
## gap_band_real_sandwich

PROVED ABSTRACTLY: if bL*j+W=qU, W is nonnegative, a positive remainder s is bounded by (C+D)/bL, and W+q(C+D)<bL, then q(U/bL+s) lies strictly between the adjacent integers j and j+1.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: This private lemma is only the abstract final sandwich. It does not establish any of its arithmetic or tail-bound hypotheses for a totient window.

- Lean declaration: [gap_band_sandwich](../../Erdos249257/CertificateKernel.lean#L15726)

- incoming **generated_by**: [Z34::finite_totient_denominator_exclusion_instances](BROWSER_Z34_1.md#node-4b822ff8dcb32b90). The larger Farey-gap windows use the real sandwich as the final strict-between-integers consumer.

<a id="node-0ccbe66280ebf953"></a>
## linear_geometric_envelope_exact_bound

PROVED: for 0<=x<1 the series sum_t (C+t)x^t is summable, and for x<=1/2 its sum is at most 2C+2.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The theorem only bounds a generic analytic envelope. Its application to a certificate still needs a coefficient growth bound and arithmetic window data.

- Lean declaration: [summable_const_add_mul_geometric](../../Erdos249257/CertificateKernel.lean#L6387)
- Lean declaration: [tsum_const_add_mul_geometric_le](../../Erdos249257/CertificateKernel.lean#L6403)

- incoming **generated_by**: [Z34::divisor_count_series_carry_and_far_tail](BROWSER_Z34_1.md#node-718cff587a049636). The divisor-count far-tail bound uses tau(n)<=n and the linear-times-geometric envelope.

<a id="node-a475c7c536f760c3"></a>
## linear_growth_coefficient_near_integer_consumer

PROVED CONDITIONAL: under c(m)<=Gm, the natural coefficient series and shifted tails are summable, b^N dilation has an integer-prefix decomposition, the far tail is at most G(N+L+2)/b^L, and a first-block divisibility plus weighted-middle certificate satisfying q(C+G(N+L+2))<b^L yields a strictly positive distance below 1/q from an integer.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The near-integer theorem consumes a complete finite certificate. It does not construct certificates or prove a cofinal supply for #249 or arbitrary-support #257.

Open hypotheses: ["a cofinal supply of first-block divisibility and middle-window certificates at every requested precision"]

- Lean declaration: [summable_coeff_term_linear](../../Erdos249257/CertificateKernel.lean#L12050)
- Lean declaration: [summable_coeff_shift_tail_linear](../../Erdos249257/CertificateKernel.lean#L12064)
- Lean declaration: [bpow_mul_coeff_series_eq_int_add_tail_linear](../../Erdos249257/CertificateKernel.lean#L12079)
- Lean declaration: [coeff_far_tail_le_linear](../../Erdos249257/CertificateKernel.lean#L12111)
- Lean declaration: [near_int_witness_of_weighted_coeff_block_certificate_linear](../../Erdos249257/CertificateKernel.lean#L12157)

- outgoing **generalises**: [Z34::unit_linear_growth_coefficient_tail_package](BROWSER_Z34_1.md#node-08246a9579cc9b06). The G-linear package extends the unit-growth analytic tail and near-integer interface from c(m)<=m to c(m)<=Gm.
- outgoing **depends_on_open**: [Z34::weighted_middle_progression_total](BROWSER_Z34_1.md#node-3cf1febd75f5add7). A concrete application must supply first-block divisibility and a selected middle-window bound at every requested precision.
- incoming **finite_instance_of**: [Z34::finite_totient_denominator_exclusion_instances](BROWSER_Z34_1.md#node-4b822ff8dcb32b90). Each numerical denominator bound is a bounded instantiation of the generic three-window near-integer certificate architecture, not a cofinal supply.

<a id="node-3f916bc2070aa5b6"></a>
## natural_quotient_denominator_formulas

PROVED: the reduced denominator of x/y is y when x and y are coprime, and in general is y/gcd(x,y), for natural x and nonzero y viewed in the rationals.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: These formulas expose denominators of finite rational quantities only. They do not prove any infinite series irrational.

- Lean declaration: [den_natCast_div_natCast_of_coprime](../../Erdos249257/CertificateKernel.lean#L5167)
- Lean declaration: [den_natCast_div_natCast](../../Erdos249257/CertificateKernel.lean#L5189)

- incoming **complements**: [Z34::strict_support_mersenne_tail_package](BROWSER_Z34_1.md#node-bfcc70596e127520). The sparse-support lane needs both analytic tail control and exact finite rational-denominator control; neither substitutes for the other.

<a id="node-ef467ce0172bb237"></a>
## one_extra_orbit_preserves_nat_weight_residue

PROVED: one extra slot beyond complete periodic cycles contributes exactly the origin value; consequently multiplying a coprime cofactor R by p^(b*phi(m)) preserves both filtered divisor counts and m-periodic natural weighted coefficients modulo b.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem constructs residue transport for one prime-power orbit. It does not place that orbit inside a global certificate progression or establish irrationality.

- Lean declaration: [card_filter_range_mul_succ_of_periodic](../../Erdos249257/CertificateKernel.lean#L11918)
- Lean declaration: [card_filter_divisors_modEq_of_periodic_extra_orbit](../../Erdos249257/CertificateKernel.lean#L11943)
- Lean declaration: [weightedCoeff_modEq_of_periodic_extra_orbit](../../Erdos249257/CertificateKernel.lean#L12013)

- outgoing **complements**: [Z34::periodic_predicate_prime_power_cycle_divisibility](BROWSER_Z34_1.md#node-6f721a207eb169a6). Complete cycles provide divisibility, whereas one extra exponent preserves a protected nonzero residue.
- outgoing **generated_by**: [Z34::bounded_eventually_periodic_weight_calculus](BROWSER_Z34_1.md#node-923980c7ebbd3931). The weighted residue theorem lifts the predicate-level one-extra-orbit count through the layer-cake decomposition.
- incoming **generalises**: [Z34::signed_periodic_extra_orbit_protected_residue](BROWSER_Z34_1.md#node-2c1ea88f764a4a44). The signed theorem transports the same one-extra-orbit residue through positive/negative decomposition and integer congruences.

<a id="node-6f721a207eb169a6"></a>
## periodic_predicate_prime_power_cycle_divisibility

PROVED: periodic predicates respect addition of period multiples and congruence; their counts over complete cycles multiply exactly; filtered divisors at p^E R decompose along the p-power fibre; and exact valuations w*phi(m)-1 across selected primes force w^|P| divisibility of the filtered divisor count.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The divisibility theorem consumes exact prime valuations and a periodic predicate. It does not construct a certificate frame or apply to aperiodic supports.

- Lean declaration: [periodic_pred_add_mul](../../Erdos249257/CertificateKernel.lean#L10799)
- Lean declaration: [periodic_pred_iff_of_modEq](../../Erdos249257/CertificateKernel.lean#L10813)
- Lean declaration: [card_filter_range_mul_of_periodic](../../Erdos249257/CertificateKernel.lean#L10828)
- Lean declaration: [card_filter_divisors_prime_pow_mul_eq_sum](../../Erdos249257/CertificateKernel.lean#L10864)
- Lean declaration: [bpow_dvd_card_filter_divisors_of_periodic_block](../../Erdos249257/CertificateKernel.lean#L10982)
- Lean declaration: [certificate_param_arithmetic_periodic](../../Erdos249257/CertificateKernel.lean#L11260)

- outgoing **specialises**: [Z34::support_coefficient_growth_cast_and_summability](BROWSER_Z34_1.md#node-734a60714243bcd7). A periodic support indicator turns the support coefficient into the filtered divisor count controlled by complete prime-power cycles.
- incoming **complements**: [Z34::one_extra_orbit_preserves_nat_weight_residue](BROWSER_Z34_1.md#node-ef467ce0172bb237). Complete cycles provide divisibility, whereas one extra exponent preserves a protected nonzero residue.

<a id="node-94ac03f726830cc9"></a>
## pigeonhole_harmonic_parameter_closure

PROVED: a finite sum bound selects one value at most the average; dyadic bucketing bounds sum_{d<=S} floor(Y/d) and its +1 variant when S<=2^J; and an explicit exponential schedule dominates the required linear parameter cost.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: These close abstract parameter inequalities only after their finite-window inputs are supplied. They are not an irrationality theorem.

- Lean declaration: [exists_le_div_of_sum_le](../../Erdos249257/CertificateKernel.lean#L7541)
- Lean declaration: [param_linear_le_two_pow](../../Erdos249257/CertificateKernel.lean#L7611)
- Lean declaration: [harmonic_div_sum_core](../../Erdos249257/CertificateKernel.lean#L7629)
- Lean declaration: [harmonic_div_sum_le](../../Erdos249257/CertificateKernel.lean#L7685)

- incoming **complements**: [Z34::weighted_middle_progression_total](BROWSER_Z34_1.md#node-3cf1febd75f5add7). The total bound becomes a usable single-frame middle certificate only after averaging and harmonic parameter compression.

<a id="node-4cc1fc0e32898088"></a>
## pointwise_middle_bound_implies_weighted_bound

PROVED: a uniform pointwise divisor-count bound B on the middle window K<r<=L implies the weighted bound sum tau(N+r)b^(L-r) <= B b^(L-K).

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This converts a supplied middle-window bound; it does not establish such a bound for any certificate frame.

- Lean declaration: [weighted_middle_bound_of_pointwise](../../Erdos249257/CertificateKernel.lean#L6736)


<a id="node-2b127bbe71930939"></a>
## rational_distance_and_full_block_near_integer_consumers

PROVED CONDITIONAL: a nonzero rational discrepancy from an integer after b^N dilation is at least the reciprocal reduced denominator; a full-block signed certificate places the dilated series within 1/q of an integer without asserting nonzero distance; and a terminating base-b value within 1/b^k of an integer snaps exactly to that integer.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The full-block consumer explicitly does not prove the near-integer distance is nonzero. It yields a dichotomy only when combined with separate rational nontermination or terminating-value analysis and a certificate supply.

Open hypotheses: ["a full-block certificate supply at all requested precisions for the intended signed coefficient sequence"]

- Lean declaration: [inv_den_le_abs_bpow_mul_sub_intCast](../../Erdos249257/CertificateKernel.lean#L13740)
- Lean declaration: [near_int_of_int_coeff_full_block_certificate](../../Erdos249257/CertificateKernel.lean#L13791)
- Lean declaration: [bpow_mul_eq_intCast_of_abs_sub_lt_inv_bpow](../../Erdos249257/CertificateKernel.lean#L14291)

- outgoing **generated_by**: [Z34::signed_linear_growth_tail_package](BROWSER_Z34_1.md#node-3ea4d8f7f5964f9a). The full-block near-integer bound uses the signed integer-prefix decomposition and absolute far-tail estimate.
- outgoing **complements**: [Z34::signed_periodic_extra_orbit_protected_residue](BROWSER_Z34_1.md#node-2c1ea88f764a4a44). Full-block certificates allow zero distance and rely on rational nontermination, whereas a protected residue supplies explicit non-cancellation when it can be integrated into the frame.

<a id="node-3ea4d8f7f5964f9a"></a>
## signed_linear_growth_tail_package

PROVED: integer casts have the expected absolute-value and exact-division normal forms; a signed coefficient sequence with |c(m)|<=Gm has summable terms and shifted tails, an integer-prefix decomposition after b^N dilation, and far-tail absolute value at most G(N+L+2)/b^L; bounded signed Mersenne weights are summable.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The package controls analytic error for signed sequences but supplies neither non-cancellation nor arithmetic block certificates.

- Lean declaration: [abs_intCast_eq_natAbs_cast](../../Erdos249257/CertificateKernel.lean#L13216)
- Lean declaration: [summable_int_coeff_term](../../Erdos249257/CertificateKernel.lean#L13222)
- Lean declaration: [summable_int_coeff_shift_tail](../../Erdos249257/CertificateKernel.lean#L13234)
- Lean declaration: [bpow_mul_int_coeff_series_eq_int_add_tail](../../Erdos249257/CertificateKernel.lean#L13247)
- Lean declaration: [int_coeff_far_tail_abs_le](../../Erdos249257/CertificateKernel.lean#L13278)
- Lean declaration: [int_cast_div_real](../../Erdos249257/CertificateKernel.lean#L13329)
- Lean declaration: [summable_intWeightedErdos_term](../../Erdos249257/CertificateKernel.lean#L13608)

- incoming **generated_by**: [Z34::rational_distance_and_full_block_near_integer_consumers](BROWSER_Z34_1.md#node-2b127bbe71930939). The full-block near-integer bound uses the signed integer-prefix decomposition and absolute far-tail estimate.

<a id="node-2c1ea88f764a4a44"></a>
## signed_periodic_extra_orbit_protected_residue

PROVED LOCAL PRODUCER: natural congruences cast to integer congruences; an m-periodic signed weight transports its cofactor coefficient modulo any M through one extra p-orbit; any positive weight residue not divisible by M yields a coefficient residue seed, and therefore some protected extra-orbit witness not divisible by M.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Non-cancellation is achieved only in isolation. The source explicitly leaves the cofactor uncontrolled by the CRT frame, so this does not produce a complete certificate or an irrationality theorem.

Open hypotheses: ["integration of the protected-residue cofactor into the simultaneously constrained CRT certificate-frame progression"]

- Lean declaration: [int_modEq_of_nat_modEq](../../Erdos249257/CertificateKernel.lean#L13059)
- Lean declaration: [intWeightedCoeff_modEq_of_periodic_extra_orbit](../../Erdos249257/CertificateKernel.lean#L13073)
- Lean declaration: [intWeightedCoeff_eq_weight_of_zero_below](../../Erdos249257/CertificateKernel.lean#L13116)
- Lean declaration: [exists_pos_intWeightedCoeff_not_dvd](../../Erdos249257/CertificateKernel.lean#L13132)
- Lean declaration: [exists_pos_intWeightedCoeff_ne_zero](../../Erdos249257/CertificateKernel.lean#L13165)
- Lean declaration: [exists_intWeightedCoeff_extra_orbit_witness_not_dvd](../../Erdos249257/CertificateKernel.lean#L13180)

- outgoing **generalises**: [Z34::one_extra_orbit_preserves_nat_weight_residue](BROWSER_Z34_1.md#node-ef467ce0172bb237). The signed theorem transports the same one-extra-orbit residue through positive/negative decomposition and integer congruences.
- outgoing **generated_by**: [Z34::signed_weight_coefficient_decomposition_and_growth](BROWSER_Z34_1.md#node-43797390a044fbfb). Signed protected residues use the exact positive/negative coefficient decomposition and its bounded-growth control.
- incoming **complements**: [Z34::rational_distance_and_full_block_near_integer_consumers](BROWSER_Z34_1.md#node-2b127bbe71930939). Full-block certificates allow zero distance and rely on rational nontermination, whereas a protected residue supplies explicit non-cancellation when it can be integrated into the frame.

<a id="node-43797390a044fbfb"></a>
## signed_weight_coefficient_decomposition_and_growth

PROVED: a signed divisor coefficient is the difference of the natural coefficients of the positive and negative parts; finite natAbs obeys the triangle inequality; and a signed weight bounded by W has coefficient absolute value at most W*tau(n) and hence at most Wn.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: These bounds prepare the signed analytic lane but neither control cancellation sharply nor supply modular certificate frames.

- Lean declaration: [intWeightedCoeff_eq_weightedCoeff_sub](../../Erdos249257/CertificateKernel.lean#L12989)
- Lean declaration: [natAbs_sum_le_sum_natAbs](../../Erdos249257/CertificateKernel.lean#L13000)
- Lean declaration: [natAbs_intWeightedCoeff_le_mul_card_divisors](../../Erdos249257/CertificateKernel.lean#L13012)
- Lean declaration: [natAbs_intWeightedCoeff_le_mul_self](../../Erdos249257/CertificateKernel.lean#L13025)

- incoming **generated_by**: [Z34::signed_periodic_extra_orbit_protected_residue](BROWSER_Z34_1.md#node-2c1ea88f764a4a44). Signed protected residues use the exact positive/negative coefficient decomposition and its bounded-growth control.

<a id="node-40270dd432d25935"></a>
## signed_weight_negation_symmetry

PROVED: negating an integer weight negates both its signed divisor coefficient and its signed weighted Mersenne series.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Negation transports statements between signs but supplies no positivity, periodicity, or certificate existence.

- Lean declaration: [intWeightedCoeff_neg](../../Erdos249257/CertificateKernel.lean#L14627)
- Lean declaration: [intWeightedErdosSeries_neg](../../Erdos249257/CertificateKernel.lean#L14633)


<a id="node-a787a04c2dabf456"></a>
## stern_brocot_zero_run_mass_fixture

PROVED FINITE INSTANCE: the Stern–Brocot zero-run cylinder mass is exactly 1/4; together with the source definition this records the root contribution, while the one-run layer is handled separately.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: This is one boundary fixture. It proves no asymptotic mass limit, cylinder estimate, or irrationality statement by itself.

- Lean declaration: [stern_brocot_zero_run_mass_eq_quarter](../../Erdos249257/CertificateKernel.lean#L18739)


<a id="node-bfcc70596e127520"></a>
## strict_support_mersenne_tail_package

PROVED: along any strictly increasing positive support and integer base b>=2, the Mersenne reciprocal terms and every shifted tail are summable, every term and tail is positive, the tail after k is at most 4 b^(-a_k), and the finite rational support sum casts to the corresponding real partial sum.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The estimates hold for a chosen strictly increasing enumeration. They do not provide the denominator-growth or certificate supply needed for arbitrary-support irrationality.

- Lean declaration: [strictMono_add_le_apply](../../Erdos249257/CertificateKernel.lean#L5330)
- Lean declaration: [summable_erdos_term](../../Erdos249257/CertificateKernel.lean#L5449)
- Lean declaration: [summable_erdos_term_shift](../../Erdos249257/CertificateKernel.lean#L5485)
- Lean declaration: [erdos_term_pos](../../Erdos249257/CertificateKernel.lean#L5491)
- Lean declaration: [erdos_tail_pos](../../Erdos249257/CertificateKernel.lean#L5504)
- Lean declaration: [erdos_tail_le](../../Erdos249257/CertificateKernel.lean#L5514)
- Lean declaration: [finiteErdosSum_image_range_cast](../../Erdos249257/CertificateKernel.lean#L5575)

- outgoing **complements**: [Z34::natural_quotient_denominator_formulas](BROWSER_Z34_1.md#node-3f916bc2070aa5b6). The sparse-support lane needs both analytic tail control and exact finite rational-denominator control; neither substitutes for the other.
- incoming **specialises**: [Z34::factorial_and_power_two_prefix_lcm_exact](BROWSER_Z34_1.md#node-e5de60ee9c422d4b). The two exact LCM families are concrete sparse supports to which the generic strict-support analytic package applies.

<a id="node-734a60714243bcd7"></a>
## support_coefficient_growth_cast_and_summability

PROVED: the support coefficient f_A(n) is at most n, its real cast is the divisor sum of the support indicator, and the Mersenne support-series indicator terms are summable uniformly over every support A at every integer base b>=2.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These facts make the generic coefficient engine applicable but do not supply its cofinal block certificates for an arbitrary infinite support.

- Lean declaration: [supportCoeff_le_self](../../Erdos249257/CertificateKernel.lean#L8868)
- Lean declaration: [supportCoeff_cast_eq_sum_indicator](../../Erdos249257/CertificateKernel.lean#L8881)
- Lean declaration: [summable_erdosSupport_indicator](../../Erdos249257/CertificateKernel.lean#L8902)

- outgoing **specialises**: [Z34::unit_linear_growth_coefficient_tail_package](BROWSER_Z34_1.md#node-08246a9579cc9b06). The support coefficient satisfies the unit linear-growth hypothesis and therefore enters the generic natural-coefficient carry package.
- incoming **specialises**: [Z34::periodic_predicate_prime_power_cycle_divisibility](BROWSER_Z34_1.md#node-6f721a207eb169a6). A periodic support indicator turns the support coefficient into the filtered divisor count controlled by complete prime-power cycles.

<a id="node-9d733f11036a1172"></a>
## support_cut_prefix_and_filter_normal_forms

PROVED: a support indicator splits pointwise at any finite cut, the finite prefix of the resulting Mersenne series is rational, and the support coefficient equals the cardinality of the support-filtered divisor set under any decidable membership instance.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Finite-prefix rationality does not determine the irrationality of the remaining infinite tail. The filter form is a coordinate bridge, not a certificate.

- Lean declaration: [indicator_support_split_at_cut](../../Erdos249257/CertificateKernel.lean#L9396)
- Lean declaration: [prefix_sum_eq_rat_cast](../../Erdos249257/CertificateKernel.lean#L9446)
- Lean declaration: [supportCoeff_eq_card_filter](../../Erdos249257/CertificateKernel.lean#L9543)

- incoming **generated_by**: [Z34::support_sieve_budget_and_disjoint_blocks](BROWSER_Z34_1.md#node-ef20b27ddb68fc65). The sieve lane works in the exact divisor-filter representation and separates finite rational prefixes from the infinite tail.

<a id="node-ef20b27ddb68fc65"></a>
## support_sieve_budget_and_disjoint_blocks

PROVED: progression hit counts admit a reciprocal-budget bound; exponential growth eventually dominates any prescribed linear parameter cost; a support divisor forces positive support coefficient; weighted hit sets have a geometric bound; and an infinite pairwise-coprime support supplies arbitrarily large, pairwise-disjoint blocks whose products remain coprime.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The family prepares one sparse-support certificate route. It does not cover arbitrary supports, and in particular does not remove the reciprocal-summability restriction from the pairwise-coprime lane.

- Lean declaration: [sum_div_add_one_cast_le](../../Erdos249257/CertificateKernel.lean#L9613)
- Lean declaration: [exists_linear_lt_pow](../../Erdos249257/CertificateKernel.lean#L9746)
- Lean declaration: [supportCoeff_pos_of_mem_dvd](../../Erdos249257/CertificateKernel.lean#L9768)
- Lean declaration: [sum_pow_weight_window_hits_le](../../Erdos249257/CertificateKernel.lean#L9778)
- Lean declaration: [coprime_prod_prod_of_pairwise_disjoint](../../Erdos249257/CertificateKernel.lean#L9798)
- Lean declaration: [coprime_prod_of_pairwise_notMem](../../Erdos249257/CertificateKernel.lean#L9812)
- Lean declaration: [exists_disjoint_support_blocks](../../Erdos249257/CertificateKernel.lean#L9826)

- outgoing **generated_by**: [Z34::support_cut_prefix_and_filter_normal_forms](BROWSER_Z34_1.md#node-9d733f11036a1172). The sieve lane works in the exact divisor-filter representation and separates finite rational prefixes from the infinite tail.

<a id="node-e27725845e1b2fc9"></a>
## totient_carry_window_exact_recurrences

PROVED: the binary weighted totient carry sum has an exact Icc-to-range form; increasing the window doubles the prior carry and adds the new totient; splitting the bottom slot separates 2^K phi(N+1); and shifting N satisfies T_K(N+1)+2^K phi(N+1)=2T_K(N)+phi(N+K+1).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These identities describe the carry field but do not show that any window is killed, non-integral, or cofinally useful.

- Lean declaration: [totient_carry_sum_eq_range](../../Erdos249257/CertificateKernel.lean#L15153)
- Lean declaration: [totient_carry_sum_succ_window](../../Erdos249257/CertificateKernel.lean#L15171)
- Lean declaration: [totient_carry_sum_bottom_split](../../Erdos249257/CertificateKernel.lean#L15191)
- Lean declaration: [totient_carry_sum_succ_shift](../../Erdos249257/CertificateKernel.lean#L15214)

- incoming **generated_by**: [Z34::finite_totient_denominator_exclusion_instances](BROWSER_Z34_1.md#node-4b822ff8dcb32b90). The bounded exclusions are finite certificate instances evaluated through the exact binary totient carry field.

<a id="node-08246a9579cc9b06"></a>
## unit_linear_growth_coefficient_tail_package

PROVED: any natural coefficient sequence satisfying c(m)<=m has a summable base-b series and shifted tails, an exact integer-prefix plus shifted-tail decomposition after multiplication by b^N, and a far-tail bound (N+L+2)/b^L.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The package assumes a coefficient growth envelope and gives no divisibility or middle-window certificate.

- Lean declaration: [summable_coeff_term](../../Erdos249257/CertificateKernel.lean#L8358)
- Lean declaration: [summable_coeff_shift_tail](../../Erdos249257/CertificateKernel.lean#L8385)
- Lean declaration: [bpow_mul_coeff_series_eq_int_add_tail](../../Erdos249257/CertificateKernel.lean#L8405)
- Lean declaration: [coeff_far_tail_le](../../Erdos249257/CertificateKernel.lean#L8437)

- incoming **specialises**: [Z34::support_coefficient_growth_cast_and_summability](BROWSER_Z34_1.md#node-734a60714243bcd7). The support coefficient satisfies the unit linear-growth hypothesis and therefore enters the generic natural-coefficient carry package.
- incoming **generalises**: [Z34::linear_growth_coefficient_near_integer_consumer](BROWSER_Z34_1.md#node-a475c7c536f760c3). The G-linear package extends the unit-growth analytic tail and near-integer interface from c(m)<=m to c(m)<=Gm.

<a id="node-3cf1febd75f5add7"></a>
## weighted_middle_progression_total

PROVED: the geometric weight of K<r<=L is at most b^(L-K), and combining it with the coprime progression divisor average bounds the total weighted middle-window mass across all y<Y.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The result controls the sum over a finite search window. Selecting a single frame and closing all certificate inequalities requires the separate pigeonhole and parameter package.

- Lean declaration: [sum_pow_weight_middle_window_le](../../Erdos249257/CertificateKernel.lean#L7464)
- Lean declaration: [sum_weighted_middle_window_le](../../Erdos249257/CertificateKernel.lean#L7492)

- outgoing **generated_by**: [Z34::coprime_progression_divisor_average](BROWSER_Z34_1.md#node-4361c3f9c742b378). The weighted total combines the progression divisor average with the geometric sum of window weights.
- outgoing **complements**: [Z34::pigeonhole_harmonic_parameter_closure](BROWSER_Z34_1.md#node-94ac03f726830cc9). The total bound becomes a usable single-frame middle certificate only after averaging and harmonic parameter compression.
- incoming **depends_on_open**: [Z34::linear_growth_coefficient_near_integer_consumer](BROWSER_Z34_1.md#node-a475c7c536f760c3). A concrete application must supply first-block divisibility and a selected middle-window bound at every requested precision.

