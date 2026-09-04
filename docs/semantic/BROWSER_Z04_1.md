# Z04_1: Radical Mobius shadow: repunit numerators, cyclotomic fibres and Mersenne channel denominators

[All problems and zones](BROWSER.md)

<a id="node-79927919cb25bf2e"></a>
## associated_residues_share_gcd

Two integers whose residues are associated modulo M have the same gcd with M.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [gcd_natAbs_eq_of_associated_mod](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L394)
- Lean declaration: [associated_modulus_dvd_natAbs](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L366)
- Lean declaration: [associated_modulus_dvd_natAbs_iff](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L386)


<a id="node-6c01e9e3e3337773"></a>
## base_shadow_generic_reduced_denominator

The reduced denominator of the unscaled radical shadow B(r) = M_r/(2^r - 1) is (2^r - 1) divided by gcd(|M_r|, 2^r - 1), for every positive r; a kernel-checked gcd certificate therefore yields the reduced denominator immediately.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [baseMobiusShadow_den](../../Erdos249257/RadicalMobiusShadow.lean#L150)
- Lean declaration: [baseMobiusShadow_den_of_gcd_eq](../../Erdos249257/RadicalMobiusShadow.lean#L163)

- incoming **finite_instance_of**: [Z04::radical_shadow_denominator_fixtures](BROWSER_Z04_2.md#node-653a407fa7311f76). Each fixture certifies one gcd and reads the denominator off the generic formula at a fixed exponent.

<a id="node-3ab4198efd124e07"></a>
## base_two_subgroup_sum_coprime_q2_minus_1

For an odd prime q the base-two evaluated subgroup sum, the geometric sum of (2^{r/q})^j for j < q, is coprime to q^2 - 1.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Odd primes q only; the binary prime is handled separately and genuinely differently.

- Lean declaration: [baseTwoRepunit_coprime_prime_sq_sub_one](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L58)

- outgoing **implies**: [Z04::odd_local_cofactor_unit_mod_mersenne](BROWSER_Z04_1.md#node-c132bba476a8a1ae). Coprimality of the evaluated subgroup sum to q^2 - 1 is the first of the two cases in the cofactor argument.

<a id="node-2cd6c0ee65c42dd5"></a>
## bertrand_supplies_upper_half_prime

For every t at least 2 the upper-half prime family, the primes in the half-open interval (t/2, t], is nonempty.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [upperHalfPrimes_nonempty](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L50)

- outgoing **implies**: [Z04::upper_half_channel_product_growth](BROWSER_Z04_2.md#node-37618ef352954ce3). The 2^{t/2} bound needs at least one prime in the upper half, supplied by Bertrand's postulate.

<a id="node-1dae52d1d151218a"></a>
## binary_factor_squarefree_sharpness

At r = 4 the binary local numerator factor has gcd 3 with 2^4 - 1, so the squarefree hypothesis in the binary unit theorem cannot be dropped.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: A single witness at r = 4. It shows the hypothesis is necessary; it does not describe how the unit statement fails in general for nonsquarefree exponents.

- Lean declaration: [localNumeratorValue_four_gcd](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L271)

- outgoing **barrier_for**: [Z04::binary_local_numerator_unit_mod_mersenne](BROWSER_Z04_1.md#node-84baf32a0a60fe2c). The r = 4 computation blocks the nonsquarefree extension of the binary unit statement, not the statement itself: with squarefreeness dropped the binary factor can share the factor 3 with 2^r - 1.

<a id="node-84baf32a0a60fe2c"></a>
## binary_local_numerator_unit_mod_mersenne

For squarefree even r, the binary local numerator factor equals 2*2^{r/2} + 1 and is coprime to 2^r - 1, hence a unit in Z/(2^r - 1); squarefreeness enters by making r/2 odd.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Requires r squarefree and even; the companion finite instance shows the conclusion is false at r = 4.

- Lean declaration: [localNumeratorValue_two_coprime_mersenne](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L194)
- Lean declaration: [localNumeratorValue_two_isUnit_mod_mersenne](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L261)

- outgoing **implies**: [Z04::mobius_numerator_odd_jordan_normal_form](BROWSER_Z04_1.md#node-5ad37c71844c9ba7). The binary factor contributes 1 to the association precisely because it is itself a unit.
- incoming **barrier_for**: [Z04::binary_factor_squarefree_sharpness](BROWSER_Z04_1.md#node-1dae52d1d151218a). The r = 4 computation blocks the nonsquarefree extension of the binary unit statement, not the statement itself: with squarefreeness dropped the binary factor can share the factor 3 with 2^r - 1.

<a id="node-b2d494fcd28ce3db"></a>
## cyclic_subgroup_sum_idempotence

In the cyclic algebra Z[X]/(X^r - 1), for q | r the order-q subgroup sum is idempotent up to scale: X^r - 1 divides the square of the subgroup sum minus q times the subgroup sum.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [cyclicModulus_dvd_subgroupSum_sq_sub_smul](../../Erdos249257/CyclicTensorMobiusShadow.lean#L87)
- Lean declaration: [subgroupSum_mul_X_pow_sub_one](../../Erdos249257/CyclicTensorMobiusShadow.lean#L57)
- Lean declaration: [X_pow_sub_one_dvd_subgroupSum_sub_C](../../Erdos249257/CyclicTensorMobiusShadow.lean#L67)

- outgoing **implies**: [Z04::local_factor_adjugate_identity](BROWSER_Z04_1.md#node-eba1e88fe513fda8). Multiplying out A_q * B_q leaves q^2 times the idempotence defect, so scaled idempotence gives the adjugate identity.

<a id="node-181415fcf1bd9103"></a>
## cyclic_tensor_factorisation

For squarefree r the Mobius numerator polynomial factors, modulo X^r - 1, as the product over the primes q | r of the local numerator factors q*Sigma_q - 1: X^r - 1 divides the numerator minus that product.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Squarefree exponents only; a congruence modulo X^r - 1, not a factorisation in Z[X].

- Lean declaration: [cyclicModulus_dvd_mobiusNumeratorPolynomial_sub_numeratorFactorProduct](../../Erdos249257/CyclicTensorMobiusShadow.lean#L267)
- Lean declaration: [expand_cyclicModulus](../../Erdos249257/CyclicTensorMobiusShadow.lean#L219)
- Lean declaration: [localNumeratorFactor_mul_prime](../../Erdos249257/CyclicTensorMobiusShadow.lean#L224)
- Lean declaration: [numeratorFactorProduct_mul_prime](../../Erdos249257/CyclicTensorMobiusShadow.lean#L233)
- Lean declaration: [subgroupSum_mul_prime_at_prime](../../Erdos249257/CyclicTensorMobiusShadow.lean#L252)
- Lean declaration: [subgroupSum_mul_cyclicModulus](../../Erdos249257/CyclicTensorMobiusShadow.lean#L257)

- incoming **implies**: [Z04::fresh_prime_expansion_trivial_mod_cyclic](BROWSER_Z04_1.md#node-748b3efcf37d5355). The prime-adjunction induction step needs exactly that the fresh-prime expansion is trivial modulo the old cyclic modulus.
- incoming **implies**: [Z04::prime_jump_recurrence](BROWSER_Z04_2.md#node-e12586c9bfe0d246). The induction step rewrites the numerator at p*r by the T5 recurrence before matching it against the local factor at p.
- incoming **specialises**: [Z04::mersenne_local_product_congruence](BROWSER_Z04_1.md#node-6added433421e72f). Base-two evaluation of the polynomial factorisation modulo X^r - 1.

<a id="node-708596126e736d71"></a>
## cyclotomic_channel_divides_mersenne

The integer |Phi_m(2)| divides 2^m - 1 for every m, and at a prime p one has Phi_p(2) = 2^p - 1, so the prime cyclotomic channels are exactly the prime-index Mersenne channels.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [cyclotomicValue_dvd_mersenne](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L321)
- Lean declaration: [cyclotomicEval_prime](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L333)
- Lean declaration: [cyclotomicValue_prime](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L345)


<a id="node-7b000b61bd5cd228"></a>
## cyclotomic_fibre_congruence

T2. For squarefree r and every m | r, the cyclotomic polynomial Phi_m divides the Mobius numerator polynomial minus the constant mu(m) J2(r/m); evaluating at X = 2, the integer Phi_m(2) divides M_r - mu(m) J2(r/m), and at a prime channel p | r this reads 2^p - 1 divides M_r + J2(r/p).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Squarefree exponents only. The theorem locates the residue of M_r in each fibre; it makes no claim that the residue is nonzero except in the top fibre, handled separately.

- Lean declaration: [cyclotomic_dvd_mobiusNumeratorPolynomial_sub](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L299)
- Lean declaration: [mobiusNumerator_mod_cyclotomicEval](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L310)
- Lean declaration: [mobiusNumerator_mod_mersenne_prime](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L666)
- Lean declaration: [cyclotomicFibreConstant](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L193)
- Lean declaration: [cyclotomic_dvd_polynomial_sub_fibreConstant](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L199)
- Lean declaration: [cyclotomicFibreConstant_eq](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L225)

- incoming **implies**: [Z04::spaced_repunit_cyclotomic_factorisation](BROWSER_Z04_2.md#node-f2e70f884896b053). Applying the two repunit divisibility facts summand by summand over the divisors of r yields the fibre congruence.
- incoming **specialises**: [Z04::top_cyclotomic_fibre_noncollapse](BROWSER_Z04_2.md#node-871b019ccc4a3041). T3 is T2 at the top fibre m = r, where J2(1) = 1 leaves the unit mu(r).
- incoming **finite_instance_of**: [Z04::cyclotomic_projection_anchors](BROWSER_Z04_1.md#node-d460e6ba575ab792). The 210 anchors instantiate T2 and the 2310 anchor instantiates T3 at fixed squarefree exponents.
- outgoing **implies**: [Z04::upper_half_channel_coprime_numerator](BROWSER_Z04_2.md#node-8f7c56fd6ce01420). The prime-channel form of T2 puts M_r in the residue class of -J2(r/p), which is t-smooth and therefore coprime to the channel.

<a id="node-d460e6ba575ab792"></a>
## cyclotomic_projection_anchors

Kernel-checked instances of T2 at r = 210 in the fibres m = 105 and m = 210, and of T3 at r = 2310.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Two exponents only. These are elaboration anchors; they are not finite substitutes for T2 or T3 and carry no unbounded supply.

- Lean declaration: [t2_210_105_anchor](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L466)
- Lean declaration: [t2_210_210_anchor](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L473)
- Lean declaration: [t3_2310_anchor](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L480)
- Lean declaration: [squarefree_210](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L446)
- Lean declaration: [squarefree_2310](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L459)

- outgoing **finite_instance_of**: [Z04::cyclotomic_fibre_congruence](BROWSER_Z04_1.md#node-7b000b61bd5cd228). The 210 anchors instantiate T2 and the 2310 anchor instantiates T3 at fixed squarefree exponents.

<a id="node-748b3efcf37d5355"></a>
## fresh_prime_expansion_trivial_mod_cyclic

For squarefree r and a prime p not dividing r, the p-fold expansion acts trivially on the Mobius numerator polynomial modulo X^r - 1: X^r - 1 divides the numerator minus its p-fold expansion.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The transport lemma for prime-adjunction induction; it is an identity modulo X^r - 1 and carries no arithmetic non-cancellation content.

- Lean declaration: [cyclicModulus_dvd_mobiusNumeratorPolynomial_sub_expand](../../Erdos249257/CyclicTensorMobiusShadow.lean#L168)
- Lean declaration: [monic_dvd_of_map_rat_dvd](../../Erdos249257/CyclicTensorMobiusShadow.lean#L152)

- outgoing **implies**: [Z04::cyclic_tensor_factorisation](BROWSER_Z04_1.md#node-181415fcf1bd9103). The prime-adjunction induction step needs exactly that the fresh-prime expansion is trivial modulo the old cyclic modulus.

<a id="node-c092c8b802ee54ac"></a>
## gcd_word_coefficient_representation

The k-th natural coefficient used by the gcd-word polynomial at exponent r is (r/gcd(r,k)) times Euler's totient of gcd(r,k). This is the coefficient-level representation consumed by the squarefree repunit-numerator identity.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: This definition alone asserts neither the squarefree polynomial identity nor any denominator survival or irrationality conclusion.

- Lean declaration: [gcdWordCoeff](../../Erdos249257/RepunitMobiusNumerator.lean#L41)


<a id="node-849458230376eca8"></a>
## global_cofactor_adjugate

For squarefree r, multiplying the local adjugate identities gives that X^r - 1 divides the product of the local numerator factors times the product of the local cofactors minus J2(r), and combining with the tensor factorisation, that X^r - 1 divides the Mobius numerator polynomial times the cofactor product minus J2(r).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: An integral adjugate for the original numerator polynomial; it does not invert anything and does not bound any gcd by itself.

- Lean declaration: [cyclicModulus_dvd_numeratorFactorProduct_mul_cofactorProduct_sub_jordanTotientTwo](../../Erdos249257/CyclicTensorMobiusShadow.lean#L326)
- Lean declaration: [cyclicModulus_dvd_mobiusNumeratorPolynomial_mul_cofactorProduct_sub_jordanTotientTwo](../../Erdos249257/CyclicTensorMobiusShadow.lean#L347)
- Lean declaration: [dvd_finset_prod_sub_prod](../../Erdos249257/CyclicTensorMobiusShadow.lean#L125)

- outgoing **generalises**: [Z04::local_factor_adjugate_identity](BROWSER_Z04_1.md#node-eba1e88fe513fda8). The global adjugate is the product over the prime factors of the local adjugate identities.

<a id="node-836677eb3a6e6c9e"></a>
## jordan_totient_two_evaluation

The second Jordan totient J2 = mu * id^2 satisfies J2(1) = 1, equals the divisor sum of mu(d)(n/d)^2, is multiplicative, takes value p^2 - 1 at a prime, and on a squarefree argument equals the product of (q^2 - 1) over its prime factors, with the same product formula for its absolute value.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [jordanTotientTwo_one](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L37)
- Lean declaration: [jordanTotientTwo_eq_divisorSum](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L40)
- Lean declaration: [jordanTotientTwo_multiplicative](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L54)
- Lean declaration: [jordanTotientTwo_prime](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L59)
- Lean declaration: [jordanTotientTwo_eq_prod_primeFactors](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L67)
- Lean declaration: [jordanTotientTwo_natAbs_eq_prod](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L614)

- incoming **specialises**: [Z04::jordan_totient_two_prime_support_bound](BROWSER_Z04_1.md#node-32744181c63a823a). The support bound reads off the product formula J2(n) = product of (q^2 - 1) over the primes of n.

<a id="node-32744181c63a823a"></a>
## jordan_totient_two_prime_support_bound

If a squarefree n has all prime factors at most t and t is at least 3, then every prime dividing |J2(n)| is also at most t; the bound at t = 3 is exactly what absorbs the exceptional factor 3 coming from 2^2 - 1.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: A smoothness statement only; it does not say J2(n) is nonzero modulo any particular channel.

- Lean declaration: [jordanTotientTwo_natAbs_primeFactors_le](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L79)

- outgoing **specialises**: [Z04::jordan_totient_two_evaluation](BROWSER_Z04_1.md#node-836677eb3a6e6c9e). The support bound reads off the product formula J2(n) = product of (q^2 - 1) over the primes of n.

<a id="node-95a73146a64e09d8"></a>
## lcm_height_channel_product_divides_shadow_denominator

The finite family upperHalfPrimes(t) is exactly the primes p with t/2 < p <= t. T4 at the development's own object says: for H positive and t at least 5, with P a family of upper-half primes dividing rad(H) and rad(H) t-smooth, the surviving part of the channel product divides the reduced denominator of H * numericMobiusShadow H; when the residual scale H/rad(H) is t-smooth the whole product divides it; concretely, at H = H_t = lcm(1..t) with t at least 5, the product of 2^p - 1 over p in upperHalfPrimes(t) divides that reduced denominator.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Statement is about the explicit finite Mobius shadow only. It says nothing about the foreign diagonal defect (the part of the actual totient tail difference not captured by the finite shadow), so it does not bear on the irrationality of sum phi(n)/2^n on its own.

- Lean declaration: [upperHalfPrimes](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L914)
- Lean declaration: [scaledMobiusShadow_upperHalf_survivorProduct_dvd_den](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L924)
- Lean declaration: [scaledMobiusShadow_upperHalf_product_dvd_den_of_scale_primeFactors_le](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L957)
- Lean declaration: [lcmHeight_upperHalf_product_dvd_den](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L983)

- outgoing **specialises**: [Z04::upper_half_channel_survives_scaled_denominator](BROWSER_Z04_2.md#node-12d3b49c3ef22e0b). T4 instantiated at r = rad(H), h = H/rad(H), with all smoothness side conditions discharged from the LCM-height support facts.
- outgoing **implies**: [Z04::lcm_height_denominator_lower_bound](BROWSER_Z04_1.md#node-3b92aae867baea37). A divisor of a positive denominator is at most that denominator.
- incoming **specialises**: [Z04::single_channel_with_two_sided_bounds](BROWSER_Z04_2.md#node-d191586330a418a5). One Bertrand prime is selected from the surviving family and its single channel is bounded on both sides.

<a id="node-3b92aae867baea37"></a>
## lcm_height_denominator_lower_bound

For t at least 5, the reduced denominator of the scaled LCM-height Mobius shadow H_t * numericMobiusShadow H_t is at least 2^{t/2}.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: A denominator statement only. Denominator growth of the explicit shadow does not imply a channel miss and does not rule out cancellation by the foreign diagonal defect, so it does not prove Erdos 249.

- Lean declaration: [lcmHeight_scaledMobiusShadow_den_lower_bound](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L85)

- incoming **implies**: [Z04::lcm_height_channel_product_divides_shadow_denominator](BROWSER_Z04_1.md#node-95a73146a64e09d8). A divisor of a positive denominator is at most that denominator.
- incoming **implies**: [Z04::upper_half_channel_product_growth](BROWSER_Z04_2.md#node-37618ef352954ce3). The 2^{t/2} bound on the channel product transfers to the denominator that the product divides.
- incoming **implies**: [Z04::lcm_height_exact_denominator](BROWSER_Z04_1.md#node-6f532b908aa314db). The exact value determines the same denominator the growth statement only bounds below; deriving 2^{t/2} from the exact formula needs an unformalised comparison of h_t times the odd Jordan scalar against 2^{rad H_t}, so in Lean the two proofs remain independent.

<a id="node-6f532b908aa314db"></a>
## lcm_height_exact_denominator

At every LCM height t, the reduced denominator of H_t * numericMobiusShadow H_t is exactly (2^{r_t} - 1) divided by the gcd of 2^{r_t} - 1 with h_t times the absolute odd Jordan scalar of r_t, where r_t = rad(H_t) and h_t = H_t/r_t. The giant Mobius numerator is replaced completely by the scale times a small scalar.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Exact for the explicit finite shadow only. It computes a denominator; it does not show any real quantity is non-integral, and it says nothing about the foreign diagonal defect, so it does not prove Erdos 249. Also note the exactness is only as sharp as the gcd it displays: the formula does not by itself assert the gcd is small, and the accompanying lower bound 2^{t/2} is proved separately and is far weaker than 2^{rad(H_t)}.

- Lean declaration: [lcmHeight_scaledMobiusShadow_den_exact](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L147)
- Lean declaration: [primeFactors_thirty](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L127)
- Lean declaration: [primeFactors_sixty](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L137)

- outgoing **specialises**: [Z04::scaled_shadow_exact_denominator](BROWSER_Z04_2.md#node-a69b54b00ab84afd). Instantiation at r = rad(H_t) and h = H_t/rad(H_t).
- outgoing **implies**: [Z04::lcm_height_denominator_lower_bound](BROWSER_Z04_1.md#node-3b92aae867baea37). The exact value determines the same denominator the growth statement only bounds below; deriving 2^{t/2} from the exact formula needs an unformalised comparison of h_t times the odd Jordan scalar against 2^{rad H_t}, so in Lean the two proofs remain independent.
- incoming **finite_instance_of**: [Z04::lcm_height_five_fixtures](BROWSER_Z04_1.md#node-ff1306cc97da951d). t = 5 instance of the exact denominator, together with the height, radical, scale and channel-product values it uses.
- incoming **transport_of**: [Z05::exact_full_target_pincer](BROWSER_Z05_1.md#node-faace0186be92bf5). explicitLcmShadowRat t is defined as (lcmHeight t) * numericMobiusShadow (lcmHeight t) (DiagonalPincerDecomposition.lean:69), so the pincer modulus d_t = lcmShadowDenominator t is exactly the reduced denominator computed by lcmHeight_scaledMobiusShadow_den_exact.

<a id="node-ff1306cc97da951d"></a>
## lcm_height_five_fixtures

Kernel-checked boundary instances at t = 5: H_5 = 60, the upper-half prime family is {3, 5}, rad(H_5) = 30, the scale is 2, the surviving channel product is 217 = (2^3 - 1)(2^5 - 1), and the exact reduced denominator is (2^30 - 1)/3.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: One height only (t = 5). Pressure tests the through-t convention and the strict lower / inclusive upper endpoints of the upper-half interval.

- Lean declaration: [lcmHeight_five_fixture](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L843)
- Lean declaration: [upperHalfPrimes_five_fixture](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L919)
- Lean declaration: [lcmRadical_five_fixture](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L178)
- Lean declaration: [lcmScale_five_fixture](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L183)
- Lean declaration: [lcmHeight_five_scaledMobiusShadow_den_exact](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L187)
- Lean declaration: [upperHalfMersenneProduct_five_fixture](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L199)

- outgoing **finite_instance_of**: [Z04::lcm_height_exact_denominator](BROWSER_Z04_1.md#node-6f532b908aa314db). t = 5 instance of the exact denominator, together with the height, radical, scale and channel-product values it uses.

<a id="node-b96e30729807f7bb"></a>
## lcm_height_prime_support

The prime support of H_t = lcm(1..t) is exactly the primes at most t; H_t is positive; the residual scale h_t = H_t/rad(H_t) divides H_t and is t-smooth; a prime divides rad(H_t) iff it is at most t; and rad(H_t)/p divides H_t and is t-smooth for any p dividing rad(H_t).

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [prime_dvd_lcmHeight_iff](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L855)
- Lean declaration: [lcmScale_dvd_lcmHeight](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L879)
- Lean declaration: [lcmScale_primeFactors_le](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L885)
- Lean declaration: [prime_dvd_lcmRadical_iff](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L891)
- Lean declaration: [lcmRadical_div_dvd_lcmHeight](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L899)
- Lean declaration: [lcmRadical_div_primeFactors_le](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L906)
- Lean declaration: [lcmHeight_pos](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L872)
- Lean declaration: [lcmHeight_zero](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L834)
- Lean declaration: [lcmHeight_one](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L838)


<a id="node-eba1e88fe513fda8"></a>
## local_factor_adjugate_identity

For q | r the local numerator factor A_q = q*Sigma_q - 1 and the integral cofactor B_q = q*Sigma_q - (q^2 - 1) multiply to the scalar q^2 - 1 modulo X^r - 1; evaluating at X = 2 the same identity holds in Z/(2^r - 1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: An adjugate identity: it exhibits a cofactor, not an inverse, and asserts nothing about q^2 - 1 being invertible.

- Lean declaration: [cyclicModulus_dvd_localNumerator_mul_localCofactor_sub_scalar](../../Erdos249257/CyclicTensorMobiusShadow.lean#L105)
- Lean declaration: [localNumerator_mul_localCofactor_mod_mersenne](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L279)

- incoming **implies**: [Z04::cyclic_subgroup_sum_idempotence](BROWSER_Z04_1.md#node-b2d494fcd28ce3db). Multiplying out A_q * B_q leaves q^2 times the idempotence defect, so scaled idempotence gives the adjugate identity.
- incoming **generalises**: [Z04::global_cofactor_adjugate](BROWSER_Z04_1.md#node-849458230376eca8). The global adjugate is the product over the prime factors of the local adjugate identities.
- incoming **reformulates**: [Z04::local_factor_base_two_evaluation](BROWSER_Z04_1.md#node-ecd65be40232a146). The base-two values are the evaluations of the same two local factors whose adjugate identity is proved in the polynomial layer.

<a id="node-ecd65be40232a146"></a>
## local_factor_base_two_evaluation

Base-two evaluation of the local factors: the evaluated local numerator factor is q times the base-two repunit sum of 2^{r/q} minus 1, and the evaluated cofactor is the same product minus (q^2 - 1).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [localNumeratorValue_eq](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L41)
- Lean declaration: [localCofactorValue_eq](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L49)
- Lean declaration: [baseTwoRepunit_mul](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L35)

- outgoing **reformulates**: [Z04::local_factor_adjugate_identity](BROWSER_Z04_1.md#node-eba1e88fe513fda8). The base-two values are the evaluations of the same two local factors whose adjugate identity is proved in the polynomial layer.

<a id="node-f17a9973708c8994"></a>
## mersenne_channel_product_structure

Mersenne numbers at distinct prime indices are pairwise coprime, so for a finite family of primes all dividing r the product of their Mersenne channels divides 2^r - 1.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [coprime_mersenne_of_distinct_primes](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L700)
- Lean declaration: [channelProduct_dvd_mersenne](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L713)

- outgoing **implies**: [Z04::upper_half_channel_survives_scaled_denominator](BROWSER_Z04_2.md#node-12d3b49c3ef22e0b). Pairwise coprimality of prime-index Mersennes is what makes the channel product divide 2^r - 1.

<a id="node-6added433421e72f"></a>
## mersenne_local_product_congruence

Evaluating the tensor factorisation at X = 2: for squarefree r, 2^r - 1 divides M_r minus the product over the primes q | r of the evaluated local numerator factors.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Squarefree exponents only, and a congruence modulo 2^r - 1 only: it locates M_r's residue class but by itself bounds no gcd of M_r with 2^r - 1, and says nothing about the foreign diagonal defect.

- Lean declaration: [mersenne_dvd_mobiusNumerator_sub_localNumeratorProduct](../../Erdos249257/CyclicTensorMobiusShadow.lean#L366)

- outgoing **specialises**: [Z04::cyclic_tensor_factorisation](BROWSER_Z04_1.md#node-181415fcf1bd9103). Base-two evaluation of the polynomial factorisation modulo X^r - 1.
- outgoing **implies**: [Z04::mobius_numerator_odd_jordan_normal_form](BROWSER_Z04_1.md#node-5ad37c71844c9ba7). The normal form starts from the congruence M_r = product of local values modulo 2^r - 1.

<a id="node-3e689506ffab44c0"></a>
## mersenne_prime_divisor_lower_bound

For an odd prime p, every prime divisor of 2^p - 1 is at least 2p + 1; in particular it exceeds any scale t with t < 2p.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [prime_dvd_mersenne_gt_scale](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L460)
- Lean declaration: [prime_dvd_mersenne_lower_bound](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L517)

- outgoing **implies**: [Z04::smooth_numbers_coprime_to_upper_half_channel](BROWSER_Z04_2.md#node-87bf3ba93a5700a3). Every prime divisor of the channel exceeds 2p > t, so no t-smooth number can share a factor with it.

<a id="node-c933122f9ceb6d38"></a>
## mersenne_quotient_channel_congruence

For m | r with r positive, the integer Phi_m(2) divides (2^r - 1)/(2^m - 1) minus r/m; that is, the geometric Mersenne cofactor is congruent to its number of blocks in the m-th cyclotomic channel.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [mersenneQuotient_mod_cyclotomicEval](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L429)
- Lean declaration: [eval_spacedRepunit_two](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L405)

- outgoing **specialises**: [Z04::spaced_repunit_cyclotomic_factorisation](BROWSER_Z04_2.md#node-f2e70f884896b053). The congruence is the old-fibre repunit statement at d = m, evaluated at X = 2.

<a id="node-5ad37c71844c9ba7"></a>
## mobius_numerator_odd_jordan_normal_form

Base-two unit normal form: for squarefree r the Mobius numerator M_r is associated, in Z/(2^r - 1), to the odd Jordan scalar, the product of (q^2 - 1) over the odd primes q dividing r. The binary prime contributes only a unit.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: candidate_new_statement.

Scope: An associatedness statement modulo 2^r - 1, for squarefree r only. It computes the numerator's residue class up to units; it says nothing about the foreign diagonal defect and therefore nothing about Erdos 249.

- Lean declaration: [localNumeratorProduct_associated_oddJordanScalar](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L306)
- Lean declaration: [mobiusNumerator_associated_oddJordanScalar](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L339)

- incoming **implies**: [Z04::mersenne_local_product_congruence](BROWSER_Z04_1.md#node-6added433421e72f). The normal form starts from the congruence M_r = product of local values modulo 2^r - 1.
- incoming **implies**: [Z04::odd_local_cofactor_unit_mod_mersenne](BROWSER_Z04_1.md#node-c132bba476a8a1ae). Each odd local factor is associated to q^2 - 1 exactly because its cofactor is a unit in the Mersenne quotient.
- incoming **implies**: [Z04::binary_local_numerator_unit_mod_mersenne](BROWSER_Z04_1.md#node-84baf32a0a60fe2c). The binary factor contributes 1 to the association precisely because it is itself a unit.
- outgoing **implies**: [Z04::scaled_gcd_collapses_to_odd_jordan_scalar](BROWSER_Z04_2.md#node-f79f3d97b9686f97). Associated residues have equal gcd with the modulus, so the numerator may be replaced by the scalar inside the gcd.

<a id="node-c132bba476a8a1ae"></a>
## odd_local_cofactor_unit_mod_mersenne

For an odd prime q dividing r, the evaluated local cofactor is coprime to 2^r - 1, equivalently a unit in Z/(2^r - 1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Says nothing about the binary prime q = 2, where the cofactor is not claimed to be a unit.

- Lean declaration: [localCofactorValue_coprime_mersenne](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L125)
- Lean declaration: [localCofactorValue_isUnit_mod_mersenne](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L185)

- outgoing **implies**: [Z04::mobius_numerator_odd_jordan_normal_form](BROWSER_Z04_1.md#node-5ad37c71844c9ba7). Each odd local factor is associated to q^2 - 1 exactly because its cofactor is a unit in the Mersenne quotient.
- incoming **implies**: [Z04::base_two_subgroup_sum_coprime_q2_minus_1](BROWSER_Z04_1.md#node-3ab4198efd124e07). Coprimality of the evaluated subgroup sum to q^2 - 1 is the first of the two cases in the cofactor argument.

<a id="node-9d1feabddd85c06e"></a>
## polynomial_numerator_evaluation_bridge

For every r, the integral Mobius numerator M_r is the finite sum over subsets s of the prime factors of r of (-1)^|s| times (r/prod(s)) times (2^r - 1)/(2^prod(s) - 1). For squarefree r, evaluating the divisor-signed spaced-repunit polynomial at X = 2 returns exactly this M_r.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The bridge is the only link between the polynomial layer and the integer layer; it is stated only for squarefree exponents.

- Lean declaration: [mobiusNumerator](../../Erdos249257/RadicalMobiusShadow.lean#L101)
- Lean declaration: [mobiusNumeratorPolynomial_eval_two](../../Erdos249257/RepunitMobiusNumerator.lean#L445)
- Lean declaration: [eval_spacedRepunit_two](../../Erdos249257/RepunitMobiusNumerator.lean#L252)
- Lean declaration: [moebius_prod_subset_primeFactors](../../Erdos249257/RepunitMobiusNumerator.lean#L274)
- Lean declaration: [divisor_mobiusNumerator_eq_subset](../../Erdos249257/RepunitMobiusNumerator.lean#L297)

- outgoing **reformulates**: [Z04::repunit_numerator_is_gcd_word](BROWSER_Z04_2.md#node-8a120346ed549dea). Same polynomial numerator in two dresses: the gcd-word theorem describes it coefficientwise, the bridge identifies its value at X = 2 with the integer numerator M_r.

<a id="node-77a5c0a8736ab293"></a>
## prime_jump_fixtures

Kernel-checked instances of the jump recurrence: the numerator polynomials at r = 2 and r = 6, the explicit Phi_6 quotient of the first new fibre and the explicit Phi_2 quotient of the corresponding old fibre, plus an r = 4, p = 3 instance showing the recurrence does not need a squarefree source exponent.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Pins sign and multiplication orientation at the two smallest exponents only.

- Lean declaration: [mobiusNumeratorPolynomial_two_fixture](../../Erdos249257/PrimePowerJumpDynamics.lean#L380)
- Lean declaration: [mobiusNumeratorPolynomial_six_fixture](../../Erdos249257/PrimePowerJumpDynamics.lean#L390)
- Lean declaration: [primeJump_new_fibre_six_factorization](../../Erdos249257/PrimePowerJumpDynamics.lean#L404)
- Lean declaration: [primeJump_old_fibre_two_factorization](../../Erdos249257/PrimePowerJumpDynamics.lean#L416)

- outgoing **finite_instance_of**: [Z04::prime_jump_recurrence](BROWSER_Z04_2.md#node-e12586c9bfe0d246). Explicit polynomials at r = 2, 6 and 12 instantiating the recurrence and its two fibre splits.

<a id="node-daedd80f87b912a6"></a>
## prime_jump_new_fibre

When a fresh prime p is adjoined to r, in a genuinely new fibre m*p (with m | r) the geometric old-divisor block vanishes, so Phi_{m*p} divides the new numerator polynomial plus the p-fold expansion of the old one; on squarefree r this is equivalently Phi_{m*p} dividing the new numerator plus the constant mu(m) J2(r/m).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: A congruence interface. It does not assert that any foreign defect misses the displayed target in the new fibre.

- Lean declaration: [cyclotomic_dvd_primeJump_new_fibre](../../Erdos249257/PrimePowerJumpDynamics.lean#L281)
- Lean declaration: [cyclotomic_dvd_primeJump_new_fibre_constant](../../Erdos249257/PrimePowerJumpDynamics.lean#L347)
- Lean declaration: [cyclotomic_dvd_expand_sub_constant](../../Erdos249257/PrimePowerJumpDynamics.lean#L256)

- incoming **implies**: [Z04::prime_jump_recurrence](BROWSER_Z04_2.md#node-e12586c9bfe0d246). Reading the recurrence modulo Phi_{m*p}, where the repunit block vanishes, gives the new-fibre congruence.

