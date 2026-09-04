# Z04_2: Radical Mobius shadow: repunit numerators, cyclotomic fibres and Mersenne channel denominators

[All problems and zones](BROWSER.md)

<a id="node-12df7e99ecb7d37c"></a>
## prime_jump_old_fibre

When a fresh prime p is adjoined to a squarefree r, on an old fibre m | r the numerator is scaled by p^2 - 1: Phi_m divides the new numerator polynomial minus (p^2 - 1) times the old one.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Squarefreeness is used only to call the T2 constant-fibre theorem, not for the underlying recurrence; the statement makes no claim about non-cancellation.

- Lean declaration: [cyclotomic_dvd_primeJump_old_fibre](../../Erdos249257/PrimePowerJumpDynamics.lean#L310)

- incoming **implies**: [Z04::prime_jump_recurrence](BROWSER_Z04_2.md#node-e12586c9bfe0d246). Reading the recurrence modulo Phi_m, where the repunit block is congruent to p, gives the old-fibre congruence.

<a id="node-e12586c9bfe0d246"></a>
## prime_jump_recurrence

T5. For a prime p not dividing r, the Mobius numerator polynomial at rp equals p times the spaced repunit of block size r with p blocks times the numerator at r, minus the p-fold expansion of the numerator at r. No squarefreeness hypothesis is needed. Equivalent orientations state the same identity with the factors commuted, with expansion written as composition with X^p, and evaluated at an arbitrary integer x, where expansion becomes evaluation at x^p.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: A polynomial identity only. It supplies no channel-avoidance statement and no infinite supply of anything.

- Lean declaration: [mobiusNumeratorPolynomial_mul_prime](../../Erdos249257/PrimePowerJumpDynamics.lean#L160)
- Lean declaration: [mobiusNumeratorPolynomial_prime_mul](../../Erdos249257/PrimePowerJumpDynamics.lean#L210)
- Lean declaration: [mobiusNumeratorPolynomial_mul_prime_comp](../../Erdos249257/PrimePowerJumpDynamics.lean#L220)
- Lean declaration: [mobiusNumeratorPolynomial_mul_prime_eval](../../Erdos249257/PrimePowerJumpDynamics.lean#L230)
- Lean declaration: [expand_spacedRepunit](../../Erdos249257/PrimePowerJumpDynamics.lean#L45)
- Lean declaration: [divisors_mul_prime_split](../../Erdos249257/PrimePowerJumpDynamics.lean#L25)
- Lean declaration: [divisors_disjoint_prime_multiples](../../Erdos249257/PrimePowerJumpDynamics.lean#L35)
- Lean declaration: [spacedRepunit_eq_sum_X_pow](../../Erdos249257/PrimePowerJumpDynamics.lean#L56)
- Lean declaration: [spacedRepunit_mul_X_pow_sub_one](../../Erdos249257/PrimePowerJumpDynamics.lean#L61)
- Lean declaration: [X_pow_sub_one_ne_zero](../../Erdos249257/PrimePowerJumpDynamics.lean#L68)
- Lean declaration: [spacedRepunit_blocks](../../Erdos249257/PrimePowerJumpDynamics.lean#L75)
- Lean declaration: [moebius_mul_prime](../../Erdos249257/PrimePowerJumpDynamics.lean#L94)
- Lean declaration: [old_divisor_summand](../../Erdos249257/PrimePowerJumpDynamics.lean#L103)
- Lean declaration: [new_divisor_summand](../../Erdos249257/PrimePowerJumpDynamics.lean#L138)

- outgoing **implies**: [Z04::prime_jump_new_fibre](BROWSER_Z04_1.md#node-daedd80f87b912a6). Reading the recurrence modulo Phi_{m*p}, where the repunit block vanishes, gives the new-fibre congruence.
- outgoing **implies**: [Z04::prime_jump_old_fibre](BROWSER_Z04_2.md#node-12df7e99ecb7d37c). Reading the recurrence modulo Phi_m, where the repunit block is congruent to p, gives the old-fibre congruence.
- incoming **finite_instance_of**: [Z04::prime_jump_fixtures](BROWSER_Z04_1.md#node-77a5c0a8736ab293). Explicit polynomials at r = 2, 6 and 12 instantiating the recurrence and its two fibre splits.
- outgoing **implies**: [Z04::cyclic_tensor_factorisation](BROWSER_Z04_1.md#node-181415fcf1bd9103). The induction step rewrites the numerator at p*r by the T5 recurrence before matching it against the local factor at p.

<a id="node-220efa863161e5dd"></a>
## prime_radical_shadow_denominator

For a prime exponent p the Mobius numerator is exactly p(2^p - 1) - 1, which is coprime to 2^p - 1, so the unscaled radical shadow B(p) has reduced denominator exactly 2^p - 1.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Statement is about the explicit finite Mobius shadow only. It says nothing about the foreign diagonal defect (the part of the actual totient tail difference not captured by the finite shadow), so it does not bear on the irrationality of sum phi(n)/2^n on its own.

- Lean declaration: [mobiusNumerator_prime](../../Erdos249257/RadicalMobiusShadow.lean#L172)
- Lean declaration: [mobiusNumerator_prime_gcd](../../Erdos249257/RadicalMobiusShadow.lean#L179)
- Lean declaration: [baseMobiusShadow_den_prime](../../Erdos249257/RadicalMobiusShadow.lean#L200)
- Lean declaration: [sum_powerset_singleton](../../Erdos249257/RadicalMobiusShadow.lean#L27)

- outgoing **specialises**: [Z04::scaled_gcd_collapses_to_odd_jordan_scalar](BROWSER_Z04_2.md#node-f79f3d97b9686f97). gcd(M_p, 2^p - 1) = 1 is the case r = p of the odd-Jordan gcd collapse, since oddJordanScalar(p) = p^2 - 1 is coprime to 2^p - 1 by the prime-divisor lower bound.

<a id="node-022ebc6b8148a5db"></a>
## radical_reduction_of_scaled_shadow

The numeric Mobius shadow of H depends only on rad(H), and multiplying it by H is exactly multiplying the unscaled radical shadow B(rad H) = M_{rad H}/(2^{rad H} - 1) by the residual scale H/rad(H).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: A normalisation of the definition, not an arithmetic theorem: the reduced denominator of the scaled object is deliberately left to the separate exact-denominator statements, because the extra factor H/rad(H) can cancel further.

- Lean declaration: [numericMobiusShadow_radical](../../Erdos249257/RadicalMobiusShadow.lean#L118)
- Lean declaration: [scaledMobiusShadow_eq_radicalBase](../../Erdos249257/RadicalMobiusShadow.lean#L125)
- Lean declaration: [scaledMobiusShadow_eq_radicalNumerator](../../Erdos249257/RadicalMobiusShadow.lean#L141)

- incoming **implies**: [Z04::squarefree_kernel_basic](BROWSER_Z04_2.md#node-e19d9a65ab386e50). The scaling identity is the divisibility rad(H) | H together with positivity of the kernel.

<a id="node-653a407fa7311f76"></a>
## radical_shadow_denominator_fixtures

Kernel-checked numerical values: M_5 = 154 with denominator 2^5 - 1; M_10 = 8460 with gcd 3 and denominator (2^10 - 1)/3; M_210 equal to an explicit 66-digit integer with gcd 9 and denominator (2^210 - 1)/9.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Verified at three exponents only (5, 10, 210). Regression evidence for the general formulas, not a substitute for them.

- Lean declaration: [prime5_numerator_fixture](../../Erdos249257/RadicalMobiusShadow.lean#L403)
- Lean declaration: [prime5_den_fixture](../../Erdos249257/RadicalMobiusShadow.lean#L409)
- Lean declaration: [twicePrime5_numerator_fixture](../../Erdos249257/RadicalMobiusShadow.lean#L414)
- Lean declaration: [twicePrime5_gcd_fixture](../../Erdos249257/RadicalMobiusShadow.lean#L420)
- Lean declaration: [twicePrime5_den_fixture](../../Erdos249257/RadicalMobiusShadow.lean#L425)
- Lean declaration: [radical210_numerator_fixture](../../Erdos249257/RadicalMobiusShadow.lean#L429)
- Lean declaration: [radical210_gcd_fixture](../../Erdos249257/RadicalMobiusShadow.lean#L437)
- Lean declaration: [radical210_den_fixture](../../Erdos249257/RadicalMobiusShadow.lean#L442)

- outgoing **finite_instance_of**: [Z04::base_shadow_generic_reduced_denominator](BROWSER_Z04_1.md#node-6c01e9e3e3337773). Each fixture certifies one gcd and reads the denominator off the generic formula at a fixed exponent.

<a id="node-1481b123d79ef011"></a>
## rational_denominator_survival_reexport

Re-exported from RationalDenominatorSurvival: a divisor of a displayed denominator that is coprime to the displayed numerator survives reduction to lowest terms, and under an extra integer scale h the surviving part is the divisor divided by its gcd with h.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [divisor_dvd_divInt_den](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L595)
- Lean declaration: [survivingDivisor_dvd_scaled_divInt_den](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L604)

- outgoing **alias_of**: [Z11::rational_denominator_divisor_survival](BROWSER_Z11_1.md#node-541429c78c537b38). Both nodes own exactly the declarations `divisor_dvd_divInt_den` and `survivingDivisor_dvd_scaled_divInt_den` of Erdos249257/RationalDenominatorSurvival.lean; the Z04 node states in its own docstring that it is a re-export.

<a id="node-8a120346ed549dea"></a>
## repunit_numerator_is_gcd_word

For squarefree r the divisor-signed spaced-repunit polynomial sum over d | r of mu(d)(r/d)(1 + X^d + ... + X^{r-d}) equals the gcd word: its coefficient at X^k is (r/gcd(r,k)) * phi(gcd(r,k)) for k < r and zero for k at least r.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Stated only on the squarefree boundary; the module does not extend the identity to nonsquarefree exponents.

- Lean declaration: [mobiusNumeratorPolynomial_eq_gcdWord](../../Erdos249257/RepunitMobiusNumerator.lean#L205)
- Lean declaration: [mobiusNumeratorPolynomial_coeff](../../Erdos249257/RepunitMobiusNumerator.lean#L217)
- Lean declaration: [coeff_spacedRepunit_of_lt](../../Erdos249257/RepunitMobiusNumerator.lean#L48)
- Lean declaration: [coeff_spacedRepunit_eq_zero_of_le](../../Erdos249257/RepunitMobiusNumerator.lean#L73)
- Lean declaration: [moebius_divisor_sum_eq_totient](../../Erdos249257/RepunitMobiusNumerator.lean#L89)
- Lean declaration: [scaled_moebius_divisor_sum_eq](../../Erdos249257/RepunitMobiusNumerator.lean#L111)
- Lean declaration: [mobiusNumeratorPolynomial_coeff_of_lt](../../Erdos249257/RepunitMobiusNumerator.lean#L134)
- Lean declaration: [mobiusNumeratorPolynomial_coeff_eq_zero_of_le](../../Erdos249257/RepunitMobiusNumerator.lean#L182)
- Lean declaration: [gcdWord_coeff_of_lt](../../Erdos249257/RepunitMobiusNumerator.lean#L194)
- Lean declaration: [gcdWord_coeff_eq_zero_of_le](../../Erdos249257/RepunitMobiusNumerator.lean#L199)

- incoming **reformulates**: [Z04::polynomial_numerator_evaluation_bridge](BROWSER_Z04_1.md#node-9d1feabddd85c06e). Same polynomial numerator in two dresses: the gcd-word theorem describes it coefficientwise, the bridge identifies its value at X = 2 with the integer numerator M_r.
- outgoing **implies**: [Z04::repunit_numerator_positivity](BROWSER_Z04_2.md#node-a723388f34e576f4). Positivity is read directly off the gcd-word coefficient formula (r/g) * phi(g).

<a id="node-a723388f34e576f4"></a>
## repunit_numerator_positivity

Every gcd-word coefficient is strictly positive, so for squarefree r the Mobius numerator polynomial has strictly positive coefficients below degree r and is nonnegative everywhere.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: No cancellation statement: positivity of coefficients says nothing about the gcd of the evaluated numerator with 2^r - 1.

- Lean declaration: [gcdWordCoeff_pos](../../Erdos249257/RepunitMobiusNumerator.lean#L226)
- Lean declaration: [mobiusNumeratorPolynomial_coeff_pos](../../Erdos249257/RepunitMobiusNumerator.lean#L234)
- Lean declaration: [mobiusNumeratorPolynomial_coeff_nonneg](../../Erdos249257/RepunitMobiusNumerator.lean#L243)

- incoming **implies**: [Z04::repunit_numerator_is_gcd_word](BROWSER_Z04_2.md#node-8a120346ed549dea). Positivity is read directly off the gcd-word coefficient formula (r/g) * phi(g).

<a id="node-f79f3d97b9686f97"></a>
## scaled_gcd_collapses_to_odd_jordan_scalar

For squarefree r and any natural scale h, the gcd of |h * M_r| with 2^r - 1 equals the gcd of h times the absolute odd Jordan scalar with 2^r - 1; the unscaled case h = 1 is the special case.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Squarefree exponents only; a statement about the displayed fraction M_r/(2^r - 1), not about the totient series.

- Lean declaration: [scaledMobiusNumerator_gcd_eq_oddJordanScalar](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L412)
- Lean declaration: [mobiusNumerator_gcd_eq_oddJordanScalar](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L431)

- incoming **specialises**: [Z04::prime_radical_shadow_denominator](BROWSER_Z04_2.md#node-220efa863161e5dd). gcd(M_p, 2^p - 1) = 1 is the case r = p of the odd-Jordan gcd collapse, since oddJordanScalar(p) = p^2 - 1 is coprime to 2^p - 1 by the prime-divisor lower bound.
- incoming **specialises**: [Z04::twice_prime_radical_shadow_denominator](BROWSER_Z04_2.md#node-d0ebbd26cf2eabf3). gcd 3 at exponent 2p is the case r = 2p, where the odd Jordan scalar is p^2 - 1 and the surviving common factor with 2^{2p} - 1 is exactly 3.
- incoming **implies**: [Z04::mobius_numerator_odd_jordan_normal_form](BROWSER_Z04_1.md#node-5ad37c71844c9ba7). Associated residues have equal gcd with the modulus, so the numerator may be replaced by the scalar inside the gcd.
- outgoing **implies**: [Z04::scaled_shadow_exact_denominator](BROWSER_Z04_2.md#node-a69b54b00ab84afd). Substituting the collapsed gcd into the reduced-denominator formula gives the exact denominator.

<a id="node-a69b54b00ab84afd"></a>
## scaled_shadow_exact_denominator

For squarefree r and any natural scale h, the reduced denominator of (h * M_r)/(2^r - 1) is exactly (2^r - 1) divided by the gcd of 2^r - 1 with h times the absolute odd Jordan scalar of r.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Statement is about the explicit finite Mobius shadow only. It says nothing about the foreign diagonal defect (the part of the actual totient tail difference not captured by the finite shadow), so it does not bear on the irrationality of sum phi(n)/2^n on its own.

- Lean declaration: [scaledMobiusNumerator_den_exact](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L441)

- incoming **implies**: [Z04::scaled_gcd_collapses_to_odd_jordan_scalar](BROWSER_Z04_2.md#node-f79f3d97b9686f97). Substituting the collapsed gcd into the reduced-denominator formula gives the exact denominator.
- incoming **specialises**: [Z04::lcm_height_exact_denominator](BROWSER_Z04_1.md#node-6f532b908aa314db). Instantiation at r = rad(H_t) and h = H_t/rad(H_t).

<a id="node-d191586330a418a5"></a>
## single_channel_with_two_sided_bounds

For t at least 5 there exists an upper-half prime p such that 2^{t/2} <= 2^p - 1 < 2^t and 2^p - 1 divides the reduced denominator of the scaled LCM-height Mobius shadow.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Existence of one surviving channel of controlled size. No statement that any residual quantity avoids that channel.

- Lean declaration: [exists_upperHalf_mersenne_channel_dvd_den_with_bounds](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L99)

- outgoing **specialises**: [Z04::lcm_height_channel_product_divides_shadow_denominator](BROWSER_Z04_1.md#node-95a73146a64e09d8). One Bertrand prime is selected from the surviving family and its single channel is bounded on both sides.

<a id="node-87bf3ba93a5700a3"></a>
## smooth_numbers_coprime_to_upper_half_channel

If every prime factor of a natural number is at most t and p is a prime with 3 <= p and t < 2p, then that number is coprime to 2^p - 1 and a unit modulo it; in particular q^2 - 1 for any prime q at most t, and |J2(r/p)| for a squarefree t-smooth r, are coprime to 2^p - 1.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The size separation is between t-smooth data and a single upper-half channel; it says nothing about data with a prime factor above t.

- Lean declaration: [coprime_mersenne_of_primeFactors_le](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L531)
- Lean declaration: [isUnit_mod_mersenne_of_primeFactors_le](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L542)
- Lean declaration: [coprime_mersenne_prime_sq_sub_one](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L630)
- Lean declaration: [coprime_mersenne_jordanTotientTwo](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L651)

- incoming **implies**: [Z04::mersenne_prime_divisor_lower_bound](BROWSER_Z04_1.md#node-3e689506ffab44c0). Every prime divisor of the channel exceeds 2p > t, so no t-smooth number can share a factor with it.
- outgoing **implies**: [Z04::upper_half_unit_target_is_unit](BROWSER_Z04_2.md#node-2f1139144e87b8b3). Each of the three arithmetic factors of the target is t-smooth, hence invertible in the channel.

<a id="node-f2e70f884896b053"></a>
## spaced_repunit_cyclotomic_factorisation

For d | r the spaced repunit with block size d and r/d blocks is the product of the cyclotomic polynomials Phi_e over the divisors e of r that do not divide d; consequently Phi_m divides it whenever m | r and m does not divide d, and Phi_m divides it minus the constant r/d whenever m | d.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [cyclotomic_dvd_spacedRepunit_of_not_dvd](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L162)
- Lean declaration: [cyclotomic_dvd_spacedRepunit_sub_C_of_dvd](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L174)
- Lean declaration: [spacedRepunit_eq_sum_X_pow](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L129)
- Lean declaration: [spacedRepunit_mul_X_pow_sub_one](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L135)
- Lean declaration: [spacedRepunit_eq_prod_cyclotomic_sdiff](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L143)

- outgoing **implies**: [Z04::cyclotomic_fibre_congruence](BROWSER_Z04_1.md#node-7b000b61bd5cd228). Applying the two repunit divisibility facts summand by summand over the divisors of r yields the fibre congruence.
- incoming **specialises**: [Z04::mersenne_quotient_channel_congruence](BROWSER_Z04_1.md#node-c933122f9ceb6d38). The congruence is the old-fibre repunit statement at d = m, evaluated at X = 2.

<a id="node-e19d9a65ab386e50"></a>
## squarefree_kernel_basic

The squarefree kernel rad(n), defined as the product of the distinct prime factors of n, is positive, divides n, is squarefree, is idempotent, has the same prime factors as n, and for n nonzero shares exactly the prime divisors of n.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [squarefreeKernel_primeFactors](../../Erdos249257/RadicalMobiusShadow.lean#L42)
- Lean declaration: [squarefreeKernel_idem](../../Erdos249257/RadicalMobiusShadow.lean#L48)
- Lean declaration: [squarefreeKernel_pos](../../Erdos249257/RadicalMobiusShadow.lean#L54)
- Lean declaration: [squarefreeKernel_dvd](../../Erdos249257/RadicalMobiusShadow.lean#L58)
- Lean declaration: [squarefreeKernel_squarefree](../../Erdos249257/RadicalMobiusShadow.lean#L63)
- Lean declaration: [prime_dvd_squarefreeKernel_iff](../../Erdos249257/RadicalMobiusShadow.lean#L77)

- outgoing **implies**: [Z04::radical_reduction_of_scaled_shadow](BROWSER_Z04_2.md#node-022ebc6b8148a5db). The scaling identity is the divisibility rad(H) | H together with positivity of the kernel.

<a id="node-871b019ccc4a3041"></a>
## top_cyclotomic_fibre_noncollapse

T3. For squarefree r the Mobius numerator M_r is coprime to |Phi_r(2)|, because in the top fibre it is congruent to mu(r) = plus or minus 1; therefore |Phi_r(2)| divides the reduced denominator of the unscaled radical shadow B(r).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Only the unscaled shadow B(r) is covered: this node says nothing about the extra scale H/rad(H), which is handled by the separate scaled statements, and nothing about the foreign diagonal defect.

- Lean declaration: [mobiusNumerator_gcd_cyclotomicValue](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L350)
- Lean declaration: [cyclotomicValue_dvd_baseMobiusShadow_den](../../Erdos249257/CyclotomicProjectionOfShadow.lean#L389)

- outgoing **specialises**: [Z04::cyclotomic_fibre_congruence](BROWSER_Z04_1.md#node-7b000b61bd5cd228). T3 is T2 at the top fibre m = r, where J2(1) = 1 leaves the unit mu(r).

<a id="node-d0ebbd26cf2eabf3"></a>
## twice_prime_radical_shadow_denominator

For every prime p at least 5 the Mobius numerator at exponent 2p expands into four explicit terms and has gcd exactly 3 with 2^{2p} - 1, so the unscaled radical shadow B(2p) has reduced denominator exactly (2^{2p} - 1)/3.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Statement is about the explicit finite Mobius shadow only. It says nothing about the foreign diagonal defect (the part of the actual totient tail difference not captured by the finite shadow), so it does not bear on the irrationality of sum phi(n)/2^n on its own.

- Lean declaration: [mobiusNumerator_twicePrime](../../Erdos249257/RadicalMobiusShadow.lean#L207)
- Lean declaration: [mobiusNumerator_twicePrime_gcd](../../Erdos249257/RadicalMobiusShadow.lean#L267)
- Lean declaration: [baseMobiusShadow_den_twicePrime](../../Erdos249257/RadicalMobiusShadow.lean#L391)
- Lean declaration: [prime_mod_six_eq_one_or_five](../../Erdos249257/RadicalMobiusShadow.lean#L225)
- Lean declaration: [prime_pow_two_mod_nine_cases](../../Erdos249257/RadicalMobiusShadow.lean#L243)

- outgoing **specialises**: [Z04::scaled_gcd_collapses_to_odd_jordan_scalar](BROWSER_Z04_2.md#node-f79f3d97b9686f97). gcd 3 at exponent 2p is the case r = 2p, where the odd Jordan scalar is p^2 - 1 and the surviving common factor with 2^{2p} - 1 is exactly 3.

<a id="node-8f7c56fd6ce01420"></a>
## upper_half_channel_coprime_numerator

For squarefree t-smooth r and an upper-half prime p | r (t < 2p, t at least 5), the channel 2^p - 1 is coprime to |M_r|, and so is the product of the channels over any finite family of such primes.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The size separation is the whole argument: it works only because the channel's prime divisors exceed 2p > t while the numerator's residue is t-smooth.

- Lean declaration: [coprime_mersenne_mobiusNumerator](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L690)
- Lean declaration: [channelProduct_coprime_mobiusNumerator](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L747)
- Lean declaration: [coprime_natAbs_of_sum_dvd](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L674)

- incoming **implies**: [Z04::cyclotomic_fibre_congruence](BROWSER_Z04_1.md#node-7b000b61bd5cd228). The prime-channel form of T2 puts M_r in the residue class of -J2(r/p), which is t-smooth and therefore coprime to the channel.
- outgoing **implies**: [Z04::upper_half_channel_survives_scaled_denominator](BROWSER_Z04_2.md#node-12d3b49c3ef22e0b). Coprimality of the channel product to the numerator is exactly the hypothesis of the scale-aware survival lemma.

<a id="node-37618ef352954ce3"></a>
## upper_half_channel_product_growth

The product of the upper-half Mersenne channels dominates the product of 2^{p-1} over the same primes, equivalently 2 to the power of the sum of (p - 1); and for t at least 5 it is at least 2^{t/2}.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: A lower bound on the channel product only. It is far weaker than the exact denominator formula proved in the same zone.

- Lean declaration: [upperHalfMersenneProduct_factorwise_lower_bound](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L32)
- Lean declaration: [upperHalfMersenneProduct_sum_lower_bound](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L41)
- Lean declaration: [upperHalfMersenneProduct_lower_bound](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L60)
- Lean declaration: [two_pow_pred_le_mersenne](../../Erdos249257/MersenneShadowDenominatorGrowth.lean#L22)

- outgoing **implies**: [Z04::lcm_height_denominator_lower_bound](BROWSER_Z04_1.md#node-3b92aae867baea37). The 2^{t/2} bound on the channel product transfers to the denominator that the product divides.
- incoming **implies**: [Z04::bertrand_supplies_upper_half_prime](BROWSER_Z04_1.md#node-2cd6c0ee65c42dd5). The 2^{t/2} bound needs at least one prime in the upper half, supplied by Bertrand's postulate.

<a id="node-12d3b49c3ef22e0b"></a>
## upper_half_channel_survives_scaled_denominator

T4. Let r be squarefree with all prime factors at most t (t at least 5), let P be a finite set of primes dividing r with t < 2p for each p in P, and let C be the product of the Mersenne channels 2^p - 1 over P. Then C divided by gcd(C, h) divides the reduced denominator of (h * M_r)/(2^r - 1) for every natural scale h; the single-prime case and the full-product corollaries under a coprime scale, or under a t-smooth scale, follow.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Exactly the part gcd(C, h) may be cancelled by the scale; the full product is claimed only under an explicit coprimality or smoothness hypothesis on the scale. Nothing is claimed about arbitrary integer cyclotomic evaluations, about non-prime channels, or about the foreign diagonal defect.

- Lean declaration: [upperHalfChannel_survivorProduct_dvd_den](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L766)
- Lean declaration: [upperHalfChannel_survivor_dvd_den](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L784)
- Lean declaration: [upperHalfChannel_product_dvd_den_of_coprime_scale](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L795)
- Lean declaration: [upperHalfChannel_product_dvd_den_of_scale_primeFactors_le](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L809)

- incoming **implies**: [Z04::upper_half_channel_coprime_numerator](BROWSER_Z04_2.md#node-8f7c56fd6ce01420). Coprimality of the channel product to the numerator is exactly the hypothesis of the scale-aware survival lemma.
- incoming **implies**: [Z04::mersenne_channel_product_structure](BROWSER_Z04_1.md#node-f17a9973708c8994). Pairwise coprimality of prime-index Mersennes is what makes the channel product divide 2^r - 1.
- incoming **specialises**: [Z04::lcm_height_channel_product_divides_shadow_denominator](BROWSER_Z04_1.md#node-95a73146a64e09d8). T4 instantiated at r = rad(H), h = H/rad(H), with all smoothness side conditions discharged from the LCM-height support facts.
- incoming **transport_of**: [Z05::channel_projected_pincer](BROWSER_Z05_1.md#node-58d9ee1fa2b10ca0). The projected pincer splits off the channel representative u/(2^p-1) at p in upperHalfPrimes t and rescales by channelModulus p = mersenne p, which is the T4 channel whose survival in the reduced denominator upperHalfChannel_survivorProduct_dvd_den establishes.

<a id="node-2f1139144e87b8b3"></a>
## upper_half_unit_target_is_unit

The T2 residue target -h*j*n^{-1} in Z/(2^p - 1) is a unit whenever p is a prime with 3 <= p, t < 2p, and each of h, n and |j| has all prime factors at most t.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Only says the target residue is invertible, so the channel does not degenerate. It does not say that the foreign diagonal defect hits or misses that target, which is the actual open supply question for Erdos 249.

- Lean declaration: [upperHalfUnitTarget](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L551)
- Lean declaration: [upperHalfUnitTarget_isUnit_of_primeFactors_le](../../Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L561)

- incoming **implies**: [Z04::smooth_numbers_coprime_to_upper_half_channel](BROWSER_Z04_2.md#node-87bf3ba93a5700a3). Each of the three arithmetic factors of the target is t-smooth, hence invertible in the channel.
- incoming **transport_of**: [Z05::channel_projected_pincer](BROWSER_Z05_1.md#node-58d9ee1fa2b10ca0). lcmChannelNumerator / lcmChannelTarget_isUnit (DiagonalPincerDecomposition.lean:119-147) instantiate upperHalfUnitTarget (lcmScale t) (lcmRadical t / p) p (jordanTotientTwo ...) and are closed by upperHalfUnitTarget_isUnit_of_primeFactors_le.

