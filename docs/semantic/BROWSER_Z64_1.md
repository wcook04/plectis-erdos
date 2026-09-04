# Z64_1: Actual-LCM orbit representation, raw-block approximation, and quantitative separation endpoint

[All problems and zones](BROWSER.md)

<a id="node-5e3dc8db2a237c5d"></a>
## actual_lcm_tail_orbit_is_an_integer_translate_of_the_scaled_totient_series

For H=periodLcm(2^a), actualLcmTailOrbit(a)=2^H*(2^H-1)*(∑' n, Nat.totient n / 2^n) - (totientPrefix(2H)-totientPrefix(H)).

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The exact identity alone proves neither nonintegrality nor irrationality. Its integer coefficient and prefix translate supply no quantitative separation from the integers.

- Lean declaration: [actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix](../../Erdos249257/TotientActualLcmOrbitSeparation.lean#L68)

- incoming **complements**: [Z64::odd_rank_raw_block_approximates_the_actual_lcm_orbit_with_explicit_error](BROWSER_Z64_1.md#node-17a0940b17634da5). The first theorem locates the orbit relative to the scaled #249 series; the second makes that orbit finitely approximable with an explicit error without proving separation.

<a id="node-f1089e332762f1e4"></a>
## cofinal_actual_lcm_orbit_separation_conditionally_forces_totient_irrationality

If PowerTwoActualLcmOrbitSeparationSupply holds, namely for every a0 there exist a,q with max(2,a0)≤a, oddGuardedCanonicalAdjacentSuffixDepth(2^a)=2q+1, and for every integer z the bound 1/32+actualLcmRawErrorRadius(a,q)≤|actualLcmTailOrbit(a)-z|, then the binary totient series ∑' n, Nat.totient n / 2^n is irrational.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The supply is open and is stronger than mere nonintegrality. It is not proved necessary or implied by irrationality; finite nonintegral examples do not establish its cofinal quantifier. No equidistribution, density, or irrationality measure is proved.

Open hypotheses: ["PowerTwoActualLcmOrbitSeparationSupply: for every a₀ there exist a,q with max 2 a₀≤a, oddGuardedCanonicalAdjacentSuffixDepth(2^a)=2q+1, and for every z:ℤ, 1/32+actualLcmRawErrorRadius a q≤|actualLcmTailOrbit a-z|."]

- Lean declaration: [irrational_totientSeries_of_actualLcmOrbitSeparationSupply](../../Erdos249257/TotientActualLcmOrbitSeparation.lean#L305)

- outgoing **generated_by**: [Z64::odd_rank_raw_block_approximates_the_actual_lcm_orbit_with_explicit_error](BROWSER_Z64_1.md#node-17a0940b17634da5). The endpoint proof uses the explicit error bound to transfer strong separation of the actual orbit to 1/32 integer separation of the raw approximation, then invokes the half-word and signed-margin consumers.

<a id="node-17a0940b17634da5"></a>
## odd_rank_raw_block_approximates_the_actual_lcm_orbit_with_explicit_error

For every a and q, |actualLcmTailOrbit(a)-actualLcmRawApprox(a,q)| < actualLcmRawErrorRadius(a,q), where actualLcmRawApprox is diagonalAdjacentSuffixRawBlock(2^a,0,2q+1)/2^(2q+1) and actualLcmRawErrorRadius=(2*actualLcmHeight(a)+2q+3)/2^(2q+1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is an upper approximation error only. It gives no lower bound or integer separation, and the error radius is not asserted to tend to zero along canonical ranks without growth control comparing q with the LCM height.

- Lean declaration: [abs_actualLcmTailOrbit_sub_rawApprox_lt](../../Erdos249257/TotientActualLcmOrbitSeparation.lean#L141)

- outgoing **complements**: [Z64::actual_lcm_tail_orbit_is_an_integer_translate_of_the_scaled_totient_series](BROWSER_Z64_1.md#node-5e3dc8db2a237c5d). The first theorem locates the orbit relative to the scaled #249 series; the second makes that orbit finitely approximable with an explicit error without proving separation.
- incoming **generated_by**: [Z64::cofinal_actual_lcm_orbit_separation_conditionally_forces_totient_irrationality](BROWSER_Z64_1.md#node-f1089e332762f1e4). The endpoint proof uses the explicit error bound to transfer strong separation of the actual orbit to 1/32 integer separation of the raw approximation, then invokes the half-word and signed-margin consumers.

