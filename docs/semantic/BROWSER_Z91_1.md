# Z91_1: Erdős 249 gcd-moment calculus: half-geometric normalizations and dyadic positivity

[All problems and zones](BROWSER.md)

<a id="node-95cae48161921751"></a>
## half_geometric_lambert_factors_are_exact_reciprocal_mersenne_factors

PROVED NORMALIZATION TOOLKIT: for every positive d, ((1/2)^d)/(1-(1/2)^d)=1/(2^d-1), and squaring gives the corresponding reciprocal-square identity. More generally, for 0≤x<1, the sum over g≥0 of x^(g+1) is x/(1-x).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The identities rewrite individual factors and one elementary sum. They do not justify unrelated sum exchanges, establish q-Padé irrationality, or evaluate the full gcd-moment series without the separate landed theorems that consume them.

- Lean declaration: [half_pow_term'](../../Erdos249257/GcdMomentCalculus.lean#L192)
- Lean declaration: [half_pow_sq_term'](../../Erdos249257/GcdMomentCalculus.lean#L206)
- Lean declaration: [tsum_pow_succ_geometric'](../../Erdos249257/GcdMomentCalculus.lean#L252)

- incoming **complements**: [Z91::positive_natural_exponents_make_two_power_denominators_strictly_positive](BROWSER_Z91_1.md#node-25084181940deb7a). The dyadic lower bound supplies the denominator positivity used by the half-geometric reciprocal-Mersenne normalization.

<a id="node-25084181940deb7a"></a>
## positive_natural_exponents_make_two_power_denominators_strictly_positive

PROVED DYADIC LOWER BOUND: for every positive natural a, 2≤2^a; in particular 2^a-1 is positive, as required by the cylinder-mass denominator arguments.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: This is only the positivity side condition for later rational cylinder identities; it contains no asymptotic or arithmetic information.

- Lean declaration: [two_le_two_pow](../../Erdos249257/GcdMomentCalculus.lean#L458)

- outgoing **complements**: [Z91::half_geometric_lambert_factors_are_exact_reciprocal_mersenne_factors](BROWSER_Z91_1.md#node-95cae48161921751). The dyadic lower bound supplies the denominator positivity used by the half-geometric reciprocal-Mersenne normalization.

