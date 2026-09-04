# Z83_1: Pointwise half-power normalization into Mersenne kernels

[All problems and zones](BROWSER.md)

<a id="node-01995ae1631c50ce"></a>
## positive_binary_indices_convert_half_power_kernels_exactly_to_mersenne_denominators

For every positive natural d, 2^d-1 is positive and the following real identities hold: (1/2)^d divided by 1-(1/2)^d equals 1/(2^d-1); (1/2)^d divided by (1-(1/2)^d)^2 equals 2^d/(2^d-1)^2; and 2^d/(2^d-1)^2 equals 1/(2^d-1)+1/(2^d-1)^2.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The identities are pointwise over the real numbers and require d>0. They do not prove summability, justify exchanging infinite sums, evaluate a Lambert series, establish coefficient positivity, decide an achievement-set membership, or imply irrationality for Erdős #249 or #257.

- Lean declaration: [two_pow_sub_one_pos](../../Erdos249257/MersenneLambertLadder.lean#L510)
- Lean declaration: [half_pow_term](../../Erdos249257/MersenneLambertLadder.lean#L514)
- Lean declaration: [half_pow_sq_term](../../Erdos249257/MersenneLambertLadder.lean#L528)
- Lean declaration: [mersenne_split](../../Erdos249257/MersenneLambertLadder.lean#L543)


