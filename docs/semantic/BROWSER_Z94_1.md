# Z94_1: Squared-Mersenne first-support enclosures and directed lattice separation

[All problems and zones](BROWSER.md)

<a id="node-8f2f8ea9ca8332d4"></a>
## directed_integer_lattice_separation_rules_out_a_full_target_hit

If every integer displacement from the Lambert-projected centre lies outside the directed first-support interval, then the actual scaled diagonal is not integral and the full-target hit predicate fails at that scale.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Conditional only. A single-scale miss, even when established, does not imply the cofinal supply needed by the #249 irrationality reduction.

Open hypotheses: ["The separation hypothesis hsep must exclude the directed interval for every integer z. The theorem does not produce hsep, prove it cofinally, or provide the unbounded certificate supply required for Erdős 249."]

- Lean declaration: [scaleFullTarget_miss_of_directed_lambert_interval](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L387)

- incoming **implies**: [Z94::the_actual_diagonal_inherits_the_first_support_directed_interval](BROWSER_Z94_1.md#node-82e21125f66fb8cf). The lattice-separation consumer contradicts any integral displacement lying inside the proved interval.

<a id="node-a53d21e97e7a2793"></a>
## integral_affine_maps_cancel_exactly_the_gcd_from_a_rational_denominator

For integers z and c and a rational x, the reduced denominator of z+c·x is den(x)/gcd(den(x),|c|). In particular, the canonical Lambert-projected diagonal centre has the denominator of its squared-Möbius partial sum divided by the gcd with the diagonal coefficient.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The formula computes the centre's denominator; it does not show that the actual diagonal avoids the integer lattice.

- Lean declaration: [rat_den_int_add_mul](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L35)
- Lean declaration: [lambertProjectedDiagonalRat_den](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L46)


<a id="node-82e21125f66fb8cf"></a>
## the_actual_diagonal_inherits_the_first_support_directed_interval

Under the same first-support hypotheses, the signed displacement of the actual scaled diagonal from its exact Lambert-projected rational centre lies between the directed lower and upper Lambert bounds obtained by multiplying the tail interval by the nonnegative diagonal coefficient.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is an enclosure, not a nonintegrality theorem. The interval may still contain an integer-lattice displacement.

- Lean declaration: [scaleDiagonalTailDifference_directed_lambert_interval](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L366)

- incoming **implies**: [Z94::the_first_omitted_mobius_channel_splits_and_directs_the_squared_tail](BROWSER_Z94_1.md#node-228ce651f612100b). The actual diagonal displacement is exactly the squared tail multiplied by the diagonal coefficient.
- outgoing **implies**: [Z94::directed_integer_lattice_separation_rules_out_a_full_target_hit](BROWSER_Z94_1.md#node-8f2f8ea9ca8332d4). The lattice-separation consumer contradicts any integral displacement lying inside the proved interval.

<a id="node-228ce651f612100b"></a>
## the_first_omitted_mobius_channel_splits_and_directs_the_squared_tail

If n>D is the first nonzero Möbius channel after D, then the squared-Mersenne tail at D is exactly μ(n)/(2^n-1)^2 plus the tail after n. When |μ(n)|=1, multiplying by μ(n) places the whole tail between 1/(2^n-1)^2 minus and plus the explicit remainder radius 4/[3(2^(n+1)-1)^2].

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The interval is conditional on the stated first-support data. It encloses the tail but does not by itself separate the corresponding diagonal from every integer.

- Lean declaration: [mobiusSquareTail_eq_first_support_add_tail](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L244)
- Lean declaration: [mobiusSquareTail_directed_of_first_support](../../Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L313)

- outgoing **implies**: [Z94::the_actual_diagonal_inherits_the_first_support_directed_interval](BROWSER_Z94_1.md#node-82e21125f66fb8cf). The actual diagonal displacement is exactly the squared tail multiplied by the diagonal coefficient.

