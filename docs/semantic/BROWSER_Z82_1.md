# Z82_1: Erdős 249 visible-lattice model: convergence toolkit and rational Lambert falsifier

[All problems and zones](BROWSER.md)

<a id="node-e4555c800e03b18b"></a>
## geometric_pair_and_totient_power_families_are_summable_inside_the_unit_interval

PROVED CONVERGENCE TOOLKIT: for 0≤r<1, the pair family r^(a+b) is summable over natural pairs and the totient-weighted family φ(n)r^n is summable; moreover the shifted geometric series ∑_{g≥0} x^(g+1) equals x/(1-x) under the same parameter bounds.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: These statements justify later rearrangements only. Summability and a closed form for the geometric tail carry no irrationality information.

- Lean declaration: [summable_pow_add](../../Erdos249257/GeometricCoprimality.lean#L87)
- Lean declaration: [summable_totient_mul_pow](../../Erdos249257/GeometricCoprimality.lean#L210)
- Lean declaration: [tsum_pow_succ_geometric](../../Erdos249257/GeometricCoprimality.lean#L234)

- outgoing **complements**: [Z82::the_positive_visible_pair_lambert_kernel_equals_an_elementary_square](BROWSER_Z82_1.md#node-ad0e93675fabecd0). The convergence toolkit licenses the sum rearrangements and geometric expansions used to prove the exact visible-pair Lambert evaluation.

<a id="node-ad0e93675fabecd0"></a>
## the_positive_visible_pair_lambert_kernel_equals_an_elementary_square

PROVED MODEL FALSIFIER: for every real 0≤r<1, summing r^(a+b)/(1-r^(a+b)) over strictly positive coprime pairs (a,b) gives exactly (r/(1-r))^2.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The equality shows that coprime restriction plus geometric decay alone can still yield a rational value at rational r. It does not show that the #249 totient constant is rational, nor does it exclude arguments using non-geometric arithmetic structure, signed cancellation, or nontrivial cylinder interactions.

- Lean declaration: [tsum_pos_coprime_lambert_eq_sq](../../Erdos249257/GeometricCoprimality.lean#L407)

- incoming **complements**: [Z82::geometric_pair_and_totient_power_families_are_summable_inside_the_unit_interval](BROWSER_Z82_1.md#node-e4555c800e03b18b). The convergence toolkit licenses the sum rearrangements and geometric expansions used to prove the exact visible-pair Lambert evaluation.

