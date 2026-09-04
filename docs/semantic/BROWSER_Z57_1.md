# Z57_1: Primitive local Boolean–Möbius repair coordinates: quotient, support sum, binary suffix, and signed repair

[All problems and zones](BROWSER.md)

<a id="node-dd4d2abaccc0d739"></a>
## local_binary_suffix_is_the_natural_truncated_dyadic_carry

localBinarySuffix D k M is 2^(M-k)-localPrefixQuotient D M-1 using natural-number subtraction.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Natural subtraction may truncate; the definition proves no honest signed residual, nonnegativity, or Boolean-word capacity.

- Lean declaration: [localBinarySuffix](../../Erdos249257/BooleanMobiusLocalRepair.lean#L102)

- outgoing **generated_by**: [Z57::local_prefix_quotient_aggregates_integral_contributions_of_a_finite_support](BROWSER_Z57_1.md#node-22b89dcd1d1ec249). The suffix subtracts the aggregated prefix quotient and the terminal unit from the depth-(M-k) dyadic target.
- incoming **generated_by**: [Z57::local_repair_integer_is_the_signed_next_coefficient_from_suffix_and_endpoint_count](BROWSER_Z57_1.md#node-fb759194ef3a4620). The signed repair coordinate doubles the preceding suffix, adds the affine unit, and subtracts the new endpoint divisor count.

<a id="node-d129ad8634ba973e"></a>
## local_mersenne_quotient_is_the_integral_scaled_weight_coordinate

localMersenneQuotient M d is the natural-number floor quotient 2^M/(2^d-1).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: It is only the integral quotient part and does not equal the full scaled weight without the separate fractional remainder.

- Lean declaration: [localMersenneQuotient](../../Erdos249257/BooleanMobiusLocalRepair.lean#L20)

- incoming **generated_by**: [Z57::local_prefix_quotient_aggregates_integral_contributions_of_a_finite_support](BROWSER_Z57_1.md#node-22b89dcd1d1ec249). The prefix quotient is definitionally the finite sum of the single-rank quotient coordinates.

<a id="node-22b89dcd1d1ec249"></a>
## local_prefix_quotient_aggregates_integral_contributions_of_a_finite_support

localPrefixQuotient D M is the sum over d in D of localMersenneQuotient M d.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The aggregate omits fractional mass and proves neither an exact half-target row nor a capacity inequality.

- Lean declaration: [localPrefixQuotient](../../Erdos249257/BooleanMobiusLocalRepair.lean#L78)

- outgoing **generated_by**: [Z57::local_mersenne_quotient_is_the_integral_scaled_weight_coordinate](BROWSER_Z57_1.md#node-d129ad8634ba973e). The prefix quotient is definitionally the finite sum of the single-rank quotient coordinates.
- incoming **generated_by**: [Z57::local_binary_suffix_is_the_natural_truncated_dyadic_carry](BROWSER_Z57_1.md#node-dd4d2abaccc0d739). The suffix subtracts the aggregated prefix quotient and the terminal unit from the depth-(M-k) dyadic target.

<a id="node-fb759194ef3a4620"></a>
## local_repair_integer_is_the_signed_next_coefficient_from_suffix_and_endpoint_count

localRepairInteger D k n is 2*localBinarySuffix D k (n-1)+1-endpointDivisorContribution D n in the integers.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The value may be negative. The definition proves no nonnegativity, Boolean representation, upper-half capacity, exact row, or tempered-orbit identification.

- Lean declaration: [localRepairInteger](../../Erdos249257/BooleanMobiusLocalRepair.lean#L123)

- outgoing **generated_by**: [Z57::local_binary_suffix_is_the_natural_truncated_dyadic_carry](BROWSER_Z57_1.md#node-dd4d2abaccc0d739). The signed repair coordinate doubles the preceding suffix, adds the affine unit, and subtracts the new endpoint divisor count.

