# Z55_1: Exact Boolean–Möbius endpoint transitions: quotient bits, support aggregation, and signed repair defect

[All problems and zones](BROWSER.md)

<a id="node-2c22a70c5ae951cc"></a>
## below_target_repair_integer_is_the_next_signed_endpoint_defect

If the endpoint-M prefix quotient has not crossed its half target, localRepairInteger D 1 (M+1) equals localEndpointDefect D (M+1).

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem does not establish its below-target hypothesis and produces no feasible repair or exact row. It does not verify a tempered-orbit instance.

- Lean declaration: [localRepairInteger_eq_localEndpointDefect_succ](../../Erdos249257/BooleanMobiusExactTransition.lean#L203)

- outgoing **transport_of**: [Z55::signed_endpoint_defect_obeys_the_exact_affine_recurrence](BROWSER_Z55_1.md#node-d583723fae6b529e). Under the below-target hypothesis, the natural suffix casts to the signed current defect, so the repair expression becomes the next defect recurrence.

<a id="node-9865c4652689d508"></a>
## finite_support_quotient_transition_adds_the_endpoint_divisor_count

For a fixed finite support of ranks at least two, localPrefixQuotient D (M+1)=2*localPrefixQuotient D M+endpointDivisorContribution D (M+1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Fixing and summing a support does not construct one that hits the half target, and the theorem does not show that the contribution equals one.

- Lean declaration: [localPrefixQuotient_succ](../../Erdos249257/BooleanMobiusExactTransition.lean#L131)

- outgoing **generated_by**: [Z55::single_mersenne_quotient_has_an_exact_divisibility_bit_transition](BROWSER_Z55_1.md#node-1ec258758f0a5327). Summing the rank-wise transition over D turns the individual divisibility bits into endpointDivisorContribution D (M+1).
- incoming **reformulates**: [Z55::signed_endpoint_defect_obeys_the_exact_affine_recurrence](BROWSER_Z55_1.md#node-d583723fae6b529e). Subtracting the support-quotient transition from the half-endpoint-target transition yields the signed affine defect recurrence exactly.

<a id="node-d583723fae6b529e"></a>
## signed_endpoint_defect_obeys_the_exact_affine_recurrence

For M at least one and a finite support of ranks at least two, localEndpointDefect D (M+1)=2*localEndpointDefect D M+1-endpointDivisorContribution D (M+1).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The defect is signed. The theorem proves no nonnegativity, boundedness, eventual behavior, exact row, or verified tempered-orbit identification.

- Lean declaration: [localEndpointDefect_succ](../../Erdos249257/BooleanMobiusExactTransition.lean#L189)

- outgoing **reformulates**: [Z55::finite_support_quotient_transition_adds_the_endpoint_divisor_count](BROWSER_Z55_1.md#node-9865c4652689d508). Subtracting the support-quotient transition from the half-endpoint-target transition yields the signed affine defect recurrence exactly.
- incoming **transport_of**: [Z55::below_target_repair_integer_is_the_next_signed_endpoint_defect](BROWSER_Z55_1.md#node-2c22a70c5ae951cc). Under the below-target hypothesis, the natural suffix casts to the signed current defect, so the repair expression becomes the next defect recurrence.

<a id="node-1ec258758f0a5327"></a>
## single_mersenne_quotient_has_an_exact_divisibility_bit_transition

For d at least two, localMersenneQuotient (M+1) d is twice localMersenneQuotient M d plus one exactly when d divides M+1, and plus zero otherwise.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The identity gives one quotient bit only; it proves no exact row, capacity inequality, sign, or cofinal support.

- Lean declaration: [localMersenneQuotient_endpoint_succ](../../Erdos249257/BooleanMobiusExactTransition.lean#L29)

- incoming **generated_by**: [Z55::finite_support_quotient_transition_adds_the_endpoint_divisor_count](BROWSER_Z55_1.md#node-9865c4652689d508). Summing the rank-wise transition over D turns the individual divisibility bits into endpointDivisorContribution D (M+1).

