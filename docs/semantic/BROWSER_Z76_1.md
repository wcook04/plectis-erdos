# Z76_1: Erdős 243 exact dynamic cancellation and primitive two-step curvature

[All problems and zones](BROWSER.md)

<a id="node-32b54c13cb91113a"></a>
## cancellation_free_steps_expose_dual_remainders_curvature_and_square_determinants

On a cancellation-free step the centered error satisfies the exact dual-remainder identity s*e-Delta*p=eNext-e. Across two steps the primitive recurrence yields q^2+(p*pNextNext-pNext^2)=(aNext-a)*p*pNext. The associated excursion transfer has square determinant, and for primitive input and second matrix row the output gcd is exactly the gcd of that determinant with the second output coordinate.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The identities expose a changing quadratic quantity and determinant-controlled cancellation. They do not prove that curvature has a fixed sign, that determinant content is bounded, or that the orbit terminates.

- Lean declaration: [cancellationFree_dualRemainder](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L291)
- Lean declaration: [cancellationFree_curvature_square](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L307)
- Lean declaration: [excursionMatrix_det_square](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L322)
- Lean declaration: [primitiveMatrix_gcd_eq_det_gcd](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L335)

- outgoing **generated_by**: [Z76::consecutive_primitive_steps_satisfy_an_exact_second_order_recurrence](BROWSER_Z76_1.md#node-9cc41ef2f0eef2ef). The dual-remainder and curvature forms are algebraic eliminations of the primitive second-order step equations; the determinant lemma records the corresponding block-content interface.

<a id="node-9cc41ef2f0eef2ef"></a>
## consecutive_primitive_steps_satisfy_an_exact_second_order_recurrence

Full content removal leaves consecutive reduced numerators coprime, and the removed factor is exactly gcd(q,a^2). Two consecutive reduced steps then obey a^2*u + h*hNext*uNextNext = h*(a+aNext)*uNext.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The recurrence is an identity under the stated step equations. It supplies no monotone quantity, anti-shadowing theorem, or global termination argument.

- Lean declaration: [reducedStep_consecutiveNumerator_coprime](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L243)
- Lean declaration: [reducedStep_cancellationFactor_eq_square](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L254)
- Lean declaration: [reducedStep_secondOrder](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L268)

- outgoing **generated_by**: [Z76::primitive_raw_steps_have_exact_square_control_of_removed_content](BROWSER_Z76_1.md#node-2d02cd243b0bd553). Primitive consecutive numerators and the exact removed factor are direct consumers of the one-step coprimality and square-content identities.
- incoming **generated_by**: [Z76::cancellation_free_steps_expose_dual_remainders_curvature_and_square_determinants](BROWSER_Z76_1.md#node-32b54c13cb91113a). The dual-remainder and curvature forms are algebraic eliminations of the primitive second-order step equations; the determinant lemma records the corresponding block-content interface.

<a id="node-2d02cd243b0bd553"></a>
## primitive_raw_steps_have_exact_square_control_of_removed_content

For a primitive pair (u,v) with q+v=a*u, the current numerator u is coprime to q and gcd(q,a*v)=gcd(q,a^2). Writing d=gcd(a,v), the removed content is exactly d*gcd(q/d,d): one forced copy of d and one residual overlap copy.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The formula controls one raw step. It does not bound the overlap over time, force descent, or exclude an infinite orbit.

- Lean declaration: [rawNext_coprime_currentNumerator](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L15)
- Lean declaration: [rawNext_gcd_eq_gcd_sq](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L33)
- Lean declaration: [rawNext_gcd_exact_overlap](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L68)

- incoming **generated_by**: [Z76::square_overlap_has_an_explicit_denominator_deletion_normal_form](BROWSER_Z76_1.md#node-1c7a411374c14827). The explicit normal form factors the one-step gcd(q,a^2) square-overlap formula into forced and residual copies and transports those factors to the reduced denominator.
- incoming **generated_by**: [Z76::consecutive_primitive_steps_satisfy_an_exact_second_order_recurrence](BROWSER_Z76_1.md#node-9cc41ef2f0eef2ef). Primitive consecutive numerators and the exact removed factor are direct consumers of the one-step coprimality and square-content identities.

<a id="node-1c7a411374c14827"></a>
## square_overlap_has_an_explicit_denominator_deletion_normal_form

After factoring a=d*alpha and w=d*omega with alpha coprime to omega, the remaining square overlap is c=gcd(omega,d). If d=b*c, the removed content is b*c^2 and c stays coprime to alpha. When the old denominator is c*t and the next one is alpha*t, c is exactly the deleted factor v/gcd(v,vNext), equivalently lcm(a,v)=c*vNext.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The normal form identifies the local payment exactly but does not show that deleted overlap is small, rare, or globally unsustainable.

- Lean declaration: [gcd_scaled_square_eq](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L136)
- Lean declaration: [cancellationOverlap_normalForm_explicit](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L159)
- Lean declaration: [cancellation_denominator_transport_explicit](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L184)
- Lean declaration: [deletedFactor_eq_oldDenominator_div_gcd](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L212)
- Lean declaration: [lcm_eq_overlap_mul_nextDenominator](../../ErdosProblems/Erdos243/DynamicCancellation.lean#L225)

- outgoing **generated_by**: [Z76::primitive_raw_steps_have_exact_square_control_of_removed_content](BROWSER_Z76_1.md#node-2d02cd243b0bd553). The explicit normal form factors the one-step gcd(q,a^2) square-overlap formula into forced and residual copies and transports those factors to the reduced denominator.

