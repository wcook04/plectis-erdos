# Z70_1: Erdős 243 state coordinates, periodic iteration, and finite-horizon residue mechanics

[All problems and zones](BROWSER.md)

<a id="node-c3ccf50e3233830e"></a>
## forced_division_transports_congruence_through_the_shrinking_modulus

The forced numerator respects congruence. When two divisible values agree modulo d*m, exact division by the common nonzero factor d makes their quotients agree modulo m; applying this with d=index+2 gives the one-step forced-quotient transport.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The transport proves residue-class invariance for one finite search step; it neither supplies divisibility nor promotes finite-horizon survival to an infinite orbit.

- Lean declaration: [forcedNumerator_modEq](../../ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L26)
- Lean declaration: [quotient_modEq_of_modEq_mul](../../ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L41)
- Lean declaration: [forcedQuotient_modEq](../../ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L85)

- outgoing **generated_by**: [Z70::forced_negative_state_search_has_exact_finite_horizon_coordinates](BROWSER_Z70_1.md#node-b0a964ec557eca7a). The exact one-step congruence transport is obtained by applying polynomial compatibility and quotient cancellation to the forced numerator and the first visible factor of the recursive horizon modulus.

<a id="node-b0a964ec557eca7a"></a>
## forced_negative_state_search_has_exact_finite_horizon_coordinates

At index n the normalized constant-negative update has forced numerator (n+1)a^2-(n+2)a+(n+3). A horizon of remaining exact divisions is represented by a recursively shrinking modulus, and ForcedSurvives records exactly whether those divisions succeed.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: ForcedSurvives describes a fixed finite number of divisions only. Finite survivors exist and do not constitute an infinite orbit.

- Lean declaration: [forcedNumerator](../../ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L22)
- Lean declaration: [horizonModulus](../../ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L53)
- Lean declaration: [ForcedSurvives](../../ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L75)

- incoming **generated_by**: [Z70::forced_division_transports_congruence_through_the_shrinking_modulus](BROWSER_Z70_1.md#node-c3ccf50e3233830e). The exact one-step congruence transport is obtained by applying polynomial compatibility and quotient cancellation to the forced numerator and the first visible factor of the recursive horizon modulus.

<a id="node-a1e47977c70ccf59"></a>
## period_relations_and_fixed_phase_drifts_iterate_exactly

If x(n+h)=x(n), then x(n+t*h)=x(n) for every t. If instead C(n+h)=C(n)+M, then C(n+t*h)=C(n)+t*M for every t. Thus both a period relation and a fixed additive phase drift iterate with an exact closed form.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These generic laws assume the one-period equality or drift. They do not prove periodicity, produce a phase drift for an Erdős 243 orbit, or exclude an aperiodic negative branch.

- Lean declaration: [periodic_add_mul](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L461)
- Lean declaration: [phaseDrift_add_mul](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L476)

- outgoing **complements**: [Z70::product_cleared_reciprocal_tail_coordinates_are_exact](BROWSER_Z70_1.md#node-0a6bc32d1421cb35). The product-cleared coordinates describe one update, while the generic iteration laws package the period and additive-drift hypotheses used later in the negative-periodic branch; the relation asserts no periodicity of an actual orbit.

<a id="node-0a6bc32d1421cb35"></a>
## product_cleared_reciprocal_tail_coordinates_are_exact

The Erdős 243 integer-state interface uses the Sylvester successor a^2-a+1, denominator update aD, tail update aC-D, centered error D-(a-1)C, and next-multiplier defect aNext-(a^2-a+1). These are exact definitions of the five product-cleared coordinates used by the rigidity proofs.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Definitions alone prove no orbit exists, no centered error vanishes, and no recurrence is eventually Sylvester.

- Lean declaration: [sylvesterNext](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L37)
- Lean declaration: [nextDenState](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L41)
- Lean declaration: [nextTailState](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L45)
- Lean declaration: [centeredState](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L49)
- Lean declaration: [sylvesterDefect](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L53)

- incoming **complements**: [Z70::period_relations_and_fixed_phase_drifts_iterate_exactly](BROWSER_Z70_1.md#node-a1e47977c70ccf59). The product-cleared coordinates describe one update, while the generic iteration laws package the period and additive-drift hypotheses used later in the negative-periodic branch; the relation asserts no periodicity of an actual orbit.

