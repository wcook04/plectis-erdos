# Z93_1: Pair-balanced rational controls and affine tempered binary orbits

[All problems and zones](BROWSER.md)

<a id="node-963d2b62b2350b64"></a>
## bounded_pair_payloads_have_a_tempered_orbit_and_fixed_value_four_ninths

If a(0)=0 and every payload digit a(k) is at most one, then the pair-balanced coefficient sequence satisfies c(n)≤n, its explicit multiplier-nine orbit is tempered, and the resulting binary coefficient series is exactly 4/9 for every such payload.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem demonstrates that rich bounded payloads can coexist with a fixed rational value. It does not construct a totient-series model, refute a valid totient-specific invariant, or decide Erdős 249.

- Lean declaration: [globalBalancedCoeff_le_self](../../Erdos249257/GenericTailOrbitRigidity.lean#L482)
- Lean declaration: [globalBalancedOrbit_isTempered](../../Erdos249257/GenericTailOrbitRigidity.lean#L499)
- Lean declaration: [globalBalancedCoeff_value](../../Erdos249257/GenericTailOrbitRigidity.lean#L545)

- incoming **implies**: [Z93::pair_balanced_coefficients_and_orbits_have_exact_even_odd_coordinates](BROWSER_Z93_1.md#node-7c8b3ae93a654a0e). The parity formulas supply the recurrence and growth calculations used by the tempered-orbit and fixed-value theorem.
- incoming **barrier_for**: [Z93::the_pair_payload_is_recovered_exactly_from_even_carry_coordinates](BROWSER_Z93_1.md#node-534f3ce374e31907). It shows that the fixed rational value does not erase the arbitrary payload from the carry state.

<a id="node-409545f2c5acbb97"></a>
## identity_coefficients_have_an_affine_multiplier_one_tempered_orbit

The identity coefficient sequence c(n)=n has the explicit multiplier-one tempered orbit u(N)=N+2. Hence a coefficient family may have an affine, rank-two section structure while still satisfying the exact tempered carry recurrence.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The identity coefficients are not Euler's totient function. This control prevents finite-rank structure alone from being read as an irrationality criterion.

- Lean declaration: [idCoeff_temperedOrbit](../../Erdos249257/GenericTailOrbitRigidity.lean#L564)


<a id="node-7c8b3ae93a654a0e"></a>
## pair_balanced_coefficients_and_orbits_have_exact_even_odd_coordinates

For the pair-balanced control, the coefficients are k-a(k) at index 2k and 2a(k) at index 2k+1. Its explicit multiplier-nine orbit is 3k+4+9a(k) at index 2k and 6k+8 at index 2k+1.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The coordinate formulas concern an artificial rational control family, not the totient sequence, and do not imply an irrationality or nonintegrality statement.

- Lean declaration: [globalBalancedCoeff_even](../../Erdos249257/GenericTailOrbitRigidity.lean#L462)
- Lean declaration: [globalBalancedCoeff_odd](../../Erdos249257/GenericTailOrbitRigidity.lean#L466)
- Lean declaration: [globalBalancedOrbit_even](../../Erdos249257/GenericTailOrbitRigidity.lean#L471)
- Lean declaration: [globalBalancedOrbit_odd](../../Erdos249257/GenericTailOrbitRigidity.lean#L475)

- outgoing **implies**: [Z93::bounded_pair_payloads_have_a_tempered_orbit_and_fixed_value_four_ninths](BROWSER_Z93_1.md#node-963d2b62b2350b64). The parity formulas supply the recurrence and growth calculations used by the tempered-orbit and fixed-value theorem.

<a id="node-534f3ce374e31907"></a>
## the_pair_payload_is_recovered_exactly_from_even_carry_coordinates

At every even coordinate 2k, subtracting the zero-payload orbit from the orbit with payload a gives exactly 9a(k). Thus the arbitrary bounded payload remains explicitly visible in the carry even though every control has the same series value 4/9.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Payload recovery is a no-go witness for overly coarse generic state summaries only; it is not an obstruction theorem for the actual totient sequence.

- Lean declaration: [globalBalancedOrbit_even_payload](../../Erdos249257/GenericTailOrbitRigidity.lean#L557)

- outgoing **barrier_for**: [Z93::bounded_pair_payloads_have_a_tempered_orbit_and_fixed_value_four_ninths](BROWSER_Z93_1.md#node-963d2b62b2350b64). It shows that the fixed rational value does not erase the arbitrary payload from the carry state.

