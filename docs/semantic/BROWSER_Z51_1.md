# Z51_1: Actual-LCM positive tail corridor, true-survivor sign, and top-edge obstruction

[All problems and zones](BROWSER.md)

<a id="node-fef50b1240a62d36"></a>
## actual_lcm_tail_orbit_is_positive

For every a at least eight, actualLcmTailOrbit a is strictly positive.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Positivity does not show that the orbit is nonintegral and does not supply the Z28 nonintegrality frontier.

- Lean declaration: [actualLcmTailOrbit_pos](../../Erdos249257/TotientActualLcmOrbitSign.lean#L144)

- outgoing **specialises**: [Z51::actual_lcm_translated_tail_difference_is_positive_in_the_short_corridor](BROWSER_Z51_1.md#node-785143dca73528e8). actualLcmTailOrbit is the J=0 translated tail difference, and the source theorem applies the corridor result at that offset.

<a id="node-785143dca73528e8"></a>
## actual_lcm_translated_tail_difference_is_positive_in_the_short_corridor

For a at least eight and J+(a+6)<2*2^a, with H=periodLcm(2^a), the translated difference totientTail(2H+J)-totientTail(H+J) is strictly positive.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The result is uniform in unbounded a but only in the displayed short-offset corridor. Positivity is not nonintegrality or irrationality.

- Lean declaration: [actualLcmTailDiff_shift_pos](../../Erdos249257/TotientActualLcmOrbitSign.lean#L39)

- incoming **specialises**: [Z51::actual_lcm_tail_orbit_is_positive](BROWSER_Z51_1.md#node-fef50b1240a62d36). actualLcmTailOrbit is the J=0 translated tail difference, and the source theorem applies the corridor result at that offset.
- incoming **transport_of**: [Z51::integral_actual_lcm_tail_difference_has_negative_true_endpoint_survivor](BROWSER_Z51_1.md#node-7741c5d88a7a4420). Exact carry tracking transports positivity of the later translated tail difference into positivity of the carry and hence negativity of the true endpoint survivor.
- incoming **barrier_for**: [Z51::integrality_places_the_discrepancy_residue_at_the_top_edge](BROWSER_Z51_1.md#node-2b26a0f4e1e79792). The top-edge conclusion proves that the positive-sign corridor alone cannot furnish the symmetric central-arc exclusion needed for a modular kill.

<a id="node-7741c5d88a7a4420"></a>
## integral_actual_lcm_tail_difference_has_negative_true_endpoint_survivor

If an integer d represents the translated actual-LCM tail difference and the J+K corridor remains short, then -carryOrbit H (H+J) d K is strictly negative and is an endpoint survivor.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem removes only the nonnegative branch of the true survivor; negative true survivors and spurious survivors remain, so no nonintegrality follows.

Open hypotheses: ["an integer d whose real cast equals the displayed translated actual-LCM tail difference"]

- Lean declaration: [actualLcm_trueEndpointSurvivor_neg](../../Erdos249257/TotientActualLcmOrbitSign.lean#L172)

- outgoing **transport_of**: [Z51::actual_lcm_translated_tail_difference_is_positive_in_the_short_corridor](BROWSER_Z51_1.md#node-785143dca73528e8). Exact carry tracking transports positivity of the later translated tail difference into positivity of the carry and hence negativity of the true endpoint survivor.
- incoming **reformulates**: [Z51::integrality_places_the_discrepancy_residue_at_the_top_edge](BROWSER_Z51_1.md#node-2b26a0f4e1e79792). Under the room bound, the negative survivor's congruence class is represented exactly by the top-edge residue P-e.

<a id="node-2b26a0f4e1e79792"></a>
## integrality_places_the_discrepancy_residue_at_the_top_edge

Under the short-corridor, integral-representative, and room hypotheses, if e=carryOrbit H (H+J) d K, P=2^K, and B=2H+J+K+2, then the discrepancy residue is exactly P-e and lies strictly between P-B and P.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem explains why positivity alone gives no symmetric certified kill. It neither proves integrality nor excludes the top-edge band required by Z36.

Open hypotheses: ["an integer d representing the translated actual-LCM tail difference", "the room inequality 2H+J+K+2<2^K"]

- Lean declaration: [actualLcm_integral_forces_topEdgeResidue](../../Erdos249257/TotientActualLcmOrbitSign.lean#L211)

- outgoing **reformulates**: [Z51::integral_actual_lcm_tail_difference_has_negative_true_endpoint_survivor](BROWSER_Z51_1.md#node-7741c5d88a7a4420). Under the room bound, the negative survivor's congruence class is represented exactly by the top-edge residue P-e.
- outgoing **barrier_for**: [Z51::actual_lcm_translated_tail_difference_is_positive_in_the_short_corridor](BROWSER_Z51_1.md#node-785143dca73528e8). The top-edge conclusion proves that the positive-sign corridor alone cannot furnish the symmetric central-arc exclusion needed for a modular kill.

