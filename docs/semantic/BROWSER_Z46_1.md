# Z46_1: Actual-LCM top-edge producer coordinates and punctured-staircase cost

[All problems and zones](BROWSER.md)

<a id="node-77ba84dee528b998"></a>
## actual_lcm_top_edge_residue_gap_is_the_one_sided_terminal_condition

ActualLcmTopEdgeResidueGap a J K m records m≤K, B<2^m, and the actual discrepancy residue at modulus 2^m is at most 2^m-B, where H=periodLcm(2^a) and B=2*H+J+K+2.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The local predicate is not proved at cofinally many scales and is not itself an irrationality theorem.

- Lean declaration: [ActualLcmTopEdgeResidueGap](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L900)

- incoming **generated_by**: [Z46::cofinal_top_edge_residue_gap_supply_is_open](BROWSER_Z46_1.md#node-cfee9524e44e88b6). The cofinal producer quantifies the exact local top-edge residue-gap predicate.
- incoming **barrier_for**: [Z46::punctured_staircase_has_exact_half_turn_penultimate_cost](BROWSER_Z46_1.md#node-b1f46fc44c743bcd). The punctured route conditionally produces the local gap, while the theorem fixes its penultimate cost and rules out the extra-bit variant without disproving the gap itself.

<a id="node-2e172c26753fabde"></a>
## cofinal_actual_final_centered_magnitude_supply_is_open

PowerTwoActualFinalTopEdgeMagnitudeSupply is the canonical guarded cofinal lower bound on the absolute centered quantity actualOddHalfCenteredLift a q.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The predicate is not proved. Only this producer and the odd-guard half-word producer have a proved equivalence.

Open hypotheses: ["PowerTwoActualFinalTopEdgeMagnitudeSupply"]

- Lean declaration: [PowerTwoActualFinalTopEdgeMagnitudeSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1471)

- incoming **equivalent_to**: [Z46::cofinal_odd_guard_half_word_band_supply_is_open](BROWSER_Z46_1.md#node-e91e500739331a79). topEdgeHalfWordBandSupply_iff_actualFinalCenteredMagnitudeSupply proves the exact iff.
- outgoing **implies**: [Z46::cofinal_flexible_actual_top_edge_magnitude_supply_is_open](BROWSER_Z46_1.md#node-a4a9eb83e15be6bc). flexibleActualTopEdgeMagnitudeSupply_of_actualFinal proves the canonical-to-flexible transport.

<a id="node-fc81071032a59bc4"></a>
## cofinal_adjacent_suffix_midband_supply_is_open

PowerTwoAdjacentSuffixMidbandSupply is the cofinal two-sided adjacent-suffix midband producer, buffered so either adjacent depth remains in the sign corridor.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The supply is not proved, and its sufficiency does not make it necessary for nonintegrality.

Open hypotheses: ["PowerTwoAdjacentSuffixMidbandSupply"]

- Lean declaration: [PowerTwoAdjacentSuffixMidbandSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1334)

- outgoing **implies**: [Z46::cofinal_top_edge_residue_gap_supply_is_open](BROWSER_Z46_1.md#node-cfee9524e44e88b6). powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband proves this one-way transport.
- incoming **implies**: [Z46::cofinal_odd_guard_half_word_band_supply_is_open](BROWSER_Z46_1.md#node-e91e500739331a79). powerTwoAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand proves this one-way transport.
- incoming **implies**: [Z46::cofinal_flexible_actual_top_edge_magnitude_supply_is_open](BROWSER_Z46_1.md#node-a4a9eb83e15be6bc). powerTwoAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude proves the transport.

<a id="node-a4a9eb83e15be6bc"></a>
## cofinal_flexible_actual_top_edge_magnitude_supply_is_open

PowerTwoFlexibleActualTopEdgeMagnitudeSupply asks for cofinally many flexible odd-rank room-and-fit scales with the required centered actual top-edge magnitude.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The supply is unproved. Its proved routes are one-way sufficient transports and do not establish strict inequivalence or necessity.

Open hypotheses: ["PowerTwoFlexibleActualTopEdgeMagnitudeSupply"]

- Lean declaration: [PowerTwoFlexibleActualTopEdgeMagnitudeSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1927)

- incoming **implies**: [Z46::cofinal_actual_final_centered_magnitude_supply_is_open](BROWSER_Z46_1.md#node-2e172c26753fabde). flexibleActualTopEdgeMagnitudeSupply_of_actualFinal proves the canonical-to-flexible transport.
- outgoing **implies**: [Z46::cofinal_adjacent_suffix_midband_supply_is_open](BROWSER_Z46_1.md#node-fc81071032a59bc4). powerTwoAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude proves the transport.
- outgoing **implies**: [Z46::cofinal_flexible_terminal_carry_corridor_escape_supply_is_open](BROWSER_Z46_1.md#node-b069da6f0ff2da22). flexibleActualTerminalCarryCorridorEscapeSupply_of_magnitude proves this one-way implication.

<a id="node-b069da6f0ff2da22"></a>
## cofinal_flexible_terminal_carry_corridor_escape_supply_is_open

PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply asks for cofinally many flexible odd-rank room-and-fit scales at which the exact terminal carry corridor is escaped on at least one side.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The supply is unproved and is sufficient, not proved necessary, for the existing nonintegrality endpoint.

Open hypotheses: ["PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply"]

- Lean declaration: [PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1895)

- incoming **implies**: [Z46::cofinal_flexible_terminal_dominance_supply_is_open](BROWSER_Z46_1.md#node-8f5bbc78c7fe20c7). flexibleActualTerminalCarryCorridorEscapeSupply_of_dominance proves this one-way implication.
- incoming **implies**: [Z46::cofinal_flexible_actual_top_edge_magnitude_supply_is_open](BROWSER_Z46_1.md#node-a4a9eb83e15be6bc). flexibleActualTerminalCarryCorridorEscapeSupply_of_magnitude proves this one-way implication.

<a id="node-8f5bbc78c7fe20c7"></a>
## cofinal_flexible_terminal_dominance_supply_is_open

PowerTwoFlexibleActualTerminalDominanceSupply is the stronger one-sided flexible producer requiring the displayed terminal dominance inequality d≤2*u at cofinally many room-and-fit scales.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The supply is not proved and is not refuted by the existing sign discussion.

Open hypotheses: ["PowerTwoFlexibleActualTerminalDominanceSupply"]

- Lean declaration: [PowerTwoFlexibleActualTerminalDominanceSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1908)

- outgoing **implies**: [Z46::cofinal_flexible_terminal_carry_corridor_escape_supply_is_open](BROWSER_Z46_1.md#node-b069da6f0ff2da22). flexibleActualTerminalCarryCorridorEscapeSupply_of_dominance proves this one-way implication.

<a id="node-e91e500739331a79"></a>
## cofinal_odd_guard_half_word_band_supply_is_open

PowerTwoOddGuardTopEdgeHalfWordBandSupply is the cofinal guarded odd-depth half-word residue-band producer.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The supply is open. Finite bands do not discharge its cofinal quantifier.

Open hypotheses: ["PowerTwoOddGuardTopEdgeHalfWordBandSupply"]

- Lean declaration: [PowerTwoOddGuardTopEdgeHalfWordBandSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1349)

- outgoing **implies**: [Z46::cofinal_adjacent_suffix_midband_supply_is_open](BROWSER_Z46_1.md#node-fc81071032a59bc4). powerTwoAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand proves this one-way transport.
- outgoing **equivalent_to**: [Z46::cofinal_actual_final_centered_magnitude_supply_is_open](BROWSER_Z46_1.md#node-2e172c26753fabde). topEdgeHalfWordBandSupply_iff_actualFinalCenteredMagnitudeSupply proves the exact iff.

<a id="node-cfee9524e44e88b6"></a>
## cofinal_top_edge_residue_gap_supply_is_open

PowerTwoActualLcmTopEdgeResidueGapSupply is the cofinal supply of power-two scales carrying the local actual-LCM top-edge residue gap.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The supply is not proved. Its existing irrationality consumer does not establish the antecedent.

Open hypotheses: ["PowerTwoActualLcmTopEdgeResidueGapSupply"]

- Lean declaration: [PowerTwoActualLcmTopEdgeResidueGapSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1325)

- outgoing **generated_by**: [Z46::actual_lcm_top_edge_residue_gap_is_the_one_sided_terminal_condition](BROWSER_Z46_1.md#node-77ba84dee528b998). The cofinal producer quantifies the exact local top-edge residue-gap predicate.
- incoming **implies**: [Z46::cofinal_adjacent_suffix_midband_supply_is_open](BROWSER_Z46_1.md#node-fc81071032a59bc4). powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband proves this one-way transport.

<a id="node-b1f46fc44c743bcd"></a>
## punctured_staircase_has_exact_half_turn_penultimate_cost

Under the theorem's room hypotheses and an assumed actual-LCM terminal punctured dyadic staircase, the penultimate arithmetic letter is exactly 2^(m-1), and 2^m<2*B for the displayed terminal budget B.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem assumes a punctured staircase and constructs none. It fixes a first-scale cost and excludes an extra-bit version; it does not prove the local top-edge gap impossible.

- Lean declaration: [puncturedDyadicStaircase_penultimate_eq_half](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1187)

- outgoing **barrier_for**: [Z46::actual_lcm_top_edge_residue_gap_is_the_one_sided_terminal_condition](BROWSER_Z46_1.md#node-77ba84dee528b998). The punctured route conditionally produces the local gap, while the theorem fixes its penultimate cost and rules out the extra-bit variant without disproving the gap itself.

