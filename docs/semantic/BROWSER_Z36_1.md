# Z36_1: Actual-LCM top-edge residue gaps, terminal compression, and conditional irrationality fan-in

[All problems and zones](BROWSER.md)

<a id="node-47a56098f86bac74"></a>
## actual_centered_magnitude_transports_to_adjacent_midband

PROVED PRODUCER TRANSPORT: cofinal terminal dominance implies terminal/carry-corridor escape; cofinal centered magnitude also implies corridor escape; the canonical actual-final magnitude supply is a special case of the flexible odd-rank supply; and any flexible centered-magnitude supply produces the adjacent-suffix midband.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Every implication is conditional on a cofinal supply definition that remains unproved.

Open hypotheses: ["one of the stated cofinal dominance or centered-magnitude supplies"]

- Lean declaration: [flexibleActualTerminalCarryCorridorEscapeSupply_of_dominance](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1917)
- Lean declaration: [flexibleActualTerminalCarryCorridorEscapeSupply_of_magnitude](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1938)
- Lean declaration: [flexibleActualTopEdgeMagnitudeSupply_of_actualFinal](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1991)
- Lean declaration: [powerTwoAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2007)

- outgoing **implies**: [Z36::terminal_carry_corridor_exactly_controls_integral_actual_orbits](BROWSER_Z36_1.md#node-069944afb4d840b8). A magnitude or dominance witness escapes one side of the exact carry corridor and can also be translated into the adjacent-suffix residue language.
- outgoing **transport_of**: [Z36::top_edge_half_word_band_is_exact_actual_centered_magnitude](BROWSER_Z36_1.md#node-f6869ec89ccb1ac1). The producer transport consumes the exact equivalence between the half-word top-edge band and the magnitude of the true centered state.
- incoming **implies**: [Z36::half_word_or_adjacent_midband_supplies_top_edge_gap](BROWSER_Z36_1.md#node-049521bd1778bd6a). The flexible centered-magnitude route first yields an adjacent midband, which the adjacent-depth dichotomy converts into a top-edge gap.

<a id="node-872c26b229074225"></a>
## first_dyadic_certificate_compresses_to_a_minimal_terminal_suffix

PROVED LOCALISATION: every nonempty dyadic certificate set has a first depth; a sufficiently long first certificate compresses to a terminal certificate, whose minimum terminal depth is identified exactly and which yields an explicit terminal certificate witness.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem localises a certificate once one exists. It does not prove cofinal existence of certificates for the actual-LCM word.

Open hypotheses: ["existence of at least one certified kill for the word under study"]

- Lean declaration: [certifiedKill_of_shifted_terminal](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L317)
- Lean declaration: [exists_firstCertifiedKill_of_exists_certifiedKill](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L378)
- Lean declaration: [FirstCertifiedKill.depth_floor](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L388)
- Lean declaration: [firstCertifiedKill_long_terminal](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L405)
- Lean declaration: [firstCertifiedKill_terminal_min](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L611)
- Lean declaration: [FirstCertifiedKill.exists_terminal_certificate](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L629)

- outgoing **implies**: [Z36::minimal_terminal_certificate_has_exact_socket_or_mixed_classification](BROWSER_Z36_1.md#node-6675a4ae94ebe6df). The first-certificate localisation reaches the minimal b+2 terminal depth, where the exact socket-or-mixed classification applies.

<a id="node-f416f27714685682"></a>
## full_terminal_dyadic_staircase_is_an_empty_producer

PROVED BARRIER: a fixed small modulus always has a positive divisible representative inside a carry strip, while a full terminal dyadic staircase at a modulus wider than the positive directed room is inconsistent; the retained tail-difference and actual-orbit nonintegrality implications from such a staircase therefore have impossible hypotheses.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The consumer-shaped nonintegrality theorems do not provide evidence for Erdős #249 because their terminal-staircase premise is inconsistent. Viable approaches must seek a nonzero residue gap rather than total dyadic annihilation.

- Lean declaration: [small_modulus_has_positive_divisible_candidate](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L165)
- Lean declaration: [actualLcmTailDiff_notMem_int_of_terminalDyadicStaircase](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2242)
- Lean declaration: [actualLcmTailOrbit_notMem_int_of_terminalDyadicStaircase](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2254)

- outgoing **barrier_for**: [Z36::top_edge_gap_has_exact_terminal_and_arithmetic_kill_forms](BROWSER_Z36_1.md#node-3a8fc581fdeaff44). The no-go rules out total terminal annihilation and redirects the search toward a nonzero residue gap or mixed terminal certificate.
- outgoing **barrier_for**: [Z36::seven_top_edge_supplies_each_conditionally_imply_totient_irrationality](BROWSER_Z36_1.md#node-4391c6d28ce8a542). The full staircase cannot serve as the missing cofinal antecedent for any irrationality endpoint, despite the retained implication-shaped wrapper.

<a id="node-049521bd1778bd6a"></a>
## half_word_or_adjacent_midband_supplies_top_edge_gap

PROVED PRODUCER CHAIN: the exact odd-guard top-edge half-word band supplies the adjacent-suffix midband; a cofinal adjacent midband supplies a cofinal actual-LCM top-edge residue gap at one of two adjacent depths; and the earlier odd-guard half-word-band supply reaches the same top-edge-gap supply using the linear LCM guard.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The source proves implications among supply predicates but no unconditional instance of any cofinal supply.

Open hypotheses: ["cofinal odd-guard half-word-band or adjacent-midband supply"]

- Lean declaration: [powerTwoAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2057)
- Lean declaration: [powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2108)
- Lean declaration: [powerTwoActualLcmTopEdgeResidueGapSupply_of_oddGuardHalfWordBand](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2121)

- outgoing **depends_on_open**: [Z36::power_two_lcm_guard_retains_linear_sign_lookahead](BROWSER_Z36_1.md#node-ae5262584a5aab36). The linear guard discharges the quantitative sign-buffer obligation, but the cofinal half-word or adjacent-midband producer itself remains open.
- outgoing **implies**: [Z36::actual_centered_magnitude_transports_to_adjacent_midband](BROWSER_Z36_1.md#node-47a56098f86bac74). The flexible centered-magnitude route first yields an adjacent midband, which the adjacent-depth dichotomy converts into a top-edge gap.
- incoming **implies**: [Z36::top_edge_and_carry_supplies_give_cofinal_orbit_nonintegrality](BROWSER_Z36_1.md#node-b6ec5e9f3a7897a9). A cofinal top-edge gap is one of the three exact supplies consumed to produce cofinal actual-orbit nonintegrality.
- incoming **depends_on_open**: [Z36::seven_top_edge_supplies_each_conditionally_imply_totient_irrationality](BROWSER_Z36_1.md#node-4391c6d28ce8a542). All endpoint wrappers still require an unproved cofinal producer; the top-edge-gap chain makes that common open antecedent explicit.

<a id="node-f4b599044d941506"></a>
## localized_top_edge_gap_excludes_integral_actual_lcm_orbit

PROVED CONDITIONAL NONINTEGRALITY: at an admissible power-two scale inside the positive-sign corridor, one localized actual-LCM top-edge residue gap proves that the corresponding actual-LCM tail orbit value is not an integer.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This is a one-scale implication. Erdős #249 requires a cofinal supply of such nonintegral orbit values, not a single certificate.

Open hypotheses: ["an actual-LCM top-edge residue gap at an admissible depth"]

- Lean declaration: [actualLcmTailOrbit_notMem_int_of_topEdgeResidueGap](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1314)

- outgoing **implies**: [Z36::top_edge_gap_has_exact_terminal_and_arithmetic_kill_forms](BROWSER_Z36_1.md#node-3a8fc581fdeaff44). Any of the exact terminal or arithmetic-kill forms that produces a top-edge gap can be consumed by the local orbit-nonintegrality theorem.
- incoming **complements**: [Z36::terminal_carry_corridor_exactly_controls_integral_actual_orbits](BROWSER_Z36_1.md#node-069944afb4d840b8). Both are local nonintegrality consumers: one excludes the positive endpoint strip by a residue gap, while the other excludes the exact open strip forced by the true carry.

<a id="node-6675a4ae94ebe6df"></a>
## minimal_terminal_certificate_has_exact_socket_or_mixed_classification

PROVED EQUIVALENCE AND CLASSIFICATION: at terminal depth b+2, certification is equivalent to either a local socket or a mixed two-level sign guard; every first certificate yields one of these alternatives, and existence of some certificate is equivalent to existence of a finite guard-cylinder witness.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The equivalence is local and finite. It does not show that the actual arithmetic word meets either guard at arbitrarily large scales.

- Lean declaration: [certifiedDyadic_twoLevel_socket_or_mixed](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L651)
- Lean declaration: [certifiedKill_of_dyadicMixedGuard](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L742)
- Lean declaration: [certifiedKill_bplus2_iff_socket_or_mixed](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L767)
- Lean declaration: [FirstCertifiedKill.exists_socket_or_mixed](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L802)
- Lean declaration: [exists_certifiedKill_iff_guardCylinderWitness](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L844)

- incoming **implies**: [Z36::first_dyadic_certificate_compresses_to_a_minimal_terminal_suffix](BROWSER_Z36_1.md#node-872c26b229074225). The first-certificate localisation reaches the minimal b+2 terminal depth, where the exact socket-or-mixed classification applies.
- outgoing **complements**: [Z36::top_edge_gap_has_exact_terminal_and_arithmetic_kill_forms](BROWSER_Z36_1.md#node-3a8fc581fdeaff44). The socket-or-mixed language classifies generic finite dyadic certificates, while the top-edge-gap language identifies the actual-LCM terminal residue and its arithmetic-kill producers.

<a id="node-ae5262584a5aab36"></a>
## power_two_lcm_guard_retains_linear_sign_lookahead

PROVED QUANTITATIVE GUARD: from a>=4, periodLcm(2^a) is strictly below 2^(2*2^a-(2a+4)); consequently, from a>=14 the odd-guarded canonical adjacent-suffix depth plus its successor and the full a+6 sign guard remain below 2*2^a.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This is a quantitative room estimate. It supplies neither a residue gap nor any of the cofinal producer hypotheses required for irrationality.

- Lean declaration: [centralBinom_succ_le_four_mul](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L28)
- Lean declaration: [four_mul_centralBinom_le_four_pow](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L41)
- Lean declaration: [centralBinom_le_four_pow_pred](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L56)
- Lean declaration: [periodLcm_two_mul_le_periodLcm_mul_four_pow_pred](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L72)
- Lean declaration: [linearGuardExponent_succ](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L81)
- Lean declaration: [linearGuardDepth_add_signGuard_lt](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L95)
- Lean declaration: [periodLcm_pow_two_lt_two_pow_linearGuard](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L106)
- Lean declaration: [oddGuardedCanonicalAdjacentSuffixDepth_powerTwo_succ_add_signGuard_lt](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L138)

- incoming **depends_on_open**: [Z36::half_word_or_adjacent_midband_supplies_top_edge_gap](BROWSER_Z36_1.md#node-049521bd1778bd6a). The linear guard discharges the quantitative sign-buffer obligation, but the cofinal half-word or adjacent-midband producer itself remains open.

<a id="node-4391c6d28ce8a542"></a>
## seven_top_edge_supplies_each_conditionally_imply_totient_irrationality

PROVED CONDITIONAL ENDPOINT FAMILY: each of seven cofinal producers—top-edge residue gap, adjacent-suffix midband, odd-guard top-edge half-word band, actual-final centered magnitude, flexible centered magnitude, flexible terminal dominance, or flexible terminal/carry-corridor escape—implies irrationality of the series sum phi(n)/2^n.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: All seven theorems are implications. The shared antecedent gap is substantive; counting multiple endpoint wrappers does not multiply mathematical progress or establish irrationality.

Open hypotheses: ["an unconditional proof of at least one cofinal producer hypothesis"]

- Lean declaration: [irrational_totientSeries_of_topEdgeResidueGapSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2184)
- Lean declaration: [irrational_totientSeries_of_adjacentSuffixMidbandSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2191)
- Lean declaration: [irrational_totientSeries_of_oddGuardTopEdgeHalfWordBandSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2198)
- Lean declaration: [irrational_totientSeries_of_actualFinalTopEdgeMagnitudeSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2205)
- Lean declaration: [irrational_totientSeries_of_flexibleActualTopEdgeMagnitudeSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2213)
- Lean declaration: [irrational_totientSeries_of_flexibleActualTerminalDominanceSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2221)
- Lean declaration: [irrational_totientSeries_of_flexibleActualTerminalCarryCorridorEscapeSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2230)

- outgoing **implies**: [Z36::top_edge_and_carry_supplies_give_cofinal_orbit_nonintegrality](BROWSER_Z36_1.md#node-b6ec5e9f3a7897a9). The endpoint family factors through cofinal actual-LCM orbit nonintegrality and then the established totient-series irrationality consumer.
- outgoing **depends_on_open**: [Z36::half_word_or_adjacent_midband_supplies_top_edge_gap](BROWSER_Z36_1.md#node-049521bd1778bd6a). All endpoint wrappers still require an unproved cofinal producer; the top-edge-gap chain makes that common open antecedent explicit.
- incoming **barrier_for**: [Z36::full_terminal_dyadic_staircase_is_an_empty_producer](BROWSER_Z36_1.md#node-f416f27714685682). The full staircase cannot serve as the missing cofinal antecedent for any irrationality endpoint, despite the retained implication-shaped wrapper.

<a id="node-069944afb4d840b8"></a>
## terminal_carry_corridor_exactly_controls_integral_actual_orbits

PROVED CONDITIONAL CORRIDOR: an integral actual-LCM orbit yields an exact integer-scaled orbit difference and, under the terminal fit, places the doubled actual centered lift strictly between the terminal arithmetic letter minus the directed endpoint bound and the terminal letter; escape through either side, or terminal dominance alone, proves nonintegrality.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem is a local nonintegrality consumer. It does not prove that corridor escape or dominance occurs cofinally.

Open hypotheses: ["an admissible odd rank whose actual centered state escapes the terminal/carry corridor"]

- Lean declaration: [exists_int_scaled_actualLcmTailOrbit_sub_eq](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1501)
- Lean declaration: [exists_int_actualLcmTailOrbit_close_of_actualTerminalCarryCorridor](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1579)
- Lean declaration: [actualTerminalCarryCorridorEscape_of_actualLcmOrbitSeparation](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1650)
- Lean declaration: [two_mul_actualOddHalfCenteredLift_eq_terminal_sub_trueCarry](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1678)
- Lean declaration: [actualLcmTailOrbit_notMem_int_of_actualTerminalCarryCorridorEscape](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1824)
- Lean declaration: [actualLcmTailOrbit_notMem_int_of_actualTerminalDominance](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1880)

- outgoing **complements**: [Z36::localized_top_edge_gap_excludes_integral_actual_lcm_orbit](BROWSER_Z36_1.md#node-f4b599044d941506). Both are local nonintegrality consumers: one excludes the positive endpoint strip by a residue gap, while the other excludes the exact open strip forced by the true carry.
- incoming **implies**: [Z36::actual_centered_magnitude_transports_to_adjacent_midband](BROWSER_Z36_1.md#node-47a56098f86bac74). A magnitude or dominance witness escapes one side of the exact carry corridor and can also be translated into the adjacent-suffix residue language.
- incoming **implies**: [Z36::top_edge_and_carry_supplies_give_cofinal_orbit_nonintegrality](BROWSER_Z36_1.md#node-b6ec5e9f3a7897a9). The cofinal dominance and corridor-escape supplies repeatedly instantiate the one-scale terminal/carry nonintegrality theorem.

<a id="node-b6ec5e9f3a7897a9"></a>
## top_edge_and_carry_supplies_give_cofinal_orbit_nonintegrality

PROVED CONDITIONAL FAN-IN: a cofinal top-edge residue-gap supply, flexible terminal-dominance supply, or flexible terminal/carry-corridor-escape supply each produces cofinally many power-two scales at which the actual-LCM tail orbit is nonintegral.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Cofinal nonintegrality follows only under an unproved supply hypothesis.

Open hypotheses: ["one of the three cofinal local certificate supplies"]

- Lean declaration: [actualLcmOrbitNonintegralitySupply_of_topEdgeResidueGap](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2153)
- Lean declaration: [actualLcmOrbitNonintegralitySupply_of_flexibleActualTerminalDominance](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2163)
- Lean declaration: [actualLcmOrbitNonintegralitySupply_of_flexibleActualTerminalCarryCorridorEscape](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2174)

- outgoing **implies**: [Z36::half_word_or_adjacent_midband_supplies_top_edge_gap](BROWSER_Z36_1.md#node-049521bd1778bd6a). A cofinal top-edge gap is one of the three exact supplies consumed to produce cofinal actual-orbit nonintegrality.
- outgoing **implies**: [Z36::terminal_carry_corridor_exactly_controls_integral_actual_orbits](BROWSER_Z36_1.md#node-069944afb4d840b8). The cofinal dominance and corridor-escape supplies repeatedly instantiate the one-scale terminal/carry nonintegrality theorem.
- incoming **implies**: [Z36::seven_top_edge_supplies_each_conditionally_imply_totient_irrationality](BROWSER_Z36_1.md#node-4391c6d28ce8a542). The endpoint family factors through cofinal actual-LCM orbit nonintegrality and then the established totient-series irrationality consumer.

<a id="node-3a8fc581fdeaff44"></a>
## top_edge_gap_has_exact_terminal_and_arithmetic_kill_forms

PROVED REPRESENTATION FAMILY: the actual-LCM top-edge residue-gap predicate is equivalent to a terminal suffix condition; diagonal suffix residue equals the corresponding window discrepancy; an adjacent-suffix midband forces a gap at one of two consecutive depths; and at the diagonal the gap is equivalent to the dedicated top-edge-gap predicate and is produced by either a fresh-loss residue certificate, an arithmetic kill, or a symmetric residue certificate.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The equivalences and one-step producers do not establish a cofinal supply of any certificate family.

- Lean declaration: [actualLcmTopEdgeResidueGap_iff_terminal](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L909)
- Lean declaration: [diagonalSuffixResidue_eq_windowDiscrepancy](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L933)
- Lean declaration: [actualLcmTopEdgeResidueGap_or_of_adjacentSuffixMidband](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L958)
- Lean declaration: [actualLcmTopEdgeResidueGap_zero_self_iff_lcmDiagonalTopEdgeGap](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1056)
- Lean declaration: [lcmDiagonalTopEdgeGap_of_diagonalFreshLossResidueCert](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1067)
- Lean declaration: [lcmDiagonalTopEdgeGap_of_lcmDiagonalArithmeticKill](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1079)
- Lean declaration: [actualLcmTopEdgeResidueGap_zero_self_of_diagonalSymmetricResidueCert](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1087)

- incoming **complements**: [Z36::minimal_terminal_certificate_has_exact_socket_or_mixed_classification](BROWSER_Z36_1.md#node-6675a4ae94ebe6df). The socket-or-mixed language classifies generic finite dyadic certificates, while the top-edge-gap language identifies the actual-LCM terminal residue and its arithmetic-kill producers.
- incoming **implies**: [Z36::localized_top_edge_gap_excludes_integral_actual_lcm_orbit](BROWSER_Z36_1.md#node-f4b599044d941506). Any of the exact terminal or arithmetic-kill forms that produces a top-edge gap can be consumed by the local orbit-nonintegrality theorem.
- incoming **reformulates**: [Z36::top_edge_half_word_band_is_exact_actual_centered_magnitude](BROWSER_Z36_1.md#node-f6869ec89ccb1ac1). The centered-magnitude equivalence translates an exact half-word residue band into actual-state language before the adjacent-depth gap dichotomy is applied.
- incoming **barrier_for**: [Z36::full_terminal_dyadic_staircase_is_an_empty_producer](BROWSER_Z36_1.md#node-f416f27714685682). The no-go rules out total terminal annihilation and redirects the search toward a nonzero residue gap or mixed terminal certificate.

<a id="node-f6869ec89ccb1ac1"></a>
## top_edge_half_word_band_is_exact_actual_centered_magnitude

PROVED EQUIVALENCE FAMILY: after centering the odd half-word residue and assuming the exact half-cell fit, membership in the top-edge band is equivalent to a lower bound on the magnitude of the true final centered state; the corresponding cofinal half-word-band supply is equivalent to the cofinal actual-final-centered-magnitude supply.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The equivalence does not prove either cofinal supply. The centered-magnitude lower bound remains an open producer condition.

- Lean declaration: [centeredTopEdgeBand_iff_abs](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1360)
- Lean declaration: [twice_topEdgeHalfWordThreshold_le_fourPow](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1378)
- Lean declaration: [oddGuardTopEdgeHalfWordBand_iff_actualFinalCenteredMagnitude](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1406)
- Lean declaration: [oddHalfWordTopEdgeBand_iff_actualCenteredMagnitude_of_fit](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1443)
- Lean declaration: [topEdgeHalfWordBandSupply_iff_actualFinalCenteredMagnitudeSupply](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1479)

- outgoing **reformulates**: [Z36::top_edge_gap_has_exact_terminal_and_arithmetic_kill_forms](BROWSER_Z36_1.md#node-3a8fc581fdeaff44). The centered-magnitude equivalence translates an exact half-word residue band into actual-state language before the adjacent-depth gap dichotomy is applied.
- incoming **transport_of**: [Z36::actual_centered_magnitude_transports_to_adjacent_midband](BROWSER_Z36_1.md#node-47a56098f86bac74). The producer transport consumes the exact equivalence between the half-word top-edge band and the magnitude of the true centered state.

