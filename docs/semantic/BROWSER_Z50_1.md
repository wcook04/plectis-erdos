# Z50_1: Critical dyadic-band reduction for upper resets

[All problems and zones](BROWSER.md)

<a id="node-90f48aee95f280c6"></a>
## actual_upper_reset_charge_stays_below_the_top_dyadic_boundary

For d≥5, whenever the concrete seam adjacent cut is an upper reset, its charge seamUpperResetCharge=4*overshoot+abovePulse is at most 2^(d+1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem applies only under successorCarries. It supplies admissibility for the generic collapse, not avoidance of any band.

- Lean declaration: [seamUpperResetCharge_le](../../Erdos249257/HalfUpperResetCriticalBand.lean#L131)

- incoming **generated_by**: [Z50::critical_band_supply_is_exactly_the_all_band_supply](BROWSER_Z50_1.md#node-a8b4d8b329bb070e). The concrete charge bound discharges E≤2^(d+1) at every actual upper reset.

<a id="node-6fa8628b2a215f81"></a>
## critical_band_supply_conditionally_forces_half_membership

If SeamUpperResetCriticalBandEscape holds, then 1/2 belongs to the Mersenne achievement set; the proof transports the critical producer through the exact equivalence and applies the existing all-band consumer.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The producer is unproved. The theorem neither establishes half-membership nor refutes the universal statement in Erdős #257, and it proves no equidistribution statement.

Open hypotheses: ["SeamUpperResetCriticalBandEscape: at every d≥13 that is an upper reset, there exists a critical index whose nearest dyadic boundary has margin at least 2(d+j) above the reset charge."]

- Lean declaration: [half_mem_mersenneAchievementSet_of_upperResetCriticalBandEscape](../../Erdos249257/HalfUpperResetCriticalBand.lean#L896)

- outgoing **generated_by**: [Z50::critical_band_supply_is_exactly_the_all_band_supply](BROWSER_Z50_1.md#node-a8b4d8b329bb070e). The endpoint transports the critical producer to the original all-band producer through the proved iff.

<a id="node-a8b4d8b329bb070e"></a>
## critical_band_supply_is_exactly_the_all_band_supply

SeamUpperResetCriticalBandEscape, requiring one certified critical gap at every late upper reset, is logically equivalent to SeamUpperResetDyadicBandEscape, which requires every indexed band escape.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The equivalence is an exact coordinate reformulation. Neither global producer is proved, and finite row checks do not discharge the universal late-row quantifier.

- Lean declaration: [seamUpperResetCriticalBandEscape_iff](../../Erdos249257/HalfUpperResetCriticalBand.lean#L883)

- outgoing **specialises**: [Z50::universal_dyadic_band_escape_collapses_to_one_critical_gap](BROWSER_Z50_1.md#node-b2d4ff874f3962ff). The global seam theorem applies the generic (d,E) collapse rowwise with E=seamUpperResetCharge.
- outgoing **generated_by**: [Z50::actual_upper_reset_charge_stays_below_the_top_dyadic_boundary](BROWSER_Z50_1.md#node-90f48aee95f280c6). The concrete charge bound discharges E≤2^(d+1) at every actual upper reset.
- incoming **generated_by**: [Z50::critical_band_supply_conditionally_forces_half_membership](BROWSER_Z50_1.md#node-6fa8628b2a215f81). The endpoint transports the critical producer to the original all-band producer through the proved iff.

<a id="node-4a026cfa9d2bd064"></a>
## critical_dyadic_band_index_encodes_the_nearest_power_transition

CriticalDyadicBandIndex d E j means j≤d, E≤2^(d-j+1), and either j=d or 2^(d-(j+1)+1)<E. It records a transition index where the indexed dyadic powers pass from at least E to below E.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The definition encodes a transition index but does not by itself prove a separately stated uniqueness theorem or a critical gap.

- Lean declaration: [CriticalDyadicBandIndex](../../Erdos249257/HalfUpperResetCriticalBand.lean#L33)

- incoming **generated_by**: [Z50::universal_dyadic_band_escape_collapses_to_one_critical_gap](BROWSER_Z50_1.md#node-b2d4ff874f3962ff). The existential certificate in the iff uses exactly CriticalDyadicBandIndex.

<a id="node-b2d4ff874f3962ff"></a>
## universal_dyadic_band_escape_collapses_to_one_critical_gap

If E≤2^(d+1), avoidance for every j≤d of the forbidden interval E<2^(d-j+1)<E+2(d+j) is equivalent to the existence of one CriticalDyadicBandIndex j with E+2(d+j)≤2^(d-j+1).

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The equivalence assumes E≤2^(d+1) and reduces quantifiers; it does not prove the required gap and is not a strength reduction.

- Lean declaration: [dyadicBandEscape_iff_exists_critical](../../Erdos249257/HalfUpperResetCriticalBand.lean#L108)

- outgoing **generated_by**: [Z50::critical_dyadic_band_index_encodes_the_nearest_power_transition](BROWSER_Z50_1.md#node-4a026cfa9d2bd064). The existential certificate in the iff uses exactly CriticalDyadicBandIndex.
- incoming **specialises**: [Z50::critical_band_supply_is_exactly_the_all_band_supply](BROWSER_Z50_1.md#node-a8b4d8b329bb070e). The global seam theorem applies the generic (d,E) collapse rowwise with E=seamUpperResetCharge.

