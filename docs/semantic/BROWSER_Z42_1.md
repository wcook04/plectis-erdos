# Z42_1: Rank-27 auxiliary ratchet: forced seam input, phase refinement, and exact non-closure boundary

[All problems and zones](BROWSER.md)

<a id="node-447e572d4bd1f10b"></a>
## all_right_landing_bridge_transports_concrete_excess_into_the_ratchet

PROVED CONDITIONAL BRIDGE: the displayed no-carry, middle-branch, and charge hypotheses force landing excess seamExcess(D+1)=2. If, in addition, the concrete seam extends right forever from that landing, then the rank-27 ratchet bounds 3*seamExcess-3; death of the auxiliary budget would contradict those hypotheses.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: No theorem here asserts that any D satisfies these hypotheses. Direct evaluation found no landing excess two in the audited range s=5..102; that measurement is not a Lean theorem. The conditional contradiction is not an unconditional exclusion.

Open hypotheses: ["the displayed no-carry, final-middle, and pulse-charge hypotheses at a concrete D", "an all-right concrete seam tail from D+1 onward", "a concrete landing equality seamExcess(D+1)=2, either assumed or produced by the displayed local hypotheses"]

- Lean declaration: [ratchetRun27_bound](../../ErdosProblems/Lift/AngleB1.lean#L506)
- Lean declaration: [ratchet27_excludes](../../ErdosProblems/Lift/AngleB1.lean#L557)
- Lean declaration: [seamExcess_landing_eq_two](../../ErdosProblems/Lift/AngleB1.lean#L594)

- outgoing **transport_of**: [Z42::ratchet_step_is_ordered_and_twelve_is_an_escape_threshold](BROWSER_Z42_1.md#node-d3a26501d32dce47). The conditional bridge compares the concrete excess update against the already ordered auxiliary ratchet recurrence.
- incoming **generated_by**: [Z42::conditional_final_middle_configuration_must_land_in_the_auxiliary_phase_set](BROWSER_Z42_1.md#node-4be16aa62af3f61f). The bridge turns the displayed concrete hypotheses into ratchet domination, and finite-core death would then be contradictory.

<a id="node-4be16aa62af3f61f"></a>
## conditional_final_middle_configuration_must_land_in_the_auxiliary_phase_set

PROVED CONDITIONAL NECESSITY: a D>=31 satisfying the displayed no-carry, final-middle, all-right-tail, and charge hypotheses must have D modulo 24570 in the rank-27 auxiliary survivor set.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: No audited concrete landing instance satisfies the implied landing equality in the stated checked range. Membership in survivors27 remains necessary only under the full displayed hypothesis package.

Open hypotheses: ["a concrete D satisfying every no-carry, middle-branch, all-right-tail, and charge hypothesis displayed by the theorem"]

- Lean declaration: [finalMiddleCell_neg_two_mem_survivors27](../../ErdosProblems/Lift/AngleB1.lean#L957)

- outgoing **generated_by**: [Z42::all_right_landing_bridge_transports_concrete_excess_into_the_ratchet](BROWSER_Z42_1.md#node-447e572d4bd1f10b). The bridge turns the displayed concrete hypotheses into ratchet domination, and finite-core death would then be contradictory.
- outgoing **depends_on_open**: [Z42::finite_core_makes_the_rank_twenty_seven_phase_set_a_fixed_point](BROWSER_Z42_1.md#node-7ae92c9aef48c698). Finite-core exclusion becomes a statement about a concrete D only under the theorem's unproved realizability and all-right-tail hypotheses.

<a id="node-7ae92c9aef48c698"></a>
## finite_core_makes_the_rank_twenty_seven_phase_set_a_fixed_point

PROVED AUXILIARY FIXED POINT: over all 24570 residue phases, after six ratchet steps every budget is either zero or at least 12. Every phase nonzero at depth six is therefore positive at every depth, so the surviving auxiliary phase set is already stable.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Stability is internal to the auxiliary recurrence. The survivor set is not certified as a set of realizable #257 classes.

- Lean declaration: [ratchet27_finite_core](../../ErdosProblems/Lift/AngleB1.lean#L690)
- Lean declaration: [ratchetRun27_pos_of_alive](../../ErdosProblems/Lift/AngleB1.lean#L712)

- outgoing **generated_by**: [Z42::ratchet_step_is_ordered_and_twelve_is_an_escape_threshold](BROWSER_Z42_1.md#node-d3a26501d32dce47). The finite core reaches the dichotomy zero-or-at-least-twelve, after which absorbing zero and the escape threshold settle every future depth.
- incoming **depends_on_open**: [Z42::conditional_final_middle_configuration_must_land_in_the_auxiliary_phase_set](BROWSER_Z42_1.md#node-4be16aa62af3f61f). Finite-core exclusion becomes a statement about a concrete D only under the theorem's unproved realizability and all-right-tail hypotheses.
- incoming **finite_instance_of**: [Z42::phase_fourteen_survives_forever_so_the_auxiliary_ratchet_stalls](BROWSER_Z42_1.md#node-337310d6461dc0cc). Phase 14 is one explicit nonzero depth-six phase, so the fixed-point theorem propagates its positivity to every depth.

<a id="node-1ce004bb0fde6c40"></a>
## nine_rank_pulse_floor_is_periodic_bounded_and_concretely_dominated

PROVED PULSE FLOOR: the nine forced ranks give a pulse floor bounded above by 11 on every row and periodic with period 24570. From row 32 onward, because all nine ranks lie in the concrete greedy seam support, this auxiliary floor is a genuine lower bound for the below-pulse of the concrete adjacent cut.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The constant floor controls only the chosen nine-rank contribution. It is not an equality with the full concrete below-pulse and does not by itself constrain a realizable final-middle cell.

- Lean declaration: [pulseFloor27_le_eleven](../../ErdosProblems/Lift/AngleB1.lean#L312)
- Lean declaration: [pulseFloor27_add_period](../../ErdosProblems/Lift/AngleB1.lean#L325)
- Lean declaration: [pulseFloor27_le_belowPulse](../../ErdosProblems/Lift/AngleB1.lean#L351)

- outgoing **generated_by**: [Z42::rank_twenty_seven_is_forced_in_the_concrete_seam_from_row_thirty_two](BROWSER_Z42_1.md#node-04059ca1badcfddb). Rank 27 can enter the nine-rank concrete lower bound only after its selected-support theorem is proved from row 32 onward.
- incoming **complements**: [Z42::rank_twenty_seven_pulse_has_exact_three_per_window_budget](BROWSER_Z42_1.md#node-60d61055e514bd2f). The floor theorem bounds the total nine-rank charge rowwise, while the window theorem gives the exact aggregate contribution of its new rank-27 term.
- incoming **generated_by**: [Z42::ratchet_step_is_ordered_and_twelve_is_an_escape_threshold](BROWSER_Z42_1.md#node-d3a26501d32dce47). The constant pulse bound of 11 is exactly what makes budget 12 forward-invariant under the ratchet step.

<a id="node-337310d6461dc0cc"></a>
## phase_fourteen_survives_forever_so_the_auxiliary_ratchet_stalls

PROVED NON-CLOSURE BARRIER: phase 14 belongs to the rank-27 auxiliary survivor set, and its ratchet budget stays positive at every depth. Thus adding rank 27 removes some auxiliary phases but cannot empty the auxiliary set or close the phase sieve by iteration alone.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem does not assert that the concrete half-membership branch realizes phase 14. It proves only that this auxiliary recurrence cannot exclude that residue class, so the computation does not solve or narrow Erdős #257 without further concrete input.

- Lean declaration: [fourteen_mem_survivors27](../../ErdosProblems/Lift/AngleB1.lean#L1021)
- Lean declaration: [ratchetRun27_pos_fourteen](../../ErdosProblems/Lift/AngleB1.lean#L1033)

- outgoing **finite_instance_of**: [Z42::finite_core_makes_the_rank_twenty_seven_phase_set_a_fixed_point](BROWSER_Z42_1.md#node-7ae92c9aef48c698). Phase 14 is one explicit nonzero depth-six phase, so the fixed-point theorem propagates its positivity to every depth.
- outgoing **barrier_for**: [Z42::rank_twenty_seven_strictly_shrinks_the_auxiliary_phase_sieve](BROWSER_Z42_1.md#node-676ed0ac88271d70). Strict shrinkage removes phase 200, but phase 14 proves that repeated rank-27 ratchet evolution does not empty the surviving set.

<a id="node-04059ca1badcfddb"></a>
## rank_twenty_seven_is_forced_in_the_concrete_seam_from_row_thirty_two

PROVED CONCRETE INPUT: for every seam row s>=32, after the eight previously forced ranks 2,3,6,7,14,20,21,26, the exact integer comparison selects rank 27. Consequently the greedy bit prefix through rank 27 has the displayed normal form and 27 belongs to the concrete seam support.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The Lean theorem begins at s=32. Failure at rows 28 through 31 is measured outside this theorem. A forced selected rank does not prove a cofinal safe-skip condition or membership of one half in the Mersenne achievement set.

- Lean declaration: [seamGreedy_postTwentySix_decision_twentySeven](../../ErdosProblems/Lift/AngleB1.lean#L110)
- Lean declaration: [seamGreedyBits_head2367_14_20_21_26_27](../../ErdosProblems/Lift/AngleB1.lean#L214)
- Lean declaration: [twentySeven_mem_seamGreedySupport](../../ErdosProblems/Lift/AngleB1.lean#L236)

- incoming **generated_by**: [Z42::nine_rank_pulse_floor_is_periodic_bounded_and_concretely_dominated](BROWSER_Z42_1.md#node-1ce004bb0fde6c40). Rank 27 can enter the nine-rank concrete lower bound only after its selected-support theorem is proved from row 32 onward.

<a id="node-60d61055e514bd2f"></a>
## rank_twenty_seven_pulse_has_exact_three_per_window_budget

PROVED EXACT WINDOW BUDGET: the rank-27 pulse is periodic with period 27 and contributes exactly three units over every 27 consecutive rows, independently of the starting row.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The identity is pulse bookkeeping. It neither asserts that an auxiliary phase is concretely realized nor supplies a contradiction on the live #257 branch.

- Lean declaration: [pulseAt_twentySeven_window](../../ErdosProblems/Lift/AngleB1.lean#L999)

- outgoing **complements**: [Z42::nine_rank_pulse_floor_is_periodic_bounded_and_concretely_dominated](BROWSER_Z42_1.md#node-1ce004bb0fde6c40). The floor theorem bounds the total nine-rank charge rowwise, while the window theorem gives the exact aggregate contribution of its new rank-27 term.

<a id="node-676ed0ac88271d70"></a>
## rank_twenty_seven_strictly_shrinks_the_auxiliary_phase_sieve

PROVED STRICT AUXILIARY SHRINKAGE: phase 200 survives the lifted rank-26 residue conditions but is killed by the rank-27 recurrence, so the rank-27 phase set is a proper subset and has strictly smaller cardinality. On the base block [0,2730), Lean computes exactly 390 survivors and proves 390<412.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The exact kernel-checked base-block count is 390 versus 412. The full-modulus counts 3522 and 3708 are measured outside Lean and are not claimed here. Shrinking an auxiliary set is not progress on the live #257 branch without a realizability bridge.

- Lean declaration: [twoHundred_mem_liftedSurvivors26](../../ErdosProblems/Lift/AngleB1.lean#L873)
- Lean declaration: [survivors27_ssubset_liftedSurvivors26](../../ErdosProblems/Lift/AngleB1.lean#L886)
- Lean declaration: [survivors27_card_lt](../../ErdosProblems/Lift/AngleB1.lean#L894)
- Lean declaration: [survivors27Base_card](../../ErdosProblems/Lift/AngleB1.lean#L913)
- Lean declaration: [survivors27Base_card_lt](../../ErdosProblems/Lift/AngleB1.lean#L947)

- outgoing **specialises**: [Z42::rank_twenty_seven_survival_refines_the_rank_twenty_six_sieve](BROWSER_Z42_1.md#node-7ef6759ac6695208). The general subset relation becomes strict because phase 200 is exhibited in the lifted rank-26 set and excluded from the rank-27 set.
- incoming **barrier_for**: [Z42::phase_fourteen_survives_forever_so_the_auxiliary_ratchet_stalls](BROWSER_Z42_1.md#node-337310d6461dc0cc). Strict shrinkage removes phase 200, but phase 14 proves that repeated rank-27 ratchet evolution does not empty the surviving set.

<a id="node-7ef6759ac6695208"></a>
## rank_twenty_seven_survival_refines_the_rank_twenty_six_sieve

PROVED AUXILIARY REFINEMENT: the earlier eight-rank finite core kills every rank-26 phase outside its residue sieve by depth three. Since the rank-27 budget is no larger than the rank-26 budget, every phase surviving the rank-27 depth-six test belongs to the lifted rank-26 survivor sieve.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Subset refinement is only about auxiliary phase predicates. It does not establish that any removed or surviving phase occurs in a concrete final-middle configuration.

- Lean declaration: [ratchet26_finite_core](../../ErdosProblems/Lift/AngleB1.lean#L813)
- Lean declaration: [survivorPhase26_of_ratchetRun27_ne_zero](../../ErdosProblems/Lift/AngleB1.lean#L826)

- outgoing **generated_by**: [Z42::ratchet_step_is_ordered_and_twelve_is_an_escape_threshold](BROWSER_Z42_1.md#node-d3a26501d32dce47). Monotone comparison of rank-27 and rank-26 budgets transports survival into the older phase sieve.
- incoming **specialises**: [Z42::rank_twenty_seven_strictly_shrinks_the_auxiliary_phase_sieve](BROWSER_Z42_1.md#node-676ed0ac88271d70). The general subset relation becomes strict because phase 200 is exhibited in the lifted rank-26 set and excluded from the rank-27 set.

<a id="node-d3a26501d32dce47"></a>
## ratchet_step_is_ordered_and_twelve_is_an_escape_threshold

PROVED AUXILIARY DYNAMICS: one ratchet step is antitone in pulse charge and monotone in its budget. Since the nine-rank pulse floor is at most 11, every budget at least 12 remains at least 12 after a step. Adding rank 27 can only decrease the auxiliary budget relative to the earlier rank-26 recurrence.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: These are statements about the auxiliary recurrence. Interpreting its budget as a bound for a concrete seam excess requires the separate all-right and landing bridge.

- Lean declaration: [ratchetStep_mono](../../ErdosProblems/Lift/AngleB1.lean#L407)
- Lean declaration: [twelve_le_ratchetStep](../../ErdosProblems/Lift/AngleB1.lean#L412)
- Lean declaration: [ratchetRun27_le_ratchetRun26](../../ErdosProblems/Lift/AngleB1.lean#L446)

- outgoing **generated_by**: [Z42::nine_rank_pulse_floor_is_periodic_bounded_and_concretely_dominated](BROWSER_Z42_1.md#node-1ce004bb0fde6c40). The constant pulse bound of 11 is exactly what makes budget 12 forward-invariant under the ratchet step.
- incoming **transport_of**: [Z42::all_right_landing_bridge_transports_concrete_excess_into_the_ratchet](BROWSER_Z42_1.md#node-447e572d4bd1f10b). The conditional bridge compares the concrete excess update against the already ordered auxiliary ratchet recurrence.
- incoming **generated_by**: [Z42::finite_core_makes_the_rank_twenty_seven_phase_set_a_fixed_point](BROWSER_Z42_1.md#node-7ae92c9aef48c698). The finite core reaches the dichotomy zero-or-at-least-twelve, after which absorbing zero and the escape threshold settle every future depth.
- incoming **generated_by**: [Z42::rank_twenty_seven_survival_refines_the_rank_twenty_six_sieve](BROWSER_Z42_1.md#node-7ef6759ac6695208). Monotone comparison of rank-27 and rank-26 budgets transports survival into the older phase sieve.

