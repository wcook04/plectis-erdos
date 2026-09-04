# Z41_1: Three-branch seam dynamics, finite-horizon shadowing, and exact defect witnesses

[All problems and zones](BROWSER.md)

<a id="node-6d5daf75bbb82992"></a>
## a_five_row_carry_free_segment_realises_the_shadowing_law

VERIFIED FINITE INSTANCE: rows 14 through 18 are carry-free, row 14 is followed by a half-point hit, and the five-step segment from row 14 to row 19 satisfies both the integral shadow identity and the normalized doubling-shadow identity.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: A five-row segment establishes non-vacuity of the hypotheses only. It gives no eventual or cofinal carry-free statement.

- Lean declaration: [hitAt_fourteen](../../ErdosProblems/Three/T2.lean#L1091)
- Lean declaration: [remainder_sixteen](../../ErdosProblems/Three/T2.lean#L1100)
- Lean declaration: [remainder_eighteen](../../ErdosProblems/Three/T2.lean#L1103)
- Lean declaration: [carryFree_run_fourteen](../../ErdosProblems/Three/T2.lean#L1106)
- Lean declaration: [shadow_witness](../../ErdosProblems/Three/T2.lean#L1125)
- Lean declaration: [y_shadow_witness](../../ErdosProblems/Three/T2.lean#L1135)

- outgoing **finite_instance_of**: [Z41::carry_free_segments_have_exact_finite_horizon_doubling_shadows](BROWSER_Z41_1.md#node-9876080fcea617e7). The segment [14,19) satisfies the carry-free hypothesis and yields the integral and normalized shadow identities.

<a id="node-8835f1ba283353cd"></a>
## a_small_remainder_forces_the_exact_middle_branch

PROVED: whenever 4rho_s<2^(s+1)+4 at a row s>=5, the carry predicate is false, the middle trigger holds, and the successor remainder obeys the exact middle-branch recurrence without any additional branch hypothesis.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The result applies only under the displayed small-remainder inequality and gives no frequency statement for such rows.

- Lean declaration: [not_successorCarries_of_four_mul_remainder_lt](../../ErdosProblems/Three/T2.lean#L811)
- Lean declaration: [middleTrigger_of_four_mul_remainder_lt](../../ErdosProblems/Three/T2.lean#L816)
- Lean declaration: [middleBranch_remainder_succ_eq_of_small](../../ErdosProblems/Three/T2.lean#L824)

- outgoing **specialises**: [Z41::explicit_thresholds_partition_each_row_into_three_branches](BROWSER_Z41_1.md#node-e103a68a78cfef0f). The stronger small-remainder inequality simultaneously excludes the carry threshold and implies the middle threshold.

<a id="node-4e788967a8918b5c"></a>
## adjacent_gap_excess_is_an_exact_nonnegative_gap_coordinate

PROVED: for every seam row s>=5, the actual adjacent-word gap is at least 2^(s+1), and is exactly 2^(s+1) plus the natural-valued adjacent-gap excess.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This coordinate measures one finite row. Its nonnegativity supplies neither a small-defect estimate nor a cofinal statement.

- Lean declaration: [adjGapExcess](../../ErdosProblems/Three/T2.lean#L205)
- Lean declaration: [two_pow_le_adjacentGap](../../ErdosProblems/Three/T2.lean#L209)
- Lean declaration: [adjGapExcess_spec](../../ErdosProblems/Three/T2.lean#L222)

- incoming **generated_by**: [Z41::explicit_thresholds_partition_each_row_into_three_branches](BROWSER_Z41_1.md#node-e103a68a78cfef0f). The carry threshold eliminates the overshoot through the exact adjacent-gap excess identity.
- incoming **specialises**: [Z41::largest_declined_rank_quantitatively_controls_the_carry_defect](BROWSER_Z41_1.md#node-55acd6c2539befa8). The rank identities replace the abstract nonnegative excess by exact or quantitative formulas in the half and late zones.

<a id="node-9497d01a942eeb33"></a>
## all_three_branches_occur_in_kernel_checked_finite_rows

VERIFIED FINITE INSTANCES: exact remainder values certify the middle branch at row 14 with below-pulse 3, the right branch at row 9 with below-pulse 1, and the carry branch at rows 13, 19, 25, and 31.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The four carry rows do not prove CarryCofinally, and the finite branch witnesses do not imply any asymptotic distribution of branches.

- Lean declaration: [remainder_thirteen](../../ErdosProblems/Three/T2.lean#L852)
- Lean declaration: [remainder_fourteen](../../ErdosProblems/Three/T2.lean#L855)
- Lean declaration: [remainder_fifteen](../../ErdosProblems/Three/T2.lean#L858)
- Lean declaration: [remainder_nineteen](../../ErdosProblems/Three/T2.lean#L861)
- Lean declaration: [remainder_twenty](../../ErdosProblems/Three/T2.lean#L864)
- Lean declaration: [remainder_twentyfive](../../ErdosProblems/Three/T2.lean#L867)
- Lean declaration: [remainder_twentysix](../../ErdosProblems/Three/T2.lean#L870)
- Lean declaration: [remainder_thirtyone](../../ErdosProblems/Three/T2.lean#L873)
- Lean declaration: [remainder_thirtytwo](../../ErdosProblems/Three/T2.lean#L876)
- Lean declaration: [middleTrigger_fourteen](../../ErdosProblems/Three/T2.lean#L881)
- Lean declaration: [not_successorCarries_fourteen](../../ErdosProblems/Three/T2.lean#L885)
- Lean declaration: [belowPulse_fourteen](../../ErdosProblems/Three/T2.lean#L892)
- Lean declaration: [right_triggers_nine](../../ErdosProblems/Three/T2.lean#L900)
- Lean declaration: [belowPulse_nine](../../ErdosProblems/Three/T2.lean#L904)
- Lean declaration: [successorCarries_thirteen](../../ErdosProblems/Three/T2.lean#L912)
- Lean declaration: [successorCarries_nineteen](../../ErdosProblems/Three/T2.lean#L918)
- Lean declaration: [successorCarries_twentyfive](../../ErdosProblems/Three/T2.lean#L924)
- Lean declaration: [successorCarries_thirtyone](../../ErdosProblems/Three/T2.lean#L930)
- Lean declaration: [carry_rows](../../ErdosProblems/Three/T2.lean#L938)

- outgoing **finite_instance_of**: [Z41::explicit_thresholds_partition_each_row_into_three_branches](BROWSER_Z41_1.md#node-e103a68a78cfef0f). The exact finite rows witness all three cases of the abstract partition.

<a id="node-9876080fcea617e7"></a>
## carry_free_segments_have_exact_finite_horizon_doubling_shadows

PROVED: for every finite carry-free run [N,N+k), the integral remainder identity and the normalized coordinate y_s=rho_s/2^(s+1)+1/2 represent y_(N+k) exactly as 2^k(y_N-delta)-M, where 0<=delta<=(N+1)/2^(N+1); hits are exactly the rows with y_s<=1.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The displacement is supplied separately for each horizon k. The theorem does not construct one limiting displaced point valid for the whole infinite tail.

- Lean declaration: [shadow_of_not_carry_run](../../ErdosProblems/Three/T2.lean#L583)
- Lean declaration: [y](../../ErdosProblems/Three/T2.lean#L637)
- Lean declaration: [half_le_y](../../ErdosProblems/Three/T2.lean#L639)
- Lean declaration: [hitAt_iff_y_le_one](../../ErdosProblems/Three/T2.lean#L645)
- Lean declaration: [y_succ](../../ErdosProblems/Three/T2.lean#L670)
- Lean declaration: [y_shadow](../../ErdosProblems/Three/T2.lean#L692)
- Lean declaration: [y_shadow_interval](../../ErdosProblems/Three/T2.lean#L729)

- outgoing **generated_by**: [Z41::each_seam_branch_has_an_exact_remainder_recurrence](BROWSER_Z41_1.md#node-00ba1b523047dbd4). Iterating the two non-carry recurrences accumulates the finite digit word and the bounded defect.
- incoming **barrier_for**: [Z41::dyadic_origin_and_expanding_uncertainty_limit_the_shadow_method](BROWSER_Z41_1.md#node-7fd748b3d1a588e3). The barrier quantifies why the finite-horizon shadow does not determine a cofinal binary orbit.
- incoming **specialises**: [Z41::negative_half_membership_forces_eventual_carry_free_finite_shadowing](BROWSER_Z41_1.md#node-19ac9b471172a9bc). Once the negative branch supplies an eventual carry-free tail, the finite-horizon shadow theorem applies at every horizon.
- incoming **finite_instance_of**: [Z41::a_five_row_carry_free_segment_realises_the_shadowing_law](BROWSER_Z41_1.md#node-6d5daf75bbb82992). The segment [14,19) satisfies the carry-free hypothesis and yields the integral and normalized shadow identities.

<a id="node-3237a12481cafa24"></a>
## cofinal_successor_carries_are_sufficient_for_half_membership

PROVED CONDITIONAL: every successor carry at row s produces a half-point hit at row s+1; therefore carries at arbitrarily large rows imply that 1/2 belongs to the Mersenne achievement set. A separate decidable two-inequality test certifies a carry from consecutive computed remainders.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: CarryCofinally is defined but not proved. Four finite carry rows do not establish the cofinal antecedent or settle the 1/2 question.

Open hypotheses: ["CarryCofinally"]

- Lean declaration: [hitAt_succ_of_successorCarries](../../ErdosProblems/Three/T2.lean#L521)
- Lean declaration: [CarryCofinally](../../ErdosProblems/Three/T2.lean#L528)
- Lean declaration: [half_mem_of_carryCofinally](../../ErdosProblems/Three/T2.lean#L541)
- Lean declaration: [successorCarries_of_numeric](../../ErdosProblems/Three/T2.lean#L551)

- outgoing **generated_by**: [Z41::each_seam_branch_has_an_exact_remainder_recurrence](BROWSER_Z41_1.md#node-00ba1b523047dbd4). The carry recurrence places the successor remainder below the half-point threshold.
- incoming **generated_by**: [Z41::negative_half_membership_forces_eventual_carry_free_finite_shadowing](BROWSER_Z41_1.md#node-19ac9b471172a9bc). The eventual absence of carries is the contrapositive consequence of the cofinal-carry sufficient criterion.

<a id="node-7fd748b3d1a588e3"></a>
## dyadic_origin_and_expanding_uncertainty_limit_the_shadow_method

PROVED BARRIER: every row coordinate y_s is dyadic, since 2^(s+1)y_s=rho_s+2^s; moreover the allowed shadowing interval, after k>=N+1 doublings, has image length at least one. Thus these two direct criteria cannot by themselves provide a cofinal binary-orbit conclusion.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The barrier applies to the unshifted dyadic-origin criterion and to the stated interval-resolution argument. It does not rule out constructing a common limiting displacement or using a different invariant.

- Lean declaration: [two_pow_mul_y](../../ErdosProblems/Three/T2.lean#L746)
- Lean declaration: [shadow_interval_covers](../../ErdosProblems/Three/T2.lean#L760)

- outgoing **barrier_for**: [Z41::carry_free_segments_have_exact_finite_horizon_doubling_shadows](BROWSER_Z41_1.md#node-9876080fcea617e7). The barrier quantifies why the finite-horizon shadow does not determine a cofinal binary orbit.

<a id="node-00ba1b523047dbd4"></a>
## each_seam_branch_has_an_exact_remainder_recurrence

PROVED: under its explicit trigger, the middle branch satisfies rho_(s+1)+p_s=4rho_s+2^(s+1), the right branch satisfies rho_(s+1)+2^(s+1)+p_s+4=4rho_s, and the carry branch satisfies both its unused-gap form and rho_(s+1)+3*2^(s+1)+4g_s+q_s=4rho_s.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Each identity retains its branch hypothesis. The unified perturbed-doubling statement is already authored separately in Z24 and is not duplicated here.

- Lean declaration: [middleBranch_remainder_succ_eq](../../ErdosProblems/Three/T2.lean#L260)
- Lean declaration: [upperBranch_remainder_succ_eq](../../ErdosProblems/Three/T2.lean#L288)
- Lean declaration: [upperBranch_remainder_succ_eq'](../../ErdosProblems/Three/T2.lean#L307)
- Lean declaration: [rightBranch_remainder_succ_eq_of_triggers](../../ErdosProblems/Three/T2.lean#L386)

- outgoing **generated_by**: [Z41::explicit_thresholds_partition_each_row_into_three_branches](BROWSER_Z41_1.md#node-e103a68a78cfef0f). The partition supplies the mutually exclusive hypotheses under which each exact branch recurrence applies.
- incoming **specialises**: [Z41::largest_declined_rank_quantitatively_controls_the_carry_defect](BROWSER_Z41_1.md#node-55acd6c2539befa8). The estimate controls the explicit 4g_s+q_s defect occurring in the carry recurrence.
- incoming **generated_by**: [Z41::cofinal_successor_carries_are_sufficient_for_half_membership](BROWSER_Z41_1.md#node-3237a12481cafa24). The carry recurrence places the successor remainder below the half-point threshold.
- incoming **generated_by**: [Z41::carry_free_segments_have_exact_finite_horizon_doubling_shadows](BROWSER_Z41_1.md#node-9876080fcea617e7). Iterating the two non-carry recurrences accumulates the finite digit word and the bounded defect.

<a id="node-e103a68a78cfef0f"></a>
## explicit_thresholds_partition_each_row_into_three_branches

PROVED: at every row s>=5, the carry threshold is exactly 3*2^(s+1)+4g_s+q_s <= 4rho_s, the middle threshold is exactly 4rho_s < 2^(s+1)+4+p_s, and these predicates partition the row into the middle, right, and carry cases.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The classification is pointwise. It does not determine which branches occur infinitely often.

- Lean declaration: [successorCarries_iff](../../ErdosProblems/Three/T2.lean#L235)
- Lean declaration: [three_mul_two_pow_le_of_successorCarries](../../ErdosProblems/Three/T2.lean#L249)
- Lean declaration: [MiddleTrigger](../../ErdosProblems/Three/T2.lean#L321)
- Lean declaration: [middleCond_iff](../../ErdosProblems/Three/T2.lean#L325)
- Lean declaration: [upperOrMiddle_iff](../../ErdosProblems/Three/T2.lean#L343)
- Lean declaration: [branch_trichotomy](../../ErdosProblems/Three/T2.lean#L353)
- Lean declaration: [not_upperOrMiddle_iff](../../ErdosProblems/Three/T2.lean#L371)

- outgoing **generated_by**: [Z41::adjacent_gap_excess_is_an_exact_nonnegative_gap_coordinate](BROWSER_Z41_1.md#node-4e788967a8918b5c). The carry threshold eliminates the overshoot through the exact adjacent-gap excess identity.
- incoming **generated_by**: [Z41::each_seam_branch_has_an_exact_remainder_recurrence](BROWSER_Z41_1.md#node-00ba1b523047dbd4). The partition supplies the mutually exclusive hypotheses under which each exact branch recurrence applies.
- incoming **specialises**: [Z41::a_small_remainder_forces_the_exact_middle_branch](BROWSER_Z41_1.md#node-8835f1ba283353cd). The stronger small-remainder inequality simultaneously excludes the carry threshold and implies the middle threshold.
- incoming **finite_instance_of**: [Z41::all_three_branches_occur_in_kernel_checked_finite_rows](BROWSER_Z41_1.md#node-9497d01a942eeb33). The exact finite rows witness all three cases of the abstract partition.

<a id="node-293f53149358f8ce"></a>
## finite_carry_defects_disprove_uniform_small_error

VERIFIED FINITE INSTANCES AND BARRIER: the carry defects 4g_s+q_s equal 11044, 2739, 691, and 695 at rows 13, 19, 25, and 31 respectively; at row 13 the defect exceeds one quarter of 2^(s+2), so the uncorrected carry-branch doubling approximation is not uniformly accurate.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The row-13 counterexample refutes uniform small error, not eventual smallness on a restricted family of rows. The external classification of rows 19, 25, and 31 as good is not used in this node.

- Lean declaration: [carryDefect_thirteen](../../ErdosProblems/Three/T2.lean#L960)
- Lean declaration: [carryDefect_nineteen](../../ErdosProblems/Three/T2.lean#L966)
- Lean declaration: [carryDefect_twentyfive](../../ErdosProblems/Three/T2.lean#L972)
- Lean declaration: [carryDefect_thirtyone](../../ErdosProblems/Three/T2.lean#L978)
- Lean declaration: [carryDefect_thirteen_large](../../ErdosProblems/Three/T2.lean#L988)

- outgoing **barrier_for**: [Z41::largest_declined_rank_quantitatively_controls_the_carry_defect](BROWSER_Z41_1.md#node-55acd6c2539befa8). The row-13 value shows that the half-zone bound permits a macroscopic defect when the largest false rank is low.

<a id="node-708fc0ca4c4e6ebf"></a>
## finite_rank_data_explain_small_and_large_gap_excess

VERIFIED FINITE MECHANISM: row 15 has largest false rank 14 and adjacent-gap excess 4, while row 13 has largest false rank 7, adjacent-gap excess 2760, above-pulse 4, and carry defect 11044; conversely the half-zone defect bound forces any largest false rank at row 13 to equal 7.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The contrast between rows 13 and 15 identifies a finite mechanism; it does not establish how largest false ranks behave asymptotically or on all carry rows.

- Lean declaration: [adjGapExcess_late_bound_fifteen](../../ErdosProblems/Three/T2.lean#L995)
- Lean declaration: [carryDefect_bound_fifteen](../../ErdosProblems/Three/T2.lean#L1003)
- Lean declaration: [isLargestFalseRank_thirteen_seven](../../ErdosProblems/Three/T2.lean#L1019)
- Lean declaration: [isLargestFalseRank_fifteen_fourteen](../../ErdosProblems/Three/T2.lean#L1033)
- Lean declaration: [adjGapExcess_fifteen](../../ErdosProblems/Three/T2.lean#L1041)
- Lean declaration: [adjGapExcess_thirteen](../../ErdosProblems/Three/T2.lean#L1049)
- Lean declaration: [abovePulse_thirteen](../../ErdosProblems/Three/T2.lean#L1058)
- Lean declaration: [largestFalseRank_thirteen_is_seven](../../ErdosProblems/Three/T2.lean#L1064)
- Lean declaration: [carryDefect_thirteen_forces_low_rank](../../ErdosProblems/Three/T2.lean#L1074)

- outgoing **finite_instance_of**: [Z41::largest_declined_rank_quantitatively_controls_the_carry_defect](BROWSER_Z41_1.md#node-55acd6c2539befa8). Rows 13 and 15 discharge the rank hypotheses and realize the low-rank and late-rank regimes exactly.

<a id="node-55acd6c2539befa8"></a>
## largest_declined_rank_quantitatively_controls_the_carry_defect

PROVED: if d is the largest false rank, the adjacent-gap excess has an exact formula in the late zone and an exact half-zone formula for s<2d; throughout the half zone this bounds 21(4g_s+q_s) by 128*4^(s-d)+42s+160, while the late condition 2s<3d makes the power term geometrically small.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The geometric conclusion requires the late-rank inequality. At the bottom of the half zone the bound permits a macroscopic normalized defect.

- Lean declaration: [three_mul_adjGapExcess_eq_exactLateGap](../../ErdosProblems/Three/T2.lean#L451)
- Lean declaration: [twentyOne_mul_adjGapExcess_eq_skipHalfGap](../../ErdosProblems/Three/T2.lean#L465)
- Lean declaration: [skipHalfGapCorrection_le](../../ErdosProblems/Three/T2.lean#L477)
- Lean declaration: [twentyOne_mul_carryDefect_le](../../ErdosProblems/Three/T2.lean#L496)
- Lean declaration: [four_pow_cube_le_of_late](../../ErdosProblems/Three/T2.lean#L510)

- outgoing **specialises**: [Z41::adjacent_gap_excess_is_an_exact_nonnegative_gap_coordinate](BROWSER_Z41_1.md#node-4e788967a8918b5c). The rank identities replace the abstract nonnegative excess by exact or quantitative formulas in the half and late zones.
- outgoing **specialises**: [Z41::each_seam_branch_has_an_exact_remainder_recurrence](BROWSER_Z41_1.md#node-00ba1b523047dbd4). The estimate controls the explicit 4g_s+q_s defect occurring in the carry recurrence.
- incoming **barrier_for**: [Z41::finite_carry_defects_disprove_uniform_small_error](BROWSER_Z41_1.md#node-293f53149358f8ce). The row-13 value shows that the half-zone bound permits a macroscopic defect when the largest false rank is low.
- incoming **finite_instance_of**: [Z41::finite_rank_data_explain_small_and_large_gap_excess](BROWSER_Z41_1.md#node-708fc0ca4c4e6ebf). Rows 13 and 15 discharge the rank hypotheses and realize the low-rank and late-rank regimes exactly.

<a id="node-19ac9b471172a9bc"></a>
## negative_half_membership_forces_eventual_carry_free_finite_shadowing

PROVED CONDITIONAL: if 1/2 does not belong to the Mersenne achievement set, then beyond some row no successor carry occurs, and for every later finite horizon the orbit has an exact doubling representation using some point in one fixed initial interval.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The antecedent is an open branch of Erdős #257. The point in the interval may depend on the horizon; the theorem does not produce one infinite doubling orbit.

Open hypotheses: ["(1 / 2 : ℝ) ∉ mersenneAchievementSet"]

- Lean declaration: [exists_no_carry_above_of_not_half_mem](../../ErdosProblems/Three/T2.lean#L779)
- Lean declaration: [shadow_of_not_half_mem](../../ErdosProblems/Three/T2.lean#L800)

- outgoing **generated_by**: [Z41::cofinal_successor_carries_are_sufficient_for_half_membership](BROWSER_Z41_1.md#node-3237a12481cafa24). The eventual absence of carries is the contrapositive consequence of the cofinal-carry sufficient criterion.
- outgoing **specialises**: [Z41::carry_free_segments_have_exact_finite_horizon_doubling_shadows](BROWSER_Z41_1.md#node-9876080fcea617e7). Once the negative branch supplies an eventual carry-free tail, the finite-horizon shadow theorem applies at every horizon.

