# Z40_1: Skip D3: late three-cofactor dichotomy, exact survivor certificates, and the auxiliary late-only ratchet

[All problems and zones](BROWSER.md)

<a id="node-249cfadf89a4122c"></a>
## angle_b2_cofactor_hypothesis_fails_on_all_seven_windows

For every D in {101,122,164,314,545,629,1112}, the Angle B2 hypothesis requiring all cofactor ranks to be selected throughout rows D+1,D+2,D+3 is false. Explicit skipped witnesses are 69 at row 103, 62 at 123, 83 at 165, 158 at 315, 365 at 547, 421 at 631, and 557 at 1113.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Failure of an antecedent blocks the Angle B2 connection theorem on these seven windows; it does not prove the negation of that theorem's conclusion and does not resolve #257.

- Lean declaration: [hcof_fails_101](../../ErdosProblems/Skip/D3.lean#L465)
- Lean declaration: [cofSkip_123_62](../../ErdosProblems/Skip/D3.lean#L472)
- Lean declaration: [hcof_fails_122](../../ErdosProblems/Skip/D3.lean#L477)
- Lean declaration: [cofSkip_165_83](../../ErdosProblems/Skip/D3.lean#L484)
- Lean declaration: [hcof_fails_164](../../ErdosProblems/Skip/D3.lean#L489)
- Lean declaration: [cofSkip_315_158](../../ErdosProblems/Skip/D3.lean#L496)
- Lean declaration: [hcof_fails_314](../../ErdosProblems/Skip/D3.lean#L501)
- Lean declaration: [hcof_fails_545](../../ErdosProblems/Skip/D3.lean#L510)
- Lean declaration: [hcof_fails_629](../../ErdosProblems/Skip/D3.lean#L519)
- Lean declaration: [cofSkip_1113_557](../../ErdosProblems/Skip/D3.lean#L526)
- Lean declaration: [hcof_fails_1112](../../ErdosProblems/Skip/D3.lean#L531)

- outgoing **complements**: [Z40::seven_skipped_three_cofactors_independently_force_late_rows](BROWSER_Z40_1.md#node-0358305b0e52041a). Some explicit cofactor skips both force a late row and witness failure of the stronger three-row hcof hypothesis.
- incoming **complements**: [Z40::finite_seven_class_verdict_uses_the_late_disjunct](BROWSER_Z40_1.md#node-7e4c6193721e484b). The finite verdict records both the right-disjunct successes and failure of the left-route hypothesis.

<a id="node-ae885660e31aa2b4"></a>
## cofinal_late_rows_imply_half_membership_and_force_a_global_dichotomy

A cofinal sequence of rows with LargestSkipLateAt yields skipped ranks tending to infinity and therefore 1/2 in the Mersenne achievement set. Equivalently, cofinally many late rows suffice. Unconditionally, either from some row onward both cofactor-three solutions are always selected, or 1/2 belongs to the achievement set.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This is the exact remaining fork, not a solution: the corpus proves neither eventual selection of both three-cofactors nor the cofinal late-skip branch independently. Erdős #257 remains open.

Open hypotheses: ["To use the direct endpoint implication, one still needs a cofinal supply of LargestSkipLateAt rows; the finite certificates in this module do not provide it.", "The unconditional final disjunction does not decide which branch holds."]

- Lean declaration: [seamGreedyUnboundedSkippedRanksAlong_of_lateAlong](../../ErdosProblems/Skip/D3.lean#L914)
- Lean declaration: [half_mem_of_lateAlong](../../ErdosProblems/Skip/D3.lean#L945)
- Lean declaration: [half_mem_of_lateCofinal](../../ErdosProblems/Skip/D3.lean#L953)
- Lean declaration: [eventually_threeCof_selected_or_half_mem](../../ErdosProblems/Skip/D3.lean#L964)

- outgoing **generalises**: [Z40::every_row_has_a_three_cofactor_selection_or_late_skip_dichotomy](BROWSER_Z40_1.md#node-a6bdc83a8730a097). The rowwise alternative is lifted to an eventual-selection versus cofinal-late endpoint dichotomy.
- outgoing **depends_on_open**: [Z40::finite_seven_class_verdict_uses_the_late_disjunct](BROWSER_Z40_1.md#node-7e4c6193721e484b). Twenty-one finite late rows do not supply the cofinal family required by the endpoint.
- incoming **barrier_for**: [Z40::periodicity_lifts_one_escape_to_an_infinite_progression](BROWSER_Z40_1.md#node-6eaedbdad9a62e84). The periodic escape concerns only an auxiliary recurrence, not concrete late skips; confusing the two would falsely close the open endpoint.

<a id="node-a6bdc83a8730a097"></a>
## every_row_has_a_three_cofactor_selection_or_late_skip_dichotomy

For every s>=5, either both ranks solving 3m=2s+1 or 3m=2s+2 are selected by the concrete seam greedy word, or the row has a late largest false rank.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The left branch selects only the late cofactor-three ranks, not all AngleB2.cofRanks. The theorem does not determine which branch occurs cofinally.

- Lean declaration: [threeCof_skipDichotomy](../../ErdosProblems/Skip/D3.lean#L590)

- outgoing **specialises**: [Z40::late_skips_reduce_exactly_to_three_cofactors](BROWSER_Z40_1.md#node-bb9ac17c0cca76e1). It applies the general late-zone dichotomy only to the two arithmetically possible cofactor-three ranks.
- incoming **depends_on_open**: [Z40::selected_late_cofactors_supply_only_a_smaller_sound_floor](BROWSER_Z40_1.md#node-c1bf99d5bd21d8af). The floor is available on the selection branch, but the global dichotomy does not establish that branch at all required rows.
- incoming **generalises**: [Z40::cofinal_late_rows_imply_half_membership_and_force_a_global_dichotomy](BROWSER_Z40_1.md#node-ae885660e31aa2b4). The rowwise alternative is lifted to an eventual-selection versus cofinal-late endpoint dichotomy.

<a id="node-7e4c6193721e484b"></a>
## finite_seven_class_verdict_uses_the_late_disjunct

On each of the twenty-one rows in the seven three-row windows, cofRanks selection or LargestSkipLateAt holds through the right, late-skip disjunct; and the bundled theorem records that the full three-row hcof hypothesis fails for every one of the seven D values.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem is restricted to seven named classes and twenty-one rows. It is not a global dichotomy for AngleB2.cofRanks.

- Lean declaration: [skipDichotomy_survivors](../../ErdosProblems/Skip/D3.lean#L547)
- Lean declaration: [hcof_fails_survivors](../../ErdosProblems/Skip/D3.lean#L579)

- outgoing **implies**: [Z40::twenty_one_rows_have_exact_late_largest_skip_certificates](BROWSER_Z40_1.md#node-ad323ad455b1857f). The bundled finite disjunction is discharged by the twenty-one exact right-disjunct certificates.
- outgoing **complements**: [Z40::angle_b2_cofactor_hypothesis_fails_on_all_seven_windows](BROWSER_Z40_1.md#node-249cfadf89a4122c). The finite verdict records both the right-disjunct successes and failure of the left-route hypothesis.
- incoming **depends_on_open**: [Z40::cofinal_late_rows_imply_half_membership_and_force_a_global_dichotomy](BROWSER_Z40_1.md#node-ae885660e31aa2b4). Twenty-one finite late rows do not supply the cofinal family required by the endpoint.

<a id="node-6f39e485d1982924"></a>
## late_only_ratchet_has_absorbing_zero_and_persistent_threshold

The auxiliary lateRun starts at 3 and evolves by lateStep using lateTotalFloor. Zero is absorbing. Because lateTotalFloor<=11, a value at least 12 remains at least 12 forever; in particular, reaching 12 by depth four guarantees nonzero value at every depth.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Persistence of lateRun is not persistence of the concrete belowPulse orbit unless the separate selected-late-cofactor hypothesis connects the floor to the row.

- Lean declaration: [lateStep](../../ErdosProblems/Skip/D3.lean#L762)
- Lean declaration: [lateRun](../../ErdosProblems/Skip/D3.lean#L765)
- Lean declaration: [lateRun_succ](../../ErdosProblems/Skip/D3.lean#L769)
- Lean declaration: [twelve_le_lateStep](../../ErdosProblems/Skip/D3.lean#L781)
- Lean declaration: [lateStep_zero](../../ErdosProblems/Skip/D3.lean#L787)
- Lean declaration: [lateRun_eq_zero_of_le](../../ErdosProblems/Skip/D3.lean#L792)
- Lean declaration: [twelve_le_lateRun_of_le](../../ErdosProblems/Skip/D3.lean#L800)
- Lean declaration: [lateRun_ne_zero_of_twelve_le_four](../../ErdosProblems/Skip/D3.lean#L812)

- outgoing **transport_of**: [Z40::selected_late_cofactors_supply_only_a_smaller_sound_floor](BROWSER_Z40_1.md#node-c1bf99d5bd21d8af). lateRun is the recurrence induced by the smaller late-only floor and inherits its ceiling eleven.
- incoming **finite_instance_of**: [Z40::named_auxiliary_phases_split_into_early_zeroes_and_permanent_escapes](BROWSER_Z40_1.md#node-a589891346ee7fed). The exact phase computations are propagated by the zero and threshold lemmas.
- incoming **generalises**: [Z40::periodicity_lifts_one_escape_to_an_infinite_progression](BROWSER_Z40_1.md#node-6eaedbdad9a62e84). Periodicity transports the phase-20 persistence certificate to infinitely many starting phases.

<a id="node-bbfa96bf007d20bc"></a>
## late_only_ratchet_has_exactly_eighty_seven_depth_twelve_survivor_phases

Among the 2730 residue phases D in [0,2730), exactly 87 satisfy lateRun D 12 != 0.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The count is only at depth 12 and does not claim that all 87 phases persist forever; named persistence results are separate. It is not a census of concrete #257 survivors.

- Lean declaration: [lateRatchet_survivor_count](../../ErdosProblems/Skip/D3.lean#L894)

- outgoing **complements**: [Z40::periodicity_lifts_one_escape_to_an_infinite_progression](BROWSER_Z40_1.md#node-6eaedbdad9a62e84). The finite census measures one full period at depth twelve, while the progression theorem proves all-depth persistence for one periodic family.

<a id="node-bb9ac17c0cca76e1"></a>
## late_skips_reduce_exactly_to_three_cofactors

A skipped rank m with 2<=m<s and 2s<3m forces the row's largest false rank to be late. At every s>=4 either all late ranks are selected or such a late largest skip exists. For divisors of 2s+1 or 2s+2 below s, the only ranks capable of lying in that zone are the two cofactor-three solutions; the half-row cofactor is never late.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The dichotomy does not prove that late skips occur cofinally. Enlarging the divisor list beyond cofactor three cannot strengthen this particular late-zone argument.

- Lean declaration: [largestSkipLateAt_of_late_skip](../../ErdosProblems/Skip/D3.lean#L50)
- Lean declaration: [lateZone_dichotomy](../../ErdosProblems/Skip/D3.lean#L77)
- Lean declaration: [threeCofOdd_late](../../ErdosProblems/Skip/D3.lean#L95)
- Lean declaration: [threeCofEven_late](../../ErdosProblems/Skip/D3.lean#L100)
- Lean declaration: [halfCof_not_late](../../ErdosProblems/Skip/D3.lean#L109)
- Lean declaration: [largestSkipLateAt_of_threeCofOdd_skip](../../ErdosProblems/Skip/D3.lean#L113)
- Lean declaration: [largestSkipLateAt_of_threeCofEven_skip](../../ErdosProblems/Skip/D3.lean#L122)
- Lean declaration: [late_divisor_cofactor_three](../../ErdosProblems/Skip/D3.lean#L135)

- incoming **complements**: [Z40::structural_recursion_makes_greedy_rows_kernel_checkable](BROWSER_Z40_1.md#node-fb7883b36caf317f). The arithmetic classification identifies meaningful late ranks, while the executable layer certifies concrete support failures and maximal false ranks.
- incoming **finite_instance_of**: [Z40::seven_skipped_three_cofactors_independently_force_late_rows](BROWSER_Z40_1.md#node-0358305b0e52041a). Each skipped odd three-cofactor instantiates the universal promotion from a late skip to a late largest skip.
- incoming **specialises**: [Z40::every_row_has_a_three_cofactor_selection_or_late_skip_dichotomy](BROWSER_Z40_1.md#node-a6bdc83a8730a097). It applies the general late-zone dichotomy only to the two arithmetically possible cofactor-three ranks.

<a id="node-a589891346ee7fed"></a>
## named_auxiliary_phases_split_into_early_zeroes_and_permanent_escapes

Kernel computation gives lateRun D 4 equal to 24,24,21,24,24 for D=20,314,545,629,1112, so all five phases are nonzero at every depth. In contrast, lateRun D 3=0 for D=101,122,164, hence those three auxiliary runs remain zero thereafter.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These values do not state the concrete belowPulse values. In particular, the selected-late-cofactor hypothesis needed to relate the auxiliary floor to concrete rows fails on the seven measured classes.

- Lean declaration: [lateRun_20_four](../../ErdosProblems/Skip/D3.lean#L825)
- Lean declaration: [lateRun_314_four](../../ErdosProblems/Skip/D3.lean#L826)
- Lean declaration: [lateRun_545_four](../../ErdosProblems/Skip/D3.lean#L827)
- Lean declaration: [lateRun_629_four](../../ErdosProblems/Skip/D3.lean#L828)
- Lean declaration: [lateRun_1112_four](../../ErdosProblems/Skip/D3.lean#L829)
- Lean declaration: [lateRun_101_three](../../ErdosProblems/Skip/D3.lean#L835)
- Lean declaration: [lateRun_122_three](../../ErdosProblems/Skip/D3.lean#L836)
- Lean declaration: [lateRun_164_three](../../ErdosProblems/Skip/D3.lean#L837)
- Lean declaration: [lateRun_twenty_ne_zero](../../ErdosProblems/Skip/D3.lean#L842)
- Lean declaration: [lateRun_314_ne_zero](../../ErdosProblems/Skip/D3.lean#L848)
- Lean declaration: [lateRun_545_ne_zero](../../ErdosProblems/Skip/D3.lean#L851)
- Lean declaration: [lateRun_629_ne_zero](../../ErdosProblems/Skip/D3.lean#L854)
- Lean declaration: [lateRun_1112_ne_zero](../../ErdosProblems/Skip/D3.lean#L857)

- outgoing **finite_instance_of**: [Z40::late_only_ratchet_has_absorbing_zero_and_persistent_threshold](BROWSER_Z40_1.md#node-6f39e485d1982924). The exact phase computations are propagated by the zero and threshold lemmas.

<a id="node-6eaedbdad9a62e84"></a>
## periodicity_lifts_one_escape_to_an_infinite_progression

lateCofFloor, lateTotalFloor, and lateRun are periodic in the starting phase with period 2730; the recurrence equality extends to every multiple of that period. Since phase 20 never reaches zero, every phase 20+2730n also survives at every depth.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The infinite progression is an escape family for lateRun only. It is not a cofinal family of concrete greedy late skips and does not prove the #257 endpoint.

- Lean declaration: [lateCofFloor_add_period](../../ErdosProblems/Skip/D3.lean#L860)
- Lean declaration: [lateTotalFloor_add_period](../../ErdosProblems/Skip/D3.lean#L864)
- Lean declaration: [lateRun_add_period](../../ErdosProblems/Skip/D3.lean#L868)
- Lean declaration: [lateRun_add_mul_period](../../ErdosProblems/Skip/D3.lean#L876)
- Lean declaration: [lateRun_progression_ne_zero](../../ErdosProblems/Skip/D3.lean#L884)

- outgoing **generalises**: [Z40::late_only_ratchet_has_absorbing_zero_and_persistent_threshold](BROWSER_Z40_1.md#node-6f39e485d1982924). Periodicity transports the phase-20 persistence certificate to infinitely many starting phases.
- incoming **complements**: [Z40::late_only_ratchet_has_exactly_eighty_seven_depth_twelve_survivor_phases](BROWSER_Z40_1.md#node-bbfa96bf007d20bc). The finite census measures one full period at depth twelve, while the progression theorem proves all-depth persistence for one periodic family.
- outgoing **barrier_for**: [Z40::cofinal_late_rows_imply_half_membership_and_force_a_global_dichotomy](BROWSER_Z40_1.md#node-ae885660e31aa2b4). The periodic escape concerns only an auxiliary recurrence, not concrete late skips; confusing the two would falsely close the open endpoint.

<a id="node-c1bf99d5bd21d8af"></a>
## selected_late_cofactors_supply_only_a_smaller_sound_floor

lateCofRanks contains precisely the applicable cofactor-three rank when s is 1 or 2 modulo 3, with certified pulse floor 2 or 1 respectively and zero otherwise. For s>=61 these ranks lie above 26 and are disjoint from the eight fixed small ranks. If every late cofactor rank is selected, lateTotalFloor=pulseFloor+lateCofFloor is bounded by the concrete belowPulse; uniformly lateCofFloor<=2 and lateTotalFloor<=11.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This is strictly the late-only floor, not AngleB2.totalFloor. On the seven measured classes the required selection hypothesis fails at the exhibited rows, so the auxiliary floor cannot simply be identified with their concrete contribution.

Open hypotheses: ["For the sound lower bound at a row, every rank in lateCofRanks s must actually be selected by the concrete seam greedy word."]

- Lean declaration: [lateCofRanks](../../ErdosProblems/Skip/D3.lean#L624)
- Lean declaration: [lateCofFloor](../../ErdosProblems/Skip/D3.lean#L630)
- Lean declaration: [lateCofRanks_subset_cofRanks](../../ErdosProblems/Skip/D3.lean#L633)
- Lean declaration: [lateCofRanks_cases](../../ErdosProblems/Skip/D3.lean#L656)
- Lean declaration: [lateCofRanks_ge](../../ErdosProblems/Skip/D3.lean#L662)
- Lean declaration: [lateCofRanks_disjoint](../../ErdosProblems/Skip/D3.lean#L665)
- Lean declaration: [lateCofFloor_le_lateCofPulse](../../ErdosProblems/Skip/D3.lean#L673)
- Lean declaration: [lateTotalFloor](../../ErdosProblems/Skip/D3.lean#L707)
- Lean declaration: [lateTotalFloor_le_belowPulse](../../ErdosProblems/Skip/D3.lean#L711)
- Lean declaration: [lateCofFloor_le_two](../../ErdosProblems/Skip/D3.lean#L771)
- Lean declaration: [lateTotalFloor_le_eleven](../../ErdosProblems/Skip/D3.lean#L774)

- outgoing **depends_on_open**: [Z40::every_row_has_a_three_cofactor_selection_or_late_skip_dichotomy](BROWSER_Z40_1.md#node-a6bdc83a8730a097). The floor is available on the selection branch, but the global dichotomy does not establish that branch at all required rows.
- incoming **transport_of**: [Z40::late_only_ratchet_has_absorbing_zero_and_persistent_threshold](BROWSER_Z40_1.md#node-6f39e485d1982924). lateRun is the recurrence induced by the smaller late-only floor and inherits its ceiling eleven.

<a id="node-0358305b0e52041a"></a>
## seven_skipped_three_cofactors_independently_force_late_rows

At rows 103,124,166,316,547,631,1114 the respective odd three-cofactors 69,83,111,211,365,421,743 are absent from the greedy support. Each skip independently forces LargestSkipLateAt at that row, without relying on the maximal-rank rowChk computation.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These seven isolated rows do not establish eventual or cofinal failure of three-cofactor selection.

- Lean declaration: [cofSkip_103_69](../../ErdosProblems/Skip/D3.lean#L386)
- Lean declaration: [lateAt_103_via_cofactor](../../ErdosProblems/Skip/D3.lean#L391)
- Lean declaration: [cofSkip_124_83](../../ErdosProblems/Skip/D3.lean#L397)
- Lean declaration: [lateAt_124_via_cofactor](../../ErdosProblems/Skip/D3.lean#L402)
- Lean declaration: [cofSkip_166_111](../../ErdosProblems/Skip/D3.lean#L408)
- Lean declaration: [lateAt_166_via_cofactor](../../ErdosProblems/Skip/D3.lean#L413)
- Lean declaration: [cofSkip_316_211](../../ErdosProblems/Skip/D3.lean#L419)
- Lean declaration: [lateAt_316_via_cofactor](../../ErdosProblems/Skip/D3.lean#L424)
- Lean declaration: [cofSkip_547_365](../../ErdosProblems/Skip/D3.lean#L430)
- Lean declaration: [lateAt_547_via_cofactor](../../ErdosProblems/Skip/D3.lean#L435)
- Lean declaration: [cofSkip_631_421](../../ErdosProblems/Skip/D3.lean#L441)
- Lean declaration: [lateAt_631_via_cofactor](../../ErdosProblems/Skip/D3.lean#L446)
- Lean declaration: [cofSkip_1114_743](../../ErdosProblems/Skip/D3.lean#L452)
- Lean declaration: [lateAt_1114_via_cofactor](../../ErdosProblems/Skip/D3.lean#L457)

- outgoing **finite_instance_of**: [Z40::late_skips_reduce_exactly_to_three_cofactors](BROWSER_Z40_1.md#node-bb9ac17c0cca76e1). Each skipped odd three-cofactor instantiates the universal promotion from a late skip to a late largest skip.
- outgoing **complements**: [Z40::twenty_one_rows_have_exact_late_largest_skip_certificates](BROWSER_Z40_1.md#node-ad323ad455b1857f). Seven rows receive an independent structural proof in addition to the maximal-rank computation.
- incoming **complements**: [Z40::angle_b2_cofactor_hypothesis_fails_on_all_seven_windows](BROWSER_Z40_1.md#node-249cfadf89a4122c). Some explicit cofactor skips both force a late row and witness failure of the stronger three-row hcof hypothesis.

<a id="node-fb7883b36caf317f"></a>
## structural_recursion_makes_greedy_rows_kernel_checkable

The structurally recursive weight list wgt equals the well-founded seam-weight recursion with sufficient fuel. Consequently the Boolean word gb is the concrete seam greedy word, has length s-2, and its bit lookup exactly decides support membership. The Boolean rowChk certifies that d is the largest false rank and, with 2s<3d, certifies LargestSkipLateAt s.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: rowChk proves only the explicitly evaluated rows. Its executability is not a uniform theorem that late skips exist.

- Lean declaration: [wgt](../../ErdosProblems/Skip/D3.lean#L158)
- Lean declaration: [wgt_eq](../../ErdosProblems/Skip/D3.lean#L162)
- Lean declaration: [seamWeights_eq_wgt](../../ErdosProblems/Skip/D3.lean#L174)
- Lean declaration: [gb](../../ErdosProblems/Skip/D3.lean#L179)
- Lean declaration: [gb_eq](../../ErdosProblems/Skip/D3.lean#L181)
- Lean declaration: [gb_length](../../ErdosProblems/Skip/D3.lean#L184)
- Lean declaration: [seamGreedyWord_apply](../../ErdosProblems/Skip/D3.lean#L187)
- Lean declaration: [mem_support_iff](../../ErdosProblems/Skip/D3.lean#L194)
- Lean declaration: [notMem_support_of_gb_false](../../ErdosProblems/Skip/D3.lean#L206)
- Lean declaration: [rowChk](../../ErdosProblems/Skip/D3.lean#L215)
- Lean declaration: [isLargestFalseRank_of_rowChk](../../ErdosProblems/Skip/D3.lean#L219)
- Lean declaration: [largestSkipLateAt_of_rowChk](../../ErdosProblems/Skip/D3.lean#L231)

- outgoing **complements**: [Z40::late_skips_reduce_exactly_to_three_cofactors](BROWSER_Z40_1.md#node-bb9ac17c0cca76e1). The arithmetic classification identifies meaningful late ranks, while the executable layer certifies concrete support failures and maximal false ranks.
- incoming **finite_instance_of**: [Z40::twenty_one_rows_have_exact_late_largest_skip_certificates](BROWSER_Z40_1.md#node-ad323ad455b1857f). All twenty-one statements are kernel-evaluated instances of rowChk soundness.

<a id="node-ad323ad455b1857f"></a>
## twenty_one_rows_have_exact_late_largest_skip_certificates

For each D in {101,122,164,314,545,629,1112}, all three rows s=D+1,D+2,D+3 have a kernel-checked late largest false rank. The certified ranks are 101,101,101; 121,123,124; 162,165,166; 314,315,316; 545,546,546; 628,630,630; and 1111,1113,1114 respectively.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The seven values were chosen by an external scan, but the Lean authority here is only the twenty-one displayed row certificates. A finite table supplies no cofinal late-row sequence.

- Lean declaration: [lateAt_102](../../ErdosProblems/Skip/D3.lean#L253)
- Lean declaration: [lateAt_103](../../ErdosProblems/Skip/D3.lean#L258)
- Lean declaration: [lateAt_104](../../ErdosProblems/Skip/D3.lean#L263)
- Lean declaration: [lateAt_123](../../ErdosProblems/Skip/D3.lean#L270)
- Lean declaration: [lateAt_124](../../ErdosProblems/Skip/D3.lean#L275)
- Lean declaration: [lateAt_125](../../ErdosProblems/Skip/D3.lean#L280)
- Lean declaration: [lateAt_165](../../ErdosProblems/Skip/D3.lean#L287)
- Lean declaration: [lateAt_166](../../ErdosProblems/Skip/D3.lean#L292)
- Lean declaration: [lateAt_167](../../ErdosProblems/Skip/D3.lean#L297)
- Lean declaration: [lateAt_315](../../ErdosProblems/Skip/D3.lean#L304)
- Lean declaration: [lateAt_316](../../ErdosProblems/Skip/D3.lean#L309)
- Lean declaration: [lateAt_317](../../ErdosProblems/Skip/D3.lean#L314)
- Lean declaration: [lateAt_546](../../ErdosProblems/Skip/D3.lean#L321)
- Lean declaration: [lateAt_547](../../ErdosProblems/Skip/D3.lean#L326)
- Lean declaration: [lateAt_548](../../ErdosProblems/Skip/D3.lean#L331)
- Lean declaration: [lateAt_630](../../ErdosProblems/Skip/D3.lean#L338)
- Lean declaration: [lateAt_631](../../ErdosProblems/Skip/D3.lean#L343)
- Lean declaration: [lateAt_632](../../ErdosProblems/Skip/D3.lean#L348)
- Lean declaration: [lateAt_1113](../../ErdosProblems/Skip/D3.lean#L355)
- Lean declaration: [lateAt_1114](../../ErdosProblems/Skip/D3.lean#L360)
- Lean declaration: [lateAt_1115](../../ErdosProblems/Skip/D3.lean#L365)

- outgoing **finite_instance_of**: [Z40::structural_recursion_makes_greedy_rows_kernel_checkable](BROWSER_Z40_1.md#node-fb7883b36caf317f). All twenty-one statements are kernel-evaluated instances of rowChk soundness.
- incoming **complements**: [Z40::seven_skipped_three_cofactors_independently_force_late_rows](BROWSER_Z40_1.md#node-0358305b0e52041a). Seven rows receive an independent structural proof in addition to the maximal-rank computation.
- incoming **implies**: [Z40::finite_seven_class_verdict_uses_the_late_disjunct](BROWSER_Z40_1.md#node-7e4c6193721e484b). The bundled finite disjunction is discharged by the twenty-one exact right-disjunct certificates.

