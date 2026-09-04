# Z18_1: Demand ledger and the implication order over the recorded open antecedents

[All problems and zones](BROWSER.md)

<a id="node-96865f94ceae7b82"></a>
## demand_lattice_249_certificate_chain

The three totient block certificate supplies of #249 -- the block certificate, the carry-aware certificate and the low-carry certificate -- form a strict chain, block implies carry-aware implies low-carry, and each implies #249. No edge was found in the reverse direction, so on the proved edges these three are at least as strong as the problem and none is a weaker stepping stone toward it.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [e_G088_G089](../../ErdosProblems/DemandLedger/edges/ClusterF.lean#L132)
- Lean declaration: [e_G089_G090](../../ErdosProblems/DemandLedger/edges/ClusterF.lean#L151)
- Lean declaration: [e_G090_G100](../../ErdosProblems/DemandLedger/edges/Bridge3.lean#L295)


<a id="node-bf4342b4342b0d1a"></a>
## demand_lattice_249_problem_class

Fourteen of the substantial open antecedents of #249 -- the pointwise, ray, multiple, diagonal, cone, jump, window, survivor, rank-two, cone-nonflat, prime-jump and nonintegrality supplies -- are mutually implied, and the class is equivalent to Erdos #249 itself. The reverse direction rests on the corpus completeness theorem irrational_totient_series_iff_pointwise_certificates: the series is irrational exactly when a certified kill exists at every positive shift and every position. These are therefore not antecedents of the problem in any useful sense; they are the problem restated.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [G103_iff_erdos249](../../ErdosProblems/DemandLedger/edges/Discharge3_G103.lean#L58)
- Lean declaration: [G103_iff_G097](../../ErdosProblems/DemandLedger/edges/Discharge3_G103.lean#L65)
- Lean declaration: [e_G096_G100](../../ErdosProblems/DemandLedger/edges/ClusterA.lean#L279)
- Lean declaration: [e_G100_G096](../../ErdosProblems/DemandLedger/edges/ClusterA.lean#L288)


<a id="node-249026f779663e0c"></a>
## demand_lattice_257_chain

For #257 the substantial antecedents form a three-level strict chain so far as the proved edges go: block dyadic safety at the displayed half-orbit state is equivalent to the real dyadic cap, both imply the two-channel cap, and that implies the class of the tempered Moebius-centred carry, the carry upper bound and the unbounded terminal-false seam condition. That bottom class is equivalent to 1/2 in mersenneAchievementSet by half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse, so it is the 1/2-membership question itself.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [e_G083_G084](../../ErdosProblems/DemandLedger/edges/ClusterE.lean#L230)
- Lean declaration: [e_G084_G083](../../ErdosProblems/DemandLedger/edges/ClusterE.lean#L252)
- Lean declaration: [e_G084_G085](../../ErdosProblems/DemandLedger/edges/ClusterE.lean#L276)
- Lean declaration: [e_G085_G073](../../ErdosProblems/DemandLedger/edges/ClusterE.lean#L289)


<a id="node-d90a41353567c27c"></a>
## demand_ledger_extraction

Every open antecedent recorded in docs/semantic/frontier.json is already a Lean Prop, namely the type of a named hypothesis binder on a conditional_implication declaration. The hypOf% elaborator lifts such a binder into a named constant taken from the kernel's ConstantInfo, so the resulting Prop is the hypothesis or elaboration fails. Applying it to the 259 conditional-implication declarations yields 101 distinct closed Props, of which 23 are substantial statements and the remainder are side conditions; the frontier records 52 antecedents in prose.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: candidate_new_statement.

- Lean declaration: [G103](../../ErdosProblems/DemandLedger/Basic.lean#L107)
- Lean declaration: [G100](../../ErdosProblems/DemandLedger/Basic.lean#L57)
- Lean declaration: [G096](../../ErdosProblems/DemandLedger/Basic.lean#L47)
- Lean declaration: [G090](../../ErdosProblems/DemandLedger/Basic.lean#L67)


<a id="node-5a69928bfe82f19b"></a>
## lcm_jump_kill_from_diagonal

periodLcm t = lcm(1..t) grows by the factor q exactly when t+1 is a prime power q, so the lcm-jump length is (q-1)*periodLcm t; at q = 2, that is t = 2^k - 1, the factor is one and the jump shift equals the diagonal shift. Kills at an lcm-jump shift are therefore exhibited at t = 1, 3, 7 and 31, read off existing diagonal deposits with no new totient arithmetic. The jump route is not an independent obstacle: any cofinal diagonal supply along t = 2^k - 1 discharges it.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [certifiedKill_lcm_jump_at_thirtyone](../../ErdosProblems/Erdos249/LcmJumpKillFromDiagonal.lean#L109)
- Lean declaration: [certifiedKill_lcm_jump_at_seven](../../ErdosProblems/Erdos249/LcmJumpKillFromDiagonal.lean#L68)
- Lean declaration: [periodLcm_jump_eq_height_at_thirtyone](../../ErdosProblems/Erdos249/LcmJumpKillFromDiagonal.lean#L62)


