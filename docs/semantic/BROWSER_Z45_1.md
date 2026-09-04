# Z45_1: Period-multiple escape: block identities, exact ray supply, and full-depth sufficient condition

[All problems and zones](BROWSER.md)

<a id="node-f0d596c2a7204f40"></a>
## eventual_integrality_at_one_period_telescopes_to_every_multiple

PROVED TELESCOPING LAW: if the h0-step tail difference is integral for every N >= N0, then for every multiplier t and every N >= N0 the difference totientTail (N+t*h0) - totientTail N is integral.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem is conditional on eventual integrality at the primitive step. It transports that hypothesis; it neither proves nor refutes it for the totient series.

- Lean declaration: [tail_diff_mul_mem_int_of_forall_step](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L381)

- outgoing **complements**: [Z45::full_depth_discrepancies_and_totient_blocks_have_exact_nesting_identities](BROWSER_Z45_1.md#node-cddb18897f186820). The block identities expose the depth-period coordinates, while telescoping transports the rationality-side integrality hypothesis along a period ray.
- incoming **generated_by**: [Z45::period_multiple_kill_supply_is_exactly_erdos_249](BROWSER_Z45_1.md#node-ba866704f7376c93). The supply-to-irrationality direction contradicts the supplied kill using integrality transported from the primitive period to its selected multiple.

<a id="node-cddb18897f186820"></a>
## full_depth_discrepancies_and_totient_blocks_have_exact_nesting_identities

PROVED EXACT IDENTITIES: windowDiscrepancy h N h is totientBlock h (N+h) - totientBlock h N; totientBlock (a+b) N is 2^b times totientBlock a N plus totientBlock b (N+a); hence a block of length 2h splits into its two adjacent h-blocks with the stated dyadic weight.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These identities reorganise discrepancy words and explain the nesting of the depth-period channels. They do not supply a central residue or any certified kill.

- Lean declaration: [windowDiscrepancy_self_eq_totientBlock_sub](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L67)
- Lean declaration: [totientBlock_add](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L77)
- Lean declaration: [totientBlock_two_mul](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L373)

- incoming **complements**: [Z45::eventual_integrality_at_one_period_telescopes_to_every_multiple](BROWSER_Z45_1.md#node-f0d596c2a7204f40). The block identities expose the depth-period coordinates, while telescoping transports the rationality-side integrality hypothesis along a period ray.

<a id="node-1d9a36651d95ed54"></a>
## full_depth_escape_is_a_stronger_open_sufficient_producer

OPEN SUFFICIENT PRODUCER: ApFullDepthEscape requires, for every d>0 and every N, some t>0 with certifiedKill (t*d) N (t*d). It implies PeriodMultipleKillSupply and hence irrationality of the totient series.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The implication is proved but the antecedent is not. Unlike PeriodMultipleKillSupply, ApFullDepthEscape is not proved necessary for irrationality.

Open hypotheses: ["ApFullDepthEscape: for every positive ray d and every basepoint N, a positive multiple t*d fires a certified kill at the locked depth L=t*d."]

- Lean declaration: [ApFullDepthEscape](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L441)
- Lean declaration: [periodMultipleKillSupply_of_apFullDepthEscape](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L444)
- Lean declaration: [irrational_totient_series_of_apFullDepthEscape](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L450)

- outgoing **implies**: [Z45::period_multiple_kill_supply_is_exactly_erdos_249](BROWSER_Z45_1.md#node-ba866704f7376c93). A full-depth escape witness at basepoint c is directly a PeriodMultipleKillSupply witness with N=c and L=t*d.

<a id="node-ba866704f7376c93"></a>
## period_multiple_kill_supply_is_exactly_erdos_249

EXACT OPEN REFORMULATION: PeriodMultipleKillSupply requires that for every d>0 and threshold c there are t>0, N>=c, and L with certifiedKill (t*d) N L. This supply implies irrationality of the totient series, irrationality supplies it already with t=1 and N=c, and therefore the supply is equivalent to Erdős #249.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Both sides of the equivalence remain open. The ray supply is not an independent proved producer and the change from arbitrary periods to one multiple on each ray does not move the truth value.

- Lean declaration: [PeriodMultipleKillSupply](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L403)
- Lean declaration: [irrational_totient_series_of_periodMultipleKillSupply](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L411)
- Lean declaration: [periodMultipleKillSupply_of_irrational](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L422)
- Lean declaration: [periodMultipleKillSupply_iff_irrational](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L432)

- outgoing **generated_by**: [Z45::eventual_integrality_at_one_period_telescopes_to_every_multiple](BROWSER_Z45_1.md#node-f0d596c2a7204f40). The supply-to-irrationality direction contradicts the supplied kill using integrality transported from the primitive period to its selected multiple.
- incoming **implies**: [Z45::full_depth_escape_is_a_stronger_open_sufficient_producer](BROWSER_Z45_1.md#node-1d9a36651d95ed54). A full-depth escape witness at basepoint c is directly a PeriodMultipleKillSupply witness with N=c and L=t*d.

