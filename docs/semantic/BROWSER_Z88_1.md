# Z88_1: Erdős 257 C5 seam remainders: greedy calculus, tail domination, sharp word-only limits, and skip certificates

[All problems and zones](BROWSER.md)

<a id="node-736482d0eae471d6"></a>
## a_certified_skipped_rank_restarts_the_counting_bound_on_its_suffix

LOCALIZED SKIP TRANSPORT: dropping k entries from seamWeightsFrom s a gives seamWeightsFrom s (a+k), and the final seam remainder is the greedy remainder of the suffix from rank a started at the residual entering a. If rank a is skipped, then the final remainder plus the tail after a is at most w_a. If three times that head slack is below 7*2^s+4, the row satisfies Bit/R2.ObeysRemainderCeiling.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: SkipsRank and the slack inequality are explicit local hypotheses, not globally proved invariants. The theorem gives no cofinal supply of such ranks and does not say every row obeys the ceiling.

- Lean declaration: [seamWeightsFrom_drop](../../ErdosProblems/Rem/C5.lean#L461)
- Lean declaration: [seam_remainder_split](../../ErdosProblems/Rem/C5.lean#L485)
- Lean declaration: [remainder_add_tail_le_of_skipsRank](../../ErdosProblems/Rem/C5.lean#L498)
- Lean declaration: [obeysCeiling_of_skipsRank](../../ErdosProblems/Rem/C5.lean#L516)

- outgoing **generated_by**: [Z88::integer_greedy_remainder_has_exact_list_recursion_and_append_composition](BROWSER_Z88_1.md#node-fc3d02f362620c0b). The append composition law identifies the entering remainder and the suffix computation at the selected rank.
- outgoing **generated_by**: [Z88::tail_domination_bounds_every_admissible_greedy_remainder_by_the_slack](BROWSER_Z88_1.md#node-0975cf2f0890732b). After splitting at a skipped rank, the same abstract TailDominated theorem bounds the remaining suffix by its local head slack.
- incoming **specialises**: [Z88::skipping_the_last_rank_automatically_forces_the_remainder_ceiling](BROWSER_Z88_1.md#node-f468d3eb2db79d13). At rank s-1 the later suffix is empty and the exact last weight makes the generic slack comparison automatic.
- incoming **complements**: [Z88::consecutive_seam_weights_never_satisfy_the_proposed_small_gap_premise](BROWSER_Z88_1.md#node-cd3a619a89d690b2). The consecutive-gap route is empty, while the skipped-rank route is a distinct live sufficient condition with explicit finite witnesses.
- incoming **finite_instance_of**: [Z88::rows_eight_eleven_and_twelve_exhibit_live_skip_and_ceiling_certificates](BROWSER_Z88_1.md#node-8ff7e78e42b91010). Rows 11 and 12 instantiate the generic rank-7 skip theorem, and row 8 instantiates its last-rank specialization.

<a id="node-d94be37b64a21d99"></a>
## an_admissible_head_minus_one_capacity_blocks_any_two_power_word_only_bound

SHARP WORD-ONLY BARRIER: at capacity w_2-1 the greedy skips the head, takes the entire later tail, and leaves exactly w_2-1-sum(tail from rank 3). This remainder satisfies 4^s<=21*remainder+35. Consequently, for every s>=6 there exists C<seamSubsetTarget s whose greedy remainder on the same seamWeights s is strictly greater than 2^s.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The witness capacity is not the actual seamSubsetTarget. The result refutes only deductions that use the seam weight word together with generic capacity admissibility; it does not prove the actual seam remainder exceeds 2^s and does not rule out target-specific arithmetic arguments.

- Lean declaration: [greedyRemainder_at_head_sub_one](../../ErdosProblems/Rem/C5.lean#L402)
- Lean declaration: [counting_bound_sharp](../../ErdosProblems/Rem/C5.lean#L419)
- Lean declaration: [exists_admissible_capacity_remainder_gt_two_pow](../../ErdosProblems/Rem/C5.lean#L442)

- outgoing **generated_by**: [Z88::head_and_tail_estimates_put_the_word_only_sharpness_witness_at_four_power_scale](BROWSER_Z88_1.md#node-6fafa78424274507). The head and suffix inequalities quantify the exact head-minus-one remainder and place it at order 4^s.
- outgoing **barrier_for**: [Z88::seam_counting_gives_an_unconditional_four_power_over_eight_remainder_bound](BROWSER_Z88_1.md#node-bf11027b971a25e4). The admissible counterexample proves that the word-only upper bound cannot be strengthened uniformly from order 4^s to the desired 2^s scale without target-specific information.
- incoming **finite_instance_of**: [Z88::row_eight_computes_the_head_minus_one_sharpness_remainder_exactly](BROWSER_Z88_1.md#node-c900fdf37ad22c12). The exact value 4443 is the row-8 instance of the same head-minus-one capacity used in the general sharpness barrier.

<a id="node-cd3a619a89d690b2"></a>
## consecutive_seam_weights_never_satisfy_the_proposed_small_gap_premise

EMPTY-PREMISE BARRIER: whenever s>=2, d>=1, and d+1<s, the adjacent seam weights satisfy 2^(s+1)+w_(d+1)<=w_d. Their gap is therefore at least 2^(s+1), so no consecutive pair differs by less than 2^s.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: This rules out one proposed sufficient condition only. It does not rule out localized skip certificates, other relations among several weights, or arithmetic information tied to the actual target.

- Lean declaration: [consecutive_gap_ge](../../ErdosProblems/Rem/C5.lean#L575)

- outgoing **complements**: [Z88::a_certified_skipped_rank_restarts_the_counting_bound_on_its_suffix](BROWSER_Z88_1.md#node-736482d0eae471d6). The consecutive-gap route is empty, while the skipped-rank route is a distinct live sufficient condition with explicit finite witnesses.

<a id="node-0b5dd454091b960a"></a>
## dyadic_scale_and_seam_head_comparisons_control_the_global_counting_input

EXACT SCALE COMPARISONS: 4^s=2^(2s); 4^s<=3*w_2+2 for the first seam weight; the actual seamSubsetTarget s is at most 2*w_2 for s>=1; and for every d>=1, 4^s<(2^d-1)*w_d+(2^d-1).

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These comparisons only supply scale and admissibility inequalities. They do not analyze the greedy decisions or establish an asymptotically smaller remainder.

- Lean declaration: [four_pow_eq_two_pow](../../ErdosProblems/Rem/C5.lean#L236)
- Lean declaration: [four_pow_le_three_mul_head](../../ErdosProblems/Rem/C5.lean#L239)
- Lean declaration: [target_le_two_mul_head](../../ErdosProblems/Rem/C5.lean#L247)
- Lean declaration: [four_pow_lt_weight_mul](../../ErdosProblems/Rem/C5.lean#L285)

- incoming **generated_by**: [Z88::seam_counting_gives_an_unconditional_four_power_over_eight_remainder_bound](BROWSER_Z88_1.md#node-bf11027b971a25e4). The scale comparisons verify actual-target admissibility and convert the head-slack estimate to 8*remainder<=4^s.

<a id="node-6fafa78424274507"></a>
## head_and_tail_estimates_put_the_word_only_sharpness_witness_at_four_power_scale

SHARPNESS ESTIMATES: for d>=3, 7*2^d*w_d<=8*4^s and 7*2^(d-1)*sum(seamWeightsFrom s d)<=8*4^s. Also 4*2^s<=2^(2s-1) for s>=3, and the head weight w_2 is strictly below the actual seam target.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: These inequalities locate the scale of a counterexample capacity. They do not themselves compute its greedy remainder or say that the actual seam target has a large remainder.

- Lean declaration: [head_weight_small](../../ErdosProblems/Rem/C5.lean#L327)
- Lean declaration: [tail_sum_small](../../ErdosProblems/Rem/C5.lean#L350)
- Lean declaration: [four_mul_two_pow_le](../../ErdosProblems/Rem/C5.lean#L376)
- Lean declaration: [head_lt_target](../../ErdosProblems/Rem/C5.lean#L383)

- incoming **generated_by**: [Z88::an_admissible_head_minus_one_capacity_blocks_any_two_power_word_only_bound](BROWSER_Z88_1.md#node-d94be37b64a21d99). The head and suffix inequalities quantify the exact head-minus-one remainder and place it at order 4^s.

<a id="node-fc3d02f362620c0b"></a>
## integer_greedy_remainder_has_exact_list_recursion_and_append_composition

EXACT GREEDY CALCULUS: the remainder on the empty word is C. On w::t it recurses on t with capacity C-w when w<=C and with unchanged capacity C when w>C. If the whole list sum is at most C, the result is C minus that sum. Scanning an append l1++l2 is exactly scanning l1 first and then scanning l2 from the resulting remainder.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: These are exact algorithmic identities for arbitrary finite lists. They contain no seam-weight estimates and give no small-remainder bound without additional hypotheses.

- Lean declaration: [greedyRemainder_nil](../../ErdosProblems/Rem/C5.lean#L104)
- Lean declaration: [greedyRemainder_cons_take](../../ErdosProblems/Rem/C5.lean#L107)
- Lean declaration: [greedyRemainder_cons_skip](../../ErdosProblems/Rem/C5.lean#L114)
- Lean declaration: [greedyRemainder_eq_sub_sum](../../ErdosProblems/Rem/C5.lean#L120)
- Lean declaration: [greedyRemainder_append](../../ErdosProblems/Rem/C5.lean#L131)

- incoming **generated_by**: [Z88::tail_domination_bounds_every_admissible_greedy_remainder_by_the_slack](BROWSER_Z88_1.md#node-0975cf2f0890732b). The abstract counting theorem is proved by list induction through the exact head take/skip recursion.
- incoming **generated_by**: [Z88::a_certified_skipped_rank_restarts_the_counting_bound_on_its_suffix](BROWSER_Z88_1.md#node-736482d0eae471d6). The append composition law identifies the entering remainder and the suffix computation at the selected rank.

<a id="node-c900fdf37ad22c12"></a>
## row_eight_computes_the_head_minus_one_sharpness_remainder_exactly

FINITE SHARPNESS CERTIFICATE: at s=8 and capacity truncatedMersenneWeight 8 2 - 1=21844, the greedy remainder on seamWeights 8 is exactly 4443, which is greater than 17 times 2^8.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is one finite counterexample capacity, not the actual seam target and not evidence about the asymptotic behavior of seamIntegerGreedyRemainder.

- Lean declaration: [counting_bound_sharp_eight](../../ErdosProblems/Rem/C5.lean#L701)

- outgoing **finite_instance_of**: [Z88::an_admissible_head_minus_one_capacity_blocks_any_two_power_word_only_bound](BROWSER_Z88_1.md#node-d94be37b64a21d99). The exact value 4443 is the row-8 instance of the same head-minus-one capacity used in the general sharpness barrier.

<a id="node-8ff7e78e42b91010"></a>
## rows_eight_eleven_and_twelve_exhibit_live_skip_and_ceiling_certificates

FINITE NON-VACUITY PACKET: the exact seam word at row 8 skips its last rank 7 and obeys the remainder ceiling. Exact words and rank-8 suffix sums at rows 11 and 12 certify a skip at rank 7 and the ceiling there as well. Rows 11 and 12 simultaneously fail Bit/R2.LargestSkipLateAt, so these two ceilings genuinely come from the localized C5 skip mechanism rather than the earlier good-row theorem.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Three rows are finite evidence only. They do not establish a pattern, an eventual or cofinal supply of skipped ranks, or the universal ceiling required to settle Erdős 257.

- Lean declaration: [seamWeights_eight](../../ErdosProblems/Rem/C5.lean#L586)
- Lean declaration: [skipsRank_eight](../../ErdosProblems/Rem/C5.lean#L599)
- Lean declaration: [obeysCeiling_eight](../../ErdosProblems/Rem/C5.lean#L606)
- Lean declaration: [seamWeights_eleven](../../ErdosProblems/Rem/C5.lean#L611)
- Lean declaration: [seamTail_eleven](../../ErdosProblems/Rem/C5.lean#L627)
- Lean declaration: [skipsRank_eleven](../../ErdosProblems/Rem/C5.lean#L635)
- Lean declaration: [obeysCeiling_eleven](../../ErdosProblems/Rem/C5.lean#L642)
- Lean declaration: [seamWeights_twelve](../../ErdosProblems/Rem/C5.lean#L649)
- Lean declaration: [seamTail_twelve](../../ErdosProblems/Rem/C5.lean#L667)
- Lean declaration: [skipsRank_twelve](../../ErdosProblems/Rem/C5.lean#L675)
- Lean declaration: [obeysCeiling_twelve](../../ErdosProblems/Rem/C5.lean#L682)
- Lean declaration: [ceiling_at_bad_rows](../../ErdosProblems/Rem/C5.lean#L693)

- outgoing **finite_instance_of**: [Z88::a_certified_skipped_rank_restarts_the_counting_bound_on_its_suffix](BROWSER_Z88_1.md#node-736482d0eae471d6). Rows 11 and 12 instantiate the generic rank-7 skip theorem, and row 8 instantiates its last-rank specialization.
- outgoing **finite_instance_of**: [Z88::skipping_the_last_rank_automatically_forces_the_remainder_ceiling](BROWSER_Z88_1.md#node-f468d3eb2db79d13). The row-8 certificate skips its last rank and obtains the ceiling through the last-rank theorem.

<a id="node-bf11027b971a25e4"></a>
## seam_counting_gives_an_unconditional_four_power_over_eight_remainder_bound

GLOBAL POSITIVE RESULT: for s>=3 and every capacity C<=2*w_2, the greedy remainder on seamWeights s plus the suffix sum from rank 3 is at most w_2. The actual seam target satisfies that capacity condition, and for every s>=6 the resulting concrete remainder obeys 8*seamIntegerGreedyRemainder s<=4^s.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The bound improves the trivial target-size estimate but remains of order 4^s. It is weaker than later Rem/C6 bounds and does not reach the 2^s scale needed to resolve Erdős 257.

- Lean declaration: [seam_remainder_bound](../../ErdosProblems/Rem/C5.lean#L261)
- Lean declaration: [seamIntegerGreedyRemainder_add_tail_le](../../ErdosProblems/Rem/C5.lean#L277)
- Lean declaration: [eight_mul_remainder_le](../../ErdosProblems/Rem/C5.lean#L299)

- outgoing **generated_by**: [Z88::tail_domination_bounds_every_admissible_greedy_remainder_by_the_slack](BROWSER_Z88_1.md#node-0975cf2f0890732b). The global seam bound instantiates the abstract theorem with the rank-2 exact head slack.
- outgoing **generated_by**: [Z88::seam_suffixes_are_geometrically_decreasing_and_tail_dominated_by_exact_head_slack](BROWSER_Z88_1.md#node-3da1fb11987ac2bb). The seam suffix geometry supplies both TailDominated and the exact head-versus-tail slack used in the specialization.
- outgoing **generated_by**: [Z88::dyadic_scale_and_seam_head_comparisons_control_the_global_counting_input](BROWSER_Z88_1.md#node-0b5dd454091b960a). The scale comparisons verify actual-target admissibility and convert the head-slack estimate to 8*remainder<=4^s.
- incoming **barrier_for**: [Z88::an_admissible_head_minus_one_capacity_blocks_any_two_power_word_only_bound](BROWSER_Z88_1.md#node-d94be37b64a21d99). The admissible counterexample proves that the word-only upper bound cannot be strengthened uniformly from order 4^s to the desired 2^s scale without target-specific information.

<a id="node-3da1fb11987ac2bb"></a>
## seam_suffixes_are_geometrically_decreasing_and_tail_dominated_by_exact_head_slack

SEAM SUFFIX GEOMETRY: when d<s, the suffix sum at d is its head truncatedMersenneWeight s d plus the suffix sum at d+1. For s>=2 and 1<=d<s the later tail is at most the head, while consecutive weights satisfy 2*w_(d+1)<=w_d. These inequalities propagate along the chain and prove that every suffix starting at j>=a is TailDominated by the exact rank-a head slack w_a-sum(tail after a).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The estimates concern the deterministic seam weight list. They do not determine which weights the actual greedy target takes or skips and do not yet produce the Bit/R2 ceiling.

- Lean declaration: [tail_sum_succ](../../ErdosProblems/Rem/C5.lean#L172)
- Lean declaration: [tail_sum_le_weight](../../ErdosProblems/Rem/C5.lean#L177)
- Lean declaration: [two_mul_weight_succ_le](../../ErdosProblems/Rem/C5.lean#L183)
- Lean declaration: [seam_chain](../../ErdosProblems/Rem/C5.lean#L206)
- Lean declaration: [seam_tailDominated](../../ErdosProblems/Rem/C5.lean#L221)

- incoming **generated_by**: [Z88::seam_counting_gives_an_unconditional_four_power_over_eight_remainder_bound](BROWSER_Z88_1.md#node-bf11027b971a25e4). The seam suffix geometry supplies both TailDominated and the exact head-versus-tail slack used in the specialization.

<a id="node-f468d3eb2db79d13"></a>
## skipping_the_last_rank_automatically_forces_the_remainder_ceiling

LAST-RANK SPECIALIZATION: for s>=4 the final seam weight is exactly 2^(s+1)+4. Therefore, if the greedy skips rank s-1, its final remainder is at most 2^(s+1)+4 and the row automatically satisfies Bit/R2.ObeysRemainderCeiling.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The conclusion assumes that the last rank is skipped. The module certifies this at row 8 only; it does not prove last-rank skipping for arbitrary or cofinally many rows.

- Lean declaration: [weight_last](../../ErdosProblems/Rem/C5.lean#L527)
- Lean declaration: [remainder_le_of_skipsLast](../../ErdosProblems/Rem/C5.lean#L552)
- Lean declaration: [obeysCeiling_of_skipsLast](../../ErdosProblems/Rem/C5.lean#L560)

- outgoing **specialises**: [Z88::a_certified_skipped_rank_restarts_the_counting_bound_on_its_suffix](BROWSER_Z88_1.md#node-736482d0eae471d6). At rank s-1 the later suffix is empty and the exact last weight makes the generic slack comparison automatic.
- incoming **finite_instance_of**: [Z88::rows_eight_eleven_and_twelve_exhibit_live_skip_and_ceiling_certificates](BROWSER_Z88_1.md#node-8ff7e78e42b91010). The row-8 certificate skips its last rank and obtains the ceiling through the last-rank theorem.

<a id="node-0975cf2f0890732b"></a>
## tail_domination_bounds_every_admissible_greedy_remainder_by_the_slack

ABSTRACT COUNTING BOUND: for any finite natural-number weight list l, if every suffix head is at most its later-tail sum plus B and the capacity satisfies C<=sum(l)+B, then integerGreedyRemainder l C<=B.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The conclusion is only as strong as the supplied uniform slack B. The theorem does not prove tail domination for seam weights and does not distinguish the actual seam target from another admissible capacity.

- Lean declaration: [greedyRemainder_le_of_tailDominated](../../ErdosProblems/Rem/C5.lean#L153)

- outgoing **generated_by**: [Z88::integer_greedy_remainder_has_exact_list_recursion_and_append_composition](BROWSER_Z88_1.md#node-fc3d02f362620c0b). The abstract counting theorem is proved by list induction through the exact head take/skip recursion.
- incoming **generated_by**: [Z88::seam_counting_gives_an_unconditional_four_power_over_eight_remainder_bound](BROWSER_Z88_1.md#node-bf11027b971a25e4). The global seam bound instantiates the abstract theorem with the rank-2 exact head slack.
- incoming **generated_by**: [Z88::a_certified_skipped_rank_restarts_the_counting_bound_on_its_suffix](BROWSER_Z88_1.md#node-736482d0eae471d6). After splitting at a skipped rank, the same abstract TailDominated theorem bounds the remaining suffix by its local head slack.

