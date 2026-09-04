# Z01_1: Certificate kernel: irrationality engines, block certificates and the wave chain

[All problems and zones](BROWSER.md)

<a id="node-9f94182cfe2c39ce"></a>
## bounded_crt_exact_valuation_frame

For every base b at least 2 and every block depth K there is an arithmetic progression, with explicitly bounded modulus built from Bertrand prime blocks and the Chinese remainder theorem, along which each slot r of the first block carries r distinct primes of prescribed exact valuation b-1 (or b*phi(m)-1 in the periodic variant), forcing b^r to divide the divisor count of the slot; the modulus support is controlled so that middle-window entries stay coprime to it.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [exists_exact_valuation_progression](../../Erdos249257/CertificateKernel.lean#L7047)
- Lean declaration: [exists_first_block_divisibility_progression](../../Erdos249257/CertificateKernel.lean#L7138)
- Lean declaration: [exists_exact_valuation_progression_with_support](../../Erdos249257/CertificateKernel.lean#L7160)
- Lean declaration: [exists_bounded_first_block_frame](../../Erdos249257/CertificateKernel.lean#L7886)
- Lean declaration: [exists_bounded_exact_valuation_frame](../../Erdos249257/CertificateKernel.lean#L11119)
- Lean declaration: [exists_bounded_disjoint_prime_blocks](../../Erdos249257/CertificateKernel.lean#L7733)
- Lean declaration: [exists_bounded_crt_residue](../../Erdos249257/CertificateKernel.lean#L7831)
- Lean declaration: [exists_bertrand_prime_block](../../Erdos249257/CertificateKernel.lean#L7696)
- Lean declaration: [factorization_eq_of_modEq_prod_pow](../../Erdos249257/CertificateKernel.lean#L6963)
- Lean declaration: [bpow_dvd_card_divisors_of_exact_prime_block](../../Erdos249257/CertificateKernel.lean#L6505)

- outgoing **implies**: [Z01::tau_block_certificate_supply](BROWSER_Z01_2.md#node-78e11eccc7fdd413). the frame is what makes the first-block divisibility condition satisfiable

<a id="node-9a3634435b900811"></a>
## canonical_witness_selector_reduction

For every finite nonempty support F of positive exponents and every prime p dividing the lcm there is a member n of F that is simultaneously valuation-maximal at p and maximal for divisibility inside F; an exact-order prime-power witness for that selector row supplies the prime-component witness at p, so an exact-order witness supply for every isolated row already gives period non-collapse.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [exists_lcm_factorization_le_row](../../Erdos249257/CertificateKernel.lean#L4473)
- Lean declaration: [exists_canonical_witness_selector_row](../../Erdos249257/CertificateKernel.lean#L4508)
- Lean declaration: [exact_order_witness_supplies_PrimeComponentWitness](../../Erdos249257/CertificateKernel.lean#L4566)
- Lean declaration: [finite_period_noncollapse_from_exact_order_witness_supply](../../Erdos249257/CertificateKernel.lean#L4669)

- outgoing **specialises**: [Z01::period_noncollapse_witness_reduction](BROWSER_Z01_2.md#node-9c0398d7b79861e9). the selector row is one concrete way of producing the per-prime witness the general reduction demands
- incoming **implies**: [Z01::exact_order_prime_power_witness_supply](BROWSER_Z01_1.md#node-16390fae0f7684fc). the unconditional exact-order supply discharges the selector reduction's only hypothesis

<a id="node-85bdec04dff8f727"></a>
## carry_aware_certificate_engine

The first-block condition may be certified in aggregate: if b^K divides the packed carry sum of the first block then the same near-integer witness and the same irrationality conclusion follow, and the digitwise certificate is the special case in which every slot is individually divisible.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [carry_block_dvd_of_digitwise_blocks](../../Erdos249257/CertificateKernel.lean#L9153)
- Lean declaration: [near_int_witness_of_weighted_coeff_carry_block_certificate](../../Erdos249257/CertificateKernel.lean#L9169)
- Lean declaration: [irrational_coeff_series_of_weighted_coeff_carry_block_certificates](../../Erdos249257/CertificateKernel.lean#L9339)
- Lean declaration: [irrational_coeff_series_of_digitwise_via_carry](../../Erdos249257/CertificateKernel.lean#L9362)
- Lean declaration: [irrational_erdosSupportSeries_of_weighted_coeff_carry_certificates](../../Erdos249257/CertificateKernel.lean#L9381)

- outgoing **generalises**: [Z01::generic_coefficient_certificate_engine](BROWSER_Z01_1.md#node-347d00f05c4a588d). aggregate first-block integrality is strictly weaker than digitwise divisibility
- incoming **generalises**: [Z01::low_carry_certificate_engine](BROWSER_Z01_2.md#node-f9f70d124b7b25b4). the residue band contains the exact-carry case as its zero-residue point
- incoming **specialises**: [Z01::erdos249_certificate_supply_restatement](BROWSER_Z01_1.md#node-fe5e91cb1960ad1c). the totient at base 2 is the coefficient instance of the generic carry engine
- incoming **barrier_for**: [Z10::no_block_certificate_at_squarefree_support](BROWSER_Z10_2.md#node-8a6ef15977d14203). not_exists_carry_certificates_squarefreeSupport, via no_carry_block_certificate: the carried first block forces b to divide the last first-block coefficient (carry_block_forces_base_divides_last_coefficient), but the squarefree incidence is 2^omega(n) - 1, odd at every n >= 2 (squarefree_incidence_is_two_pow_omega_minus_one), so the aggregate divisibility hypothesis of irrational_coeff_series_of_weighted_coeff_carry_block_certificates has no instance at even b.
- incoming **transport_of**: [Z10::sunflower_conditional_irrationality](BROWSER_Z10_2.md#node-369dbe6f906c9180). forcedSlotCarrySelection_of_tailSelection and sunflowerForcedCarrySupply_of_forcedSlotCarrySelection restate the carry-aware block-certificate supply of irrational_erdosSupportSeries_of_weighted_coeff_carry_certificates as a forced-slot selector on an orthogonal petal bouquet; the obligation is the same certificate supply in support coordinates.

<a id="node-f5235071542ebedb"></a>
## certified_kill_fixtures

Verified kill instances: all shifts 1 to 8 killed at position 12 depth 16 and all shifts 1 to 16 killed at position 14 depth 9; lcm-diagonal cells killed for t up to 6 and at t = 7, 8, with the corresponding tail differences shown non-integral; three lcm-cone cells killed; three cone non-flatness menus certified.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [totient_tail_period_killed_upto_eight](../../Erdos249257/CertificateKernel.lean#L18800)
- Lean declaration: [totient_tail_period_killed_upto_sixteen](../../Erdos249257/CertificateKernel.lean#L18883)
- Lean declaration: [totient_tail_period_lcm_diagonal_killed_upto_six](../../Erdos249257/CertificateKernel.lean#L18961)
- Lean declaration: [totient_tail_period_lcm_diagonal_killed_at_seven_and_eight](../../Erdos249257/CertificateKernel.lean#L18970)
- Lean declaration: [totient_tail_period_lcm_diagonal_not_int_at_seven_and_eight](../../Erdos249257/CertificateKernel.lean#L19098)
- Lean declaration: [totient_tail_lcm_cone_cells_killed](../../Erdos249257/CertificateKernel.lean#L19077)
- Lean declaration: [totient_tail_cone_nonflat_cells_certified](../../Erdos249257/CertificateKernel.lean#L19161)

- outgoing **finite_instance_of**: [Z01::certified_kill_soundness](BROWSER_Z01_1.md#node-ce3a6b8b2b87a632). explicit verified kills at named cells
- incoming **implies**: [Z01::totient_series_rational_exclusions_from_kills](BROWSER_Z01_2.md#node-4bdd060dc42777bf). the fixture kills exclude exactly the rationals whose denominator has the corresponding Mersenne shape
- outgoing **equivalent_to**: [Z06::finite_kill_deposits](BROWSER_Z06_1.md#node-91eeb9cf682bd8dd). Same kernel-decided cells: endpoint kills for h<=8 at (12,16) and h<=16 at (14,9), lcm-diagonal kills through t=8, three off-diagonal cone cells and three certified menus.
- incoming **reformulates**: [Z05::t_seven_finite_full_target_miss](BROWSER_Z05_2.md#node-7cc8cb692e7c3423). By diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget, foreignDiagonalDefect_misses_fullTarget_seven is non-integrality of R_{2H_7}-R_{H_7}, which is totient_tail_period_lcm_diagonal_not_int_at_seven_and_eight.
- outgoing **finite_instance_of**: [Z06::reduction_pointwise_certificate_supply](BROWSER_Z06_1.md#node-eb9013360d8a36f2). the fixture kills certifiedKill h 12 16 for h<=8 and certifiedKill h 14 9 for h<=16 are cells of the same predicate the pointwise supply quantifies as 'for every h and every N0 some N>=N0 with a firing depth'; only the two bases N=12,14 are realised.
- outgoing **finite_instance_of**: [Z06::reduction_lcm_diagonal_supply](BROWSER_Z06_1.md#node-9bc987ebd91ed7a5). the lcm-diagonal cells killed for t<=6 and at t=7,8 are literally certifiedKill (periodLcm t) (periodLcm t) L, the decidable predicate P t whose cofinal truth is the diagonal supply hypothesis.
- outgoing **finite_instance_of**: [Z06::reduction_lcm_cone_supply](BROWSER_Z06_1.md#node-0b5ba2e40a1dd8ec). the three killed lcm-cone cells are instances of certifiedKill (m*periodLcm t) (q*periodLcm t) L, the annihilator the two-multiplier cone supply asks for at arbitrarily large scale.
- outgoing **finite_instance_of**: [Z06::reduction_cone_nonflat_menu_supply](BROWSER_Z06_1.md#node-83d97029da15536b). the three certified cone non-flatness menus are firing coneNonflatCert (periodLcm t) L Q rows, the exact object the menu supply requires at arbitrarily large t.
- incoming **depends_on_open**: [Z06::reduction_pointwise_certificate_supply](BROWSER_Z06_1.md#node-eb9013360d8a36f2). the fixtures produce certifiedKill h N L only at the two bases N = 12 and N = 14 and only for h <= 8 and h <= 16; the supply demands arbitrarily large N for every h, and no node supplies a further base for any h.
- incoming **depends_on_open**: [Z06::reduction_lcm_cone_supply](BROWSER_Z06_1.md#node-0b5ba2e40a1dd8ec). the three killed lcm-cone cells here are the only certified annihilators on the cone outside the diagonal; they sit at bounded scale and produce nothing cofinal.
- incoming **depends_on_open**: [Z06::reduction_cone_nonflat_menu_supply](BROWSER_Z06_1.md#node-83d97029da15536b). the three certified non-flatness menus recorded here are the corpus's entire stock of firing menus; the supply needs one per arbitrarily large scale.
- incoming **depends_on_open**: [Z06::reduction_multiple_period_supply](BROWSER_Z06_1.md#node-0818db056d314224). the endpoint and survivor kills recorded here are the only realised multiples m*h0 carrying a firing certificate, and they sit at two fixed positions; nothing produces a kill at arbitrarily large N for a general primitive period.
- outgoing **alias_of**: [Z06::finite_kill_deposits](BROWSER_Z06_1.md#node-91eeb9cf682bd8dd). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18472/18555/18633/18749/18833 re-export `certifiedKill_all_small`, `certifiedKill_all_upto_sixteen`, `certifiedKill_periodLcm_diagonal_upto_six`, the lcm-cone cells and the coneNonflatCert cells; the Z01 fixture list is the re-exported subset of Z06's deposit list.
- outgoing **specialises**: [Z02::aggregate_imported_scales_fire](BROWSER_Z02_1.md#node-8747b08e0d7df4ce). Z01's `totient_tail_period_lcm_diagonal_killed_upto_six` and `..._at_seven_and_eight` assert the diagonal kill at the scales t <= 8, which are members of the literal list quantified over by Z02's `certifiedKill_diagonal_all_imported_through_t29`; depth differences are absorbed by the depth-monotonicity theorem `certifiedKill_succ` (Z06).
- incoming **specialises**: [Z05::t_seven_finite_full_target_miss](BROWSER_Z05_2.md#node-7cc8cb692e7c3423). `foreignDiagonalDefect_misses_fullTarget_seven` (DiagonalPincerDecomposition.lean:275) is proved as `tail_diff_not_int_periodLcm_diagonal_seven_eight.1` transported through the definitional pincer iff `diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget` (:215); it is the t = 7 cell of Z01's `totient_tail_period_lcm_diagonal_not_int_at_seven_and_eight`.

<a id="node-ce3a6b8b2b87a632"></a>
## certified_kill_soundness

Soundness of the decidable kill certificates: a certified window kill, a carry-survivor kill, or a rank-two second-difference kill each proves that the corresponding totient tail difference is not an integer.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [totient_tail_diff_not_int_of_certified_kill](../../Erdos249257/CertificateKernel.lean#L18775)
- Lean declaration: [totient_tail_diff_not_int_of_survivor_kill](../../Erdos249257/CertificateKernel.lean#L18833)
- Lean declaration: [totient_tail_second_diff_not_int_of_rank_two_kill](../../Erdos249257/CertificateKernel.lean#L19057)

- outgoing **implies**: [Z01::erdos249_period_kill_supply_restatement](BROWSER_Z01_1.md#node-091f2dbf4dfd2e47). kill soundness converts each certificate into the non-integrality the period law needs
- incoming **equivalent_to**: [Z01::window_kill_completeness](BROWSER_Z01_2.md#node-82033994a112e164). completeness plus soundness make certificate existence and non-integrality the same predicate
- incoming **barrier_for**: [Z01::engine_strength_separations](BROWSER_Z01_1.md#node-8f3c278e1c645ebc). exhibits cells where one kill engine fires and a sibling engine at the same budget does not, so no engine here may be treated as subsuming the others
- incoming **finite_instance_of**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). explicit verified kills at named cells
- outgoing **equivalent_to**: [Z06::endpoint_certificate_soundness](BROWSER_Z06_1.md#node-552175c811881922). Both nodes carry the same declaration tail_diff_notMem_int_of_certifiedKill (TotientTailPeriodKiller.lean); Z01 bundles the survivor and rank-two dresses of the identical truncation-and-residue-band soundness argument.
- outgoing **alias_of**: [Z06::endpoint_certificate_soundness](BROWSER_Z06_1.md#node-552175c811881922). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18447 `totient_tail_diff_not_int_of_certified_kill := TotientTailPeriodKiller.tail_diff_notMem_int_of_certifiedKill`.
- outgoing **alias_of**: [Z06::carry_orbit_survivor_soundness](BROWSER_Z06_1.md#node-05d318200f8fe921). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18505 `totient_tail_diff_not_int_of_survivor_kill := TotientTailPeriodKiller.tail_diff_notMem_int_of_survivorKill`.
- outgoing **alias_of**: [Z06::rank2_second_difference_soundness](BROWSER_Z06_1.md#node-a1d74e04b71bd15d). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18729 `totient_tail_second_diff_not_int_of_rank_two_kill := TotientTailPeriodKiller.second_diff_notMem_int_of_certifiedRank2Kill`.

<a id="node-777841e3f0e5f4e5"></a>
## coefficient_nonnegative_signed_irrationality

For every base b at least 2 and every periodic integer weight whose divisor coefficients are all nonnegative (or all nonpositive) and do not eventually vanish, the signed series is irrational: a terminating value would force every coefficient beyond the first block to vanish, contradicting the non-vanishing assumption. This closes the terminating escape of the dichotomy for sign-mixed weights with one-signed coefficients.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero](../../Erdos249257/CertificateKernel.lean#L14583)
- Lean declaration: [irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero](../../Erdos249257/CertificateKernel.lean#L14643)
- Lean declaration: [coeff_eq_zero_of_full_block_certificate_of_bpow_mul_eq_intCast](../../Erdos249257/CertificateKernel.lean#L14328)

- outgoing **repair_of**: [Z01::signed_weight_dichotomy](BROWSER_Z01_2.md#node-70067b8f2d9c9efe). closes the terminating alternative of the dichotomy for one-signed divisor coefficients

<a id="node-779bda153125d283"></a>
## concrete_period_noncollapse_instances

Verified period non-collapse and certificate-row instances at explicit small parameters: base 2 with exponent sets {2}, {6}, {10}, {30} and base 3 with {2}, giving the orders of 2 modulo 3, 63, 1023 and 1073741823, plus the corresponding emitted certificate tables and local-layer fixtures.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [orderOf_b2_mod63_eq_6_from_emittedCertificate](../../Erdos249257/CertificateKernel.lean#L3455)
- Lean declaration: [orderOf_b2_mod1023_eq_10_from_emittedCertificate](../../Erdos249257/CertificateKernel.lean#L3638)
- Lean declaration: [orderOf_b2_mod1073741823_eq_30_from_emittedCertificate](../../Erdos249257/CertificateKernel.lean#L3870)
- Lean declaration: [finite_period_noncollapse_from_concrete_generated_rows](../../Erdos249257/CertificateKernel.lean#L3216)
- Lean declaration: [finite_period_noncollapse_from_multi_support_generated_rows](../../Erdos249257/CertificateKernel.lean#L3477)
- Lean declaration: [orderOf_b2_mod63_eq_6_from_exact_order_witness_route](../../Erdos249257/CertificateKernel.lean#L4778)
- Lean declaration: [b2_F3_6_p3_local_layer_blocks_collapse_fixture](../../Erdos249257/CertificateKernel.lean#L4295)

- outgoing **finite_instance_of**: [Z01::finite_period_noncollapse](BROWSER_Z01_1.md#node-ed84a74576eddd3a). explicit (b, F) fixtures instantiate the general period non-collapse theorem
- outgoing **finite_instance_of**: [Z10::finite_fragment_residual_transport](BROWSER_Z10_1.md#node-cc4b29d2ebadd1ad). the transport's exact-period clause says a removed finite fragment F leaves a rational with odd reduced denominator whose order of 2 is exactly lcm F; the fixtures verify that at F = {2},{6},{10},{30} with denominators 3, 63, 1023 and 2^30-1 and orders 2, 6, 10, 30.

<a id="node-18a57855d478e08e"></a>
## cone_nonflat_menu_refuter

A firing cone non-flatness certificate over a finite menu of cone vertices, with one-sided floors held, forces some pair of menu vertices to have a non-integral totient tail difference. Each vertex charges only its own one-sided radius, so the menu floor is half the pairwise floor.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [totient_tail_nonintegral_pair_of_cone_nonflat_cert](../../Erdos249257/CertificateKernel.lean#L19129)

- outgoing **implies**: [Z01::erdos249_cone_nonflat_supply_restatement](BROWSER_Z01_1.md#node-4653d6568a5b39ff). menu soundness is what converts a firing menu into a non-integral cone pair
- incoming **reformulates**: [Z01::menu_refuter_exactness_and_monotonicity](BROWSER_Z01_2.md#node-95967a6c8d05ed40). characterises exactly when the refuter fires and shows firing persists at greater depth and larger menus
- outgoing **alias_of**: [Z06::menu_refuter_soundness](BROWSER_Z06_1.md#node-a8ce1315616306e2). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18801 `totient_tail_nonintegral_pair_of_cone_nonflat_cert := TotientTailPeriodKiller.exists_nonintegral_pair_of_coneNonflatCert`.

<a id="node-c94ed0ccee7e7675"></a>
## den_gap_irrationality_criterion

A real number is irrational if it is approximated by a sequence of rationals that are eventually distinct from it and for which the denominator times the approximation error tends to zero.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [irrational_of_den_mul_abs_sub_tendsto_zero](../../Erdos249257/CertificateKernel.lean#L5371)
- Lean declaration: [one_div_den_mul_den_le_abs_sub](../../Erdos249257/CertificateKernel.lean#L5342)

- incoming **specialises**: [Z01::lcm_gap_irrationality_theorem](BROWSER_Z01_1.md#node-df3ac7a0b39aeae8). the lcm-gap theorem is the denominator-gap criterion applied to partial sums whose denominators are controlled by period non-collapse

<a id="node-5af9c6b05c0988ca"></a>
## denominator_outgrows_lcm

For a finite exponent set whose lcm is at least 2, the denominator of the corresponding partial sum is strictly larger than that lcm; in particular the partial sums over 1..N of 1/(b^n - 1) have denominators exceeding lcm(1..N).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [lcm_lt_den_finiteErdosSum](../../Erdos249257/CertificateKernel.lean#L5260)
- Lean declaration: [lcm_Icc_lt_den_erdosPartialSum](../../Erdos249257/CertificateKernel.lean#L5291)

- outgoing **specialises**: [Z01::finite_period_noncollapse](BROWSER_Z01_1.md#node-ed84a74576eddd3a). the denominator lower bound is read off the exact order equality

<a id="node-82d682802aaa267c"></a>
## divisor_block_certificate_engine

A finite block certificate (N,K,L,B or N,K,L,C) whose first block satisfies b^r dividing tau(N+r) for r up to K, whose middle window is bounded pointwise or in weighted form, and whose one arithmetic inequality dominates the geometric middle mass and the crude far tail, produces a near-integer witness; certificates for every precision give full-support irrationality.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [near_int_witness_of_divisor_block_certificate](../../Erdos249257/CertificateKernel.lean#L6527)
- Lean declaration: [irrational_erdosSum_full_support_of_block_certificates](../../Erdos249257/CertificateKernel.lean#L6708)
- Lean declaration: [near_int_witness_of_weighted_divisor_block_certificate](../../Erdos249257/CertificateKernel.lean#L6791)
- Lean declaration: [irrational_erdosSum_full_support_of_weighted_block_certificates](../../Erdos249257/CertificateKernel.lean#L6944)
- Lean declaration: [weighted_block_certificate_of_pointwise](../../Erdos249257/CertificateKernel.lean#L6773)

- outgoing **repair_of**: [Z01::lcm_gap_fails_at_full_support](BROWSER_Z01_1.md#node-61c9e082f77d5d6b). the near-integer block-certificate engine is the replacement route to full support that the barrier forces
- outgoing **implies**: [Z01::full_support_near_int_reduction](BROWSER_Z01_1.md#node-84f534afd83c7e7d). a block certificate produces exactly the near-integer witness the reduction demands
- incoming **implies**: [Z01::tau_block_certificate_supply](BROWSER_Z01_2.md#node-78e11eccc7fdd413). supplies the certificates the engine consumes, at every precision
- incoming **generalises**: [Z01::generic_coefficient_certificate_engine](BROWSER_Z01_1.md#node-347d00f05c4a588d). the same certificate shape stated for an arbitrary coefficient sequence with a growth envelope
- incoming **transport_of**: [Z17::n1049_three_halves_barrier](BROWSER_Z17_1.md#node-2f70395be8f6b4ad). Reviewed judgement, not a Lean bridge: the coordinatewise corridor a^K | Q*digit with Q*b^(N+K+1) < a^(K+1) is the rational-base transcription of the divisibility-plus-height pair of a digitwise block certificate; no Lean declaration ties coordinatewiseCorridor to the CertificateKernel schema.

<a id="node-8f3c278e1c645ebc"></a>
## engine_strength_separations

Kernel-checked separations between the #249 certificate engines at explicit cells: the carry-survivor certificate kills a period at a cell where no window certificate of equal budget does; the rank-two second-difference certificate is sound but strictly deeper than the plain window certificate at its fixture cell; the cone non-flatness menu refuter strictly beats the pairwise window certificate in depth at one cell and fires jointly on a three-vertex menu where every two-vertex sub-menu fails.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [totient_tail_survivor_strict_at_equal_budget](../../Erdos249257/CertificateKernel.lean#L18876)
- Lean declaration: [totient_tail_rank_two_kill_sound_but_not_shallower_cell](../../Erdos249257/CertificateKernel.lean#L19090)
- Lean declaration: [totient_tail_cone_nonflat_strict_win_at_cell](../../Erdos249257/CertificateKernel.lean#L19173)
- Lean declaration: [totient_tail_cone_nonflat_joint_win_at_cell](../../Erdos249257/CertificateKernel.lean#L19190)

- outgoing **barrier_for**: [Z01::certified_kill_soundness](BROWSER_Z01_1.md#node-ce3a6b8b2b87a632). exhibits cells where one kill engine fires and a sibling engine at the same budget does not, so no engine here may be treated as subsuming the others
- outgoing **equivalent_to**: [Z06::certificate_family_comparisons_at_cells](BROWSER_Z06_1.md#node-ae74fd4330038e95). Same four separation fixtures (survivor_strict_at_equal_budget, rank2_kill_sound_but_not_shallower_at_cell, cone_nonflat_strict_win_at_cell, cone_nonflat_joint_win_at_cell) under the two zones' naming.
- outgoing **finite_instance_of**: [Z06::reduction_cone_nonflat_menu_supply](BROWSER_Z06_1.md#node-83d97029da15536b). the recorded three-vertex menu that fires where every two-vertex sub-menu fails is a firing coneNonflatCert instance at one cell of the menu supply family, and it also shows that family is not exhausted by its two-vertex sub-cells.
- incoming **depends_on_open**: [Z06::reduction_rank2_qray_supply](BROWSER_Z06_2.md#node-725e8c140eeebb35). the only rank-two second-difference certificate exhibited anywhere is the single fixture cell recorded in this separation node (and its twin among the Z06 deposits); one cell does not produce a q-ray supply at arbitrarily large scale.
- outgoing **alias_of**: [Z06::certificate_family_comparisons_at_cells](BROWSER_Z06_1.md#node-ae74fd4330038e95). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18548/18762/18845/18862 re-export `survivor_strict_at_equal_budget`, `rank2_kill_sound_but_not_shallower_at_cell`, `cone_nonflat_strict_win_at_cell`, `cone_nonflat_joint_win_at_cell`; the same four single-cell separations.

<a id="node-500dc88fa675b8f4"></a>
## engine_subsumption_carry_low_carry_gap

Engine ordering, machine-checked: an exact-carry certificate is the zero-residue case of a low-carry residue-band certificate, and a low-carry certificate is the j = 0 case of a gap certificate. The digitwise, exact-carry, low-carry and gap interfaces therefore form a chain of strictly weakening demands rather than independent methods.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [irrational_coeff_series_of_carry_via_low_carry](../../Erdos249257/CertificateKernel.lean#L15060)
- Lean declaration: [totient_gap_certificate_of_low_carry_certificate](../../Erdos249257/CertificateKernel.lean#L16006)
- Lean declaration: [totient_low_carry_full_block_certificate_mono](../../Erdos249257/CertificateKernel.lean#L15319)

- outgoing **reformulates**: [Z01::gap_certificate_engine](BROWSER_Z01_1.md#node-d3d303b78be4b97c). records the machine-checked chain digitwise to carry to low-carry to gap

<a id="node-fe5e91cb1960ad1c"></a>
## erdos249_certificate_supply_restatement

If block certificates (digitwise, carry-aware, low-carry residue-band, or low-carry full-block) exist at every precision q for the totient coefficient at base 2, then the sum of phi(n)/2^n is irrational. Each of these is Erdos #249 with the open content moved into the certificate-supply hypothesis; none of the supplies is proved.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Open hypotheses: ["hcert : forall q, 0 < q -> exists N K L C, K <= L and (forall r in Icc 1 K, 2^r divides Nat.totient (N+r)) and (sum over Icc (K+1) L of totient (N+r)*2^(L-r) <= C) and q*(C + (N+L+2)) < 2^L -- totient block certificate supply at every precision", "hcert : forall q, 0 < q -> exists N K L C, 2^K divides the packed first-block carry sum ... -- carry-aware totient certificate supply", "hcert : forall q, 0 < q -> exists N K L C, q*((packed carry sum mod 2^K)*2^(L-K) + C + (N+L+2)) < 2^L -- low-carry residue-band totient certificate supply", "hcert : forall q, 0 < q -> exists N K, q*((packed carry sum mod 2^K) + (N+K+2)) < 2^K -- low-carry full-block totient certificate supply"]

- Lean declaration: [irrational_tsum_totient_div_pow_two_of_totient_block_certificates](../../Erdos249257/CertificateKernel.lean#L14766)
- Lean declaration: [irrational_tsum_totient_div_pow_two_of_totient_carry_certificates](../../Erdos249257/CertificateKernel.lean#L14789)
- Lean declaration: [irrational_tsum_totient_div_pow_two_of_totient_low_carry_certificates](../../Erdos249257/CertificateKernel.lean#L15084)
- Lean declaration: [irrational_tsum_totient_div_pow_two_of_totient_low_carry_full_block_certificates](../../Erdos249257/CertificateKernel.lean#L15108)

- outgoing **specialises**: [Z01::carry_aware_certificate_engine](BROWSER_Z01_1.md#node-85bdec04dff8f727). the totient at base 2 is the coefficient instance of the generic carry engine
- outgoing **implies**: [Z01::erdos249_gap_supply_restatement](BROWSER_Z01_1.md#node-31a4afdc8be1ccc1). a low-carry certificate is a gap certificate, so the earlier supply hypotheses are strictly stronger than the later one
- incoming **depends_on_open**: [Z01::totient_carry_field_recurrences](BROWSER_Z01_2.md#node-4d900bc1a4e58804). the recurrences describe the field in which the missing certificate supply would have to be found
- outgoing **depends_on_open**: [Z10::arbitrarily_long_prescribed_omega_blocks](BROWSER_Z10_1.md#node-958b912def239eb0). the divisibility half of the block certificate is producible: this construction gives, for every K, an N with omega(N+r) >= r for r <= K, which with the first-block hinge forces 2^r | phi(N+r). The remaining half - a middle-window budget C with q*(C + (N+L+2)) < 2^L - has no producer anywhere, so the supply stays open.

<a id="node-4653d6568a5b39ff"></a>
## erdos249_cone_nonflat_supply_restatement

If one firing vertex menu exists at arbitrarily large scale then the sum of phi(n)/2^n is irrational. The supply of firing menus is unproved, so this is Erdos #249 restated at the weakest currently available certificate interface.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Open hypotheses: ["hsupply : forall t0, exists t >= t0, exists L, exists Q nonempty with all q positive and (q*periodLcm t + L + 2 : int) < 2^L, TotientTailPeriodKiller.coneNonflatCert (periodLcm t) L Q -- firing menu supply at arbitrarily large scale"]

- Lean declaration: [irrational_totient_series_of_lcm_cone_nonflat_supply](../../Erdos249257/CertificateKernel.lean#L19140)

- outgoing **generalises**: [Z01::erdos249_cone_supply_restatement](BROWSER_Z01_1.md#node-4007efd56b0e194f). the menu refuter's one-sided floors are half the pairwise floors, so its supply hypothesis is weaker
- incoming **implies**: [Z01::cone_nonflat_menu_refuter](BROWSER_Z01_1.md#node-18a57855d478e08e). menu soundness is what converts a firing menu into a non-integral cone pair
- outgoing **equivalent_to**: [Z06::reduction_cone_nonflat_menu_supply](BROWSER_Z06_1.md#node-83d97029da15536b). Shared declaration irrational_totient_series_of_lcm_cone_nonflat_supply; identical firing-menu supply antecedent.
- incoming **finite_instance_of**: [Z06::finite_kill_deposits](BROWSER_Z06_1.md#node-91eeb9cf682bd8dd). the menu refutations at (t,Q,L) = (1,[1,2,3],5), (2,[1,2,3,4],5), (3,[1,2,3],6) are firing vertex menus, the object whose cofinal existence is this restatement's sole hypothesis.
- outgoing **depends_on_open**: [Z06::finite_kill_deposits](BROWSER_Z06_1.md#node-91eeb9cf682bd8dd). the only firing vertex menus in the corpus are the three deposited here at t = 1,2,3; the hypothesis needs one at arbitrarily large t and no node produces menus beyond these.
- outgoing **alias_of**: [Z06::reduction_cone_nonflat_menu_supply](BROWSER_Z06_1.md#node-83d97029da15536b). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18812 `irrational_totient_series_of_lcm_cone_nonflat_supply := TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonflat_supply`; same firing-menu supply hypothesis.

<a id="node-4007efd56b0e194f"></a>
## erdos249_cone_supply_restatement

If one certified annihilator, or one non-integral tail difference, or one rank-two kill exists anywhere on the lcm cone at arbitrarily large scale, then the sum of phi(n)/2^n is irrational. The diagonal, the q-ray steps, the q-gaps and the prime-jump pairs are cells of this one supply statement; the supply is unproved, so these are Erdos #249 restated.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Open hypotheses: ["hsupply : forall t0, exists t >= t0, exists q m L, 0 < q and certifiedKill (m*periodLcm t) (q*periodLcm t) L -- one certified annihilator anywhere on the lcm cone at arbitrarily large scale", "hsupply : forall t0, exists t >= t0, totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t) not in the range of the integers -- diagonal non-integrality supply", "hsupply : forall t0, exists t >= t0, exists L, certifiedKill (periodLcm (t+1) - periodLcm t) (periodLcm t) L -- lcm-jump kill supply"]

- Lean declaration: [irrational_totient_series_of_lcm_cone_window_kill_supply](../../Erdos249257/CertificateKernel.lean#L19014)
- Lean declaration: [irrational_totient_series_of_lcm_diagonal_nonintegrality_supply](../../Erdos249257/CertificateKernel.lean#L19034)
- Lean declaration: [irrational_totient_series_of_lcm_cone_nonintegrality_supply](../../Erdos249257/CertificateKernel.lean#L19046)
- Lean declaration: [irrational_totient_series_of_lcm_qray_rank_two_kill_supply](../../Erdos249257/CertificateKernel.lean#L19067)
- Lean declaration: [irrational_totient_series_of_lcm_jump_window_kill_supply](../../Erdos249257/CertificateKernel.lean#L19152)

- incoming **implies**: [Z01::lcm_cone_flatness_law](BROWSER_Z01_1.md#node-ae87c97d6ef2cef3). cone flatness under rationality is exactly what a single cone annihilator contradicts
- outgoing **generalises**: [Z01::erdos249_period_kill_supply_restatement](BROWSER_Z01_1.md#node-091f2dbf4dfd2e47). the cone supply hypothesis is weaker: one annihilator anywhere on the cone instead of kills along a ray
- incoming **generalises**: [Z01::erdos249_cone_nonflat_supply_restatement](BROWSER_Z01_1.md#node-4653d6568a5b39ff). the menu refuter's one-sided floors are half the pairwise floors, so its supply hypothesis is weaker
- incoming **depends_on_open**: [Z01::lcm_ray_window_structure](BROWSER_Z01_2.md#node-74e2b93b64962549). describes the arithmetic of the ray on which the missing supply would live
- outgoing **equivalent_to**: [Z06::reduction_lcm_cone_supply](BROWSER_Z06_1.md#node-0b5ba2e40a1dd8ec). Shared declarations irrational_totient_series_of_lcm_cone_certificate_supply / _nonintegrality_supply: one cone-annihilator supply obligation stated in two zones.
- incoming **finite_instance_of**: [Z06::finite_kill_deposits](BROWSER_Z06_1.md#node-91eeb9cf682bd8dd). the off-diagonal cone cells (t,q,m) = (2,3,1), (3,2,2), (3,1,3) and the rank-2 kill at (1,8,9) are firing instances of the certified-annihilator and rank-two clauses of this cone supply.
- incoming **finite_instance_of**: [Z05::t_seven_finite_full_target_miss](BROWSER_Z05_2.md#node-7cc8cb692e7c3423). by exact_full_target_pincer a full-target miss at height t is exactly non-integrality of the LCM-diagonal tail difference at t, which is this node's second supply clause ('diagonal non-integrality supply'); the t=7 miss is that clause at one scale.
- outgoing **depends_on_open**: [Z06::finite_kill_deposits](BROWSER_Z06_1.md#node-91eeb9cf682bd8dd). the only realised off-diagonal cone annihilators anywhere are the three cells (2,3,1), (3,2,2), (3,1,3) and the rank-2 kill (1,8,9) deposited here, all at t <= 3; nothing produces cells at arbitrarily large scale.
- outgoing **alias_of**: [Z06::reduction_lcm_cone_supply](BROWSER_Z06_1.md#node-0b5ba2e40a1dd8ec). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18686/18718 re-export `irrational_totient_series_of_lcm_cone_certificate_supply` and `..._of_lcm_cone_nonintegrality_supply`; the two-multiplier cone supply is the same statement.
- outgoing **alias_of**: [Z06::reduction_rank2_qray_supply](BROWSER_Z06_2.md#node-725e8c140eeebb35). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18739 `irrational_totient_series_of_lcm_qray_rank_two_kill_supply := TotientTailPeriodKiller.irrational_totient_series_of_lcm_qray_rank2_supply`; the Z01 node bundles this q-ray cell with the other cone cells.
- outgoing **alias_of**: [Z06::reduction_lcm_jump_supply](BROWSER_Z06_1.md#node-564a2d94fcffaa77). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18824 `irrational_totient_series_of_lcm_jump_window_kill_supply := TotientTailPeriodKiller.irrational_totient_series_of_lcm_jump_kill_supply`; identical lcm-jump supply hypothesis.

<a id="node-31a4afdc8be1ccc1"></a>
## erdos249_gap_supply_restatement

If for every precision q there is a window whose gap inequality holds for the totient carry residue, then the sum of phi(n)/2^n is irrational. This is Erdos #249 restated with the open content in the gap-certificate supply, which is not proved.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Open hypotheses: ["hsupply : forall q, 0 < q -> exists N K, (q*((sum over Icc 1 K of totient (N+r)*2^(K-r)) mod 2^K)) mod 2^K + q*(N+K+2) < 2^K -- gap certificate supply at every precision"]

- Lean declaration: [irrational_tsum_totient_div_pow_two_of_gap_certificate_supply](../../Erdos249257/CertificateKernel.lean#L16025)

- outgoing **specialises**: [Z01::gap_certificate_engine](BROWSER_Z01_1.md#node-d3d303b78be4b97c). the totient gap supply is the fixed-instance form of the generic gap engine
- incoming **implies**: [Z01::erdos249_certificate_supply_restatement](BROWSER_Z01_1.md#node-fe5e91cb1960ad1c). a low-carry certificate is a gap certificate, so the earlier supply hypotheses are strictly stronger than the later one
- incoming **finite_instance_of**: [Z06::gap_denominator_rungs](BROWSER_Z06_1.md#node-36f3f6e03a170c3d). the K=120 and K=240 windows certify the gap inequality for every denominator q up to 2.48e17 and 7.96e34 respectively; the supply asks for a window at EVERY precision q, so the rungs are its bounded-q instance, and the recorded sharpness (the mediant denominator b+d is the first failure) shows those two windows cannot be pushed further.
- outgoing **depends_on_open**: [Z06::gap_denominator_rungs](BROWSER_Z06_1.md#node-36f3f6e03a170c3d). the rungs discharge the gap-certificate supply for all q up to 2.48e17 (K=120) and 7.96e34 (K=240) and are sharp there; beyond those denominators nothing in the corpus produces a window.

<a id="node-091f2dbf4dfd2e47"></a>
## erdos249_period_kill_supply_restatement

If certified period kills exist at arbitrarily large positions -- for every shift, or for one multiple of every shift, or along the single lcm(1..t) family, or standing at the diagonal point N = lcm(1..t) -- then the sum of phi(n)/2^n is irrational. Each weakening shrinks the supply obligation but every one of them is still unproved, so each of these is Erdos #249 restated.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Open hypotheses: ["hsupply : forall h, 0 < h -> forall N0, exists N >= N0, exists L, TotientTailPeriodKiller.certifiedKill h N L -- certified kill supply at every shift and arbitrarily large position", "hsupply : forall h0 > 0, forall N0, exists m > 0, exists N >= N0, exists K, survivorKill (m*h0) N K -- one kill per divisibility ray", "hsupply : forall t0 N0, exists t >= t0, exists N >= N0, exists L, certifiedKill (periodLcm t) N L -- kills along the lcm family", "hsupply : forall t0, exists t >= t0, exists L, certifiedKill (periodLcm t) (periodLcm t) L -- kills at the lcm diagonal point"]

- Lean declaration: [irrational_totient_series_of_period_kill_supply](../../Erdos249257/CertificateKernel.lean#L18792)
- Lean declaration: [irrational_totient_series_of_multiple_period_kill_supply](../../Erdos249257/CertificateKernel.lean#L18851)
- Lean declaration: [irrational_totient_series_of_multiple_window_kill_supply](../../Erdos249257/CertificateKernel.lean#L18858)
- Lean declaration: [irrational_totient_series_of_lcm_period_kill_supply](../../Erdos249257/CertificateKernel.lean#L18866)
- Lean declaration: [irrational_totient_series_of_lcm_window_kill_supply](../../Erdos249257/CertificateKernel.lean#L18913)
- Lean declaration: [irrational_totient_series_of_lcm_diagonal_window_kill_supply](../../Erdos249257/CertificateKernel.lean#L18923)
- Lean declaration: [irrational_totient_series_of_lcm_diagonal_period_kill_supply](../../Erdos249257/CertificateKernel.lean#L18931)

- incoming **implies**: [Z01::totient_tail_shift_and_period_law](BROWSER_Z01_2.md#node-f148b27a710470c2). the tail-period law is what turns a kill supply into irrationality
- incoming **implies**: [Z01::certified_kill_soundness](BROWSER_Z01_1.md#node-ce3a6b8b2b87a632). kill soundness converts each certificate into the non-integrality the period law needs
- incoming **generalises**: [Z01::erdos249_cone_supply_restatement](BROWSER_Z01_1.md#node-4007efd56b0e194f). the cone supply hypothesis is weaker: one annihilator anywhere on the cone instead of kills along a ray
- outgoing **equivalent_to**: [Z06::reduction_pointwise_certificate_supply](BROWSER_Z06_1.md#node-eb9013360d8a36f2). Both nodes carry irrational_totient_series_of_certificate_supply; each is Erdos #249 with the open content moved into the same cofinal certificate-supply hypothesis.
- incoming **finite_instance_of**: [Z06::finite_kill_deposits](BROWSER_Z06_1.md#node-91eeb9cf682bd8dd). the deposited endpoint kills (h<=8 at (12,16), h<=16 at (14,9)), the survivor kill (1,12,7) and the lcm-diagonal kills at t<=8 are instances of three of the four supply forms this restatement quantifies cofinally.
- outgoing **alias_of**: [Z06::reduction_pointwise_certificate_supply](BROWSER_Z06_1.md#node-eb9013360d8a36f2). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18464 `irrational_totient_series_of_period_kill_supply := TotientTailPeriodKiller.irrational_totient_series_of_certificate_supply`; the two nodes carry the same free hypothesis verbatim.
- outgoing **alias_of**: [Z06::reduction_multiple_period_supply](BROWSER_Z06_1.md#node-0818db056d314224). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18523/18530 re-export `irrational_totient_series_of_multiple_survivor_supply` and `..._of_multiple_certificate_supply`; identical one-kill-per-divisibility-ray hypothesis.
- outgoing **alias_of**: [Z06::reduction_lcm_ray_supply](BROWSER_Z06_1.md#node-4d62df0326f8fad7). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18538/18585 re-export `irrational_totient_series_of_lcm_survivor_supply` and `..._of_lcm_certificate_supply`; identical lcm-family supply hypothesis.
- outgoing **alias_of**: [Z06::reduction_lcm_diagonal_supply](BROWSER_Z06_1.md#node-9bc987ebd91ed7a5). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18595/18603 re-export `irrational_totient_series_of_lcm_diagonal_certificate_supply` and `..._survivor_supply`; identical diagonal supply hypothesis.

<a id="node-79ab550ed10b5c4b"></a>
## erdos_borwein_full_support_irrationality

For every integer base b at least 2 the sum over n at least 1 of 1/(b^n - 1) is irrational; at b = 2 this is the irrationality of the Erdos-Borwein constant. The same statement is re-derived through the generic coefficient engine and through the support-series formulation at A = the whole of the naturals.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [irrational_erdosSum_full_support](../../Erdos249257/CertificateKernel.lean#L8328)
- Lean declaration: [irrational_erdosBorwein_series](../../Erdos249257/CertificateKernel.lean#L8335)
- Lean declaration: [irrational_erdosSum_full_support_via_coeff_engine](../../Erdos249257/CertificateKernel.lean#L8689)
- Lean declaration: [irrational_erdosSupportSeries_univ](../../Erdos249257/CertificateKernel.lean#L9045)

- incoming **implies**: [Z01::tau_block_certificate_supply](BROWSER_Z01_2.md#node-78e11eccc7fdd413). certificates at every precision close the full-support theorem unconditionally
- incoming **specialises**: [Z01::multiples_support_irrationality](BROWSER_Z01_2.md#node-879ace93eae03ce4). the multiples support is the full support at base b^d
- incoming **equivalent_to**: [Z12::erdos_borwein_constant_irrational](BROWSER_Z12_1.md#node-e28c693fde9f6a98). irrational_erdosBorweinMersenneConstant is the achievement-set-coordinate name of irrational_erdosSum_full_support / irrational_erdosSupportSeries_univ, tied by erdosSupportSeries_univ_eq_erdosSum_full_support and positiveMersenneSupportValue_eq_erdosSupportSeries.
- incoming **specialises**: [Z12::erdos_borwein_constant_irrational](BROWSER_Z12_1.md#node-e28c693fde9f6a98). `irrational_erdosBorweinMersenneConstant` (GreedyAchievementSet.lean:2433) is `irrational_erdosBorwein_series` (CertificateKernel.lean:8007), which is in turn `irrational_erdosSum_full_support 2`; Z01 states the same conclusion for every integer base b >= 2.

<a id="node-16390fae0f7684fc"></a>
## exact_order_prime_power_witness_supply

For every base b at least 2 and every n at least 2 there exist a prime q and an exponent s such that b has multiplicative order exactly n modulo q^s. Because the interface asks for a prime power rather than a bare prime, the classical Zsigmondy exception pairs need no special treatment; primes dividing the n-th cyclotomic value are lifted by the odd-prime and 2-adic exponent laws.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [exists_exactOrderPrimePowerWitness](../../Erdos249257/CertificateKernel.lean#L4977)
- Lean declaration: [exists_prime_dvd_cyclotomic_eval](../../Erdos249257/CertificateKernel.lean#L4807)
- Lean declaration: [orderOf_isRoot_cyclotomic_zmod_pow_mul](../../Erdos249257/CertificateKernel.lean#L4819)
- Lean declaration: [exactOrderPrimePowerWitness_lift_odd](../../Erdos249257/CertificateKernel.lean#L4864)
- Lean declaration: [exactOrderPrimePowerWitness_lift_two](../../Erdos249257/CertificateKernel.lean#L4932)

- outgoing **implies**: [Z01::canonical_witness_selector_reduction](BROWSER_Z01_1.md#node-9a3634435b900811). the unconditional exact-order supply discharges the selector reduction's only hypothesis
- incoming **implies**: [Z01::lifting_the_exponent_calculus](BROWSER_Z01_2.md#node-2060d63596cd0fe1). the exponent laws are what lift a cyclotomic prime to a prime power of exact order

<a id="node-ed84a74576eddd3a"></a>
## finite_period_noncollapse

For every finite nonempty set F of positive exponents and every integer base b at least 2, the multiplicative order of b modulo the reduced denominator of the finite sum of 1/(b^n - 1) over n in F is exactly the lcm of F. No hypothesis remains: the period of the reduced denominator never collapses below the lcm of the exponents.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [finite_period_noncollapse](../../Erdos249257/CertificateKernel.lean#L5091)
- Lean declaration: [finite_period_noncollapse_concrete](../../Erdos249257/CertificateKernel.lean#L5233)
- Lean declaration: [finite_period_noncollapse_rat_den](../../Erdos249257/CertificateKernel.lean#L5246)
- Lean declaration: [coprime_base_reducedDenominator](../../Erdos249257/CertificateKernel.lean#L5061)

- incoming **implies**: [Z01::period_noncollapse_witness_reduction](BROWSER_Z01_2.md#node-9c0398d7b79861e9). the reduction discharged by the canonical selector and cyclotomic supply is exactly what proves the unconditional theorem
- incoming **finite_instance_of**: [Z01::concrete_period_noncollapse_instances](BROWSER_Z01_1.md#node-779bda153125d283). explicit (b, F) fixtures instantiate the general period non-collapse theorem
- incoming **specialises**: [Z01::denominator_outgrows_lcm](BROWSER_Z01_1.md#node-5af9c6b05c0988ca). the denominator lower bound is read off the exact order equality
- incoming **reformulates**: [Z01::rational_denominator_bridge](BROWSER_Z01_2.md#node-cb8ae7db72537740). identifies the Nat reduced denominator with the Rat denominator of the same partial sum
- incoming **finite_instance_of**: [Z10::support23_period_six_carry_fixture](BROWSER_Z10_2.md#node-a4d7972fa4b13a06). the fixture records reduced denominator 21 for the finite support {2,3} with carry orbit of exact period 6 = lcm{2,3}: the multiplicative order of 2 modulo the reduced denominator equals the lcm of the exponent set, at one finite F.
- incoming **finite_instance_of**: [Z10::dyadic_prefix_fixtures](BROWSER_Z10_1.md#node-e66868b5312099b9). both fixtures instantiate the sharp order statement: order 6 = lcm{2,3} at reduced denominator 21, and order 42 = lcm{2,3,6,7,14} at reduced denominator 344043.

<a id="node-9716dc225759669c"></a>
## finite_prefix_and_rational_prefix_calculus

A support splits at any height cut into a rational finite prefix and a tail support, the two series differ by a rational, and irrationality transfers in both directions; a rational-prefix near-integer composition absorbs the prefix denominator into the precision, which is necessary because no power of b can clear a denominator coprime to b.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [erdosSupportSeries_eq_prefix_add_tail](../../Erdos249257/CertificateKernel.lean#L9422)
- Lean declaration: [irrational_erdosSupportSeries_of_tail](../../Erdos249257/CertificateKernel.lean#L9467)
- Lean declaration: [irrational_erdosSupportSeries_tail_of_irrational](../../Erdos249257/CertificateKernel.lean#L9476)

- outgoing **reformulates**: [Z01::support_coefficient_representation](BROWSER_Z01_2.md#node-950d0bc2e85796ab). splits a support at a height cut into a rational prefix and a tail support

<a id="node-84f534afd83c7e7d"></a>
## full_support_near_int_reduction

Full-support irrationality reduces to near-integer witnesses for the divisor-count series: if for every precision q some power of b times the divisor-count series lies at nonzero distance below 1/q from an integer, then the sum over n of 1/(b^n - 1) is irrational.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [irrational_erdosSum_full_support_of_near_int](../../Erdos249257/CertificateKernel.lean#L6252)

- outgoing **specialises**: [Z01::near_integer_irrationality_criterion](BROWSER_Z01_2.md#node-d00fae1092f3f7c6). applies the near-integer criterion to the divisor-count series through the Lambert identity
- incoming **implies**: [Z01::divisor_block_certificate_engine](BROWSER_Z01_1.md#node-82d682802aaa267c). a block certificate produces exactly the near-integer witness the reduction demands

<a id="node-d3d303b78be4b97c"></a>
## gap_certificate_engine

A gap certificate lands the scaled shifted tail strictly inside some consecutive-integer interval: with W the residue of q times the packed block modulo b^L, the single inequality W + q*(C + N + L + 2) < b^L refutes the rational value a/q. This replaces the bottom-band demand of the low-carry engine by avoiding one thin top band.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [strict_between_int_witness_of_weighted_coeff_gap_certificate](../../Erdos249257/CertificateKernel.lean#L15755)
- Lean declaration: [coeff_series_shifted_ne_int_div_of_gap_certificate](../../Erdos249257/CertificateKernel.lean#L15953)
- Lean declaration: [tsum_totient_div_pow_two_ne_int_div_of_totient_gap_certificate](../../Erdos249257/CertificateKernel.lean#L15986)
- Lean declaration: [tsum_totient_div_pow_two_ne_int_div_of_totient_low_carry_full_block_certificate](../../Erdos249257/CertificateKernel.lean#L15366)

- outgoing **generalises**: [Z01::low_carry_certificate_engine](BROWSER_Z01_2.md#node-f9f70d124b7b25b4). the low-carry certificate is the j = 0 case of the gap certificate
- incoming **reformulates**: [Z01::engine_subsumption_carry_low_carry_gap](BROWSER_Z01_1.md#node-500dc88fa675b8f4). records the machine-checked chain digitwise to carry to low-carry to gap
- incoming **specialises**: [Z01::erdos249_gap_supply_restatement](BROWSER_Z01_1.md#node-31a4afdc8be1ccc1). the totient gap supply is the fixed-instance form of the generic gap engine
- incoming **finite_instance_of**: [Z01::totient_denominator_exclusion_ladder](BROWSER_Z01_2.md#node-ba5ac6fac81df5f1). each rung is the gap engine run at one verified window, giving one bounded denominator range

<a id="node-1e4f5f5eeed01a3b"></a>
## gcd_moment_squared_lambert

The squared Lambert transform is the divisor calculus of the gcd of two independent fair-coin waiting times: the reciprocal Mersenne square series is the sigma-minus-tau coefficient series, the totient-weighted square series is the gcd-moment series, each pair divisibility event has mass 1/(2^d - 1)^2, and the reduced-direction masses over coprime pairs sum to exactly 1. Stern-Brocot cylinder masses converge to the closed form with geometric depth error.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [tsum_inv_mersenne_sq_eq_sigma_sub_tau_series](../../Erdos249257/CertificateKernel.lean#L18636)
- Lean declaration: [tsum_totient_div_mersenne_sq_eq_gcd_moment_series](../../Erdos249257/CertificateKernel.lean#L18646)
- Lean declaration: [tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq](../../Erdos249257/CertificateKernel.lean#L18656)
- Lean declaration: [tsum_visible_coprime_inv_mersenne_eq_one](../../Erdos249257/CertificateKernel.lean#L18666)
- Lean declaration: [stern_brocot_cylinder_mass_error_le](../../Erdos249257/CertificateKernel.lean#L18674)
- Lean declaration: [tendsto_stern_brocot_cylinder_mass](../../Erdos249257/CertificateKernel.lean#L18686)

- outgoing **generalises**: [Z01::visible_lattice_coprimality](BROWSER_Z01_2.md#node-b0d79ae7dbb72785). the squared Lambert transform is the divisor calculus of the gcd of the same two waiting times
- incoming **depends_on_open**: [Z01::stern_brocot_run_geometry](BROWSER_Z01_2.md#node-95bba30642ae44bd). run geometry measures the Fibonacci pressure inside the gcd-moment cylinders without supplying a denominator surplus
- outgoing **reformulates**: [Z07::squared_kernel_totient_rung](BROWSER_Z07_1.md#node-03deb2c00196d21f). Shared declaration tsum_totient_div_mersenne_sq_eq_gcd_moment_series: the totient-weighted squared Lambert transform is the Pillai gcd-sum coefficient series.
- outgoing **reformulates**: [Z07::gcd_divisibility_factorisation](BROWSER_Z07_1.md#node-e13974d93e7d6998). Shared declaration tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq: each pair-divisibility event has base-2 mass 1/(2^d-1)^2, the probabilistic reading of the squared Mersenne reciprocal.
- outgoing **specialises**: [Z07::squared_kernel_zeta_rung](BROWSER_Z07_1.md#node-94b26f9d541d4fcd). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18308 `tsum_inv_mersenne_sq_eq_sigma_sub_tau_series := GcdMomentCalculus.tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series`, the r = 1/2 case of Z07's `tsum_one_lambert_sq_pure`.
- outgoing **specialises**: [Z07::squared_kernel_totient_rung](BROWSER_Z07_1.md#node-03deb2c00196d21f). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18318 `tsum_totient_div_mersenne_sq_eq_gcd_moment_series := GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series`, the r = 1/2 case of Z07's `tsum_totient_lambert_sq_pure`.
- outgoing **alias_of**: [Z07::gcd_divisibility_factorisation](BROWSER_Z07_1.md#node-e13974d93e7d6998). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18328 `tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq := GcdMomentCalculus.tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq`; Z07's node is exactly this single base-2 statement.
- outgoing **alias_of**: [Z07::reduced_direction_law](BROWSER_Z07_1.md#node-5096670b26a83467). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18338 `tsum_visible_coprime_inv_mersenne_eq_one := GcdMomentCalculus.tsum_pos_coprime_inv_mersenne_eq_one`; same base-2 statement, renamed.
- outgoing **alias_of**: [Z07::stern_brocot_cylinder_law](BROWSER_Z07_1.md#node-efa27d01040f40cb). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18346/18358 re-export `GcdMomentCalculus.sternBrocotDepthMass_error` and `tendsto_sternBrocotDepthMass`; Z01 carries two of the four declarations Z07 owns (the mediant split and the child-mass bound stay in Z07).

<a id="node-1e796f279b3072ef"></a>
## generated_gap_window_checkers

An unrolled binary-splitting Bool checker for the gap inequality at the single window (N,K) = (1,120), with per-level soundness lemmas up to recursion depth 22, certifies the gap inequality for every precision q at most 2^22 by ordinary kernel Decidable evaluation with no new axioms; the exact packed carry residues of the windows 1..120 and 1..240 are computed.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [totient_gap_row_window_1_120_sound](../../Erdos249257/CertificateKernel.lean#L16040)
- Lean declaration: [totient_gap_check_window_1_120_pow_22_sound](../../Erdos249257/CertificateKernel.lean#L16375)
- Lean declaration: [totient_carry_residue_window_1_120_eq](../../Erdos249257/CertificateKernel.lean#L17310)
- Lean declaration: [totient_carry_residue_window_1_240_eq](../../Erdos249257/CertificateKernel.lean#L18310)

- outgoing **implies**: [Z01::totient_denominator_exclusion_ladder](BROWSER_Z01_2.md#node-ba5ac6fac81df5f1). the kernel-verified checker run is what discharges the 4194304 rung

<a id="node-347d00f05c4a588d"></a>
## generic_coefficient_certificate_engine

For any natural coefficient sequence with growth envelope c(m) at most m (or at most G times m), block certificates for every precision imply irrationality of the sum of c(m)/b^m; the same engine is stated for the support-coefficient series of an arbitrary support set. The engine is parametric in the coefficient sequence and carries no fixed unproved hypothesis of its own.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Not progress on arbitrary-support #257: instantiating c = supportCoeff A leaves the certificate supply for a general A open.

- Lean declaration: [near_int_witness_of_weighted_coeff_block_certificate](../../Erdos249257/CertificateKernel.lean#L8512)
- Lean declaration: [irrational_coeff_series_of_weighted_coeff_block_certificates](../../Erdos249257/CertificateKernel.lean#L8665)
- Lean declaration: [irrational_coeff_series_of_weighted_coeff_block_certificates_linear](../../Erdos249257/CertificateKernel.lean#L12309)
- Lean declaration: [irrational_erdosSupportSeries_of_weighted_coeff_certificates](../../Erdos249257/CertificateKernel.lean#L9031)

- outgoing **generalises**: [Z01::divisor_block_certificate_engine](BROWSER_Z01_1.md#node-82d682802aaa267c). the same certificate shape stated for an arbitrary coefficient sequence with a growth envelope
- incoming **generalises**: [Z01::carry_aware_certificate_engine](BROWSER_Z01_1.md#node-85bdec04dff8f727). aggregate first-block integrality is strictly weaker than digitwise divisibility
- incoming **implies**: [Z01::periodic_support_irrationality](BROWSER_Z01_2.md#node-c998de19d061f2c2). the periodic orbit sieve supplies the certificates the generic engine consumes
- incoming **implies**: [Z01::pairwise_coprime_support_irrationality](BROWSER_Z01_2.md#node-6cc55d9d294a0368). disjoint coprime blocks supply the certificates for that support class
- incoming **generalises**: [Z01::signed_protected_block_engine](BROWSER_Z01_2.md#node-eed4f03deb5e41b2). extends the certificate interface from natural to integer coefficients via a protected slot
- incoming **barrier_for**: [Z10::no_block_certificate_at_squarefree_support](BROWSER_Z10_2.md#node-8a6ef15977d14203). not_exists_digitwise_certificates_squarefreeSupport: at the squarefree support and every even base b, no tuple (N,K,L,C) satisfies the digitwise weighted-coefficient block schema already at precision q = b^2; that schema is exactly the hypothesis consumed by irrational_coeff_series_of_weighted_coeff_block_certificates / irrational_erdosSupportSeries_of_weighted_coeff_certificates, the evidence of this engine node.
- incoming **barrier_for**: [Z17::n1049_three_halves_barrier](BROWSER_Z17_1.md#node-2f70395be8f6b4ad). The coordinatewise corridor predicate (a^K divides Q*digit, 0 < digit <= N+K, Q*b^(N+K+1) < a^(K+1)) is the rational-base transcription of this engine's three clauses - first-block divisibility, the c(m) <= m growth envelope, and the height inequality. ErdosProblems.Erdos1049.threeHalves_no_coordinatewiseCorridor shows it has no instance at base 3/2 once N >= 1 and K >= 1, via n1049_corridor_power_vs_linear. Scope: only the literal coordinatewise transfer at 3/2; the identification of the corridor with this engine's schema is a reviewed reading of the two Lean shapes, not a proved equivalence.

<a id="node-9f4a9661ab62e636"></a>
## lambert_divisor_identity

The Lambert rearrangement: the sum over n of 1/(b^n - 1) equals the sum over m of tau(m)/b^m, and more generally for a weight bounded between 0 and 1 the weighted Lambert series equals the divisor-weight-sum series. Specialised at b = 2 this is the Erdos-Borwein constant identity.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [erdosSum_full_support_eq_tsum_divisor_count](../../Erdos249257/CertificateKernel.lean#L6193)
- Lean declaration: [erdosBorwein_constant_lambert_identity](../../Erdos249257/CertificateKernel.lean#L6237)
- Lean declaration: [weighted_lambert_series_identity](../../Erdos249257/CertificateKernel.lean#L8807)
- Lean declaration: [tsum_prod_weight_mul_pow_eq_tsum_divisor_weight_sum](../../Erdos249257/CertificateKernel.lean#L8753)

- incoming **reformulates**: [Z01::support_coefficient_representation](BROWSER_Z01_2.md#node-950d0bc2e85796ab). the support series is rewritten as a coefficient series by the same divisor rearrangement

<a id="node-4d6cc8cc64c5cf91"></a>
## lambert_ladder_rational_rungs

Exact evaluations on the Mersenne-Lambert ladder L(f) = sum f(d)/(2^d - 1): L of the Moebius function is 1/2 and L of the totient is 2. These are the rational rungs immediately adjacent to the irrational Erdos-Borwein rung L(1) = E and the open rung L(phi * mu) = S.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [tsum_totient_div_two_pow_sub_one_eq_two](../../Erdos249257/CertificateKernel.lean#L18429)
- Lean declaration: [tsum_moebius_div_two_pow_sub_one_eq_half](../../Erdos249257/CertificateKernel.lean#L18434)

- incoming **reformulates**: [Z01::totient_series_moebius_square_lens](BROWSER_Z01_2.md#node-b089feaf4597b079). places the open constant one Dirichlet convolution from the rational rungs
- incoming **barrier_for**: [Z10::mobius_sign_truncation_overshoots_one_half](BROWSER_Z10_2.md#node-5310e365367dca64). Same sign split applied to the L(mu) = 1/2 rung recorded in this node: the Boolean-support reading of that rung overshoots its own value by at least 1/63 (half_add_one_div_sixty_three_le_tsum_negativeMobius), so the rung is not a route into the Mersenne achievement set.
- outgoing **equivalent_to**: [Z07::lambert_rung_totient_rational](BROWSER_Z07_1.md#node-d6a59f5238058fa9). Shared declaration tsum_totient_div_two_pow_sub_one_eq_two: the rational rung L(phi) = 2.
- outgoing **equivalent_to**: [Z07::lambert_rung_moebius_rational](BROWSER_Z07_1.md#node-76e8be10a56dc445). Shared declaration tsum_moebius_div_two_pow_sub_one_eq_half: the rational rung L(mu) = 1/2.
- outgoing **specialises**: [Z07::lambert_rung_totient_rational](BROWSER_Z07_1.md#node-d6a59f5238058fa9). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18101 `tsum_totient_div_two_pow_sub_one_eq_two := MersenneLambertLadder.tsum_totient_div_two_pow_sub_one_eq_two`, which Z07 owns as the r = 1/2 evaluation of the r-parametric identity `tsum_totient_lambert` (sum phi(d) r^d/(1-r^d) = sum n r^n for 0 <= r < 1).
- outgoing **specialises**: [Z07::lambert_rung_moebius_rational](BROWSER_Z07_1.md#node-76e8be10a56dc445). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18106 `tsum_moebius_div_two_pow_sub_one_eq_half := MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half`, the r = 1/2 case of Z07's r-parametric `tsum_moebius_lambert`.

<a id="node-ae87c97d6ef2cef3"></a>
## lcm_cone_flatness_law

Contrapositive reduction for #249 on the lcm cone: the headline theorem carries the free hypothesis hrat : not Irrational (sum phi(n)/2^n) -- the negation of the open problem, proved nowhere -- and concludes that from some scale on the whole lcm cone {k * lcm(1..t)} is fractionally flat, every difference of totient tails between two cone points being an integer. It transports #249 into the task of exhibiting one non-flat cone pair; on its own it proves nothing unconditional about the constant. Cone scales are nested because lcm(1..t) divides lcm(1..u) for t at most u (that second declaration is unconditional and purely arithmetic).

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The flatness conclusion holds only under the rationality hypothesis. Nothing here shows the cone is or is not flat, and no cone pair is exhibited; the supply side is the separate restatement node erdos249_cone_supply_restatement.

- Lean declaration: [rational_totient_series_forces_lcm_cone_flatness](../../Erdos249257/CertificateKernel.lean#L19002)
- Lean declaration: [period_lcm_dvd_period_lcm_of_le](../../Erdos249257/CertificateKernel.lean#L18995)

- outgoing **implies**: [Z01::erdos249_cone_supply_restatement](BROWSER_Z01_1.md#node-4007efd56b0e194f). cone flatness under rationality is exactly what a single cone annihilator contradicts
- incoming **implies**: [Z01::rationality_forces_tail_period](BROWSER_Z01_2.md#node-06ed6d0b0890515b). the eventual tail period is specialised to the lcm cone to give fractional flatness of the whole cone
- outgoing **equivalent_to**: [Z06::lcm_cone_flatness_law](BROWSER_Z06_1.md#node-2b6c6005924da837). Same theorem rational_totient_series_forces_lcm_cone_flatness, stated at LcmConeFlatness.lean:90 and re-exported at CertificateKernel.lean:18674; the two zones own one statement under one name.
- outgoing **alias_of**: [Z06::lcm_cone_flatness_law](BROWSER_Z06_1.md#node-2b6c6005924da837). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18674 `rational_totient_series_forces_lcm_cone_flatness := TotientTailPeriodKiller.rational_totient_series_forces_lcm_cone_flatness` (owned at LcmConeFlatness.lean:90). The two nodes share the node id and the theorem.
- outgoing **alias_of**: [Z06::lcm_ray_divisibility_skeleton](BROWSER_Z06_1.md#node-190e1b1c4523c82a). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18667 `period_lcm_dvd_period_lcm_of_le := TotientTailPeriodKiller.periodLcm_dvd_periodLcm`; the nesting clause the Z01 node attaches to the flatness law is a component of Z06's divisibility skeleton.

<a id="node-61c9e082f77d5d6b"></a>
## lcm_gap_fails_at_full_support

At the full support a k = k+1 the lcm-gap hypothesis is false: the prefix lcm contains the coprime pair k-1, k, so the truncated gap is eventually zero and does not tend to infinity. The lcm-gap engine therefore provably cannot reach the Erdos-Borwein case.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Rules out only the hypothesis of irrational_erdosSum_of_lcm_gap at the single support a k = k+1. It does not rule out full-support irrationality itself (proved in this module by the near-integer block-certificate engine), does not rule out the lcm-gap criterion at any other support, and says nothing about denominator-based engines that do not go through this particular gap hypothesis.

- Lean declaration: [lcm_gap_hypothesis_fails_full_support](../../Erdos249257/CertificateKernel.lean#L6272)

- outgoing **barrier_for**: [Z01::lcm_gap_irrationality_theorem](BROWSER_Z01_1.md#node-df3ac7a0b39aeae8). shows the gap hypothesis is false at the full support, so this engine cannot reach the Erdos-Borwein case
- incoming **repair_of**: [Z01::divisor_block_certificate_engine](BROWSER_Z01_1.md#node-82d682802aaa267c). the near-integer block-certificate engine is the replacement route to full support that the barrier forces

<a id="node-df3ac7a0b39aeae8"></a>
## lcm_gap_irrationality_theorem

For every base b at least 2 and every strictly increasing exponent sequence starting at 1 or above, if the difference between the k-th exponent and the lcm of the first k exponents tends to infinity then the sum of 1/(b^(a k) - 1) is irrational.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [irrational_erdosSum_of_lcm_gap](../../Erdos249257/CertificateKernel.lean#L5883)

- outgoing **specialises**: [Z01::den_gap_irrationality_criterion](BROWSER_Z01_1.md#node-c94ed0ccee7e7675). the lcm-gap theorem is the denominator-gap criterion applied to partial sums whose denominators are controlled by period non-collapse
- incoming **specialises**: [Z01::lcm_gap_support_instances](BROWSER_Z01_2.md#node-63152823758282cd). factorial and power-of-two supports satisfy the gap hypothesis
- incoming **barrier_for**: [Z01::lcm_gap_fails_at_full_support](BROWSER_Z01_1.md#node-61c9e082f77d5d6b). shows the gap hypothesis is false at the full support, so this engine cannot reach the Erdos-Borwein case

