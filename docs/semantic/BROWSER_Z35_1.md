# Z35_1: Cyclotomic anchors, filtered carry collapse, and full-Mersenne claim ceilings

[All problems and zones](BROWSER.md)

<a id="node-43bd0b7f22f9cfdc"></a>
## anchored_kill_and_guard_cylinder_supplies_are_exact_claim_ceiling

EXACT ANCHORED CLAIM CEILING: the guard-cylinder normal form and the arbitrary-depth cyclotomic anchored-kill supply are equivalent. Either supply implies irrationality; clean anchors plus irrationality repopulate it, and for the concrete binary cyclotomic layers both formulations are exactly Erdős #249.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Unconditional prime production is already discharged, but no cofinal guard or anchored-kill supply is established. Therefore #249 remains open.

Open hypotheses: ["terminal anti-locking of the actual totient word at cofinally many clean binary cyclotomic anchors"]

- Lean declaration: [cyclotomicGuardCylinderSupply_iff_anchoredKillSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3259)
- Lean declaration: [irrational_totient_series_of_cyclotomicAnchoredKillSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3282)
- Lean declaration: [cyclotomicAnchoredKillSupply_of_irrational_of_cleanAnchorSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3299)
- Lean declaration: [cyclotomicAnchoredKillSupply_iff_irrational_of_cleanAnchorSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3316)
- Lean declaration: [binaryCyclotomicAnchoredKillSupply_iff_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3327)
- Lean declaration: [irrational_totient_series_of_cyclotomicGuardCylinderSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3336)
- Lean declaration: [binaryCyclotomicGuardCylinderSupply_iff_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3345)

- outgoing **reformulates**: [Z35::cyclotomic_four_and_one_state_supplies_are_exact_claim_ceiling](BROWSER_Z35_1.md#node-8468b9a5d3b068fe). The terminal guard-cylinder socket is another exact finite normal form of the certified anchored kill at the same clean cyclotomic provenance.
- outgoing **generated_by**: [Z35::eventual_period_integrality_propagates_to_multiples](BROWSER_Z35_1.md#node-7c186fdbd5de546c). The irrationality consumer defeats a hypothetical eventual period h using a certified discrepancy at an anchored multiple hq.
- incoming **barrier_for**: [Z35::period_30_certificates_exclude_fixed_denominator_family](BROWSER_Z35_1.md#node-2c30d9f57118609a). Two fixed certified anchors and one denominator exclusion do not satisfy the cofinal clean-anchor quantifier in the claim-ceiling supply.

<a id="node-fc0e1de4482bad8d"></a>
## binary_cyclotomic_layers_supply_clean_cofinal_anchors

PROVED UNCONDITIONAL CLEAN ANCHORS: |Phi_n(2)| divides 2^n-1, and a prime divisor p of a positive binary cyclotomic layer has n=p^a ord_p(2). The refactored clean-order theorem excludes the characteristic-prime cases past q>max(h,2^h); the resulting layer-supply and eventual degree-one order consumers give, for every h>0 and threshold N0, a prime q and clean prime divisor p of |Phi_(hq)(2)| with p coprime to hq, exact order hq, hq dividing p-1, and p-1>=N0. The concrete binary layers therefore satisfy CleanCyclotomicAnchorSupply and UnboundedPrimeDivisorSupply.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This completely supplies anchor provenance and unbounded prime support, but not the cofinal terminal carry kill attached to those anchors. It is the concrete X-2 specialization of the conditional prime-ray interfaces in Z73; neither route proves a tail discrepancy, cofinal certificate supply, or irrationality of the binary totient series.

- Lean declaration: [binaryCyclotomicLayer_dvd_mersenneLayer](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1416)
- Lean declaration: [binaryCyclotomicLayer_prime_order_decomposition](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1431)
- Lean declaration: [two_ne_zero_of_prime_dvd_binaryCyclotomicLayer](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1460)
- Lean declaration: [prime_dvd_binaryCyclotomicLayer_clean_order](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1501)
- Lean declaration: [exists_clean_binaryCyclotomicAnchor](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1607)
- Lean declaration: [binaryCyclotomicLayer_layerSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1650)
- Lean declaration: [binaryCyclotomicLayer_eventualOrderConsumer](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1676)
- Lean declaration: [binaryCyclotomicLayer_unboundedPrimeDivisorSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1693)
- Lean declaration: [cleanCyclotomicAnchorSupply_binaryCyclotomicLayer](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1773)

- outgoing **generalises**: [Z35::prime_index_mersenne_layers_have_unbounded_prime_support](BROWSER_Z35_1.md#node-7f17832c3632cf20). The composite-index binary cyclotomic theorem replaces the prime-index Mersenne layer by |Phi_(hq)(2)| and additionally eliminates the characteristic-prime case to obtain exact clean order hq.
- incoming **depends_on_open**: [Z35::cyclotomic_and_basepoint_filter_supplies_are_exact_claim_ceiling](BROWSER_Z35_1.md#node-0bc4da8da25bd984). Clean anchors are unconditional, but the terminal filtered-kill field attached to cofinally many of them is precisely the unresolved side of the equivalence.

<a id="node-19adbd143738f6c5"></a>
## clean_prime_filter_has_four_candidate_normal_form

PROVED FOUR-STATE CLASSIFICATION: at a clean anchor with H<=p-1, every denominator-compatible launch in the analytic initial interval is one of r-2p, r-p, r, or r+p for the canonical residue r. All four representatives lie in the forced class, and after three carry steps their locked subset has cardinality at most one.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The reduction replaces O(p) launches by four and then at most one; it does not kill the surviving state or provide cofinally many usable anchors.

- Lean declaration: [primeFiltered_candidate_eq_one_of_four](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L338)
- Lean declaration: [primeFourCarryCandidate_modEq_residue](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L400)
- Lean declaration: [primeFourCarry_survivor_at_three_unique](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L420)
- Lean declaration: [primeFourCarryLockedThrough_three_card_le_one](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L523)

- outgoing **specialises**: [Z35::filtered_carry_spacing_collapses_to_one_survivor](BROWSER_Z35_1.md#node-f3c9ce845e60725f). The four-state classification applies the general modular spacing theorem at clean prime modulus p and depth three.
- incoming **generated_by**: [Z35::four_state_and_single_locked_kills_are_equivalent](BROWSER_Z35_1.md#node-2ec6e51da49797e5). The lossless one-state reduction is possible because the explicit four-state set has at most one member locked through depth three.

<a id="node-a7564c2497ea7510"></a>
## cleared_totient_block_controls_tail_and_residue_orbit

PROVED EXACT BLOCK DYNAMICS: (2^H-1)R_N is the integer block Q_(H,N) plus R_(N+H)-R_N; sliding N advances Q by the same affine recurrence as the carry modulo the exact multiple (2^H-1)phi(N+1). Consequently a carry initially congruent to -Q modulo any divisor p of 2^H-1 remains congruent to the shifted negative block at every depth.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The residue orbit is a consumer interface. It neither makes the true tail difference integral nor supplies a modulus or an escaping carry.

- Lean declaration: [mersenne_mul_tail_eq_block_add_diff](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L119)
- Lean declaration: [totientBlock_succ](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L151)
- Lean declaration: [carryOrbit_modEq_neg_totientBlock_shift](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L169)

- incoming **generated_by**: [Z35::scaled_tail_forces_prime_or_full_mersenne_residue](BROWSER_Z35_1.md#node-58c7ed139b6ff7c1). The denominator filter is obtained by combining integrality with the exact identity (2^H-1)R_N=Q plus the H-step tail difference.

<a id="node-0bc4da8da25bd984"></a>
## cyclotomic_and_basepoint_filter_supplies_are_exact_claim_ceiling

EXACT CLAIM-CEILING FAMILY: the cofinal residue-filtered, literal four-state, and one-locked-state cyclotomic supplies are mutually lossless; they feed the free-basepoint supply and each closes irrationality. Under clean Mersenne-dividing anchors irrationality reconstructs the filtered certificates, so for the concrete binary layers—and for the basepoint-decoupled supply—these predicates are each equivalent to Erdős #249.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: No cofinal kill supply is proved independently. Equivalence to Irrational S must not be read as a solution of #249.

Open hypotheses: ["the truth of any equivalent cofinal terminal-kill supply remains exactly the unresolved irrationality of the binary totient series"]

- Lean declaration: [primeBasepointSingleLockedCarryKillSupply_iff_filtered](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1854)
- Lean declaration: [cyclotomicPrimeFourCarryKillSupply_iff_filtered](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1879)
- Lean declaration: [cyclotomicPrimeSingleLockedCarryKillSupply_iff_four](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1904)
- Lean declaration: [primeBasepointFilteredCarryKillSupply_of_cyclotomicFiltered](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1927)
- Lean declaration: [irrational_totient_series_of_primeBasepointFilteredCarryKillSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1946)
- Lean declaration: [irrational_totient_series_of_cyclotomicPrimeFilteredCarryKillSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2018)
- Lean declaration: [cyclotomicPrimeFilteredCarryKillSupply_of_irrational_of_cleanAnchorSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2089)
- Lean declaration: [cyclotomicPrimeFilteredCarryKillSupply_iff_irrational_of_cleanAnchorSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2113)
- Lean declaration: [binaryCyclotomicPrimeFilteredCarryKillSupply_iff_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2126)
- Lean declaration: [primeBasepointFilteredCarryKillSupply_iff_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2136)

- outgoing **depends_on_open**: [Z35::binary_cyclotomic_layers_supply_clean_cofinal_anchors](BROWSER_Z35_1.md#node-fc0e1de4482bad8d). Clean anchors are unconditional, but the terminal filtered-kill field attached to cofinally many of them is precisely the unresolved side of the equivalence.
- outgoing **generated_by**: [Z35::free_basepoint_search_is_sound_and_pointwise_complete](BROWSER_Z35_1.md#node-e9e1c46dddc766d3). Pointwise soundness and completeness lift to the cofinal supply equivalence once clean anchors and denominator clearing are composed.
- incoming **reformulates**: [Z35::cyclotomic_four_and_one_state_supplies_are_exact_claim_ceiling](BROWSER_Z35_1.md#node-8468b9a5d3b068fe). The literal four-state and one-state supplies are lossless finite normal forms of the same filtered cofinal predicate.

<a id="node-8468b9a5d3b068fe"></a>
## cyclotomic_four_and_one_state_supplies_are_exact_claim_ceiling

EXACT FINITE-STATE CLAIM CEILING: cyclotomic four-state supply implies irrationality; with clean Mersenne-dividing anchors it is equivalent to irrationality. For the concrete binary cyclotomic layers both the literal four-state supply and the one-locked-state supply are exactly Erdős #249.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The at-most-one state reduction is unconditional locally; its eventual escape at cofinally many anchors is exactly the unresolved content.

Open hypotheses: ["no cofinal four-state or single-locked-state kill supply is proved independently for the binary cyclotomic layers"]

- Lean declaration: [irrational_totient_series_of_cyclotomicPrimeFourCarryKillSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3185)
- Lean declaration: [cyclotomicPrimeFourCarryKillSupply_iff_irrational_of_cleanAnchorSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3194)
- Lean declaration: [binaryCyclotomicPrimeFourCarryKillSupply_iff_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3206)
- Lean declaration: [binaryCyclotomicPrimeSingleLockedCarryKillSupply_iff_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3217)

- outgoing **reformulates**: [Z35::cyclotomic_and_basepoint_filter_supplies_are_exact_claim_ceiling](BROWSER_Z35_1.md#node-0bc4da8da25bd984). The literal four-state and one-state supplies are lossless finite normal forms of the same filtered cofinal predicate.
- incoming **reformulates**: [Z35::anchored_kill_and_guard_cylinder_supplies_are_exact_claim_ceiling](BROWSER_Z35_1.md#node-43bd0b7f22f9cfdc). The terminal guard-cylinder socket is another exact finite normal form of the certified anchored kill at the same clean cyclotomic provenance.

<a id="node-8785b2c2b9ff5ed7"></a>
## edge_lock_rigidity_transports_carry_escape_to_centered_gap

PROVED FINITE ESCAPE TRANSPORT: if a sufficiently large Mersenne divisor has no central gap at two adjacent basepoints, centered lifts obey the literal affine recurrence; over an edge-locked interval they equal the ordinary carry orbit. Therefore one carry escape, a survivorKill, or a certifiedKill forces a genuine centered full-Mersenne gap at or before the checked depth.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Each theorem is finite and requires explicit large-modulus room. It does not supply cofinally many compatible H,N,M or solve #249.

- Lean declaration: [fullMersenneBlockCenteredLift_succ_eq_of_two_edge_locks](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2496)
- Lean declaration: [fullMersenneBlockCenteredLift_add_eq_carryOrbit_of_edge_locks](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2556)
- Lean declaration: [exists_fullMersenneCenteredResidueGap_of_carryOrbit_escape](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2586)
- Lean declaration: [exists_fullMersenneCenteredResidueGap_of_survivorKill](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2614)
- Lean declaration: [survivorKill_of_certifiedKill](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2685)
- Lean declaration: [exists_fullMersenneCenteredResidueGap_of_certifiedKill](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2715)

- outgoing **generated_by**: [Z35::full_mersenne_centered_residue_has_exact_modular_dynamics](BROWSER_Z35_1.md#node-f370025a965d7459). Two-edge and interval rigidity iterate the centered modular recurrence after large-modulus room removes every wrap.
- incoming **finite_instance_of**: [Z35::period_30_certificates_exclude_fixed_denominator_family](BROWSER_Z35_1.md#node-2c30d9f57118609a). The two period-30 certified kills are fixed finite inputs accepted by the general certificate-to-full-Mersenne-gap transport.

<a id="node-7c186fdbd5de546c"></a>
## eventual_period_integrality_propagates_to_multiples

PROVED PERIOD TRANSPORT: if R_(N+h)-R_N is integral at every sufficiently late N, then R_(N+hk)-R_N is integral for every k and every such N by telescoping k adjacent h-step differences.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The lemma propagates a supplied eventual integrality law; it neither proves such a law nor proves its negation.

- Lean declaration: [tail_diff_int_of_period_mul](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1735)

- incoming **generated_by**: [Z35::anchored_kill_and_guard_cylinder_supplies_are_exact_claim_ceiling](BROWSER_Z35_1.md#node-43bd0b7f22f9cfdc). The irrationality consumer defeats a hypothetical eventual period h using a certified discrepancy at an anchored multiple hq.

<a id="node-f3c9ce845e60725f"></a>
## filtered_carry_spacing_collapses_to_one_survivor

PROVED PRODUCT-MODULUS SPACING: two launches in one class modulo M differ at carry depth K by a multiple of 2^K M, so a strip of radius below 2^(K-1)M contains at most one survivor. At a clean prime basepoint N<p with H<=p-1, depth three already forces uniqueness.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Uniqueness says at most one candidate survives. It does not show that the remaining candidate escapes.

- Lean declaration: [primeBasepointFiltered_survivor_at_three_unique](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L209)
- Lean declaration: [modulusFiltered_survivor_unique](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L250)

- incoming **specialises**: [Z35::clean_prime_filter_has_four_candidate_normal_form](BROWSER_Z35_1.md#node-19adbd143738f6c5). The four-state classification applies the general modular spacing theorem at clean prime modulus p and depth three.
- incoming **generalises**: [Z35::free_basepoint_filter_collapses_to_single_locked_state](BROWSER_Z35_1.md#node-c5710d29d2587797). The basepoint-decoupled construction uses the same modulus-spacing mechanism with N independent of the filtering modulus.

<a id="node-2ec6e51da49797e5"></a>
## four_state_and_single_locked_kills_are_equivalent

PROVED FINITE CERTIFICATE EQUIVALENCE: a four-state kill is exactly emptiness of the locked-through set and is monotone in depth. From depth three onward it is equivalent to killing only the at-most-one locked state, and under clean prime geometry it is exactly the original residue-filtered carry-kill predicate.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Equivalence of finite search encodings does not establish any certificate, let alone a cofinal supply.

- Lean declaration: [primeFourCarryKill_iff_lockedThrough_eq_empty](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L492)
- Lean declaration: [primeFourCarryKill_mono](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L551)
- Lean declaration: [primeSingleLockedCarryKill_of_primeFourCarryKill](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L563)
- Lean declaration: [primeFourCarryKill_of_primeSingleLockedCarryKill](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L575)
- Lean declaration: [primeSingleLockedCarryKill_iff_primeFourCarryKill](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L604)
- Lean declaration: [primeFourCarryKill_iff_primeFilteredCarryKill](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L613)

- outgoing **generated_by**: [Z35::clean_prime_filter_has_four_candidate_normal_form](BROWSER_Z35_1.md#node-19adbd143738f6c5). The lossless one-state reduction is possible because the explicit four-state set has at most one member locked through depth three.
- incoming **complements**: [Z35::prime_filtered_search_is_sound_and_pointwise_complete](BROWSER_Z35_1.md#node-a462fab98f52fc8d). Finite predicate equivalence compresses the search, while soundness/completeness identifies what success or failure means for one fixed true tail difference.

<a id="node-c5710d29d2587797"></a>
## free_basepoint_filter_collapses_to_single_locked_state

PROVED BASEPOINT-DECOUPLED NORMAL FORM: at an arbitrary basepoint the filtered launch set has at most one three-step survivor under clean prime geometry, and also under a composite modulus wider than the analytic radius. Filtered and single-locked certificates are depth-monotone and equivalent from depth three onward; setting N=p-1 recovers the original prime-predecessor predicate.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Basepoint freedom permits a later arithmetic construction but supplies neither the modulus nor terminal escape.

- Lean declaration: [primeBasepointFilteredLockedThrough_three_card_le_one](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L824)
- Lean declaration: [modulusFilteredLockedThrough_three_card_le_one](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L846)
- Lean declaration: [primeBasepointFilteredCarryKill_mono](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L888)
- Lean declaration: [primeBasepointSingleLockedCarryKill_of_filtered](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L900)
- Lean declaration: [primeBasepointFilteredCarryKill_of_singleLocked](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L912)
- Lean declaration: [primeBasepointSingleLockedCarryKill_iff_filtered](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L944)
- Lean declaration: [primeBasepointFilteredCarryKill_pred_iff](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L954)

- outgoing **generalises**: [Z35::filtered_carry_spacing_collapses_to_one_survivor](BROWSER_Z35_1.md#node-f3c9ce845e60725f). The basepoint-decoupled construction uses the same modulus-spacing mechanism with N independent of the filtering modulus.
- incoming **reformulates**: [Z35::full_mersenne_single_locked_supply_is_exact_claim_ceiling](BROWSER_Z35_1.md#node-22ff80f6222cce44). Its finite residual is exactly the composite-modulus free-basepoint predicate after the quotient is made wider than the analytic radius.

<a id="node-e9e1c46dddc766d3"></a>
## free_basepoint_search_is_sound_and_pointwise_complete

PROVED FREE-BASEPOINT SEARCH CHARACTERISATION: a filtered kill plus the correct block congruence excludes integrality of the true H-step tail difference at any N; conversely, nonintegrality of that fixed difference yields some finite filtered-kill depth.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem is local in H,N,p. It does not prove any global supply or the required congruence from rationality.

- Lean declaration: [tail_diff_notMem_int_of_primeBasepointFilteredCarryKill](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L972)
- Lean declaration: [exists_primeBasepointFilteredCarryKill_of_tail_diff_notMem_int](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1029)

- outgoing **generalises**: [Z35::prime_filtered_search_is_sound_and_pointwise_complete](BROWSER_Z35_1.md#node-a462fab98f52fc8d). The same pointwise search semantics hold at arbitrary N; N=p-1 recovers the prime-predecessor version.
- incoming **complements**: [Z35::scaled_tail_forces_prime_or_full_mersenne_residue](BROWSER_Z35_1.md#node-58c7ed139b6ff7c1). The filter supplies the congruence hypothesis needed by the sound free-basepoint kill consumer.
- incoming **generated_by**: [Z35::cyclotomic_and_basepoint_filter_supplies_are_exact_claim_ceiling](BROWSER_Z35_1.md#node-0bc4da8da25bd984). Pointwise soundness and completeness lift to the cofinal supply equivalence once clean anchors and denominator clearing are composed.

<a id="node-19e78fc3b6a9fd73"></a>
## full_mersenne_candidate_is_near_integer_and_gap_excludes_it

PROVED FULL-QUOTIENT GEOMETRY: a launch in the full-Mersenne residue class forces vR_N within 2(N+H+2)/M of an integer. Every noninteger real has a positive lattice gap, so once this error is smaller no launch exists. Irrationality makes all positive integer scalings of shifted tails nonintegral, while a rational value with denominator 2^c v makes vR_N integral for every N>=c.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The forward near-integer implication alone proves nothing. The global conclusions below remain equivalent reformulations of the unknown irrationality statement.

- Lean declaration: [scaled_tail_near_int_of_mersenne_factor_candidate](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1170)
- Lean declaration: [exists_uniform_int_gap_of_notMem_int](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1248)
- Lean declaration: [no_mersenne_factor_candidate_of_scaled_tail_gap](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1287)
- Lean declaration: [scaled_totientTail_notMem_int_of_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1312)
- Lean declaration: [exists_int_scaled_tail_of_rat_den_eq](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1335)

- outgoing **specialises**: [Z35::scaled_tail_forces_prime_or_full_mersenne_residue](BROWSER_Z35_1.md#node-58c7ed139b6ff7c1). Retaining the exact quotient M turns one compatible residue-class launch into a quantitative near-integer approximation to vR_N.
- incoming **generated_by**: [Z35::full_mersenne_single_locked_supply_is_exact_claim_ceiling](BROWSER_Z35_1.md#node-22ff80f6222cce44). The full-quotient supply uses the scaled-tail lattice gap and exponential quotient growth to collapse the entire initial launch set.

<a id="node-f370025a965d7459"></a>
## full_mersenne_centered_residue_has_exact_modular_dynamics

PROVED CENTERED-RESIDUE DYNAMICS: modulo any M dividing 2^H-1, the block residue doubles and subtracts the next delta-totient letter when N advances. The canonical signed lift represents the same class; if the two signed sides fit inside one modulus, the modular recurrence is literal equality. With sufficient room, central-arc escape is exactly the centered lift exceeding the analytic radius.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The recurrence describes the residue orbit. It does not prove central escape at any cofinal family of heights.

- Lean declaration: [fullMersenneBlockResidue_succ](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2322)
- Lean declaration: [fullMersenneBlockCenteredLift_emod](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2366)
- Lean declaration: [fullMersenneBlockCenteredLift_succ_modEq](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2378)
- Lean declaration: [fullMersenneBlockCenteredLift_succ_eq_of_abs_add_abs_lt](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2423)
- Lean declaration: [fullMersenneCenteredResidueGap_iff_abs_centeredLift](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2456)

- incoming **generated_by**: [Z35::edge_lock_rigidity_transports_carry_escape_to_centered_gap](BROWSER_Z35_1.md#node-8785b2c2b9ff5ed7). Two-edge and interval rigidity iterate the centered modular recurrence after large-modulus room removes every wrap.
- incoming **reformulates**: [Z35::initial_and_centered_gap_are_same_zero_launch_condition](BROWSER_Z35_1.md#node-d3aee3a7d9b72d6a). The initial no-launch predicate is the Euclidean representative form of the same central-arc gap encoded by the centered lift.

<a id="node-4ae8e13de62b666b"></a>
## full_mersenne_gap_supplies_are_exact_claim_ceiling

EXACT ARITHMETIC CLAIM CEILING: irrationality supplies a full-Mersenne initial gap at every prescribed basepoint and hence cofinally; conversely such gaps exclude every rational denominator. Initial-gap and centered-residue supplies are equivalent to #249, and the basepoint may be fixed canonically at the dyadic denominator exponent c without loss.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: No theorem here proves the centered residue gap without assuming irrationality or an equivalent supply. This is a reformulation of #249, not its resolution.

Open hypotheses: ["the cofinal centered residue gap is itself exactly the unresolved irrationality statement, not an independently supplied theorem"]

- Lean declaration: [exists_fullMersenneInitialResidueGap_at_of_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2948)
- Lean declaration: [fullMersenneInitialResidueGapSupply_of_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3034)
- Lean declaration: [irrational_totient_series_of_fullMersenneInitialResidueGapSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3049)
- Lean declaration: [fullMersenneInitialResidueGapSupply_iff_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3108)
- Lean declaration: [fullMersenneCenteredResidueGapSupply_iff_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3122)
- Lean declaration: [fullMersenneCenteredResidueGapSupply_of_canonicalBasepoint](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3132)
- Lean declaration: [fullMersenneCanonicalBasepointResidueGapSupply_of_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3143)
- Lean declaration: [fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3165)
- Lean declaration: [primeBasepointSingleLockedCarryKillSupply_iff_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3178)

- outgoing **generated_by**: [Z35::initial_and_centered_gap_are_same_zero_launch_condition](BROWSER_Z35_1.md#node-d3aee3a7d9b72d6a). The supply equivalences lift the exact finite initial/centered normal form through every prospective denominator.
- outgoing **reformulates**: [Z35::full_mersenne_single_locked_supply_is_exact_claim_ceiling](BROWSER_Z35_1.md#node-22ff80f6222cce44). The zero-launch centered gap removes even the one locked state, yielding a sharper but still equivalent arithmetic claim ceiling.

<a id="node-22ff80f6222cce44"></a>
## full_mersenne_single_locked_supply_is_exact_claim_ceiling

EXACT FULL-QUOTIENT CLAIM CEILING: for every prospective dyadic preperiod c and positive odd denominator part v, the supply of a remote Euler-multiple H whose quotient M=(2^H-1)/v is wider than the initial radius and whose sole three-step survivor eventually escapes is equivalent to irrationality of the binary totient series.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The reverse theorem starts from irrationality. The equivalence therefore identifies the residual but contributes no unconditional cofinal escape.

Open hypotheses: ["FullMersenneSingleLockedCarryKillSupply is not proved independently of assuming irrationality"]

- Lean declaration: [fullMersenneSingleLockedCarryKillSupply_of_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2168)
- Lean declaration: [irrational_totient_series_of_fullMersenneSingleLockedCarryKillSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2235)
- Lean declaration: [fullMersenneSingleLockedCarryKillSupply_iff_irrational](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2292)

- outgoing **generated_by**: [Z35::full_mersenne_candidate_is_near_integer_and_gap_excludes_it](BROWSER_Z35_1.md#node-19e78fc3b6a9fd73). The full-quotient supply uses the scaled-tail lattice gap and exponential quotient growth to collapse the entire initial launch set.
- outgoing **reformulates**: [Z35::free_basepoint_filter_collapses_to_single_locked_state](BROWSER_Z35_1.md#node-c5710d29d2587797). Its finite residual is exactly the composite-modulus free-basepoint predicate after the quotient is made wider than the analytic radius.
- incoming **reformulates**: [Z35::full_mersenne_gap_supplies_are_exact_claim_ceiling](BROWSER_Z35_1.md#node-4ae8e13de62b666b). The zero-launch centered gap removes even the one locked state, yielding a sharper but still equivalent arithmetic claim ceiling.

<a id="node-d3aee3a7d9b72d6a"></a>
## initial_and_centered_gap_are_same_zero_launch_condition

PROVED ZERO-LAUNCH NORMAL FORM: for positive modulus M, absence of every representative of the forced block class in the initial interval [-B,B] is equivalent to the least nonnegative residue lying in the central open arc. Every positive-height factorisation vM=2^H-1 has M>0, so the equivalence applies to the intended full quotient.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This identifies two finite predicates. It does not prove that either gap occurs.

- Lean declaration: [fullMersenneInitialResidueGap_iff_centered](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2741)
- Lean declaration: [mersenne_factor_modulus_pos](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L2823)

- outgoing **reformulates**: [Z35::full_mersenne_centered_residue_has_exact_modular_dynamics](BROWSER_Z35_1.md#node-f370025a965d7459). The initial no-launch predicate is the Euclidean representative form of the same central-arc gap encoded by the centered lift.
- incoming **generated_by**: [Z35::full_mersenne_gap_supplies_are_exact_claim_ceiling](BROWSER_Z35_1.md#node-4ae8e13de62b666b). The supply equivalences lift the exact finite initial/centered normal form through every prospective denominator.

<a id="node-2c30d9f57118609a"></a>
## period_30_certificates_exclude_fixed_denominator_family

PROVED FINITE CERTIFICATES: at H=30 the kernel checks certified kills at the natural basepoint N=300 with depth 13 and the prime anchor N=330 with depth 10; the deeper natural window has exact depth-16 residue 2928 modulo 2^16. The natural certificate proves that the binary totient series equals no rational whose denominator divides 2^300(2^30-1).

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The result excludes one explicit denominator-divisor family only. It is not evidence for the cofinal supply and does not prove irrationality.

- Lean declaration: [certifiedKill_cyclotomic_30_331_natural](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3356)
- Lean declaration: [certifiedKill_cyclotomic_30_331_anchor](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3363)
- Lean declaration: [windowDiscrepancy_30_300_16_mod](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3370)
- Lean declaration: [totient_series_ne_rat_of_den_dvd_30_300](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L3377)

- outgoing **finite_instance_of**: [Z35::edge_lock_rigidity_transports_carry_escape_to_centered_gap](BROWSER_Z35_1.md#node-8785b2c2b9ff5ed7). The two period-30 certified kills are fixed finite inputs accepted by the general certificate-to-full-Mersenne-gap transport.
- outgoing **barrier_for**: [Z35::anchored_kill_and_guard_cylinder_supplies_are_exact_claim_ceiling](BROWSER_Z35_1.md#node-43bd0b7f22f9cfdc). Two fixed certified anchors and one denominator exclusion do not satisfy the cofinal clean-anchor quantifier in the claim-ceiling supply.

<a id="node-a462fab98f52fc8d"></a>
## prime_filtered_search_is_sound_and_pointwise_complete

PROVED POINTWISE SEARCH CHARACTERISATION: assuming the denominator filter for an integral tail difference, a finite prime-filtered kill proves that difference nonintegral. Conversely, nonintegrality of the fixed tail difference implies that some uniform finite depth kills every candidate in the finite filtered interval.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Completeness is pointwise after nonintegrality is assumed. It does not prove nonintegrality at any new height or a cofinal supply.

- Lean declaration: [tail_diff_notMem_int_of_primeFilteredCarryKill](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L661)
- Lean declaration: [exists_primeFilteredCarryKill_of_tail_diff_notMem_int](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L719)

- outgoing **complements**: [Z35::four_state_and_single_locked_kills_are_equivalent](BROWSER_Z35_1.md#node-2ec6e51da49797e5). Finite predicate equivalence compresses the search, while soundness/completeness identifies what success or failure means for one fixed true tail difference.
- incoming **generalises**: [Z35::free_basepoint_search_is_sound_and_pointwise_complete](BROWSER_Z35_1.md#node-e9e1c46dddc766d3). The same pointwise search semantics hold at arbitrary N; N=p-1 recovers the prime-predecessor version.

<a id="node-7f17832c3632cf20"></a>
## prime_index_mersenne_layers_have_unbounded_prime_support

PROVED UNCONDITIONAL SUPPORT: if q and p are prime and p divides 2^q-1, then the order of 2 modulo p is q and q divides p-1. The exact X-2 layer therefore satisfies the degree-one order consumer and clean layer-supply hypotheses, yielding prime divisors beyond every size bound at arbitrarily remote prime indices.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: Unbounded prime support supplies clean arithmetic anchors only. It proves no tail discrepancy, carry kill, cofinal certificate supply, or irrationality of the binary totient series.

- Lean declaration: [prime_index_dvd_pred](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L33)
- Lean declaration: [mersenneLayer_orderConsumer](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L76)
- Lean declaration: [mersenneLayer_layerSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L84)
- Lean declaration: [mersenneLayer_unboundedPrimeDivisorSupply](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L105)

- incoming **generalises**: [Z35::binary_cyclotomic_layers_supply_clean_cofinal_anchors](BROWSER_Z35_1.md#node-fc0e1de4482bad8d). The composite-index binary cyclotomic theorem replaces the prime-index Mersenne layer by |Phi_(hq)(2)| and additionally eliminates the characteristic-prime case to obtain exact clean order hq.

<a id="node-58c7ed139b6ff7c1"></a>
## scaled_tail_forces_prime_or_full_mersenne_residue

PROVED DENOMINATOR FILTER: if vR_N and the H-step tail difference are integers, then a prime p coprime to v dividing 2^H-1 forces the difference into -Q_(H,N) modulo p. More strongly, an exact factorisation vM=2^H-1 forces the same class modulo the full quotient M without a primality hypothesis.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The filter is conditional on integrality of the scaled tail and the tail difference. It does not assert rationality or produce a contradiction without a kill or gap.

- Lean declaration: [tail_diff_modEq_neg_totientBlock_of_scaled_tail](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1075)
- Lean declaration: [tail_diff_modEq_neg_totientBlock_of_scaled_tail_factor](../../ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean#L1123)

- outgoing **generated_by**: [Z35::cleared_totient_block_controls_tail_and_residue_orbit](BROWSER_Z35_1.md#node-a7564c2497ea7510). The denominator filter is obtained by combining integrality with the exact identity (2^H-1)R_N=Q plus the H-step tail difference.
- outgoing **complements**: [Z35::free_basepoint_search_is_sound_and_pointwise_complete](BROWSER_Z35_1.md#node-e9e1c46dddc766d3). The filter supplies the congruence hypothesis needed by the sound free-basepoint kill consumer.
- incoming **specialises**: [Z35::full_mersenne_candidate_is_near_integer_and_gap_excludes_it](BROWSER_Z35_1.md#node-19e78fc3b6a9fd73). Retaining the exact quotient M turns one compatible residue-class launch into a quantitative near-integer approximation to vR_N.

