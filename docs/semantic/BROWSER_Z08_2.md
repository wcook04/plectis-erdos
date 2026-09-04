# Z08_2: First-harmonic spectral lane: window phases, pivot anti-reconstruction and adjacent-window transport

[All problems and zones](BROWSER.md)

<a id="node-19846368535f0b44"></a>
## survivor_kill_forces_adjacent_exit

An existing finite survivor-kill certificate at shifted base N+L, together with dyadic room along the run, forces within K steps either a same-base kill certificate or a boundary non-integrality certificate at some base N+i.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [exists_adjacent_exit_of_survivorKill](../../Erdos249257/AdjacentCarryTube.lean#L390)

- incoming **implies**: [Z08::adjacent_carry_state_is_carry_orbit](BROWSER_Z08_1.md#node-fa7d5cb5f5e3b353). the affine conjugacy lets the existing survivorKill certificate be evaluated on the adjacent carry state

<a id="node-d47ec06f23f8ca12"></a>
## tail_orbit_equals_scaled_series_orbit

The tail difference R_{N+h} − R_N equals the scaled series 2^N(2^h−1)·S minus an explicit integer prefix difference, so the first character of the tail difference is exactly the first character of the scaled series orbit; that orbit is a unit-modulus squaring orbit.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [tail_diff_eq_scaled_totient_series_sub_prefix](../../Erdos249257/PivotAntiReconstruction.lean#L54)
- Lean declaration: [tailOrbitFirstExp_eq_scaledTotientSeriesFirstExp](../../Erdos249257/PivotAntiReconstruction.lean#L66)
- Lean declaration: [tailOrbitFirstExp_succ](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L167)

- outgoing **depends_on_open**: [Z08::squaring_orbit_expansivity](BROWSER_Z08_1.md#node-53f8c8a03ff9e4e5). the scaled series orbit is the squaring orbit to which the expansivity theorem is applied
- outgoing **reformulates**: [Z06::certificate_supply_is_equivalent_to_249](BROWSER_Z06_1.md#node-b7430ca307ffd27e). tail_diff_eq_scaled_totient_series_sub_prefix (PivotAntiReconstruction.lean:54) and tail_diff_mem_int_iff_scaled_series_mem_int (LcmConeFlatness.lean:327) are the same identity R_{N+h}-R_N = 2^N(2^h-1)S - integer prefix.

<a id="node-64fcf02a48defd2c"></a>
## tail_orbit_initial_phase_normal_form

The exact phase recurrence iterates: for every shift h and offsets M,k, tailOrbitFirstExp h (M+k) = (tailOrbitFirstExp h M)^(2^k). The initial phase is the scaled angle of (2^h−1) times the totient series, and phase 1 is equivalent to an integral tail difference. Consequently the cofinal strict-prime gap producer is equivalent to a power-of-two orbit condition on the single initial phase at each shift; non-dyadic initial phase yields only a conditional cofinal nonpositive-phase route.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The initial-phase equivalence supplies no real-part gap and does not prove that the actual totient phase enters a useful region.

- Lean declaration: [TotientTailOrbitCofinalNonpositive](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L412)
- Lean declaration: [totientTailOrbitCofinalNonpositive_of_irrational](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L418)
- Lean declaration: [totientTailOrbitCofinalNonpositive_iff_irrational](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L445)
- Lean declaration: [tailOrbitFirstExp_add](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L191)
- Lean declaration: [tailOrbitFirstExp_eq_initial_pow_two](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L201)
- Lean declaration: [naturalPrimeTailOrbitStrictGap_iff_initial_phase](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L278)
- Lean declaration: [tailOrbitFirstExp_zero_eq_scaled_angle](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L209)
- Lean declaration: [tailOrbitFirstExp_eq_one_iff_tail_diff_mem_int](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L221)
- Lean declaration: [cofinally_tailOrbitFirstExp_re_nonpos_of_not_dyadic](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L360)

- outgoing **reformulates**: [Z08::strict_prime_escape_socket_implies_249](BROWSER_Z08_1.md#node-0b67e31a997e2802). the exact iff rewrites the same strict-prime producer in terms of one initial phase and its power-of-two orbit; no stronger hypothesis or endpoint conclusion is added

<a id="node-a698699f4a2c065f"></a>
## two_mode_variance_bound

Exact two-mode formula for centred fibre variance, V = 2|F| − 2Re W₀ − ‖W₁ − C₁‖²/|F|; and if Re W₀ ≤ (4/5)|F| together with normalised anti-lock ‖(W₁ − C₁)/|F|‖ ≤ 2/5 (implied by ‖W₁‖ ≤ |F|/3 and ‖C₁‖ ≤ |F|/15), then V ≥ (6/25)|F|, strictly above the consumer's |F|/5.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [pivotFiberReconstructionVariance_eq_twoMode](../../Erdos249257/PivotAntiReconstruction.lean#L958)
- Lean declaration: [pivotFiberReconstructionVariance_eq_twoMode_div_card](../../Erdos249257/PivotAntiReconstruction.lean#L976)
- Lean declaration: [pivotFiberReconstructionVariance_ge_six_div_twentyfive_of_twoMode](../../Erdos249257/PivotAntiReconstruction.lean#L990)
- Lean declaration: [pivotFiberReconstructionVariance_ge_six_div_twentyfive_of_modeBounds](../../Erdos249257/PivotAntiReconstruction.lean#L1056)

- incoming **implies**: [Z08::fibre_defect_is_variance_plus_bias](BROWSER_Z08_1.md#node-63758a2aaf803f36). the two-mode variance formula is the defect decomposition rewritten through the two fibre modes
- outgoing **implies**: [Z08::pivot_fibre_socket_implies_249](BROWSER_Z08_1.md#node-e117d433ed5c8c02). the two-mode bound is what makes the two-mode cancellation socket sufficient with 6/25 slack

<a id="node-f9fb77dfb6a1aa1d"></a>
## two_point_chord_separation_forces_certificate

Any two distinct bases in a dyadic block whose first-harmonic phases have squared chord separation at least 19/25 force a certificate at one member of the pair, under the room inequality.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [exists_certifiedKill_of_phasePairSeparation](../../Erdos249257/AdjacentPhaseSeparation.lean#L258)

- outgoing **specialises**: [Z08::first_harmonic_saving_forces_certificate](BROWSER_Z08_1.md#node-31fd9d44a9504048). the two-point chord consumer is the subset consumer applied to the two-element set {N, M}

<a id="node-39d7ceb51308869b"></a>
## window_discrepancy_is_exact_tail_prefix

The finite window discrepancy divided by 2^L is the exact depth-L prefix of the tail difference R_{N+h} − R_N, the only omitted term being the translated tail difference at shifted base N+L, also divided by 2^L.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [tail_diff_eq_windowDiscrepancy_div_add_shifted](../../Erdos249257/AdjacentPhaseSeparation.lean#L170)

- outgoing **implies**: [Z08::adjacent_step_carries_no_new_coordinate](BROWSER_Z08_1.md#node-01364e78810ea848). the adjacent-step identity is the difference of the exact prefix identity at bases N and N+1
- outgoing **implies**: [Z08::finite_window_approximates_tail_orbit](BROWSER_Z08_1.md#node-99a65d7b883357a9). the omitted shifted-tail term in the prefix identity is exactly the rotation between the finite and infinite phases
- outgoing **reformulates**: [Z06::endpoint_certificate_soundness](BROWSER_Z06_1.md#node-552175c811881922). tail_diff_eq_windowDiscrepancy_div_add_shifted (AdjacentPhaseSeparation.lean:54) is the same depth-L split of R_{N+h}-R_N used by windowDiscrepancy_div_eq inside tail_diff_notMem_int_of_certifiedKill.

<a id="node-c5d275f2b251a636"></a>
## window_separated_pairs_equivalent_to_249

The fibre-free counted-separated-pairs socket is logically equivalent to irrationality of the #249 totient series. Both sides are open; the equivalence is a geometric reformulation of the open problem, not progress on it.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["Irrational (∑' n, (φ n)/2^n) — Erdős #249 itself, open"]

- Lean declaration: [dtwWindowSeparatedPairs_iff_irrational_totient_series](../../Erdos249257/PivotAntiReconstruction.lean#L1765)

- incoming **implies**: [Z08::window_separated_pairs_implies_249](BROWSER_Z08_2.md#node-71462c4ebdb6fa9c). the forward direction of the equivalence
- incoming **implies**: [Z08::irrationality_implies_window_separated_pairs](BROWSER_Z08_1.md#node-ccbfc3844e7d9a48). the reverse direction of the equivalence
- outgoing **alias_of**: [Z08::window_separated_pairs_implies_249](BROWSER_Z08_2.md#node-71462c4ebdb6fa9c). the iff packages the conditional endpoint together with its converse; they cite the same mathematical content
- outgoing **equivalent_to**: [Z06::certificate_supply_is_equivalent_to_249](BROWSER_Z06_1.md#node-b7430ca307ffd27e). dtwWindowSeparatedPairs_iff_irrational_totient_series (PivotAntiReconstruction.lean:1744) and irrational_totient_series_iff_certificate_supply (LcmConeFlatness.lean:412) are two proved equivalences with the same right-hand side Irrational (sum phi(n)/2^n).
- outgoing **equivalent_to**: [Z05::exact_full_target_pincer](BROWSER_Z05_1.md#node-faace0186be92bf5). Chaining dtwWindowSeparatedPairs_iff_irrational_totient_series with irrational_totient_series_iff_lcm_diagonal_certificate_supply and periodLcm_diagonal_kill_iff_tail_diff_notMem_int puts the geometric separated-pairs socket and the diagonal full-target predicate on the same open proposition.
- outgoing **alias_of**: [Z06::certificate_supply_is_equivalent_to_249](BROWSER_Z06_1.md#node-b7430ca307ffd27e). `dtwWindowSeparatedPairs_iff_irrational_totient_series` (Z08) and `irrational_totient_series_iff_certificate_supply` (Z06) each prove their socket logically equivalent to Irrational (sum phi n / 2^n), so the two sockets are provably equivalent to each other; both are the open problem in different coordinates, not independent obligations.

<a id="node-71462c4ebdb6fa9c"></a>
## window_separated_pairs_implies_249

A cofinal supply of counted separated pairs of window phases on any nonempty subset of a cofinal dyadic block implies #249 irrationality. Since the converse also holds, the hypothesis is a restatement of the open problem.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["DTWWindowSeparatedPairs: for every h > 0 and X₀ there exist X, L, a nonempty T ⊆ Ico X (2X), a pair set P ⊆ T×T and δ ≥ 0 with common separation δ and mass 2·|T|²/5 ≤ |P|·δ² — proved equivalent to Erdős #249 itself"]

- Lean declaration: [irrational_totient_series_of_windowSeparatedPairs](../../Erdos249257/PivotAntiReconstruction.lean#L1622)

- outgoing **implies**: [Z08::window_separated_pairs_equivalent_to_249](BROWSER_Z08_2.md#node-c5d275f2b251a636). the forward direction of the equivalence
- incoming **barrier_for**: [Z08::irrationality_implies_window_separated_pairs](BROWSER_Z08_1.md#node-ccbfc3844e7d9a48). the reverse implication shows the counted-separated-pairs hypothesis is not a weaker obligation than the conclusion it produces
- incoming **alias_of**: [Z08::window_separated_pairs_equivalent_to_249](BROWSER_Z08_2.md#node-c5d275f2b251a636). the iff packages the conditional endpoint together with its converse; they cite the same mathematical content
- incoming **implies**: [Z08::pivot_fibre_socket_implies_249](BROWSER_Z08_1.md#node-e117d433ed5c8c02). DTWPivotWindowSeparatedPairs forgets to DTWWindowSeparatedPairs, so the fibre socket is at least as strong as the equivalent one
- outgoing **depends_on_open**: [Z06::certificate_supply_is_equivalent_to_249](BROWSER_Z06_1.md#node-b7430ca307ffd27e). the separated-pairs socket is proved equivalent to #249 in its own zone, and this node proves the certificate supply equally equivalent to #249; the antecedent is therefore the open problem itself, not a weaker intermediate, and no producer strictly below #249 can exist.

