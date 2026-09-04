# Z08_1: First-harmonic spectral lane: window phases, pivot anti-reconstruction and adjacent-window transport

[All problems and zones](BROWSER.md)

<a id="node-f8c46b9cc3daa97f"></a>
## adjacent_arc_forces_endpoint_certificate

If the adjacent step residue lies in the robust central arc [2W, 2^L − 2W] with W = N+h+L+2, the endpoint certificate fires at the original base N; and under the room inequality the commonly proposed middle third of the dyadic circle is contained in that robust arc.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [certifiedKill_of_adjacentCertificateArc](../../Erdos249257/AdjacentPhaseSeparation.lean#L103)
- Lean declaration: [adjacentMiddleThird_implies_certificateArc](../../Erdos249257/AdjacentPhaseSeparation.lean#L134)
- Lean declaration: [certifiedKill_of_adjacentMiddleThird](../../Erdos249257/AdjacentPhaseSeparation.lean#L158)

- incoming **implies**: [Z08::adjacent_residue_is_translated_window_residue](BROWSER_Z08_1.md#node-de15b2ac67df78ec). the inverse translation by the endpoint letter is what moves the arc event back to a certificate at base N
- outgoing **implies**: [Z08::adjacent_socket_implies_249](BROWSER_Z08_1.md#node-6e439b49065f8d30). the middle-third socket is consumed through the arc-to-certificate theorem

<a id="node-fa7d5cb5f5e3b353"></a>
## adjacent_carry_state_is_carry_orbit

Across a run of consecutive robust adjacent failures with enough dyadic room, the adjacent carry state obeys c ↦ 2c − deltaTotient and is therefore exactly the existing carryOrbit at shifted base N+L started from the initial adjacent carry state.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [adjacentCarryState_eq_carryOrbit](../../Erdos249257/AdjacentCarryTube.lean#L363)

- incoming **implies**: [Z08::adjacent_failure_trichotomy](BROWSER_Z08_1.md#node-e455996ea274f346). the third branch of the trichotomy is exactly the strict carry box in which the carry recurrence holds
- outgoing **implies**: [Z08::survivor_kill_forces_adjacent_exit](BROWSER_Z08_2.md#node-19846368535f0b44). the affine conjugacy lets the existing survivorKill certificate be evaluated on the adjacent carry state
- outgoing **reformulates**: [Z06::carry_orbit_survivor_soundness](BROWSER_Z06_1.md#node-05d318200f8fe921). adjacentCarryState_eq_carryOrbit identifies the adjacent carry state across a run of robust failures with carryOrbit at shifted base, the exact object of carryOrbit_eq_tail_diff and survivorKill.

<a id="node-e455996ea274f346"></a>
## adjacent_failure_trichotomy

A robust adjacent-arc failure at depth with 4W < 2^L forces at least one of three things (the Lean conclusion is an inclusive disjunction, not an exclusive trichotomy, even though the case split on |adjacentWindowLift| against W is exclusive): the original same-base kill certificate fires; or the tail difference R_{N+h} − R_N is provably not an integer via the boundary-equality case; or the adjacent carry state lies inside the strict candidate box |c| ≤ N+L+h+1 of the existing survivor machinery.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [certifiedKill_of_adjacentWindowLift_abs_gt](../../Erdos249257/AdjacentCarryTube.lean#L257)
- Lean declaration: [tail_diff_notMem_int_of_adjacentWindowLift_abs_eq](../../Erdos249257/AdjacentCarryTube.lean#L279)
- Lean declaration: [adjacentFailure_kill_or_boundaryKill_or_strictCarry](../../Erdos249257/AdjacentCarryTube.lean#L336)

- incoming **implies**: [Z08::canonical_signed_lift_of_adjacent_failure](BROWSER_Z08_1.md#node-5006d415210463ed). the trichotomy is a case split on the size of the signed lift translated to the window coordinate
- outgoing **implies**: [Z08::adjacent_carry_state_is_carry_orbit](BROWSER_Z08_1.md#node-fa7d5cb5f5e3b353). the third branch of the trichotomy is exactly the strict carry box in which the carry recurrence holds

<a id="node-de15b2ac67df78ec"></a>
## adjacent_residue_is_translated_window_residue

Sliding the base by one translates the window residue by exactly the fresh endpoint totient-difference letter, and that translation is exactly invertible: the adjacent step residue and the original window residue determine each other modulo 2^L.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [adjacentStepResidue_eq_translated_windowResidue](../../Erdos249257/AdjacentPhaseSeparation.lean#L74)
- Lean declaration: [windowResidue_eq_adjacentStepResidue_sub_endpoint](../../Erdos249257/AdjacentPhaseSeparation.lean#L89)

- outgoing **implies**: [Z08::adjacent_arc_forces_endpoint_certificate](BROWSER_Z08_1.md#node-f8c46b9cc3daa97f). the inverse translation by the endpoint letter is what moves the arc event back to a certificate at base N
- outgoing **implies**: [Z08::canonical_signed_lift_of_adjacent_failure](BROWSER_Z08_1.md#node-5006d415210463ed). the signed lift is a canonical representative of the translated residue class

<a id="node-6e439b49065f8d30"></a>
## adjacent_socket_implies_249

Two unproved cofinal adjacent-separation hypotheses each imply #249 irrationality: cofinal adjacent middle-third occupancy, and cofinal squared chord separation 19/25 of an adjacent phase pair. Neither is proved.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["DTWAdjacentMiddleThirdSeparation: for every h > 0 and X₀ there exist X, L, N with room and AdjacentMiddleThirdAt h N L, i.e. 2^L ≤ 6·adjacentStepResidue ≤ 5·2^L", "DTWAdjacentPhaseSeparation: for every h > 0 and X₀ there exist X, L, N with room and (19/25) ≤ ‖windowFirstExp h (N+1) L − windowFirstExp h N L‖²"]

- Lean declaration: [irrational_totient_series_of_adjacentMiddleThirdSeparation](../../Erdos249257/AdjacentPhaseSeparation.lean#L283)
- Lean declaration: [irrational_totient_series_of_adjacentPhaseSeparation](../../Erdos249257/AdjacentPhaseSeparation.lean#L295)

- incoming **depends_on_open**: [Z08::adjacent_step_carries_no_new_coordinate](BROWSER_Z08_1.md#node-01364e78810ea848). the adjacent sockets quantify over the same adjacent step whose exact identity and error bound are established here
- incoming **implies**: [Z08::adjacent_arc_forces_endpoint_certificate](BROWSER_Z08_1.md#node-f8c46b9cc3daa97f). the middle-third socket is consumed through the arc-to-certificate theorem

<a id="node-01364e78810ea848"></a>
## adjacent_step_carries_no_new_coordinate

The adjacent window step divided by 2^L equals the current tail difference minus the known endpoint totient letter, plus an error that is a difference of two adjacent tail strips over 2^L and is bounded in absolute value by (2N + 2L + 2h + 5)/2^L.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [adjacent_step_div_eq_tail_diff_add_error](../../Erdos249257/AdjacentPhaseSeparation.lean#L197)
- Lean declaration: [abs_adjacent_step_tail_error_lt](../../Erdos249257/AdjacentPhaseSeparation.lean#L215)

- incoming **implies**: [Z08::window_discrepancy_is_exact_tail_prefix](BROWSER_Z08_2.md#node-39d7ceb51308869b). the adjacent-step identity is the difference of the exact prefix identity at bases N and N+1
- outgoing **depends_on_open**: [Z08::adjacent_socket_implies_249](BROWSER_Z08_1.md#node-6e439b49065f8d30). the adjacent sockets quantify over the same adjacent step whose exact identity and error bound are established here

<a id="node-6333ac02d919248f"></a>
## anchor_defect_equals_first_harmonic_threshold

The anchor defect of a finite base set equals 2|T| − 2·(sum of first-harmonic cosines), equals the sum of squared distances of the phases from the constant phase 1, and the threshold |T|/5 on the defect is exactly, in both directions, the 9/10 first-harmonic threshold on the same set.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [firstHarmonicAnchorDefect_eq](../../Erdos249257/PivotAntiReconstruction.lean#L550)
- Lean declaration: [firstHarmonicAnchorDefect_eq_sum_norm_sq](../../Erdos249257/PivotAntiReconstruction.lean#L562)
- Lean declaration: [firstHarmonicAnchorDefect_ge_iff_first_harmonic_gap](../../Erdos249257/PivotAntiReconstruction.lean#L575)

- outgoing **equivalent_to**: [Z08::first_harmonic_saving_forces_certificate](BROWSER_Z08_1.md#node-31fd9d44a9504048). firstHarmonicAnchorDefect_ge_iff_first_harmonic_gap makes the |T|/5 defect threshold and the 9/10 cosine threshold interderivable on the same finite set
- outgoing **implies**: [Z08::finite_fibre_intake_forces_certificate](BROWSER_Z08_1.md#node-e2ff35a1ebced3c7). each fibre intake condition is reduced to the anchor-defect threshold on the fibre before reaching the consumer

<a id="node-5006d415210463ed"></a>
## canonical_signed_lift_of_adjacent_failure

Failure of the robust adjacent arc selects a canonical short signed representative of the adjacent step residue with absolute value below 2W; under 4W < 2^L that representative is the unique such integer in its residue class.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [adjacentSignedLift_mod](../../Erdos249257/AdjacentCarryTube.lean#L87)
- Lean declaration: [adjacentSignedLift_abs_lt](../../Erdos249257/AdjacentCarryTube.lean#L98)
- Lean declaration: [adjacentSignedLift_exists_unique](../../Erdos249257/AdjacentCarryTube.lean#L114)

- incoming **implies**: [Z08::adjacent_residue_is_translated_window_residue](BROWSER_Z08_1.md#node-de15b2ac67df78ec). the signed lift is a canonical representative of the translated residue class
- outgoing **implies**: [Z08::adjacent_failure_trichotomy](BROWSER_Z08_1.md#node-e455996ea274f346). the trichotomy is a case split on the size of the signed lift translated to the window coordinate

<a id="node-0854ea45144b9464"></a>
## clean_prime_pivot_supplier_fibre

On the canonical largest-prime supplier bases the totient of the pivot argument factors as φ(cofactor)·(p−1), and the canonical cofactor-one fibre at overlap s = L−h is exactly the set of bases N in [X,2X) with N+h+1 prime.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The iff mem_pivotFiber_one_overlap_iff holds only under the side conditions 4 ≤ X and h ≤ L, which the canonical statement above suppresses; outside them the cofactor-one fibre is not asserted to be the shifted-prime set. Both sides of the iff are decidable finite conditions, so this equivalence is not a restatement of any open problem.

- Lean declaration: [totient_pivotArgument_eq_mul](../../Erdos249257/FirstHarmonicPivot.lean#L265)
- Lean declaration: [mem_pivotFiber_one_overlap_iff](../../Erdos249257/FirstHarmonicPivot.lean#L423)

- outgoing **reformulates**: [Z08::point_escape_socket_implies_249](BROWSER_Z08_1.md#node-5b519e8a0024ad61). membership in the canonical cofactor-one fibre is exactly primality of N+h+1, which is what the prime-indexed socket quantifies over

<a id="node-ecd364f1be939956"></a>
## dyadic_root_blocks_strict_prime_gap

If a tail-orbit phase reaches 1, or more generally a dyadic root that reaches 1 under finitely many squarings, the cofinal natural-prime strict-gap producer is impossible for that shift.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The source proves only the barrier implication. It neither finds a dyadic root in the actual totient orbit nor decides Erdős #249.

- Lean declaration: [tailOrbitFirstExp_eq_one_of_le](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L294)
- Lean declaration: [not_naturalPrimeTailOrbitStrictGap_of_phase_one](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L308)
- Lean declaration: [not_naturalPrimeTailOrbitStrictGap_of_dyadic_root](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L322)
- Lean declaration: [exists_tailOrbitFirstExp_zero_pow_two_eq_one_iff_dyadic](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L249)
- Lean declaration: [tailOrbitFirstExp_zero_pow_two_ne_one_upto_sixteen](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L333)

- outgoing **barrier_for**: [Z08::strict_prime_escape_socket_implies_249](BROWSER_Z08_1.md#node-0b67e31a997e2802). an entered absorbing dyadic root contradicts the strict real-part gap required by the producer, while the source leaves actual root entry open

<a id="node-287e448e10ef5542"></a>
## equal_residues_give_equal_phase

Two bases whose window discrepancies agree modulo 2^L have exactly equal first-harmonic phases (and cosines); no choice of integer representative or analytic approximation remains at the call site.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [windowFirstExp_eq_of_discrepancy_emod_eq](../../Erdos249257/PivotAntiReconstruction.lean#L128)
- Lean declaration: [windowFirstCos_eq_of_discrepancy_emod_eq](../../Erdos249257/PivotAntiReconstruction.lean#L138)

- outgoing **depends_on_open**: [Z08::finite_fibre_intake_forces_certificate](BROWSER_Z08_1.md#node-e2ff35a1ebced3c7). residue collisions are the exact lattice interface a separated-pairs producer would have to avoid

<a id="node-76014e1239285452"></a>
## exponential_depth_pays_budgets

For any base and any positive error budget there is a depth, beyond any prescribed threshold, that simultaneously satisfies the certificate room inequality and drives the phase-truncation error below the budget.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [exists_natural_window_depth_with_error](../../Erdos249257/PivotAntiReconstruction.lean#L257)

- outgoing **implies**: [Z08::orbit_gap_transfers_to_window](BROWSER_Z08_1.md#node-579eb72034627f6d). the depth theorem supplies a depth at which the transported error budget is met and the room inequality holds
- outgoing **repair_of**: [Z06::endpoint_certificate_depth_floor](BROWSER_Z06_1.md#node-3ca91ce92ac997b8). certifiedKill_depth_floor forbids only bounded or sub-logarithmic depth, requiring 2(N+h+L+2) < 2^L. exists_natural_window_depth_with_error produces, for any base and any positive error budget and beyond any prescribed threshold, a depth that satisfies the (strictly stronger) certificate room inequality and simultaneously drives the phase-truncation error below the budget, so the floor is met rather than violated.

<a id="node-63758a2aaf803f36"></a>
## fibre_defect_is_variance_plus_bias

The fibre reconstruction defect equals 2|F| − 2·Re(window mode), equals the sum of squared distances of the residuals from the locked reconstruction conj(phase), and equals centred variance plus card times squared bias.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [pivotFiberReconstructionDefect_eq_twoModeAnchor](../../Erdos249257/PivotAntiReconstruction.lean#L885)
- Lean declaration: [pivotFiberReconstructionDefect_eq_sum_residual_norm_sq](../../Erdos249257/PivotAntiReconstruction.lean#L901)
- Lean declaration: [pivotFiberReconstructionDefect_eq_variance_add_bias](../../Erdos249257/PivotAntiReconstruction.lean#L932)

- incoming **generalises**: [Z08::finite_variance_and_pairwise_energy_identities](BROWSER_Z08_1.md#node-c6ca3b05349e818b). the defect decomposition is the generic bias–variance identity instantiated at the reconstruction error
- incoming **implies**: [Z08::reconstruction_error_is_rotated_anchor_error](BROWSER_Z08_1.md#node-1b14635dde7ae03a). the rotation identity is what identifies the residual-anchor distance with the window anchor distance
- outgoing **implies**: [Z08::two_mode_variance_bound](BROWSER_Z08_2.md#node-a698699f4a2c065f). the two-mode variance formula is the defect decomposition rewritten through the two fibre modes

<a id="node-2bf4a02851518e63"></a>
## fibre_variance_equals_pairwise_energy

Centred reconstruction-error energy on a supplier fibre is exactly normalised pairwise energy, so a pairwise-energy bound at 2|F|²/5 gives fibre variance at least |F|/5 with the unknown fibre mean eliminated.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [pivotFiberReconstructionVariance_eq_pairwise](../../Erdos249257/PivotAntiReconstruction.lean#L834)
- Lean declaration: [pivotFiberReconstructionVariance_ge_one_fifth_of_pairwise](../../Erdos249257/PivotAntiReconstruction.lean#L848)

- incoming **generalises**: [Z08::finite_variance_and_pairwise_energy_identities](BROWSER_Z08_1.md#node-c6ca3b05349e818b). the fibre variance identity is the generic pairwise-energy identity instantiated at the reconstruction error

<a id="node-e2ff35a1ebced3c7"></a>
## finite_fibre_intake_forces_certificate

A single supplier fibre supplies a certificate under any of a descending chain of finite intake conditions: anchor defect at least |F|/5; centred variance at least |F|/5; reconstruction-error pairwise energy at least 2|F|²/5; a counted separated-pair set of that mass; the same two conditions for the raw window phases with no pivot weighting.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [exists_certifiedKill_of_pivotFiberReconstructionDefect](../../Erdos249257/PivotAntiReconstruction.lean#L1074)
- Lean declaration: [exists_certifiedKill_of_pivotFiberReconstructionVariance](../../Erdos249257/PivotAntiReconstruction.lean#L1092)
- Lean declaration: [exists_certifiedKill_of_pivotFiberPairwiseEnergy](../../Erdos249257/PivotAntiReconstruction.lean#L1107)
- Lean declaration: [exists_certifiedKill_of_pivotFiberSeparatedPairs](../../Erdos249257/PivotAntiReconstruction.lean#L1125)
- Lean declaration: [pivotFiberReconstructionDefect_ge_one_fifth_of_windowPairwise](../../Erdos249257/PivotAntiReconstruction.lean#L1149)
- Lean declaration: [exists_certifiedKill_of_pivotFiberWindowPairwiseEnergy](../../Erdos249257/PivotAntiReconstruction.lean#L1165)
- Lean declaration: [exists_certifiedKill_of_pivotFiberWindowSeparatedPairs](../../Erdos249257/PivotAntiReconstruction.lean#L1181)

- incoming **implies**: [Z08::anchor_defect_equals_first_harmonic_threshold](BROWSER_Z08_1.md#node-6333ac02d919248f). each fibre intake condition is reduced to the anchor-defect threshold on the fibre before reaching the consumer
- outgoing **implies**: [Z08::pivot_fibre_socket_implies_249](BROWSER_Z08_1.md#node-e117d433ed5c8c02). each cofinal fibre socket is composed with the fibre intake and the certificate-supply reduction
- incoming **depends_on_open**: [Z08::equal_residues_give_equal_phase](BROWSER_Z08_1.md#node-287e448e10ef5542). residue collisions are the exact lattice interface a separated-pairs producer would have to avoid

<a id="node-c6ca3b05349e818b"></a>
## finite_variance_and_pairwise_energy_identities

Standard finite complex identities: sum of squared norms equals centred energy plus card times squared mean; total pairwise energy equals 2·card times centred energy; a counted set of separated ordered pairs lower-bounds pairwise energy by |P|δ²; and pairwise energy at 2|T|²/5 forces squared distance |T|/5 from any fixed anchor.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [sum_norm_sq_eq_centered_add_mean](../../Erdos249257/PivotAntiReconstruction.lean#L617)
- Lean declaration: [sum_pairwise_norm_sq_eq_two_card_mul_centered](../../Erdos249257/PivotAntiReconstruction.lean#L670)
- Lean declaration: [card_mul_sq_le_sum_pairwise_norm_sq_of_separatedPairs](../../Erdos249257/PivotAntiReconstruction.lean#L720)
- Lean declaration: [card_div_five_le_sum_anchor_norm_sq_of_pairwise](../../Erdos249257/PivotAntiReconstruction.lean#L747)

- outgoing **generalises**: [Z08::fibre_variance_equals_pairwise_energy](BROWSER_Z08_1.md#node-2bf4a02851518e63). the fibre variance identity is the generic pairwise-energy identity instantiated at the reconstruction error
- outgoing **generalises**: [Z08::fibre_defect_is_variance_plus_bias](BROWSER_Z08_1.md#node-63758a2aaf803f36). the defect decomposition is the generic bias–variance identity instantiated at the reconstruction error

<a id="node-99a65d7b883357a9"></a>
## finite_window_approximates_tail_orbit

The finite-window phase and the infinite tail-orbit phase differ by an explicit rotation, with ‖windowFirstExp − tailOrbitFirstExp‖ < 2π(N+L+h+2)/2^L.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [tailOrbitFirstExp_eq_window_mul_remainder](../../Erdos249257/PivotAntiReconstruction.lean#L149)
- Lean declaration: [norm_windowFirstExp_sub_tailOrbitFirstExp_le](../../Erdos249257/PivotAntiReconstruction.lean#L174)
- Lean declaration: [norm_windowFirstExp_sub_tailOrbitFirstExp_lt](../../Erdos249257/PivotAntiReconstruction.lean#L202)

- incoming **implies**: [Z08::window_discrepancy_is_exact_tail_prefix](BROWSER_Z08_2.md#node-39d7ceb51308869b). the omitted shifted-tail term in the prefix identity is exactly the rotation between the finite and infinite phases
- outgoing **implies**: [Z08::orbit_gap_transfers_to_window](BROWSER_Z08_1.md#node-579eb72034627f6d). the truncation bound is what converts an orbit real-part gap into a window real-part gap

<a id="node-9c3e30400a8ccd57"></a>
## first_harmonic_character_representation

Writing r for windowDiscrepancy(h,N,L) modulo 2^L, the real and complex first harmonics are exactly windowFirstCos(h,N,L) = cos(2πr/2^L) and windowFirstExp(h,N,L) = exp(i·2πr/2^L). The complex character has real part equal to the real first harmonic and unit norm, and it equals the character of the unreduced integer window discrepancy (reduction mod 2^L is invisible to the character).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [windowFirstCos](../../Erdos249257/FirstHarmonicGap.lean#L27)
- Lean declaration: [windowFirstExp](../../Erdos249257/FirstHarmonicPivot.lean#L38)
- Lean declaration: [windowFirstExp_re](../../Erdos249257/FirstHarmonicPivot.lean#L42)
- Lean declaration: [norm_windowFirstExp](../../Erdos249257/FirstHarmonicPivot.lean#L48)
- Lean declaration: [windowFirstExp_eq_unreduced](../../Erdos249257/PivotAntiReconstruction.lean#L77)

- outgoing **reformulates**: [Z08::first_harmonic_saving_forces_certificate](BROWSER_Z08_1.md#node-31fd9d44a9504048). the complex character has the consumer's real part as its real part and unit norm, so norm savings feed the real-part consumer

<a id="node-31fd9d44a9504048"></a>
## first_harmonic_saving_forces_certificate

If the first harmonic of the window residue has a constant saving on a nonempty finite set T of bases inside a dyadic block [X,2X) — sum of cosines at most (9/10)|T| — and the depth satisfies the room inequality 16(2X+h+L+2) ≤ 2^L, then some N in T carries a kill certificate at depth L. The complex-norm form (norm of the phase sum at most 21X/25) and the anchor-defect form (defect at least |T|/5) are the same statement in different dress.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [exists_certifiedKill_of_first_harmonic_gap_subset](../../Erdos249257/FirstHarmonicGap.lean#L104)
- Lean declaration: [exists_certifiedKill_of_first_harmonic_gap](../../Erdos249257/FirstHarmonicGap.lean#L128)
- Lean declaration: [exists_certifiedKill_of_first_harmonic_norm_gap](../../Erdos249257/FirstHarmonicPivot.lean#L53)
- Lean declaration: [exists_certifiedKill_of_firstHarmonicAnchorDefect](../../Erdos249257/PivotAntiReconstruction.lean#L865)

- incoming **reformulates**: [Z08::first_harmonic_character_representation](BROWSER_Z08_1.md#node-9c3e30400a8ccd57). the complex character has the consumer's real part as its real part and unit norm, so norm savings feed the real-part consumer
- incoming **specialises**: [Z08::two_point_chord_separation_forces_certificate](BROWSER_Z08_2.md#node-f9fb77dfb6a1aa1d). the two-point chord consumer is the subset consumer applied to the two-element set {N, M}
- incoming **equivalent_to**: [Z08::anchor_defect_equals_first_harmonic_threshold](BROWSER_Z08_1.md#node-6333ac02d919248f). firstHarmonicAnchorDefect_ge_iff_first_harmonic_gap makes the |T|/5 defect threshold and the 9/10 cosine threshold interderivable on the same finite set
- incoming **implies**: [Z08::pivot_budget_forces_first_harmonic_gap](BROWSER_Z08_1.md#node-b1a0940bc007776e). the four-term budget yields exactly the 9/10 block gap the consumer takes as hypothesis
- outgoing **implies**: [Z08::first_harmonic_socket_implies_249](BROWSER_Z08_1.md#node-10d76cb364aaef8c). the first-harmonic sockets are composed with the block consumer and the certificate-supply reduction

<a id="node-10d76cb364aaef8c"></a>
## first_harmonic_socket_implies_249

Two unproved cofinal first-harmonic hypotheses each imply irrationality of the #249 totient series: a cofinal complex-norm saving on dyadic blocks, and a cofinal four-term pivot budget. Neither hypothesis is proved anywhere in the corpus.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["DTWFirstHarmonicNormGap: for every h > 0 and every X₀ there exist X ≥ max X₀ 1 and L with room and ‖∑_{N ∈ Ico X (2X)} windowFirstExp h N L‖ ≤ (21/25)·X", "DTWPivotResidualDecorrelation: for every h > 0 there exist an overlap s > 0 and η ∈ (0,1) such that cofinally PivotBudgetAt h X L s η holds, whose binding piece is (pivotCenteredCorrelation h X L s η).re ≤ (14/25)·X"]

- Lean declaration: [irrational_totient_series_of_first_harmonic_norm_gap](../../Erdos249257/FirstHarmonicPivot.lean#L83)
- Lean declaration: [irrational_totient_series_of_pivotResidualDecorrelation](../../Erdos249257/FirstHarmonicPivot.lean#L577)

- incoming **implies**: [Z08::first_harmonic_saving_forces_certificate](BROWSER_Z08_1.md#node-31fd9d44a9504048). the first-harmonic sockets are composed with the block consumer and the certificate-supply reduction

<a id="node-ccbfc3844e7d9a48"></a>
## irrationality_implies_window_separated_pairs

The Lean statement is the implication: irrationality of the #249 series implies the fibre-free counted-separated-pairs socket at every positive shift. It is classed as a barrier rather than as a producer because its antecedent is the target itself: together with the forward consumer in the same file it shows the socket cannot be a strictly weaker intermediate obligation, so proving it is not a partial result short of #249.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: It closes only DTWWindowSeparatedPairs, the shift-uniform fibre-free counted-separated-pairs predicate, and 'closes' means only that the predicate is not a weaker obligation than #249 — not that it is false or useless. Precision point: irrationality DOES supply the fixed-shift predicate DTWWindowSeparatedPairsAt h at every h > 0 (that is literally how this theorem is proved, one shift at a time), so the barrier direction reaches the fixed-shift predicate. What is NOT established for a single shift is the converse: the forward consumer irrational_totient_series_of_windowSeparatedPairs quantifies over every h, so no single DTWWindowSeparatedPairsAt h is shown to imply #249, and it therefore remains a live target — one moreover implied by the weaker hypothesis of non-dyadicity of (2^h−1)·S. No separation is proved, so 'strictly weaker' is not a corpus result. Beyond that the theorem does NOT close: (ii) any pivot-fibre socket (anti-reconstruction, reconstruction variance, pairwise energy, separated pairs, window pairwise energy, window separated pairs), none of which is shown to follow from irrationality; (iii) the natural-prime sockets (window gap, point escape, prime tail-orbit gap, strict prime tail-orbit gap); (iv) the adjacent-separation sockets; (v) the first-harmonic norm-gap and pivot-budget sockets. It also does not say the socket is false or useless — it remains a correct sufficient condition, only not a weaker one.

Open hypotheses: ["Irrational (∑' n, (φ n)/2ⁿ) — the antecedent of this implication is Erdős #249 itself; the theorem is recorded as a barrier on the socket, never as evidence for it"]

- Lean declaration: [windowSeparatedPairs_of_irrational_totient_series](../../Erdos249257/PivotAntiReconstruction.lean#L1755)

- incoming **implies**: [Z08::squaring_orbit_expansivity](BROWSER_Z08_1.md#node-53f8c8a03ff9e4e5). irrationality prevents the scaled orbit from landing at 1, and expansivity then gives the cofinal unit chords the socket needs
- incoming **specialises**: [Z08::nondyadic_scaled_series_gives_fixed_shift_socket](BROWSER_Z08_1.md#node-56f767b53b6de465). the fixed-shift non-dyadic route reaches only DTWWindowSeparatedPairsAt h; the shift-uniform equivalence does not transfer to a single shift because the forward consumer quantifies over every h, so no single-shift equivalence is established
- outgoing **implies**: [Z08::window_separated_pairs_equivalent_to_249](BROWSER_Z08_2.md#node-c5d275f2b251a636). the reverse direction of the equivalence
- outgoing **barrier_for**: [Z08::window_separated_pairs_implies_249](BROWSER_Z08_2.md#node-71462c4ebdb6fa9c). the reverse implication shows the counted-separated-pairs hypothesis is not a weaker obligation than the conclusion it produces

<a id="node-56f767b53b6de465"></a>
## nondyadic_scaled_series_gives_fixed_shift_socket

At a single fixed shift h, if (2^h − 1)·S is not a dyadic rational then the scaled orbit has cofinally many adjacent chords of length at least 1, and hence the fixed-shift fibre-free counted-separated-pairs socket DTWWindowSeparatedPairsAt h holds. Non-dyadicity at one shift is strictly weaker than irrationality of S.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["¬ IsDyadicReal (((2:ℝ)^h − 1) * ∑' n, (φ n)/2^n) at the fixed shift h — no value of h is known for which this is proved"]

- Lean declaration: [cofinally_scaledTotientSeriesFirstExp_adjacent_chord_ge_one_of_not_dyadic](../../Erdos249257/PivotAntiReconstruction.lean#L471)
- Lean declaration: [windowSeparatedPairsAt_of_not_dyadic_scaled_totient_series](../../Erdos249257/PivotAntiReconstruction.lean#L1744)

- incoming **implies**: [Z08::squaring_orbit_expansivity](BROWSER_Z08_1.md#node-53f8c8a03ff9e4e5). non-dyadicity at a fixed shift is exactly the hypothesis that keeps the orbit off 1 at that shift
- outgoing **specialises**: [Z08::irrationality_implies_window_separated_pairs](BROWSER_Z08_1.md#node-ccbfc3844e7d9a48). the fixed-shift non-dyadic route reaches only DTWWindowSeparatedPairsAt h; the shift-uniform equivalence does not transfer to a single shift because the forward consumer quantifies over every h, so no single-shift equivalence is established
- outgoing **depends_on_open**: [Z06::unconditional_denominator_exclusion](BROWSER_Z06_2.md#node-a7dd11b48fa35258). non-dyadicity of (2^h - 1)*S is produced here only at bounded dyadic depth: the exclusion rules out denominators dividing 2^12 (h<=8) and 2^14 (h<=16). No node excludes dyadic denominators of unbounded 2-adic height, so no h is known for which the antecedent holds.

<a id="node-579eb72034627f6d"></a>
## orbit_gap_transfers_to_window

Any real-part gap in the infinite tail orbit survives truncation to depth L with exactly the supplied additive error: if (tailOrbitFirstExp h N).re ≤ a and the truncation budget is at most ε, then windowFirstCos h N L ≤ a + ε; the 4/5 orbit gap with budget 1/10 gives the 9/10 finite gap the consumer wants.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [windowFirstCos_le_add_of_tailOrbitGap](../../Erdos249257/PivotAntiReconstruction.lean#L220)
- Lean declaration: [windowFirstCos_le_nine_tenths_of_tailOrbitGap](../../Erdos249257/PivotAntiReconstruction.lean#L233)

- incoming **implies**: [Z08::finite_window_approximates_tail_orbit](BROWSER_Z08_1.md#node-99a65d7b883357a9). the truncation bound is what converts an orbit real-part gap into a window real-part gap
- incoming **implies**: [Z08::exponential_depth_pays_budgets](BROWSER_Z08_1.md#node-76014e1239285452). the depth theorem supplies a depth at which the transported error budget is met and the room inequality holds
- outgoing **implies**: [Z08::point_escape_socket_implies_249](BROWSER_Z08_1.md#node-5b519e8a0024ad61). the prime tail-orbit gap is transported to a finite window gap and then consumed as a singleton escape

<a id="node-b1a0940bc007776e"></a>
## pivot_budget_forces_first_harmonic_gap

If the four pivot-decomposition terms obey the one-sided budget (centred real part at most 14X/25, and norms at most X/100, X/100 and 8X/25), then the block first-harmonic gap 9/10 holds. The budget arithmetic 14/25 + 1/100 + 1/100 + 8/25 = 9/10 is the whole content.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [first_harmonic_gap_of_pivotBudgetAt](../../Erdos249257/FirstHarmonicPivot.lean#L549)

- outgoing **implies**: [Z08::first_harmonic_saving_forces_certificate](BROWSER_Z08_1.md#node-31fd9d44a9504048). the four-term budget yields exactly the 9/10 block gap the consumer takes as hypothesis
- incoming **depends_on_open**: [Z08::pivot_four_term_decomposition](BROWSER_Z08_1.md#node-77545f21a3adf70d). the budget theorem is stated over the four terms produced by the exact decomposition; no term is estimated

<a id="node-465588952cd95ba8"></a>
## pivot_factorisation_is_exact_division

Any proposed one-dimensional prime pivot phase can be removed from the window phase by exact division, so the window phase is the product of a residual weight and the pivot phase identically. This is a definition-plus-identity, not an independence claim: the residual retains the full coupling.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [windowFirstExp_eq_residual_mul_pivot](../../Erdos249257/FirstHarmonicPivot.lean#L131)
- Lean declaration: [windowFirstExp_eq_pivotResidualAt_mul_phase](../../Erdos249257/FirstHarmonicPivot.lean#L258)

- outgoing **reformulates**: [Z08::pivot_four_term_decomposition](BROWSER_Z08_1.md#node-77545f21a3adf70d). the decomposition is the exact division identity summed over the supplier/non-supplier and good/bad partitions

<a id="node-e117d433ed5c8c02"></a>
## pivot_fibre_socket_implies_249

Eight unproved cofinal pivot-fibre hypotheses each imply irrationality of the #249 totient series, all by composition through the fibre intake and the certificate-supply reduction. None of the hypotheses is proved anywhere in the corpus.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: None of the eight sockets is known to be weaker than #249: each implies it, so proving any one of them is at least as hard as proving #249. One of them is provably no easier than a statement already known to be exactly as hard: windowSeparatedPairs_of_pivotWindowSeparatedPairs (line 1377) sends DTWPivotWindowSeparatedPairs into DTWWindowSeparatedPairs, which dtwWindowSeparatedPairs_iff_irrational_totient_series proves equivalent to #249. These endpoints therefore record where an estimate would have to land, not any reduction in difficulty.

Open hypotheses: ["DTWPivotAntiReconstruction: cofinally, one nonempty supplier fibre has anchor defect at least card/5", "DTWPivotReconstructionVariance: cofinally, centred reconstruction variance at least card/5 on such a fibre", "DTWPivotPairwiseReconstructionEnergy: cofinally, reconstruction-error pairwise energy at least 2·card²/5", "DTWPivotSeparatedPairs: cofinally, a counted separated-pair subset of the fibre square of mass at least 2·card²/5", "DTWPivotWindowPairwiseEnergy: the same at the level of raw window phases", "DTWPivotWindowSeparatedPairs: counted separated pairs of raw window phases", "DTWNaturalPivotWindowGap: cofinally, Re of the window mode on the cofactor-one prime fibre at most (9/10)·card", "DTWNaturalPivotTwoModeCancellation: the same with Re W₀ ≤ (4/5)card together with ‖W₁‖ ≤ card/3 and ‖C₁‖ ≤ card/15"]

- Lean declaration: [irrational_totient_series_of_pivotAntiReconstruction](../../Erdos249257/PivotAntiReconstruction.lean#L1523)
- Lean declaration: [irrational_totient_series_of_naturalPivotWindowGap](../../Erdos249257/PivotAntiReconstruction.lean#L1541)
- Lean declaration: [irrational_totient_series_of_pivotReconstructionVariance](../../Erdos249257/PivotAntiReconstruction.lean#L1582)
- Lean declaration: [irrational_totient_series_of_pivotPairwiseReconstructionEnergy](../../Erdos249257/PivotAntiReconstruction.lean#L1589)
- Lean declaration: [irrational_totient_series_of_pivotSeparatedPairs](../../Erdos249257/PivotAntiReconstruction.lean#L1596)
- Lean declaration: [irrational_totient_series_of_pivotWindowPairwiseEnergy](../../Erdos249257/PivotAntiReconstruction.lean#L1603)
- Lean declaration: [irrational_totient_series_of_pivotWindowSeparatedPairs](../../Erdos249257/PivotAntiReconstruction.lean#L1612)
- Lean declaration: [irrational_totient_series_of_naturalPivotTwoModeCancellation](../../Erdos249257/PivotAntiReconstruction.lean#L1774)

- incoming **implies**: [Z08::finite_fibre_intake_forces_certificate](BROWSER_Z08_1.md#node-e2ff35a1ebced3c7). each cofinal fibre socket is composed with the fibre intake and the certificate-supply reduction
- incoming **implies**: [Z08::two_mode_variance_bound](BROWSER_Z08_2.md#node-a698699f4a2c065f). the two-mode bound is what makes the two-mode cancellation socket sufficient with 6/25 slack
- incoming **reformulates**: [Z08::socket_hierarchy_among_open_producers](BROWSER_Z08_1.md#node-86d63bb3c6dc6521). the endpoint theorems are the socket order composed with the single irrationality consumer
- outgoing **implies**: [Z08::window_separated_pairs_implies_249](BROWSER_Z08_2.md#node-71462c4ebdb6fa9c). DTWPivotWindowSeparatedPairs forgets to DTWWindowSeparatedPairs, so the fibre socket is at least as strong as the equivalent one

<a id="node-77545f21a3adf70d"></a>
## pivot_four_term_decomposition

The block sum of window phases splits exactly into four evaluator-visible terms: centred correlation on good supplier bases, fibre-mean contribution, bad-cofactor contribution, and non-supplier contribution.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [windowFirstExp_sum_eq_pivot_decomposition](../../Erdos249257/FirstHarmonicPivot.lean#L514)

- outgoing **depends_on_open**: [Z08::pivot_budget_forces_first_harmonic_gap](BROWSER_Z08_1.md#node-b1a0940bc007776e). the budget theorem is stated over the four terms produced by the exact decomposition; no term is estimated
- incoming **reformulates**: [Z08::pivot_factorisation_is_exact_division](BROWSER_Z08_1.md#node-465588952cd95ba8). the decomposition is the exact division identity summed over the supplier/non-supplier and good/bad partitions

<a id="node-5b519e8a0024ad61"></a>
## point_escape_socket_implies_249

Two unproved pointwise hypotheses imply #249 irrationality: a cofinal single-base escape below 9/10 inside the canonical shifted-prime fibre, and a cofinal prime-indexed real-part gap at 4/5 in the exact infinite tail orbit. Neither is proved.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["DTWNaturalPivotPointEscape: for every h > 0 and N₀ there exist X, L, N with N ∈ pivotFiber X L (L−h) 1 and windowFirstCos h N L ≤ 9/10", "DTWNaturalPrimeTailOrbitGap: for every h > 0 and N₀ there is a prime p ≥ max (N₀+h+1) (h+5) with (tailOrbitFirstExp h (p−h−1)).re ≤ 4/5"]

- Lean declaration: [irrational_totient_series_of_naturalPivotPointEscape](../../Erdos249257/PivotAntiReconstruction.lean#L1550)
- Lean declaration: [irrational_totient_series_of_naturalPrimeTailOrbitGap](../../Erdos249257/PivotAntiReconstruction.lean#L1574)

- incoming **reformulates**: [Z08::clean_prime_pivot_supplier_fibre](BROWSER_Z08_1.md#node-0854ea45144b9464). membership in the canonical cofactor-one fibre is exactly primality of N+h+1, which is what the prime-indexed socket quantifies over
- incoming **implies**: [Z08::orbit_gap_transfers_to_window](BROWSER_Z08_1.md#node-579eb72034627f6d). the prime tail-orbit gap is transported to a finite window gap and then consumed as a singleton escape
- incoming **generalises**: [Z08::strict_prime_escape_socket_implies_249](BROWSER_Z08_1.md#node-0b67e31a997e2802). the strict 9/10 orbit gap is a weaker hypothesis than the 4/5 gap and reaches the same point-escape socket

<a id="node-1b14635dde7ae03a"></a>
## reconstruction_error_is_rotated_anchor_error

The pivot reconstruction error equals the window anchor error (windowFirstExp − 1) rotated by the conjugate pivot phase, and its fibre sum is exactly the residual-weighted mode minus the bare conjugate-pivot mode. No independence or phase-only surrogate is introduced.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [pivotReconstructionError_eq_conj_phase_mul_window_sub_one](../../Erdos249257/PivotAntiReconstruction.lean#L778)
- Lean declaration: [pivotFiberReconstructionErrorSum_eq_twoMode](../../Erdos249257/PivotAntiReconstruction.lean#L810)

- outgoing **implies**: [Z08::fibre_defect_is_variance_plus_bias](BROWSER_Z08_1.md#node-63758a2aaf803f36). the rotation identity is what identifies the residual-anchor distance with the window anchor distance

<a id="node-86d63bb3c6dc6521"></a>
## socket_hierarchy_among_open_producers

The unproved cofinal producer hypotheses of this lane are ordered by proved implications: counted separated pairs imply pairwise energy imply variance imply anti-reconstruction; raw window separated pairs imply window pairwise energy imply anti-reconstruction and also imply the fibre-free socket; two-mode cancellation implies the natural window gap and the variance socket; and the prime tail-orbit gap implies the natural point escape.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [naturalPivotPointEscape_of_naturalPrimeTailOrbitGap](../../Erdos249257/PivotAntiReconstruction.lean#L1266)
- Lean declaration: [windowSeparatedPairs_of_pivotWindowSeparatedPairs](../../Erdos249257/PivotAntiReconstruction.lean#L1395)
- Lean declaration: [pivotWindowPairwiseEnergy_of_windowSeparatedPairs](../../Erdos249257/PivotAntiReconstruction.lean#L1410)
- Lean declaration: [pivotAntiReconstruction_of_windowPairwiseEnergy](../../Erdos249257/PivotAntiReconstruction.lean#L1423)
- Lean declaration: [pivotPairwiseReconstructionEnergy_of_separatedPairs](../../Erdos249257/PivotAntiReconstruction.lean#L1434)
- Lean declaration: [pivotReconstructionVariance_of_pairwiseEnergy](../../Erdos249257/PivotAntiReconstruction.lean#L1448)
- Lean declaration: [naturalPivotWindowGap_of_naturalPivotTwoModeCancellation](../../Erdos249257/PivotAntiReconstruction.lean#L1460)
- Lean declaration: [pivotAntiReconstruction_of_naturalPivotWindowGap](../../Erdos249257/PivotAntiReconstruction.lean#L1474)
- Lean declaration: [pivotReconstructionVariance_of_naturalPivotTwoModeCancellation](../../Erdos249257/PivotAntiReconstruction.lean#L1491)
- Lean declaration: [pivotAntiReconstruction_of_reconstructionVariance](../../Erdos249257/PivotAntiReconstruction.lean#L1510)

- outgoing **reformulates**: [Z08::pivot_fibre_socket_implies_249](BROWSER_Z08_1.md#node-e117d433ed5c8c02). the endpoint theorems are the socket order composed with the single irrationality consumer

<a id="node-53f8c8a03ff9e4e5"></a>
## squaring_orbit_expansivity

A unit-modulus squaring orbit that never reaches 1 has cofinally many adjacent chords of length at least 1. No equidistribution or measure input is used.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [cofinally_adjacent_chord_ge_one_of_unit_squaring](../../Erdos249257/PivotAntiReconstruction.lean#L335)

- incoming **depends_on_open**: [Z08::tail_orbit_equals_scaled_series_orbit](BROWSER_Z08_2.md#node-d47ec06f23f8ca12). the scaled series orbit is the squaring orbit to which the expansivity theorem is applied
- outgoing **implies**: [Z08::irrationality_implies_window_separated_pairs](BROWSER_Z08_1.md#node-ccbfc3844e7d9a48). irrationality prevents the scaled orbit from landing at 1, and expansivity then gives the cofinal unit chords the socket needs
- outgoing **implies**: [Z08::nondyadic_scaled_series_gives_fixed_shift_socket](BROWSER_Z08_1.md#node-56f767b53b6de465). non-dyadicity at a fixed shift is exactly the hypothesis that keeps the orbit off 1 at that shift

<a id="node-0b67e31a997e2802"></a>
## strict_prime_escape_socket_implies_249

The problem-owned refinement: a cofinal prime-indexed strict gap Re < 9/10 in the exact infinite tail orbit — weaker than the legacy 4/5 socket — already supplies the finite singleton escape by choosing the truncation budget adaptively from the strict slack, hence implies #249 irrationality.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The producer DTWNaturalPrimeTailOrbitStrictGap is unproved: no prime p is known for which (tailOrbitFirstExp h (p−h−1)).re < 9/10 is established, at any h. Calling it the weakest live producer is a statement about hypothesis strength within this lane only; it is not evidence that it is attainable.

Open hypotheses: ["DTWNaturalPrimeTailOrbitStrictGap: for every h > 0 and N₀ there is a prime p ≥ max (N₀+h+1) (h+5) with (tailOrbitFirstExp h (p−h−1)).re < 9/10"]

- Lean declaration: [naturalPivotPointEscape_of_naturalPrimeTailOrbitStrictGap](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L485)
- Lean declaration: [irrational_totient_series_of_naturalPrimeTailOrbitStrictGap](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L524)
- Lean declaration: [naturalPrimeTailOrbitStrictGap_of_cofinal_nonpositive_prime_shift](../../ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean#L465)

- outgoing **generalises**: [Z08::point_escape_socket_implies_249](BROWSER_Z08_1.md#node-5b519e8a0024ad61). the strict 9/10 orbit gap is a weaker hypothesis than the 4/5 gap and reaches the same point-escape socket
- incoming **reformulates**: [Z08::tail_orbit_initial_phase_normal_form](BROWSER_Z08_2.md#node-64fcf02a48defd2c). the exact iff rewrites the same strict-prime producer in terms of one initial phase and its power-of-two orbit; no stronger hypothesis or endpoint conclusion is added
- incoming **barrier_for**: [Z08::dyadic_root_blocks_strict_prime_gap](BROWSER_Z08_1.md#node-ecd364f1be939956). an entered absorbing dyadic root contradicts the strict real-part gap required by the producer, while the source leaves actual root entry open

