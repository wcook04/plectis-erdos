# Z06_2: Tail-period killer and the lcm cone: waves 20-25 of the #249 reduction chain (plus the Farey-gap and unit-gap side lanes)

[All problems and zones](BROWSER.md)

<a id="node-725e8c140eeebb35"></a>
## reduction_rank2_qray_supply

Certified second-difference kills along the q-rays of the lcm cone, at arbitrarily large scale, imply irrationality, because cone flatness forces both first differences integral.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : forall t0, exists t, t0 <= t and exists q L, 0 < q and certifiedRank2Kill (periodLcm t) (q * periodLcm t) L"]

- Lean declaration: [irrational_totient_series_of_lcm_qray_rank2_supply](../../Erdos249257/LcmConeFlatness.lean#L587)

- outgoing **depends_on_open**: [Z06::lcm_cone_flatness_law](BROWSER_Z06_1.md#node-2b6c6005924da837). Rank-2 supply is sound only because flatness forces both first differences integral on q-rays.
- outgoing **depends_on_open**: [Z01::engine_strength_separations](BROWSER_Z01_1.md#node-8f3c278e1c645ebc). the only rank-two second-difference certificate exhibited anywhere is the single fixture cell recorded in this separation node (and its twin among the Z06 deposits); one cell does not produce a q-ray supply at arbitrarily large scale.
- incoming **alias_of**: [Z01::erdos249_cone_supply_restatement](BROWSER_Z01_1.md#node-4007efd56b0e194f). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18739 `irrational_totient_series_of_lcm_qray_rank_two_kill_supply := TotientTailPeriodKiller.irrational_totient_series_of_lcm_qray_rank2_supply`; the Z01 node bundles this q-ray cell with the other cone cells.

<a id="node-f7cede0c08a3a33d"></a>
## reduction_unit_gap_supply_projection

Any all-denominator reduced-denominator unit-gap supply would in particular produce, for every odd prime power and every threshold, a window whose certified interval contains at most one candidate.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : PrimitiveReducedDenominatorUnitGapSupply, i.e. forall a u, 0 < u -> Odd u -> exists N K, a <= N and 0 < K and ReducedDenominatorUnitGapCert u N K"]

- Lean declaration: [primitiveReducedDenominatorUnitGapSupply_prime_power_projection](../../Erdos249257/PrimitiveWeightCertificate.lean#L127)

- incoming **barrier_for**: [Z06::unit_gap_prime_power_ceiling](BROWSER_Z06_2.md#node-8a53e82f59607500). Any unit-gap supply must solve a zero-or-one-candidate problem at every odd prime power.

<a id="node-0cce8442c93a2c03"></a>
## shift_identity_totient_tail

Two-to-the-N times the #249 constant splits exactly as an integer prefix plus the local totient tail: 2^N * sum_n phi(n)/2^n = Phi_N + R_N, where Phi_N is a finite integer sum and R_N = sum_{m>=1} phi(N+m)/2^m converges.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [two_pow_mul_totient_series_eq](../../Erdos249257/TotientTailPeriodKiller.lean#L150)
- Lean declaration: [totientTail](../../Erdos249257/TotientTailPeriodKiller.lean#L57)
- Lean declaration: [totientPrefix](../../Erdos249257/TotientTailPeriodKiller.lean#L61)

- incoming **depends_on_open**: [Z06::tail_period_law_from_rationality](BROWSER_Z06_2.md#node-2b462b01c608150a). The period law is read off the prefix/tail split of 2^N S; no open input, but it is the transport step that makes R_N the target.
- incoming **reformulates**: [Z01::totient_tail_shift_and_period_law](BROWSER_Z01_2.md#node-f148b27a710470c2). two_pow_mul_totient_series_eq_prefix_add_tail and two_pow_mul_totient_series_eq are the same prefix/tail split 2^N S = Phi_N + R_N, and totient_tail_carry_recurrence is totientTail_succ.
- incoming **alias_of**: [Z01::totient_tail_shift_and_period_law](BROWSER_Z01_2.md#node-f148b27a710470c2). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18438 `two_pow_mul_totient_series_eq_prefix_add_tail := TotientTailPeriodKiller.two_pow_mul_totient_series_eq`; same identity 2^N*S = Phi_N + R_N. The Z01 node bundles this with two further re-exports, edged separately.

<a id="node-10099dc166b2a256"></a>
## sparse_pulse_countermodel_construction

The sparse pulse c_k = -A on a finite anchor set and 0 elsewhere, with letters a_i = 2 c_i - c_{i+1}, satisfies the affine binary recurrence by construction, has every letter in the ideal (A), has |c| <= |A| and |a| <= 2|A|, and at the lcm anchor set (q-1)H for 2 <= q < t with A = phi(H) it reproduces every exact whole-ray totient anchor letter phi(H).

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Carries NO arithmetic content about the #249 objects. sparsePulseState/sparsePulseLetter are hand-written definitions (a two-case 'if k in S then -A else 0') and the accompanying proofs are structural one-liners (ring, simp, split); the only #249-facing input is that at the lcm anchor set the letters happen to equal the true whole-ray anchor differences phi(H). Its entire mathematical value is as substrate for the barrier node barrier_finite_rank_shift_algebra, so it is classified infrastructure. Adversarial-review note (2026-07-25): reclassified from generated_certificate_instance, which was wrong - nothing here is machine-generated certificate data. That class is correctly used elsewhere in this zone only by gap_denominator_rungs, whose Farey-neighbour constants are search output.

- Lean declaration: [sparsePulse_recurrence](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L54)
- Lean declaration: [sparsePulse_dvd_letter](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L74)
- Lean declaration: [lcmAnchorPulseLetter_eq](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L559)
- Lean declaration: [lcmAnchorStates](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L427)

- incoming **depends_on_open**: [Z06::barrier_finite_rank_shift_algebra](BROWSER_Z06_1.md#node-9f93e6afd7e89d02). The countermodel is the engine of the no-go.

<a id="node-2b462b01c608150a"></a>
## tail_period_law_from_rationality

If the #249 constant equals a rational r whose denominator divides 2^N (2^h - 1) then R_{N+h} - R_N is an integer; hence if the constant is not irrational there exist h >= 1 and N0 such that every shifted tail difference at period h from N0 on is an integer. This converts irrationality of the series into non-integrality of some shifted tail difference.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [tail_diff_int_of_den_dvd](../../Erdos249257/TotientTailPeriodKiller.lean#L327)
- Lean declaration: [eventual_period_of_not_irrational](../../Erdos249257/TotientTailPeriodKiller.lean#L358)

- outgoing **depends_on_open**: [Z06::shift_identity_totient_tail](BROWSER_Z06_2.md#node-0cce8442c93a2c03). The period law is read off the prefix/tail split of 2^N S; no open input, but it is the transport step that makes R_N the target.
- incoming **equivalent_to**: [Z01::rationality_forces_tail_period](BROWSER_Z01_2.md#node-06ed6d0b0890515b). rational_totient_series_forces_eventual_tail_period and eventual_period_of_not_irrational are the same contrapositive reduction: non-irrationality forces an eventual integral shifted tail difference.
- incoming **transport_of**: [Z17::n251_euler_odd_denominator](BROWSER_Z17_1.md#node-1f1777114f52b839). ratIntegral_totientMultiplier_of_odd_den supplies the period phi(d) from the odd part of the reduced denominator, the same Euler-order mechanism that tail_diff_int_of_den_dvd uses to convert rationality into an integral shifted tail difference.
- incoming **alias_of**: [Z01::rationality_forces_tail_period](BROWSER_Z01_2.md#node-06ed6d0b0890515b). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18455 `rational_totient_series_forces_eventual_tail_period := TotientTailPeriodKiller.eventual_period_of_not_irrational`; identical hypothesis (not Irrational S) and conclusion.

<a id="node-1bb6df87e4fcba59"></a>
## tail_strip_and_carry_recurrence

The local totient tail satisfies 0 < R_M <= M + 2 and the exact carry recurrence R_{M+1} = 2 R_M - phi(M+1); consequently every shifted tail difference is trapped in the open strip |R_{N+h} - R_N| < N + h + 2, and at any depth L the difference equals a signed increment prefix plus 2^{-L} times the translated difference.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [totientTail_succ](../../Erdos249257/CarrySurvivorExtinction.lean#L94)
- Lean declaration: [abs_tail_diff_lt](../../Erdos249257/CarrySurvivorExtinction.lean#L79)
- Lean declaration: [tail_diff_eq_increment_prefix_add_shifted](../../Erdos249257/CarrySurvivorExtinction.lean#L354)
- Lean declaration: [totientTail_eq_partial_add_shifted](../../Erdos249257/CarrySurvivorExtinction.lean#L120)

- incoming **depends_on_open**: [Z06::endpoint_certificate_soundness](BROWSER_Z06_1.md#node-552175c811881922). Soundness uses the one-sided deep-tail bound derived from phi(n) <= n.
- incoming **alias_of**: [Z01::totient_tail_shift_and_period_law](BROWSER_Z01_2.md#node-f148b27a710470c2). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18497 `totient_tail_carry_recurrence := TotientTailPeriodKiller.totientTail_succ`; identical carry recurrence R_{M+1} = 2R_M - phi(M+1). Z06 additionally owns the strip bound.

<a id="node-a7dd11b48fa35258"></a>
## unconditional_denominator_exclusion

The #249 constant equals no rational whose denominator divides 2^12 (2^h - 1) for some 1 <= h <= 8, and no rational whose denominator divides 2^14 (2^h - 1) for some 1 <= h <= 16. Equivalently: no dyadic rational with denominator up to 2^14, and no k/(2^a m) with a <= 14 and the multiplicative order of 2 mod m at most 16.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [totient_series_ne_rat_of_den_dvd](../../Erdos249257/TotientTailPeriodKiller.lean#L416)
- Lean declaration: [totient_series_ne_rat_of_den_dvd_upto_sixteen](../../Erdos249257/CarrySurvivorExtinction.lean#L587)

- outgoing **finite_instance_of**: [Z06::finite_kill_deposits](BROWSER_Z06_1.md#node-91eeb9cf682bd8dd). The two exclusions are exactly the kernel-decided certificate blocks fed through the tail-period law.
- incoming **equivalent_to**: [Z01::totient_series_rational_exclusions_from_kills](BROWSER_Z01_2.md#node-4bdd060dc42777bf). Shared declarations totient_series_ne_rat_of_den_dvd and totient_series_ne_rat_of_den_dvd_upto_sixteen: the same two unconditional denominator exclusions at (N,h) = (12, <=8) and (14, <=16).
- incoming **depends_on_open**: [Z08::nondyadic_scaled_series_gives_fixed_shift_socket](BROWSER_Z08_1.md#node-56f767b53b6de465). non-dyadicity of (2^h - 1)*S is produced here only at bounded dyadic depth: the exclusion rules out denominators dividing 2^12 (h<=8) and 2^14 (h<=16). No node excludes dyadic denominators of unbounded 2-adic height, so no h is known for which the antecedent holds.
- incoming **alias_of**: [Z01::totient_series_rational_exclusions_from_kills](BROWSER_Z01_2.md#node-4bdd060dc42777bf). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18479/18562 re-export `totient_series_ne_rat_of_den_dvd` and `..._upto_sixteen`; identical bounded-denominator exclusions.

<a id="node-8a53e82f59607500"></a>
## unit_gap_prime_power_ceiling

At an odd prime-power reduced denominator, a valid unit-gap certificate forces the candidate count to be at most 1: the unit-gap strengthening can rescue at most one lattice point over the ordinary empty-gap certificate.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Applies ONLY to prime-power reduced denominators. It does not bound the candidate count for composite odd denominators with two or more distinct prime factors (where several consecutive integers can all be nonunits), does not show the unit-gap certificate fails to exist, and does not rule out the unit-gap supply hypothesis; it only shows that supply must solve a zero-or-one-candidate problem at every odd prime power as the depth grows.

- Lean declaration: [reducedDenominatorCandidateCount_prime_pow_le_one](../../Erdos249257/PrimitiveWeightCertificate.lean#L111)

- outgoing **barrier_for**: [Z06::reduction_unit_gap_supply_projection](BROWSER_Z06_2.md#node-f7cede0c08a3a33d). Any unit-gap supply must solve a zero-or-one-candidate problem at every odd prime power.

<a id="node-0968298cee21901b"></a>
## unit_gap_prime_power_classification

For a reduced denominator that is a prime power p^e (e > 0), the reduced-denominator unit-gap certificate holds if and only if the candidate count L is zero, or L = 1 and p divides J+1.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [reducedDenominatorUnitGapCert_prime_pow_iff](../../Erdos249257/PrimitiveWeightCertificate.lean#L54)


<a id="node-9c9cc20db0ae9940"></a>
## unit_gap_strict_strengthening_instance

At (u, N, K) = (3, 3, 5) the dyadic carry is 24, the unit-gap certificate holds, and the ordinary empty-gap certificate fails (scaled residue plus tail height is 38 against modulus 32): the unit-gap refinement is strictly stronger at at least one row.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [reducedDenominatorUnitGapCert_three_window_3_5](../../Erdos249257/PrimitiveWeightCertificate.lean#L151)
- Lean declaration: [not_ordinary_gap_certificate_three_window_3_5](../../Erdos249257/PrimitiveWeightCertificate.lean#L157)


