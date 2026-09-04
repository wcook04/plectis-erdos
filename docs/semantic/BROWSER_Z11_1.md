# Z11_1: Shared tempered binary-carry trunk and support-free zero-window transfer

[All problems and zones](BROWSER.md)

<a id="node-1ce1b5ef053ed69d"></a>
## affine_carry_fixed_depth_reset

For the input-driven affine carry recursion u(n+1) = 2u(n) - a(n+1) with a common forcing word a, two orbits started from different initial carries satisfy u_L - v_L = 2^L * (u_0 - v_0) exactly; consequently their endpoint values agree modulo 2^L. Depth-L residues are therefore determined by the last L forcing symbols and not by the predecessor carry.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The Lean statements are affineBinaryOrbit_sub and affineBinaryOrbit_mod_twoPow_eq: they compare two orbits STARTED AT INDEX 0 under the same forcing word a, and say the depth-L difference is 2^L*(u0-v0), hence 0 mod 2^L. The second clause of the canonical statement, 'depth-L residues are determined by the LAST L forcing symbols', is prose: there is no shift/translation lemma in the module placing the window at an arbitrary starting index, and no lemma exhibiting the residue as a function of a restricted to that window. Also nothing links affineBinaryOrbit to IsTemperedBinaryOrbit, binaryCoeffTail or either problem, so the module's framing of this as 'the positive replacement' for the barrier is a design intention, not a proved substitution.

- Lean declaration: [affineBinaryOrbit_sub](../../Erdos249257/GenericTailOrbitRigidity.lean#L289)
- Lean declaration: [affineBinaryOrbit_mod_twoPow_eq](../../Erdos249257/GenericTailOrbitRigidity.lean#L307)

- outgoing **repair_of**: [Z11::balanced_pulse_no_autonomous_finite_state](BROWSER_Z11_1.md#node-791e746b70a218df). The module presents the input-driven affine cocycle with its 2^L synchronisation as the positive replacement for the autonomous state the barrier rules out.
- outgoing **reformulates**: [Z06::dyadic_coboundary_shift_calculus](BROWSER_Z06_1.md#node-b5d0116c5f6ae00e). affineBinaryOrbit_sub / affineBinaryOrbit_mod_twoPow_eq and dyadicClearedPrefix_dyadicCoboundary are the same statement about the dyadic coboundary a = 2c - Ec: the depth-L cleared prefix is 2^L c_n - c_{n+L}, so depth-L residues ignore the initial carry.
- incoming **reformulates**: [Z12::mobius_centered_carry_coboundary](BROWSER_Z12_2.md#node-f4856da5bcdafc98). mobiusCenteredHalfCarry_coboundary is the affine recentring of the input-driven binary orbit u(n+1) = 2u(n) - a(n+1) that affineBinaryOrbit_sub describes, with the signed Moebius baseline as the shift.

<a id="node-791e746b70a218df"></a>
## balanced_pulse_no_autonomous_finite_state

WHAT IS ACTUALLY PROVED IN LEAN, itemised. (a) balancedPulseCoeff m r (radius R = floor((m+1)/2), value R-r at index m, 2r at index m+1, zero elsewhere) is admissible for the generic class: for 2 <= m and r <= R one has balancedPulseCoeff m r n <= n for all n (balancedPulseCoeff_le_self). (b) The two-site weighted numerator is constant in r: 2*c(m) + c(m+1) = 2R (balancedPulse_weighted_pair). (c) The right-hand site decodes the parameter: c(m+1)/2 = r (balancedPulse_endpoint_fanout). (d) A PURELY GENERIC pigeonhole: any label : Fin (R+1) -> Lambda admitting a left inverse decode is injective, hence R+1 <= card Lambda for finite Lambda (balancedPulse_label_injective, balancedPulse_label_card_lower_bound). (e) Arithmetic: k+1 <= balancedPulseRadius (2k) + 1 (balancedPulse_fanout_unbounded). (f) A constant state map state : Fin (R+1) -> State with state r = state 0 for all r admits no decode with decode (state r) = r (balancedPulse_no_autonomous_decoder). The assembly of (a)-(f) into a no-go for autonomous finite-state successor interfaces is PROSE in the module docstring, not a Lean theorem: see scope_caveat for the three missing formal links.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: THREE FORMAL LINKS ARE MISSING, verified by grep: `balancedPulse` occurs only in Erdos249257/GenericTailOrbitRigidity.lean and in no other module. (1) NO Lean declaration states that binaryCoeffSeries (balancedPulseCoeff m r) is independent of r. balancedPulse_weighted_pair proves only the natural-number identity 2*c(m)+c(m+1)=2R; the step from that to equality of the real series values is never taken in Lean. The canonical claim 'all of which have the same binary series value' is therefore UNFORMALISED. (2) NO Lean declaration states that the coefficients of balancedPulseCoeff m r agree strictly before m across r (it follows in one line from balancedPulseCoeff_eq_zero_of_ne, but it is not stated), and nothing connects 'the common pre-m history' to the `state`/`label` maps: in balancedPulse_label_injective, balancedPulse_label_card_lower_bound and balancedPulse_no_autonomous_decoder the maps are arbitrary functions out of Fin (balancedPulseRadius m + 1) and balancedPulseCoeff never appears in the statement. The pulse family enters those three declarations only as a numeral for the domain cardinality. (3) NO Lean declaration connects any of this to IsTemperedBinaryOrbit, binaryCoeffTail, or the rationality criterion, so the barrier is not formally attached to the object it is advertised as blocking. In addition this does NOT rule out: (i) any method aimed at the actual problems, because the witness sequences vanish at every index except m and m+1, and no such sequence is Euler phi (never zero on positive n) or a support coefficient f_A of an infinite support, so #249/#257 methods are never confronted with this family; (ii) input-driven or growing-depth state, which the same module then offers as the positive replacement (affineBinaryOrbit); (iii) decoders that read more than the common pre-m history, or that read the arithmetic structure of the index; (iv) approximate, non-exact successor interfaces, or interfaces that only need the value rather than the exact tail. The previous version of this caveat said 'the genuine unbounded-fan-out content lives in balancedPulse_label_card_lower_bound'; that was itself an overclaim and is retracted here, since that declaration is generic pigeonhole with no pulse content.

Open hypotheses: ["hstate : forall r, state r = state <0> in balancedPulse_no_autonomous_decoder -- an UNPROVED MODELLING ASSUMPTION (not an open number-theoretic problem). The docstring justifies it by 'as every state determined by the common pre-m history must', but no Lean declaration in this corpus proves that a state determined by the common pre-m history is constant on the pulse family, because the required premise (equal series value and equal pre-m coefficients across the family) is itself never formalised. Without hstate the declaration has no content."]

- Lean declaration: [balancedPulse_no_autonomous_decoder](../../Erdos249257/GenericTailOrbitRigidity.lean#L247)
- Lean declaration: [balancedPulse_label_card_lower_bound](../../Erdos249257/GenericTailOrbitRigidity.lean#L228)
- Lean declaration: [balancedPulse_label_injective](../../Erdos249257/GenericTailOrbitRigidity.lean#L216)
- Lean declaration: [balancedPulse_fanout_unbounded](../../Erdos249257/GenericTailOrbitRigidity.lean#L237)

- outgoing **barrier_for**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). It blocks replacing the tempered orbit in the criterion by an autonomous finite-state successor function, but only inside the generic linear-growth class.
- incoming **repair_of**: [Z11::affine_carry_fixed_depth_reset](BROWSER_Z11_1.md#node-1ce1b5ef053ed69d). The module presents the input-driven affine cocycle with its 2^L synchronisation as the positive replacement for the autonomous state the barrier rules out.

<a id="node-636d86dd83d106a9"></a>
## binary_coefficient_series_representation

For a natural coefficient sequence c, binaryCoeffSeries c is the real series sum over n>=0 of c(n+1)/2^(n+1). It is the common binary generating-series interface instantiated by Euler's totient for Erdős #249 and by support coefficients for Erdős #257.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The definition supplies only the ambient real series. It does not assert convergence beyond the hypotheses used by downstream theorems, rationality, irrationality, or any property special to totients or support coefficients.

- Lean declaration: [binaryCoeffSeries](../../Erdos249257/GenericTailOrbitRigidity.lean#L37)


<a id="node-51b4e0f463db1e09"></a>
## binary_tail_shift_identity

For c(n) <= n the scaled binary tail satisfies T_c(0) = X_c, 0 <= T_c(N) <= N + 2, T_c(N)/2^N -> 0, and the exact one-step shift identity T_c(N+1) = 2*T_c(N) - c(N+1). This is the analytic normalisation of the object: shifting the binary window by one digit doubles the tail and expels the head coefficient.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [binaryCoeffTail_succ](../../Erdos249257/GenericTailOrbitRigidity.lean#L111)
- Lean declaration: [binaryCoeffTail_zero](../../Erdos249257/GenericTailOrbitRigidity.lean#L73)
- Lean declaration: [binaryCoeffTail_nonneg](../../Erdos249257/GenericTailOrbitRigidity.lean#L78)
- Lean declaration: [binaryCoeffTail_le](../../Erdos249257/GenericTailOrbitRigidity.lean#L85)
- Lean declaration: [binaryCoeffTail_div_pow_tendsto_zero](../../Erdos249257/GenericTailOrbitRigidity.lean#L91)

- outgoing **implies**: [Z11::tempered_orbit_rigidity](BROWSER_Z11_1.md#node-a9e7e0703d37a58b). The one-step shift identity is exactly the recurrence that the difference d(N) = u(N) - v*T_c(N) must satisfy, and the o(2^N) tail bound makes the temperedness hypothesis non-vacuous.
- outgoing **reformulates**: [Z12::integer_half_carry_calculus](BROWSER_Z12_1.md#node-59e84eab60406093). integerHalfCarry_eq_scaled_residual_add_tail writes the half carry as 2^(N+1)(1/2 - value) + binaryCoeffTail at N+1: the affine recentring at target 1/2 of the generic shift identity binaryCoeffTail_succ.
- incoming **reformulates**: [Z17::n251_tail_block_identity](BROWSER_Z17_2.md#node-48fddc1aba479f46). tail_iterate_eq_pow_mul_sub_block iterates the same dyadic tail recurrence T(N+1) = 2 T(N) - g(N+1) that binaryCoeffTail_succ states for coefficient sequences with c(n) <= n.
- incoming **transport_of**: [Z17::n1049_cleared_tail_recurrence](BROWSER_Z17_1.md#node-7f708faae54a5953). rationalBaseClearedTailQ_succ gives cleared(N+1) = r*cleared(N) - B*coeff(N+1)*s^(N+1), which collapses at s = 1 (rationalBaseForcingNat_one) to the integer-base tail recurrence binaryCoeffTail_succ; the factor s^(N+1) is the denominator-base tax.
- outgoing **specialises**: [Z17::n1049_cleared_tail_recurrence](BROWSER_Z17_1.md#node-7f708faae54a5953). Z17's `ErdosProblems.Erdos1049.rationalBaseClearedTailQ_succ` gives cleared(N+1) = r cleared(N) - B coeff(N+1) s^(N+1) for a rational base r/s; at (r,s,B) = (2,1,1) this is Z11's `binaryCoeffTail_succ` T(N+1) = 2 T(N) - c(N+1), the s = 1 collapse being recorded by `ErdosProblems.Erdos1049.rationalBaseForcingNat_one`.

<a id="node-831b7c9a93c3f3d6"></a>
## explicit_fixed_power_divisor_bound

For every n >= 1 and every k >= 1, the divisor count satisfies tau(n)^k <= (k^(2^k))^k * n, and hence tau(n) <= k^(2^k) * n^(1/k) for all n (including n = 0). The proof is entirely in the naturals: at each prime power p^a one has (a+1)^k <= k^k * 2^a <= k^k * p^a when p < 2^k, and (a+1)^k <= p^a when p >= 2^k, and there are at most 2^k primes below the cutoff.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [card_divisors_pow_le_divisorSubpowerConst_pow_mul](../../Erdos249257/SublogDivisorCoverage.lean#L107)
- Lean declaration: [card_divisors_le_divisorSubpowerConst_mul_rpow](../../Erdos249257/SublogDivisorCoverage.lean#L142)

- outgoing **implies**: [Z11::support_coefficient_subpower_envelope](BROWSER_Z11_1.md#node-c4e55b27c24c8597). The support coefficient is bounded by the divisor count pointwise, so the divisor bound transfers verbatim and uniformly in A.

<a id="node-541429c78c537b38"></a>
## rational_denominator_divisor_survival

If D > 0, m divides D, and m is coprime to |a|, then m divides the denominator of the reduced rational a/D. More generally, if C divides D and C is coprime to |a|, then C/gcd(C,h) divides the denominator of the reduced rational (h*a)/D: scaling by h can cancel exactly the part gcd(C,h) of C and no more. The clean corollary 'if in addition C is coprime to h then C itself divides the reduced denominator' is present only as an UNNAMED `example` at RationalDenominatorSurvival.lean:99, so it is not citable and does not appear in the declaration atlas.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: This node covers only the two named theorems. The module additionally contains seven unnamed `example` declarations (lines 79, 82, 87, 90, 93, 96, 99) which are outside docs/declaration_atlas.json entirely, because the atlas indexes named declarations only. They are recorded in declaration_roles below with synthetic identifiers of the form `example@<line>` and are NOT citable Lean names.

- Lean declaration: [divisor_dvd_divInt_den](../../Erdos249257/RationalDenominatorSurvival.lean#L17)
- Lean declaration: [survivingDivisor_dvd_scaled_divInt_den](../../Erdos249257/RationalDenominatorSurvival.lean#L38)

- outgoing **repair_of**: [Z09::scalar_localisation_height_barrier](BROWSER_Z09_2.md#node-e79c79b3968927cf). The barrier shows scalar clearing transfers the discarded reduced denominator into the coefficient (scalarLocalization_complement_dvd). survivingDivisor_dvd_scaled_divInt_den does that bookkeeping exactly rather than trying to avoid it: for C dividing D and coprime to |a|, C/gcd(C,h) divides the denominator of (h*a)/D, so a scalar multiplier h cancels precisely gcd(C,h) of C and no more.
- incoming **alias_of**: [Z04::rational_denominator_survival_reexport](BROWSER_Z04_2.md#node-1481b123d79ef011). Both nodes own exactly the declarations `divisor_dvd_divInt_den` and `survivingDivisor_dvd_scaled_divInt_den` of Erdos249257/RationalDenominatorSurvival.lean; the Z04 node states in its own docstring that it is a re-export.

<a id="node-46b1e212e1d31fe2"></a>
## rational_support_zero_window_lower_bound

Suppose A contains a positive element and the Erdos #257 series sum_{a in A} 1/(2^a - 1) equals p/(2^c * v) with v > 0. Then for every N and every h, if the support coefficient f_A vanishes at c+N+1, ..., c+N+h, one has 2^h <= v * T_{f_A}(c+N+h); and with any upper envelope for that tail, 2^h <= v * envelope(c+N+h). Substituting the unconditional (1/k)-envelope gives 2^h <= 2*v*k^(2^k) * (c+N+1+h)^(1/k).

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Not a restatement: the hypothesis is the NEGATION of the #257 conclusion and the conclusion is new structural information about A, so is_restatement_of_open_problem is correctly false. But the direction of implication means no instance of this theorem can be discharged without deciding #257 negatively for some A, and the corpus exhibits no infinite A satisfying hvalue. Same vacuity risk as sublogarithmic_zero_window_bound. The existence of the doubling state is supplied entirely by exists_shifted_odd_tail_nat_states_of_support_fraction (RationalSupportCarrySkeleton.lean:668), which lies outside this zone and is itself conditioned on hvalue.

Open hypotheses: ["hvalue : erdosSupportSeries 2 A = (p : R) / ((2 ^ c * v : N) : R) -- i.e. the assumption that sum_{a in A} 1/(2^a - 1) is rational, which is exactly what Erdos #257 asks one to refute for infinite A; nobody has proved it for any infinite A and it is expected to be false"]

- Lean declaration: [pow_le_mul_binaryCoeffTail_of_support_fraction_zeroWindow](../../Erdos249257/SublogDivisorCoverage.lean#L232)
- Lean declaration: [pow_le_mul_tailEnvelope_of_support_fraction_zeroWindow](../../Erdos249257/SublogDivisorCoverage.lean#L285)
- Lean declaration: [pow_le_divisorSubpower_of_support_fraction_zeroWindow](../../Erdos249257/SublogDivisorCoverage.lean#L319)
- Lean declaration: [pow_le_mul_two_mul_rpow_of_card_divisors_bound_zeroWindow](../../Erdos249257/SublogDivisorCoverage.lean#L301)

- incoming **implies**: [Z11::zero_window_exact_state_doubling](BROWSER_Z11_1.md#node-86b97cb3d41e8e96). The support version is the generic doubling certificate applied to the shifted odd-denominator natural state supplied by the rationality hypothesis.
- outgoing **implies**: [Z11::sublogarithmic_zero_window_bound](BROWSER_Z11_1.md#node-d8afdc3d1b1800f5). It supplies the lower certificate 2^h <= v*T(c+N+h) that the absorption step inverts.
- incoming **depends_on_open**: [Z11::sublogarithmic_zero_window_bound](BROWSER_Z11_1.md#node-d8afdc3d1b1800f5). Both carry the identical unproved antecedent that the #257 series for A is rational; neither is unconditional.
- outgoing **transport_of**: [Z10::rational_value_constructs_odd_tail_state](BROWSER_Z10_2.md#node-ded6e5d67b309122). Both carry the identical antecedent erdosSupportSeries 2 A = p/(2^c*v) and speak of the same doubling state, produced by exists_shifted_odd_tail_nat_states_of_support_fraction (RationalSupportCarrySkeleton.lean:668).
- outgoing **depends_on_open**: [Z10::rationality_iff_tempered_support_carry_orbit](BROWSER_Z10_2.md#node-dd2d02eb2e53e47f). the hypothesis erdosSupportSeries 2 A = p/(2^c v) is the left side of this equivalence; for infinite A its failure is exactly Erdos #257, and the equivalence shows the only route to it would be a tempered incidence carry orbit, which nothing constructs.

<a id="node-c6723797a207ec2e"></a>
## rational_value_predicate_normalisation

The explicit predicate 'x = p/v for some integer p and positive natural v' is equivalent to the Mathlib predicate 'x is not irrational'. This only makes the carry multiplier v visible in downstream theorem statements.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [hasRationalValue_iff_not_irrational](../../Erdos249257/GenericTailOrbitRigidity.lean#L52)

- outgoing **reformulates**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). It is the only thing separating the explicit-denominator form of the criterion from its Mathlib Irrational form.

<a id="node-e4f918bdb6539d80"></a>
## rationality_iff_tempered_orbit

For c(n) <= n, the binary series sum c(n)/2^n is rational if and only if there exist a positive integer v and an integer sequence u with u(N+1) = 2u(N) - v*c(N+1) and u(N) = o(2^N). Both directions are proved: rationality supplies u(N) = v*T_c(N) built from the truncation integers, and any tempered orbit gives the value u(0)/v. Instantiated at c = Euler phi this is exactly Erdos #249 and at c = supportCoeff A exactly Erdos #257, so the two sides of the equivalence are equally open for the sequences of interest: the criterion transports the problem into carry-orbit language without reducing its difficulty.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: BOTH SIDES OPEN. open_antecedents is empty because the Lean theorem has no free hypothesis (hgrowth : c n <= n is a binder discharged for both sequences of interest), not because nothing is open. At c = Nat.totient, 'HasRationalValue (binaryCoeffSeries Nat.totient)' is the negation of Erdos #249 and is unproved; the right-hand side 'exists a tempered orbit' is by this very theorem equivalent to it and is therefore equally unproved. At c = supportCoeff A the same holds for Erdos #257 via erdosSupportSeries_two_eq_binaryCoeffSeries (BooleanMobiusCarry.lean:376). So the equivalence changes vocabulary, not difficulty, and is correctly flagged is_restatement_of_open_problem = true. Nothing downstream in this zone discharges either side.

- Lean declaration: [binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit](../../Erdos249257/GenericTailOrbitRigidity.lean#L426)
- Lean declaration: [not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit](../../Erdos249257/GenericTailOrbitRigidity.lean#L435)
- Lean declaration: [exists_temperedBinaryOrbit_of_rational](../../Erdos249257/GenericTailOrbitRigidity.lean#L368)
- Lean declaration: [rational_of_exists_temperedBinaryOrbit](../../Erdos249257/GenericTailOrbitRigidity.lean#L413)

- incoming **implies**: [Z11::tempered_orbit_rigidity](BROWSER_Z11_1.md#node-a9e7e0703d37a58b). The reverse direction of the criterion is rigidity evaluated at N = 0 together with T_c(0) = X_c.
- incoming **reformulates**: [Z11::rational_value_predicate_normalisation](BROWSER_Z11_1.md#node-c6723797a207ec2e). It is the only thing separating the explicit-denominator form of the criterion from its Mathlib Irrational form.
- incoming **barrier_for**: [Z11::balanced_pulse_no_autonomous_finite_state](BROWSER_Z11_1.md#node-791e746b70a218df). It blocks replacing the tempered orbit in the criterion by an autonomous finite-state successor function, but only inside the generic linear-growth class.
- incoming **transport_of**: [Z09::finite_level_carry_anti_compression](BROWSER_Z09_1.md#node-321a6939105b78f6). The node's free hypothesis IsTemperedBinaryOrbit Nat.totient v u is, by not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit, equivalent to rationality of sum phi(n)/2^n, i.e. to failure of Erdos #249.
- incoming **transport_of**: [Z09::rationality_forces_unbounded_carry_rank](BROWSER_Z09_2.md#node-0b905695e89a37be). not_irrational_totientSeries_implies_unbounded_carryRank is the composition of the rank bound with binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit instantiated at c = Nat.totient.
- outgoing **equivalent_to**: [Z10::rationality_iff_tempered_support_carry_orbit](BROWSER_Z10_2.md#node-dd2d02eb2e53e47f). erdosSupportSeries_two_eq_binaryCoeffSeries (BooleanMobiusCarry.lean:376) identifies the base-2 support series with binaryCoeffSeries (supportCoeff A), so erdosSupportSeries_rational_iff_exists_temperedCarry is binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit at c = supportCoeff A.
- incoming **transport_of**: [Z12::tempered_mobius_carry_yields_half](BROWSER_Z12_2.md#node-c0baa14342623c9d). support_half_of_mobiusCenteredHalfCarry_tempered is the Moebius-recentred instance of the tempered-orbit criterion at c = supportCoeff A with target value 1/2; the temperedness hypothesis is the same o(2^N) condition.
- incoming **finite_instance_of**: [Z10::support23_period_six_carry_fixture](BROWSER_Z10_2.md#node-a4d7972fa4b13a06). the exhibited period-six orbit 10,20,19,17,13,26 with all differences divisible by 21 is a concrete tempered integer carry orbit with multiplier v=21 for c = supportCoeff {2,3}, realising the right-hand side of the equivalence at the rational value 10/21.
- incoming **depends_on_open**: [Z09::finite_level_carry_anti_compression](BROWSER_Z09_1.md#node-321a6939105b78f6). the free hypothesis IsTemperedBinaryOrbit phi v u is, by this equivalence instantiated at c = phi, logically equivalent to rationality of sum phi(n)/2^n, i.e. to the FAILURE of Erdos #249; so no producer can exist and the theorem is vacuous if #249 is true.
- incoming **depends_on_open**: [Z10::rational_value_constructs_odd_tail_state](BROWSER_Z10_2.md#node-ded6e5d67b309122). the free hypothesis is rationality of the #257 support series; instantiated at c = supportCoeff A this equivalence shows that is exactly existence of a tempered integer carry orbit, and it records that both sides are equally open. No producer exists.
- incoming **depends_on_open**: [Z10::rational_value_forces_order_wrap_ratio_bound](BROWSER_Z10_2.md#node-3845be9631e85dab). the free hypothesis is rationality of the #257 support series; instantiated at c = supportCoeff A this equivalence shows that is exactly existence of a tempered integer carry orbit, and it records that both sides are equally open. No producer exists.
- incoming **depends_on_open**: [Z10::dyadic_denominator_forces_reciprocal_mass_above_one](BROWSER_Z10_1.md#node-3f4c27e9053d57d5). the free hypothesis is rationality of the #257 support series; instantiated at c = supportCoeff A this equivalence shows that is exactly existence of a tempered integer carry orbit, and it records that both sides are equally open. No producer exists.
- incoming **depends_on_open**: [Z10::carry_state_unbounded_at_common_multiples](BROWSER_Z10_1.md#node-2195d2fe55e6ff39). the free hypothesis is rationality of the #257 support series; instantiated at c = supportCoeff A this equivalence shows that is exactly existence of a tempered integer carry orbit, and it records that both sides are equally open. No producer exists.
- incoming **specialises**: [Z10::rationality_iff_tempered_support_carry_orbit](BROWSER_Z10_2.md#node-dd2d02eb2e53e47f). `erdosSupportSeries_rational_iff_exists_temperedCarry` (BooleanMobiusCarry.lean:383) is the c := supportCoeff A instance of `binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit` (GenericTailOrbitRigidity.lean:425), the growth side condition c n <= n discharged by `supportCoeff_le_self`.

<a id="node-1c1335942a503a9a"></a>
## self_reference_absorption_log_inversion

Fix an integer k >= 2, a natural Y >= 1 and a real L >= 1. If 2^h <= L*(Y+h)^(1/k), then 2^((k-1)h) <= L^k * Y, hence h <= (log_2 Y + log_2(L^k))/(k-1). Composed with a window lower certificate and a matching (1/k)-power tail envelope, this converts the pair (certificate, envelope) into the explicit window-length bound h <= (log_2(start+1) + log_2((scale*C)^k))/(k-1). The step that removes the self-reference is Y+h <= Y*2^h, which consumes exactly one of the k binary factors.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Side conditions omitted from the canonical statement's composed form, present in the Lean: length_le_logb_of_binaryTailWindowLowerBound additionally requires hscale : 0 <= scale and hLC : 1 <= scale * C, and its envelope binder is the exact shape C*(M+1)^(1/k) (not an arbitrary envelope). The absorption lemma pow_sub_one_mul_le_of_pow_le_mul_add_invNat_rpow requires k >= 2, Y >= 1 and L >= 1. Only the reverse direction is proved: nothing here shows the resulting bound is tight, and the k-th-power step is lossy, so the exponent 1/(k-1) is an artefact of the absorption, not a proved optimum.

- Lean declaration: [pow_sub_one_mul_le_of_pow_le_mul_add_invNat_rpow](../../Erdos249257/BinaryTailWindowTransfer.lean#L255)
- Lean declaration: [length_le_logb_of_pow_le_mul_add_invNat_rpow](../../Erdos249257/BinaryTailWindowTransfer.lean#L303)
- Lean declaration: [length_le_logb_of_binaryTailWindowLowerBound](../../Erdos249257/BinaryTailWindowTransfer.lean#L334)

- outgoing **implies**: [Z11::sublogarithmic_zero_window_bound](BROWSER_Z11_1.md#node-d8afdc3d1b1800f5). The support-free transfer lemma is applied verbatim with scale = v, C = 2*k^(2^k), start = c+N.

<a id="node-d8afdc3d1b1800f5"></a>
## sublogarithmic_zero_window_bound

Suppose A contains a positive element and sum_{a in A} 1/(2^a - 1) = p/(2^c * v) with v > 0. Then for every k >= 2, every zero window of f_A starting after c+N has length h <= (log_2(c+N+1) + log_2((2*v*k^(2^k))^k))/(k-1); and for every epsilon > 0 there is a constant B = B(epsilon, c, v) >= 0 with h <= epsilon*log_2(N+1) + B for all N and h, and h <= epsilon*log_2 N + B for all N >= 1. Equivalently, under rationality the gaps in the support of f_A are o(log N). The bound is uniform in A, p, N and h at fixed (c, v), but the constant B is not small: choosing k of order 1/epsilon makes B grow like 2^(1/epsilon), so the estimate is asymptotic in N and gives nothing at bounded N.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: DOCSTRING/STATEMENT MISMATCH, flagged deliberately. supportCoeffZeroWindow_length_le_eps_logb_add carries the docstring heading '**Unconditional T11.**' and sits under the section header '## Unconditional T11', but its Lean binder list contains hvalue : erdosSupportSeries 2 A = p / (2^c * v), i.e. rationality of the #257 series for A. The theorem is CONDITIONAL; only the divisor-envelope half (support_coefficient_subpower_envelope) is unconditional, and the module's own opening docstring says as much ('The unconditional half is now closed in the same module'). This node is classified from the Lean binders, not the heading. The module also carries an explicit NON-CLAIM paragraph disclaiming any resolution of #257 or #249. Vacuity risk: if #257 is true for all infinite A then hvalue is satisfiable only by finite A (and by the A the corpus does not exclude), so the theorem may have no infinite-support instances at all; nothing in the corpus exhibits an A satisfying hvalue with infinite support.

Open hypotheses: ["hvalue : erdosSupportSeries 2 A = (p : R) / ((2 ^ c * v : N) : R) -- the rationality of sum_{a in A} 1/(2^a - 1); this is the negation of the Erdos #257 conclusion and is proved nowhere in the corpus"]

- Lean declaration: [supportCoeffZeroWindow_length_le_eps_logb](../../Erdos249257/SublogDivisorCoverage.lean#L435)
- Lean declaration: [supportCoeffZeroWindow_length_le_eps_logb_add](../../Erdos249257/SublogDivisorCoverage.lean#L392)
- Lean declaration: [supportCoeffZeroWindow_length_le_logb_divisorSubpower](../../Erdos249257/SublogDivisorCoverage.lean#L348)

- incoming **implies**: [Z11::rational_support_zero_window_lower_bound](BROWSER_Z11_1.md#node-46b1e212e1d31fe2). It supplies the lower certificate 2^h <= v*T(c+N+h) that the absorption step inverts.
- incoming **implies**: [Z11::support_coefficient_subpower_envelope](BROWSER_Z11_1.md#node-c4e55b27c24c8597). It supplies the unconditional (1/k)-power upper envelope, the only other input the transfer layer consumes.
- incoming **implies**: [Z11::self_reference_absorption_log_inversion](BROWSER_Z11_1.md#node-1c1335942a503a9a). The support-free transfer lemma is applied verbatim with scale = v, C = 2*k^(2^k), start = c+N.
- outgoing **depends_on_open**: [Z11::rational_support_zero_window_lower_bound](BROWSER_Z11_1.md#node-46b1e212e1d31fe2). Both carry the identical unproved antecedent that the #257 series for A is rational; neither is unconditional.
- outgoing **transport_of**: [Z10::rational_value_forces_order_wrap_ratio_bound](BROWSER_Z10_2.md#node-3845be9631e85dab). The two nodes convert one and the same open rationality antecedent, through the same odd-denominator tail state, into two different structural consequences for A: a zero-window length bound and a reciprocal-mass lower bound.
- outgoing **depends_on_open**: [Z10::rationality_iff_tempered_support_carry_orbit](BROWSER_Z10_2.md#node-dd2d02eb2e53e47f). same rationality hypothesis; the equivalence identifies it with existence of a tempered incidence carry orbit, undecided for every infinite support in the corpus.

<a id="node-74c62382f3340c5b"></a>
## subpower_tail_envelope_from_coefficient_bound

If f(n) <= C*n^delta for all n with 0 <= delta <= 1, then the binary tail of f satisfies T_f(M) <= 2*C*(M+1)^delta for every M. The proof uses M+j+1 <= (M+1)(j+1), sub-multiplicativity of the delta-power, and the exact identity sum_{j>=0} (j+1)/2^(j+1) = 2.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [binaryCoeffTail_le_two_mul_rpow](../../Erdos249257/BinaryTailWindowTransfer.lean#L156)
- Lean declaration: [binaryCoeffTailEnvelope_two_mul_rpow](../../Erdos249257/BinaryTailWindowTransfer.lean#L220)

- incoming **specialises**: [Z11::support_coefficient_subpower_envelope](BROWSER_Z11_1.md#node-c4e55b27c24c8597). The support-tail envelope is the generic envelope constructor instantiated at f = supportCoeff A with delta = 1/k.
- incoming **depends_on_open**: [Z10::denominator_shell_pressure_from_analytic_tail_bound](BROWSER_Z10_1.md#node-1630e5ef2f14794e). the missing hypothesis is a denominator-uniform shell-plus-far-tail bound beta <= K/2^X + 2/2^(2X); this is the corpus's only unconditional binary-tail envelope and it is neither denominator-uniform nor of that shape, which is what the module docstring calls the global bottleneck.

<a id="node-c4e55b27c24c8597"></a>
## support_coefficient_subpower_envelope

For every support set A and every k >= 1: the natural-number power form f_A(n)^k <= (k^(2^k))^k * n holds for every n >= 1 (the Lean binder is hn : 0 < n), and the real form f_A(n) <= k^(2^k) * n^(1/k) holds for every n including n = 0; consequently the binary tail of f_A satisfies T_{f_A}(M) <= 2*k^(2^k)*(M+1)^(1/k) for all M. The bound is uniform in A.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [supportCoeffTailEnvelope_divisorSubpower](../../Erdos249257/SublogDivisorCoverage.lean#L268)
- Lean declaration: [supportCoeff_le_divisorSubpowerConst_mul_rpow](../../Erdos249257/SublogDivisorCoverage.lean#L186)
- Lean declaration: [supportCoeff_pow_le_divisorSubpowerConst_pow_mul](../../Erdos249257/SublogDivisorCoverage.lean#L176)

- outgoing **specialises**: [Z11::subpower_tail_envelope_from_coefficient_bound](BROWSER_Z11_1.md#node-74c62382f3340c5b). The support-tail envelope is the generic envelope constructor instantiated at f = supportCoeff A with delta = 1/k.
- incoming **implies**: [Z11::explicit_fixed_power_divisor_bound](BROWSER_Z11_1.md#node-831b7c9a93c3f3d6). The support coefficient is bounded by the divisor count pointwise, so the divisor bound transfers verbatim and uniformly in A.
- outgoing **implies**: [Z11::sublogarithmic_zero_window_bound](BROWSER_Z11_1.md#node-d8afdc3d1b1800f5). It supplies the unconditional (1/k)-power upper envelope, the only other input the transfer layer consumes.
- outgoing **reformulates**: [Z10::divisor_pair_square_root_envelope](BROWSER_Z10_1.md#node-1d5f5df7a851affd). supportCoeff_le_two_mul_sqrt and supportCoeff_le_divisorSubpowerConst_mul_rpow are the same envelope f_A <= tau at two exponents (1/2 and 1/k), and both are pushed to the binary tail by the same geometric majorant.
- incoming **depends_on_open**: [Z10::sunflower_conditional_irrationality](BROWSER_Z10_2.md#node-369dbe6f906c9180). the selector needs binaryCoeffTail (supportCoeff A) (N+K) <= 16, a CONSTANT bound. The nearest existing control is this uniform envelope T(M) <= 2*k^(2^k)*(M+1)^(1/k), which is unbounded in M for every k, so it cannot produce the selector; nothing else in the corpus bounds the incidence tail by a constant on any infinite support.

<a id="node-a9e7e0703d37a58b"></a>
## tempered_orbit_rigidity

Let c be a coefficient sequence with c(n) <= n for all n. If an integer sequence u satisfies u(N+1) = 2u(N) - v*c(N+1) for all N and u(N)/2^N tends to 0, then u(N) equals v times the scaled binary tail of c at N, for every N. The engine is the abstract fact that a real sequence with d(N+1) = 2d(N) and d(N) = o(2^N) is identically zero.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [temperedBinaryOrbit_eq_scaledTail](../../Erdos249257/GenericTailOrbitRigidity.lean#L339)
- Lean declaration: [doublingOrbit_eq_zero_of_tempered](../../Erdos249257/GenericTailOrbitRigidity.lean#L315)

- incoming **implies**: [Z11::binary_tail_shift_identity](BROWSER_Z11_1.md#node-51b4e0f463db1e09). The one-step shift identity is exactly the recurrence that the difference d(N) = u(N) - v*T_c(N) must satisfy, and the o(2^N) tail bound makes the temperedness hypothesis non-vacuous.
- outgoing **implies**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). The reverse direction of the criterion is rigidity evaluated at N = 0 together with T_c(0) = X_c.
- outgoing **repair_of**: [Z17::n251_free_carry_barrier](BROWSER_Z17_1.md#node-f3051b3e0ee128e4). The barrier's freedom comes from an arbitrary integer carry K with no growth constraint (ErdosProblems.Erdos251.carryPartialSum_eq is a bare telescoping identity with no limit taken). temperedBinaryOrbit_eq_scaledTail proves that once c(n) <= n and u(N)/2^N -> 0 are imposed, u(N) = v * T_c(N) for every N, so exactly the freedom the barrier exploits is removed; the Z17 scope itself flags that the natural-valued version needs K(n+1) <= 2K(n).

<a id="node-86b97cb3d41e8e96"></a>
## zero_window_exact_state_doubling

If a natural-number state u obeys u(n+1) + v*f(offset+n+1) = 2*u(n) and f vanishes at the h indices offset+N+1, ..., offset+N+h, then u(N+h) = 2^h * u(N) exactly. If in addition u(N) > 0 then 2^h <= u(N+h); and if u realises the scaled tail, u(n) = v*T_f(offset+n), this yields the reusable lower certificate 2^h <= v*T_f(offset+N+h). Only positivity at the left edge of the window is used.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The sentence 'Only positivity at the left edge of the window is used' is accurate for the generic binaryTailWindowLowerBound_of_natState (binder huN : 0 < u N) but NOT for the support-side pow_le_shiftedTailState_of_supportCoeffZeroWindow, whose Lean binder is the strictly stronger hpos : forall n, 0 < u n. Also note that state_eq_pow_mul_of_coeffZeroWindow says nothing about the existence of such a state u; the only producer of one in this zone is the rationality-conditioned exists_shifted_odd_tail_nat_states_of_support_fraction (RationalSupportCarrySkeleton.lean:668), so this node is unconditional exactly because it quantifies over hypothetical states.

- Lean declaration: [state_eq_pow_mul_of_coeffZeroWindow](../../Erdos249257/BinaryTailWindowTransfer.lean#L59)
- Lean declaration: [binaryTailWindowLowerBound_of_natState](../../Erdos249257/BinaryTailWindowTransfer.lean#L90)
- Lean declaration: [shiftedTailState_eq_pow_mul_of_supportCoeffZeroWindow](../../Erdos249257/SublogDivisorCoverage.lean#L207)
- Lean declaration: [pow_le_shiftedTailState_of_supportCoeffZeroWindow](../../Erdos249257/SublogDivisorCoverage.lean#L218)

- outgoing **implies**: [Z11::rational_support_zero_window_lower_bound](BROWSER_Z11_1.md#node-46b1e212e1d31fe2). The support version is the generic doubling certificate applied to the shifted odd-denominator natural state supplied by the rationality hypothesis.

