# Z87_1: Angle A4: exact non-integrality coordinates, scalar lift obstruction, and frontier localisation

[All problems and zones](BROWSER.md)

<a id="node-f4620f495f80de1c"></a>
## frontier_multiplier_lattice_defeats_the_bounded_depth_localisation_argument

For every positive natural M and real D, some D' has M·D' integral and |D-D'|≤1/(2M). At the 67-over-periodLcm(66) rung, mersenneRatio(67,periodLcm(66))≥2^L whenever L≤66·periodLcm(66). Hence every real D has such a multiplier-lattice point D' within 2^(-(L+1)) at every depth in that range.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is a barrier only for the stated bounded-depth localisation argument. It is not a lower bound on every possible proof, does not determine the minimal certificate depth for the concrete totient series, and does not refute a lift using additional arithmetic information.

- Lean declaration: [exists_lattice_point](../../ErdosProblems/Lift/AngleA4.lean#L634)
- Lean declaration: [frontier_multiplier_ge](../../ErdosProblems/Lift/AngleA4.lean#L649)
- Lean declaration: [frontier_ball_meets_lattice](../../ErdosProblems/Lift/AngleA4.lean#L666)

- outgoing **barrier_for**: [Z87::the_period_lift_is_exactly_multiplication_by_the_mersenne_geometric_ratio](BROWSER_Z87_1.md#node-851b60d61e92c2e3). The multiplier lattice is exactly the set where the scalar lift conclusion fails, and the density estimate shows bounded-depth localization cannot exclude that set by radius alone.
- outgoing **complements**: [Z87::one_rational_witness_passes_all_period_kills_through_sixty_six_and_fails_at_sixty_seven](BROWSER_Z87_1.md#node-1c6b39e3229d4f4e). The fixed rational witness gives an exact logical counterexample, while the lattice theorem quantifies why the associated frontier multiplier remains dense at bounded localization depth.

<a id="node-c7567e14d9ea0b0b"></a>
## lcm_nesting_and_multiplicative_order_locate_period_kill_transport

The period-lcm ladder is divisibility-monotone: s≤t implies periodLcm(s) divides periodLcm(t), and killing a period implies killing each divisor period. Moreover, if d is prime, q>1, and q divides 2^d-1, then q divides 2^H-1 exactly when d divides H.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: These transports organise which reciprocal denominator appears at which rung. They produce neither a new prime divisor nor a certified kill for the totient series.

- Lean declaration: [periodLcm_dvd_of_le](../../ErdosProblems/Lift/AngleA4.lean#L554)
- Lean declaration: [killsPeriod_of_dvd](../../ErdosProblems/Lift/AngleA4.lean#L560)
- Lean declaration: [dvd_two_pow_sub_one_iff](../../ErdosProblems/Lift/AngleA4.lean#L574)

- outgoing **complements**: [Z87::the_period_lift_is_exactly_multiplication_by_the_mersenne_geometric_ratio](BROWSER_Z87_1.md#node-851b60d61e92c2e3). The scalar factorisation describes one rung, while lcm nesting and exact order identify which divisor periods and reciprocal denominators occur along the ladder.
- incoming **generated_by**: [Z87::one_rational_witness_passes_all_period_kills_through_sixty_six_and_fails_at_sixty_seven](BROWSER_Z87_1.md#node-1c6b39e3229d4f4e). The proof uses period-lcm nesting and the order-67 divisibility criterion to transport the rational witness across every lower rung.

<a id="node-59a4cdaf7082ee3b"></a>
## new_reciprocal_denominators_disprove_the_scalar_lift_for_arbitrary_reals

Let q>1 be odd. If q does not divide 2^h-1, then 1/q kills period h; if q divides 2^h-1, then 1/q does not kill period h. Hence whenever q divides 2^(pH)-1 but not 2^H-1, the same real number 1/q kills H and fails to kill pH. In particular 1/11 kills periodLcm(4)=12 and fails at periodLcm(5)=60.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This refutes the lift only as a general implication about arbitrary real numbers. It does not show that the concrete totient series fails a lift, lacks extra arithmetic structure, or is rational.

- Lean declaration: [killsPeriod_one_div](../../ErdosProblems/Lift/AngleA4.lean#L489)
- Lean declaration: [not_killsPeriod_one_div](../../ErdosProblems/Lift/AngleA4.lean#L510)
- Lean declaration: [killsPeriod_lift_fails](../../ErdosProblems/Lift/AngleA4.lean#L528)
- Lean declaration: [lift_fails_periodLcm_four_to_five](../../ErdosProblems/Lift/AngleA4.lean#L542)

- outgoing **barrier_for**: [Z87::the_period_lift_is_exactly_multiplication_by_the_mersenne_geometric_ratio](BROWSER_Z87_1.md#node-851b60d61e92c2e3). Reciprocals whose denominator divides the new Mersenne ratio make the multiplied coordinate integral even though the lower-period coordinate is nonintegral.
- incoming **finite_instance_of**: [Z87::one_rational_witness_passes_all_period_kills_through_sixty_six_and_fails_at_sixty_seven](BROWSER_Z87_1.md#node-1c6b39e3229d4f4e). The frontier witness specializes the reciprocal-denominator counterexample to q=193707721 and the lcm-ladder transition into t=67.

<a id="node-1c6b39e3229d4f4e"></a>
## one_rational_witness_passes_all_period_kills_through_sixty_six_and_fails_at_sixty_seven

The integer q₆₇=193707721 divides 2^67-1; periodLcm(66)=1182266884102822267511361600 is not divisible by 67. Therefore 1/q₆₇ kills periodLcm(t) for every t≤66, but it does not kill periodLcm(67).

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The witness concerns an arbitrary rational number satisfying the same lower-rung conclusions, not the concrete totient series. It shows that lower-rung kill conclusions alone do not force the next rung, but it does not negate the independently certified t=67 totient-series cell.

- Lean declaration: [frontierWitness_dvd](../../ErdosProblems/Lift/AngleA4.lean#L600)
- Lean declaration: [periodLcm_66_val](../../ErdosProblems/Lift/AngleA4.lean#L605)
- Lean declaration: [not_dvd_67_periodLcm_66](../../ErdosProblems/Lift/AngleA4.lean#L607)
- Lean declaration: [frontierWitness_kills_upto_66](../../ErdosProblems/Lift/AngleA4.lean#L616)
- Lean declaration: [frontierWitness_fails_at_67](../../ErdosProblems/Lift/AngleA4.lean#L624)

- outgoing **finite_instance_of**: [Z87::new_reciprocal_denominators_disprove_the_scalar_lift_for_arbitrary_reals](BROWSER_Z87_1.md#node-59a4cdaf7082ee3b). The frontier witness specializes the reciprocal-denominator counterexample to q=193707721 and the lcm-ladder transition into t=67.
- outgoing **generated_by**: [Z87::lcm_nesting_and_multiplicative_order_locate_period_kill_transport](BROWSER_Z87_1.md#node-c7567e14d9ea0b0b). The proof uses period-lcm nesting and the order-67 divisibility criterion to transport the rational witness across every lower rung.
- incoming **complements**: [Z87::frontier_multiplier_lattice_defeats_the_bounded_depth_localisation_argument](BROWSER_Z87_1.md#node-f4620f495f80de1c). The fixed rational witness gives an exact logical counterexample, while the lattice theorem quantifies why the associated frontier multiplier remains dense at bounded localization depth.

<a id="node-f9a77bc8e42f4eee"></a>
## period_killing_is_a_faithful_conditional_reduction_to_irrationality

For each period h, killsPeriod(S,h)—nonintegrality of every dyadic multiple 2^N(2^h-1)S—is equivalent to the existence, for every position N, of some certifiedKill(h,N,L). If killsPeriod(S,h) holds for every positive h, then the binary totient series S is irrational.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is a faithful conditional reduction, not an unconditional irrationality theorem. The global period-kill hypothesis remains unsupplied and is not weakened by changing coordinates.

Open hypotheses: ["Prove killsPeriod(totientSeries,h) for every positive period h, equivalently supply a certified kill at every position of every positive period."]

- Lean declaration: [killsPeriod_iff](../../ErdosProblems/Lift/AngleA4.lean#L410)
- Lean declaration: [irrational_of_killsPeriod](../../ErdosProblems/Lift/AngleA4.lean#L418)

- outgoing **generated_by**: [Z87::window_approximation_makes_certified_kill_and_tail_nonintegrality_pointwise_equivalent](BROWSER_Z87_1.md#node-008e44a3026f78a6). The period-wide equivalence applies the pointwise certificate/nonintegrality equivalence at every position before invoking the certificate-supply irrationality criterion.

<a id="node-4e12f91646e10292"></a>
## tail_differences_form_a_dyadic_affine_orbit_with_upward_closed_integrality

Write R_N for the shifted totient tail, D_(h,N)=R_(N+h)-R_N, and S for the binary totient series. Then R_(N+1)=2R_N-φ(N+1), D_(h,N+1)=2D_(h,N)-(φ(N+h+1)-φ(N+1)), integrality of D_(h,N) propagates to every later position, and D_(h,N+k)-2^kD_(h,N) is an integer. Moreover D_(h,N)=2^N(2^h-1)S-(Φ_(N+h)-Φ_N), so D_(h,N) is integral exactly when 2^N(2^h-1)S is integral.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The identities and transport laws do not show that any displayed quantity is nonintegral. Upward closure of integrality makes later positions harder for certificates; it supplies no certificate, period lift, cofinal family, or irrationality result.

- Lean declaration: [totientTail_succ](../../ErdosProblems/Lift/AngleA4.lean#L133)
- Lean declaration: [tailDiff_succ](../../ErdosProblems/Lift/AngleA4.lean#L156)
- Lean declaration: [tailDiff_mem_int_succ](../../ErdosProblems/Lift/AngleA4.lean#L168)
- Lean declaration: [tailDiff_mem_int_mono](../../ErdosProblems/Lift/AngleA4.lean#L178)
- Lean declaration: [tailDiff_shift_mod_int](../../ErdosProblems/Lift/AngleA4.lean#L188)
- Lean declaration: [tailDiff_eq](../../ErdosProblems/Lift/AngleA4.lean#L203)
- Lean declaration: [tailDiff_mem_int_iff](../../ErdosProblems/Lift/AngleA4.lean#L220)

- incoming **generated_by**: [Z87::window_approximation_makes_certified_kill_and_tail_nonintegrality_pointwise_equivalent](BROWSER_Z87_1.md#node-008e44a3026f78a6). The round trip uses the exact tail-difference coordinate, its integrality interpretation, and its monotonic position orbit.
- incoming **generated_by**: [Z87::the_period_lift_is_exactly_multiplication_by_the_mersenne_geometric_ratio](BROWSER_Z87_1.md#node-851b60d61e92c2e3). The additive lift congruence subtracts the two closed tail-difference formulas and uses the exact Mersenne-ratio factorisation.

<a id="node-851b60d61e92c2e3"></a>
## the_period_lift_is_exactly_multiplication_by_the_mersenne_geometric_ratio

For M=mersenneRatio(p,H)=∑_{i<p}2^(Hi), one has M(2^H-1)=2^(pH)-1. Thus killsPeriod(x,pH) is equivalent to nonintegrality, for every N, of M·(2^N(2^H-1)x); for the totient tail, D_(pH,N)-M·D_(H,N) is an integer.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem identifies the lift's scalar multiplier but does not prove that nonintegrality survives multiplication by M. In particular it supplies no implication from a killed H-cell to a killed pH-cell for the concrete totient series.

- Lean declaration: [mersenneRatio_mul](../../ErdosProblems/Lift/AngleA4.lean#L429)
- Lean declaration: [killsPeriod_lift_iff](../../ErdosProblems/Lift/AngleA4.lean#L443)
- Lean declaration: [tailDiff_lift_mod_int](../../ErdosProblems/Lift/AngleA4.lean#L461)

- outgoing **generated_by**: [Z87::tail_differences_form_a_dyadic_affine_orbit_with_upward_closed_integrality](BROWSER_Z87_1.md#node-4e12f91646e10292). The additive lift congruence subtracts the two closed tail-difference formulas and uses the exact Mersenne-ratio factorisation.
- incoming **barrier_for**: [Z87::new_reciprocal_denominators_disprove_the_scalar_lift_for_arbitrary_reals](BROWSER_Z87_1.md#node-59a4cdaf7082ee3b). Reciprocals whose denominator divides the new Mersenne ratio make the multiplied coordinate integral even though the lower-period coordinate is nonintegral.
- incoming **complements**: [Z87::lcm_nesting_and_multiplicative_order_locate_period_kill_transport](BROWSER_Z87_1.md#node-c7567e14d9ea0b0b). The scalar factorisation describes one rung, while lcm nesting and exact order identify which divisor periods and reciprocal denominators occur along the ladder.
- incoming **barrier_for**: [Z87::frontier_multiplier_lattice_defeats_the_bounded_depth_localisation_argument](BROWSER_Z87_1.md#node-f4620f495f80de1c). The multiplier lattice is exactly the set where the scalar lift conclusion fails, and the density estimate shows bounded-depth localization cannot exclude that set by radius alone.

<a id="node-008e44a3026f78a6"></a>
## window_approximation_makes_certified_kill_and_tail_nonintegrality_pointwise_equivalent

For every h,N,L, the window discrepancy approximates 2^L D_(h,N) with error at most N+h+L+2. Linear-over-exponential decay supplies a depth at which this error is smaller than the distance of a nonintegral D_(h,N) from the integers, while failure of a depth-L residue certificate places the discrepancy near a multiple of 2^L. Consequently D_(h,N) nonintegral produces some certifiedKill(h,N,L), and some such certificate exists exactly when 2^N(2^h-1)S is nonintegral. At fixed h, existence of a certificate at N implies existence at every earlier M≤N.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The depth is existential and not a uniform or effective bound across h,N. Pointwise equivalence does not show nonintegrality at any cell, does not provide cofinally many killed periods, and does not prove irrationality on its own.

- Lean declaration: [tailDiff_approx](../../ErdosProblems/Lift/AngleA4.lean#L240)
- Lean declaration: [exists_depth](../../ErdosProblems/Lift/AngleA4.lean#L278)
- Lean declaration: [exists_near_multiple](../../ErdosProblems/Lift/AngleA4.lean#L301)
- Lean declaration: [exists_certifiedKill_of_tailDiff_notMem_int](../../ErdosProblems/Lift/AngleA4.lean#L325)
- Lean declaration: [exists_certifiedKill_iff](../../ErdosProblems/Lift/AngleA4.lean#L383)
- Lean declaration: [exists_certifiedKill_antitone](../../ErdosProblems/Lift/AngleA4.lean#L398)

- outgoing **generated_by**: [Z87::tail_differences_form_a_dyadic_affine_orbit_with_upward_closed_integrality](BROWSER_Z87_1.md#node-4e12f91646e10292). The round trip uses the exact tail-difference coordinate, its integrality interpretation, and its monotonic position orbit.
- incoming **generated_by**: [Z87::period_killing_is_a_faithful_conditional_reduction_to_irrationality](BROWSER_Z87_1.md#node-f9a77bc8e42f4eee). The period-wide equivalence applies the pointwise certificate/nonintegrality equivalence at every position before invoking the certificate-supply irrationality criterion.

