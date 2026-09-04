# Z17_1: Neighbouring Erdos problems (#243, #251, #269, #1049) and the problem-owned library root

[All problems and zones](BROWSER.md)

<a id="node-7f708faae54a5953"></a>
## n1049_cleared_tail_recurrence

Exact rational-base cleared-tail recurrence: with prefix sum of coeff(m+1) s^(m+1)/r^(m+1) and cleared tail B r^N (F - prefix), one has cleared(N+1) = r * cleared(N) - B coeff(N+1) s^(N+1). The forcing term carries the factor s^(N+1), which is the denominator-base tax absent from the integer-base case s = 1.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [rationalBaseClearedTailQ_succ](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L187)
- Lean declaration: [rationalBasePrefixQ_succ](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L173)

- incoming **reformulates**: [Z17::n1049_forcing_term_growth](BROWSER_Z17_1.md#node-ef3ddd09d41bbf8a). The natural-valued forcing magnitude is the N-indexed shadow of the inhomogeneous term B * coeff(N+1) * s^(N+1) in the cleared recurrence.
- outgoing **transport_of**: [Z11::binary_tail_shift_identity](BROWSER_Z11_1.md#node-51b4e0f463db1e09). rationalBaseClearedTailQ_succ gives cleared(N+1) = r*cleared(N) - B*coeff(N+1)*s^(N+1), which collapses at s = 1 (rationalBaseForcingNat_one) to the integer-base tail recurrence binaryCoeffTail_succ; the factor s^(N+1) is the denominator-base tax.
- incoming **specialises**: [Z11::binary_tail_shift_identity](BROWSER_Z11_1.md#node-51b4e0f463db1e09). Z17's `ErdosProblems.Erdos1049.rationalBaseClearedTailQ_succ` gives cleared(N+1) = r cleared(N) - B coeff(N+1) s^(N+1) for a rational base r/s; at (r,s,B) = (2,1,1) this is Z11's `binaryCoeffTail_succ` T(N+1) = 2 T(N) - c(N+1), the s = 1 collapse being recorded by `ErdosProblems.Erdos1049.rationalBaseForcingNat_one`.

<a id="node-32f6ed0f441257b9"></a>
## n1049_coordinatewise_corridor_definition

The coordinatewise rational-base corridor for natural parameters (a,b,N,K,Q,digit) is exactly the conjunction a > 0, Q > 0, digit > 0, digit <= N+K, a^K divides Q*digit, and Q*b^(N+K+1) < a^(K+1). It packages the simultaneous coordinate-clearing divisibility and subunit tail estimate used in the elementary rational-base obstruction.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is a predicate, not an existence theorem. It neither supplies a corridor nor asserts anything about the Lambert series value; the separate no-go theorem excludes only this literal corridor shape at base 3/2.

- Lean declaration: [CoordinatewiseCorridor](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L113)


<a id="node-1d6245e723f6e572"></a>
## n1049_corridor_power_vs_linear

If a coordinatewise rational-base corridor holds with numerator base a and denominator base b, i.e. a^K divides Q*digit with 0 < digit <= N+K and Q b^(N+K+1) < a^(K+1), then b^(N+K+1) < a (N+K): the corridor converts into a power-versus-linear inequality.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [coordinatewiseCorridor_implies_pow_lt_linear](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L121)

- outgoing **implies**: [Z17::n1049_three_halves_barrier](BROWSER_Z17_1.md#node-2f70395be8f6b4ad). The 3/2 no-go is the power-versus-linear transport combined with 3x < 2^(x+1).

<a id="node-ef3ddd09d41bbf8a"></a>
## n1049_forcing_term_growth

For denominator base s >= 2, positive B and positive coefficients, the natural-valued forcing magnitude B * coeff(N+1) * s^(N+1) is at least 2^(N+1); in the integer-base case s = 1 it collapses to B * coeff(N+1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: A monotonicity of powers under s >= 2, 1 <= B, 1 <= coeff (N+1). It quantifies the denominator-base tax and nothing else: no convergence, no positivity of any remainder, and no irrationality follows, and the coefficients are abstract rather than the actual divisor function.

- Lean declaration: [twoPow_le_rationalBaseForcingNat](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L204)
- Lean declaration: [rationalBaseForcingNat_one](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L218)

- outgoing **reformulates**: [Z17::n1049_cleared_tail_recurrence](BROWSER_Z17_1.md#node-7f708faae54a5953). The natural-valued forcing magnitude is the N-indexed shadow of the inhomogeneous term B * coeff(N+1) * s^(N+1) in the cleared recurrence.

<a id="node-674454f54ac6dbe3"></a>
## n1049_pade_exponent_bounds

Doubled denominator-exponent bookkeeping for the rational Pade homogenisation: for 0 <= k <= n the doubled P-summand exponent 2(k(n-k) + nk) + k(k-1) never exceeds 3n^2 - n, the gap factoring as (n-k)(3n-k-1); the doubled Q-maximum satisfies the exact gap identity 3n^2 - n - Qmax = 2(n + m(m-1)), hence is also bounded by 3n^2 - n whenever m >= 1.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Denominator-exponent bookkeeping only, over Z with every exponent doubled to avoid floors and parity. The module states that positivity of the Pade remainder and its asymptotics remain separate analytic obligations; neither is formalised here or elsewhere in the corpus, so no Pade irrationality argument is closed by these inequalities. The Q-bound additionally needs m >= 1, so the m = 0 summand is not covered.

- Lean declaration: [rationalPadePSummandDenExpTwice_le](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L30)
- Lean declaration: [rationalPadeQMaxDenExpTwice_gap](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L52)
- Lean declaration: [rationalPadeQMaxDenExpTwice_le](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L60)


<a id="node-ab52746fa01b3cc1"></a>
## n1049_pade_exponent_coordinates

The doubled rational-Pade denominator coordinates are defined over the integers by E~(n) = 3n^2-n for the proposed common exponent, P~(n,k) = 2(k(n-k)+nk)+k(k-1) for a homogenised P summand, and, with j=n-m-1, Q~(n,m) = 2(n^2-n)+j^2+2jm+j-m^2+3m for the maximal Q-summand exponent.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: These definitions contain only exponent bookkeeping. They do not prove coefficient integrality, derive the expressions from a Pade construction, establish nonvanishing or positivity of a remainder, control its decay, or imply irrationality.

- Lean declaration: [rationalPadeDenExpTwice](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L19)
- Lean declaration: [rationalPadePSummandDenExpTwice](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L24)
- Lean declaration: [rationalPadeQMaxDenExpTwice](../../ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L46)


<a id="node-fc349e7d374ec745"></a>
## n1049_rational_base_forcing_magnitude

For natural denominator base s, clearing multiplier B, coefficient sequence c and cutoff N, the natural forcing magnitude is exactly G_N = B*c(N+1)*s^(N+1), the inhomogeneous term whose size is compared across integer and noninteger denominator bases.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The definition imposes no positivity assumptions and proves no growth by itself. Its exponential lower bound for s >= 2 and collapse at s = 1 are separate theorems.

- Lean declaration: [rationalBaseForcingNat](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L198)


<a id="node-e96c683c0cd27165"></a>
## n1049_rational_base_tail_coordinates

For rational r,s, an abstract coefficient sequence c and cutoff N, the rational-base prefix is P_N = sum over 0 <= m < N of c(m+1)*s^(m+1)/r^(m+1). Given rational B and a putative value F, the corresponding cleared-tail coordinate is U_N = B*r^N*(F-P_N).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These are definitions for an arbitrary rational F and abstract coefficients. They do not identify F with an infinite Lambert series, prove convergence, make U_N integral or bounded, or establish irrationality.

- Lean declaration: [rationalBasePrefixQ](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L168)
- Lean declaration: [rationalBaseClearedTailQ](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L181)


<a id="node-11c92ca57c31808c"></a>
## n1049_seven_halves_certificates

Two exact arithmetic facts supporting the published 7/2 lane: 2^18 < 7^7, and 7/18 = 1/2 - 1/9 as rationals.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: These are two norm_num facts (2^18 < 7^7 and 7/18 = 1/2 - 1/9). They do not formalise Bundschuh-Vaananen, do not establish log 2 / log 7 < 7/18 (the logarithmic monotonicity step is deliberately outside the module), do not supply 3 < pi, and do not establish irrationality of the Lambert value at base 7/2 or at any other base. No irrationality statement about 7/2 exists in Lean anywhere in this corpus.

- Lean declaration: [sevenHalves_power_certificate](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L32)
- Lean declaration: [sevenHalves_rational_margin](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L36)

- outgoing **depends_on_open**: [Z17::n1049_three_halves_barrier](BROWSER_Z17_1.md#node-2f70395be8f6b4ad). Not a logical dependency between the two nodes: the 7/2 lane rests on the published Bundschuh-Vaananen theorem, which is cited but not formalised anywhere in the corpus and has no node of its own, while the 3/2 barrier rules out only the coordinatewise corridor transfer. The relation records that neither lane produces irrationality inside the corpus.

<a id="node-2f70395be8f6b4ad"></a>
## n1049_three_halves_barrier

At base 3/2 no coordinatewise corridor can occur once both the shift N and the cleared window K are at least one, because exponential growth 2^(N+K+1) already beats 3(N+K).

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rules out only the literal coordinatewise transfer of the integer-base Erdos corridor at the single base 3/2, and only when N >= 1 and K >= 1. It does not assert or deny irrationality of the sum over n of 1/((3/2)^n - 1), does not touch the unrestricted rational-base conjecture, and does not rule out blockwise, multi-digit, Pade or any non-coordinatewise corridor at 3/2, nor corridors at other rational bases (the published 7/2 lane is untouched).

- Lean declaration: [threeHalves_no_coordinatewiseCorridor](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L155)
- Lean declaration: [three_mul_lt_two_pow_succ](../../ErdosProblems/Erdos1049/RationalBaseLambert.lean#L142)

- incoming **implies**: [Z17::n1049_corridor_power_vs_linear](BROWSER_Z17_1.md#node-1d6245e723f6e572). The 3/2 no-go is the power-versus-linear transport combined with 3x < 2^(x+1).
- incoming **depends_on_open**: [Z17::n1049_seven_halves_certificates](BROWSER_Z17_1.md#node-11c92ca57c31808c). Not a logical dependency between the two nodes: the 7/2 lane rests on the published Bundschuh-Vaananen theorem, which is cited but not formalised anywhere in the corpus and has no node of its own, while the 3/2 barrier rules out only the coordinatewise corridor transfer. The relation records that neither lane produces irrationality inside the corpus.
- outgoing **barrier_for**: [Z01::generic_coefficient_certificate_engine](BROWSER_Z01_1.md#node-347d00f05c4a588d). The coordinatewise corridor predicate (a^K divides Q*digit, 0 < digit <= N+K, Q*b^(N+K+1) < a^(K+1)) is the rational-base transcription of this engine's three clauses - first-block divisibility, the c(m) <= m growth envelope, and the height inequality. ErdosProblems.Erdos1049.threeHalves_no_coordinatewiseCorridor shows it has no instance at base 3/2 once N >= 1 and K >= 1, via n1049_corridor_power_vs_linear. Scope: only the literal coordinatewise transfer at 3/2; the identification of the corridor with this engine's schema is a reviewed reading of the two Lean shapes, not a proved equivalence.
- outgoing **transport_of**: [Z01::divisor_block_certificate_engine](BROWSER_Z01_1.md#node-82d682802aaa267c). Reviewed judgement, not a Lean bridge: the coordinatewise corridor a^K | Q*digit with Q*b^(N+K+1) < a^(K+1) is the rational-base transcription of the divisibility-plus-height pair of a digitwise block certificate; no Lean declaration ties coordinatewiseCorridor to the CertificateKernel schema.

<a id="node-8f6a187ae0408c62"></a>
## n243_bounded_rise_barrier

A sequence of naturals tending to infinity cannot have uniformly bounded upward increments while permanently avoiding infinitely many fresh pairwise-coprime moduli; in particular no reduced exact tail whose numerator tends to infinity can have a uniformly bounded rise, in the strict or the eventual form.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rules out only the bounded-rise regime for a reduced tail that is already known to tend to infinity. It does not rule out unbounded upward increments, tails that do not tend to infinity, orbits whose reduction fails to be coprime at every index, or any behaviour of the actual reciprocal series (which is never formed). It also says nothing once the gcd fails to stabilise, since the reduction step needs a fixed common divisor.

- Lean declaration: [no_boundedRise_of_tailAvoidance](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L897)
- Lean declaration: [no_boundedRise_reducedTail](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1035)
- Lean declaration: [no_eventuallyBoundedRise_reducedTail](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1060)

- incoming **implies**: [Z17::n243_crt_forbidden_block](BROWSER_Z17_1.md#node-de1840a0772feabe). The shifted CRT block supplies the forbidden window that a bounded-rise sequence would have to jump over.
- incoming **implies**: [Z17::n243_reduced_tail_coprimality](BROWSER_Z17_1.md#node-8a3a81bd0d3f3c7e). Pairwise coprimality of the multipliers and whole-modulus avoidance are the two arithmetic inputs the abstract avoidance no-go requires.
- outgoing **implies**: [Z17::n243_no_cofinally_bounded_negative](BROWSER_Z17_1.md#node-6cb028631d8c269c). After reduction, the bounded-rise no-go is applied to the reduced numerator.

<a id="node-3b469b7714b83e6c"></a>
## n243_boundednegative_rigidity

Headline of the #243 module: for an exact natural orbit with a(n) > 1, positive tail state, strict centering |E(n)| < C(n), a uniform lower bound -B <= E(n), and division-free normalized vanishing of E relative to C, the centered error vanishes from some index onward. An eventual form allows the centering and the lower bound to start at different indices.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hvanish : forall K, exists N, forall n, N <= n -> K * Int.natAbs (E n) < C n  (division-free normalized vanishing; the dominant unproved input)", "hbound : forall n, -(B : Int) <= E n  (bounded negative part of the centered error)", "hcentered : forall n, Int.natAbs (E n) < C n  (strict centering of the representative)"]

- Lean declaration: [boundedNegativePart_eventually_zero](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2265)
- Lean declaration: [eventuallyBoundedNegativePart_eventually_zero](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2352)

- incoming **implies**: [Z17::n243_zero_absorbing](BROWSER_Z17_1.md#node-8ed97fdab48db8b8). Absorption of zero is the first ingredient of the two-branch wrapper.
- incoming **implies**: [Z17::n243_centered_eventually_zero](BROWSER_Z17_1.md#node-4d08b6f8783fb55b). The eventually-nonnegative branch of the wrapper is discharged by monotone stabilisation.
- incoming **implies**: [Z17::n243_no_cofinally_bounded_negative](BROWSER_Z17_1.md#node-6cb028631d8c269c). The cofinally-negative branch of the wrapper is discharged by the CRT route.
- outgoing **implies**: [Z17::n243_sylvester_from_vanishing](BROWSER_Z17_1.md#node-c6955bb4d7727994). Eventual vanishing of the centered error feeds the Sylvester-step conversion, which is the #243 rigidity conclusion, but only under the wrapper's three unproved hypotheses.

<a id="node-4d08b6f8783fb55b"></a>
## n243_centered_eventually_zero

If naturals satisfy C(n+1) + E(n) = C(n), then C is nonincreasing, hence eventually constant, and the nonnegative errors E vanish from some index onward.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [centeredState_eventually_zero](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1837)
- Lean declaration: [antitone_nat_eventually_constant](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1819)

- outgoing **implies**: [Z17::n243_boundednegative_rigidity](BROWSER_Z17_1.md#node-3b469b7714b83e6c). The eventually-nonnegative branch of the wrapper is discharged by monotone stabilisation.

<a id="node-88d7343f7122abe3"></a>
## n243_constant_negative_excluded

There is no infinite orbit of naturals with a(n) >= 2, D(n+1) = a(n) D(n) and a constant negative centered error, i.e. with D(n) + m = (a(n) - 1) (c + n m) for a fixed positive magnitude m and any initial tail state c; the same holds from any starting index onward. No growth condition on a is assumed.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Excludes only the exactly-constant negative centered magnitude m, in the exact integer system (multiplicative denominator update plus the shape equation) with a n >= 2. It says nothing about variable, eventually-variable or cofinally-bounded negative magnitudes, which is where the live #243 obstruction sits, and the reciprocal series sum 1/a n is never formed in Lean in this zone, so no irrationality statement is touched.

- Lean declaration: [no_normalizedConstantNegative_orbit](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L100)
- Lean declaration: [no_scalePrimitiveConstantNegative_orbit](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L147)
- Lean declaration: [no_constantNegative_orbit](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L286)
- Lean declaration: [no_eventuallyConstantNegative_orbit](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L350)

- outgoing **barrier_for**: [Z17::n243_finite_horizon_residue](BROWSER_Z17_1.md#node-bc429b291b277120). The finite-horizon residue machinery searches exactly the normalized E = -1, C0 = 1 branch whose infinite orbits no_normalizedConstantNegative_orbit rules out unconditionally. It bounds the search, it does not empty it: survivors exist at every finite horizon h, and what is excluded is only an infinite surviving orbit.
- incoming **generalises**: [Z17::n243_periodic_negative_excluded](BROWSER_Z17_1.md#node-bad7807347c97f27). Period-h version of the same divisor-lock plus pigeonhole argument, but it adds the regime hypothesis e(n) < a(n), so it does not strictly subsume the constant case.

<a id="node-de1840a0772feabe"></a>
## n243_crt_forbidden_block

Given finitely many pairwise-coprime moduli each greater than one, there are consecutive integers x, x+1, ..., x+k-1 with the i-th divisible by the i-th modulus, and the block can be pushed beyond any prescribed bound.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [exists_shifted_consecutiveMultiples](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L833)

- outgoing **implies**: [Z17::n243_bounded_rise_barrier](BROWSER_Z17_1.md#node-8f6a187ae0408c62). The shifted CRT block supplies the forbidden window that a bounded-rise sequence would have to jump over.

<a id="node-537d1b1415ef72f1"></a>
## n243_defect_identity

Exact defect identity: (a' - (a^2 - a + 1)) * (a C - D) = a^2 (D - (a-1) C) - (D' - (a'-1) C') for the one-step images D' = a D, C' = a C - D. In words, the Sylvester defect times the next tail state equals a^2 times the current centered error minus the next centered error.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [sylvesterDefect_mul_nextTailState](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1769)

- outgoing **implies**: [Z17::n243_sylvester_from_vanishing](BROWSER_Z17_1.md#node-c6955bb4d7727994). The Sylvester step is extracted by cancelling a nonzero cofactor in the defect identity.
- outgoing **implies**: [Z17::n243_zero_absorbing](BROWSER_Z17_1.md#node-8ed97fdab48db8b8). The same identity makes C(n+1) divide E(n+1), which is what makes zero absorbing under strict centering.

<a id="node-c4cb4509aa3a79ea"></a>
## n243_divisor_lock_propagation

Divisor propagation in the product-cleared orbit: every multiplier a(j) divides every strictly later denominator state D(k) for j < k; if a prime p divides both the current denominator state and the current multiplier then the shape equation D + e = (a-1) C together with C(n+1) = C(n) + e(n) forces p into the next tail state; and once p divides D(N) and C(N) it divides D(n), C(n) and e(n) at every later index n >= N.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Statements about the exact integer recurrence system only (multiplicative denominator update, additive tail update, shape equation). Nothing here produces a divisor to lock, exhibits any concrete orbit, or touches the reciprocal series sum 1/a(n), which is never formed anywhere in this zone.

- Lean declaration: [base_dvd_denState_later](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L382)
- Lean declaration: [divisorLocksTailSucc](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L402)
- Lean declaration: [divisorLock_persists](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L429)

- outgoing **implies**: [Z17::n243_periodic_negative_excluded](BROWSER_Z17_1.md#node-bad7807347c97f27). base_dvd_denState_later, divisorLocksTailSucc and divisorLock_persists are the three lemmas repeatedDivisor_forces_periodicCommonScale consumes at lines 503, 505 and 510 to turn a repeated prime divisor of the period drift into a common scale; base_dvd_denState_later is also reused by the reduced-tail coprimality lemmas.

<a id="node-bc429b291b277120"></a>
## n243_finite_horizon_residue

Survival through h forced divisions of the map a -> ((n+1)a^2 - (n+2)a + (n+3))/(n+2) depends only on the initial state modulo the ascending-factorial horizon modulus, which at the initial index equals (h+1)!.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: forcedSurvives_iff_of_modEq_factorial converts the question 'does this state survive h forced divisions' into the question 'does its class mod (h+1)! survive', i.e. it makes a fixed finite horizon decidable. It is not a statement about the actual #243 objects: the module docstring states explicitly that the result is finite-horizon only and 'neither constructs an infinite negative-state orbit nor rules one out'. Survivors do exist at every finite horizon; only the infinite orbit is excluded, and that exclusion comes from n243_constant_negative_excluded, not from here.

- Lean declaration: [forcedSurvives_iff_of_modEq](../../ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L97)
- Lean declaration: [forcedSurvives_iff_of_modEq_factorial](../../ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L134)
- Lean declaration: [horizonModulus_eq_ascFactorial](../../ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L59)
- Lean declaration: [horizonModulus_zero_eq_factorial](../../ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L69)

- incoming **barrier_for**: [Z17::n243_constant_negative_excluded](BROWSER_Z17_1.md#node-88d7343f7122abe3). The finite-horizon residue machinery searches exactly the normalized E = -1, C0 = 1 branch whose infinite orbits no_normalizedConstantNegative_orbit rules out unconditionally. It bounds the search, it does not empty it: survivors exist at every finite horizon h, and what is excluded is only an infinite surviving orbit.

<a id="node-fea4fe4150324bcf"></a>
## n243_gcd_stabilises

If the exact orbit has cofinally many indices carrying a positive negative-state magnitude bounded by B, then the tail gcd is eventually constant. (The general ingredient is that a positive divisibility chain with cofinally bounded values is eventually constant.)

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hnegative : forall n, exists t e, n <= t and 0 < e and e <= B and D t + e = (a t - 1) * C t  (cofinally many uniformly bounded negative-state magnitudes; nothing in the corpus produces such indices for any actual reciprocal tail)"]

- Lean declaration: [tailGcd_eventuallyConstant_of_cofinally_boundedNegative](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1630)
- Lean declaration: [dvdChain_eventuallyConstant_of_cofinally_bounded](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1599)

- incoming **implies**: [Z17::n243_tailgcd_chain](BROWSER_Z17_1.md#node-f2322bcb3bc0273f). The tail gcd is a divisibility chain and equals gcd(C, e) at negative indices, which is what turns bounded magnitudes into bounded chain values.
- outgoing **implies**: [Z17::n243_no_cofinally_bounded_negative](BROWSER_Z17_1.md#node-6cb028631d8c269c). Stabilisation of the gcd is what lets the orbit be divided down to a reduced tail with coprime states.

<a id="node-c0f7f494b0545cb7"></a>
## n243_nat_int_transport

The natural product-cleared recurrences realise the integer state maps: casting the natural tail and denominator recurrences gives exactly nextTailState and nextDenState, and hence the signed identity C(n+1) = C(n) - E(n) over the integers.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [natTail_eq_nextTailState](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1863)
- Lean declaration: [natDen_eq_nextDenState](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1875)
- Lean declaration: [natTail_eq_sub_centeredState](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1972)


<a id="node-6cb028631d8c269c"></a>
## n243_no_cofinally_bounded_negative

An exact orbit whose tail state tends to infinity, whose one-step rise is bounded by B, and which has cofinally many negative-state magnitudes in (0, B], is contradictory; the divergence of the tail state may itself be supplied by division-free normalized vanishing of a positive magnitude sequence.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hRise : forall n, C (n + 1) <= C n + B  (uniformly bounded upward tail rise)", "hnegative : forall n, exists t e, n <= t and 0 < e and e <= B and D t + e = (a t - 1) * C t  (cofinally bounded negative excursions)", "hCTop : Filter.Tendsto C Filter.atTop Filter.atTop, or in the second form hvanish : forall K, exists N, forall n >= N, K * magnitude n < C n"]

- Lean declaration: [no_cofinallyBoundedNegative_of_tailTendsto](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1655)
- Lean declaration: [no_cofinallyBoundedNegative_of_normalizedVanishes](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1748)
- Lean declaration: [tailState_tendsto_atTop_of_nonzero_normalizedVanishes](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1733)

- incoming **implies**: [Z17::n243_gcd_stabilises](BROWSER_Z17_1.md#node-fea4fe4150324bcf). Stabilisation of the gcd is what lets the orbit be divided down to a reduced tail with coprime states.
- incoming **implies**: [Z17::n243_bounded_rise_barrier](BROWSER_Z17_1.md#node-8f6a187ae0408c62). After reduction, the bounded-rise no-go is applied to the reduced numerator.
- outgoing **implies**: [Z17::n243_boundednegative_rigidity](BROWSER_Z17_1.md#node-3b469b7714b83e6c). The cofinally-negative branch of the wrapper is discharged by the CRT route.

<a id="node-bad7807347c97f27"></a>
## n243_periodic_negative_excluded

There is no orbit with a(n) >= 2, a positive negative-magnitude sequence e that is periodic with period h and satisfies e(n) < a(n) pointwise, together with a fixed positive drift M of the tail state over one period and the exact shape equation D(n) + e(n) = (a(n) - 1) C(n); the eventual version holds too.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Closes only the exactly-periodic branch inside the natural tail regime. The Lean requires helt : forall n, e n < a n (a multiplier never divides its own phase magnitude), hepos : forall n, 0 < e n, exact periodicity e (n + h) = e n and a constant phase drift C (n + h) = C n + M with 0 < M. It therefore does not exclude aperiodic negative magnitudes, magnitudes with e n >= a n, magnitudes that are only approximately periodic, or the cofinally-bounded-negative branch that n243_no_cofinally_bounded_negative still leaves conditional. Because of helt it does not subsume n243_constant_negative_excluded. The reciprocal series itself is never formed anywhere in this zone.

- Lean declaration: [no_phasePrimitivePeriodicNegative_orbit](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L548)
- Lean declaration: [no_periodicNegative_orbit](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L690)
- Lean declaration: [no_eventuallyPeriodicNegative_orbit](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L796)
- Lean declaration: [repeatedDivisor_forces_periodicCommonScale](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L494)

- incoming **implies**: [Z17::n243_divisor_lock_propagation](BROWSER_Z17_1.md#node-c4cb4509aa3a79ea). base_dvd_denState_later, divisorLocksTailSucc and divisorLock_persists are the three lemmas repeatedDivisor_forces_periodicCommonScale consumes at lines 503, 505 and 510 to turn a repeated prime divisor of the period drift into a common scale; base_dvd_denState_later is also reused by the reduced-tail coprimality lemmas.
- outgoing **generalises**: [Z17::n243_constant_negative_excluded](BROWSER_Z17_1.md#node-88d7343f7122abe3). Period-h version of the same divisor-lock plus pigeonhole argument, but it adds the regime hypothesis e(n) < a(n), so it does not strictly subsume the constant case.

<a id="node-8a3a81bd0d3f3c7e"></a>
## n243_reduced_tail_coprimality

Along a reduced exact tail (coprime numerator and denominator at every index, with u(n+1) + v(n) = a(n) u(n) and v(n+1) = a(n) v(n)), the multipliers at distinct indices are pairwise coprime and every earlier multiplier is coprime to every later numerator.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [reducedTail_pairwiseCoprime](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1010)
- Lean declaration: [reducedTail_wholeModulusAvoidance](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1024)
- Lean declaration: [reducedStep_coprime_currentFactor](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L983)

- outgoing **implies**: [Z17::n243_bounded_rise_barrier](BROWSER_Z17_1.md#node-8f6a187ae0408c62). Pairwise coprimality of the multipliers and whole-modulus avoidance are the two arithmetic inputs the abstract avoidance no-go requires.

<a id="node-202f1338bc419f9e"></a>
## n243_state_algebra

In the product-cleared reciprocal-tail system the next tail state is exactly the current one minus the centered error, C(n+1) = C(n) - E(n); and the whole system (denominator update, tail update, centered error) is equivariant under multiplying C and D by a common scale.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [nextTailState_eq_sub_centered](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L57)
- Lean declaration: [nextDenState_scale](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L65)
- Lean declaration: [nextTailState_scale](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L70)
- Lean declaration: [centeredState_scale](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L75)


<a id="node-c6955bb4d7727994"></a>
## n243_sylvester_from_vanishing

If two consecutive centered errors vanish and the next tail state is nonzero, then the multiplier takes the exact Sylvester step a' = a^2 - a + 1; along an exact orbit, eventual vanishing of the centered error together with eventual nonvanishing of the tail state gives the Sylvester recurrence from some index onward.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Unconditional as a conversion, but both of its inputs are supplied nowhere unconditionally: eventual vanishing of the centered state is only produced by n243_boundednegative_rigidity, which carries three unproved hypotheses (normalized vanishing, bounded negative part, strict centering), and eventual nonvanishing of the tail state is an outright assumption. Nothing in the zone therefore derives the Sylvester recurrence for any actual orbit, and the reciprocal series is never formed.

- Lean declaration: [sylvesterNext_eq_of_centered_zero](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1781)
- Lean declaration: [sylvesterNext_eventually_of_centered_zero](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1799)

- incoming **implies**: [Z17::n243_defect_identity](BROWSER_Z17_1.md#node-537d1b1415ef72f1). The Sylvester step is extracted by cancelling a nonzero cofactor in the defect identity.
- incoming **implies**: [Z17::n243_boundednegative_rigidity](BROWSER_Z17_1.md#node-3b469b7714b83e6c). Eventual vanishing of the centered error feeds the Sylvester-step conversion, which is the #243 rigidity conclusion, but only under the wrapper's three unproved hypotheses.

<a id="node-f2322bcb3bc0273f"></a>
## n243_tailgcd_chain

The tail gcd gcd(C(n), D(n)) divides its successor along an exact orbit, and at a negative-state index it equals gcd(C(n), e(n)), the gcd with the positive negative-state magnitude.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tailGcd_dvd_succ](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1424)
- Lean declaration: [tailGcd_eq_gcd_negativeMagnitude](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1581)

- outgoing **implies**: [Z17::n243_gcd_stabilises](BROWSER_Z17_1.md#node-fea4fe4150324bcf). The tail gcd is a divisibility chain and equals gcd(C, e) at negative indices, which is what turns bounded magnitudes into bounded chain values.

<a id="node-8ed97fdab48db8b8"></a>
## n243_zero_absorbing

In the strict-centering regime |E(n)| < C(n) for all n, a vanishing centered error is absorbing: E(n) = 0 forces E(n+1) = 0, because the defect identity makes C(n+1) divide E(n+1) and the only multiple of smaller absolute value is zero. Failure of eventual vanishing therefore makes every error on the tail nonzero.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The strict-centering hypothesis hcentered : forall n, Int.natAbs (E n) < C n is a free hypothesis of centeredState_zero_absorbing that is discharged nowhere in the corpus, and the very same hypothesis is listed as an open antecedent of n243_boundednegative_rigidity. It is recorded here as a regime normalisation (for an exact orbit the multiplier a n can be chosen so that E is a centred representative) rather than as an open input, but that choice is the only reason this node is not a conditional_implication. The theorem therefore says nothing about orbits outside the strictly centred regime, and no concrete orbit is exhibited inside it. eventually_nonzero_of_zero_absorbing is pure logic on an abstract E and carries no arithmetic at all.

- Lean declaration: [centeredState_zero_absorbing](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2221)
- Lean declaration: [eventually_nonzero_of_zero_absorbing](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2248)

- incoming **implies**: [Z17::n243_defect_identity](BROWSER_Z17_1.md#node-537d1b1415ef72f1). The same identity makes C(n+1) divide E(n+1), which is what makes zero absorbing under strict centering.
- outgoing **implies**: [Z17::n243_boundednegative_rigidity](BROWSER_Z17_1.md#node-3b469b7714b83e6c). Absorption of zero is the first ingredient of the two-branch wrapper.

<a id="node-1f1777114f52b839"></a>
## n251_euler_odd_denominator

If a rational has odd reduced denominator d then (2^phi(d) - 1) times it is an integer; consequently a tail state with odd reduced denominator has an integral shift after phi(d) steps.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [ratIntegral_totientMultiplier_of_odd_den](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L695)
- Lean declaration: [tailShift_integral_totient_of_odd_den](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L877)

- outgoing **specialises**: [Z17::n251_integrality_criterion](BROWSER_Z17_1.md#node-0102a98d308d7360). Euler's congruence instantiates the criterion at h = phi(den) when the denominator is odd.
- incoming **barrier_for**: [Z17::n251_free_carry_barrier](BROWSER_Z17_1.md#node-f3051b3e0ee128e4). The totient-shift integrality is exactly the kind of consequence a free integer carry satisfies without any periodicity, so the criterion cannot be run backwards to constrain the coefficient word.
- outgoing **transport_of**: [Z06::tail_period_law_from_rationality](BROWSER_Z06_2.md#node-2b462b01c608150a). ratIntegral_totientMultiplier_of_odd_den supplies the period phi(d) from the odd part of the reduced denominator, the same Euler-order mechanism that tail_diff_int_of_den_dvd uses to convert rationality into an integral shifted tail difference.

<a id="node-f3051b3e0ee128e4"></a>
## n251_free_carry_barrier

An arbitrary integer carry sequence K emits the dyadic coefficients 2K(n) - K(n+1) whose partial sums telescope exactly to K(0) - K(n)/2^n. Hence a rational dyadic value is compatible with a completely unconstrained, in particular non-periodic, coefficient stream; rationality alone cannot force eventual periodicity or automaticity of the coefficient word.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The Lean content is weaker than the barrier reading. carryPartialSum_eq is a finite telescoping identity (carryPartialSum K n = K 0 - K n / 2^n) and natCarryCoeff_cast is a cast lemma; no limit is taken in Lean, no series is shown to converge, no aperiodic carry sequence with a rational dyadic value is instantiated, and no Lean statement has the form 'X cannot work'. The no-go is an editorial reading of the identity, one unformalised limit step away from being formal. Within that reading it rules out only the inference 'rational dyadic value implies eventually periodic or automatic coefficient stream' via the coboundary identity alone. It does not rule out irrationality of the dyadic prime or prime-gap series, does not use or contradict any size or growth property of the actual prime gaps, and does not rule out arguments based on growing-block dyadic anti-concentration, which the module names as the missing producer. The natural-valued version needs K (n+1) <= 2 K n, so nonnegativity of the emitted coefficients is a real constraint that the barrier does not remove.

- Lean declaration: [carryPartialSum_eq](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1137)
- Lean declaration: [natCarryCoeff_cast](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1180)

- outgoing **barrier_for**: [Z17::n251_euler_odd_denominator](BROWSER_Z17_1.md#node-1f1777114f52b839). The totient-shift integrality is exactly the kind of consequence a free integer carry satisfies without any periodicity, so the criterion cannot be run backwards to constrain the coefficient word.
- incoming **repair_of**: [Z11::tempered_orbit_rigidity](BROWSER_Z11_1.md#node-a9e7e0703d37a58b). The barrier's freedom comes from an arbitrary integer carry K with no growth constraint (ErdosProblems.Erdos251.carryPartialSum_eq is a bare telescoping identity with no limit taken). temperedBinaryOrbit_eq_scaledTail proves that once c(n) <= n and u(N)/2^N -> 0 are imposed, u(N) = v * T_c(N) for every N, so exactly the freedom the barrier exploits is removed; the Z17 scope itself flags that the natural-valued version needs K(n+1) <= 2K(n).
- outgoing **reformulates**: [Z06::dyadic_coboundary_shift_calculus](BROWSER_Z06_1.md#node-b5d0116c5f6ae00e). carryPartialSum_eq (partial sums of 2K(n) - K(n+1) telescope to K(0) - K(n)/2^n) is the #251 statement of the same dyadic coboundary / cleared-prefix identity as dyadicClearedPrefix_dyadicCoboundary.
- outgoing **specialises**: [Z06::dyadic_coboundary_shift_calculus](BROWSER_Z06_1.md#node-b5d0116c5f6ae00e). `ErdosProblems.Erdos251.carryPartialSum_eq` (partial sums of the emitted word 2K(n) - K(n+1) telescope to K(0) - K(n)/2^n) is the base-point case of Z06's `dyadicClearedPrefix_dyadicCoboundary`, which computes the depth-L cleared prefix of a = 2c - Ec as 2^L c_n - c_{n+L} at every start and horizon.

<a id="node-4710f7307cdf47a7"></a>
## n251_indexing_normalisation

The displayed zero-based partial sum of p(i)/2^i equals twice the partial sum in the convention with denominator 2^(i+1).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [prime0DisplayedPartialSumQ_eq_two_mul](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L111)

- incoming **reformulates**: [Z17::n251_summation_by_parts](BROWSER_Z17_2.md#node-7d13ce1c0a940dae). Both are index conventions for the same finite dyadic prime sum; the gap form is the difference-transform of the displayed form.

<a id="node-0102a98d308d7360"></a>
## n251_integrality_criterion

A shifted tail difference is an integer exactly when (2^h - 1) times the current tail state is an integer, because the two differ by an explicit integer block.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tailShift_integral_iff_scaledTail](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L802)

- incoming **implies**: [Z17::n251_tail_block_identity](BROWSER_Z17_2.md#node-48fddc1aba479f46). The integrality criterion is the block identity modulo the explicit integer block.
- incoming **specialises**: [Z17::n251_euler_odd_denominator](BROWSER_Z17_1.md#node-1f1777114f52b839). Euler's congruence instantiates the criterion at h = phi(den) when the denominator is odd.
- outgoing **transport_of**: [Z06::certificate_supply_is_equivalent_to_249](BROWSER_Z06_1.md#node-b7430ca307ffd27e). tailShift_integral_iff_scaledTail is the generic-digit form of tail_diff_mem_int_iff_scaled_series_mem_int: a shifted dyadic tail difference is an integer exactly when (2^h - 1) times the tail state is, instantiated at prime gaps rather than at phi.
- incoming **specialises**: [Z06::certificate_supply_is_equivalent_to_249](BROWSER_Z06_1.md#node-b7430ca307ffd27e). Z17's `ErdosProblems.Erdos251.tailShift_integral_iff_scaledTail` states for any dyadic tail obeying T(N+1) = 2T(N) - g(N+1) with integer digits that a shifted tail difference is integral exactly when (2^h - 1) times the tail state is; Z06's `tail_diff_mem_int_iff_scaled_series_mem_int` is that criterion for the totient tail, where the scaled state is 2^N (2^h - 1) S.

<a id="node-fa31ac950ba3d817"></a>
## n251_integrality_propagates

Once a fixed tail shift is integral at one index it is integral at every later index, by the recurrence alone and with no prime-distribution input.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tailShift_integral_succ](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L888)
- Lean declaration: [tailShift_integral_add](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L900)


