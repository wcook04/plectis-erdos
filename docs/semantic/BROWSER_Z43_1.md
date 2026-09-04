# Z43_1: Erdős 251 coordinate systems: prime-gap sums, dyadic tails, real escape, and free carries

[All problems and zones](BROWSER.md)

<a id="node-cf5834e91b3a3ea6"></a>
## finite_dyadic_partial_sum_coordinates

The normalized dyadic partial sum, displayed prime partial sum, forward-difference partial sum, and actual prime-gap partial sum are the exact rational finite-sum coordinates used by the source's summation-by-parts argument.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The definitions supply neither convergence nor an infinite-series identity; the already-authored theorem nodes in Z17 and Z31 retain those claims.

- Lean declaration: [dyadicPartialSumQ](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L101)
- Lean declaration: [prime0DisplayedPartialSumQ](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L106)
- Lean declaration: [dyadicDifferencePartialSumQ](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L121)
- Lean declaration: [primeGapPartialSumQ](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L161)

- outgoing **specialises**: [Z43::zero_based_prime_gap_coordinates](BROWSER_Z43_1.md#node-9d0829b9bf59924e). The four finite sums instantiate the zero-based prime and gap coordinates; this relation carries no convergence claim.

<a id="node-9b54a6abb087a27f"></a>
## free_carry_coordinate_system

The free-carry coordinates are the rational and natural coefficients kappa_n=2*K_n-K_(n+1), together with their finite dyadic partial sum.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These definitions alone prove neither the finite telescoping theorem, an infinite limit, nor an aperiodic rational-sum example; Z17 retains the finite identity.

- Lean declaration: [carryCoeff](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1129)
- Lean declaration: [carryPartialSum](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1133)
- Lean declaration: [natCarryCoeff](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1177)

- outgoing **complements**: [Z43::rational_dyadic_tail_coordinate_system](BROWSER_Z43_1.md#node-107eec185ae4a80b). The carry coordinates provide a second finite telescoping interface, without an infinite-series or irrationality transport.

<a id="node-e8380c992c0225dc"></a>
## integrality_is_invariant_under_integer_translation

For a rational number x and an integer z, x-z is integral if and only if x is integral.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This generic arithmetic equivalence does not produce an integral tail shift.

- Lean declaration: [ratIntegral_sub_int_iff](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L677)

- outgoing **generated_by**: [Z43::rational_dyadic_tail_coordinate_system](BROWSER_Z43_1.md#node-107eec185ae4a80b). The recurrence's integer block motivates the generic integer-translation equivalence, which by itself produces no integral shift.

<a id="node-107eec185ae4a80b"></a>
## rational_dyadic_tail_coordinate_system

The rational interface consists of the recurrence T_(N+1)=2*T_N-g_(N+1), the shift T_(N+h)-T_N, rational integrality, and the recursively accumulated integer block.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is an abstract rational recurrence, not the actual infinite prime-gap tail.

- Lean declaration: [DyadicTailRecurrence](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L482)
- Lean declaration: [tailShift](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L544)
- Lean declaration: [RatIntegral](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L575)
- Lean declaration: [dyadicTailBlock](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L647)

- incoming **generated_by**: [Z43::integrality_is_invariant_under_integer_translation](BROWSER_Z43_1.md#node-e8380c992c0225dc). The recurrence's integer block motivates the generic integer-translation equivalence, which by itself produces no integral shift.
- incoming **specialises**: [Z43::rational_initial_data_generate_an_exact_rational_orbit](BROWSER_Z43_1.md#node-82c21dd84f187a0f). Primitive recursion gives one exact orbit satisfying the abstract rational recurrence.
- incoming **complements**: [Z43::real_tail_escape_coordinate_system](BROWSER_Z43_1.md#node-62575037bf600f1a). The real interface parallels the rational recurrence while adding a cofinal nonintegrality predicate; no actual prime-gap instantiation is asserted.
- incoming **complements**: [Z43::free_carry_coordinate_system](BROWSER_Z43_1.md#node-9b54a6abb087a27f). The carry coordinates provide a second finite telescoping interface, without an infinite-series or irrationality transport.

<a id="node-82c21dd84f187a0f"></a>
## rational_initial_data_generate_an_exact_rational_orbit

For any integer digit sequence and rational initial value q, primitive recursion constructs the displayed rational orbit beginning at q, and that orbit satisfies DyadicTailRecurrence exactly.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This constructs an abstract orbit; it proves neither irrationality nor identification with the actual prime-gap tail.

- Lean declaration: [rationalDyadicOrbit](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1384)
- Lean declaration: [rationalDyadicOrbit_recurrence](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1388)

- outgoing **specialises**: [Z43::rational_dyadic_tail_coordinate_system](BROWSER_Z43_1.md#node-107eec185ae4a80b). Primitive recursion gives one exact orbit satisfying the abstract rational recurrence.

<a id="node-e22c2978bb8209bc"></a>
## real_dyadic_prime_and_gap_term_coordinates

The real term coordinates are prime0 n / 2^(n+1), prime0 n / 2^n, and primeGap0 n / 2^(n+1); the displayed prime term is exactly twice the normalized prime term.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These term definitions and the factor-two identity prove no summability or irrationality conclusion.

- Lean declaration: [primeDyadicTerm](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L183)
- Lean declaration: [primeDisplayedDyadicTerm](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L188)
- Lean declaration: [primeGapDyadicTerm](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L192)
- Lean declaration: [primeDisplayedDyadicTerm_eq_two_mul](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L196)

- outgoing **specialises**: [Z43::zero_based_prime_gap_coordinates](BROWSER_Z43_1.md#node-9d0829b9bf59924e). The three real terms cast and scale the exact zero-based prime and gap coordinates.

<a id="node-62575037bf600f1a"></a>
## real_tail_escape_coordinate_system

The real interface consists of the real dyadic recurrence, real tail shift, real integrality, and CofinalNonintegralTailShifts, which requires every positive shift to fail integrality cofinally.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These definitions do not establish the actual prime-gap real recurrence or cofinal escape; the paper's external prime-number-theorem argument is not formalized here.

- Lean declaration: [RealDyadicTailRecurrence](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1372)
- Lean declaration: [realTailShift](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1376)
- Lean declaration: [RealIntegral](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1380)
- Lean declaration: [CofinalNonintegralTailShifts](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1408)

- outgoing **complements**: [Z43::rational_dyadic_tail_coordinate_system](BROWSER_Z43_1.md#node-107eec185ae4a80b). The real interface parallels the rational recurrence while adding a cofinal nonintegrality predicate; no actual prime-gap instantiation is asserted.

<a id="node-9d0829b9bf59924e"></a>
## zero_based_prime_gap_coordinates

prime0 n is the zero-based nth prime and primeGap0 n = prime0 (n+1) - prime0 n. Consecutive primes are monotone, so casting the natural gap to rational numbers gives the exact rational difference.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These coordinates make no distributional, convergence, rationality, or irrationality claim.

- Lean declaration: [prime0](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L40)
- Lean declaration: [primeGap0](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L44)
- Lean declaration: [prime0_mono_step](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L152)
- Lean declaration: [primeGap0_cast](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L156)

- incoming **specialises**: [Z43::finite_dyadic_partial_sum_coordinates](BROWSER_Z43_1.md#node-cf5834e91b3a3ea6). The four finite sums instantiate the zero-based prime and gap coordinates; this relation carries no convergence claim.
- incoming **specialises**: [Z43::real_dyadic_prime_and_gap_term_coordinates](BROWSER_Z43_1.md#node-e22c2978bb8209bc). The three real terms cast and scale the exact zero-based prime and gap coordinates.

