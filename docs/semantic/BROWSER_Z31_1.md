# Z31_1: Prime-gap dyadic tail collapse and cofinal escape frontier

[All problems and zones](BROWSER.md)

<a id="node-99ecbc4e45b17636"></a>
## actual_prime_gap_eventual_smallness_would_exclude_integral_shifts

PROVED CONDITIONAL: for any fixed positive shift of a rational recurrence driven by the actual prime gaps, eventual strict smallness of that shift excludes its eventual integrality, because the latter pair would force the prime-gap word to become periodic.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The eventual-smallness hypothesis is stronger than the proposed cofinal adjacent-pair condition and is not established. The theorem therefore does not resolve Erdős #251.

Open hypotheses: ["eventual strict smallness of the actual prime-gap tail shift for each required positive shift length"]

- Lean declaration: [primeGapTailShift_not_eventuallyIntegral_of_eventually_small](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1059)

- outgoing **specialises**: [Z31::eventually_small_integral_shift_forces_digit_periodicity](BROWSER_Z31_1.md#node-27f3be822bf9fdcc). The actual-prime-gap result specialises the abstract eventual-smallness rigidity theorem and discharges its nonperiodicity premise with the proved prime-gap theorem.
- outgoing **generated_by**: [Z31::actual_prime_gaps_are_unbounded_and_not_eventually_periodic](BROWSER_Z31_1.md#node-7539d8c9a7c2387d). The actual-gap exclusion consumes the proved non-eventual-periodicity of the gap word; its separate eventual-smallness premise is not supplied.
- outgoing **complements**: [Z31::cofinal_adjacent_small_mismatches_exclude_eventual_integrality](BROWSER_Z31_1.md#node-3425b082d1a4647c). Eventual smallness is a stronger global route, whereas the adjacent-pair theorem requires only sporadic cofinal small mismatches.

<a id="node-7539d8c9a7c2387d"></a>
## actual_prime_gaps_are_unbounded_and_not_eventually_periodic

PROVED: the zero-based consecutive-prime-gap sequence is unbounded by the factorial prime-free-interval construction and therefore is not eventually periodic with any positive period.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: Unboundedness and non-eventual-periodicity alone give no tail smallness or anti-concentration. They do not exclude a rational dyadic sum for an unrestricted integer coefficient stream.

- Lean declaration: [exists_primeGap0_gt](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L57)
- Lean declaration: [primeGap0_not_eventually_periodic](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1023)

- incoming **generated_by**: [Z31::actual_prime_gap_eventual_smallness_would_exclude_integral_shifts](BROWSER_Z31_1.md#node-99ecbc4e45b17636). The actual-gap exclusion consumes the proved non-eventual-periodicity of the gap word; its separate eventual-smallness premise is not supplied.

<a id="node-e92e927a0ffa1981"></a>
## adjacent_small_mismatch_is_a_local_nonintegrality_certificate

PROVED LOCAL CERTIFICATE: for a rational dyadic recurrence, two adjacent shifts lying strictly between -1 and 1 cannot both be integral when the corresponding integer digits differ.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem consumes one already-certified adjacent small pair. It does not prove that such pairs occur for actual prime gaps.

- Lean declaration: [ratIntegral_eq_zero_of_neg_one_lt_of_lt_one](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L913)
- Lean declaration: [tailShift_not_both_integral_of_small_pair_of_digit_ne](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L979)

- incoming **generated_by**: [Z31::cofinal_adjacent_small_mismatches_exclude_eventual_integrality](BROWSER_Z31_1.md#node-3425b082d1a4647c). The cofinal theorem chooses one adjacent small-mismatch certificate beyond the alleged onset of integrality.

<a id="node-3425b082d1a4647c"></a>
## cofinal_adjacent_small_mismatches_exclude_eventual_integrality

PROVED CONDITIONAL: if adjacent small mismatching pairs occur beyond every threshold for a fixed shift, that shift cannot be eventually integral; the same implication is Lean-checked for the actual consecutive-prime-gap digits.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The Lean result is a consumer for the quantified supply. It does not prove either full-tail inequality or the cofinal occurrence of mismatching pairs.

Open hypotheses: ["cofinal adjacent small-mismatch supply for each fixed positive shift of the actual prime-gap tail"]

- Lean declaration: [not_eventuallyIntegralTailShift_of_cofinal_small_mismatch](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1006)
- Lean declaration: [primeGapTailShift_not_eventuallyIntegral_of_cofinal_small_mismatch](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1112)

- outgoing **generated_by**: [Z31::adjacent_small_mismatch_is_a_local_nonintegrality_certificate](BROWSER_Z31_1.md#node-e92e927a0ffa1981). The cofinal theorem chooses one adjacent small-mismatch certificate beyond the alleged onset of integrality.
- incoming **depends_on_open**: [Z31::cofinal_nonintegral_shifts_force_irrational_initial_state](BROWSER_Z31_1.md#node-5830f0f7ef6d65a0). For the actual prime-gap orbit, a cofinal small-mismatch supply for every fixed positive h would exclude every eventual integral shift and feed the abstract cofinal-escape consumer; the supply and analytic tail instantiation remain open.
- incoming **complements**: [Z31::actual_prime_gap_eventual_smallness_would_exclude_integral_shifts](BROWSER_Z31_1.md#node-99ecbc4e45b17636). Eventual smallness is a stronger global route, whereas the adjacent-pair theorem requires only sporadic cofinal small mismatches.
- incoming **complements**: [Z31::finite_approximation_gap_certifies_nonintegrality](BROWSER_Z31_1.md#node-b8ea617f0c29a94e). Finite anti-concentration directly certifies nonintegrality, while adjacent small mismatches certify that two neighboring shifts cannot both be integral; both still require a cofinal prime-gap producer.

<a id="node-5830f0f7ef6d65a0"></a>
## cofinal_nonintegral_shifts_force_irrational_initial_state

PROVED CONDITIONAL ABSTRACTLY: a real dyadic tail recurrence with integer digits has irrational initial state whenever, for every fixed positive shift length and every threshold, some later shift is not an integer.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The Lean theorem is generic. The paper derives the actual prime-gap real recurrence from the classical prime number theorem, but that analytic instantiation is not formalised in this module.

Open hypotheses: ["CofinalNonintegralTailShifts for the actual prime-gap real tail", "formal Lean instantiation of the convergent actual prime-gap tail recurrence"]

- Lean declaration: [realTail_eq_ratCast_rationalDyadicOrbit](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1395)
- Lean declaration: [irrational_initial_of_cofinalNonintegralTailShifts](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1416)

- outgoing **reformulates**: [Z31::every_rational_dyadic_tail_has_an_eventually_integral_shift](BROWSER_Z31_1.md#node-2a5f6efc29c9309b). The real irrationality consumer is the contrapositive of the rational denominator-collapse theorem after exact real/rational orbit transport.
- outgoing **depends_on_open**: [Z31::cofinal_adjacent_small_mismatches_exclude_eventual_integrality](BROWSER_Z31_1.md#node-3425b082d1a4647c). For the actual prime-gap orbit, a cofinal small-mismatch supply for every fixed positive h would exclude every eventual integral shift and feed the abstract cofinal-escape consumer; the supply and analytic tail instantiation remain open.
- incoming **specialises**: [Z31::finite_approximation_gap_certifies_nonintegrality](BROWSER_Z31_1.md#node-b8ea617f0c29a94e). A cofinal family of finite approximation-gap certificates, together with valid tail-error bounds, would supply the nonintegral shifts consumed by the abstract irrationality theorem.

<a id="node-27f3be822bf9fdcc"></a>
## eventually_small_integral_shift_forces_digit_periodicity

PROVED CONDITIONAL: if one fixed rational tail shift is eventually integral and eventually remains strictly between -1 and 1, it is eventually zero; for an integer-digit dyadic recurrence this forces the digit word to be eventually periodic with that shift, so nonperiodicity excludes eventual integrality whenever eventual smallness is available.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Actual prime-gap nonperiodicity is proved, but eventual smallness of every relevant full tail shift is not. This implication does not manufacture that analytic estimate.

Open hypotheses: ["eventual strict smallness of a fixed actual prime-gap tail shift"]

- Lean declaration: [tailShift_eventually_zero_of_eventually_integral_of_eventually_small](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L926)
- Lean declaration: [digits_eventually_periodic_of_eventually_integralTailShift_of_eventually_small](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L943)
- Lean declaration: [not_eventuallyIntegralTailShift_of_eventually_small_of_not_periodic](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L964)

- incoming **specialises**: [Z31::actual_prime_gap_eventual_smallness_would_exclude_integral_shifts](BROWSER_Z31_1.md#node-99ecbc4e45b17636). The actual-prime-gap result specialises the abstract eventual-smallness rigidity theorem and discharges its nonperiodicity premise with the proved prime-gap theorem.

<a id="node-2a5f6efc29c9309b"></a>
## every_rational_dyadic_tail_has_an_eventually_integral_shift

PROVED ABSTRACTLY: every rational-valued recurrence T(N+1)=2T(N)-g(N+1) with integer digits reaches a state with odd reduced denominator, and consequently admits one fixed positive shift length whose tail displacement is integral at every sufficiently late index.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The shift length depends on the odd denominator reached from the hypothetical rational initial value and is not known in advance. The theorem applies to arbitrary integer digits and does not use prime-gap distribution.

- Lean declaration: [exists_twoPow_mul_odd_den](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1306)
- Lean declaration: [exists_odd_den_state](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1341)
- Lean declaration: [exists_eventually_integral_tailShift](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1357)

- incoming **reformulates**: [Z31::cofinal_nonintegral_shifts_force_irrational_initial_state](BROWSER_Z31_1.md#node-5830f0f7ef6d65a0). The real irrationality consumer is the contrapositive of the rational denominator-collapse theorem after exact real/rational orbit transport.

<a id="node-b8ea617f0c29a94e"></a>
## finite_approximation_gap_certifies_nonintegrality

PROVED GENERIC CERTIFICATE: if a rational approximation is farther than R from every integer and the full rational value differs from that approximation by at most R, then the full value is not integral.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem does not construct a prime-gap approximation, prove a tail-error bound, or establish cofinally many anti-concentrated blocks. Those analytic and arithmetic producers remain open.

- Lean declaration: [not_ratIntegral_of_approximation_gap](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1438)

- outgoing **specialises**: [Z31::cofinal_nonintegral_shifts_force_irrational_initial_state](BROWSER_Z31_1.md#node-5830f0f7ef6d65a0). A cofinal family of finite approximation-gap certificates, together with valid tail-error bounds, would supply the nonintegral shifts consumed by the abstract irrationality theorem.
- outgoing **complements**: [Z31::cofinal_adjacent_small_mismatches_exclude_eventual_integrality](BROWSER_Z31_1.md#node-3425b082d1a4647c). Finite anti-concentration directly certifies nonintegrality, while adjacent small mismatches certify that two neighboring shifts cannot both be integral; both still require a cofinal prime-gap producer.

<a id="node-0c19a3a9b3431dc1"></a>
## prime_and_gap_irrationality_are_exactly_equivalent

PROVED CONDITIONAL REFORMULATION: under summability of the normalized dyadic prime terms, the normalized prime series is irrational if and only if the consecutive-prime-gap series is irrational; the displayed denominator-2^n normalization is exactly four plus twice the gap series and has the same irrationality status.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This node preserves the open status of Erdős #251. It identifies an equivalent gap-series target but supplies no irrationality witness.

Open hypotheses: ["Summable primeDyadicTerm", "irrationality of the consecutive-prime-gap dyadic series"]

- Lean declaration: [irrational_tsum_primeDyadicTerm_iff_primeGap](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L435)
- Lean declaration: [tsum_primeDisplayedDyadicTerm_eq_four_add_two_primeGap](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L444)
- Lean declaration: [irrational_tsum_primeDisplayedDyadicTerm_iff_primeGap](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L459)

- outgoing **reformulates**: [Z31::prime_gap_series_is_exact_summable_coboundary](BROWSER_Z31_1.md#node-7893781c138766f8). The irrationality equivalence is obtained from the summable coboundary identity by rational translation and nonzero rational scaling; it adds no truth-value progress.

<a id="node-7893781c138766f8"></a>
## prime_gap_series_is_exact_summable_coboundary

PROVED CONDITIONAL: termwise, the normalized consecutive-prime-gap term is twice the next normalized prime term minus the current prime term; therefore summability of the normalized dyadic prime series implies summability of the gap series and the exact identity sum(primes)=2+sum(gaps).

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Lean does not prove the prime-number-theorem input here. The declarations are conditional on summability, and they do not prove irrationality of either series.

Open hypotheses: ["Summable primeDyadicTerm"]

- Lean declaration: [primeGapDyadicTerm_eq](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L202)
- Lean declaration: [summable_primeGapDyadicTerm_of_summable_primeDyadicTerm](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L385)
- Lean declaration: [tsum_primeDyadicTerm_eq_two_add_primeGap](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L404)

- incoming **reformulates**: [Z31::prime_and_gap_irrationality_are_exactly_equivalent](BROWSER_Z31_1.md#node-0c19a3a9b3431dc1). The irrationality equivalence is obtained from the summable coboundary identity by rational translation and nonzero rational scaling; it adds no truth-value progress.

