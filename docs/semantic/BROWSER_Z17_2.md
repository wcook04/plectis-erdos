# Z17_2: Neighbouring Erdos problems (#243, #251, #269, #1049) and the problem-owned library root

[All problems and zones](BROWSER.md)

<a id="node-0f1a409a67915230"></a>
## n251_small_gap_values

The first two zero-based consecutive prime gaps are 1 and 2 (3 - 2 and 5 - 3).

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [primeGap0_zero](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L47)
- Lean declaration: [primeGap0_one](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L51)


<a id="node-7d13ce1c0a940dae"></a>
## n251_summation_by_parts

Exact finite summation by parts for dyadic partial sums: the sum of P(i)/2^(i+1) over i < n+1 equals P(0) plus the dyadic sum of forward differences minus the endpoint term P(n)/2^(n+1); specialised to the primes this rewrites the dyadic prime partial sum as 2 plus the dyadic prime-gap partial sum minus an endpoint correction.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [dyadicPartialSumQ_eq_start_add_differences](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L138)
- Lean declaration: [prime0_dyadic_summation_by_parts](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L172)

- outgoing **reformulates**: [Z17::n251_indexing_normalisation](BROWSER_Z17_1.md#node-4710f7307cdf47a7). Both are index conventions for the same finite dyadic prime sum; the gap form is the difference-transform of the displayed form.

<a id="node-48fddc1aba479f46"></a>
## n251_tail_block_identity

For any rational sequence obeying the dyadic tail recurrence T(N+1) = 2 T(N) - g(N+1) with integer digits, iterating h steps gives T(N+h) = 2^h T(N) - B(h,N) with B the explicit integer block, so the shifted difference T(N+h) - T(N) equals (2^h - 1) T(N) minus that integer block; the shift also propagates one step at a time.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tailShift_succ](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L563)
- Lean declaration: [tail_iterate_eq_pow_mul_sub_block](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L653)
- Lean declaration: [tailShift_eq_scaled_sub_block](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L667)

- outgoing **implies**: [Z17::n251_integrality_criterion](BROWSER_Z17_1.md#node-0102a98d308d7360). The integrality criterion is the block identity modulo the explicit integer block.
- outgoing **reformulates**: [Z11::binary_tail_shift_identity](BROWSER_Z11_1.md#node-51b4e0f463db1e09). tail_iterate_eq_pow_mul_sub_block iterates the same dyadic tail recurrence T(N+1) = 2 T(N) - g(N+1) that binaryCoeffTail_succ states for coefficient sequences with c(n) <= n.

<a id="node-36891fb62e9a4d31"></a>
## n269_fiber_normal_form

Grouping the finite smooth exponent box by running-LCM height puts the finite kernel sum in normal form: the coefficient of each height is the cardinality of its fiber times the reciprocal of that height.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [finiteSmoothKernelSum_groupedByHeight](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L406)
- Lean declaration: [smoothHeightFiber_kernel_sum](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L384)


<a id="node-2688220bd2b15ee2"></a>
## n269_height_cubic_majorant

For any bases and any nonzero x, the three-prime height is at most x^3, since each pure-power component is at most x.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [threePrimeHeight_le_cube](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L430)


<a id="node-090ca85042590325"></a>
## n269_jump_set_cardinality

For three pairwise-distinct primes, the first count positive powers in each channel are distinct and pairwise disjoint across channels, giving 3*count values; adjoining the common origin 1 gives exactly 3*count + 1 distinct jump values.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [threePrimePositiveJumpSet_card](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L249)
- Lean declaration: [threePrimeJumpSetWithOrigin_card](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L278)
- Lean declaration: [positivePrimePowers_card](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L208)


<a id="node-e9c543dcc2ae001f"></a>
## n269_kernel_235_not_rank_one

The {2,3,5} kernel is not of rank one: the product of the values at (0,0,0) and (1,1,0) is 1/60 while the product at (1,0,0) and (0,1,0) is 1/12, so the kernel does not factor as a product of one-dimensional channels.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [kernel_235_not_rankOne](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L479)

- incoming **implies**: [Z17::n269_kernel_235_values](BROWSER_Z17_2.md#node-d677b02dda13df9c). Direction corrected: the four explicit kernel evaluations are the simp lemmas that norm_num consumes to close kernel_235_not_rankOne, so the values imply the rank-one obstruction (a two-by-two product comparison among them), not the reverse.

<a id="node-d677b02dda13df9c"></a>
## n269_kernel_235_values

The first exact {2,3,5} kernel values: 1 at the origin, 1/2 at exponent (1,0,0), 1/6 at (0,1,0) and 1/60 at (1,1,0).

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [kernel_235_origin](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L443)
- Lean declaration: [kernel_235_two](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L450)
- Lean declaration: [kernel_235_three](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L458)
- Lean declaration: [kernel_235_six](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L467)

- outgoing **finite_instance_of**: [Z17::n269_running_lcm_identity](BROWSER_Z17_2.md#node-cbefdd820961abb5). Four explicit evaluations of the height and its reciprocal kernel at {2,3,5}.
- outgoing **implies**: [Z17::n269_kernel_235_not_rank_one](BROWSER_Z17_2.md#node-e9c543dcc2ae001f). Direction corrected: the four explicit kernel evaluations are the simp lemmas that norm_num consumes to close kernel_235_not_rankOne, so the values imply the rank-one obstruction (a two-by-two product comparison among them), not the reverse.

<a id="node-b42e57ea6018943d"></a>
## n269_log_cell_constancy

The three-prime height, the literal smooth-prefix LCM and the reciprocal lattice kernel are all constant on a logarithmic cell, i.e. whenever none of the three floor-logarithm coordinates changes.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [threePrimeHeight_eq_of_sameLogCell](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L169)
- Lean declaration: [smoothPrefixLcm_eq_of_sameLogCell](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L179)
- Lean declaration: [threePrimeKernelQ_eq_of_sameLogCell](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L191)

- incoming **implies**: [Z17::n269_running_lcm_identity](BROWSER_Z17_2.md#node-cbefdd820961abb5). Constancy of the literal LCM on a logarithmic cell is obtained by rewriting through the height identity.

<a id="node-74578f66482ad2a5"></a>
## n269_residue_escape_contradiction

If a positive natural c is at most bound and is congruent modulo C to a residue lying strictly above bound and at most C, that is contradictory; equivalently, a bounded positive state in the window forces its prescribed residue to stay within the bound.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [no_bounded_positive_state_of_residue_escape](../../ErdosProblems/Erdos269/ResidueEscape.lean#L76)
- Lean declaration: [residue_le_bound_of_bounded_positive_state](../../ErdosProblems/Erdos269/ResidueEscape.lean#L96)

- outgoing **depends_on_open**: [Z17::n269_tail_step_normal_form](BROWSER_Z17_2.md#node-7b2767d4fca9d6d6). The finite contradiction only bites once some producer supplies an escaping residue for the variable-base tail orbit; no such producer exists in this zone or elsewhere in the corpus.

<a id="node-cbefdd820961abb5"></a>
## n269_running_lcm_identity

For three pairwise-distinct primes p, q, r and x nonzero, the least common multiple of all {p,q,r}-smooth numbers not exceeding x equals the product of the largest pure powers p^log_p x * q^log_q x * r^log_r x.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [smoothPrefixLcm_eq_threePrimeHeight](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L123)
- Lean declaration: [smoothPrefixLcm_dvd_threePrimeHeight](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L77)

- outgoing **implies**: [Z17::n269_log_cell_constancy](BROWSER_Z17_2.md#node-b42e57ea6018943d). Constancy of the literal LCM on a logarithmic cell is obtained by rewriting through the height identity.
- outgoing **implies**: [Z17::n269_single_coordinate_jump](BROWSER_Z17_2.md#node-363ce7eff1400b57). The jump ratios for the literal LCM are obtained through the same identity.
- incoming **finite_instance_of**: [Z17::n269_kernel_235_values](BROWSER_Z17_2.md#node-d677b02dda13df9c). Four explicit evaluations of the height and its reciprocal kernel at {2,3,5}.

<a id="node-0627051332d8a963"></a>
## n269_short_shell_quadratic

In a half-open multiplicative interval of width at most one base, fixing the other exponents pins that base's exponent; hence a {p,q,r}-smooth exponent shell in such an interval injects into a two-coordinate box, and when the coordinate heights are sorted and sum to j the shell cardinality obeys 9 * card <= (j + 3)^2.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [smoothExponentShell_card_le_dropFirst](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L543)
- Lean declaration: [smoothExponentShell_card_le_dropThird](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L585)
- Lean declaration: [smoothExponentShell_card_quadratic](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L646)
- Lean declaration: [exponent_unique_in_short_interval](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L509)


<a id="node-363ce7eff1400b57"></a>
## n269_single_coordinate_jump

If exactly one floor-logarithm coordinate advances by one, the three-prime height, and hence the running LCM, is multiplied by exactly the corresponding prime base.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [threePrimeHeight_firstLogStep](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L294)
- Lean declaration: [threePrimeHeight_secondLogStep](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L305)
- Lean declaration: [threePrimeHeight_thirdLogStep](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L316)
- Lean declaration: [smoothPrefixLcm_firstLogStep](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L326)
- Lean declaration: [smoothPrefixLcm_secondLogStep](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L339)
- Lean declaration: [smoothPrefixLcm_thirdLogStep](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L352)

- incoming **implies**: [Z17::n269_running_lcm_identity](BROWSER_Z17_2.md#node-cbefdd820961abb5). The jump ratios for the literal LCM are obtained through the same identity.

<a id="node-7b2767d4fca9d6d6"></a>
## n269_tail_step_normal_form

The variable-base tail step next = base * (state - digit) is the same as next = base * state - base * digit.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tailStateStep_eq](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L490)

- incoming **depends_on_open**: [Z17::n269_residue_escape_contradiction](BROWSER_Z17_2.md#node-74578f66482ad2a5). The finite contradiction only bites once some producer supplies an escaping residue for the variable-base tail orbit; no such producer exists in this zone or elsewhere in the corpus.

