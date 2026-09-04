# Z72_1: Erdős 1049 Heine-Zudilin cone exponents and endpoint obstructions

[All problems and zones](BROWSER.md)

<a id="node-c15f4f9d70210566"></a>
## bottom_exponents_have_an_exact_endpoint_and_increase_inside_the_cone

At k=a2 the doubled normalised bottom exponent is 2(a2-a1)(a0+a2-b). Its consecutive difference at k is 2(a0-b+k+1); consequently, under b<=a0+a2, it strictly increases for every k>=a2.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The statement assumes the displayed cone inequality and concerns only exponent bookkeeping. It supplies neither coefficient integrality nor asymptotic decay.

- Lean declaration: [zudilinBottomExpTwice_at_a2](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L52)
- Lean declaration: [zudilinBottomExpTwice_succ_sub](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L60)
- Lean declaration: [zudilinBottomExpTwice_strict_step](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L70)

- incoming **complements**: [Z72::raw_summand_degrees_increase_through_the_allowed_index_range](BROWSER_Z72_1.md#node-a27b1afe446e862f). The two monotonicity packets control different exponent axes of the same finite coefficient construction: normalised bottom order versus raw polynomial degree.

<a id="node-bdf9b601faa59fb3"></a>
## homogeneous_three_two_evaluation_representation

For an integral polynomial P and declared width W, homEvalThreeTwo(W,P) is the integer homogeneous evaluation sum over 0<=i<=W of coeff(P,i)*3^i*2^(W-i). The bottom 3-adic and top 2-adic endpoint jets are reductions of this same integer.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The coordinate definition supplies neither endpoint-unit hypotheses nor divisibility obstructions, coefficient constructions, analytic decay, or irrationality/transcendence conclusions.

- Lean declaration: [homEvalThreeTwo](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L98)


<a id="node-a3b7f5c846545363"></a>
## irrationality_exponent_bounds_force_twice_the_lower_rate_below_the_upper_rate

If C0>0, an irrationality exponent mu satisfies 2<=mu, and mu<=C1/C0, then 2*C0<=C1.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem assumes both exponent bounds. It neither proves irrationality, constructs a linear-form family, nor supplies numerical values of C0 and C1.

- Lean declaration: [twice_le_of_irrationalityExponent_bounds](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L416)

- incoming **complements**: [Z72::one_endpoint_unit_blocks_a_common_local_prime_across_both_channels](BROWSER_Z72_1.md#node-4306df50ebbec27c). The endpoint obstruction controls local common content, while the exponent inequality isolates the independent analytic-rate constraint; neither statement supplies the other's hypotheses.

<a id="node-4306df50ebbec27c"></a>
## one_endpoint_unit_blocks_a_common_local_prime_across_both_channels

If the left polynomial has top coefficient plus or minus one, its homogeneous value and the other channel cannot both be divisible by 2. If the right polynomial has constant coefficient plus or minus one, the two values cannot both be divisible by 3.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The barrier requires an endpoint unit and excludes only simultaneous divisibility by the named local prime. It does not prove the endpoint-unit hypotheses for a Zudilin family or rule out other common factors.

- Lean declaration: [not_two_dvd_both_homEval_of_left_top_unit](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L374)
- Lean declaration: [not_three_dvd_both_homEval_of_right_const_unit](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L384)

- outgoing **complements**: [Z72::irrationality_exponent_bounds_force_twice_the_lower_rate_below_the_upper_rate](BROWSER_Z72_1.md#node-a3b7f5c846545363). The endpoint obstruction controls local common content, while the exponent inequality isolates the independent analytic-rate constraint; neither statement supplies the other's hypotheses.

<a id="node-a27b1afe446e862f"></a>
## raw_summand_degrees_increase_through_the_allowed_index_range

The consecutive difference of the doubled raw summand degree is 2(a0+a1+a2-k-2). If a1>0, b<=a0+a2, and k<=b-2, that difference is positive, so the raw degree strictly increases through the allowed index range.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Strict degree growth does not construct the coefficient polynomial, prove endpoint units, or establish any irrationality or transcendence statement.

- Lean declaration: [zudilinRawDegreeTwice_succ_sub](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L79)
- Lean declaration: [zudilinRawDegreeTwice_strict_step](../../ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L88)

- outgoing **complements**: [Z72::bottom_exponents_have_an_exact_endpoint_and_increase_inside_the_cone](BROWSER_Z72_1.md#node-c15f4f9d70210566). The two monotonicity packets control different exponent axes of the same finite coefficient construction: normalised bottom order versus raw polynomial degree.

