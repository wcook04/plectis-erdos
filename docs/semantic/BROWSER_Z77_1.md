# Z77_1: Erdős 243 divisibility-growth, primitive reduction, and geometric-rate engines

[All problems and zones](BROWSER.md)

<a id="node-f554286f9bccd51f"></a>
## a_larger_positive_exponential_base_eventually_beats_fixed_prefactors

For natural U,V,A,B with V>0, B>0, and A<B, there is a cutoff M after which U*A^m < V*B^m for every m>=M.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The theorem is a generic asymptotic comparison. It does not establish that the Erdős 243 tail satisfies either exponential bound consumed by later arguments.

- Lean declaration: [eventually_const_mul_pow_lt_const_mul_pow](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2066)

- incoming **complements**: [Z77::strict_divisibility_growth_has_exact_binary_and_interval_accounting](BROWSER_Z77_1.md#node-d80cd8af72bc3135). Strict-growth accounting converts repeated divisibility events into powers of two, while geometric domination compares those powers with a larger asymptotic rate; neither theorem supplies the chain or rate hypotheses of the other.

<a id="node-d3cff8fe64992dea"></a>
## exact_tail_gcd_reduction_produces_primitive_coordinates

If the tail numerator C is positive, dividing C and D by their exact gcd produces coprime reducedTailNumerator and reducedTailDenominator coordinates.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Primitivity is a coordinate fact. It does not bound the next gcd-growth factor or exclude recurrent cancellation.

- Lean declaration: [reducedTail_coprime](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1474)

- outgoing **complements**: [Z77::strict_divisibility_growth_has_exact_binary_and_interval_accounting](BROWSER_Z77_1.md#node-d80cd8af72bc3135). Primitive tail coordinates isolate the exact gcd whose strict growth is counted; the relation asserts only the intended coordinate interface, not a growth theorem.

<a id="node-d80cd8af72bc3135"></a>
## strict_divisibility_growth_has_exact_binary_and_interval_accounting

A strict step x<y in a natural divisibility chain x|y forces 2x<=y. The strictGrowthCount splits exactly across an interval boundary, and any strict step before n makes the cumulative count at n positive.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The lemmas count and price strict events once a divisibility chain is supplied. They do not prove that the tail-gcd chain has finitely or infinitely many such events.

- Lean declaration: [two_mul_le_of_dvd_of_lt](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1206)
- Lean declaration: [strictGrowthCount_add](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1281)
- Lean declaration: [strictGrowthCount_pos_of_event](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1300)

- outgoing **complements**: [Z77::a_larger_positive_exponential_base_eventually_beats_fixed_prefactors](BROWSER_Z77_1.md#node-f554286f9bccd51f). Strict-growth accounting converts repeated divisibility events into powers of two, while geometric domination compares those powers with a larger asymptotic rate; neither theorem supplies the chain or rate hypotheses of the other.
- incoming **complements**: [Z77::exact_tail_gcd_reduction_produces_primitive_coordinates](BROWSER_Z77_1.md#node-d3cff8fe64992dea). Primitive tail coordinates isolate the exact gcd whose strict growth is counted; the relation asserts only the intended coordinate interface, not a growth theorem.

