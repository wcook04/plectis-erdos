# Z71_1: Erdős 251 finite dyadic partial-sum successor laws

[All problems and zones](BROWSER.md)

<a id="node-7c3444b3443bd5db"></a>
## dyadic_partial_sums_gain_exactly_the_new_last_term

Increasing the cutoff from n to n+1 adds exactly P(n)/2^(n+1) to the finite dyadic partial sum, and adds exactly (P(n+1)-P(n))/2^(n+1) to its forward-difference partial sum.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These identities concern arbitrary finite rational sequences. They do not prove summability of the prime or prime-gap series, identify an infinite tail, or settle Erdős 251.

- Lean declaration: [dyadicPartialSumQ_succ](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L124)
- Lean declaration: [dyadicDifferencePartialSumQ_succ](../../ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L129)


