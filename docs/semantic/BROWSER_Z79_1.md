# Z79_1: Erdős 257 Mersenne digit terms: summability under every binary selector

[All problems and zones](BROWSER.md)

<a id="node-a35c61d95434e13e"></a>
## every_binary_mersenne_digit_series_is_summable

For every binary selector b : Nat -> Fin 2, the real series with kth term mersenneDigitTerm k b = b(k) * mersenneWeight (k+1) is summable. The proof is uniform in b: each digit is 0 or 1, so the term norm is bounded by mersenneWeight (k+1), whose series is already summable.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This theorem establishes analytic summability only. It does not compute the sum, prove uniqueness or injectivity of the digit coding, state the one-coordinate update formula, classify an achievement set or its measure, constrain the selected support, or settle any irrationality assertion in Problem 257.

- Lean declaration: [summable_mersenneDigitTerm](../../ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L175)


