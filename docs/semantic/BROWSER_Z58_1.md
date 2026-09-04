# Z58_1: Summable Mersenne-gap mass and explicit geometric tails

[All problems and zones](BROWSER.md)

<a id="node-a2ca6aa4b11fb304"></a>
## every_shifted_mersenne_gap_sequence_is_summable

For every cutoff N, the nonnegative sequence k ↦ mersenneGap(N+k+1) is summable.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Scalar summability says nothing about which gaps are encountered by the greedy orbit and supplies no achievement-set membership or nonmembership result.

- Lean declaration: [summable_mersenneGap_shift](../../Erdos249257/HalfGapMass.lean#L69)

- outgoing **generated_by**: [Z58::mersenne_gap_has_an_explicit_two_scale_pointwise_upper_envelope](BROWSER_Z58_1.md#node-fc841ca7d0d07349). Nonnegativity and domination by the two shifted geometric envelopes prove summability for every cutoff.
- incoming **generated_by**: [Z58::remaining_mersenne_gap_mass_has_an_explicit_geometric_tail_bound](BROWSER_Z58_1.md#node-7f1ff6799986438e). Summability licenses termwise comparison and splitting of the two geometric envelope sums.

<a id="node-fc841ca7d0d07349"></a>
## mersenne_gap_has_an_explicit_two_scale_pointwise_upper_envelope

For every positive n, mersenneGap n ≤ (2/3)*4^(-n)+3*8^(-n).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is only a one-sided upper bound for n>0, not an equality or a sharp asymptotic constant.

- Lean declaration: [mersenneGap_le](../../Erdos249257/HalfGapMass.lean#L40)

- incoming **generated_by**: [Z58::every_shifted_mersenne_gap_sequence_is_summable](BROWSER_Z58_1.md#node-a2ca6aa4b11fb304). Nonnegativity and domination by the two shifted geometric envelopes prove summability for every cutoff.
- incoming **generated_by**: [Z58::remaining_mersenne_gap_mass_has_an_explicit_geometric_tail_bound](BROWSER_Z58_1.md#node-7f1ff6799986438e). Summing the pointwise 4-adic and 8-adic terms produces the constants 2/9 and 3/7.

<a id="node-7f1ff6799986438e"></a>
## remaining_mersenne_gap_mass_has_an_explicit_geometric_tail_bound

For every N, the infinite sum over k≥0 of mersenneGap(N+k+1) is at most (2/9)*4^(-N)+(3/7)*8^(-N). The summed indices are strictly beyond level N.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem gives an upper envelope, not a matching lower bound or the asymptotic equivalence (2/9)*4^(-N). It is not a measure, covering, Borel–Cantelli, category, or probabilistic theorem.

- Lean declaration: [mersenneGap_tail_le](../../Erdos249257/HalfGapMass.lean#L83)

- outgoing **generated_by**: [Z58::every_shifted_mersenne_gap_sequence_is_summable](BROWSER_Z58_1.md#node-a2ca6aa4b11fb304). Summability licenses termwise comparison and splitting of the two geometric envelope sums.
- outgoing **generated_by**: [Z58::mersenne_gap_has_an_explicit_two_scale_pointwise_upper_envelope](BROWSER_Z58_1.md#node-fc841ca7d0d07349). Summing the pointwise 4-adic and 8-adic terms produces the constants 2/9 and 3/7.
- incoming **generated_by**: [Z58::remaining_mersenne_gap_mass_tends_to_zero](BROWSER_Z58_1.md#node-4f142c304ac61021). The nonnegative gap tail is squeezed between zero and two geometric terms tending to zero.

<a id="node-4f142c304ac61021"></a>
## remaining_mersenne_gap_mass_tends_to_zero

As N tends to infinity, the shifted total gap mass ∑ k, mersenneGap(N+k+1) tends to zero.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This deterministic analytic budget is not a cofinal producer, certifies no real such as 1/2, and does not settle Erdős #257.

- Lean declaration: [tendsto_mersenneGap_tail_zero](../../Erdos249257/HalfGapMass.lean#L104)

- outgoing **generated_by**: [Z58::remaining_mersenne_gap_mass_has_an_explicit_geometric_tail_bound](BROWSER_Z58_1.md#node-7f1ff6799986438e). The nonnegative gap tail is squeezed between zero and two geometric terms tending to zero.

