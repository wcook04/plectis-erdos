# Z67_1: Exact Möbius–Lambert and foreign-residue coordinates for the totient tail

[All problems and zones](BROWSER.md)

<a id="node-06c159f9d623229f"></a>
## a_uniform_reduced_numerator_gap_forces_a_full_target_miss

Fix H,D and a natural m. If the reduced numerator of lambertProjectedDiagonalRat(H,D) stays at distance at least m from every integer multiple of its reduced denominator, and the Lambert square-complement bound multiplied by that denominator is strictly less than m, then ScaleFullTargetHit(H) is false.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This consumer does not construct m, prove the uniform numerator gap, establish the analytic bound, produce a cofinal family of heights, or imply irrationality; its conclusion concerns one fixed height H.

Open hypotheses: ["Produce a natural m that uniformly separates the reduced numerator of lambertProjectedDiagonalRat(H,D) from every integer multiple of its reduced denominator.", "Prove that the Lambert square-complement bound at H,D, after multiplication by that reduced denominator, is strictly smaller than m."]

- Lean declaration: [scaleFullTarget_miss_of_lambert_projected_num_gap](../../Erdos249257/LambertProjectedNumeratorGap.lean#L23)

- outgoing **complements**: [Z67::renormalized_residue_projection_equals_the_lambert_center_past_twice_the_height](BROWSER_Z67_1.md#node-975cd5c44da15eac). Coordinate agreement identifies the residue and Lambert centers; the numerator-gap theorem is a distinct conditional separation consumer and must not be conflated with that agreement.

<a id="node-e24bead2fcdcbe50"></a>
## absolute_lambert_pair_regrouping_respects_arbitrary_product_filters

Let w,v : ℕ → ℝ satisfy |w(d)| ≤ d and |v(m)| ≤ m at positive indices, let P be any decidable predicate on ℕ, and let 0 ≤ x < 1. Then the absolutely convergent positive-pair sum of w(d)v(m)x^(dm), restricted by P(dm), equals the positive-index sum whose nth coefficient is the divisor sum ∑_{e∣n} w(e)v(n/e), restricted by P(n).

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is an exact real-series regrouping on 0 ≤ x < 1. It does not cover x=1, assert positivity of either weight, or imply integrality, irrationality, or target avoidance.

- Lean declaration: [tsum_lambert_pair_regroup_if](../../Erdos249257/TotientShiftedMobiusPulse.lean#L124)

- incoming **generated_by**: [Z67::literal_totient_tail_is_the_exact_shifted_mobius_pulse_sum](BROWSER_Z67_1.md#node-6a5d0ca5ee46d0b3). The shifted-pulse theorem applies the generic restricted Lambert regrouping to the strict-tail predicate and then evaluates the divisor fibres.

<a id="node-f4b6d09bc21ecc1e"></a>
## explicit_mobius_shadow_is_exactly_the_divisor_residue_channel_sum

For every positive height H, scaleExplicitShadow(H) equals the finite sum of residueIncrement(d,H) over the positive divisors d of H.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This identifies only the divisor-indexed residue channels. It does not identify the full infinite foreign-residue tail and does not supply a separation or target-miss conclusion.

- Lean declaration: [scaleExplicitShadow_eq_sum_divisors_residueIncrement](../../Erdos249257/ActualForeignResidueProjection.lean#L338)

- outgoing **complements**: [Z67::literal_totient_tail_is_the_exact_positive_index_foreign_residue_kernel_sum](BROWSER_Z67_1.md#node-6313ac05eaa1b04e). The finite shadow identity controls the divisor-indexed residue channels, while the global kernel identity controls the complete positive-index tail coordinate.
- incoming **generated_by**: [Z67::renormalized_residue_projection_equals_the_lambert_center_past_twice_the_height](BROWSER_Z67_1.md#node-975cd5c44da15eac). The agreement proof replaces the divisor part of the finite residue split by scaleExplicitShadow using this exact identity, alongside other tail inputs.

<a id="node-6313ac05eaa1b04e"></a>
## literal_totient_tail_is_the_exact_positive_index_foreign_residue_kernel_sum

For every N, totientTail(N) is exactly the convergent sum over positive d of positiveForeignResidueKernel(d,N).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Here “positive” describes the positive-natural index type, not the sign of the summand: the kernel contains a Möbius factor and is not asserted nonnegative. The identity alone gives no separation, nonvanishing, irrationality, or target-miss theorem.

- Lean declaration: [totientTail_eq_tsum_positiveForeignResidueKernel](../../Erdos249257/TotientShiftedMobiusForeignBridge.lean#L61)

- outgoing **reformulates**: [Z67::literal_totient_tail_is_the_exact_shifted_mobius_pulse_sum](BROWSER_Z67_1.md#node-6a5d0ca5ee46d0b3). The foreign-residue theorem rewrites the shifted-pulse sum pointwise through positiveForeignResidueKernel_eq_shiftedMobiusPulseTerm.
- incoming **complements**: [Z67::explicit_mobius_shadow_is_exactly_the_divisor_residue_channel_sum](BROWSER_Z67_1.md#node-f4b6d09bc21ecc1e). The finite shadow identity controls the divisor-indexed residue channels, while the global kernel identity controls the complete positive-index tail coordinate.
- incoming **generated_by**: [Z67::renormalized_residue_projection_equals_the_lambert_center_past_twice_the_height](BROWSER_Z67_1.md#node-975cd5c44da15eac). The agreement proof uses the global foreign-residue kernel identity as its exact infinite-tail representation input, together with additional tail identities.

<a id="node-6a5d0ca5ee46d0b3"></a>
## literal_totient_tail_is_the_exact_shifted_mobius_pulse_sum

For every N, the literal tail totientTail(N) is exactly the convergent sum over positive d of the shifted Möbius pulse μ(d)·2^(d-r_d(N))·((⌊N/d⌋+1)/(2^d-1) + 1/(2^d-1)^2), where r_d(N)=d-(N mod d).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The equality is an exact coordinate formula, not a sign or noncancellation result. It neither proves the tail nonzero nor yields integrality, irrationality, or target avoidance by itself.

- Lean declaration: [totientTail_eq_tsum_shiftedMobiusPulse](../../Erdos249257/TotientShiftedMobiusPulse.lean#L547)

- outgoing **generated_by**: [Z67::absolute_lambert_pair_regrouping_respects_arbitrary_product_filters](BROWSER_Z67_1.md#node-e24bead2fcdcbe50). The shifted-pulse theorem applies the generic restricted Lambert regrouping to the strict-tail predicate and then evaluates the divisor fibres.
- incoming **reformulates**: [Z67::literal_totient_tail_is_the_exact_positive_index_foreign_residue_kernel_sum](BROWSER_Z67_1.md#node-6313ac05eaa1b04e). The foreign-residue theorem rewrites the shifted-pulse sum pointwise through positiveForeignResidueKernel_eq_shiftedMobiusPulseTerm.

<a id="node-975cd5c44da15eac"></a>
## renormalized_residue_projection_equals_the_lambert_center_past_twice_the_height

For every H>0 and every cutoff D with 2H≤D, renormalizedResidueProjection(H,D) equals lambertProjectedDiagonal(H,D). Equivalently, the explicit divisor shadow, projected foreign defect, and rational first-tail correction combine exactly into the canonical Lambert projected center.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The cutoff condition is part of the theorem. Coordinate agreement is not rational separation: this theorem does not provide a numerator gap, bound the analytic complement, prove target avoidance, or establish irrationality.

- Lean declaration: [renormalizedResidueAgreement_of_twice_le](../../Erdos249257/TotientShiftedMobiusForeignBridge.lean#L338)

- outgoing **generated_by**: [Z67::literal_totient_tail_is_the_exact_positive_index_foreign_residue_kernel_sum](BROWSER_Z67_1.md#node-6313ac05eaa1b04e). The agreement proof uses the global foreign-residue kernel identity as its exact infinite-tail representation input, together with additional tail identities.
- outgoing **generated_by**: [Z67::explicit_mobius_shadow_is_exactly_the_divisor_residue_channel_sum](BROWSER_Z67_1.md#node-f4b6d09bc21ecc1e). The agreement proof replaces the divisor part of the finite residue split by scaleExplicitShadow using this exact identity, alongside other tail inputs.
- incoming **complements**: [Z67::a_uniform_reduced_numerator_gap_forces_a_full_target_miss](BROWSER_Z67_1.md#node-06c159f9d623229f). Coordinate agreement identifies the residue and Lambert centers; the numerator-gap theorem is a distinct conditional separation consumer and must not be conflated with that agreement.

