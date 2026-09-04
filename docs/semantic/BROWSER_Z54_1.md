# Z54_1: Rank-one subrank obstruction for the Möbius–Mersenne ladder

[All problems and zones](BROWSER.md)

<a id="node-b15a60cbd0c84d33"></a>
## every_rank_one_strict_subrank_quotient_uniformly_overshoots_theta_two

For every e≥1 and prefix length Y≥4, 1/480 < mobiusMersennePrefix(Y,e+2)^2 / mobiusMersennePrefix(Y,2e+2) - Theta_2. Thus this exact rank-one quotient family stays a uniform positive distance above the #249 ladder target.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: candidate_new_statement.

Scope: The barrier applies only to this quotient with e≥1 and Y≥4. It does not exclude higher-rank determinants, other exponent patterns, nonlinear coordinates, or other finite-linear constructions, and it does not prove the target irrational.

- Lean declaration: [rankOneSubrankQuotient_sub_theta_two_gt](../../ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L238)

- outgoing **generated_by**: [Z54::high_mobius_mersenne_rungs_have_a_uniform_positive_floor](BROWSER_Z54_1.md#node-28c2de185bd7029a). The quotient proof applies the 1429/1512 floor to rungs e+2 and 2e+2 together with the residual prefix and upper-rung estimates.
- incoming **generalises**: [Z54::positive_finite_averaging_cannot_evade_the_rank_one_gap](BROWSER_Z54_1.md#node-d7fc43cdfd9acbd5). Strictly positive weights preserve the pointwise 1/480 margin, while a singleton family recovers the original obstruction.
- incoming **transport_of**: [Z54::rational_rank_one_realisations_give_linear_form_errors_growing_with_denominator](BROWSER_Z54_1.md#node-9936aa1f4bf61b0c). Substituting rankOneSubrankQuotient e Y=p/q, multiplying by q>0, and taking absolute values gives the stated linear-form bound.

<a id="node-28c2de185bd7029a"></a>
## high_mobius_mersenne_rungs_have_a_uniform_positive_floor

For every Möbius–Mersenne ladder rung r≥3, 1429/1512≤Theta_r.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The lower floor is not claimed sharp and proves no rationality or irrationality statement.

- Lean declaration: [mobiusMersenneTheta_ge_alpha](../../ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L163)

- incoming **generated_by**: [Z54::every_rank_one_strict_subrank_quotient_uniformly_overshoots_theta_two](BROWSER_Z54_1.md#node-b15a60cbd0c84d33). The quotient proof applies the 1429/1512 floor to rungs e+2 and 2e+2 together with the residual prefix and upper-rung estimates.

<a id="node-d7fc43cdfd9acbd5"></a>
## positive_finite_averaging_cannot_evade_the_rank_one_gap

Every nonempty finite weighted average of admissible rank-one quotients, with every weight strictly positive, remains more than 1/480 above Theta_2.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem requires a finite nonempty family and strictly positive weights. It does not cover signed weights, cancellation, zero-weight degeneracies, or infinite combinations.

- Lean declaration: [positive_direct_sum_sub_theta_two_gt](../../ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L300)

- outgoing **generalises**: [Z54::every_rank_one_strict_subrank_quotient_uniformly_overshoots_theta_two](BROWSER_Z54_1.md#node-b15a60cbd0c84d33). Strictly positive weights preserve the pointwise 1/480 margin, while a singleton family recovers the original obstruction.

<a id="node-9936aa1f4bf61b0c"></a>
## rational_rank_one_realisations_give_linear_form_errors_growing_with_denominator

If an admissible rank-one quotient is exactly p/q with q≥1, then q/480 < |q*Theta_2-p|.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem assumes an exact equality with p/q and neither produces such a representation nor assumes gcd(p,q)=1. Its bound applies only to rationals arising from this quotient family, not arbitrary rational approximants.

- Lean declaration: [primitive_form_abs_gt](../../ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L341)

- outgoing **transport_of**: [Z54::every_rank_one_strict_subrank_quotient_uniformly_overshoots_theta_two](BROWSER_Z54_1.md#node-b15a60cbd0c84d33). Substituting rankOneSubrankQuotient e Y=p/q, multiplying by q>0, and taking absolute values gives the stated linear-form bound.

