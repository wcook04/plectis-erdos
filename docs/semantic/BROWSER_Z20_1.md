# Z20_1: Skip and wire calculations with vacuity recorded

[All problems and zones](BROWSER.md)

<a id="node-8cb180fa59b8a7d3"></a>
## diagonal_band_plateau_transfer_wall_at_83

Every lcm-diagonal scale t at most 82 has a certified kill, but periodLcm 83 is not equal to periodLcm 82, so the plateau-rewrite transport used inside the finite band stops at 82. Moreover, any future certified kill at t = 83 must have depth at least 125.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This rules out only carrying the t = 81 certificate to t = 83 by equality of periodLcm values, and only excludes depths below 125 there. It does not prove that no t = 83 certificate exists, does not prevent a fresh computation at depth 125 or above, and does not address the still-open unbounded certificate supply consumed by the irrationality reduction.

- Lean declaration: [periodLcm_83_eq_mul](../../ErdosProblems/Skip/LadderT67.lean#L71281)
- Lean declaration: [band_maximal_at_82](../../ErdosProblems/Skip/LadderT67.lean#L71285)
- Lean declaration: [t83_depth_floor](../../ErdosProblems/Skip/LadderT67.lean#L71294)


<a id="node-93f424c1c977da2b"></a>
## diagonal_ladder_equal_depth_after_modulus_tripling

Although periodLcm 81 is three times periodLcm 79 and the arithmetic floor rises from 117 to 119, the least certified depth is 120 at both cells. This is a checked counterexample to the proposed law that each new prime-power rung must strictly increase the least certificate depth.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem rules out only strict increase at every prime-power rung. It does not give a transfer from t = 79 to t = 81, a formula for later depths, or evidence for a cofinal certificate supply.

- Lean declaration: [rung_depth_not_strictly_increasing](../../ErdosProblems/Skip/LadderT67.lean#L71332)


<a id="node-b356cc46f7d9658e"></a>
## diagonal_ladder_exact_minimal_depths

For the lcm-diagonal cells t = 71, 73, 79 and 81, the least depths L for which certifiedKill (periodLcm t) (periodLcm t) L holds are exactly 105, 113, 120 and 120, respectively. The bundled Lean theorem supplies both a certificate at each displayed depth and failure at every smaller depth.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Four exact finite cells do not supply certificates at arbitrarily large scales, do not predict the next firing depth, and do not prove irrationality of the totient series.

- Lean declaration: [ladder_minimal_depths](../../ErdosProblems/Skip/LadderT67.lean#L71342)


<a id="node-bdf4359372c531ef"></a>
## diagonal_ladder_sampled_excess_changes_direction

The checked certificate/failure pattern at t = 71, 73, 79 and 81 shows that the sampled excess of least certificate depth over its arithmetic floor decreases and increases: the displayed excesses along t = 67, 71, 73, 79, 81 are 2, 0, 2, 3, 1. In particular the floor is missed at t = 73, 79 and 81, and this finite sample is not monotone.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This refutes monotonicity only for the displayed finite table. It does not establish any eventual behaviour, distribution, or recurrence law for certificate depths.

- Lean declaration: [ladder_excess_not_monotone](../../ErdosProblems/Skip/LadderT67.lean#L71314)


<a id="node-51ce7279a596b690"></a>
## skip_existential_bound_conditional

PROVED: exists_bound_allRight_landingExcess_two_impossible states an existential threshold after which an all-right tail together with landing seam excess two gives a contradiction.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The audit found that the exhibited bound exceeds every D admitted by the theorem's own finite hypotheses, while the all-right alternative restates the unresolved achievement-set condition and landing seam excess two was not observed. No residue class is excluded by this headline theorem.

Open hypotheses: ["hright: the seam word extends right at every row from D+1 onward", "hlanding: Recon257.seamExcess (D+1) = 2"]

- Lean declaration: [exists_bound_allRight_landingExcess_two_impossible](../../ErdosProblems/Skip/D1.lean#L399)


