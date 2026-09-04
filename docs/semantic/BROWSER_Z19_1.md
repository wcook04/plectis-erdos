# Z19_1: Lift and reconstruction experiments with explicit hypothesis boundaries

[All problems and zones](BROWSER.md)

<a id="node-8d1b1526052c3eb0"></a>
## angle_b2_conditional_contradiction

PROVED: allRight_landingExcess_two_impossible derives False only from its displayed all-right, landing-excess-two, and three-row cofactor-support hypotheses. It does not state that a survivor set is empty.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The audit found the cofactor-support hypothesis false at D = 101, 122, 164, 314, 545, 629, and 1112, and found no observed landing seam excess equal to two in s = 5..102. Those observations are audit evidence, not additional Lean theorems.

Open hypotheses: ["hright: the seam word extends right at every row from D+1 onward", "hlanding: Recon257.seamExcess (D+1) = 2", "hcof: the required cofactor ranks lie in the seam-word support on rows D+1 through D+3"]

- Lean declaration: [allRight_landingExcess_two_impossible](../../ErdosProblems/Lift/AngleB2.lean#L432)


<a id="node-06c2d203443f78bc"></a>
## angle_b3_large_offset_nonrecurrence

PROVED: for a pulse sequence bounded above by Q, a ratchet orbit starting at b₀ at least Q+2 cannot return to its initial value at a positive time.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem applies only in the large-offset region b₀ ≥ Q+2. It does not cover the live offsets 1 through 9. The separate universal-barrier theorem has an unsatisfied initial hypothesis for the concrete use discussed in the audit.

Open hypotheses: ["hQ: P s ≤ Q for every row s", "hb: Q+2 ≤ b₀"]

- Lean declaration: [ratchetOrbit_no_recurrence](../../ErdosProblems/Lift/AngleB3.lean#L297)
- Lean declaration: [ratchetOrbit_pulseFloor_eq_recon257_ratchetRun](../../ErdosProblems/Lift/AngleB3.lean#L388)


<a id="node-2906a7b0ee52d691"></a>
## t67_diagonal_certificate_and_exact_minimal_depth

PROVED FINITE LADDER STEP: the lcm-diagonal cell t = 67 has least certified-kill depth exactly 100: depths 98 and 99 fail, the older t = 64 depth 93 cannot survive, and the result extends the certified finite band through t ≤ 70 using exact period-lcm plateaus.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This is one finite rung and a bounded band through 70. It neither supplies certificates at arbitrarily large scales nor proves irrationality in Erdős #249.

- Lean declaration: [certifiedKill_four_mul_lt](../../ErdosProblems/Lift/Recon67.lean#L69)
- Lean declaration: [certifiedKill_lift_depth](../../ErdosProblems/Lift/Recon67.lean#L76)
- Lean declaration: [certifiedKill_lift_depth_ladder](../../ErdosProblems/Lift/Recon67.lean#L87)
- Lean declaration: [t67_depth_floor](../../ErdosProblems/Lift/Recon67.lean#L105)
- Lean declaration: [t67_not_certifiedKill_at_t64_depth](../../ErdosProblems/Lift/Recon67.lean#L118)
- Lean declaration: [not_certifiedKill_diagonal_t67_98](../../ErdosProblems/Lift/Recon67.lean#L18808)
- Lean declaration: [not_certifiedKill_diagonal_t67_99](../../ErdosProblems/Lift/Recon67.lean#L18814)
- Lean declaration: [certifiedKill_diagonal_t67](../../ErdosProblems/Lift/Recon67.lean#L18821)
- Lean declaration: [t67_minimal_depth](../../ErdosProblems/Lift/Recon67.lean#L18827)
- Lean declaration: [exists_diagonalKill_le_70](../../ErdosProblems/Lift/Recon67.lean#L18852)


<a id="node-27a1c539c8513cd2"></a>
## t71_diagonal_certificate_and_exact_minimal_depth

PROVED FINITE LADDER STEP: the lcm-diagonal cell t = 71 has least certified-kill depth exactly 105, attaining its arithmetic floor; the t = 67 depth 100 is dead here, and the certificate plus the period-lcm plateau at 72 extends the conditional prior band through t ≤ 72.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The final band theorem assumes the earlier band through 70, and all conclusions remain finite. They do not give the cofinal certificate supply required by Erdős #249.

- Lean declaration: [certifiedKill_four_mul_lt71](../../ErdosProblems/Lift/CertT67.lean#L75)
- Lean declaration: [t71_depth_floor](../../ErdosProblems/Lift/CertT67.lean#L85)
- Lean declaration: [t71_not_certifiedKill_at_t67_depth](../../ErdosProblems/Lift/CertT67.lean#L99)
- Lean declaration: [certifiedKill_diagonal_t71](../../ErdosProblems/Lift/CertT67.lean#L21281)
- Lean declaration: [t71_minimal_depth](../../ErdosProblems/Lift/CertT67.lean#L21288)
- Lean declaration: [pl72](../../ErdosProblems/Lift/CertT67.lean#L21294)
- Lean declaration: [exists_diagonalKill_le_72_of_band_le_70](../../ErdosProblems/Lift/CertT67.lean#L21302)


