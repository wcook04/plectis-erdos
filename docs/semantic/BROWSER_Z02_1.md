# Z02_1: Diagonal-pincer finite kills, lower window tranche (t = 29, 31, 37)

[All problems and zones](BROWSER.md)

<a id="node-8747b08e0d7df4ce"></a>
## aggregate_imported_scales_fire

The historical list aggregates bundle the checked diagonal kills through t = 29, 31, and 37. The current finite aggregate states that every natural t at most 82 has some depth L with certifiedKill (periodLcm t) (periodLcm t) L. These packages add no arithmetic beyond the individual finite kills and plateau transfers.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The current aggregate is silent at t = 83. A longer finite band is still finite and does not supply remaining_open.unbounded_certificate_supply, which is what the irrationality reduction consumes.

- Lean declaration: [certifiedKill_diagonal_all_imported_through_t29](../../Erdos249257/DiagonalPincerCertificatesT29.lean#L1013)
- Lean declaration: [certifiedKill_diagonal_all_imported_through_t31](../../Erdos249257/DiagonalPincerCertificatesT31.lean#L1110)
- Lean declaration: [certifiedKill_diagonal_all_imported_through_t37](../../Erdos249257/DiagonalPincerCertificatesT37.lean#L1268)
- Lean declaration: [exists_diagonalKill_le_82](../../ErdosProblems/Skip/LadderT67.lean#L71264)

- incoming **specialises**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). Z01's `totient_tail_period_lcm_diagonal_killed_upto_six` and `..._at_seven_and_eight` assert the diagonal kill at the scales t <= 8, which are members of the literal list quantified over by Z02's `certifiedKill_diagonal_all_imported_through_t29`; depth differences are absorbed by the depth-monotonicity theorem `certifiedKill_succ` (Z06).

