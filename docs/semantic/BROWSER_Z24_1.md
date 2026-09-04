# Z24_1: Three-branch recurrence and exact counterexamples

[All problems and zones](BROWSER.md)

<a id="node-5257b790527253b5"></a>
## perturbed_doubling_recurrence

PROVED: the successor remainder obeys an exact perturbed doubling identity with explicitly bounded carry and error terms; under no successor carry, the sharper bounds n ≤ 1 and E ≤ 2s hold.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This proves the branch that Rem/C3 had originally recorded only as measured. The resulting global carry hypotheses remain open.

- Lean declaration: [remainder_succ_perturbed_doubling](../../ErdosProblems/Three/T2.lean#L412)
- Lean declaration: [remainder_succ_perturbed_doubling_of_not_carry](../../ErdosProblems/Three/T2.lean#L433)


<a id="node-269bddddfa866928"></a>
## residual_invariant_counterexample

PROVED: ResidualInvariant is false, with the failure witnessed at s = 13 and d = 7.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The counterexample invalidates the universal invariant. It does not imply that no corrected invariant can exist.

- Lean declaration: [not_residualInvariant](../../ErdosProblems/Three/T1.lean#L159)

- outgoing **alias_of**: [Z23::residual_invariant_refuted](BROWSER_Z23_1.md#node-d6573f73e8113001). Both nodes cite the identical Lean proposition `ErdosProblems/Three/T1.lean:159:not_residualInvariant`. Z24 records its concrete witness s = 13, d = 7; Z23 records the same proposition as a barrier for the remainder programme. They are two presentations of one checked statement, not two results.

