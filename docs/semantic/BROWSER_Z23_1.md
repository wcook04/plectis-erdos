# Z23_1: Remainder recurrences, bounded measurements, and their limits

[All problems and zones](BROWSER.md)

<a id="node-ce49e10135cd5443"></a>
## bounded_hit_gap_reduction

PROVED: a uniform bound on gaps between hit rows implies that one half belongs to the Mersenne achievement set.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The bounded-gap premise is not proved. The same file proves that the proposed bound eight is false.

Open hypotheses: ["h: HitGapBoundedBy K for some fixed natural number K"]

- Lean declaration: [half_mem_of_hitGapBoundedBy](../../ErdosProblems/Rem/C3.lean#L156)


<a id="node-d6573f73e8113001"></a>
## residual_invariant_refuted

PROVED: the predicate ResidualInvariant introduced for the remainder programme is false.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This refutes that invariant only. It does not refute every possible remainder invariant and does not resolve #257.

- Lean declaration: [not_residualInvariant](../../ErdosProblems/Three/T1.lean#L159)

- incoming **alias_of**: [Z24::residual_invariant_counterexample](BROWSER_Z24_1.md#node-269bddddfa866928). Both nodes cite the identical Lean proposition `ErdosProblems/Three/T1.lean:159:not_residualInvariant`. Z24 records its concrete witness s = 13, d = 7; Z23 records the same proposition as a barrier for the remainder programme. They are two presentations of one checked statement, not two results.

