# Z26_1: Failure of the hlow condition and conversion to hit certificates

[All problems and zones](BROWSER.md)

<a id="node-43855392c3bb1bf9"></a>
## hlow_failure_gives_hit

PROVED: under BitAdmissible, failure of hlow forces the seam remainder below 2^s; in particular the seven-five failure certifies that row seven is a hit.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: A single hit or conditional hit conversion does not prove the cofinal supply required for membership of one half.

Open hypotheses: ["h: BitAdmissible s d", "hfail: the hlow inequality fails at s,d"]

- Lean declaration: [seamRemainder_lt_two_pow_of_not_hlow](../../ErdosProblems/Hlow/H2.lean#L294)
- Lean declaration: [seven_is_a_hit_from_failure](../../ErdosProblems/Hlow/H2.lean#L397)


<a id="node-940d50d1abb265c3"></a>
## universal_hlow_refuted

PROVED: the universal hlow implication, even with its hhigh premise, is false.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This closes the proposed universal side condition, not the achievement-set problem.

- Lean declaration: [not_hlow_of_hhigh](../../ErdosProblems/Hlow/H1.lean#L441)


