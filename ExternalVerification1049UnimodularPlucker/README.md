# ExternalVerification1049UnimodularPlucker

Prepared locally during the r7 paper-complete Lean assimilation for Erdős
problem 1049. No Palomar submission has been made and no public repository has
been touched.

## Statement

See `Challenge.lean`. The challenge file imports only `Mathlib` and states the
theorem in Mathlib vocabulary with `sorry`. `Solution.lean` proves the same
statement token for token by transporting the live declaration from
`ErdosProblems/Erdos1049/`.

## Mechanism

Unimodularity of a row gives a Bezout identity, and the vanishing adjacent
minor propagates that identity along the sequence, so every pairwise minor
vanishes. Over the ring of integers modulo 2^S times 3^R the collapsed rows
span a one-parameter image, and the pigeonhole principle on binary selectors of
width S + 2R then produces the collision. 

## Boundary

Erdős problem 1049 is open. This package proves a lemma of the surrounding
construction. It contains no irrationality statement, no irrationality-exponent
bound, and nothing that bears on the parent problem.

Permitted axioms are `propext`, `Classical.choice` and `Quot.sound`; see
`AxiomAudit.lean`.
