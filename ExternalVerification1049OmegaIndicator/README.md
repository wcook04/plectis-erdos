# ExternalVerification1049OmegaIndicator

Prepared locally during the r7 paper-complete Lean assimilation for Erdős
problem 1049. No Palomar submission has been made and no public repository has
been touched.

## Statement

See `Challenge.lean`. The challenge file imports only `Mathlib` and states the
theorem in Mathlib vocabulary with `sorry`. `Solution.lean` proves the same
statement token for token by transporting the live declaration from
`ErdosProblems/Erdos1049/`.

## Mechanism

The interval from zero to one is partitioned at all forty-eight rational
breakpoints induced by the denominators 12, 13, 14 and 15. On each cell the
four floor values are fixed from the cell bounds, and membership in the
thirteen-interval support is then decided by integer arithmetic. Every cell is
handled for every real point it contains. 

## Boundary

Erdős problem 1049 is open. This package proves a lemma of the surrounding
construction. It contains no irrationality statement, no irrationality-exponent
bound, and nothing that bears on the parent problem.

Permitted axioms are `propext`, `Classical.choice` and `Quot.sound`; see
`AxiomAudit.lean`.
