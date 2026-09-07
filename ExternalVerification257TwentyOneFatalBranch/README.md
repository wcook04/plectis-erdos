# Erdős #257: exact denominator-21 fatal branch

This statement-isolated package exposes five Lean-checked endpoints from the
denominator-`21` quotient-greedy analysis:

- every closed row, including exact saturation, is the canonical integer-
  greedy row;
- a closed lower state at every even depth already represents `1/21`;
- membership of `1/21` is equivalent to excluding one explicit fatal,
  cofinite, quotient/rational-aligned branch;
- inside that branch the canonical remainder is eventually strictly above
  binary capacity; and
- the same branch eventually follows one exact affine support-and-remainder
  recurrence.

The central boundary is literal: the package classifies the sole surviving
nonmembership regime but does **not** prove that the regime is impossible and
does not prove membership of `1/21` unconditionally.

`Challenge.lean` imports only Mathlib. `Solution.lean` transports the
source-current proofs from `TwentyOneQuotientGreedy.lean`. `AxiomAudit.lean`
prints the axiom roster for all five selected declarations. The deliberate
negative fixture omits the required declaration surface and is expected to be
rejected by Comparator.
