# Erdős #243 repair entropy

This package exposes three Lean-checked consequences of the exact reduced-tail
recovery calculus:

- a repaired finite family pays the square of its transversal LCM inside the
  recovery product budget;
- an independent repaired family satisfies the resulting cardinality bound;
- normalized vanishing forces every sufficiently late recovery of any fixed
  positive length to have trivial total cancellation payment.

These are conditional state-system theorems. They do not control recovery
lengths tending to infinity, do not prove a positive repair-LCM entropy rate,
and do not solve Erdős #243.

`Challenge.lean` imports only Mathlib and contains the trusted specification
placeholders. `Solution.lean` transports the exact source declarations from
`ErdosProblems/Erdos243/RepairEntropy.lean`. The negative fixture deliberately
drops the square on the repaired-family LCM and must be rejected.
