# Erdős #257: Boolean–Möbius carry characterization

This Comparator package exposes the complete source-current correspondence
between normalized supports of a rational Mersenne value and quotient-only
Boolean–Möbius carry certificates:

- a support fraction produces a positive, square-root-bounded integral carry
  and reconstructs the original support;
- a carry certificate reconstructs a normalized support and its exact rational
  value;
- the reconstruction theorem also exposes the divisor-incidence coefficient,
  tempered orbit, Möbius-selected support and scalar value; and
- the two existence statements are equivalent.

This is an exact characterization, not an irrationality theorem. Finite
supports already yield certificates for their rational values, and the formal
results do not exclude infinite Boolean carry paths. The package is therefore
subordinate to the unconditional irrationality and achievement-set families
for Erdős #257.

`Challenge.lean` imports only Mathlib and repeats every definition appearing in
the theorem types. `Solution.lean` transports the checked source declarations
from `Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean`. The deliberate
negative changes the type of the final equivalence by adding one `True`
argument, so Comparator must reject it.
