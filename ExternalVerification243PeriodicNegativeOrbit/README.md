# Erdős #243: periodic negative-orbit exclusion

This package exposes the complete three-step exclusion of periodic negative
magnitudes in the exact reciprocal-tail orbit.  The mathematical mechanism is
not a finite helper: phase-wise congruence forces every multiplier to share a
prime with the positive drift; repeated prime divisors create a common scale;
and strong induction divides out that scale until the phase-primitive
pigeonhole contradiction applies.  Shifting the orbit gives the eventual-tail
endpoint.

The selected declarations are ordered strongest first:

| Comparator declaration | Exact paper route | Checked source route |
|---|---|---|
| `no_eventuallyPeriodicNegative_orbit` | `res:periodic` (eventual form after the proof) | `Erdos243/ReciprocalTailRigidity.lean:796` |
| `no_periodicNegative_orbit` | `res:periodic` | `Erdos243/ReciprocalTailRigidity.lean:690` |
| `no_phasePrimitivePeriodicNegative_orbit` | `res:periodic` (first proof case) | `Erdos243/ReciprocalTailRigidity.lean:548` |

The theorem is conditional on the exact recurrence, positive drift, periodic
positive magnitude, and the genuine bound `e n < a n`.  The paper explicitly
records that this bound is assumed rather than derived in the abstract model.
The package therefore excludes a major structured tail but does not solve the
unrestricted parent problem.

The portfolio-relative Plectis Signal is provisionally 87/100.  This is an
editorial reading priority, not proof authority, novelty, Palomar acceptance,
mechanical readiness, or submission authorization.  Focused source/challenge/
solution/deliberate-negative/axiom-audit elaboration passes, and all three
selected declarations use exactly `propext`, `Quot.sound`, and
`Classical.choice`.  Terminal Comparator/NanoDa replay remains required before
submission readiness.
