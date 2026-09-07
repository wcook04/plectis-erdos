# Erdős #1041: the separation-or counterexample

An explicit monic cubic has both critical values on distinct positive rays with
least critical modulus above `13/25`, and normalised critical-value separation
below `2/375`. Every clause is kernel-checked. Erdős Problem #1041 itself
remains open.

## Statement

There is a monic cubic over `ℂ` with every zero in the open unit disc, exactly
two critical points, both simple, whose critical values lie on distinct positive
rays, whose least critical modulus exceeds `13/25`, and whose normalised
critical-value separation satisfies

```
‖1 - f(c₋) / f(c₊)‖ < 2/375 < 2.
```

The witness is `f(z) = z³ + (3/100) z - 3/4`, with critical points `± i/10`.

## Mechanism

The critical points come from the exact factorisation
`f'(z) = 3 (z - i/10) (z + i/10)`, which also gives simplicity through
`f''(z) = 6z`. The two critical values are `-3/4 ± i/500`, so they have equal
modulus `μ`, and `μ² = 9/16 + 1/250000` puts `μ` above `3/4` and hence above
`13/25`. The least-modulus claim is the two-element `IsLeast` over the critical
set, not an assumed minimum. Ray separation is decided by comparing real and
imaginary parts: no positive real scalar carries one critical value to the
other. The normalised separation is the exact identity
`1 - f(c₋)/f(c₊) = (i/250) / f(c₊)`, whose modulus is `(1/250)/μ`.

Root containment is proved from the root equation and the triangle inequality,
without Rouché.

## Boundary

Erdős Problem #1041 is open. This entry is a counterexample to a covering
reading of a separation criterion: it shows that distinct critical-value rays
and a critical modulus above `13/25` do not by themselves force a large
normalised separation. It gives no path, no length bound, and no progress on
the parent problem.

The Challenge states the proposition over Mathlib alone. The Solution supplies
the witness and transports the local theorems of
`ErdosProblems/Erdos1041/PaperSeparationCounterexample.lean`.

## Files

| File | Role |
|---|---|
| `Challenge.lean` | Mathlib-only statement, `sorry`-ed. |
| `Statements.lean` | Shared namespace anchor imported by the Solution. |
| `Solution.lean` | Same statement, proved by transport from the live module. |
| `AxiomAudit.lean` | `#print axioms` driver for the Solution's theorem. |
| `comparator.json` | Theorem name and the three permitted axioms. |
| `formalization.yaml` | Entry metadata, status, and boundary. |

## Verification state (r7 wave 2, 2026-09-07)

`Challenge.lean` elaborates under the pinned toolchain with rc 0 and the expected
`sorry` warning. `Solution.lean` has not yet elaborated in place: its
`ExternalVerification1041SeparationOrCounterexample` lib entry is not in
`lakefile.toml`, and it imports
`ErdosProblems.Erdos1041.PaperSeparationCounterexample`, whose `.olean` only the
serialized project build produces.

The transport was verified through a probe instead. One file inlined the
byte-copy of `ErdosProblems/Erdos1041/PaperSeparationCounterexample.lean` ahead
of the byte-copy of this Solution's theorem, importing only
`ErdosProblems.Erdos1041.NewtonFlowRaySeparation` and Mathlib. It elaborated
with rc 0 and `#print axioms` gave exactly `propext`, `Classical.choice`,
`Quot.sound`, the three permitted in `comparator.json`. The Solution's proof term
therefore closes the Challenge statement from the live declarations with no
`sorryAx`. What is still unverified is the two-module import wiring, not the
mathematics.

The source module `PaperSeparationCounterexample.lean` itself elaborates rc 0
with the same three axioms.
