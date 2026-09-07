# Erdős #68: moving-factor scale split

This package exposes the strongest source-current private-factor family that
was already present in Lean and in the paper but missing from Comparator and
the Palomar portfolio.

It selects three coherent endpoints, strongest first:

1. `movingPrivateFactorScaleSplit_implies_irrational`: one canonical moving
   prefix-private prime and two explicit scale bounds imply irrationality;
2. `splitFactorNormalizedCollision_implies_irrational`: arbitrary factors of
   one moving private modulus give a more flexible normalized-collision
   criterion, so two denominator owners are unnecessary;
3. `fixedOwnerPair_eventually_absorbed`: every fixed pair of owners eventually
   has private quotient one.

The two irrationality theorems are conditional.  They do not supply the
cofinal scale inequalities or projection disagreements, and the package does
not solve Erdős #68.

## Exact routes

- source:
  `ErdosProblems/Erdos68/PrimeZeroBranch.lean` and
  `ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean`;
- paper:
  `ErdosProblems/papers/erdos-68-factorial-denominator-irrationality.tex` at
  `res:moving-factor-scale-split`,
  `res:split-factor-normalized-collision`, and
  `bdry:fixed-owner-absorption`;
- public-base patch:
  `ErdosProblems/papers/erdos-68-companion-orbit-equivalence.patch`;
- Comparator:
  `comparator.json`, with the exact permitted axiom trio and NanoDa enabled;
- deliberate mismatch fixture:
  `comparator-negative-mismatch.json`.

The Challenge is 196 lines and 6,437 bytes, below Palomar's preferred
300-line/32-KiB review threshold.  It imports only Mathlib and carries three
intentional specification `sorry`s.  `Solution.lean` imports the proof-bearing
source and contains no intentional placeholder.  Focused source/challenge/
solution/deliberate-negative/axiom-audit elaboration passes, and all three
selected declarations use exactly `propext`, `Quot.sound`, and
`Classical.choice`.  Terminal Comparator/NanoDa replay remains a separate
mechanical gate until its receipt is recorded.

The canonical portfolio ledger assigns this conditional family Plectis Signal
28/100.  The statements are real irrationality implications, so the paper
places them ahead of bare equivalence coordinates; their unproved scale
producers retain most of the parent difficulty, so they remain below the
unconditional channel-radius obstruction and other burden-discharging results.
The score ranks reader attention only: it is not proof authority, novelty,
Palomar acceptance, or submission authorization.
