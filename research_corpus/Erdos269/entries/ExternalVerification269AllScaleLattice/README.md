# Erdős #269: all-scale rationality lattice and collision target

This package exposes the full arithmetic reduction for the actual
`{2,3,5}` running-LCM shell tail. It first proves the symmetric prime-power
clearing law: below any boundary `r^m`, for `r` equal to `2`, `3`, or `5`, the
running height has one additional factor `r` available. Thus the dyadic
normalizer used by the orbit is one member of three exact boundary families.
It then proves that finite shell windows clear at every dyadic scale and that,
if the full value is `p/q`, every normalized tail state

```text
X_a = (H(2^a)/2) T_a
```

lies simultaneously on the `(1/q)`-lattice. Pigeonhole modulo `1` then forces
two distinct scales with `X_j-X_i` integral. Consequently pairwise
incongruence of the actual states modulo `1` would prove irrationality.

The six endpoints are ordered by mathematical signal: the all-scale lattice
and forced collision first, then prime-power clearing, infinite-tail splitting,
finite-window clearing, and the half-height identity. This is the exact
general-denominator target, not an irrationality theorem:
the source does not yet prove pairwise incongruence or exclude every forced
collision. `Challenge.lean` is Mathlib-only; the deliberate negative weakens
the essential positive-denominator hypothesis and must be rejected. Focused
Challenge, Solution, deliberate-negative, and axiom-audit builds pass, with
the five original endpoints previously passed focused checking. The newly
exposed prime-power endpoint and reordered six-endpoint package require a fresh
focused and axiom receipt. Terminal Comparator/NanoDa replay is still required
before submission readiness.
