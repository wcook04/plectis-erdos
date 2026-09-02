# Erdős 1041: adaptive singleton-cluster limit and selection lab

Status: one ordinary exact analytic bridge plus deterministic floating-point
candidate evidence. 2026-08-27. This note does **not** prove unrestricted
Erdős 1041 and does not promote the numerical sweep to a theorem.

## 1. Exact singleton-cluster limit

Let `c` be a simple critical point of `f`, let `v=f(c)` be nonzero and distinct
from every other critical value, and suppose `|v|<1`. Let the two inverse lifts
of the open value segment from `0` to `v` start at roots `a,b` and converge to
`c`. Write `L(c)` for the total length of those two arms.

For sufficiently small `epsilon>0`, let

```text
Q_epsilon = B(v,epsilon)
```

and let `W_epsilon` be the component of `f^{-1}(Q_epsilon)` containing `c`.
Truncate the value segment at its first point `q_epsilon` on
`boundary Q_epsilon`, and call the truncated access arc `alpha_epsilon`.
Then `W_epsilon` is a Jordan domain and `f:W_epsilon->Q_epsilon` has degree
two. In the notation of `PartialClusterPreimagePerimeterIdentity.md`,

> **Theorem 1 (singleton limit).**
>
> ```text
> Lambda(alpha_epsilon,W_epsilon)
>   + (1/2) length(boundary W_epsilon)  ->  L(c).          (AS1)
> ```
>
> Equivalently, the mean of the two complete singleton-lollipop lifts tends
> to the canonical critical inverse-ray length `L(c)`.

### Proof

In a local holomorphic coordinate `zeta` at `c`,

```text
f(z)-v = A zeta^2 (1+O(zeta)),       A != 0.
```

Hence `W_epsilon` has diameter `O(sqrt(epsilon))`, and its boundary is the
inverse image of a circle under a uniformly nondegenerate perturbation of the
square map. Therefore

```text
length(boundary W_epsilon)=O(sqrt(epsilon)).
```

Away from a fixed small neighbourhood of `c`, the two inverse branches along
the access segment are regular and their truncated lifts converge in `C^1`.
Inside that neighbourhood, the omitted tails have length
`O(sqrt(epsilon))` by the same square-root coordinate. Thus the sum of the two
lifted stem lengths tends to the sum of the two complete arm lengths `L(c)`.
Adding half the vanishing boundary perimeter proves `(AS1)`. The exact
preimage-perimeter identity identifies the left side with the mean complete
lollipop length. ∎

### Consequence

If some admissible simple critical point satisfies `L(c)<2`, then all
sufficiently small singleton circles satisfy the strict partial-cluster budget
and prove the parent theorem through the landed transposition/closure consumer.
Thus the componentwise combined-charge producer is the singleton specialization
of the partial-cluster producer, while multi-critical clusters remain a genuine
fallback rather than a separate competing architecture.

## 2. Deterministic selection probe

The checker generates 252 configurations in degrees `3..9` from seed `1041`:
near-regular, random-circle, and two-cluster families, twelve rows per
degree/family. It appends the stored degree-six and degree-nine hard witnesses.
For every admissible critical value it draws a small isolating circle, continues
the complete lollipop lifts, and selects the best singleton only after
integration.

All 254 configurations have a selected moved-block mean below `1.93`; the
eight worst rows are rerun at higher resolution. The worst refined row is a
near-regular cubic at about `1.908`, and both pinned hard rows are below `1.90`.

This is evidence for attacking
`critical_point_selection_with_inverse_ray_length_control` and its
componentwise combined-charge form. It is not a proof of `min_c L(c)<=2`, an
interval certificate, or a universal cluster selector.

## 3. Selector correction

A one-start centre optimizer can return a legal all-critical-value circle whose
mean exceeds two even when another legal centre for the same critical set is
short. Such a row is an optimizer trap, not a mathematical counterexample.
Consequently packet work must distinguish:

1. a fixed numerical centre-selection heuristic;
2. existence of some circular isolating domain;
3. existence of an arbitrary Jordan isolating domain;
4. the singleton limit `L(c)`.

Only the first is falsified by a failed local optimizer. The present evidence
supports concentrating proof effort on the exact singleton/combined-charge
throat while retaining adaptive multi-cluster and Bergman/COVER failure
consumers.

## 4. Replay and claim boundary

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_adaptive_cluster_selection.py
```

Theorem 1 is ordinary exact complex analysis. The sweep uses IEEE-754 root
finding, Hungarian branch matching, and polygonal arclength, so every measured
margin remains candidate evidence only.
