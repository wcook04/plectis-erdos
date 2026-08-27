# Erdős #1041: the centroid is a canonical interior metric hub

Status: analytic theorem, 2026-08-24.  The exact five-point variance and
pair-budget kernel passed its canonical cached Lean build on 2026-08-24.
This closes the metric and basepoint
parts of the two-segment mechanism at one canonical polynomial-adapted hub in
every degree.  It does **not** prove that the two required straight spokes stay
in the unit lemniscate, and therefore does not solve unrestricted Erdős #1041.

## Theorem

Let `a_1,...,a_n` be points in the open unit disk, with `n>=2`, and let

```text
h = (a_1+...+a_n)/n,
f(z) = product_j (z-a_j).
```

Then

```text
|f(h)| < 1,                                             (1)
```

and there are distinct indices `i,j` such that

```text
|a_i-h|+|a_j-h| < 2.                                   (2)
```

Thus the centroid is always strictly inside the unit lemniscate and always
lies in the open major-axis-two ellipse of at least one pair of roots.  If the
two corresponding centroid spokes are contained in `{|f|<1}`, their broken
line proves the Erdős conclusion.

## Proof

Write `d_j=|a_j-h|` and `S=sum_j d_j^2`.  Expanding about the centroid gives the
variance identity

```text
S = sum_j |a_j|^2 - n|h|^2 < n.                        (3)
```

The strict inequality uses only `|a_j|<1`.  Arithmetic-geometric mean applied
to the nonnegative numbers `d_j^2` now gives

```text
|f(h)|^2 = product_j d_j^2 <= (S/n)^n < 1,
```

which proves (1).

For (2), suppose instead that `d_i+d_j>=2` for every unordered pair.  Squaring
and summing over all pairs gives

```text
2n(n-1) <= sum_{i<j}(d_i+d_j)^2.                       (4)
```

But the pair sum has the exact form

```text
sum_{i<j}(d_i+d_j)^2
  = (n-2)S + (sum_j d_j)^2
  <= (n-2)S+nS
  = 2(n-1)S
  < 2n(n-1).                                           (5)
```

The middle inequality is Cauchy--Schwarz.  Equations (4) and (5) contradict
one another.  Hence some distinct pair satisfies (2).

## Why this is a real reduction rather than another equivalent form

The free-hub two-segment formulation has three obligations: find a hub inside
the unit lemniscate, find a pair whose ellipse contains the hub, and prove both
root spokes are contained.  The theorem discharges the first two obligations
at the fixed, explicit hub `h=mean(a_j)` in every degree.  Only the containment
obligation remains.  No critical-value selection, first-merge arc length, or
turning estimate occurs.

The remaining condition is genuinely nontrivial and, without an additional
hypothesis, false.  On the exact separated quintic from
`AdaptiveMecDichotomyLab.md` at radius `9999/10000`, direct segment maximization
finds exactly two safe centroid spokes, with maxima about `0.998814` and
`0.999651`; a bounded probe accepted 878 random separated quintics without a
failure.  Scaling the same rational directions to `99999/100000` exposes the
thin margin: `CentroidHubCounterexample.md` gives four exact rational waypoint
escapes, so at most one centroid spoke is safe.  The analytic theorem above
survives unchanged, but universal centroid visibility is retired.

## Exact downstream handoff

The falsifier condition was met by `CentroidHubCounterexample.md`: four of five
centroid spokes escape despite every pair-square exceeding the stronger `5/9`
close-pair certificate.  Retain the
centroid as a canonical interior metric basepoint, but do not use it as a fixed
visibility selector.  The separated-quintic owner should move to a hub that is
allowed to vary between the centroid and a critical point, or to a curved
component construction.  The Lean companion kernel-checks the quintic
variance and pair-budget algebra; the displayed all-degree proof is analytic.
The formal module does not encode spoke containment.

## Forum-comment assimilation (2026-08-24)

The 47-comment Erdős Problems thread supplied by the operator was read in full.
Its mathematical effect on this lane is precise.

* Pendyala's quartic theorem is already source-attributed and consumed by
  `QuarticQuotientFiberCase.md`.
* The valid logarithmic-derivative area bound discussed by Tao is already the
  `L^1` coarea currency analysed in `LemniscateCapacityBudget.md` and
  `UnconditionalConstantFactorBound.md`; by itself it does not select the
  root-joining geometry with the sharp constant.
* The gradient-flow spanning-tree proposition from the claimed unrestricted
  proof must not be revived.  `CassiniAttachmentDeficitLab.md` gives a stronger
  local conclusion than the forum diagnosis: for `z^2-(9/10)^2`, an exact Lean
  certificate disproves the printed tree budget itself by a fixed gap greater
  than `4/25`.
* Mac Lane's winding lemniscates reinforce the claim boundary here.  Knowing
  that the centroid lies in a multi-root sublevel component cannot be converted
  into a short path by connectedness alone.
* The suggested root--critical-point matching problem is geometrically
  interesting, but without sublevel containment it does not yet feed the sharp
  path theorem.

Thus the comments support the current algebraic-hub strategy and its explicit
visibility residual; they do not supply or validate an unrestricted proof.
