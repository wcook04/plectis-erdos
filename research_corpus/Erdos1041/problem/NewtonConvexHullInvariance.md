# Erdős #1041: Newton descent stays in the root convex hull

## Claim boundary

Let

\[
  f(z)=a\prod_{j=1}^n (z-z_j),\qquad
  K=\operatorname{conv}\{z_1,\ldots,z_n\}.
\]

Every nonsingular forward trajectory of the Newton descent field

\[
  N(z)=-\frac{f(z)}{f'(z)}
      =-\left(\sum_j\frac1{z-z_j}\right)^{-1}
\]

that starts in `K` stays in `K` until it reaches a root.  Consequently, each
canonical descending inverse-ray branch from a non-root critical point stays
in `K` as well.  In particular, if all roots lie in a disk, no such branch can
escape that disk spatially.

This is a confinement theorem, not a solution of Erdős #1041.  It rules out
spatial escape, but a curve can have arbitrarily large arclength inside a
bounded convex set.  The remaining theorem must control turning, projection
multiplicity, or the Reeb-tree allocation of length.

## Supporting-half-plane calculation

Fix a supporting line of `K`, rotate coordinates so its outward unit normal
is the positive real direction, and let `z` be a point of the supporting
face.  Write the rotated displacements as

\[
  w_j=\overline\nu\,(z-z_j).
\]

The supporting property gives `Re(w_j) >= 0`.  Since

\[
  \operatorname{Re}\frac1w
  =\frac{\operatorname{Re}w}{|w|^2}\geq 0,
\]

we have

\[
  \operatorname{Re}S\geq 0,
  \qquad S=\sum_j\frac1{w_j}.
\]

Rotation commutes with the Newton formula, and hence the outward component
of the rotated Newton vector is

\[
  \operatorname{Re}\left(-\frac1S\right)
  =-\frac{\operatorname{Re}S}{|S|^2}\leq 0.
\]

The totalized-inverse version of exactly this calculation is Lean-checked in
`NewtonFlowRaySeparation.lean` as
`newtonReciprocalVector_supportingHalfPlane`.

There is an equivalent nonsingular field

\[
  V(z)=-\overline{\sum_j\frac1{z-z_j}}.
\]

Away from roots and critical points,

\[
  N(z)=\frac{V(z)}{|\sum_j1/(z-z_j)|^2},
\]

so `N` and `V` have the same oriented trajectories.  The field `V` makes the
support calculation especially transparent and is locally Lipschitz away
from the roots.

## Convex invariance

A closed convex set is the intersection of its supporting half-planes.  At
each boundary point of `K`, the calculation above puts the Newton vector in
the tangent cone of every active supporting half-plane.  The standard
closed-convex viability theorem (equivalently, the first-exit argument using
the metric projection to `K`) therefore makes `K` forward invariant for the
flow, up to the terminal singularity at a root.

For a descending branch issuing from a critical point `c`, there are two
cases.

1. If `c` is in the relative interior of `K`, every sufficiently short
   positive-time segment of the branch begins in `K`, and forward invariance
   applies.
2. If a non-root critical point lies on a supporting face, then
   `sum_j 1/(c-z_j)=0`.  Every summand has nonnegative outward real part, so
   every summand has zero outward real part.  Thus all roots lie on the same
   supporting line.  After an affine rotation the polynomial has real roots,
   its critical value is real, and its canonical inverse-ray branches remain
   on that line.  Multiple-root endpoints are already roots.

This also covers the lower-dimensional case in which `K` is a segment.

## Consequence for the live #1041 route

The March local-hole mechanism failed because a critical-to-root branch can
leave a proposed local hole.  The present theorem replaces that false local
claim with a true global one: the branch cannot leave the convex hull of all
roots.  If the roots lie in the open unit disk, every such branch lies in
their compact convex hull, hence in the open unit disk.

What it does **not** provide is the required total length bound.  The next
precise producer should exploit the constant-argument identity

\[
  f(z(t))=e^{-t}f(z(0))
\]

together with convex confinement to bound either:

- the number of intersections with almost every line (then use coarea), or
- the total variation of the tangent angle on each Reeb-tree edge, or
- the overlap multiplicity of orthogonal projections of all selected edges.

Computation is useful only as a falsifier for one of those explicit uniform
bounds; another unconstrained trajectory scan is not the next step.
