# Strictness away from the canonical second-mode phases

Status: complete analytic equality classification with dense calibration and
focused Lean formalization, 2026-08-25.  It proves that every noncanonical
phase has a strictly negative canonical-radius chord, supplying open mixed
stability collars away from the already-classified null-box phases.

## The theorem

Reduce the pure second-mode coefficient phase to

\[
\pi/3\le\theta\le\pi
\]

and use the canonical-radius adjacent chord as in
SexticSecondModePhaseCircle.md.  If

\[
\pi/3<\theta<\pi,                                          \tag{1}
\]

then every point of the joining chord has strictly negative model value.
Consequently equality in this connector family can occur only at

\[
\theta=\pi/3\quad\text{or}\quad\theta=\pi,                 \tag{2}
\]

the two rotated copies of the canonical square-contact model.

## Strict phase envelope

Write a chord point as \(\rho e^{i\alpha}\), with
\(0\le\alpha\le\pi/3\).  On the first half, set

\[
x=\theta+2\alpha,qquad y=\pi/3+2\alpha.
\]

Under (1) and \(0\le\alpha\le\pi/6\), both
\((x+y)/2\) and \((x-y)/2\) lie strictly between \(0\) and \(\pi\).
Therefore

\[
\cos x-\cos y
=-2\sin{(x+y)\over2}\sin{(x-y)\over2}<0.                 \tag{3}
\]

On the second half compare instead with \(y=\pi+2\alpha\).  Both sine
factors in (3) are now strictly negative, so their product is again positive
and the cosine difference is strictly negative.  Thus the actual phase value
is strictly below one of the two canonical boundary values at every chord
point.  Those boundary values are nonpositive by the existing Bernstein
certificate, proving strict negativity.

## Stability consequence

Fix any closed phase subarc separated from the endpoint set (2).  The chord
value is continuous on the compact product of that subarc and \([0,1]\), and
is pointwise negative by the theorem.  Hence it has a uniform negative
margin.  All sufficiently small normalized \(E_1\) and \(E_3\) perturbations
preserve the connector on that subarc.

This leaves mixed stability to be checked only in neighborhoods of the two
canonical endpoint phases.  Those are exactly the phases for which the
tetrahedral transverse selector and the complete null-box atlas were built.
Thus the phase-circle and null-box mechanisms now meet at the correct
equality set; no unidentified phase degeneracy remains.

## Computational adversary

A tangent-constrained differential-evolution scout over
\(|A|<0.8\), \(|B|=1\), and \(C\in i[-1,1]\) again drove its worst point to
the canonical boundary:

\[
|A|\approx2.38\cdot10^{-5},\quad
C\approx1.62\cdot10^{-4}i,
\]

with the exact canonical radius and negative sampled score
\(-8.06\cdot10^{-5}\).  The computation suggested the equality
classification; inequalities (3) and the Lean kernel prove it.

## Handoff

The remaining finite homogeneous work is now localized to overlap constants
between:

1. the uniform strict collars on closed noncanonical phase arcs;
2. the canonical transverse/null-box neighborhoods at (2);
3. the \(4/5\) first-mode overlap boundary; and
4. the explicit anisotropic compactness box for the normalized cubic mode.

This theorem does not itself supply all four overlap constants or the final
nonlinear remainder transfer.
