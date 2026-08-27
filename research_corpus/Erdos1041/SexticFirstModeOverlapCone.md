# A quantitative overlap between the sextic first- and second-mode charts

Status: complete homogeneous tangent-model theorem with exact replay and
focused Lean formalization, 2026-08-25.  It enlarges the adjacent first-mode
chart into the nominally second-mode-dominant region.  The deeper mixed core
and nonlinear transfer remain open.

## The theorem

Use the paired tangent-ray model

\[
R_j(t)=(t-t^5)A_j+(t^2-t^4)B_j-t^6,qquad 0\le t\le1.
\]

Let \(A=|E_1|\), \(B=|E_2|\), normalize \(B\le1\), and choose the two
adjacent directions with \(A_j\le-A/2\).  If

\[
4B\le5A,                                                     \tag{O}
\]

then both complete rays are nonpositive.  A sufficiently small joining chord
is strictly negative under the same explicit scale conditions used in the
first-mode theorem.  Thus the closed chart is not merely \(B\le A\), but

\[
B\le {5A\over4}.                                            \tag{1}
\]

The residual mixed annulus consequently satisfies \(A/B<4/5\).

## Ray proof

The worst first-mode projection is \(-A/2\), and the worst second-mode
projection is \(B\).  Under (O), the ray is bounded by

\[
B\left[-{2\over5}(t-t^5)+(t^2-t^4)\right]-t^6.
\]

If the bracket is nonpositive there is nothing to prove.  If it is positive,
use \(B\le1\).  The resulting normalized upper bound factors as

\[
-{t\over5}
\left(5t^5-2t^4+5t^3-5t+2\right).                          \tag{2}
\]

The parenthesized polynomial is positive on \([0,1]\).  For \(t\le2/5\),

\[
P=t^3(5t^2-2t+5)+(2-5t)\ge0.
\]

For \(t\ge2/5\),

\[
P=t^4(5t-2)+(5t^3-5t+2).
\]

The remaining cubic is globally positive on the nonnegative ray.  With
\(s=\sqrt3\),

\[
s^3(5t^3-5t+2)
=5(st-1)^2(st+2)+6s-10>0,                                  \tag{3}
\]

using \(s>5/3\).  Equations (2)--(3) prove the ray claim.

The exact optimal ratio obtainable from this worst-projection argument is
about \(0.7368097409\), the maximum of

\[
{2t(1-t^2-t^4)\over1-t^4}.
\]

The rational \(4/5\) is deliberately weaker and proof-robust.

## Chord proof

On the selected adjacent chord the linear term is at most \(-Au/2\).  Under
\(B\le5A/4\), \(u\le1/16\), the quadratic and quartic terms are each at most
\(5Au/64\), and the paired quintic term is at most \(Au/16\).  If

\[
8|E_3|u^2\le A,qquad 8u^5\le A,
\]

the cubic and baseline terms are each at most \(Au/8\).  The total positive
budget is \(15Au/32<Au/2\), so the chord has strict margin \(Au/32\).

## Handoff

Together with the all-phase pure second-mode theorem, the unresolved
homogeneous tangent set is now a compact mixed annulus with

\[
|E_1|/|E_2|<4/5
\]

but bounded away from zero outside a collar of the pure phase circle.  The
next atlas only needs to bridge that annulus to the already-proved null-box
cells; it no longer needs either pure boundary or the near-equal mode region.

