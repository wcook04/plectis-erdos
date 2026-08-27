# Erdős #1041: the primitive-quintic boundary two-tail theorem

Status: analytic theorem proved on 2026-08-24.  The finite real-moment
separator is formalized in `PrimitiveQuinticBoundaryTail.lean`.  This closes
the unit-circle (paraorthogonal) boundary of the primitive sparse quintic
tail problem.  It does **not** yet prove the corresponding strict-interior
statement.

## The theorem

Let

\[
 p(z)=z^5+a z^4+c\overline a\,z+c,
 \qquad |c|=1,
\]

and suppose all five roots `w_i` lie on the unit circle.  Then at least two
distinct roots satisfy

\[
 |c+c\overline a\,w_i|\le 1.                     \tag{1}
\]

If `a != 0`, the two inequalities in (1) are strict.  If `a=0`, every tail
has modulus exactly one, so the non-strict statement is sharp.

This is precisely the boundary family obtained from Schur reduction.  If

\[
 q(z)=z^4+\alpha z^3+\delta
\]

is Schur stable, then

\[
 p_c(z)=zq(z)+c q^\#(z)
\]

has all five roots on the unit circle for `|c|=1`, and its two nonzero lower
coefficients obey `b=c conjugate(a)`.

## The phase-sensitive proof

Write `a=r e^{i phi}` and rotate the roots by

\[
 v_i=e^{-i\phi}w_i,\qquad x_i=\operatorname{Re}v_i.
\]

The missing `z^3,z^2` coefficients and Newton's identities give

\[
 \sum_i v_i=-r,\qquad
 \sum_i v_i^2=r^2,\qquad
 \sum_i v_i^3=-r^3.                              \tag{2}
\]

Because `|v_i|=1`, taking real parts in (2) yields the exact real moments

\[
 \sum_i x_i=-r,
 \quad
 \sum_i x_i^2=\frac{5+r^2}{2},
 \quad
 \sum_i x_i^3=-\frac{r^3+3r}{4}.                 \tag{3}
\]

Also `r^3=|sum_i v_i^3|<=5`, hence `r<2`.  For `r>0`, the tail condition is

\[
 |1+r v_i|<1
 \quad\Longleftrightarrow\quad
 x_i<-\frac r2.                                  \tag{4}
\]

Set `h=-r/2` and introduce the cubic separator

\[
 Q_r(x)=(h-x)(1-x)^2.
\]

On `[-1,1]`, this is positive exactly when `x<h`.  Substitution of (3)
gives the unexpectedly rigid identity

\[
 \sum_{i=1}^5 Q_r(x_i)=5-2r.                     \tag{5}
\]

On the safe arc `[-1,h]`, the separator is decreasing and therefore

\[
 Q_r(x)\le Q_r(-1)=4-2r.                         \tag{6}
\]

Outside the safe arc it is nonpositive.  If at most one root were safe,
(6) would make the left side of (5) at most `4-2r`, contradicting (5) by
exactly one.  Thus two distinct roots satisfy (4), proving the strict part
when `r>0`.  The case `r=0` is the stated equality case.

## Why this is new information

The preceding symmetric-energy hierarchy sees only the unordered moduli of
the five tails and is known not to characterize two-tail safety.  The cubic
separator consumes the signed phase data hidden in the missing coefficients:
all three moments in (3) are used, and their contribution collapses to the
constant one-unit gap between (5) and (6).

The exact audit includes the nontrivial boundary polynomial

\[
 z^5+\tfrac12 z^4+\tfrac12 z+1
   = z(z^4+\tfrac12)+(1+\tfrac12 z^4),
\]

whose quartic Schur core is `z^4+1/2`.  It numerically replays the unit-circle
roots, the Newton moments, and the two strict tails.  The computation is a
check; the proof above and the Lean kernel are authority.

## Boundary and solved interior successor

For `|c|<1`, the same Schur parametrization gives

\[
 a=\alpha+c\overline\delta,
 \qquad b=\delta+c\overline\alpha,
\]

and all roots are strictly inside the unit disk.  The initially selected
continuation route was radial tail-count monotonicity: a deterministic audit
followed 320 tracks, observed 802 outward crossings, and found no inward
crossing.  That conjectural bridge is no longer needed.  The successor
`PrimitiveQuinticInteriorTail` harmonically extends `Q_r`, proves that every
unsafe interior root contributes at most `2/31`, and closes the full strict
interior primitive-quintic theorem directly.

No unrestricted Erdős #1041 or unrestricted degree-five claim is made here.

The Refinery should place this result after the elementary-symmetric tail
hierarchy and immediately before `PrimitiveQuinticInteriorTail`, preserving
the `a=0` boundary equality case and the explicit boundary/interior
distinction.
