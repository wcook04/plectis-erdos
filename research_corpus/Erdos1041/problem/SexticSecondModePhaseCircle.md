# The all-phase pure second-mode sextic circle

Status: complete analytic homogeneous theorem with exact symbolic replay and
focused Lean formalization, 2026-08-25.  This closes every coefficient phase
of \(\operatorname {Re}(Bz^2-z^6)\).  Mixed first/cubic modes and the finite
nonlinear transfer remain open; unrestricted Erdős #1041 is not claimed.

## The theorem

Let \(|B|=1\), \(\omega=e^{i\pi/3}\), and

\[
H_B(z)=\operatorname {Re}(Bz^2-z^6).
\]

Put

\[
q={7+4\sqrt3\over27},\qquad r=q^{1/4}.
\]

For every phase of \(B\), there are adjacent sixth-root directions
\(\omega^j,\omega^{j+1}\) such that the two radial tails from radius \(r\)
to those roots and their joining chord all lie in \(\{H_B\le0\}\).  The path
has length

\[
2(1-r)+r=2-r<2.
\]

Equality on the chord occurs only in the rotated canonical double-contact
configurations.  Thus the canonical mixed-slice certificate is the worst
boundary of the entire phase circle, not an isolated lucky phase.

## Phase reduction

Write \(B=e^{i\phi}\).  Rotating an adjacent root pair by \(\omega^j\)
replaces \(\phi\) by \(\phi+2j\pi/3\).  Three such rotations reduce every
phase to

\[
{\pi\over3}\le\theta\le\pi.                                \tag{1}
\]

Use the base chord from \(1\) to \(\omega\).  Both endpoint second-mode
projections are at most \(1/2\):

\[
\cos\theta\le {1\over2},\qquad
\cos(\theta+2\pi/3)\le {1\over2}.
\]

Since \(r^4=q>1/2\), on either outward ray \(x\ge r\),

\[
x^2p-x^6=x^2(p-x^4)\le0.                                   \tag{2}
\]

## Two boundary phases control the chord

Parameterize the chord as

\[
w(t)=(1-t)+t\omega=\rho(t)e^{i\alpha(t)},qquad 0\le t\le1.
\]

Here \(0\le\alpha\le\pi/3\), and \(\alpha\le\pi/6\) precisely on the
first half.  In polar coordinates,

\[
H_{e^{i\theta}}(rw)
=r^2\rho^2\cos(\theta+2\alpha)-r^6\rho^6\cos(6\alpha).       \tag{3}
\]

For fixed \(\alpha\), only the first cosine depends on \(\theta\).  The
cosine-difference identity proves

\[
\begin{array}{ll}
\cos(\theta+2\alpha)\le\cos(\pi/3+2\alpha),
  &0\le\alpha\le\pi/6,\\[2mm]
\cos(\theta+2\alpha)\le\cos(\pi+2\alpha),
  &\pi/6\le\alpha\le\pi/3.
\end{array}                                                  \tag{4}
\]

Thus the first half is bounded by phase \(\pi/3\), and the second by phase
\(\pi\).

The \(\theta=\pi\) boundary is exactly the canonical chord
\(\operatorname {Re}(-z^2-z^6)\).  For \(\theta=\pi/3\), rotate by
\(\omega^{-1}\) and reverse the chord parameter; it becomes the same
canonical chord.  In both cases the existing exact factorization says

\[
H(rw(t))=-r^2q(t+1+\sqrt3)(t+1-\sqrt3)^2C(t)\le0,
\]

where every Bernstein coefficient of \(C\) is positive.  Combining this
with (4) proves the theorem.

## Computational discovery and exact proof boundary

A phase/radius minimax sweep over 1,920 connectors found its worst score at
phase \(\phi=\pi/3\), pair \((1,2)\), radius approximately
\(0.8504\).  The small positive sampled score came from the coarse radius
grid.  Inserting the exact algebraic radius \(r=0.8474865856\ldots\) made the
worst score numerical zero, at the canonical phase.  Symbolic replay verifies
both boundary-coordinate identities exactly.  The analytic factorization and
Lean kernel, not the float sweep, are proof authority.

## Downstream handoff

The pure \(E_2\) phase circle is no longer part of the residual.  In the
second-mode-dominant tangent region \(|E_1|<|E_2|\), one must now prove a
uniform neighborhood of this phase circle while allowing the normalized
first and cubic modes.  The canonical null-box atlas already handles the only
known double-contact degeneration; the next task is to overlap its cells with
strict phase-circle arcs and then perform the origin-anchored remainder
transfer.
