# The anisotropic cubic transition cone

Status: complete analytic coefficient theorem with exact replay and focused
Lean formalization, 2026-08-25.  It replaces the isotropic low-mode threshold
by the natural mode-dependent exponents and makes the complementary
second-mode normalization compact.  It does not settle that compact atlas or
unrestricted Erdős #1041.

## The theorem

Write \(\Delta=s^6\), with \(0<s\le1/64\), and use the sextic Fourier model

\[
G(z)=-\Delta+\operatorname {Re}
(E_1z+E_2z^2+E_3z^3+E_4z^4+E_5z^5-z^6).
\]

Assume the actual-root pairings

\[
|E_4|\le|E_2|+2\Delta,qquad
|E_5|\le|E_1|+2\Delta,                                     \tag{P}
\]

and the anisotropic low-mode bounds

\[
|E_1|\le {3s^5\over2048},qquad
|E_2|\le {3s^4\over2048}.                                  \tag{A}
\]

Choose the cubic parity whose projection is nonpositive.  On all three
selected sixth-root rays,

\[
G(t\omega^j)\le-\Delta/2qquad(0\le t\le1).                \tag{R}
\]

At inner radius \(u=s^2/4\), the complete nuisance budget is below
\(\Delta/32\), while the unit-bounded cubic and sextic terms are each at most
\(\Delta/64\).  Hence the whole inner disk has the same half-deficit margin,
and any two selected same-parity rays give a strict short staple.

## Why the exponents are natural

A mode \(a_mt^m\) competes with \(t^6+\Delta\).  Optimizing in \(t\) forces

\[
a_m=O(\Delta^{(6-m)/6}).
\]

Thus the correct thresholds are \(\Delta^{5/6}=s^5\) for \(E_1\) and
\(\Delta^{2/3}=s^4\) for \(E_2\).  The earlier lumped
\(|E_1|+|E_2|=O(\Delta^{5/6})\) cone discarded the larger natural
second-mode region.

## Ray proof

For \(0\le t\le1\), pairing gives the nuisance upper bound

\[
2|E_1|t+2|E_2|t^2+2\Delta(t^4+t^5).                        \tag{1}
\]

Apply the exact Young factorizations at the scaled variables
\(r=s/4\), \(x=t/2\):

\[
6r^5x\le x^6+5r^6,qquad
3r^4x^2\le x^6+2r^6.                                      \tag{2}
\]

The second follows from

\[
x^6-3r^4x^2+2r^6=(x^2-r^2)^2(x^2+2r^2).
\]

Using (A), the first two terms of (1) are bounded respectively by

\[
{t^6\over64}+{5\Delta\over4096},qquad
{t^6\over64}+{2\Delta\over4096}.                           \tag{3}
\]

For the paired radial error,

\[
2\Delta(t^4+t^5)\le4\Delta t^4
\le {\Delta\over4}+{t^6\over64}.                           \tag{4}
\]

To prove the last inequality, split at \(t=1/2\).  Below it,
\(4t^4\le1/4\); above it, \(t^2\ge1/4\) and
\(\Delta=s^6\le64^{-6}<1/1024\), so
\(4\Delta t^4\le t^6/64\).  Adding (3)--(4) to
\(-\Delta-t^6\) leaves much more than the asserted half-deficit margin.

## Inner disk

At \(u=s^2/4\), (P)--(A) give

\[
\begin{aligned}
2|E_1|u&\le3\Delta/4096,\\
2|E_2|u^2&\le3\Delta/16384,\\
2\Delta(u^4+u^5)&\le\Delta/64.
\end{aligned}
\]

Their sum is below \(\Delta/32\).  Also
\(u^3=\Delta/64\) and \(u^6\le u^3\), proving the inner margin.

## Compactness consequence

The complementary second-mode branch now has

\[
|E_2|>{3\over2048}\Delta^{2/3}.                            \tag{5}
\]

Normalize by \(\rho=|E_2|^{1/4}\).  Parseval/radial energy gives
\(|E_3|\le\sqrt{12\Delta}\).  From (5),

\[
{|E_3|\over\rho^3}
\le\sqrt{12}\left({2048\over3}\right)^{3/4},               \tag{6}
\]

an absolute constant.  This is the missing compactness statement: the cubic
coordinate can no longer diverge in the normalized second-mode atlas.

The next owner should combine (6), the \(4/5\) first-mode overlap, the pure
second-mode phase circle, and the canonical null-box cells into one finite
compact atlas, then spend strict margins on the origin-anchored remainder.
