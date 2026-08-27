# The paired radial-deficit cone at the sextic cubic face

Status: complete analytic coefficient theorem with exact replay and a focused
Lean kernel, 2026-08-25.  This closes the low-mode branch of the sextic cubic
normalization problem.  It is not yet the full near-Fekete transfer or the
unrestricted Erdős #1041 theorem.

## The theorem

Consider the sextic Fourier model

\[
 G(z)=-\Delta+\operatorname {Re}
 \bigl(E_1z+E_2z^2+E_3z^3+E_4z^4+E_5z^5-z^6\bigr).
\]

Suppose \(0<\Delta\le1\), \(|E_3|\le1\), and the approximate tangent
pairing inequalities

\[
 |E_4|\le |E_2|+2\Delta,\qquad
 |E_5|\le |E_1|+2\Delta                                      \tag{P}
\]

hold.  If

\[
 |E_1|+|E_2|\le\Delta,                                      \tag{L}
\]

write \(\Delta=s^5\).  Whenever \(s\le1/10\), one parity class of the six
sixth-root directions consists of three rays on which

\[
 G(t\omega^j)\le-\Delta/2\qquad(0\le t\le1).                \tag{R}
\]

Moreover the whole disk \(|z|\le\Delta/16\) satisfies

\[
 G(z)\le-\Delta/2.                                           \tag{D}
\]

Any two of the three selected rays, truncated at
\(u=\Delta/16\) and joined through that disk, therefore form a strict safe
staple of length

\[
 2(1-u)+\sqrt3,u=2-(2-\sqrt3)u<2.
\]

Consequently every coefficient tuple satisfying (P) lies in exactly one of
two explicit branches:

\[
 |E_1|+|E_2|\le\Delta \quad\text{(the closed paired cone)},
 \qquad
 |E_1|+|E_2|>\Delta \quad\text{(the transverse branch)}.     \tag{N}
\]

This is a normalization dichotomy, not a renaming of the earlier four-mode
hypothesis: (P) is forced by the geometry of perturbed roots in the unit disk,
and (L) involves only the two genuinely low Fourier modes.

## Proof

Put \(e_m=|E_m|\).  Pairing and low-mode dominance give

\[
 e_1+e_2+e_4+e_5
 \le 2(e_1+e_2)+4\Delta
 \le6\Delta.                                                  \tag{1}
\]

For \(0\le t\le1\), every nuisance power is at most \(t\), so their total
contribution is at most \(6\Delta t\).  Choose the parity
\(\varepsilon\in\{1,-1\}\) for which
\(\varepsilon\operatorname {Re}E_3\le0\).  On each of the three rays with
\(\omega^{3j}=\varepsilon\), the cubic contribution is nonpositive.

The exact identity

\[
\begin{aligned}
 t^6-6s^5t+5s^6
   &=(t-s)^2\bigl(t^4+2st^3+3s^2t^2+4s^3t+5s^4\bigr)\\
   &\ge0
\end{aligned}                                                 \tag{2}
\]

is weighted Young's inequality with its equality scale exposed.  Since
\(\Delta=s^5\), (2) yields

\[
 -\Delta+6\Delta t-t^6
 \le-\Delta+5s\Delta
 \le-\Delta/2,
\]

which proves (R).

For \(|z|\le u=\Delta/16\), the nuisance modes contribute at most
\(6\Delta u\le3\Delta/8\).  The cubic and sextic terms are bounded above by
\(u^3\) and \(u^6\).  Because \(u\le1/16\),

\[
 u^3\le\Delta/4096,\qquad u^6\le u^3.
\]

Thus their combined upper bound is strictly below \(\Delta/8\), proving (D).
The staple-length calculation is the already verified same-parity
sixth-root geometry.

## Why pairing is geometric

For actual perturbed roots \(a_k=\omega^k(1+e_k)\) in the unit disk, write
\(e_k=x_k+iy_k\) and \(\Delta=-\operatorname {Re}E_0\).  The disk condition
gives \(x_k\le0\) and \(\sum|x_k|=\Delta\).  Separating the Fourier transforms
of \((x_k)\) and \((y_k)\) gives

\[
 |E_{6-m}+\overline{E_m}|\le2\Delta.
\]

The reverse triangle inequality then gives (P) for \(m=1,2\).  No genericity
or division by a first nonzero coefficient is used.

## Competing attacks and the selected one

Three structurally different continuations were compared.

1. A finite angular atlas on the full four-nuisance coefficient box.  The
   earlier cubic-face checker falsified its simplest positive-radius version.
2. An exact alternating factorization for cyclic trinomials.  This is strong
   on a thin algebraic face but does not control an open perturbation cone.
3. Pairing plus a degree-six Young envelope.  This uses an actual-root
   invariant, survives every coefficient phase, and leaves one explicit
   transverse inequality.  It is the route proved here.

The cheapest falsifier for route 3 was the equality scale \(t=s\): if the
Young envelope failed there, no uniform ray margin could survive.  Identity
(2) shows it is exact there and nonnegative everywhere.

## Exact downstream handoff

The remaining near-Fekete sextic obligation is now sharply localized to

\[
 |E_1|+|E_2|>\Delta.                                         \tag{T}
\]

The next owner should normalize this transverse branch by
\(\rho=\max(|E_1|^{1/5},|E_2|^{1/4})\), compare the existing mixed sextic
atlas on the resulting compact coefficient section, and absorb the
origin-anchored \(O(\eta^2|z|)\) remainder.  The present theorem must be used
as the complementary low-mode branch; it does not itself claim the finite
transfer, all sextics, or unrestricted Erdős #1041.

