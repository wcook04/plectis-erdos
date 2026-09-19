# The cubic-to-transverse transition cone

Status: complete analytic theorem with exact replay and focused Lean
formalization, 2026-08-25.  This strengthens the paired low-mode cone to the
natural transition scale and leaves a quantitatively compact transverse
branch.  It does not yet prove that branch or unrestricted Erdős #1041.

## The theorem

Use the sextic Fourier model

\[
G(z)=-\Delta+\operatorname {Re}
(E_1z+E_2z^2+E_3z^3+E_4z^4+E_5z^5-z^6)
\]

with \(|E_3|\le1\) and the actual-root pairings

\[
|E_4|\le|E_2|+2\Delta,qquad
|E_5|\le|E_1|+2\Delta.                                      \tag{P}
\]

Write \(\Delta=s^6\), where \(0<s\le1/64\).  If

\[
L:=|E_1|+|E_2|\le {s^5\over16}={\Delta^{5/6}\over16},        \tag{C}
\]

then one parity class of sixth-root directions supplies three rays on which

\[
G(t\omega^j)\le-\Delta/2\qquad(0\le t\le1).                 \tag{R}
\]

The whole disk \(|z|\le s^2/4=\Delta^{1/3}/4\) also satisfies
\(G(z)\le-\Delta/2\).  Joining two selected rays through this disk gives a
strict safe staple of length

\[
2-(2-\sqrt3)s^2/4<2.
\]

Hence the only complementary cubic transition region is

\[
|E_1|+|E_2|>{\Delta^{5/6}\over16}.                           \tag{T}
\]

This strictly improves the previous threshold \(L\le\Delta\): their ratio is
\(\Delta^{-1/6}/16\), which tends to infinity in the near-Fekete limit.

## Proof

From (P),

\[
S:=|E_1|+|E_2|+|E_4|+|E_5|\le2L+4\Delta.
\]

Since \(s\le1/64\), (C) yields

\[
S\le{s^5\over8}+4s^6\le{3s^5\over16}
  =6\left({s\over2}\right)^5.                               \tag{1}
\]

Choose the cubic parity so that its projection is nonpositive.  On a selected
ray the nuisance contribution is at most \(St\).  Applying the exact Young
factorization from the paired cone at scale \(s/2\) gives

\[
6(s/2)^5t\le t^6+5(s/2)^6.
\]

Therefore

\[
G(t\omega^j)
 \le-s^6+5(s/2)^6
 =-{59\over64}\Delta
 \le-\Delta/2,
\]

proving (R).

For \(u=s^2/4\), the three remaining upper bounds are

\[
Su\le {3s^7\over64}\le {3\Delta\over64},\qquad
u^3={\Delta\over64},\qquad
u^6\le u^3.
\]

Their sum is far below \(\Delta/2\), proving the inner-disk assertion.

## Why this is the correct transition exponent

Ignoring constants, the dangerous ray envelope is

\[
-\Delta+Lt-t^6.
\]

Its positive maximum has size \(L^{6/5}\).  It can be absorbed by the radial
deficit exactly when \(L=O(\Delta^{5/6})\).  Thus exponent \(5/6\) is forced
by balancing the low linear nuisance against the sextic baseline; it is not
an artifact of the proof constants.

## Exact handoff

Normalize branch (T) by a low-mode balance radius.  Because
\(L/\Delta^{5/6}>1/16\), the normalized radial deficit is uniformly bounded
and cannot converge back to the pure cubic face.  The remaining coefficient
section is therefore compact after phase gauge and pairing.  The next task is
to cover that compact section by the existing canonical mixed/null-box
connectors plus finitely many new cells, and then spend their strict margins
on the origin-anchored \(O(\eta^2|z|)\) remainder.
