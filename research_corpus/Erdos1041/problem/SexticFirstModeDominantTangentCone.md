# The first-mode-dominant sextic tangent cone

Status: complete homogeneous tangent-model theorem with exact scalar replay
and focused Lean formalization, 2026-08-25.  It closes the full all-phase
first-mode-dominant tangent chart.  The finite nonlinear transfer and the
second-mode-dominant chart remain open, as does unrestricted Erdős #1041.

## Exact radial/tangent decomposition

Write the perturbed sixth roots as

\[
a_k=\omega^k(1+e_k),\qquad e_k=x_k+i y_k,qquad |1+e_k|\le1.
\]

Then \(x_k\le0\).  With

\[
E_m=\sum_{k=0}^5e_k\omega^{-km},
\]

the finite Fourier perturbation is

\[
\sum_{m=0}^5E_mz^m
=\sum_{k=0}^5 e_k K(z\omega^{-k}),qquad
K(u)=1+u+\cdots+u^5.                                      \tag{1}
\]

On a sixth-root ray \(z=t\omega^j\), put
\(q=\omega^{j-k}\), \(c=\operatorname {Re}q\).  Since \(q^6=1\),

\[
\operatorname {Re}K(tq)
=\frac{(1-t^6)(1-tc)}{1-2tc+t^2}>0
\qquad(0\le t<1).                                          \tag{2}
\]

Thus every inward radial displacement \(x_k\) contributes nonpositively on
every root ray.  The approximate-pairing error should not be paid as an
adversarial \(2\Delta\) norm budget there; its sign is favourable.

For the pure tangent part \(x_k=0\), the Fourier pairs are exact:

\[
E_5=-\overline {E_1},\qquad E_4=-\overline {E_2},
\qquad E_3\in i\mathbb R.                                  \tag{3}
\]

The cubic term vanishes on all sixth-root rays.  If

\[
A_j=\operatorname {Re}(E_1\omega^j),\qquad
B_j=\operatorname {Re}(E_2\omega^{2j}),
\]

then the complete ray value is exactly

\[
H(t\omega^j)
=(t-t^5)A_j+(t^2-t^4)B_j-t^6.                              \tag{4}
\]

## The first-mode-dominant theorem

Assume \(E_1\ne0\) and \(|E_2|\le|E_1|=:A\).  There are two adjacent
sixth-root directions \(j,j+1\) for which

\[
A_j,A_{j+1}\le-A/2.                                        \tag{5}
\]

Indeed, after writing \(E_1=Ae^{i\phi}\), six translates of the phase sector
\([2\pi/3,\pi]\) tile a full period; both that sector and its translate by
\(\pi/3\) have cosine at most \(-1/2\).

For either selected direction, \(B_j\le|E_2|\le A\).  Hence (4) is at most

\[
\begin{aligned}
&-{A\over2}(t-t^5)+A(t^2-t^4)-t^6\\
&\quad=-{A\over2}t(1-t^2)(t-1)^2-t^6\le0.                  \tag{6}
\end{aligned}

So both entire radial arms are safe, for every coefficient phase and every
relative second-mode phase.

## The small joining chord

Let \(C=|E_3|\).  On the chord joining \(u\omega^j\) to
\(u\omega^{j+1}\), linearity and (5) bound the first mode by \(-Au/2\).
All other terms are bounded in norm by

\[
Au^2+Cu^3+Au^4+Au^5+u^6.                                  \tag{7}
\]

Choose \(u>0\) so that

\[
u\le1/16,qquad 8Cu^2\le A,qquad 8u^5\le A.               \tag{8}
\]

Such a positive \(u\) always exists.  The three \(A\)-terms in (7) total at
most \(3Au/16\); the cubic and baseline terms are each at most \(Au/8\).
Consequently the whole chord is at most \(-Au/16<0\).  Since the selected
directions are adjacent, the staple length is \(2-u<2\).

## What computation did and did not do

The stronger conjecture that two directions simultaneously satisfy
\(A_j\le0\) and \(A_j+B_j/2\le0\) was falsified on the first deterministic
random sample: only direction 2 survived.  Formula (6) is the repair.  It
uses the sextic baseline throughout the ray instead of demanding that the
tangent part be nonpositive by itself.  Exact rational replay checks (2),
(6), and the chord constants; computation is not proof authority.

## Downstream handoff

Combine this theorem with the transition cone.  Outside the cubic cone, if
\(|E_2|\le|E_1|\), the homogeneous tangent selector is now explicit and has a
positive-radius chord.  The remaining tangent face is

\[
|E_1|<|E_2|.                                                \tag{9}
\]

Its pure \(E_2\) boundary is already covered by the canonical mixed-slice
machinery, but uniform all-phase perturbations must still be proved.  After
that finite homogeneous closure, the strict model margins must absorb the
origin-anchored \(O(\eta^2|z|)\) remainder.  This note does not claim that
transfer has already been completed.
