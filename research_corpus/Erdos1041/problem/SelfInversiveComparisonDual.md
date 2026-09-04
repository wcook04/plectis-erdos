# Erdős 1041: the exact self-inversive comparison dual

## Claim boundary

This note assimilates the returned self-inversive handoff into the live
Erdős-1041 corpus.  It proves the finite-dimensional comparison problem and an
exact no-go theorem for comparison-only gap selection.  It does **not** prove
the unrestricted path theorem: the surviving burden is geometric and metric.

Let

\[
g(z)=\prod_{j=1}^n(z-w_j),\qquad |w_j|=1,
\]

with distinct roots in cyclic order, and put \(c=g(0)\).  Choose \(|\eta|=1\)
so that \(G(t)=\eta e^{-int/2}g(e^{it})\) is real.  In every root gap,

\[
\frac{G'}G=\frac12\sum_j\cot\frac{t-\theta_j}{2},\qquad
\left(\frac{G'}G\right)'=-\frac14\sum_j\csc^2\frac{t-\theta_j}{2}<0.
\]

Thus each gap has a unique maximum \(v_k=e^{i\tau_k}\) of \(|g|\).  Write
\(M_k=|g(v_k)|\), and set

\[
A(z)=zg'(z)-\frac n2g(z).
\]

The roots of \(A\) are precisely the \(v_k\), all simple and on the unit
circle.

## Exact gap product and positive quadrature

At a root \(w_j\), \(A(w_j)=w_jg'(w_j)\).  Evaluating the same resultant first
over the roots of \(g\), then over the roots of \(A\), gives

\[
\prod_{k=1}^n M_k
=\left(\frac2n\right)^n\prod_{i<j}|w_i-w_j|^2
=2^n\mathcal D(g),
\quad
\mathcal D(g)=n^{-n}\prod_{i<j}|w_i-w_j|^2.
\]

Define

\[
\lambda_k=\frac{g(v_k)}{v_kA'(v_k)}
=-\frac{G(\tau_k)}{G''(\tau_k)}>0,
\qquad
\omega_k=\frac n4\lambda_k.
\]

The residues of \(g(z)/(zA(z))\) at zero, the \(v_k\), and infinity give
\(\sum_k\lambda_k=4/n\), hence \(\sum_k\omega_k=1\).

Let \(\mathcal A(g)\) be the affine family of monic degree-\(n\)
self-inversive polynomials with constant term \(c\).  For every
\(q\in\mathcal A(g)\),

\[
\boxed{\sum_k\omega_k\frac{q(v_k)}{g(v_k)}=1.}
\]

Indeed, \(h=g-q\) has degree at most \(n-1\) and vanishes at zero, so
\(h=zp\) with \(\deg p\le n-2\).  Lagrange interpolation at the roots of
\(A\) gives \(\sum_k p(v_k)/A'(v_k)=0\), which is the displayed identity.
The ratios are real by self-inversiveness.  Positivity of the weights therefore
recovers the alternation conclusion: some ratio is at least one.

## Explicit affine equivalence

For every gap define

\[
Q_k(z)=\frac2n\frac{z+v_k}{z-v_k}A(z).
\]

The pole cancels.  The polynomial is monic, self-inversive, has constant term
\(c\), and satisfies

\[
\frac{Q_k(v_j)}{g(v_j)}=
\begin{cases}0,&j\ne k,\\1/\omega_k,&j=k.\end{cases}
\]

Consequently evaluation is an affine bijection

\[
\mathcal A(g)\longleftrightarrow
\left\{x\in\mathbb R^n:\sum_k\omega_kx_k=1\right\},
\qquad
q(z)=\sum_k\omega_kx_kQ_k(z).
\]

For positive node scales \(B_k\), this gives the exact minimax value

\[
\inf_{q\in\mathcal A(g)}\max_k\frac{|q(v_k)|}{B_k}
=\left(\sum_k\omega_k\frac{B_k}{M_k}\right)^{-1}.
\]

The optimizer is unique and has
\(x_k=TB_k/M_k\).  This closes the packet's comparison-polynomial producer.

## Sharp no-go for a comparison-only proof

For any nonempty proper subset \(S\) of the gaps, let
\(W=\sum_{k\in S}\omega_k\).  With sufficiently small \(\varepsilon>0\), set

\[
x_k=1+\varepsilon\ (k\in S),\qquad
x_k=1-\varepsilon\frac{W}{1-W}\ (k\notin S).
\]

Then \(\sum\omega_kx_k=1\), so the affine inverse supplies an admissible
comparison polynomial whose set of strict alternation candidates is exactly
\(S\).  Thus alternation signs alone contain no geometric tie-breaker.  Any
full proof must couple the dual ratios to spoke entry, chord safety, intrinsic
distance, or an equivalent path potential.

## Dilation identity and topological merger

For \(0<s<1\), the canonical comparator

\[
q_s(z)=\frac{g(sz)+s^ng(z/s)}{1+s^n}
\]

has \(n\) simple unit-circle roots \(\zeta_k(s)\), and resultants give

\[
\prod_k|g(s\zeta_k(s))|
=\frac{\prod_j|g(s^2w_j)|}{(1+s^n)^n}.
\]

Since

\[
\prod_j|g(rw_j)|
=\exp\!\left(-\sum_{m\ge1}\frac{r^m}{m}|p_m|^2\right)<1,
\]

some canonical node satisfies \(|g(s\zeta_k(s))|<(1+s^n)^{-1}<1\).
This is an all-degree subunit-node theorem, but it supplies only one component
attachment.

Finally, the derivative resultant implies that a non-regular unit-root
configuration has a critical point in \(|g|<1\); its component contains at
least two roots.  The regular polygon has the same conclusion by radial paths.
This proves topological co-connectivity, not the required metric bound.

## Verification and surviving interface

`SelfInversiveComparisonDual.lean` checks the weighted-average consequence and
the arbitrary-candidate-set construction.  The executable replay uses the
condition-invariant residual
\(\omega_kQ_k(v_j)/g(v_j)-\delta_{kj}\), rather than the ill-conditioned raw
value \(Q_k(v_k)/g(v_k)=1/\omega_k\).

The surviving interface is a path-coupled metric theorem.  The comparison dual
is auxiliary to that theorem and cannot replace it.
