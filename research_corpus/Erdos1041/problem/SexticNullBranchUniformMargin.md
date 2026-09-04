# A uniform stability tube for the positive sextic null branch

## Result

Put

\[
 s=\sqrt3,\qquad q_0={7+4s\over27},\qquad
 \beta_*={106+25s\over1221}.
\]

For \(0<\varepsilon\leq\beta\leq\beta_*\), let \(R^4=q_0(1+
\tfrac32\beta(s-1))\), let \(\rho^4=q_0(1-\tfrac32\beta(s-1))\), and set

\[
 L={R\over\rho},\qquad M={\rho\over R}.
\]

The mirror companion constructed in `SexticNullBranchCompanion` has, after
division by the positive normalization used there, the uniform bound

\[
 C_\beta(t)\leq-{\varepsilon^2\over10}\qquad(0\leq t\leq1).
\]

Its two outward rays satisfy the same bound (in fact the selected non-real ray
has the fixed stronger bound \(-1/100\)).  Consequently any perturbation of the
normalized real model whose pointwise real error on this connector is at most
\(\varepsilon^2/20\) leaves the entire connector strictly inside the
lemniscate inequality.  In particular an \(\ell^1\) coefficient error below
\(\varepsilon^2/20\) suffices whenever the normalized connector lies in the
closed unit disk.

This is a genuine finite-perturbation stability theorem for every compact
subbranch \(\varepsilon\leq\beta\leq\beta_*\).  It does **not** include the
singular endpoint \(\beta=0\), and therefore does not by itself settle the
whole near-Fekete regime or Erdős #1041.

## Proof

The companion chord is

\[
 C_\beta(t)=p(t)(1-q(-\beta)\ell(t)r(t))
 -3s\beta L(2-s)t+3s\beta M t(1-t),
\]

whereas its mirror comparison polynomial is the same expression with
\(L=M=1\).  Hence

\[
 C_\beta(t)-F_{-\beta}(t)
 =-3s\beta t\big((L-1)(2-s)+(1-M)(1-t)\big).                 \tag{1}
\]

We split at \(t=1/2\).

### The first half of the chord

At \(\beta=0\), the exact factorization is

\[
 F_0(t)=-2q_0(t+1+s)(t-s+1)^2P_3(t),
\]

where the four Bernstein coefficients of \(P_3\) are all at least \(1/10\).
For \(0\leq t\leq1/2\),

\[
 q_0>{1\over2},\quad t+1+s>2,
 \quad(t-s+1)^2\geq {1\over20},\quad P_3(t)\geq {1\over10}.
\]

The square bound follows from

\[
 (s-\tfrac32)^2={21\over4}-3s>{1\over20},
 \qquad s<{26\over15}.
\]

Thus \(F_0(t)\leq-1/100\).

At \(\beta=\beta_*\), the mirror endpoint factors as

\[
 F_{-\beta_*}(t)
 =-A(t-s+1)^2Q_4(t),\qquad
 A={4943+2813s\over10989}\geq {4\over5}.
\]

All five Bernstein coefficients of \(Q_4\) are at least \(9/10\).  Therefore
\(F_{-\beta_*}(t)\leq-9/250<-1/100\) on the same half interval.  Since
\(F_{-\beta}\) is the convex interpolation of these two endpoint polynomials,

\[
 F_{-\beta}(t)\leq-1/100\qquad(0\leq t\leq1/2).             \tag{2}
\]

Equation (1) only decreases the value.  Finally \(\varepsilon<1/4\), so
\(\varepsilon^2/10<1/160<1/100\).

### The second half of the chord

The radii give

\[
 q(\beta)=L^4q(-\beta),\qquad
 q(\beta)-q(-\beta)=3q_0\beta(s-1).
\]

Because \(q(-\beta)\leq q_0\) and \(L\geq1\), cancellation of the positive
\(q_0\) gives

\[
 L^4-1\geq3\beta(s-1).                                     \tag{3}
\]

The actual ratio satisfies \(L<2\) (indeed its fourth power is below \(4/3\)
on this interval).  Since

\[
 L^4-1=(L-1)(L^3+L^2+L+1)\leq15(L-1),
\]

\((3)\) implies

\[
 L-1\geq {\beta(s-1)\over5}.                               \tag{4}
\]

For \(t\geq1/2\), discard the two already nonpositive terms in (1), use (4),
and obtain

\[
 \begin{aligned}
 C_\beta(t)
 &\leq-3s\beta(L-1)(2-s)t\\
 &\leq-{3\over10}s(s-1)(2-s)\beta^2\\
 &<-{\beta^2\over10}\leq-{\varepsilon^2\over10}.
 \end{aligned}
\]

The strict constant comparison is exact:

\[
 {3\over10}s(s-1)(2-s)-{1\over10}
 ={13\over5}-{3s\over2}>0,
\]

again because \(s<26/15\).

### Rays and perturbations

For the mirror selected ray, the value at its truncation point is at most

\[
 -\left(-{86\over9}+{17s\over3}\right)\beta_*
 =-\left(-{13\over27}+{8s\over27}\right)<-{1\over100}.
\]

The sixth-degree growth estimate already proved for the companion shows that
the ray can only decrease beyond that point.  The comparison \(L\geq1\)
decreases the actual companion ray further.  The other selected ray is more
negative.  Since an additive perturbation \(E\) with
\(|E|\leq\varepsilon^2/20\) satisfies

\[
 -{\varepsilon^2\over10}+|E|
 \leq-{\varepsilon^2\over20}<0,
\]

the connector survives throughout the stated coefficient tube.

## Formal and computational status

`SexticNullBranchUniformMargin.lean` checks the rational square-root bounds,
the Bernstein lower bounds, the two-region margin argument, the ray margin,
the radius-ratio implication, and the additive-error consumer.  The companion
Python checker independently verifies the exact identities and evaluates the
actual radius-ratio connector on a dense deterministic grid.

## Downstream handoff

The next obstruction is now sharply localized: analyze a shrinking
neighborhood of \(\beta=0\), where no uniform \(\varepsilon^2\) tube can be
obtained by fixing \(\varepsilon>0\).  The right next object is a stratified
blow-up that compares the first nonzero coefficient mode with the next mode,
using this theorem as the outer annulus.  No work is needed on
\(\varepsilon\leq\beta\leq\beta_*\) after that overlap is established.
