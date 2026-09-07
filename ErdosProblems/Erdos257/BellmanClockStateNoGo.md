# The Bellman state retains the Mersenne clock

Write
\[
 w_n=\frac1{2^n-1},\qquad
 \mathcal A_n=\left\{\sum_{k\geq n}\varepsilon_kw_k:
                  \varepsilon_k\in\{0,1\}\right\}.
\]
The supply-or-expand alternative has an exact Bellman formulation after
arbitrary positive global recuts are allowed.  The unresolved scalar value
\(x\) and the current rank \(n\) form a sufficient state.  Reverse
superincreasingness makes the action deterministic.

The rank cannot be removed by normalizing \(x\) by \(w_n\).  We give two
states with the same normalized value, one representable and one lying in an
exact achievement gap.  Thus the dynamic program is scalar but
nonstationary, or equivalently stationary in two variables after the
Mersenne clock is retained.

## 1. The exact Bellman equation

Let
\[
 V_n(x)=\mathbf 1_{\mathcal A_n}(x).
\]
The weights satisfy
\[
 w_n>\sum_{k>n}w_k.                                \tag{1}
\]
Indeed,
\[
 \sum_{k>n}w_k
 \leq\frac{2^{-n}}{1-2^{-(n+1)}}
 <\frac{2^{-n}}{1-2^{-n}}=w_n.
\]
Consequently a representation of \(x\) must omit \(w_n\) when \(x<w_n\),
and must contain \(w_n\) when \(x\geq w_n\).  Hence
\[
 \boxed{
 V_n(x)=
 \begin{cases}
 V_{n+1}(x),&0\leq x<w_n,\\
 V_{n+1}(x-w_n),&x\geq w_n.
 \end{cases}}                                      \tag{2}
\]
The second line is also valid when \(x\) is too large to belong to
\(\mathcal A_n\): both sides then vanish.

In cylinder language, the first branch keeps the unresolved value as a
positive residual and moves the atom boundary to the right.  The second
branch exposes \(w_n\) and recodes the remaining value \(x-w_n\).  Equation
(2) is lossless only because a global recut is allowed to replace the whole
residual cylinder representation.  A fixed descendant genealogy does not
have this Bellman property, as shown by the finite cut obstruction.

The required recut exists algebraically for every state arising from the
root.  If \(x=p/q>0\) with \(q\) odd, choose \(H\) such that
\(q\mid 2^H-1\).  Then
\[
 x=B M(2,H),\qquad
 B=\frac{3p(2^H-1)}q\in\mathbb N.
\]
The same statement applies to \(x-w_n\) whenever the second branch of (2)
is taken.  Thus cylinder coordinates do not add state after unrestricted
global recutting; their role is to realize the positive remainder exactly.

Starting with \(x_n=x\), define the forced greedy orbit
\[
 \varepsilon_n=\mathbf 1_{x_n\geq w_n},\qquad
 x_{n+1}=x_n-\varepsilon_nw_n.                     \tag{3}
\]
Then
\[
 x\in\mathcal A_n
 \quad\Longleftrightarrow\quad
 \lim_{k\to\infty}x_k=0.                           \tag{4}
\]
Indeed, any representation must have the digits in (3), by (1).  Conversely,
if \(x_k\to0\), its greedy partial sums converge to \(x\).

Thus reverse superincreasingness removes the occupied-rank set from the
state, but it does not prove that the residual tends to zero.

## 2. The autonomous two-variable state

Put
\[
 z_n=w_n,\qquad y_n=\frac{x_n}{w_n}.
\]
The identity
\[
 w_{n+1}=\frac{w_n}{2+w_n}                         \tag{5}
\]
turns (3) into the stationary system
\[
 \boxed{
 \begin{aligned}
 \varepsilon&=\mathbf 1_{y\geq1},\\
 y'&=(2+z)(y-\varepsilon),\\
 z'&=\frac{z}{2+z}.
 \end{aligned}}                                    \tag{6}
\]
The exact Markov state is therefore \((y,z)\), or equivalently \((n,x)\).
For the target \(M(2,3)=1/21\), the initial state at rank two is
\[
 (y_2,z_2)=\left(\frac17,\frac13\right).           \tag{7}
\]
A bounded orbit \((y_n)\) would imply \(x_n=z_ny_n\to0\), and infinitely
many values \(y_n\geq1\) would give infinite Boolean support.  Proving both
properties for (7) would construct the desired Boolean subsum.  Neither
property follows from (6) alone.

## 3. Normalized value is not a stationary state

Consider the common normalized value
\[
 y=\frac{10}{21}.                                  \tag{8}
\]
At rank two it gives
\[
 x=yw_2=\frac{10}{63}=w_3+w_6,                    \tag{9}
\]
so \(V_2(x)=1\).

At rank four the same normalized value gives
\[
 \widetilde x=yw_4=\frac2{63}.                    \tag{10}
\]
The forced decisions omit \(w_4\) and \(w_5\), since
\[
 \frac2{63}<\frac1{31}<\frac1{15},                \tag{11}
\]
and then take \(w_6=1/63\).  The remaining value is again \(1/63\).
But (1) at rank six gives
\[
 \sum_{k>6}w_k<w_6=\frac1{63}.                    \tag{12}
\]
No continuation can fill the remainder, so
\[
 V_4(2/63)=0.                                      \tag{13}
\]

Equations (9) and (13) prove that there is no rank-independent value
function \(V(y)\) depending only on \(x/w_n\).  The perturbation \(z=w_n\)
in (6) is essential; replacing \(2+z\) by its limiting value two changes
exact achievement gaps.

This is the Bellman form of the moving-phase obstruction.  The scalar
residual is sufficient when paired with the absolute rank, but a stationary
one-dimensional threshold cannot encode the interaction between binary
renormalization and the Mersenne denominators.

## 4. Exact receipt

The companion script checks (5)--(13) with rational arithmetic:

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/bellman_clock_state_nogo.py
