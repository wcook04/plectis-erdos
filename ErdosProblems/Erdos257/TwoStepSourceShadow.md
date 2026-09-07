# The bounded-lookahead primitive-source shadow

## Result

Put

\[
 w_d=\frac1{2^d-1},\qquad
 q_{N,d}=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor.
\]

For a coprime product target

\[
 x=M(a,b)=w_aw_b
\]

define its primitive-source coefficients by

\[
 c_d=\#\{(i,j)\in\mathbb N_{>0}^2:
          \gcd(i,j)=1,\ ai+bj=d\}.                 \tag{1}
\]

These coefficients represent the target exactly:

\[
 \boxed{x=\sum_{d\geq1}c_dw_d.}                   \tag{2}
\]

For a horizon $N$ and a fixed lookahead $H$, set

\[
 x_{N,H}=\sum_{d\leq N+H}c_dw_d,
 \qquad
 C_N=\sum_{d\leq N}c_dq_{N,d}.                   \tag{3}
\]

Let $g^{N,H}$ be the ordinary real-greedy Boolean word for $x_{N,H}$,
stopped at rank $N$, and put

\[
 G_{N,H}=\sum_{d\leq N}g_d^{N,H}q_{N,d}.          \tag{4}
\]

The new proof target is the finite-row inequality

\[
 \boxed{G_{N,H}\geq C_N.}                         \tag{S}
\]

Exact rational arithmetic verifies (S)

- for $M(2,3)=1/21$ with $H=1$ through $N=450$;
- for $M(4,5)=1/465$ with $H=2$ through $N=450$;
- for the totient source $4/9=\sum_{k\geq1}\varphi(k)w_{2k}$ with
  $H=2$ through $N=450$.

The inequality is not a generic feature of positive Lambert sources.  With
the same $H=2$ definition it first fails for the noncoprime product sources

\[
\begin{array}{c|rrrrrr}
(a,b)&(3,9)&(4,8)&(5,10)&(6,9)&(4,4)&(3,3)\\
\hline
\text{first failing }N&21&20&25&33&12&9
\end{array}
\]

and every first deficit is $-1$.  Thus (S) detects arithmetic structure
which is absent from the known ancestry-free and nonprimitive
countermodels.

This note proves that (S), if established at all depths for any of the three
positive sources above, immediately produces an infinite Boolean
representation of the corresponding rational target.  It does **not** prove
(S) at all depths.

## 1. Why the primitive source is the whole target

Every pair $(u,v)\in\mathbb N_{>0}^2$ has a unique decomposition

\[
 (u,v)=k(i,j),\qquad \gcd(i,j)=1.
\]

Consequently

\[
\begin{aligned}
 \sum_{d\geq1}c_dw_d
 &=\sum_{\gcd(i,j)=1}\sum_{k\geq1}2^{-k(ai+bj)}\\
 &=\sum_{u,v\geq1}2^{-au-bv}\\
 &=\frac1{(2^a-1)(2^b-1)}.
\end{aligned}                                      \tag{5}
\]

In particular, the primitive source for $(2,3)$ is exactly $1/21$; it is
not a lower comparison target.  The truncation in (3), rather than the full
primitive sum, is what lies below $x$.

The totient identity follows in the same way from

\[
 \sum_{k\geq1}\frac{\varphi(k)z^k}{1-z^k}
 =\frac{z}{(1-z)^2}
\]

at $z=1/4$.

## 2. Conditional consumer: the shadow inequality solves the target

Let $b=(b_d)$ be the ordinary real-greedy word for the full target $x$.
Because $x_{N,H}\leq x$, monotonicity of greedy coding for the strictly
superincreasing sequence $(w_d)$ gives

\[
 (b_1,\ldots,b_N)\ \geq_{\rm lex}\
 (g_1^{N,H},\ldots,g_N^{N,H}).                     \tag{6}
\]

The finite quotient row $(q_{N,d})_{d\leq N}$ is also strictly
superincreasing.  Therefore lexicographic order implies quotient order, and
(S) gives

\[
 B_N:=\sum_{d\leq N}b_dq_{N,d}
 \geq G_{N,H}\geq C_N.                            \tag{7}
\]

On the other hand, real-greedy feasibility gives

\[
 B_N\leq\lfloor2^Nx\rfloor.                       \tag{8}
\]

Define the actual quotient defect

\[
 Q_N=\lfloor2^Nx\rfloor-B_N.
\]

Equations (7)--(8) yield

\[
 0\leq Q_N\leq
 K_N:=\lfloor2^Nx\rfloor-C_N.                    \tag{9}
\]

For a coprime product source, the exact source clock gives

\[
 K_N=\left\lfloor\frac{N}{ab}\right\rfloor.       \tag{10}
\]

For the totient source $4/9$, direct carry evaluation gives
$K_N\leq(N+2)/3$.  Thus in every case $K_N=O(N)$.

If

\[
 r_N=x-\sum_{d\leq N}b_dw_d,
\]

then

\[
 0\leq2^Nr_N
 =Q_N+\{2^Nx\}
  -\sum_{d\leq N}b_d
      \left\{\frac{2^N}{2^d-1}\right\}
 <Q_N+1.                                           \tag{11}
\]

Hence $r_N=O(N2^{-N})\to0$.  It follows that

\[
 x=\sum_{d\geq1}b_dw_d.                           \tag{12}
\]

No compatibility between the different finite comparator words
$g^{N,H}$ is needed.  They are compared row by row with the one coherent
full-target greedy word $b$.

The shadow argument itself proves achievement membership.  Infinitude of the
support follows separately from the standard Bang--Zsigmondy argument.  If a
finite representation has largest selected rank $m>6$, a primitive prime
divisor of $2^m-1$ survives denominator clearing and cannot divide the target
denominator (whose prime orders are among $2,3$ for $1/21$, among $2,4,5$ for
$1/465$, and just $2$ for $4/9$).  The exceptional range $m\leq6$ is a
finite subset check, and no subset gives any of the three targets.

## 3. Equivalent threshold formulation

Let $z^N$ be the lexicographically least Boolean word on $[1,N]$ such that

\[
 \sum_{d\leq N}z_d^Nq_{N,d}\geq C_N.              \tag{13}
\]

Strict superincrease makes this word canonical.  The shadow statement (S)
is equivalent to

\[
 \boxed{\sum_{d\leq N}z_d^Nw_d\leq x_{N,H}.}       \tag{T}
\]

Indeed, (T) makes $z^N$ affordable for the real-greedy target $x_{N,H}$,
so greedy monotonicity gives $g^{N,H}\geq_{\rm lex}z^N$ and hence (S).
Conversely, (S) gives $g^{N,H}\geq_{\rm lex}z^N$, and real
superincrease gives the affordability in (T).

This is a finite theorem with an explicit threshold and an explicit budget:
the primitive quotient demand through $N$ must be financed by only the next
$H$ primitive-source layers.

Exact computation finds the stronger equality

\[
 \sum_{d\leq N}z_d^Nq_{N,d}=C_N                  \tag{13a}
\]

through every tested positive-source row.  Equality (13a) is not assumed in
the shadow reduction.  If it held cofinally, it would already solve the
target without (T), because

\[
 \left|x-\sum_{d\leq N}z_d^Nw_d\right|
 \leq\frac{K_N+N+1}{2^N}\longrightarrow0.
\]

For the product source,

\[
 C_{N+1}=2C_N+A_{N+1},\qquad
 A_m=\sum_{d\mid m}c_d,
\]

by $q_{N+1,d}=2q_{N,d}+\mathbf1_{d\mid N+1}$.  Thus an induction for
(13a) is exactly the endpoint-$K_N$ source-corridor recut problem already
isolated elsewhere in the corpus: the upper pure-power suffix must finance
the pulse $A_{N+1}$ across the moving midpoint.  The shadow formulation is
potentially different only because (S) can hold even when the canonical
threshold overshoots $C_N$.

## 4. Exact fractional identity and the remaining proof boundary

Write

\[
 \theta_{N,d}=\left\{\frac{2^N}{2^d-1}\right\},
 \quad
 \Phi_c=\sum_{d\leq N}c_d\theta_{N,d},
 \quad
 \Phi_g=\sum_{d\leq N}g_d^{N,H}\theta_{N,d},
\]

and let $r_{N,H}$ be the residual after running the truncated-source greedy
word through rank $N$.  Exact expansion gives

\[
 G_{N,H}-C_N
 =\Phi_c
  +2^N\sum_{N<d\leq N+H}c_dw_d
  -\Phi_g-2^Nr_{N,H}.                              \tag{14}
\]

If $k=d-(N\bmod d)$, then

\[
 \theta_{N,d}=\frac{2^{N\bmod d}}{2^d-1}<2^{1-k}. \tag{15}
\]

Thus every Boolean fractional load admits the uniform divisor bound

\[
 \Phi_g
 \leq\sum_{k=1}^N2^{1-k}\tau(N+k)
 \leq4\sqrt{2N}.                                   \tag{16}
\]

The first inequality groups a rank $d$ by its next multiple $N+k$; the
second uses $\tau(m)\leq2\sqrt m$ and $N+k\leq2N$.

In the product case

\[
 \sum_{d\mid m}c_d
 =\#\{(i,j)>0:ai+bj=m\}.                            \tag{17}
\]

For $(a,b)=(2,3)$, write the count on the right as $A_m$.  It differs from
$m/6$ by at most $1$.  Möbius inversion therefore gives

\[
 c_n=\sum_{d\mid n}\mu(d)A_{n/d}
 \geq\frac{\varphi(n)}6-\tau(n).                   \tag{18}
\]

The elementary estimates

\[
 \frac n{\varphi(n)}
 =\prod_{p\mid n}\frac p{p-1}
 \leq1+\omega(n)\leq1+\log_2n
\]

show that $c_n/\sqrt n\to\infty$.  Since the one-step lookahead term in
(14) is

\[
 2^Nc_{N+1}w_{N+1}>\frac12c_{N+1},                 \tag{19}
\]

it eventually dominates the whole Boolean fractional load (16).  The
asymptotic obstruction is therefore concentrated in the scaled truncated
greedy residual $2^Nr_{N,1}$: any bound

\[
 2^Nr_{N,1}=o(c_{N+1})                              \tag{20}
\]

would prove the $1/21$ shadow inequality for every sufficiently large $N$,
leaving only a finite exact audit.  Existing computations are much stronger
than (20), but no all-depth proof of (20) is presently available.  An
ancestry-free residual estimate cannot be used here: generic cofinite and
gap countermodels carry a positive homogeneous residual.

Equations (14)--(20) are a plausible route to (S), but the residual bound,
or an equivalent proof of the threshold affordability (T), is still
missing.

That is the exact theorem boundary.  Equality $G_{N,H}=C_N$ is false in
general even for $1/21$; the verified statement is the one-sided inequality.

## 5. The exact raw-pulse budget and the terminal-run dichotomy

The source side of (14) has a lower bound which is invisible in a generic
positive Lambert comparison.  Put

\[
 A_m=\sum_{d\mid m}c_d.
\]

If $d\mid N+1$, then

\[
 \theta_{N,d}=\frac{2^{d-1}}{2^d-1}>\frac12.
\]

The same inequality for the new rank $d=N+1$ is supplied by the lookahead
term rather than by $\Phi_c$.  Consequently the complete one-step source
budget satisfies

\[
 \boxed{
 \Phi_c+2^Nc_{N+1}w_{N+1}>\frac12A_{N+1}.}         \tag{21}
\]

With two steps of lookahead, the divisor families of $N+1$ and $N+2$ are
disjoint except at $d=1$, where all the sources considered here have
$c_1=0$.  The second family contributes more than one quarter per source
unit.  Hence

\[
 \boxed{
 \Phi_c+2^N(c_{N+1}w_{N+1}+c_{N+2}w_{N+2})
 >\frac12A_{N+1}+\frac14A_{N+2}.}                 \tag{22}
\]

This is an exact discriminator in the finite audit.  At the first shadow
failure of each of the six noncoprime controls, both $A_{N+1}$ and
$A_{N+2}$ are zero: the lookahead window is a literal hole in the raw
source.  No such hole can occur for the $(2,3)$ source at large ranks,
because $A_m$ is the number of positive solutions of $2i+3j=m$ and differs
from $m/6$ by at most one.

There is also an exact interpretation of a large remaining scaled
residual.  Let $s=s(N)$ be the last skipped rank of the truncated-source
greedy word.  Every rank $s<d\leq N$ is then selected, so the residual at
the skipped rank gives

\[
 r_{N,H}
 <w_s-\sum_{s<d\leq N}w_d
 =\gamma_s+\sum_{d>N}w_d,                          \tag{23}
\]

where

\[
 \gamma_s=w_s-\sum_{d>s}w_d.
\]

The Lambert expansion

\[
 \gamma_s=\sum_{k\geq2}
 \frac{2^k-2}{2^k-1}\,2^{-ks}
\]

shows, for $s\geq2$, that $0<\gamma_s<4^{-s}$: the $k=2$ term is
$\frac23 4^{-s}$ and the terms $k\geq3$ total less than
$\frac13 4^{-s}$.  Also $\sum_{d>N}w_d<2^{1-N}$.  Therefore

\[
 \boxed{2^Nr_{N,H}<2^{N-2s}+2.}                   \tag{24}
\]

Combine (14), (16), (21), and integrality of a negative shadow margin.  A
sufficiently large one-step shadow failure for $1/21$ forces

\[
 2^Nr_{N,1}
 >\frac12A_{N+1}-4\sqrt{2N}+1
 =\frac N{12}-O(\sqrt N).                         \tag{25}
\]

Equations (24)--(25) force

\[
 s(N)\leq\frac N2-\frac12\log_2N+O(1).            \tag{26}
\]

Thus a shadow failure is not an arbitrary fractional accident: it requires
a terminal all-selected run extending past the midpoint gate.

This gives a rigorous cofinal dichotomy.  Suppose shadow failures occur at
unbounded horizons.  If their last-skipped ranks $s(N)$ are unbounded, then
(23) gives $r_{N,1}\to0$, while $x_{N,1}\to x$.  The associated finite
Boolean greedy sums converge to $x$, so closedness of the achievement set
proves $x$ is achieved.  If $s(N)$ is bounded, pass to a subsequence on
which $s$ and the finite prefix through $s$ are fixed.  The only branch not
already giving convergence is then a single positive permanent cofinite
gap

\[
 x-\sum_{d\in P}w_d-\sum_{d>s}w_d>0.              \tag{27}
\]

Accordingly, the raw-pulse argument removes every diffuse or repeatedly
moving shadow obstruction.  The sole residual obstruction is exactly the
fixed cofinite fatal branch already isolated by the quotient/greedy corpus;
it is not solved by (21)--(26).

## 6. Reproduction

Run

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/two_step_source_shadow.py --depth 450
```

The script uses exact `Fraction` arithmetic, asserts every positive case,
and checks the first failing horizon of all six controls.
