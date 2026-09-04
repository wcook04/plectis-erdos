# A terminal-corridor no-go for every coprime product source

## Result

Put

\[
 w_n=\frac1{2^n-1},\qquad
 M(a,b)=w_aw_b,
\]

and assume that $a,b\geq2$ are coprime.  Let

\[
 D=(2^a-1)(2^b-1),\qquad L=ab.
\]

The binary source clock of $M(a,b)=1/D$ has an exact formula.  If

\[
 r_{a,b}(n)=\#\{(i,j)\in\mathbb N_{>0}^2:ai+bj=n\}
\]

and $t_n$ is the periodic binary digit of $1/D$, then the raw carry

\[
 K_0=0,\qquad K_n=2K_{n-1}+t_n-r_{a,b}(n)
\]

satisfies

\[
 \boxed{K_n=\left\lfloor\frac n{ab}\right\rfloor.} \tag{1}
\]

This formula includes $M(2,3)=1/21$ and $M(4,5)=1/465$.  It does not
give terminal representability.  For every $B$ with $2^B>D$, the cofinite
Boolean word

\[
 b_n^{(B)}=\mathbf1_{n>B}                           \tag{2}
\]

lies strictly below $1/D$, is quotient-admissible at every depth, and has
a strictly positive target quotient left after its complete upper half has
been spent.  Thus the product period, the exact raw clock (1), quotient
admissibility, and an all-selected terminal block do not imply terminal
repayment for any coprime product source.

The word in (2) is not the real greedy word.  The theorem therefore does not
disprove terminal repayment for the actual greedy orbit of $1/21$, nor does
it decide whether $M(a,b)$ has an infinite Boolean representation.  It
rules out a source-only argument uniformly in $a,b$.

There is nevertheless a positive structural theorem before the first period
boundary.  The Boolean source in (5) is not merely a collision-free additive
count: it has a unique Boolean divisor ancestry.  Consequently, every quotient
row of $M(a,b)$ before rank $ab$ closes exactly.  Section 3 proves this fact.

## 1. The lattice count in one product period

The count $r_{a,b}$ satisfies

\[
 \boxed{r_{a,b}(n+L)=r_{a,b}(n)+1\qquad(n>0).}       \tag{3}
\]

Indeed, sending $(i,j)$ to $(i+b,j)$ injects the solutions at $n$
into those at $n+L$.  Among $1\leq i\leq b$, exactly one value satisfies
$ai\equiv n\pmod b$.  Its corresponding $j$ is positive because
$ai\leq ab=L<n+L$.  This is the unique solution not in the image.

There is no positive solution at $n=L$.  If $ai+bj=ab$, positivity of
$j$ gives $0<i<b$, while reduction modulo $b$ and coprimality force
$b\mid i$, a contradiction.  Hence, for $q\geq0$ and $1\leq s<L$,

\[
 r_{a,b}(qL+s)=q+r_{a,b}(s),\qquad
 r_{a,b}(qL)=q-1\quad(q\geq1).                     \tag{4}
\]

Before rank $L$, the count is Boolean:

\[
 r_{a,b}(s)\in\{0,1\}\qquad(1\leq s<L).            \tag{5}
\]

Two distinct solutions differ by
$(i,j)\mapsto(i+kb,j-ka)$ for some nonzero integer $k$.  Positivity then
forces their common value to be at least $L+a+b>L$, proving (5).

## 2. The binary word and raw carry

The geometric expansion gives

\[
 \frac1D=\sum_{n\geq1}r_{a,b}(n)2^{-n}.             \tag{6}
\]

Insert (4) into (6) and group the terms by their residue modulo $L$.  The
linear terms in $q$ cancel, leaving

\[
 \frac1D
 =\sum_{q\geq0}\left(
   \sum_{s=1}^{L-1}r_{a,b}(s)2^{-(qL+s)}
   +2^{-(q+1)L}
 \right).                                           \tag{7}
\]

For completeness, the cancellation uses

\[
 \sum_{s=1}^{L-1}2^{-s}=1-2^{1-L}
\]

and

\[
 \sum_{q\geq0}q2^{-qL}(2-2^{1-L})
 =2\sum_{q\geq1}2^{-qL}.
\]

Equation (7), together with (5), identifies the period-$L$ binary word:

\[
 \boxed{
 t_s=r_{a,b}(s)\quad(1\leq s<L),\qquad t_L=1.}      \tag{8}
\]

Now let $n=qL+s$.  If $1\leq s<L$, equations (4) and (8) give

\[
 2q+t_s-r_{a,b}(n)=q.
\]

At $n=(q+1)L$, they give

\[
 2q+1-q=q+1.
\]

Induction proves (1).

## 3. Unique Boolean ancestry before the period boundary

Let

\[
 \mathcal S=\{ai+bj:i,j\geq1\}.
\]

For every $n<L$, the set of divisors of $n$ which belong to $\mathcal S$ is
closed under greatest common divisors.  Indeed, take $x,y\in\mathcal S$ with
$x\mid n$ and $y\mid n$.  Write

\[
 x=gr,\qquad y=gs,\qquad \gcd(r,s)=1,
\]

where $g=\gcd(x,y)$.  Since $\operatorname{lcm}(x,y)=grs$ divides $n$,

\[
 grs<ab.                                             \tag{9}
\]

Choose positive representations

\[
 x=ai+bj,\qquad y=ak+b\ell.
\]

The identity $sx=ry$ gives

\[
 a(si-rk)=b(r\ell-sj).                              \tag{10}
\]

Both $si$ and $rk$ lie strictly between $0$ and $b$: for example,
$a(si)<sx=grs<ab$, and the other three bounds follow in the same way.
Because $b\mid(si-rk)$, the first pair of bounds forces $si=rk$.
Similarly $a\mid(r\ell-sj)$ and the second pair forces $r\ell=sj$.
Coprimality of $r$ and $s$ now gives positive integers $I,J$ such that

\[
 i=rI,\quad k=sI,\quad j=rJ,\quad \ell=sJ.
\]

It follows that

\[
 g=aI+bJ\in\mathcal S,                              \tag{11}
\]

which proves the gcd-closure claim.

Let $A_{a,b}$ be the set of divisibility-minimal members of $\mathcal S$
below $L$.  The semigroup $\mathcal S$ is upward closed under multiplication:
if $d=ai+bj$ and $d\mid n$, then $n=a(mi)+b(mj)$ for $m=n/d$.
Thus an $n<L$ outside $\mathcal S$ has no $\mathcal S$-divisor.  If
$n\in\mathcal S$, the gcd of all its $\mathcal S$-divisors belongs to
$\mathcal S$ by (11), divides every one of them, and is therefore the unique
member of $A_{a,b}$ dividing $n$.  Hence

\[
 \boxed{
 \mathbf1_{\mathcal S}(n)
   =\sum_{\substack{d\mid n\\d\in A_{a,b}}}1
 \qquad(1\leq n<L).}                               \tag{12}
\]

By (5) and (8), the left side is exactly the target digit $t_n$.  Therefore
the Boolean support $A_{a,b}$ has proper-divisor load $t_n$ at every rank
$n<L$.  Expanding the target floor in its first $N$ binary digits and using

\[
 \left\lfloor\frac{2^N}{2^d-1}\right\rfloor
 =\sum_{\substack{k\geq1\\kd\leq N}}2^{N-kd}
\]

on each selected column makes this coefficient identity equivalent, for every
$N<L$, to

\[
 \boxed{
 \left\lfloor\frac{2^N}{D}\right\rfloor
 =\sum_{\substack{d\in A_{a,b}\\d\leq N}}
   \left\lfloor\frac{2^N}{2^d-1}\right\rfloor.}   \tag{13}
\]

Thus every coprime product source has a canonical, source-reachable Boolean
prefix with zero quotient defect throughout its first period.  In fact, it is
the actual real greedy prefix.  To see the required orientation, decompose
every positive pair uniquely into a positive multiple of a primitive pair:

\[
 M(a,b)
 =\sum_{\substack{i,j\geq1\\\gcd(i,j)=1}}w_{ai+bj}.
\]

Below $L$, an exponent $ai+bj$ belongs to $A_{a,b}$ exactly when $(i,j)$ is
primitive.  One direction follows because a common divisor of $i,j$ would
produce a smaller member of $\mathcal S$ dividing the exponent.  Conversely,
a smaller $\mathcal S$-divisor would, by uniqueness of the representation
below $L$, express $(i,j)$ as a nontrivial multiple.  The displayed positive
identity therefore shows that, after any initial segment of $A_{a,b}$ has
been selected, the real residual is positive.

If $N\notin A_{a,b}$, (13) gives

\[
 2^N\left(M(a,b)-\sum_{\substack{d\in A_{a,b}\\d<N}}w_d\right)
 =\left\{\frac{2^N}{D}\right\}
  -\sum_{\substack{d\in A_{a,b}\\d<N}}
     \left\{\frac{2^N}{2^d-1}\right\}.
\]

The left side is positive and the first term on the right is smaller than
$1$, so the residual is smaller than $2^{-N}<w_N$; rank $N$ is correctly
skipped.  If $N\in A_{a,b}$, the positive decomposition leaves $w_N$ plus a
positive remainder, so rank $N$ is correctly taken.  Induction proves exact
greedy agreement through $L-1$.

This is a real ancestry theorem, not a raw multiplicity statement.  It stops
exactly where the period carry enters: at rank $L$, (8) has $t_L=1$ whereas
$r_{a,b}(L)=0$.  Past that boundary, additive multiplicities and binary carry
return, and (12) alone gives no Boolean continuation.

## 4. A universal cofinite terminal counterfamily

Fix $B$ with $2^B>D$, and take the word (2).  The complete Mersenne tail
obeys

\[
 \sum_{n>B}w_n
 <\frac{2}{2^{B+1}-1}.                              \tag{14}
\]

Because $D$ is odd, $2^B>D$ implies
$2D<2^{B+1}-1$.  Thus (14) is strictly smaller than $1/D$.  Every finite
prefix of (2) is consequently real-feasible.

For a finite Boolean word $c$, define its quotient defect at depth $N$ by

\[
 Q_N(c)=\left\lfloor\frac{2^N}{D}\right\rfloor
 -\sum_{d\leq N}c_d
  \left\lfloor\frac{2^N}{2^d-1}\right\rfloor.       \tag{15}
\]

Real feasibility implies $Q_N(c)\geq0$: after multiplication by $2^N$,
the sum of the integer quotient coins is at most the scaled real prefix,
which is strictly below $2^N/D$.  Hence (2) is quotient-admissible at every
depth.

At depth $2B$, the selected ranks are exactly $B<d\leq2B$.  Since
$2B<2d$, Euclidean division gives

\[
 \left\lfloor\frac{2^{2B}}{2^d-1}\right\rfloor
 =2^{2B-d}.
\]

Therefore the complete upper-half supply is

\[
 \sum_{B<d\leq2B}2^{2B-d}=2^B-1.                  \tag{16}
\]

On the other hand, $2^B>D$ gives

\[
 \left\lfloor\frac{2^{2B}}D\right\rfloor\geq2^B.
\]

Combining this with (15)--(16) proves

\[
 \boxed{Q_{2B}(b^{(B)})\geq1.}                    \tag{17}
\]

Thus an empty lower half and a completely selected upper half still leave an
unpaid target quotient.  Any terminal-corridor theorem whose hypotheses retain
only the product source, quotient admissibility, and the terminal block is
false for every coprime pair $a,b\geq2$.

For $1/21=M(2,3)$, one may take $B=5$.  The upper quotient coins total
$31$, while

\[
 \left\lfloor\frac{2^{10}}{21}\right\rfloor=48,
 \qquad Q_{10}=17.                                  \tag{18}
\]

The missing hypothesis is real greedy complementarity, or an equivalent
ownership law which records every affordable earlier rank.  Changing the
product anchor does not supply it.

## 5. Exact audit

The companion program checks (3)--(8) and the Boolean ancestry identity
(12)--(13) for coprime pairs through a bounded grid, and verifies
(14)--(18) with exact integer and rational arithmetic.  The universal
statements follow from the displayed calculations, not from the audit range.

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/coprime_product_terminal_corridor_nogo.py
```
