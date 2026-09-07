# Compatibility of the $1/465$ source corridor

Status: exact conditional theorem, 2026-08-21.  The results below prove that
the full-prefix quotient construction gives a compatible infinite Boolean
word once its endpoint interval and lower-prefix conditions hold at every
rank.  They also isolate the only obstruction in the induction that would
establish those conditions.  The required all-rank phase exclusion is not
proved here.

Put

\[
 x=\frac1{465},\qquad K_n=\left\lfloor\frac n{20}\right\rfloor.
\]

Let $t_n\in\{0,1\}$ be the binary digits of $x$, so that, if
$u_0=1$,

\[
 2u_{n-1}=465t_n+u_n.
\]

The word $t$ has period $20$, with ones in residue classes
$9,13,14,17,18,19,20$.  For a Boolean word
$b=(b_1,\ldots,b_n)$, define

\[
 f_b(j)=\sum_{d\mid j}b_d,\qquad
 Q_0=0,\qquad Q_j=2Q_{j-1}+t_j-f_b(j).
 \tag{1}
\]

Write $\mathcal T_n$ for the set of words of length $n$ satisfying

\[
 0\leq Q_j\leq K_j\qquad(1\leq j\leq n).          \tag{2}
\]

Thus $\mathcal T=\bigcup_n\mathcal T_n$, with the usual prefix edges, is
a finitely branching rooted tree.  The point of retaining the complete word
in a state is that this tree structure is then literal; an endpoint-only
table with an arbitrarily chosen representative need not have this property.

## 1. The coherent one-step lemma

For $b\in\mathcal T_{n-1}$, put

\[
 g_n(b)=\sum_{\substack{d\mid n\\d<n}}b_d.
\]

Suppose that the endpoint map $b\mapsto Q_{n-1}(b)$ is a bijection from
$\mathcal T_{n-1}$ to $[0,K_{n-1}]\cap\mathbb Z$, and that $g_n(b)$
has the same value $g_n$ for every state.  The two children of the state
with endpoint $q$ have endpoints

\[
 q'=2q+t_n-g_n-b_n,\qquad b_n\in\{0,1\}.          \tag{3}
\]

As $q$ runs from $0$ to $K_{n-1}$, these endpoints are the distinct
integers in

\[
 [t_n-g_n-1,\,2K_{n-1}+t_n-g_n].                 \tag{4}
\]

Indeed, parity in (3) determines $b_n$, and then determines $q$.  Let
$r(n)$ be the number of positive solutions of $4i+5j=n$.  The product
identity for the source gives

\[
 K_n=2K_{n-1}+t_n-r(n).                           \tag{5}
\]

The left endpoint in (4) is at most zero.  If $g_n\leq r(n)$, the right
endpoint is at least $K_n$.  Intersecting (4) with the corridor therefore
proves that the endpoint map on $\mathcal T_n$ is a bijection onto
$[0,K_n]\cap\mathbb Z$.

Agreement of all states through $\lfloor n/2\rfloor$ is more than is
needed for this lemma, but it makes $g_n$ state-independent.  Every proper
divisor of $n$ is at most $n/2$.

## 2. Inverse blocks

Suppose that all words under consideration agree through rank $m$, where
$m\geq\lfloor n/2\rfloor$.  For $m<j\leq n$, all proper-divisor sums
$g_j$ are then fixed.  Put $c_j=t_j-g_j$.  Equation (3) has the unique
inverse

\[
 b_j\equiv c_j-q_j\pmod 2,\qquad
 q_{j-1}=\frac{q_j-c_j+b_j}{2}.                   \tag{6}
\]

Unwinding the block gives

\[
 q_n=2^{n-m}q_m+A_{m,n}
      -\sum_{j=m+1}^n2^{n-j}b_j,                  \tag{7}
\]

where $A_{m,n}$ depends only on the fixed loads $g_j$ and the source
digits $t_j$.  Thus the terminal endpoint determines both its ancestor
endpoint and its suffix bits.  If the ancestor endpoint is fixed and the
terminal endpoints form an integer interval, the corresponding suffixes,
read as binary integers, form an interval in the reverse order.

This gives a precise nesting criterion.  Let

\[
 a_{n,m}:\mathcal T_n\longrightarrow\mathcal T_m
\]

be prefix restriction.  If the endpoint map is injective on
$\mathcal T_m$, then all words in $\mathcal T_n$ agree through $m$ if
and only if their ancestors under $a_{n,m}$ have one common endpoint.
Consequently the computational statement that the inverse block has one
common lower-half ancestor is exactly a compatibility statement about the
full-prefix tree, rather than a statement about levelwise endpoint counts.

## 3. The even-rank obstruction

The common-prefix induction is automatic at odd ranks.  Its only new bit at
rank $2s$ is $b_s$.  The following calculation identifies what must be
excluded.

Assume that the endpoint map on $\mathcal T_{2s-1}$ is a bijection onto
$[0,K_{2s-1}]\cap\mathbb Z$, and that all its words agree through $s-1$.
Between ranks $s$ and $2s-1$, every proper divisor lies below $s$.
Equation (7) therefore applies to this whole block.

If $b_s$ takes both values on $\mathcal T_{2s-1}$, the binary-interval
description in (7) supplies an integer $a$ such that

\[
 \begin{array}{c|c}
 b_s=1 & 0\leq q\leq a-1,\\
 b_s=0 & a\leq q\leq K_{2s-1}.
 \end{array}                                      \tag{8}
\]

The adjacent boundary words have suffixes

\[
 1,0^{s-1}\quad\hbox{and}\quad0,1^{s-1};       \tag{9}
\]

their endpoints are $a-1$ and $a$, respectively.

The phase condition can also be stated without naming the individual
suffixes.  Let $C_s$ be the right-hand side of (7) with all $s$ suffix
bits set to zero.  Since $q_{2s-1}=C_s-B$, where $B$ is the integer
represented by $b_s\ldots b_{2s-1}$, endpoint fullness gives

\[
 K_{2s-1}\leq C_s\leq2^s-1.
\]

The leading suffix bit varies if and only if
$[C_s-K_{2s-1},C_s]$ crosses the binary midpoint.  Equivalently,

\[
 2^{s-1}\leq C_s
 \leq2^{s-1}+K_{2s-1}-1.                          \tag{10}
\]

Thus the unresolved even seam is an integer exclusion from an interval of
length $K_{2s-1}$ adjacent to an exponentially larger dyadic midpoint.

Every proper divisor of $2s$, other than $s$, is less than $s$.  Hence

\[
 h=\sum_{\substack{d\mid2s\\d<2s,\ d\ne s}}b_d
\]

is common to all states.  Put $c=t_{2s}-h$.  Before intersection with the
new corridor, the children of the two families in (8) have endpoint sets

\[
 [c-2,\,2a+c-3]
 \quad\hbox{and}\quad
 [2a+c-1,\,2K_{2s-1}+c].                          \tag{11}
\]

They omit exactly the middle integer

\[
 z_s=2a+c-2.                                      \tag{12}
\]

There are no collisions within or between the two intervals.  If both
families have a child in $[0,K_{2s}]$, then the left interval reaches at
least $0$ and the right interval begins at most at $K_{2s}$.  It follows
that

\[
 1\leq z_s\leq K_{2s}-1.                          \tag{13}
\]

Thus a full child endpoint interval is impossible while both values of
$b_s$ survive.  Conversely, if $z_s\notin[0,K_{2s}]$, and the two outer
endpoints in (11) bracket the corridor, then (11) covers every corridor
endpoint exactly once and all surviving children have the same value of
$b_s$.

This is the exact even-rank phase condition.  A proof that $z_s$ always
lies outside the corridor whenever the split (8) occurs would complete the
simultaneous induction of endpoint bijectivity and common lower-half
prefixes.  Neither the divisor estimate $g_n\leq r(n)$ nor levelwise
nonemptiness alone proves this phase condition.

The obstruction is not a formal consequence of corridor widths.  In the
same two-family calculation, take a parent corridor with ceiling $10$, put
$a=6$, and take $c=-5$.  Equation (12) gives $z_s=5$, an interior missing
endpoint.  This artificial state need not arise from the fixed $1/465$
source; it shows why the remaining proof must use that source's arithmetic.

## 4. Compactness and the target value

Suppose now that, for every $n$, the endpoint map on $\mathcal T_n$ is a
bijection onto $[0,K_n]\cap\mathbb Z$.  In particular every level of the
finitely branching tree $\mathcal T$ is nonempty.  König's lemma gives an
infinite Boolean word $b$ whose every prefix satisfies (2).  No choice of
one representative independently at successive levels is used here: the
vertices are complete prefixes and the edges are literal restriction maps.

Along this branch,

\[
 0\leq Q_n\leq K_n=O(n),
\]

so $Q_n/2^n\to0$.  The finite quotient telescope, followed by the Lambert
regrouping, gives

\[
 \sum_{d\geq1}\frac{b_d}{2^d-1}=\frac1{465}.      \tag{14}
\]

The support of this word is necessarily infinite.  Otherwise let $m$ be
its largest selected rank.  If $m>6$, Bang--Zsigmondy gives a primitive
prime divisor $p$ of $2^m-1$.  The multiplicative order of $2$ modulo $p$
is $m$, so $p$ divides no earlier Mersenne denominator.  Moreover
$p\nmid465$, since the primes $3,5,31$ have orders $2,4,5$, respectively.
The term $1/(2^m-1)$ then has negative $p$-adic valuation, while every
earlier term and $1/465$ is $p$-integral, which contradicts (14).  The
Zsigmondy exception $m=6$ and all smaller maxima are excluded by the direct
check of the $2^6$ subsets of ranks $1,\ldots,6$; none sums to $1/465$.

Strict superincreasingness of the Mersenne weights shows that there is at
most one such tempered branch.  It also implies a nonquantitative
stabilisation statement: for each fixed $m$, all sufficiently deep levels
$\mathcal T_n$ have the same prefix through $m$.  This follows because a
second prefix occurring at arbitrarily large depths would, by König's
lemma, produce a second infinite branch.  This eventual stabilisation does
not supply the quantitative bound $n\geq2m$ needed by the lower-half
induction.

## 5. Finite evidence

The script

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_source_corridor_dp.py --horizon 10000

retains complete prefixes.  In exact integer arithmetic it finds one state
for every endpoint $0\leq q\leq K_n$ and agreement through
$\lfloor n/2\rfloor$ at every audited rank.  This is finite evidence for
the hypotheses above.  It is not a proof of the all-rank phase exclusion in
(12)--(13).
