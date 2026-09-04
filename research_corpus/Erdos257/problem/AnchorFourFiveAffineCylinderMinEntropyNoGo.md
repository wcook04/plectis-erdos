# Affine greedy cylinders and a blockwise min-entropy no-go

## Status

This note derives the exact affine cylinder law obeyed by the real-greedy
residual for \(1/465\). It then gives an exact family of period-\(20\) greedy
cylinders which begin below the dyadic cutoff and end in the dangerous dyadic
interval with cleared gap numerator \(1\). Consequently neither affine block
factorisation, greedy-cylinder admissibility, nor a least-positive-
representative bound applied one block at a time can prove the required
dyadic undershoot. The construction changes the starting residual; it is not
a counterexample on the actual \(1/465\) orbit.

Put

\[
 q_j=2^j-1,\qquad w_j=q_j^{-1}.
\]

Let \(R_j\) be a real-greedy residual after the decision at rank \(j\), with

\[
 b_j=\mathbf 1_{R_{j-1}\geq w_j},\qquad
 R_j=R_{j-1}-b_jw_j.
\]

For the actual orbit considered elsewhere, \(R_0=1/465\). The identities
below hold for any positive rational starting residual.

## 1. Exact affine block factorisation

Use the dyadic-gap coordinate

\[
 g_j=1-2^jR_j
\]

and the threshold

\[
 \theta_j=\frac{2^{j-1}-1}{2^j-1}
          =\frac12-\frac1{2q_j}.
\]

The greedy decision and the two affine branches are exactly

\[
 b_j=1\iff g_{j-1}\leq\theta_j,
\]

\[
 g_j=
 \begin{cases}
  2g_{j-1}-1,&b_j=0,\\[1mm]
  2g_{j-1}+q_j^{-1},&b_j=1.
 \end{cases}                                      \tag{1}
\]

For a word \(u=(u_1,\ldots,u_L)\in\{0,1\}^L\) beginning after rank \(n\),
write

\[
 a_{n+i}(u_i)=
 \begin{cases}
  -1,&u_i=0,\\
  q_{n+i}^{-1},&u_i=1,
 \end{cases}
\]

and

\[
 c_{n,L}(u)=\sum_{i=1}^L2^{L-i}a_{n+i}(u_i).
\]

On the cylinder with decision word \(u\), iteration of (1) gives

\[
 \boxed{g_{n+L}=2^Lg_n+c_{n,L}(u).}               \tag{2}
\]

If \(u\) and \(v\) are consecutive words of lengths \(L\) and \(M\), then

\[
 \boxed{
 c_{n,L+M}(uv)=2^Mc_{n,L}(u)+c_{n+L,M}(v).}       \tag{3}
\]

Thus the period-\(20\) return is an exact affine map of slope \(2^{20}\).
There is no stochastic approximation in (2) or (3).

There is also an integer version. Put

\[
 Q_{n,L}(u)=\prod_{\substack{1\leq i\leq L\\u_i=1}}q_{n+i},
 \qquad C_{n,L}(u)=Q_{n,L}(u)c_{n,L}(u)\in\mathbb Z.
\]

If \(g_n=G/D\), without requiring lowest terms, then

\[
 \boxed{
 g_{n+L}=\frac{2^LQ_{n,L}(u)G+DC_{n,L}(u)}
                 {DQ_{n,L}(u)}.}                 \tag{4}
\]

Equivalently, the integer pair updates by

\[
 (D,G)\longmapsto
 \bigl(DQ_{n,L}(u),\,2^LQ_{n,L}(u)G+DC_{n,L}(u)\bigr).       \tag{5}
\]

For consecutive words \(u,v\), the integer charges concatenate as

\[
 \boxed{
 C_{n,L+M}(uv)
 =2^MQ_{n+L,M}(v)C_{n,L}(u)
  +Q_{n,L}(u)C_{n+L,M}(v).}                       \tag{6}
\]

Equations (5) and (6) are the cleared-numerator state and concatenation law
suggested by an inverse-cylinder approach.

## 2. The dangerous interval

If rank \(m\) is skipped, then \(R_m<w_m\). In the \(g\)-coordinate,

\[
 R_m\geq2^{-m}
 \quad\Longleftrightarrow\quad
 -\frac1{q_m}<g_m\leq0.                           \tag{7}
\]

Hence the desired theorem for the actual \(1/465\) orbit is that its skipped
states never enter the interval in (7).

## 3. Exact recompression in one period-\(20\) cylinder

Fix \(m\geq40\) and an integer \(k\geq2\). Define

\[
 \rho_{m,k}=\frac{k}{k2^m-1}
\]

and the starting residual at rank \(m-20\)

\[
 S_{m,k}=\rho_{m,k}+\sum_{d=m-19}^{m-1}w_d.       \tag{8}
\]

Then

\[
 \boxed{0<S_{m,k}<2^{-(m-20)}<w_{m-20}.}         \tag{9}
\]

To prove the upper bound, first note

\[
 0<\rho_{m,k}-2^{-m}
   =\frac1{2^m(k2^m-1)}\leq2^{-2m}.
\]

Also, for every \(d\geq1\),

\[
 0<w_d-2^{-d}
   =\frac1{2^d(2^d-1)}<2^{-2d+1}.
\]

The dyadic parts in (8) sum to

\[
 2^{-m}+\sum_{d=m-19}^{m-1}2^{-d}
 =2^{-(m-20)}-2^{-m}.
\]

The total correction is less than

\[
 2^{-2m}+\sum_{d=m-19}^{\infty}2^{-2d+1}
 =2^{-2m}+\frac83\,2^{-2m+38}<2^{-m}
\]

for \(m\geq40\), proving (9).

Starting from \(S_{m,k}\), the next twenty greedy decisions are exactly

\[
 \boxed{1^{19}0.}                                \tag{10}
\]

Indeed, immediately before every rank \(d=m-19,\ldots,m-1\), the residual is

\[
 \rho_{m,k}+\sum_{e=d}^{m-1}w_e\geq w_d,
\]

so that rank is taken. After those nineteen subtractions the residual is
\(\rho_{m,k}\), and

\[
 2^{-m}<\rho_{m,k}<w_m                           \tag{11}
\]

because \(k\geq2\). Rank \(m\) is therefore skipped inside the dangerous
interval.

More sharply, its cleared dyadic gap is the least possible nonzero integer:

\[
 \boxed{
 g_m=1-2^m\rho_{m,k}=-\frac1{k2^m-1}.}           \tag{12}
\]

Thus the endpoint numerator in (4), after reduction, has absolute value
\(1\), at arbitrarily late period-\(20\) blocks. The starting state (9) is
itself strictly below its dyadic cutoff, so even the implication

\[
 \text{safe skipped state at }m-20
 \Longrightarrow
 \text{safe skipped state at }m
\]

fails on the exact greedy cylinder \(1^{19}0\).

## 4. Consequence for the \(1/465\) route

The affine factorisation is exact, but it has no blockwise min-entropy gain:
an admissible period-\(20\) word can recompress the cleared gap all the way to
one unit. Any lower bound depending only on the block word, its affine
multiplier, cylinder admissibility, and safety at the preceding block
boundary is therefore false.

This does not settle the actual \(1/465\) orbit, because the family (8) does
not assert \(S_{m,k}=R_{m-20}\) for that orbit. A viable anti-compression
theorem must use arithmetic tying the cylinder to the fixed source
\(R_0=1/465\): for example, the full selected-divisor history or an equivalent
source-coupled residue. The affine block law alone deliberately forgets that
information.

The companion script verifies (1)--(6) and the family (8)--(12) with exact
rational arithmetic.
