# Irrationality of a reciprocal-divergent burst-and-escape support

## Status

This note gives an abstract denominator-versus-tail irrationality criterion
and applies it to a self-similar construction class not covered by the two
standard support tests in the current corpus.  The explicit support below is
neither eventually periodic nor reciprocal-summable:

\[
\sum_{n\in A}\frac1n=\infty.
\]

Nevertheless its Boolean Mersenne sum is irrational.  Thus making every
generation internally dense does not rescue a construction whose successive
generations escape too quickly in rank.  The abstract theorem also gives the
complementary quantitative law: every support not detected by denominator
escape must keep its next selected rank within \(O(1)\) of its accumulated
Mersenne LCM height.

## The denominator-versus-tail theorem

Let

\[
A=\{a_1<a_2<\cdots\}\subseteq\mathbb N
\]

be any infinite support, and put

\[
S_j=\sum_{i=1}^j\frac1{2^{a_i}-1},\qquad
T_j=\sum_{i>j}\frac1{2^{a_i}-1}.
\]

Let \(D_j\) be the reduced denominator of \(S_j\), and define the explicit
Mersenne LCM

\[
\mathcal D_j=\operatorname{lcm}_{1\le i\le j}(2^{a_i}-1).
\tag{1}
\]

Thus \(D_j\mid\mathcal D_j\).

> **Denominator-tail criterion.** If
> \[
> \liminf_{j\to\infty}D_jT_j=0,
> \tag{2}
> \]
> then \(\sum_{n\in A}(2^n-1)^{-1}\) is irrational.

Indeed, suppose the full sum were \(p/q\) with \(q>0\).  Positivity and the
infinitude of \(A\) make \(T_j=p/q-S_j\) a nonzero rational.  Its denominator
divides \(qD_j\), so

\[
T_j\ge\frac1{qD_j}.
\tag{3}
\]

This contradicts (2).

The complete Mersenne tail gives a support-only sufficient condition.  Since

\[
T_j
\le\sum_{n=a_{j+1}}^\infty\frac1{2^n-1}
<2^{2-a_{j+1}},
\tag{4}
\]

one obtains:

> **LCM-height escape criterion.** If
> \[
> \liminf_{j\to\infty}
> \mathcal D_j\,2^{\,2-a_{j+1}}=0,
> \tag{5}
> \]
> then the Boolean Mersenne sum on \(A\) is irrational.

Conversely, if the sum is the rational \(p/q\), (3)--(4) force, at every
rank \(j\),

\[
\boxed{
a_{j+1}
<\log_2 D_j+\log_2 q+2
\le\log_2\mathcal D_j+\log_2 q+2.
}
\tag{6}
\]

This is the promised no-large-gap law.  A rational support cannot place its
next selected rank substantially beyond the binary height already present
in the LCM of its earlier Mersenne denominators.

There is also an unconditional dichotomy for every infinite support.  Either
the liminf in (5) is zero, in which case the sum is irrational, or there are
constants \(\eta>0\) and \(j_0\) such that

\[
\mathcal D_j2^{\,2-a_{j+1}}\ge\eta\qquad(j\ge j_0).
\]

In the second case,

\[
a_{j+1}\le\log_2\mathcal D_j+2-\log_2\eta
\qquad(j\ge j_0).
\tag{7}
\]

Thus every construction which evades the denominator-tail proof is forced
into a quantitative LCM-dense regime.  This conclusion applies in
particular to reciprocal-divergent supports; reciprocal divergence alone
does not decide which side of the dichotomy occurs.

## The explicit support

Define

\[
L_1=2,\qquad L_{k+1}=L_k^3,
\]

and let

\[
A=\bigcup_{k\ge1}\{L_k,L_k+1,\ldots,2L_k-1\}.
\tag{8}
\]

The blocks are disjoint because \(L_k^3>2L_k\) for \(L_k\ge2\).  Put

\[
X_A=\sum_{n\in A}\frac1{2^n-1}.
\tag{9}
\]

> **Theorem.** The real number \(X_A\) is irrational.

## Reciprocal divergence and nonperiodicity

Every block contributes at least one half to the reciprocal support sum:

\[
\sum_{n=L_k}^{2L_k-1}\frac1n
\ge L_k\frac1{2L_k}
=\frac12.
\tag{10}
\]

Hence

\[
\sum_{n\in A}\frac1n=\infty.
\tag{11}
\]

On the other hand, the zero gap between the \(k\)-th and \((k+1)\)-st
blocks has length

\[
L_{k+1}-2L_k=L_k^3-2L_k\longrightarrow\infty.
\]

Since there are also infinitely many nonzero blocks, the indicator of \(A\)
is not eventually periodic.

Thus neither eventual-periodicity irrationality nor the existing
reciprocal-summability theorem applies to this support.

## Denominator separation

Let

\[
X_k=\sum_{\substack{n\in A\\n<2L_k}}\frac1{2^n-1}
\]

be the sum through the \(k\)-th block, and let \(D_k\) be the product of
its displayed denominators.  We do not need this product to be reduced.
Since every selected rank in \(X_k\) is at most \(2L_k-1\),

\[
\begin{aligned}
D_k
&\le \prod_{n=1}^{2L_k-1}(2^n-1)\\
&<2^{\sum_{n=1}^{2L_k-1}n}
<2^{2L_k^2}.
 \end{aligned}
\tag{12}
\]

The remaining support begins at \(L_{k+1}=L_k^3\).  Positivity and the
complete geometric tail give

\[
\begin{aligned}
0<X_A-X_k
&\le\sum_{n=L_k^3}^{\infty}\frac1{2^n-1}\\
&<\sum_{n=L_k^3}^{\infty}2^{1-n}
=2^{2-L_k^3}.
\end{aligned}
\tag{13}
\]

Suppose, for contradiction, that \(X_A=p/q\) with \(p,q\in\mathbb Z\) and
\(q>0\).  The difference \(X_A-X_k\) is a nonzero rational whose
denominator divides \(qD_k\).  Therefore

\[
X_A-X_k\ge\frac1{qD_k}
>q^{-1}2^{-2L_k^2}.
\tag{14}
\]

For all sufficiently large \(k\),

\[
2^{2-L_k^3}<q^{-1}2^{-2L_k^2},
\]

because \(L_k^3-2L_k^2-2\to\infty\).  This contradicts (13)--(14), proving
the theorem.

## Construction consequence

This excludes a broader mechanism than a single geometrically sparse orbit.
Each generation in (8) contains \(L_k\) consecutive selected ranks and
contributes a fixed positive amount to \(\sum_{n\in A}1/n\).  The
obstruction is instead the separation of scales: before the next burst, the
old rational denominator has height \(2^{O(L_k^2)}\), whereas the new tail
is \(2^{-L_k^3+O(1)}\).

More generally, the same proof applies to any infinite sequence of finite
Boolean blocks for which the logarithm of the accumulated denominator
before the next block is \(o\) of that block's first rank.  Such
burst-and-escape substitutions cannot produce a rational target even when
their support is reciprocal-divergent and highly nonuniform inside every
generation.
