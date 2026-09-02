# The Tao--Teräväinen incidence boundary for arbitrary Mersenne supports

Status: exact algebraic classification and exact correlation counterexample,
2026-08-21. The source analysed is Tao--Teräväinen,
[arXiv:2512.01739v2](https://arxiv.org/abs/2512.01739), especially Section 5
and equations (5.1)--(5.21). The conclusions below do not extend their
irrationality theorem to arbitrary supports. They identify an exact input of
their proof and show that reciprocal divergence alone does not provide it.

Let \(A\subseteq\mathbb N\) and put
\[
 f_A(n)=\sum_{d\mid n}{\mathbf{1}}_A(d),
 \qquad
 S_A=\sum_{d\in A}\frac1{2^d-1}
     =\sum_{n\geq1}\frac{f_A(n)}{2^n}.             \tag{1}
\]

## 1. The inputs used in the prime-support proof

For prime support, \(f_A=\omega\). Rationality of \(S_A\) first gives the
shift congruence in equation (5.1) of the source. The next step is not a
formal consequence of that congruence. It uses, for every prime \(p\), the
exact localization
\[
 \omega(pn)-\omega(n)=1-{\mathbf{1}}_{p\mid n}.          \tag{2}
\]
This is what produces equation (5.2): dilation by \(p\) changes the shifted
series by one geometrically summable divisibility defect \(\delta_p\).

The proof then requires a \(K\)-dimensional affine cube of distinct primes
\(p_\epsilon\), equations (5.4)--(5.7). The alternating cube sum cancels the
first \(K\) shifted terms. After truncation, each remaining prime atom gives
the random variable \(X_p\) in equation (5.13). The technical reduction,
Theorem 5.1, needs both
\[
 kappa_1,ldots,\kappa_5=o(1)                    \tag{3}
\]
and the nonvanishing diagonal variance
\[
 sum_{p\in S_1}\operatorname{Var}X_p\gg1.        \tag{4}
\]
For medium primes the paper proves
\[
 \operatorname{Var}X_p\asymp\frac1{2^Kp},        \tag{5}
\]
and obtains (4) from Mertens' theorem. The off-diagonal and large-prime
terms are controlled by exact congruence separation and by the quantitative
two-point multiplicative correlation theorem developed earlier in the
paper.

Thus the proof uses three logically distinct properties of the prime
support:

1. localized dilation as in (2);
2. affine-cube supply among admissible dilation parameters;
3. reciprocal mass carried by approximately decorrelated incidence atoms,
   together with cancellation of the large-atom part.

Only the reciprocal mass resembles the condition
\(\sum_{d\in A}1/d=\infty\).

## 2. Exact classification of localized dilation

The algebraic input (2) has a complete classification for divisor-incidence
sequences.

> **Localized-dilation theorem.** Let \(a\in A\). The identity
> \[
>  f_A(an)-f_A(n)=1-{\mathbf{1}}_{a\mid n}               \tag{6}
> \]
> holds for every \(n\geq1\) if and only if
> \[
>  \gcd(a,b)=1\qquad\text{for every }b\in A, b\ne a.             \tag{7}
> \]

To prove the forward direction, suppose that \(b\in A\setminus\{a\}\)
and \(g=\gcd(a,b)>1\). Put \(n=b/g\). Then \(b\nmid n\) but
\(b\mid an\). Multiplication by \(a\) cannot destroy any old
\(A\)-divisor. The contribution of \(a\) changes by exactly the right side of
(6), whether that change is zero or one, while \(b\) supplies one additional
new divisor, a contradiction.

Conversely, assume (7). The contribution of \(a\) to
\(f_A(an)-f_A(n)\) is exactly \(1-{\mathbf{1}}_{a\mid n}\). For
\(b\in A\setminus\{a\}\), coprimality gives
\[
 b\mid an\quad\Longleftrightarrow\quad b\mid n,
\]
so every other contribution cancels. This proves (6).

Consequently, a family of support elements can play the dilation role of
the primes only if each chosen element is coprime to every other element of
the full support. If every element of \(A\) is to be available, the exact
minimum algebraic condition is pairwise coprimality of \(A\). This statement
concerns the shift--dilate step only; pairwise coprimality does not supply
the affine cubes or the analytic estimates (3)--(5).

## 3. The correlation requirement is independent

The ideal uniform-residue covariance of two incidence atoms is
\[
 \lim_{X\to\infty}\operatorname{Cov}_{n\leq X}
   ({\mathbf{1}}_{d\mid n},{\bf1}_{e\mid n})
 =\frac1{\operatorname{lcm}(d,e)}-\frac1{de}
 =\frac{\gcd(d,e)-1}{de}.                         \tag{8}
\]
It vanishes for distinct coprime atoms. A shared factor produces a positive
main term, before any of the shifted-correlation errors treated in the
paper arise. Hence a divergent reciprocal sum does not imply the diagonal
variance structure used in (4); the shared-factor covariance can be of the
same order as the square of the total reciprocal mass.

This failure occurs in a support which is as close to the primes as a fixed
dilation permits. Let
\[
 A=2\mathbb P=\{2p:p\text{ prime}\}.              \tag{9}
\]
Then
\[
 sum_{a\in A}\frac1a=\frac12\sum_p\frac1p=\infty.               \tag{10}
\]
Nevertheless every two distinct elements of \(A\) have common factor \(2\),
so no element of \(A\) satisfies the localized identity (6). For distinct
primes \(p,q\), (8) gives the exact limiting covariance
\[
 \operatorname{Cov}({\mathbf{1}}_{2p\mid n},{\bf1}_{2q\mid n})
 =\frac1{4pq}.                                    \tag{11}
\]
Thus, over a finite prime set \(P\), the off-diagonal covariance sum is
\[
 \frac14\left(
   \left(\sum_{p\in P}\frac1p\right)^2
   -\sum_{p\in P}\frac1{p^2}
 \right),                                        \tag{12}
\]
which is unbounded and quadratic in the reciprocal mass.

The aggregate incidence sequence has an equally explicit obstruction:
\[
 f_A(n)=
 \begin{cases}
  0,&n\text{ odd},\\
  \omega(n/2),&n\text{ even}.
 \end{cases}                                      \tag{13}
\]
Therefore
\[
 f_A(n)f_A(n+1)=0\qquad(n\geq1).                 \tag{14}
\]
The means of \(f_A(n)\) and \(f_A(n+1)\) on \([1,X]\) both tend to
infinity, by divergence of \(\sum_p1/p\). Their centered consecutive
correlation is consequently the negative product of these means and tends
to \(-\infty\). Reciprocal divergence is compatible with maximal
dependence, not with the decoupling package in Theorem 5.1.

## 4. Exact boundary

Equations (6)--(14) rule out a direct replacement of the prime support in
the Tao--Teräväinen proof by an arbitrary reciprocal-divergent set. The
missing assumption is not a stronger lower bound on
\(\sum_{a\in A}1/a\). One needs, separately, localized coprime dilation
parameters, affine-cube supply among those parameters, and a medium/large
atom correlation package strong enough to give (3)--(5).

The set \(2\mathbb P\) is a counterexample to those implications, not a
rational Mersenne subseries. In fact
\[
 \sum_{a\in2\mathbb P}\frac1{2^a-1}
 =\sum_p\frac1{4^p-1},                            \tag{15}
\]
and the source explicitly states that its prime-support method can be
modified to establish the corresponding result for every integer base
\(b\geq2\). Thus the authors identify a base-four route for this particular
series, although Section 5 writes out the details only in base two. What
fails is the proposed support-agnostic inference from reciprocal divergence
to the base-two divisor-incidence hypotheses. No conclusion about the full
dense-support case follows from the paper without a new producer for the
three structural inputs above.
