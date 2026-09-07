# Moving gcd frames defeat a coprime-or-nested-core dichotomy

Let \(A\subseteq\mathbb N\), and write

\[
f_A(n)=\sum_{\substack{a\in A\\a\mid n}}1.
\]

The covariance of the divisibility atoms admits an exact positive
decomposition indexed by their common divisors. This suggests separating a
reciprocal-divergent support into either decorrelated atoms or a persistent
common-divisor branch. The construction below shows that this dichotomy is
false, even after allowing one fixed scaling factor and even after imposing
the no-large-gap inequality forced by a hypothetical rational Mersenne sum.

The covariance may instead move through a sequence of finite, mutually
coprime frames. Every frame carries a fixed amount of reciprocal mass, but no
fixed divisor and no pairwise-coprime extraction retains divergent mass.

The results below are ordinary deductions. The accompanying script checks the
finite identities and representative clique blocks exactly. No rational
Mersenne subseries is constructed.

## 1. The weighted gcd frame

For \(a\ge1\), let \(I_a(n)={\bf1}_{a\mid n}\). Uniform averaging gives

\[
\lim_{X\to\infty}\frac1X\sum_{n\le X}I_a(n)I_b(n)
=\frac1{\operatorname{lcm}(a,b)}.
\]

Hence

\[
\lim_{X\to\infty}\operatorname{Cov}_{n\le X}(I_a,I_b)
=\frac{\gcd(a,b)-1}{ab}.
\tag{1}
\]

The identity

\[
\gcd(a,b)=\sum_{d\mid a,\ d\mid b}\varphi(d)
\tag{2}
\]

turns (1) into a sum of rank-one positive forms.

### Proposition 1 (weighted gcd-frame identity)

Let \(F\subseteq\mathbb N\) be finite and let \(c_a\in\mathbb R\) for
\(a\in F\). Then

\[
\begin{aligned}
&\lim_{X\to\infty}\frac1X\sum_{n\le X}
\left(
\sum_{a\in F}c_a\left(I_a(n)-\frac1a\right)
\right)^2\\
&\qquad=
\sum_{d\ge2}\varphi(d)
\left(
\sum_{\substack{a\in F\\d\mid a}}\frac{c_a}{a}
\right)^2.
\end{aligned}
\tag{3}
\]

Only divisors of members of \(F\) contribute on the right.

### Proof

Expand the square and apply (1). Equations (1)--(2) give

\[
\sum_{a,b\in F}c_ac_b\frac{\gcd(a,b)-1}{ab}
=
\sum_{d\ge2}\varphi(d)
\sum_{\substack{a,b\in F\\d\mid a,\ d\mid b}}
\frac{c_ac_b}{ab}.
\]

The inner double sum is the square in (3). \(\square\)

For nonnegative weights, every common divisor contributes positive covariance.
The formula does not say that one divisor must carry a positive proportion of
the total mass. The frame index \(d\) may change with the scale.

## 2. Prime blocks and semiprime cliques

The reciprocal sum of the primes diverges. Partition a tail of the prime
sequence into consecutive finite blocks

\[
\mathcal P_1,\mathcal P_2,\ldots
\]

as follows. Having chosen the preceding blocks, let \(r_j=\min\mathcal P_j\)
be the next unused prime, and stop the block at the first prime for which

\[
S_j:=\sum_{p\in\mathcal P_j}\frac1p\ge1.
\tag{4}
\]

Minimality gives

\[
1\le S_j\le1+\frac1{r_j}.
\tag{5}
\]

Define the \(j\)-th support block by

\[
A_j=\{pq:p,q\in\mathcal P_j,\ p<q\},
\qquad
A=\bigcup_{j\ge1}A_j.
\tag{6}
\]

Unique factorization makes the blocks \(A_j\) disjoint.

### Theorem 2 (moving-frame counterexample)

The support \(A\) in (6) has all of the following properties.

1. Its reciprocal sum diverges:
   \[
   \sum_{a\in A}\frac1a=\infty.
   \tag{7}
   \]
2. For every \(d>1\), the fiber
   \[
   A(d)=\{a\in A:d\mid a\}
   \tag{8}
   \]
   is finite.
3. Every pairwise-coprime subset \(C\subseteq A\) has
   \[
   \sum_{c\in C}\frac1c<\infty.
   \tag{9}
   \]
4. If \(A=\{a_1<a_2<\cdots\}\), and
   \[
   \mathcal D_m=\operatorname{lcm}_{i\le m}(2^{a_i}-1),
   \tag{10}
   \]
   then
   \[
   a_{m+1}<\log_2\mathcal D_m
   \tag{11}
   \]
   for all sufficiently large \(m\).

Consequently, \(A\) has neither a divergent fixed common-divisor branch nor a
divergent pairwise-coprime subfamily, while its ranks satisfy a stronger
eventual inequality than the rational no-large-gap law.

### Proof of reciprocal divergence

Put \(T_j=\sum_{p\in\mathcal P_j}p^{-2}\). The reciprocal mass of one
semiprime clique is

\[
\sum_{a\in A_j}\frac1a
=\sum_{\substack{p,q\in\mathcal P_j\\p<q}}\frac1{pq}
=\frac{S_j^2-T_j}{2}.
\tag{12}
\]

Since \(p\ge r_j\) in the block,

\[
T_j\le\frac{S_j}{r_j}.
\tag{13}
\]

The numbers \(r_j\) tend to infinity, so (5), (12), and (13) show that the
quantity in (12) tends to \(1/2\). Summing over \(j\) proves (7).

### Proof that no divisor persists

Every member of \(A\) is the product of two primes from one finite block, and
distinct prime blocks are disjoint. If \(A(d)\) is nonempty, every prime
divisor of \(d\) lies in one block \(\mathcal P_j\), and \(A(d)\subseteq A_j\).
The set \(A_j\) is finite. This proves (8).

### Proof that coprime extractions are summable

For a pairwise-coprime set \(C\subseteq A\), the members of
\(C_j=C\cap A_j\) form a matching on the vertex set \(\mathcal P_j\).
For each edge \(pq\),

\[
\frac1{pq}\le\frac12\left(\frac1{p^2}+\frac1{q^2}\right).
\]

No vertex occurs twice in the matching, so

\[
\sum_{c\in C_j}\frac1c
\le\frac12T_j
\le\frac{S_j}{2r_j}.
\tag{14}
\]

At least \(r_j\) primes are required for the sum in (4) to reach \(1\),
because every summand is at most \(1/r_j\). Distinct primes are distinct
integers, and hence

\[
r_{j+1}\ge2r_j.
\tag{15}
\]

Equations (5), (14), and (15) show that
\(\sum_j\sum_{c\in C_j}1/c\) converges. This proves (9).

### Proof of the no-large-gap inequality

We use the standard consequence of the prime number theorem that the ratio of
consecutive primes tends to \(1\). It implies that consecutive elements of
the ordered set \(A\) also have ratio tending to \(1\).

Indeed, let \(pq\in A_j\), \(p<q\), and suppose first that \(q\) is not the
largest prime of \(\mathcal P_j\). Replacing \(q\) by the next prime gives a
larger member of \(A_j\) with ratio tending uniformly to \(1\). If \(q\) is
the largest prime but \(p\) is not the preceding prime, replace \(p\)
instead. At the maximum element of \(A_j\), use the product of the first two
primes of \(\mathcal P_{j+1}\). The boundary ratio also tends to \(1\).
Thus

\[
\frac{a_{m+1}}{a_m}\longrightarrow1.
\tag{16}
\]

For consecutive exponents \(a_{m-1},a_m\), put
\(g_m=\gcd(a_{m-1},a_m)\). Within one block, the gcd is either \(1\) or
one prime, and the complementary prime factor tends to infinity. Across two
blocks the gcd is \(1\). Therefore

\[
g_m=o(a_m).
\tag{17}
\]

The Mersenne gcd identity gives

\[
\gcd(2^u-1,2^v-1)=2^{\gcd(u,v)}-1.
\]

Since the two-term least common multiple divides \(\mathcal D_m\),

\[
\begin{aligned}
\log_2\mathcal D_m
&\ge
\log_2\operatorname{lcm}(2^{a_{m-1}}-1,2^{a_m}-1)\\
&>
a_{m-1}+a_m-g_m-2.
\end{aligned}
\tag{18}
\]

Equations (16)--(18) give

\[
\log_2\mathcal D_m\ge(2-o(1))a_m,
\]

whereas \(a_{m+1}=(1+o(1))a_m\). This proves (11). \(\square\)

## 3. Where the covariance is stored

Take unit weights on one block \(A_j\). For a vertex prime
\(p\in\mathcal P_j\), the \(p\)-frame coefficient in (3) is

\[
\sum_{\substack{a\in A_j\\p\mid a}}\frac1a
=\frac1p\left(S_j-\frac1p\right).
\tag{19}
\]

Its contribution to the right side of (3) is

\[
(p-1)\frac1{p^2}
\left(S_j-\frac1p\right)^2.
\tag{20}
\]

For all sufficiently large \(j\), equations (4)--(5) give

\[
\sum_{p\in\mathcal P_j}
(p-1)\frac1{p^2}
\left(S_j-\frac1p\right)^2
\ge\frac18.
\tag{21}
\]

Thus every block carries a fixed amount of positive covariance energy. The
frame primes are new in every block, so no single frame recurs infinitely
often. The reciprocal divergence is stored in moving finite covariance
cliques.

This is the obstruction missed by a coprime-or-nested-core dichotomy. The
first branch asks a matching to retain the mass of a complete weighted graph;
(14) shows that every such matching is summable. The second branch asks one
vertex, or a nested sequence of persistent divisors, to retain the mass;
(8) shows that every vertex occurs at only one finite scale.

## 4. Stress tests

The support \(2\mathbb P\) lies in a fixed-core branch: every exponent has
the common factor \(2\), and division by \(2\) leaves the primes. The full
semiprime layer also has persistent branches, since for each fixed prime \(p\)
the elements \(pq\) carry divergent reciprocal mass as \(q\) varies. The
construction (6) is a thinning of the semiprime layer which preserves total
divergent mass while making every fixed prime star finite.

A nested primorial chain has persistent divisors. The burst-and-escape support
treated by the existing denominator-tail argument instead violates the
no-large-gap law. The moving-clique support does neither: its prime frames are
disjoint, and (11) excludes rank escape as an explanation.

The LCM-free constructions named in the proposed dichotomy are not needed for
this counterexample. Each finite block in (6) is deliberately rich in
common-divisor patterns. Thus the universal dichotomy already fails in a
pattern-rich class. Restricting one branch to LCM-free or sunflower-free
supports cannot repair a statement asserted for every reciprocal-divergent
support.

## 5. Consequence for the dense-support attack

For a fixed integer \(g\ge1\), suppose that \(gB\subseteq A\) and that the
elements of \(B\) are pairwise coprime. If \(g>1\), then \(gB\subseteq A(g)\)
is finite by (8). If \(g=1\), equation (9) shows that
\(\sum_{b\in B}1/b<\infty\). Hence no fixed-core scaling of \(A\) supplies
divergent decorrelated dilation mass.

The other proposed alternative also fails: there is no nontrivial divisor
with an infinite fiber, and hence no nested common-divisor branch. Equation
(11) shows that the failure cannot be converted into a denominator-tail
contradiction by the rational no-large-gap law.

The gcd-frame identity remains exact, but it has a third regime. Divergent
reciprocal mass can move through finite frames whose individual matching
capacity is summable and whose divisor labels never persist. Any analytic use
of (3) must therefore control moving frame energy directly. A fixed-core
Tao--Teräväinen reduction and a nested-divisor rank argument do not exhaust
the dense-support case.
