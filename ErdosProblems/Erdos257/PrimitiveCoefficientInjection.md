# A primitive-coefficient comparison at the first collision

For coprime positive integers $a,b$, put

\[
 c_{a,b}(N)=\#\{(p,q)\in\mathbb N_{>0}^2:
                  (p,q)=1,\ ap+bq=N\}.
\]

The comparison observed at the first collision is valid at every rank.

## 1. The comparison theorem

**Theorem.** For every positive integer $N$,
\[
                 c_{2,11}(N)\geq c_{10,11}(N).       \tag{1}
\]

The proof uses reduced residues. Suppose that $as-br=1$, and define
$k=rp+sq$. The matrix
\[
 \begin{pmatrix}a&b\\r&s\end{pmatrix}
\]
is unimodular, with inverse formulas
\[
 p=sN-bk,\qquad q=ak-rN.
\]
It follows that $(p,q)=1$ if and only if $(N,k)=1$. Positivity gives
\[
 c_{a,b}(N)
 =\#\left\{k\in\mathbb Z:
       \frac{rN}{a}<k<\frac{sN}{b},\ (k,N)=1\right\}.       \tag{2}
\]
For $(a,b)=(2,11)$, take $(r,s)=(1,6)$. For
$(a,b)=(10,11)$, take $(r,s)=(9,10)$. Thus the two intervals in (2) are
\[
 I_N=\left(\frac N2,\frac{6N}{11}\right),\qquad
 J_N=\left(\frac{9N}{10},\frac{10N}{11}\right).     \tag{3}
\]

If $5\nmid N$, multiplication by $5$, reduced modulo $N$, gives the
injection
\[
             k\longmapsto 5k-4N,\qquad J_N\longrightarrow I_N. \tag{4}
\]
If $25\mid N$, write $N=5m$. The map
\[
             k\longmapsto k-2m                                  \tag{5}
\]
also sends the reduced residues in $J_N$ injectively into those in $I_N$.
Indeed its image lies in $(N/2,28N/55)$, it is coprime to $m$, and
reduction modulo $5$ is unchanged because $5\mid m$.

It remains to consider $N=5m$ with $5\nmid m$. Every primitive solution of
\[
             10p+11q=5m
\]
has $q=5q'$ and $5\nmid p$. Division by $5$ therefore injects these
solutions into the primitive solutions of $2p+11q'=m$. It is enough to
prove
\[
                 c_{2,11}(5m)\geq c_{2,11}(m).        \tag{6}
\]

Write $U(t)=c_{2,11}(t)$. Formula (2) and Möbius inversion give the standard
estimate
\[
 \left|U(t)-\frac{\varphi(t)}{22}\right|
       \leq 2^{\omega(t)},                            \tag{7}
\]
because the number of integers in an open interval differs from its length
by at most one. Since $5\nmid m$, equations (7) and
$\varphi(5m)=4\varphi(m)$ give
\[
 U(5m)-U(m)
 \geq \frac{3\varphi(m)}{22}-3\,2^{\omega(m)}.        \tag{8}
\]
Consequently (6) holds whenever
$\varphi(m)/2^{\omega(m)}\geq22$.

For completeness, the complementary finite classification is as follows.
The product formula
\[
 \frac{\varphi(m)}{2^{\omega(m)}}
 =\prod_{p^e\parallel m}\frac{p^{e-1}(p-1)}2          \tag{9}
\]
shows that, when $5\nmid m$, a value below $22$ has no prime divisor larger
than $83$. Multiplying the factors in (9) until their product reaches $22$
gives the following maximum $m$, grouped by its largest prime divisor:

\[
\begin{array}{c|rrrrrrrrrrrr}
p&2&3&7&11&13&17&19&23&29&31&37&41\\
\hline
\max m&64&216&588&924&1092&1122&798&966&1218&372&444&492
\end{array}
\]
\[
\begin{array}{c|rrrrrrrrrrr}
p&43&47&53&59&61&67&71&73&79&83\\
\hline
\max m&516&282&318&354&366&402&426&438&474&498.
\end{array}
\]
In particular $m\leq1218$. Direct enumeration of the reduced residues in
(3) verifies (6) for $m\leq1218$, $5\nmid m$. The theorem
`primitive211IntervalCount_scale_five_small` in
`PrimitiveCoefficientInjectionFinite.lean` certifies this finite residue
count. This is the finite part of the proof, rather than evidence for an
unbounded extrapolation. The script
`scripts/primitive_coefficient_injection.py` independently performs both the
exact factor classification and the enumeration. Equations (4)--(9) then
prove (1) for every $N$.

## 2. The first carry tax

At the first collision, the two stop-$11$ cylinders are $M(8,3)$ and
$M(2,9)$. Their four children are
\[
 M(8,11),\quad M(11,3),\quad M(2,11),\quad M(11,9),
\]
and the one-step carry tax is $M(10,11)$. Theorem (1) implies
coefficientwise that
\[
 \operatorname{Prim}\bigl(M(8,11)+M(11,3)+M(2,11)+M(11,9)\bigr)
 \geq \operatorname{Prim}\bigl(M(10,11)\bigr).       \tag{10}
\]
Thus the first carry has a positive primitive Mersenne expansion without an
LCM lift. Its first possible rank is $13$, strictly after the emitted atom
$w_{10}$. The coefficients in this expansion are nonnegative integers, not
necessarily Boolean.

## 3. Failure of universal packet domination

The analogue of (10) for arbitrary same-stop pairs is false. For a child
cylinder $M(e,n)$, its coefficient at the first tax rank $2n-1$ is
\[
 c_{e,n}(2n-1)
 =\begin{cases}1,&e\mid n-1,\\0,&e\nmid n-1.\end{cases}              \tag{11}
\]
Indeed the second primitive coordinate must equal $1$, after which the
first coordinate is $(n-1)/e$. The same statement holds for $M(n,e)$.
The tax cylinder always has
\[
                         c_{n-1,n}(2n-1)=1.           \tag{12}
\]
Hence coefficientwise payment of even the first tax coefficient requires
one endpoint in the child packet to divide $n-1$.

At stop $20$, the root tree has exactly the two cylinders $M(11,9)$ and
$M(17,3)$. Their child packet is
\[
 M(11,20)+M(20,9)+M(17,20)+M(20,3).
\]
None of $11,9,17,3$ divides $19$. At rank $39$, therefore, all four child
coefficients vanish while
\[
                         c_{19,20}(39)=1.             \tag{13}
\]
This is an exact counterexample to the proposed universal child-packet
domination. Stop $17$ already has a failing pair, $(14,3),(12,5)$, at rank
$33$, but a different pairing using the third stop-$17$ cylinder remains
available. Stop $20$ is the first displayed case in which the same-stop pair
is unique, so pairing cannot repair the missing divisor of $n-1$.

The first collision succeeds for the same structural reason: its endpoint
$2$ divides $10$, and Theorem (1) proves that the resulting child $M(2,11)$
pays every later primitive coefficient of $M(10,11)$, not only the first
one. At stop $20$ the endpoint-divisibility condition already fails at the
first coefficient. A support-changing operation such as the LCM lift is
therefore unavoidable there if the remainder is required to stay in a
positive cylinder cone.

## 4. Reproduction

Run

```
./repo-python formal_math/erdos257_period_noncollapse/scripts/primitive_coefficient_injection.py --depth 5000
```

The output separates the unbounded argument above from the diagnostic
coefficient scan. It also checks (10) through the requested depth and
verifies the exact stop-$20$, rank-$39$ counterexample.
