<a id="erdos-257-mersenne-support-subseries"></a>

# Irrationality criteria for Lambert subseries

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We prove that if $`E`$ satisfies a finite-prime weighted summability condition at base two and $`V`$ admits a summable positive divisor cover, then $`\sum_{a\in A}(b^a-1)^{-1}`$ is irrational for every infinite $`A\subseteq E\cup V`$ and every integer $`b\ge2`$. The two hereditary support classes are incomparable, each contains supports of divergent reciprocal sum, and their unions can lie in neither class. The proof compares a multiple of the series with an integer and averages the error first over multiples of a modulus and then over dyadic lengths. The second average restores the factor $`1/a`$ that incomplete residue periods lose, and because both criteria run through the same average, a single index makes both errors small at once. Irrationality for arbitrary infinite support at base two remains open.

<a id="sec:problem"></a>

# Introduction

For a set $`A`$ of positive integers and a real number $`b>1`$, write
``` math
X_A(b)=\sum_{a\in A}\frac1{b^a-1}.
```
The series converges by comparison with a geometric series, since $`(b^a-1)^{-1}\le b^{1-a}/(b-1)`$. Erdős proved that the full series $`X_{\mathbb{N}_{>0}}(b)`$ is irrational at every integer base \[erdos1948\], and later obtained the same conclusion for pairwise coprime supports of finite reciprocal sum \[erdos1968, p. 222\]. On that page he remarked that the coprimality assumption could be removed, and gave no details. For arbitrary infinite support in base two the question is Problem #257:

<div id="res:problem" class="problem">

**Problem 1** (Erdős \#257). Is $`X_A(2)`$ irrational for every infinite $`A\subseteq\mathbb{N}_{>0}`$?

</div>

We look for conditions on a support that every infinite subset inherits. The first replaces reciprocal summability by a weight that sees divisibility: for $`a=2^km`$ with $`m`$ odd, it charges $`1/[m(b^{2^k}-1)]`$ where reciprocal summability charges $`1/(2^km)`$, so that a large power of $`2`$ pays for many odd cofactors. More generally, we fix a finite set $`P`$ of primes and write $`h(a)=\prod_{p\in P}p^{v_p(a)}`$ for the *$`P`$-part* of $`a`$, where $`v_p(a)`$ is the exponent of $`p`$ in $`a`$. The prime powers may grow with $`a`$; the set of primes stays fixed.

<div id="res:weighted-support" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#res-weighted-support">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#res-weighted-support-comparator">Comparator</a></p>

**Theorem 2** (a weighted condition on the support). *Let $`b\ge2`$ be an integer, let $`A\subseteq\mathbb{N}_{>0}`$ be infinite, and let $`P`$ be a finite nonempty set of primes. Set $`h(a)=\prod_{p\in P}p^{v_p(a)}`$. If*

<a id="eq:weighted-fixed-base"></a>

``` math
\begin{equation}
\label{eq:weighted-fixed-base}
 W_{b,P}(A):=\sum_{a\in A}
 \frac{h(a)}{a(b^{h(a)}-1)}<\infty,
\end{equation}
```
*then $`X_A(b)`$ is irrational. In particular, the base-two condition*

<a id="eq:weighted-return"></a>

``` math
\begin{equation*}
\label{eq:weighted-return}
 \sum_{a\in A}\frac{h(a)}{a(2^{h(a)}-1)}<\infty
 \tag{W}
\end{equation*}
```
*implies that $`X_A(b)`$ is irrational for every integer $`b\ge2`$. Both conclusions are hereditary under passage to infinite subsets.*

</div>

For an example beyond reciprocal summability, consider the support
``` math
A_\star=\{2^km:k\ge1,\ m\text{ odd},\ m\le2^{2^k}\}.
```
For fixed $`k`$ the odd cofactors have reciprocal sum of order $`2^k`$, so the corresponding terms contribute at least $`1/4`$ to $`\sum_{a\in A_\star}1/a`$ and at most $`2^{1-k}`$ to [\[eq:weighted-return\]](#eq%3Aweighted-return); Section [2](#sec%3Aeight-return-extensions) proves both bounds. Hence every infinite subset of $`A_\star`$ has an irrational value at every integer base, although $`A_\star`$ has divergent reciprocal sum. Since $`h/(2^h-1)\le1`$, the theorem also contains the reciprocal-summable case, and Section [7](#sec%3Areciprocal-support) gives a direct proof of the extension Erdős stated.

The second condition uses the joint divisibility of the exponents: it bounds fractional powers of divisor counts by positive divisor sums (Theorem [3](#thm%3Avariable-fractional-cover)). The two conditions are incomparable, and they combine. If $`E`$ satisfies the base-two weighted condition and $`V`$ has a summable divisor cover, then every infinite subset of $`E\cup V`$ has an irrational sum (Theorem [4](#res%3Amixed-supports)). Since two irrational subseries may add up to a rational number, the proof has to control both errors at the same index. The separating constructions of Proposition [5](#res%3Aweighted-cover-incomparability) produce such a union that lies outside both individual classes (Corollary [6](#res%3Astrict-mixed-supports)). All three criteria are sufficient conditions; none of them characterises the supports in Problem [1](#res%3Aproblem).

Every proof compares a multiple of $`X_A(b)`$ with an integer. For a positive integer $`N`$ we put

<a id="eq:intro-displacement"></a>

``` math
\begin{equation}
 \Delta_{b,A}(N)=\sum_{a\in A}\frac{b^{N\bmod a}-1}{b^a-1}
 =(b^N-1)X_A(b)-J_{b,A}(N),\qquad
 J_{b,A}(N)=\sum_{\substack{a\in A\\a\le N}}
             \sum_{j=1}^{\lfloor N/a\rfloor}b^{N-ja}.
 \label{eq:intro-displacement}\tag{D}
\end{equation}
```
The identity follows on dividing $`N`$ by each $`a`$. At an integer base $`J_{b,A}(N)`$ is an integer, and for infinite $`A`$ the displacement $`\Delta_{b,A}(N)`$ is positive, because some $`a\in A`$ exceeds $`N`$. Hence, if $`X_A(b)=p/q`$ with $`p\in\mathbb Z`$ and $`q\ge1`$ an integer, then $`q\Delta_{b,A}(N)`$ is a positive integer and $`\Delta_{b,A}(N)\ge1/q`$. It therefore suffices to find displacements tending to zero. The displacement is a positive real number and may exceed $`1`$, so it should be distinguished from a fractional part; Erdős also proposed working with fractional parts of powers times the value of the series \[erdos1968, p. 226\].

To make the displacement small we take $`N`$ to be a multiple of a modulus. Divisibility then cancels the finitely many exponents that divide the modulus, and the remaining terms have small means over a complete period when their gcd with the modulus is large. The bound for an incomplete period lacks the factor $`1/a`$, and averaging over dyadic lengths restores it: an exponent enters the truncated error only once the sampled range reaches it, and the reciprocals of the later lengths form a geometric tail bounded by a multiple of $`1/a`$. Exponents beyond the sampled range are estimated separately. Because every bound depends explicitly on the modulus, both criteria can share one average.

Sections [2](#sec%3Aeight-return-extensions)–[4](#sec%3Amixed) prove the three criteria, and Sections [5](#sec%3Acomparison)–[6](#sec%3Amap) separate their support classes and describe the limits of the method. The appendices give the direct proof for reciprocal-summable supports, the exact denominators of finite subseries, and tests for whether a prescribed rational number is a subseries sum; these tests decide neither $`1/2`$ nor $`1/21`$.

<a id="sec:eight-return-extensions"></a>

# Finite averages and the weighted criterion

Fix the integer base $`b`$ and the finite prime set $`P`$. We first estimate averages over the multiples of a fixed modulus $`Q`$ and then choose $`Q`$ to suit the weighted hypothesis. The role of the gcd is already visible at $`b=2`$, $`Q=4`$ and $`a=6`$, where the residues of $`4,8,12`$ modulo $`6`$ are $`4,2,0`$ and
``` math
\frac13\left(\frac{2^4-1}{63}+\frac{2^2-1}{63}+0\right)
 =\frac2{21}\le\frac{2}{6(2^2-1)}=\frac19.
```
The final expression is the mean of $`2^{4m\bmod6}/63`$ over the same period, and if $`6\mid Q`$ the term with exponent $`6`$ vanishes at every multiple of $`Q`$. The proof uses both effects: divisibility removes finitely many exponents, and the gcd estimate bounds the rest.

<div class="proof">

*Proof of Theorem [2](#res%3Aweighted-support).* *The contribution of one exponent.* Put $`d_a(m)=(b^{m\bmod a}-1)/(b^a-1)`$ and $`g=(Q,a)`$, for positive integers $`Q,a,T`$. The residues $`tQ\bmod a`$ run through an orbit of length $`a/g`$, and splitting $`1,\ldots,T`$ into full orbits and a remainder gives

<a id="eq:weighted-finite-orbit"></a>

``` math
\begin{equation}
\label{eq:weighted-finite-orbit}
 \frac1T\sum_{t=1}^T d_a(tQ)
 \le \frac{g}{a(b^g-1)}+\frac1{T(b^g-1)}.
\end{equation}
```
Indeed, after we drop the $`-1`$ in the numerator, each orbit sums to $`\sum_{t=1}^{a/g}b^{tQ\bmod a}/(b^a-1)=1/(b^g-1)`$. The complete orbits give the first term in [\[eq:weighted-finite-orbit\]](#eq%3Aweighted-finite-orbit), and by nonnegativity the remaining indices cost at most one more orbit. The complete-period term is bounded by the weighted summand of the theorem whenever $`g\ge h(a)`$. The modulus chosen below guarantees this for $`h(a)\le H`$, and for larger prime parts it gives a uniform lower bound on $`g`$ instead. Moreover, for $`Y=QT`$,

<a id="eq:weighted-outer-short"></a>

``` math
\begin{equation}
\label{eq:weighted-outer-short}
 \frac1T\sum_{t=1}^T\sum_{\substack{a\in A\\a>Y}}d_a(tQ)
 \le\frac4T,
\end{equation}
```
because $`d_a(tQ)\le2\,2^{tQ-a}`$ when $`a>QT`$ and $`\sum_{t=1}^T2^{tQ-QT}\le2`$.

*Recovering the reciprocal factor.* For each fixed $`a`$ the error in [\[eq:weighted-finite-orbit\]](#eq%3Aweighted-finite-orbit) tends to zero, but it carries no factor $`1/a`$, so its sum over the growing range $`a\le QT`$ is out of reach. We take $`T=2^j`$ and sum over $`j`$ first. A fixed $`a`$ enters the truncated error only when $`2^j\ge a/Q`$, and the reciprocals of those lengths form a geometric tail of sum at most $`2Q/a`$. Thus, for integers $`Q,M\ge1`$ and $`\alpha_a\ge0`$ with $`\sum_a\alpha_a/a<\infty`$,

<a id="eq:weighted-dyadic-short"></a>

``` math
\begin{equation}
\label{eq:weighted-dyadic-short}
 \sum_{j=M}^{2M-1}\frac1{2^j}\sum_{a\le Q2^j}\alpha_a
 \le2Q\sum_{a\ge1}\frac{\alpha_a}{a};
\end{equation}
```
the estimate remains valid if the dyadic lengths start later. After division by $`M`$ the cost $`2Q`$ becomes $`2Q/M`$.

*Choosing the modulus.* Fix $`\varepsilon>0`$. Choose a finite nonempty $`F\subseteq A`$ such that the sum in [\[eq:weighted-fixed-base\]](#eq%3Aweighted-fixed-base) over $`A\setminus F`$ is below $`\varepsilon`$, and let $`L`$ be any fixed positive common multiple of $`F`$. Besides cancelling $`F`$, the modulus should contain every power of a prime in $`P`$ up to a growing threshold $`H`$, and we truncate each prime power separately so that the modulus stays polynomial in $`H`$. With $`p_*=\max P`$ and $`H\ge2p_*`$, set
``` math
Q=L\prod_{p\in P}p^{\lfloor\log_pH\rfloor},\qquad
 G=\left\lfloor\frac H{p_*}\right\rfloor.
```
For $`a\in F`$ the displacement term vanishes, since $`a\mid Q`$. For $`a\notin F`$ with $`h(a)\le H`$ we have $`h(a)\mid Q`$, hence $`(Q,a)\ge h(a)`$, and since $`n/(b^n-1)`$ decreases, the complete-period term in [\[eq:weighted-finite-orbit\]](#eq%3Aweighted-finite-orbit) is at most $`h(a)/[a(b^{h(a)}-1)]`$. These complete-period contributions therefore sum to less than $`\varepsilon`$, and the dyadic estimate will control their incomplete periods.

For $`h(a)>H`$ we have $`(Q,a)\ge G`$ instead. Indeed, if every prime-power component $`p^{v_p(a)}`$ with $`p\in P`$ is at most $`H`$, then $`h(a)\mid Q`$ and $`(Q,a)\ge h(a)>H`$; otherwise some $`p^{v_p(a)}>H`$ contributes $`p^{\lfloor\log_pH\rfloor}>H/p\ge H/p_*\ge G`$ to the gcd. We sum the complete-period bounds over $`a\le QT`$ using $`\sum_{a\le QT}1/a\le1+\log(QT)`$. Since there are at most $`QT`$ incomplete-period terms, each at most $`1/[T(b^G-1)]`$, these exponents contribute at most
``` math
\frac{G(1+\log(QT))+Q}{b^G-1}.
```
*Balancing the two errors.* Since $`T=2^j`$ with $`j<2M`$, increasing $`M`$ lowers the incomplete-period cost $`Q/M`$ and raises the large-gcd cost $`GM/b^G`$. With $`F`$ and $`L`$ fixed, $`Q\le LH^{|P|}`$ is polynomial in $`H`$, while $`G=H/p_*+O(1)`$ grows linearly, so the choice $`M=\lfloor b^{G/2}\rfloor`$ sends both costs to zero. Here $`M`$ counts the scales $`M\le j<2M`$, whose observation lengths are $`2^j`$. We apply [\[eq:weighted-dyadic-short\]](#eq%3Aweighted-dyadic-short) with $`\alpha_a={\bf1}_A(a)/(b^{h(a)}-1)`$, for which $`\sum_a\alpha_a/a\le W_{b,P}(A)`$ because $`h(a)\ge1`$. Together with [\[eq:weighted-outer-short\]](#eq%3Aweighted-outer-short), the preceding estimates give

<a id="eq:weighted-main-bound"></a>

``` math
\begin{equation}
\label{eq:weighted-main-bound}
 \frac1M\sum_{j=M}^{2M-1}\frac1{2^j}
 \sum_{t=1}^{2^j}\Delta_{b,A}(tQ)
 \le \varepsilon+\frac{2QW_{b,P}(A)}M
 +\frac{G(1+\log Q+2M\log2)+Q}{b^G-1}+4\,2^{-M}.
\end{equation}
```
The first two terms account for the complete and incomplete periods of exponents with $`h(a)\le H`$, and the last two for the exponents $`a\le QT`$ with $`h(a)>H`$ and for the tail $`a>QT`$. With $`F`$ and $`L`$ fixed, every term after $`\varepsilon`$ tends to zero as $`H\to\infty`$. The left-hand side is the expectation of $`\Delta_{b,A}(N)`$ when we choose one of the $`M`$ scales uniformly and then one of its $`2^j`$ indices uniformly. Hence, for large $`H`$, some sampled $`N=Qt`$ satisfies $`\Delta_{b,A}(N)<2\varepsilon`$, and since $`\varepsilon`$ is arbitrary this contradicts the lower bound $`1/q`$ forced by rationality. The argument gives no rate of decay in $`N`$. Finally, $`W_{b,P}(A)\le W_{2,P}(A)`$ for $`b\ge2`$, and the weighted sum can only decrease when we pass to a subset. ◻

</div>

Duverney and Tachiya \[duverneytachiya, Section 2, (2.3)–(2.9)\] also bound an average along an arithmetic progression and select an index at which a combined quantity is small; their progression is built by the Chinese remainder theorem. In the proof above, the additional dyadic average is what controls the incomplete-period error while the modulus grows.

<a id="an-example-beyond-reciprocal-summability"></a>

## An example beyond reciprocal summability

For the support from the introduction we compare the two sums layer by layer. Recall that
``` math
A_\star=\{2^k m:k\ge1,\ m\text{ odd},\ m\le2^{2^k}\}.
```
Elements of different layers have different $`2`$-adic valuations, so the layers are disjoint. For $`r\ge2`$ put
``` math
S_r=\sum_{\substack{m\le2^r\\m\text{ odd}}}\frac1m.
```
Each block $`2^j\le m<2^{j+1}`$ with $`1\le j<r`$ contains $`2^{j-1}`$ odd integers, whose reciprocals sum to between $`1/4`$ and $`1/2`$, and including $`m=1`$ we obtain $`r/4\le S_r\le r`$. The reciprocals in the $`k`$th layer therefore sum to $`2^{-k}S_{2^k}\ge1/4`$, and $`\sum_{a\in A_\star}1/a`$ diverges. For $`P=\{2\}`$ the same layer contributes to the weighted sum at most
``` math
\frac{S_{2^k}}{2^{2^k}-1}
 \le\frac{2^k}{2^{2^k}-1}
 \le2^{1-k}.
```
The last bound uses $`2^{2^k}-1\ge2^{2^k-1}`$ and $`2^k\ge2k`$, and summing over $`k`$ proves [\[eq:weighted-return\]](#eq%3Aweighted-return), although the reciprocal sum diverges.

One can also prescribe the sets of primes for which the weighted sum converges. Let $`E`$ be a finite set of primes and let $`\mathcal U`$ be an upward-closed family of subsets of $`E`$ that contains $`E`$ and omits $`\varnothing`$. A finite union of constructions of the kind just described has divergent reciprocal sum, and for every $`b\ge2`$ and every finite prime set $`P`$ its weighted sum $`W_{b,P}`$ is finite exactly when $`P\cap E\in\mathcal U`$. Taking $`P=E`$, we see that every infinite subset has an irrational sum at every integer base. The construction is given in [Section 1.3 of the companion paper](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=record257:witness-rules).

<a id="sec:common-kernel"></a>

# Positive divisor majorants

The weighted criterion treats the exponents one at a time, whereas a divisor cover uses their joint divisibility. To describe it we write the series in terms of its divisor counts:

<a id="eq:incidence"></a>

``` math
\begin{equation}
 c_A(n)=\#\{a\in A:a\mid n\},\qquad
 X_A(b)=\sum_{n\ge1}c_A(n)b^{-n}.
 \label{eq:incidence}
\end{equation}
```
This follows on expanding $`(b^a-1)^{-1}=\sum_{j\ge1}b^{-aj}`$ and interchanging the nonnegative sums. The selector $`\mathbf1_A`$ takes only the values zero and one, whereas $`0\le c_A(n)\le\tau(n)`$, where $`\tau(n)`$ is the number of positive divisors of $`n`$. The $`c_A(n)`$ are power-series coefficients before any carrying, and they may exceed the range of base-$`b`$ digits.

The criteria of Kaneko, Suzuki and Tachiya \[kanekosuzukitachiya, Theorems 1 and 3\] require the nonzero power-series coefficients to be sparse, and sparsity of the selected Lambert denominators does not supply this. For any nonempty $`A`$, the coefficient $`c_A(n)`$ is positive on every multiple of $`\min A`$, so its nonzero positions have positive lower density and violate their support-counting hypotheses. Their criteria therefore do not apply directly to [\[eq:incidence\]](#eq%3Aincidence). The density calculation, and the difference between their remote-tail average and our displacement, appear in [Section 1.2 of the companion paper](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=record257:weighted-proof).

<a id="a-finite-divisor-set-and-the-cover-condition"></a>

## A finite divisor set and the cover condition

For finite $`F\subseteq\mathbb{N}_{>0}`$ write $`f_F(n)=\#\{a\in F:a\mid n\}`$, and consider the four exponents $`F=\{2,6,10,30\}`$. The count vanishes when $`n`$ is odd, and for even $`n`$ each of the primes $`3`$ and $`5`$ that divides $`n`$ doubles it. Thus
``` math
f_F(n)=\mathbf1_{2\mid n}(1+\mathbf1_{3\mid n})(1+\mathbf1_{5\mid n}).
```
For $`0<\alpha\le1`$ put $`z=2^\alpha-1`$. Raising to the power $`\alpha`$ and expanding, we obtain a positive divisor sum:
``` math
f_F(n)^\alpha
 =\mathbf1_{2\mid n}+z\mathbf1_{6\mid n}
  +z\mathbf1_{10\mid n}+z^2\mathbf1_{30\mid n},\qquad
 C=\frac12\left(1+\frac z3\right)\left(1+\frac z5\right).
```
Since $`\mathbf1_{d\mid n}`$ has mean $`1/d`$, the constant $`C`$ is the mean of this expansion, and the same factorisation applies to $`\{qd:d\mid\prod_{p\in P}p\}`$ whenever no prime in $`P`$ divides $`q`$. A small exponent $`\alpha`$ shrinks the coefficients, but the tail estimate then costs $`(2^\alpha-1)^{-1}=1/z`$. The condition below balances these two effects over a sequence of finite sets.

<div id="thm:variable-fractional-cover" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/74163c42aff9214b1199ff9bd5408721b78f0251/lean/ErdosProblems/Erdos257/PaperCompleteR8/PositiveCoverReturn.lean#L241">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#thm-variable-fractional-cover-comparator">Comparator</a></p>

**Theorem 3** (a summable divisor-cover criterion). *For each $`j\ge1`$, let $`F_j\subseteq\mathbb{N}_{>0}`$ be finite, let $`0<\alpha_j\le1`$, and let $`c_{j,d}\ge0`$ satisfy*
``` math
f_{F_j}(n)^{\alpha_j}\le\sum_{d\mid n}c_{j,d}\quad(n\ge1).
```
*Set $`C_j=\sum_{d\ge1}c_{j,d}/d`$. If*

<a id="eq:strengthened-cover"></a>

``` math
\begin{equation*}
 \sum_{j\ge1}\frac{C_j2^{j\alpha_j}}{2^{\alpha_j}-1}<\infty,
 \tag{V}\label{eq:strengthened-cover}
\end{equation*}
```
*then $`X_A(b)`$ is irrational for every infinite $`A\subseteq\bigcup_jF_j`$ and every integer $`b\ge2`$.*

</div>

For example, take $`F_j=\{4^j\}`$, $`\alpha_j=1`$ and $`c_{j,4^j}=1`$, with all other coefficients zero. Then $`C_j=4^{-j}`$, and the cost in [\[eq:strengthened-cover\]](#eq%3Astrengthened-cover) is $`\sum_j2^{-j}`$. Every finite set admits the majorant $`\alpha_j=1`$, $`c_{j,d}=\mathbf1_{F_j}(d)`$, so the whole restriction lies in the summability of the total cost. The covering sets may overlap, and their majorants may use divisors outside them. Section [5](#sec%3Acomparison) gives a necessary condition that holds whatever these choices are.

<a id="a-finite-mean-for-shifted-divisor-tails"></a>

## A finite mean for shifted divisor tails

A divisor majorant turns the tail into a sum of geometric tails, one for each divisor. Indeed, the positive offsets $`r`$ with $`d\mid N+r`$ are $`d-(N\bmod d),2d-(N\bmod d),\ldots`$, so that
``` math
\sum_{\substack{r\ge1\\d\mid N+r}}B^{-r}
 =\frac{B^{N\bmod d}}{B^d-1}.
```
Fractional powers introduce bases $`B=2^\alpha`$ that may be close to $`1`$. The estimate we need must therefore stay uniform after multiplication by $`B-1`$, and it must allow the modulus to grow, since the mixed proof fixes the first covering sets before it enlarges the modulus.

For $`1<B\le2`$, positive integers $`L,d,M`$, and an integer $`R\ge0`$, put
``` math
w_{B,d}(n)=\frac{B^{n\bmod d}}{B^d-1},\qquad
 \mathscr D_{L;R,M}F
 =\frac1M\sum_{k=R}^{R+M-1}\frac1{2^k}
      \sum_{m=1}^{2^k}F(Lm).
```
In words, we choose $`k`$ uniformly from $`R,\ldots,R+M-1`$, then $`m`$ uniformly from $`1,\ldots,2^k`$, and observe $`N=Lm`$. Each scale receives the same weight, and an index $`N`$ observed at several scales collects the sum of their weights.

The finite estimate

<a id="eq:mixed-finite-kernel"></a>

``` math
\begin{equation*}
 \mathscr D_{L;R,M}w_{B,d}
 \le\frac{1+4L/M}{d(B-1)}
 \tag{S}\label{eq:mixed-finite-kernel}
\end{equation*}
```
is uniform as $`B\downarrow1`$ after multiplication by $`B-1`$, where it becomes $`(1+4L/M)/d`$. The factor $`(B-1)^{-1}`$ is the source of the cost $`(2^\alpha-1)^{-1}`$ in [\[eq:strengthened-cover\]](#eq%3Astrengthened-cover). The bound holds for every starting scale $`R`$ and depends on the modulus only through the ratio $`L/M`$, which tends to zero on the scales used in the weighted proof.

To prove [\[eq:mixed-finite-kernel\]](#eq%3Amixed-finite-kernel), fix $`T=2^k`$ and compare $`d`$ with the largest sampled multiple $`LT`$. When $`d\le LT`$, the orbit of $`L`$ modulo $`d`$ has length $`d/g`$, with $`g=(L,d)`$, and total weight $`1/(B^g-1)`$. Splitting the sample into complete cycles (possibly none) and one remaining piece, we obtain
``` math
\frac1T\sum_{m=1}^T w_{B,d}(Lm)
 \le\frac{g}{d(B^g-1)}+\frac1{T(B^g-1)}
 \le\frac1{d(B-1)}+\frac1{T(B-1)}.
```
Over the dyadic lengths with $`d\le L2^k`$, the errors $`1/[T(B-1)]`$ sum to at most $`2L/[d(B-1)]`$. When $`d>2LT`$, we have $`Lm\bmod d=Lm`$ and $`2Lm\le d-1`$, hence $`\sum_{i=0}^{d-1}B^i\ge dB^{(d-1)/2}\ge dB^{Lm}`$, and each term $`w_{B,d}(Lm)`$ is at most $`1/[d(B-1)]`$. For fixed $`d`$, the transition range $`LT<d\le2LT`$ occurs for at most one $`T`$ as $`T`$ doubles, and at that scale geometric summation gives
``` math
\frac1T\sum_{m=1}^T w_{B,d}(Lm)
 =\frac{B^L}{T(B^L-1)}\frac{B^{LT}-1}{B^d-1}
 \le\frac{LB^L}{d(B^L-1)}
 \le\frac{2L}{d(B-1)}.
```
In the first inequality, the convexity of $`x\mapsto B^x-1`$ and its value $`0`$ at the origin bound the ratio by $`LT/d`$; the last uses $`(B^L-1)/(B-1)=\sum_{i=0}^{L-1}B^i\ge B^{L-1}`$ and $`B\le2`$. Before division by $`M`$, the incomplete periods and the possible transition scale together cost at most $`4L/[d(B-1)]`$, and adding the mean term $`1/[d(B-1)]`$ proves [\[eq:mixed-finite-kernel\]](#eq%3Amixed-finite-kernel). Since all terms are nonnegative, we may sum the estimate against any coefficients $`c_d`$ with $`\sum_dc_d/d<\infty`$.

<a id="proof-of-the-cover-criterion"></a>

## Proof of the cover criterion

<div class="proof">

*Proof of Theorem [3](#thm%3Avariable-fractional-cover).* Write $`B_j=2^{\alpha_j}`$ and
``` math
U_j(N)=\sum_{r\ge1}2^{-r}f_{F_j}(N+r),\qquad
 V_j(N)=\sum_{d\ge1}c_{j,d}w_{B_j,d}(N).
```
We must make the tails $`U_j`$ small, and [\[eq:mixed-finite-kernel\]](#eq%3Amixed-finite-kernel) controls the means of the $`V_j`$. Subadditivity of $`x\mapsto x^{\alpha_j}`$ and the divisor majorant connect the two:
``` math
U_j(N)^{\alpha_j}
 \le\sum_{r\ge1}B_j^{-r}f_{F_j}(N+r)^{\alpha_j}
 \le\sum_{d\ge1}c_{j,d}
       \sum_{\substack{r\ge1\\d\mid N+r}}B_j^{-r}
 =V_j(N).
```
For the displacement itself, the geometric-series identity gives
``` math
\Delta_{2,F_j}(N)=U_j(N)-X_{F_j}(2)\le U_j(N).
```
For $`j\le J`$ divisibility will cancel the displacement, so that $`U_j(N)=X_{F_j}(2)`$, and only the tails with $`j>J`$ have to be made small.

Fix $`\varepsilon>0`$ and allot the allowance $`t_j=\varepsilon2^{-j}`$ to the $`j`$th tail, so that the allowances sum to $`\varepsilon`$. Since $`t_j^{-\alpha_j}V_j<1`$ implies $`U_j<t_j`$, this allocation accounts for the factor $`2^{j\alpha_j}`$ in the cover cost. Choose $`J`$ with
``` math
K_J:=\sum_{j>J}\frac{C_jt_j^{-\alpha_j}}{B_j-1}<\frac14.
```
which is possible because $`\varepsilon^{-\alpha_j}\le\max(1,\varepsilon^{-1})`$. Choose $`L`$ divisible by every member of the first $`J`$ finite sets. For every $`R\ge0`$ and $`M\ge4L`$, the estimate [\[eq:mixed-finite-kernel\]](#eq%3Amixed-finite-kernel) bounds the $`\mathscr D_{L;R,M}`$-mean of $`S_J(N):=\sum_{j>J}t_j^{-\alpha_j}V_j(N)`$ by $`(1+4L/M)K_J<1/2`$, so some sample satisfies $`S_J(N)<1`$. This single choice controls all countably many tails at once: each nonnegative summand is below $`1`$, hence $`U_j(N)<t_j`$ for every $`j>J`$. The first $`J`$ sets contribute no displacement, the later sets cover the rest of $`A`$, and overlaps only enlarge the upper bound. Thus
``` math
0<\Delta_{2,A}(N)\le\sum_{j>J}U_j(N)\le\varepsilon.
```
Equation [\[eq:intro-displacement\]](#eq%3Aintro-displacement) therefore excludes rationality at base two. To pass to larger bases, note that for $`0\le r<d`$ the function $`(b^r-1)/(b^d-1)`$ is nonincreasing on $`b>1`$. For $`r>0`$ we cancel $`b-1`$ and write it as $`A(b)/(A(b)+C(b))`$, where $`A(b)=\sum_{i<r}b^i`$ and $`C(b)=\sum_{r\le j<d}b^j`$; its derivative has the sign of $`A'C-AC'=\sum_{i<r\le j<d}(i-j)b^{i+j-1}<0`$. Hence $`\Delta_{b,A}(N)\le\Delta_{2,A}(N)`$ for every real $`b\ge2`$, and when $`b`$ is an integer this contradicts the lower bound that [\[eq:intro-displacement\]](#eq%3Aintro-displacement) gives under rationality. Since any prescribed positive integer may be included as a divisor of $`L`$, the chosen indices can also be taken arbitrarily large. ◻

</div>

The same proof permits any positive weights $`\eta_j`$ with $`\sum_j\eta_j=1`$: we replace $`2^{j\alpha_j}`$ in [\[eq:strengthened-cover\]](#eq%3Astrengthened-cover) by $`\eta_j^{-\alpha_j}`$ and take $`t_j=\varepsilon\eta_j`$. These weights allocate the error allowances and leave the Lambert subseries itself unweighted. The stronger condition $`\sum_jC_j2^{j\alpha_j}2^{\alpha_j}/(2^{\alpha_j}-1)^2<\infty`$ implies [\[eq:strengthened-cover\]](#eq%3Astrengthened-cover), since each of its summands is the corresponding summand of [\[eq:strengthened-cover\]](#eq%3Astrengthened-cover) multiplied by $`2^{\alpha_j}/(2^{\alpha_j}-1)>1`$. That argument compares the two hypotheses for a given cover. After optimisation over all covers, the inclusion of the corresponding support classes is strict, as a [Lean proof](https://github.com/wcook04/plectis-erdos/blob/3973d3b10bce72017b8f60093f0d6c3f4f592d80/lean/ErdosProblems/Erdos257/PaperCompleteR8/AnalyticIncomparability.lean#L41) shows with an explicit infinite squarefree support.

<a id="sec:mixed"></a>

# A common index for the two criteria

Small displacements at unrelated indices give no control of the union, since the two errors must be small at the same index. We therefore put both finite cancellation requirements into one modulus and bound both remaining errors on the same finite distribution. The weighted proof enlarges the modulus, and (S) keeps the cover estimate valid while it does so. We work at base two and pass to larger integer bases by comparing displacements.

<div id="res:mixed-supports" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#res-mixed-supports">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#res-mixed-supports-comparator">Comparator</a></p>

**Theorem 4** (mixed weighted and cover supports). *Let $`E,V\subseteq\mathbb{N}_{>0}`$. Suppose $`E`$ satisfies [\[eq:weighted-return\]](#eq%3Aweighted-return) for a finite nonempty prime set $`P`$, and $`V\subseteq\bigcup_jF_j`$ for finite sets and nonnegative majorants satisfying the hypotheses of Theorem [3](#thm%3Avariable-fractional-cover), with either [\[eq:strengthened-cover\]](#eq%3Astrengthened-cover) or its positive-weight variant. Then $`X_A(b)`$ is irrational for every infinite $`A\subseteq E\cup V`$ and every integer $`b\ge2`$.*

</div>

<div class="proof">

*Proof.* *Fix the finite cancellation requirements.* Fix $`\varepsilon>0`$ and an integer $`N_0\ge1`$, and put $`\rho=\varepsilon/3`$. Use the cover notation $`B_j,U_j,V_j`$ above, with $`\eta_j=2^{-j}`$ in the case [\[eq:strengthened-cover\]](#eq%3Astrengthened-cover). Set $`t_j=\rho\eta_j`$ and choose $`J`$ so that
``` math
K_J=\sum_{j>J}\frac{C_jt_j^{-\alpha_j}}{B_j-1}<\frac1{16}.
```
Choose a finite $`F\subseteq E`$ so that the weighted sum over $`E\setminus F`$ is $`\kappa<\rho/16`$. Let $`L`$ be a positive common multiple of $`N_0`$, of the members of $`F`$, and of the members of the first $`J`$ finite sets. We fix $`J`$, $`F`$ and $`L`$ before choosing any scales, and every later modulus will be a multiple of $`L`$.

*Estimate both errors on one distribution.* With these finite data fixed, we use the base-two choices
``` math
Q=L\prod_{p\in P}p^{\lfloor\log_pH\rfloor},\qquad
 G=\lfloor H/\max P\rfloor,\qquad M=\lfloor2^{G/2}\rfloor.
```
Both estimates use $`\mathscr D_{Q;M,M}`$, in which the scale index $`k`$ runs from $`M`$ to $`2M-1`$ and each observation is $`N=Qm`$. The estimate [\[eq:weighted-main-bound\]](#eq%3Aweighted-main-bound) allows any common multiple of $`F`$ as $`L`$, so it accommodates the extra divisors required by the cover. It also holds for finite or empty $`E`$, since infinitude entered the weighted proof only through the final positive displacement. Consequently
``` math
\mathscr D_{Q;M,M}(\Delta_{2,E}/\rho)<\frac18
```
for sufficiently large $`H`$. On the same finite distribution, (S) and the interchange of nonnegative sums give
``` math
\mathscr D_{Q;M,M}S_J\le(1+4Q/M)K_J<\frac18,
 \qquad S_J=\sum_{j>J}t_j^{-\alpha_j}V_j,
```
because $`Q/M\to0`$.

*Choose the index only after adding the errors.* Adding the two estimates, we obtain
``` math
\mathscr D_{Q;M,M}\bigl(\Delta_{2,E}/\rho+S_J\bigr)<\frac14.
```
This step uses only the linearity of the mean, and requires no independence between the two errors. We choose a sampled $`N=Qm`$ at which the nonnegative sum is less than $`1`$. Then $`\Delta_{2,E}(N)<\rho`$ and every summand of $`S_J(N)`$ is less than $`1`$, so $`U_j^{\alpha_j}\le V_j`$ gives $`U_j(N)<t_j`$ for every $`j>J`$. The displacement terms from the first $`J`$ finite sets vanish, because their exponents divide $`L`$ and hence $`N`$. Therefore
``` math
\Delta_{2,A}(N)\le\Delta_{2,E}(N)+\Delta_{2,V}(N)<2\rho<\varepsilon,
 \qquad N\ge Q\ge L\ge N_0.
```
The inequality remains valid when $`E`$ and $`V`$ overlap, and $`\Delta_{2,A}(N)>0`$ because $`A`$ is infinite. By the comparison $`0<\Delta_{b,A}(N)\le\Delta_{2,A}(N)`$ from the proof of Theorem [3](#thm%3Avariable-fractional-cover), the displacements take arbitrarily small positive values at every integer base, and [\[eq:intro-displacement\]](#eq%3Aintro-displacement) rules out rationality. ◻

</div>

<a id="sec:comparison"></a>

# Comparison of the support classes

Let $`\mathcal W_b`$ consist of supports satisfying the weighted condition at base $`b`$ for some finite nonempty prime set, and let $`\mathcal C`$ consist of supports with a cover satisfying [\[eq:strengthened-cover\]](#eq%3Astrengthened-cover). Membership asks for a single finite prime set, or a single summable cover, that serves the whole support, and the constructions below defeat every such choice.

<div id="res:weighted-cover-incomparability" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#res-weighted-cover-incomparability">Lean</a></p>

**Proposition 5** (incomparable support criteria). *There are infinite positive supports $`E`$ and $`V`$ such that*
``` math
E\in\mathcal W_2,\quad E\notin\mathcal C,\qquad
 V\in\mathcal C,\quad V\notin\mathcal W_b\ (b\ge2),\qquad
 \sum_{a\in V}\frac1a=\infty.
```

</div>

Both constructions are built from blocks $`\{qd:d\mid\prod_{p\in P}p\}`$, arranged with opposite divisibility patterns. In $`E`$, the growing powers $`q=2^k`$ make the weighted sum converge, while the many simultaneous divisors defeat every cover. In $`V`$, pairwise disjoint prime sets force every finite-prime weighted sum to diverge, while fractional powers of the divisor counts keep the cover cost summable.

<a id="a-lower-bound-independent-of-the-cover"></a>

## A lower bound independent of the cover

To exclude every cover at once, we bound the cost of an arbitrary cover from below in terms of finite subsets of the support. For finite $`F`$ let $`\mathbb E_F`$ denote the uniform mean modulo $`\operatorname{lcm}(F)`$, with $`\operatorname{lcm}(\varnothing)=1`$ and $`f_{\varnothing}=0`$. We allow arbitrary weights $`\eta_j>0`$ with $`\sum_j\eta_j=1`$, so that the lower bound also applies to reweighted covers. Set
``` math
K=\sum_j\frac{C_j\eta_j^{-\alpha_j}}{2^{\alpha_j}-1},\qquad
 \Psi(0)=0,\quad
 \Psi(t)=\inf_{0<\alpha\le1}\frac{t^\alpha}{2^\alpha-1}\quad(t\ge1).
```
Here $`K`$ depends on the cover together with its majorants, exponents and weights, whereas $`\Psi`$ minimises over the scalar exponent $`\alpha`$ alone. Writing $`\log^+t=\log\max\{1,t\}`$, we claim that for every finite $`F\subseteq\bigcup_jF_j`$,

<a id="eq:cover-log-obstruction"></a>

``` math
\begin{equation}
 K\ge\mathbb E_F\Psi(f_F)\ge e\,\mathbb E_F\log^+f_F.
 \label{eq:cover-log-obstruction}
\end{equation}
```
Indeed, if $`f_F(n)=t>0`$, coverage gives $`\sum_jf_{F_j}(n)\ge t`$, so some $`j`$ satisfies $`f_{F_j}(n)\ge\eta_jt`$, and multiplying its divisor majorant by $`\eta_j^{-\alpha_j}/(2^{\alpha_j}-1)`$ gives at least $`t^{\alpha_j}/(2^{\alpha_j}-1)\ge\Psi(t)`$. The index $`j`$ may depend on $`n`$, but the sum of all these weighted majorants bounds $`\Psi(f_F(n))`$ at every $`n`$. We average over $`1\le n\le X`$. Each divisor indicator has mean $`\lfloor X/d\rfloor/X\le1/d`$, so the weighted majorants have total mean at most $`K`$, and as $`X\to\infty`$ the mean of $`\Psi(f_F)`$ tends to $`\mathbb E_F\Psi(f_F)`$. This proves the first inequality; only the finitely supported function $`f_F`$ needs a period, and the covering moduli need not divide $`\operatorname{lcm}(F)`$. The second inequality is immediate for $`t=0,1`$, and for $`t>1`$ it follows from $`2^\alpha-1\le\alpha`$ and $`e^u/u\ge e`$ with $`u=\alpha\log t`$.

For the blocks $`\{qd:d\mid\prod_{p\in P}p\}`$, Appendix [11](#app%3Aelementary-details) determines the optimal cost asymptotically, in [\[eq:optimal-cube-cost\]](#eq%3Aoptimal-cube-cost); the separation below needs only [\[eq:cover-log-obstruction\]](#eq%3Acover-log-obstruction).

<a id="two-separating-constructions"></a>

## Two separating constructions

<div class="proof">

*Proof of Proposition [5](#res%3Aweighted-cover-incomparability).* Both constructions use the divergence of the reciprocal sum over odd primes, which persists after finitely many primes are removed. If it converged, $`\prod_{p\text{ odd}}(1+1/p)`$ would bound the reciprocal sum of the odd squarefree integers, and the decomposition $`n=ds^2`$ would then make the odd harmonic series converge.

*A weighted support with no divisor cover.* The $`k`$th group of exponents will carry the factor $`2^k`$. Since the event $`v_2(n)=k`$ has density $`2^{-(k+1)}`$, a prime reciprocal sum of order $`2^k`$ contributes a fixed amount to the mean logarithmic count, and taking its leading constant below $`\log2`$ leaves exponential decay in the weighted sum. Accordingly, choose pairwise disjoint finite sets $`P_k`$ of odd primes such that $`2^k/4\le S_k:=\sum_{p\in P_k}1/p<2^k/4+1`$. Put $`M_k=\prod_{p\in P_k}p`$ and $`E=\bigcup_{k\ge1}\{2^kd:d\mid M_k\}`$. For $`P=\{2\}`$ the weighted sum is
``` math
\sum_{k\ge1}\frac{\prod_{p\in P_k}(1+1/p)}{2^{2^k}-1}
 \le 2e\sum_{k\ge1}
       \exp\bigl(-(\log2-1/4)2^k\bigr)<\infty.
```
For $`F_m=\bigcup_{k=1}^m\{2^kd:d\mid M_k\}`$ we average $`\log^+f_{F_m}`$ over a period, splitting along the disjoint events $`v_2(n)=k<m`$ of density $`2^{-(k+1)}`$. On the $`k`$th event we use only the $`k`$th group, which gives $`f_{F_m}(n)\ge2^{Z_k(n)}`$ with $`Z_k(n)=\sum_{p\in P_k}\mathbf1_{p\mid n}`$. Since divisibility by odd primes is independent of that event,
``` math
\mathbb E_{F_m}\log^+f_{F_m}
 \ge(\log2)\sum_{k=1}^{m-1}2^{-(k+1)}S_k
 \ge\frac{m-1}{8}\log2.
```
By [\[eq:cover-log-obstruction\]](#eq%3Acover-log-obstruction), a cover satisfying [\[eq:strengthened-cover\]](#eq%3Astrengthened-cover) would bound all these means by its fixed cost, which is impossible since they grow with $`m`$. Thus $`E\notin\mathcal C`$.

*A divisor cover with no finite-prime weighted condition.* Inductively choose odd primes $`q_j\ge4^j`$ and pairwise disjoint finite sets $`P_j`$ of odd primes, each time using only primes not used before. We stop each $`P_j`$ at the first prefix with $`R_j:=\prod_{p\in P_j}(1+1/p)\ge q_j`$; the divergence of the prime reciprocal sum permits this, and minimality gives $`q_j\le R_j<4q_j/3`$. Put $`S_j=\sum_{p\in P_j}1/p`$, $`M_j=\prod_{p\in P_j}p`$, and $`V=\bigcup_{j\ge1}F_j`$, where $`F_j=\{q_jd:d\mid M_j\}`$. Each prime divides exponents in at most one of the sets $`F_j`$, and
``` math
\sum_{a\in F_j}\frac1a=\frac{R_j}{q_j}\in[1,4/3).
```
Hence $`\sum_{a\in V}1/a`$ diverges. Given a finite set $`P`$ of primes, every exponent in all but finitely many of the sets $`F_j`$ is coprime to $`\prod_{p\in P}p`$. On each such $`F_j`$ we have $`h_P(a)=1`$, so $`F_j`$ contributes $`R_j/[q_j(b-1)]\ge1/(b-1)`$ to the base-$`b`$ weighted sum. Hence $`V\notin\mathcal W_b`$ for every integer $`b\ge2`$.

It remains to make the whole cover cost summable. The inequalities $`\log(1+x)\ge x-x^2/2`$ and $`\sum_{p\in P_j}p^{-2}\le1`$ give $`S_j\le\log R_j+1/2<\log q_j+1`$. Writing $`z_j=2^{\alpha_j}-1`$, we see that the index weight and the divisor product contribute $`(1+z_j)^j\prod_{p\in P_j}(1+z_j/p)\le\exp(z_j(j+S_j))`$, and we choose $`z_j(j+S_j)=1`$ to keep this factor bounded at the price of the remaining cost $`1/(q_jz_j)`$. Set
``` math
z_j=(j+S_j)^{-1},\qquad
 \alpha_j=\log_2(1+z_j),\qquad
 c_{j,q_jd}=z_j^{\omega(d)}\quad(d\mid M_j),
```
with all other coefficients zero, where $`\omega(d)`$ is the number of prime factors of $`d`$. If $`q_j\mid n`$ and exactly $`Z`$ primes of $`P_j`$ divide $`n`$, the divisor majorant equals $`(1+z_j)^Z=f_{F_j}(n)^{\alpha_j}`$, and if $`q_j\nmid n`$ both sides vanish. The sum defining $`C_j`$ is $`C_j=q_j^{-1}\prod_{p\in P_j}(1+z_j/p)`$, whence
``` math
\frac{C_j2^{j\alpha_j}}{2^{\alpha_j}-1}
 =\frac{(1+z_j)^j}{q_jz_j}
    \prod_{p\in P_j}(1+z_j/p)
 \le\frac{e(j+S_j)}{q_j}
 \le e\bigl((1+\log4)j+1\bigr)4^{-j}.
```
The last step uses the fact that $`(j+\log x+1)/x`$ decreases for $`x\ge4^j`$. The bound is summable in $`j`$ and already includes the factor $`2^{j\alpha_j}`$ required by [\[eq:strengthened-cover\]](#eq%3Astrengthened-cover), so $`V\in\mathcal C`$. ◻

</div>

<a id="a-strict-enlargement-and-finite-unions"></a>

## A strict enlargement and finite unions

The mixed theorem therefore applies to a support that lies outside both individual classes.

<div id="res:strict-mixed-supports" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/74163c42aff9214b1199ff9bd5408721b78f0251/lean/ErdosProblems/Erdos257/PaperCompleteR8/AnalyticIncomparability.lean#L75">Lean</a></p>

**Corollary 6** (a support requiring the mixed criterion). *There is an infinite positive support $`U`$ with $`U\notin\mathcal C`$ and $`U\notin\mathcal W_b`$ for every integer $`b\ge2`$, such that $`X_A(b)`$ is irrational for every infinite $`A\subseteq U`$ and every integer $`b\ge2`$.*

</div>

<div class="proof">

*Proof.* Let $`U=E\cup V`$, with $`E`$ and $`V`$ as in Proposition [5](#res%3Aweighted-cover-incomparability). A cover of $`U`$ is also a cover of $`E`$, and since all summands are nonnegative, convergence of the weighted sum over $`U`$ for some prime set would give convergence of the sum over $`V`$ for the same prime set. Thus $`U`$ belongs to neither individual class, and Theorem [4](#res%3Amixed-supports) gives irrationality for every infinite subset of $`U`$ at every integer base $`b\ge2`$. ◻

</div>

The cover class defined by (V), with its fixed dyadic weights, is closed under finite unions. When two covers are interleaved, the index-dependent factor $`2^{j\alpha_j}`$ has to be controlled, and we do this by placing their $`j`$th finite sets at positions $`2j-1`$ and $`2j`$ and halving each exponent, which keeps the factor from increasing. The old majorant coefficients still work, since $`f^{\alpha/2}\le f^\alpha`$ for every nonnegative integer $`f`$, and it remains to compare the denominators in the cost. If $`T_j=C_j2^{j\alpha_j}/(2^{\alpha_j}-1)`$ denotes the original $`j`$th cost, the new cost is at most
``` math
\frac{C_j2^{j\alpha_j}}{2^{\alpha_j/2}-1}
 =(1+2^{\alpha_j/2})T_j\le(1+\sqrt2)T_j.
```
For $`r`$ covers we interleave at positions at most $`rj`$ and divide each exponent by $`r`$, and the cost ratio is then $`(2^\alpha-1)/(2^{\alpha/r}-1)<2r`$. Weighted supports are closed under finite unions as well: we take the union of their prime sets, which can only increase $`h_P(a)`$, and $`h/(b^h-1)`$ decreases with $`h`$. Since both criteria are hereditary and admit finite supports, the mixed class is closed under finite unions and finite changes, already with the fixed dyadic weights in (V). Countable unions may leave the mixed class: every prime singleton is admitted, yet the full set of primes fails the small-displacement condition, as Section [6](#sec%3Amap) shows. Finally, the reciprocal-summable class is contained in the weighted class, since $`h/(2^h-1)\le1`$, and Appendix [7](#sec%3Areciprocal-support) gives a direct proof for it.

<a id="sec:map"></a>

# Limits of the small-displacement criterion

Small displacement is sufficient for irrationality, and the full support already shows that it is far from necessary:
``` math
\Delta_{2,\mathbb{N}_{>0}}(N)
 >(2^N-1)\sum_{a>N}2^{-a}=1-2^{-N}\ge\frac12
 \qquad(N\ge1).
```
Erdős nevertheless proved the full-support value [irrational](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L8328) \[erdos1948\]. A proof for arbitrary support therefore cannot rely on making these displacements tend to zero in every case, although other uses of the displacement, integer linear forms and averaging arguments remain available.

The set $`\mathcal P`$ of all primes gives a second obstruction. Every prime singleton is admitted by both support criteria, and yet $`\Delta_{2,\mathcal P}(N)>1/3`$ for every $`N\ge1`$. Indeed, writing $`\omega(n)`$ for the number of distinct prime divisors of $`n`$, we have $`\sum_{r\ge1}2^{-r}\omega(N+r)\ge1`$, whereas $`X_{\mathcal P}(2)\le\sum_{a\ge2}(2^a-1)^{-1}<2/3`$.

Tao and Teräväinen nevertheless prove that $`X_{\mathcal P}(2)`$ is irrational \[taoteravainen2025, Theorem 1.3, p. 4\]. The paragraph after their theorem states extensions to prime support at every integer base and to the full set of prime powers at base $`2`$, with the modifications left to the reader; arbitrary infinite sets of primes lie outside its scope. No theorem here assumes such an extension.

The logarithmic lower bound [\[eq:cover-log-obstruction\]](#eq%3Acover-log-obstruction) has no converse of the obvious kind: a logarithmic majorant in place of a fractional one need not control averages along the multiples of a prescribed modulus. The counterexample, and the bound that survives on ordinary initial intervals, are proved in [Section 13 of the companion paper](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=record257:logarithmic-sampling); those proofs were first worked out in an AI-assisted note of 17 September 2026. They concern finite averages only, and leave open an irrationality criterion built on other uses of logarithmic divisor counts.

For squarefree support, irrationality already follows from the theorem of Duverney and Tachiya, at every base $`2^j`$ with $`j\ge1`$, by their Corollary 1.2 and Example 1.1 \[duverneytachiya, p. 4\]. Their corollary covers the $`s`$-free products of any pairwise coprime sequence of polynomial growth, and they present it as support for the conjecture of Erdős and Graham stated here as Problem [1](#res%3Aproblem). For the squarefree support with $`1`$ removed, the divisor count is $`2^{\omega(n)}-1`$, which is odd for $`n\ge2`$; this parity excludes a first-block-divisibility condition at even bases. Adjoining $`1`$ removes the parity obstruction and changes the sum by a rational number, so the obstruction concerns the normalisation of the certificate and says nothing against irrationality of the sum. Details, and the other known support families, appear in [the comparison with known support theorems in the companion paper](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=record257:known-supports).

A criterion based on growth alone gives a different class: if $`A=\{c_1<c_2<\cdots\}`$ and $`\limsup_n c_n/2^n=\infty`$, then $`X_A(b)`$ is irrational for every integer $`b\ge2`$ \[erdos1975, Theorem 1\]. The same section of the companion paper derives this from Erdős’s criterion on denominator growth and gives examples showing that this class and reciprocal summability are incomparable. The interval-filling constructions of \[bkkkz2026\] and the freely chosen lacunary denominators of \[vandoornkovac\] concern sequences other than subseries of the fixed Mersenne weights.

Arguments based on prime incidences need further care: multiplying all prime exponents by $`2`$ creates positive correlations between their divisibility indicators, and size conditions alone cannot restore the independence. The identity and the covariance calculation appear at the end of [the companion paper’s discussion of mixed supports](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=record257:mixed-proof).

<a id="sec:separated-support-transfer"></a>

## Algebraic bases on separated supports

The companion paper [*Reading eight Erdős problems together*](../../../paper/synthesis/optimal-sparse-perturbations.pdf), in its subsection “Divisibility cuts at every algebraic base”, states a transcendence extension based on the number-field Subspace Theorem. Its hypothesis is an infinite set $`H`$ with indices $`L_j<M_j`$, where $`L_j\to\infty`$ and $`M_j-L_j\to\infty`$, such that every $`n\in H`$ with $`n\le L_j`$ divides $`L_j`$ and every $`n\in H`$ with $`n>L_j`$ is a multiple of $`M_j`$. Its stated conclusion is that $`\sum_{n\in B}w_n/(t^n-1)`$ is transcendental for every infinite $`B\subseteq H`$, all bounded positive integer weights $`w_n`$ and every real algebraic $`t>1`$.

Every divisibility chain has such cuts, and so does $`H_* = \bigcup_j N_j\{1,\ldots,2^{N_j}\}`$ with $`N_0=1`$ and $`N_{j+1}=2N_j\operatorname{lcm}(1,\ldots,2^{N_j})`$. Each block of $`H_*`$ has reciprocal sum at least $`1/2`$ and contains antichains of unbounded size, while the weighted sum for one prime is at most $`2t^2/(t-1)^3`$ at every real $`t>1`$. The example thus also satisfies the weighted criterion; we make no claim that every support satisfying that criterion has the separation property.

The companion proof is an ordinary argument outside this paper, with no Lean proof of transcendence, and none of the weighted, cover or mixed theorems depends on it. Irrationality for arbitrary infinite support at base two is the open problem.

<a id="sec:reciprocal-support"></a>

# Reciprocal-summable supports

Erdős stated the following extension of his pairwise-coprime theorem \[erdos1968, p. 222\]. It follows from Theorem [2](#res%3Aweighted-support), since $`h/(2^h-1)\le1`$, but a direct argument shows why reciprocal summability makes the averaging simpler.

<div id="res:reciprocal-support" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/74163c42aff9214b1199ff9bd5408721b78f0251/lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean#L395">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#res-reciprocal-support-comparator">Comparator</a></p>

**Theorem 7** (reciprocal-summable supports). *Let $`A\subseteq\mathbb{N}_{>0}`$ be infinite. If*
``` math
\sum_{a\in A}\frac1a<\infty,
```
*then $`X_A(b)`$ is irrational for every integer $`b\ge2`$.*

</div>

Erdős also discussed weaker conditions \[erdos1968, pp. 222, 226\]; we make no identification of our weighted hypothesis with the conditions he suggested.

Reciprocal summability permits two successive limits. First the observation length grows while the modulus stays fixed, and then the modulus grows until each fixed exponent divides it. The two interchanges of limit and sum use different summable bounds, and neither requires the infinite support to have a period.

Fix the integer base $`b\ge2`$ and put
``` math
w_{b,d}(N)=\frac{b^{N\bmod d}}{b^d-1},\qquad
 T_N^{(b)}=\sum_{d\in A}w_{b,d}(N).
```
Then $`T_N^{(b)}-T_0^{(b)}=\Delta_{b,A}(N)`$. For a fixed positive integer $`Q`$, the orbit of $`Q`$ modulo $`d`$ consists of $`d/g`$ residues, where $`g=(Q,d)`$, and summing the geometric progression gives

<a id="eq:gcd-orbit-mean"></a>

``` math
\begin{equation}
 M_{Q,b}(d):=\lim_{X\to\infty}\frac1X\sum_{m=1}^Xw_{b,d}(Qm)
 =\frac{g}{d(b^g-1)}\le\frac1d.
 \label{eq:gcd-orbit-mean}
\end{equation}
```
In the example $`b=2`$, $`Q=4`$, $`d=6`$ of Section [2](#sec%3Aeight-return-extensions), the mean is $`1/9`$ for $`w_{2,6}`$ and $`2/21`$ for its displacement. When $`d\mid Q`$ we have $`w_{b,d}(Qm)=w_{b,d}(0)`$, and the displacement vanishes.

To interchange the sum over exponents with this limit, we need a bound that is summable in $`d`$ for the fixed modulus $`Q`$. Counting positive multiples of $`d`$ gives
``` math
\begin{align*}
 \frac1X\sum_{m=1}^Xw_{b,d}(Qm)
 &=\sum_{r\ge1}b^{-r}
       \frac{\#\{1\le m\le X:d\mid Qm+r\}}X\\
 &\le\sum_{r\ge1}b^{-r}\frac{Q+r}{d}
 =\frac{Q/(b-1)+b/(b-1)^2}{d}\le\frac{Q+2}{d}.
\end{align*}
```
Indeed, the counted multiples are distinct and at most $`QX+r`$. For this fixed $`Q`$ the majorant $`(Q+2)/d`$ is summable over $`A`$, so dominated convergence takes the limit in the observation length inside the sum over $`d`$ and gives the Cesàro mean $`\sum_{d\in A}M_{Q,b}(d)`$. The majorant deteriorates as $`Q`$ grows, which is why a second limit is needed.

Next let $`Q_t=\operatorname{lcm}(1,\ldots,t)`$. For each fixed $`d`$ we eventually have $`d\mid Q_t`$ and $`M_{Q_t,b}(d)=(b^d-1)^{-1}`$, and a second dominated-convergence argument, now with the bound $`M_{Q_t,b}(d)\le1/d`$, yields

<a id="eq:lcm-prefix-orbit-limit"></a>

``` math
\begin{equation}
 \sum_{d\in A}M_{Q_t,b}(d)\longrightarrow X_A(b).
 \label{eq:lcm-prefix-orbit-limit}
\end{equation}
```
Hence the limiting displacement means tend to zero. We choose $`t`$, then a sufficiently long finite average, and then a term no larger than that average. The resulting arbitrarily small positive displacements contradict the bound $`1/q`$ that [\[eq:intro-displacement\]](#eq%3Aintro-displacement) gives under rationality, and this proves Theorem [7](#res%3Areciprocal-support) at every integer base.

For example, the powerful integers (those whose prime exponents are all at least two) have the form $`u^2v^3`$, so their reciprocal sum is at most $`\zeta(2)\zeta(3)`$, and the theorem applies to every infinite set of powerful integers. For the full set of perfect powers, compare Duverney and Tachiya \[duverneytachiya, Corollary 1.2, p. 4\] and the earlier linear-independence results of Luca and Tachiya \[lucatachiya2014independence\].

<a id="sec:period"></a>

# Finite-support denominator periods

For a finite support, the least common multiple of the selected exponents survives every cancellation: it is the multiplicative order of the base modulo the reduced denominator.

<div id="res:period" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#res-period">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#res-period-comparator">Comparator</a></p>

**Theorem 8** (the exact denominator period). *Let $`F\subseteq\mathbb{N}_{>0}`$ be finite and nonempty, let $`b\ge2`$ be an integer, and let $`D_F>0`$ be the denominator of $`X_F(b)`$ in lowest terms. Then $`D_F`$ is coprime to $`b`$, and*
``` math
\operatorname{ord}_{D_F}(b)=\operatorname{lcm}\{n:n\in F\}.
```
*If moreover $`\operatorname{lcm}(F)\ge2`$, then $`\operatorname{lcm}(F)<D_F`$. We use $`\operatorname{ord}_1(b)=1`$, so the statement includes $`F=\{1\}`$ at $`b=2`$.*

</div>

Put $`L=\operatorname{lcm}(F)`$. Clearing denominators gives $`D_F\mid b^L-1`$, so the order divides $`L`$. For the reverse divisibility, fix a divisibility-maximal $`n\in F`$ with $`n\ge2`$ and choose a prime $`\ell\mid\Phi_n(b)`$. With $`e=v_\ell(b^n-1)`$, the cyclotomic fact in Section [11](#app%3Aelementary-details) gives $`\operatorname{ord}_{\ell^e}(b)=n`$ for the full prime power $`\ell^e`$. Every other selected exponent $`m`$ satisfies $`n\nmid m`$, hence $`v_\ell(b^m-1)<e`$, so the $`n`$th summand has the uniquely smallest $`\ell`$-adic valuation and cannot cancel. Thus $`\ell^e\mid D_F`$ and $`n\mid\operatorname{ord}_{D_F}(b)`$. Running over all maximal selected exponents proves the order statement, and the size bound follows from $`\operatorname{ord}_{D_F}(b)\mid\varphi(D_F)<D_F`$ when $`L\ge2`$. For $`F=\{1\}`$ the order is one directly.

The unique-valuation argument also allows signs $`\pm1`$ on the finite summands; this signed extension lies outside the formal statement. The difference between primes and prime powers is visible in
``` math
X_{\{2,3\}}(2)=\frac{10}{21},\qquad
 X_{\{2,6\}}(2)=\frac{22}{63}.
```
In both examples $`2`$ has multiplicative order six modulo the denominator. The first combines the orders two and three, while the second retains the prime power $`9`$, modulo which $`2`$ has order six, although no prime divisor of $`63`$ has order six. At base two the boundary case $`F=\{1\}`$ has $`D_F=L=1`$. Lower bounds for denominators give no upper control of the heights of infinite partial sums, and so by themselves decide no value of an infinite subseries. Van Assche instead constructs approximants for the full Lambert series and proves both the nonvanishing and the decay of the associated integer linear forms \[vanassche2001, Lemma 1 and (34)–(35)\]; that approximation mechanism requires more than the survival of denominators.

In particular, $`1/21`$ is not a finite subseries sum. If it were, the order of $`2`$ modulo $`21`$ would force every selected exponent to divide $`6`$. The exponent $`1`$ is excluded since its weight is $`1`$, any sum containing $`2`$ or $`3`$ exceeds $`1/21`$, and the only other nonzero sum is $`1/63`$, from the exponent $`6`$. The next appendix uses this to separate finite from infinite representations.

<a id="sec:rational-membership"></a>

# Rational membership

The preceding results start from a support and prove irrationality. We now fix a target value and ask whether some support represents it. The first recurrence below is a necessary condition for a rational value, and the greedy recurrence then gives an exact criterion for membership; neither supplies the arithmetic information still missing for $`1/2`$ and $`1/21`$.

<a id="sec:forced"></a>

## Rational values and scaled tails

Suppose $`X_A(2)=p/v`$, where $`p\in\mathbb{Z}`$ and $`v\ge1`$ is an integer. Multiplying the coefficient-series identity by $`v2^N`$ gives
``` math
z_N:=v\sum_{r\ge1}c_A(N+r)2^{-r}
     =2^Np-v\sum_{n=1}^{N}c_A(n)2^{N-n}\in\mathbb{Z}.
```
Separating the first term of the tail then gives $`z_{N+1}=2z_N-vc_A(N+1)`$, in which every coefficient $`c_A(n)`$ is a divisor count of the same set $`A`$.

For nonempty $`A`$, any $`a_0=\min A`$ consecutive integers contain a multiple of $`a_0`$, so the runs of zeros in $`c_A`$ have length at most $`a_0-1`$. For infinite $`A`$ we choose $`k`$ exponents and a common multiple $`L`$; then $`c_A(L)\ge k`$, and the scaled tail satisfies $`\sum_{r\ge1}c_A(L-1+r)2^{-r}\ge k/2`$. Thus the scaled tails are unbounded.

The compatibility condition on the coefficients is the Dirichlet convolution identity $`\mu*c_A=\mathbf1_A`$, where $`\mu`$ is the Möbius function, so a putative recurrence with integral forcing must satisfy $`(\mu*c_A)(n)\in\{0,1\}`$ for all $`n`$. The telescoping proof of the integer-recurrence criterion and the Möbius inversion argument are given under [Bounds for a general coefficient sequence](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=record257:coefficient-recurrence) in the companion paper, whose example $`A=\{2\}`$ has value $`1/3`$. The correspondence admits finite supports, so a counterexample to Problem [1](#res%3Aproblem) must in addition be infinite.

<a id="sec:geometry"></a>

## The achievement set

Let $`w_n=(2^n-1)^{-1}`$ and
``` math
\mathcal A=\left\{\sum_{n\ge1}\varepsilon_nw_n:
                   \varepsilon_n\in\{0,1\}\right\},\qquad
 R_N=\sum_{n>N}w_n.
```
The estimate
``` math
2^{-N}<R_N\le2^{-N}+\frac23\,4^{-N}<w_N\qquad(N\ge1)
```
follows on writing $`w_n=2^{-n}+4^{-n}/(1-2^{-n})`$, with $`n\ge N+1\ge2`$ for the middle bound. If two selectors first differ at $`n`$, their sums differ by at least $`w_n-R_n>0`$, which proves uniqueness. Since every weight exceeds its tail, Hornich’s theorem \[hornich1941\], as proved by Nitecki \[nitecki2013, Theorem 4(1), p. 9\], shows that $`\mathcal A`$ is a Cantor set of measure $`\lim_N2^NR_N`$, and the estimate above gives $`2^NR_N\to1`$, so $`\lambda(\mathcal A)=1`$. Concretely, fixing the first $`N`$ digits gives $`2^N`$ disjoint closed intervals of length $`R_N`$; these unions decrease to $`\mathcal A`$, and continuity of Lebesgue measure from above gives the same limit. Kovač and Tao record this strict-tail inequality and the Cantor conclusion in the fixed-base setting \[kovactao, Remark 4.1\].

The [geometry section of the companion paper](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=record257:geometry) also treats restricted supports. For any allowed set $`J`$ of exponents, removing exponents can only decrease the tail of each retained weight, so the same inequality gives injectivity. If $`J`$ omits exactly the finite set $`F`$, its achievement set has measure $`2^{-|F|}`$, and if $`J`$ omits infinitely many exponents, the measure is zero.

<a id="sec:actual-repairs"></a>

## The greedy recurrence

For $`x\ge0`$ the greedy rule starts with $`r_0=x`$ and, at each rank $`n\ge1`$, selects $`n`$ when $`r_{n-1}\ge(2^n-1)^{-1}`$, in which case it subtracts that weight. Let $`A_x`$ be the resulting support and $`c_x(n)=\#\{a\in A_x:a\mid n\}`$, and set
``` math
P_0=0,\qquad P_{N+1}=2P_N+c_x(N+1),\qquad
 Q_N=\lfloor2^Nx\rfloor-P_N.
```
Here $`P_N=\sum_{j=1}^N2^{N-j}c_x(j)`$ truncates the coefficient series [\[eq:incidence\]](#eq%3Aincidence), whereas $`r_N`$ truncates the selected Lambert weights: $`Q_N`$ measures the error of coefficient truncation, and $`r_N`$ is the real remainder after $`N`$ greedy decisions. The bound $`P_N\le2^NX_{A_x}(2)\le2^Nx`$ gives $`Q_N\ge0`$, and

<a id="eq:actual-repair-recurrence"></a>

``` math
\begin{equation}
 Q_{N+1}=2Q_N+\beta_N-c_x(N+1),\qquad
 \beta_N=\lfloor2^{N+1}x\rfloor-2\lfloor2^Nx\rfloor\in\{0,1\}.
 \label{eq:actual-repair-recurrence}
\end{equation}
```

The recurrence is integral for every real target. Writing $`\delta=x-X_{A_x}(2)\ge0`$, we obtain from the coefficient expansion
``` math
Q_N=\left\lfloor 2^N\delta+
             \sum_{r\ge1}c_x(N+r)2^{-r}\right\rfloor.
```
For a represented target $`\delta=0`$ and $`Q_N=O(\sqrt N)`$, which leaves too little room for unit increases throughout a long window. For an unrepresented target, $`2^N\delta`$ eventually dominates the divisor count in the recurrence and forces strict increase. The theorem below makes both halves precise.

<div id="res:general-repair" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/74163c42aff9214b1199ff9bd5408721b78f0251/lean/ErdosProblems/Erdos257/PaperCompleteR20/GeneralRepairCorrespondence.lean#L15">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#res-general-repair-comparator">Comparator</a></p>

**Theorem 9** (membership and nonincreasing integer remainders). *For every real $`x\ge0`$, the following are equivalent:*
``` math
\begin{gathered}
 x\in\mathcal A;\\
 \forall K\ge0\ \exists N\ge K:\quad Q_{N+1}\le Q_N;\\
 \forall K\ge0\ \exists N\in[K,K+2\lfloor\sqrt K\rfloor+12):
 \quad Q_{N+1}\le Q_N.
 \end{gathered}
```

</div>

<div class="proof">

*Proof.* For a represented target the remaining sum is at least $`w_n`$ exactly when $`n`$ belongs to the representing support, since $`R_n<w_n`$. Hence the greedy rule recovers that support, and
``` math
0\le Q_N\le\sum_{r\ge1}c_x(N+r)2^{-r}
 \le2\sqrt N+4,
```
since $`c_x(n)\le\tau(n)\le2\sqrt n`$ and $`\sqrt{N+r}\le\sqrt N+\sqrt r\le\sqrt N+r`$. Put $`s=\lfloor\sqrt K\rfloor`$ and $`T=2s+12`$. Strict increase at all $`T`$ steps would give $`Q_{K+T}\ge T`$, but $`K+T<(s+4)^2`$ gives $`Q_{K+T}<2s+12=T`$. This proves the window condition, and hence the cofinal nonincreases.

Conversely, if $`x\notin\mathcal A`$, then $`\delta>0`$ and $`Q_N\ge2^N\delta-1`$, which eventually exceeds $`c_x(N+1)\le N+1`$. Equation [\[eq:actual-repair-recurrence\]](#eq%3Aactual-repair-recurrence) then makes $`Q_N`$ strictly increasing, contradicting the cofinal nonincreases. ◻

</div>

The nonincreases must occur along the target’s own greedy sequence. For $`x=0`$ no exponent is selected and $`Q_N=0`$ at every rank, and every finite subseries sum is likewise represented and satisfies the criterion. The target $`x=3/4`$ lies strictly between $`R_1<2/3`$ and $`w_1=1`$, so it is unrepresented and its integer remainders eventually increase strictly. For $`1/2`$ and $`1/21`$ the theorem leaves open which alternative occurs.

An ordinary extension of the argument, beyond the square-root window proved in Lean, gives a uniform subpower window: for each $`0<\varepsilon<1`$, a window of length $`\lceil C_\varepsilon(K+1)^\varepsilon\rceil`$ suffices for a suitable constant $`C_\varepsilon`$. Indeed, $`\tau(n)\le A_\varepsilon n^\varepsilon`$ gives $`Q_N\le D_\varepsilon(N+1)^\varepsilon`$ for represented targets, where $`D_\varepsilon=A_\varepsilon\sum_{r\ge1}r^\varepsilon2^{-r}`$. Choose $`C_\varepsilon>D_\varepsilon(C_\varepsilon+3)^\varepsilon`$, which is possible because $`\varepsilon<1`$. For $`T=\lceil C_\varepsilon(K+1)^\varepsilon\rceil`$, strict increase at all $`T`$ steps would give
``` math
T\le Q_{K+T}\le D_\varepsilon(K+T+1)^\varepsilon
 \le D_\varepsilon(C_\varepsilon+3)^\varepsilon(K+1)^\varepsilon<T,
```
a contradiction. The converse again follows from exponential growth when $`x`$ is unrepresented. Like the square-root window, the shorter window leaves the membership of any particular target undecided.

At $`x=1/2`$ the digits $`\beta_N`$ vanish for $`N\ge1`$, and at $`x=1/21`$ they are six-periodic. For these two targets the missing arithmetic input is therefore

<a id="eq:actual-selector-obligation"></a>

``` math
\begin{equation}
 \forall K\ \exists N\ge K:\qquad
 c_x(N+1)\ge Q_N+\beta_N,
 \qquad x\in\{1/2,1/21\}.
 \label{eq:actual-selector-obligation}
\end{equation}
```
Here $`Q_N`$ and $`c_x`$ must arise from the same greedy support $`A_x`$. The companion paper keeps counterexamples to fixed-multiplier schedules, with their finite phase masks; they concern those schedules only and decide neither target.

<a id="sec:open"></a>

# Integer quotients, approximation and further questions

We now give two further tests. For $`1/21`$ we compare integer greedy remainders with the real greedy sequence, and for $`1/2`$ we allow arbitrary finite approximating supports. Both tests require suitable data at unbounded depths.

<a id="integer-quotients-for-121."></a>

#### Integer quotients for $`1/21`$.

For $`M,d\ge1`$, set
``` math
q_M(d)=\left\lfloor\frac{2^M}{2^d-1}\right\rfloor,
 \qquad T_M=\left\lfloor\frac{2^M}{21}\right\rfloor.
```
For $`d\ge2`$ the geometric expansion gives $`q_M(d)=\sum_{j=1}^{\lfloor M/d\rfloor}2^{M-jd}`$, because the omitted fraction $`2^{M\bmod d}/(2^d-1)`$ is less than $`1`$; thus $`q_M(d)`$ is the coefficient prefix contributed by the exponent $`d`$. Starting with the remainder $`T_{2R}`$, we run through $`d=2,\ldots,R`$ in order and subtract $`q_{2R}(d)`$ whenever it does not exceed the current remainder. Let $`D_R`$ be the set of selected exponents and $`s_R`$ the final remainder, so that
``` math
s_R=T_{2R}-\sum_{d\in D_R}q_{2R}(d)\ge0.
```
The precision is $`4^R`$, although $`D_R`$ records decisions only through rank $`R`$; the agreement condition below also uses a second run at the same precision, continued through rank $`2R`$. For example, $`R=6`$ gives $`T_{12}=195`$, $`D_6=\{5\}`$ and $`s_6=195-\lfloor4096/31\rfloor=63\le64`$. This single row satisfies the bound in part (2) of the theorem below, and says nothing about whether such rows occur at unbounded depths.

Write $`r_n=r_n(1/21)`$ for the real greedy remainder and $`A_{1/21}`$ for its support. The condition $`\mathcal F_{21}`$ asserts that there are integers $`n,R_0,K_0\ge0`$ with all of the following properties:

1.  $`r_n>R_n`$, the set of positive exponents outside $`A_{1/21}`$ is finite, and every exponent greater than $`n`$ belongs to $`A_{1/21}`$;

2.  for every $`R\ge R_0`$, the integer rule with target $`T_{2R}`$ and weights $`q_{2R}(2),\ldots,q_{2R}(2R)`$ selects exactly the same exponents as the real greedy rule on $`\{2,\ldots,2R\}`$;

3.  for every $`K\ge K_0`$, the interval $`(K,2K]`$ contains an exponent of $`A_{1/21}`$.

A positive limiting remainder gives a tail violation and the eventual selection of every exponent, hence the first and last clauses; the middle clause asks in addition for agreement with the integer rules.

<div id="res:one-over-twenty-one-frontier" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#res-one-over-twenty-one-frontier">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#res-one-over-twenty-one-frontier-comparator">Comparator</a></p>

**Theorem 10** (integer-quotient tests for $`1/21`$). *The following statements hold.*

1.  *$`1/21\in\mathcal A`$ if and only if $`\mathcal F_{21}`$ does not hold.*

2.  *If there is an unbounded sequence of ranks $`R`$ with $`s_R\le 2^R`$, then $`1/21\in\mathcal A`$.*

3.  *On $`\mathcal F_{21}`$, eventually $`s_R>2^R`$, the boundary rank $`R+1`$ belongs to $`D_{R+1}`$, and, for all sufficiently large $`R`$,*
    ``` math
    \begin{aligned}
     D_{R+1}&=D_R\cup\{R+1\},\\
     s_{R+1}&=4s_R+
     \left\lfloor\frac{4(2^{2R}\bmod21)}{21}\right\rfloor
     -2c_{D_R}(2R+1)-c_{D_R}(2R+2)\\
     &\hspace{3em}{}-(2^{R+1}+1).
     \end{aligned}
    ```
    *Here $`c_{D_R}(m)=\#\{d\in D_R:d\mid m\}`$.*

</div>

<div class="proof">

*Proof.* Write $`x=1/21`$, $`G=A_{1/21}`$ and $`\delta=x-X_G(2)\ge0`$. If $`x\notin\mathcal A`$, then $`\delta>0`$, and since the real remainder tends to $`\delta`$, every sufficiently small weight is selected and eventually $`r_n>R_n`$. For the integer comparisons we first choose $`d_0`$ with $`w_d<\delta/2`$ for $`d>d_0`$. The comparisons through $`d_0`$ are strict, since equality would give a finite representation of $`x`$. After division by $`4^R`$, each quotient weight differs from $`w_d`$ by less than $`4^{-R}`$, and the remainders differ by at most $`d/4^R`$ whenever the earlier decisions agree, so for large $`R`$ the first $`d_0`$ decisions agree. At the later ranks $`d\le2R`$ the normalised remainder exceeds $`\delta/2>w_d`$, since $`2R/4^R<\delta/2`$, and both rules select every remaining rank through $`2R`$. This proves $`\mathcal F_{21}`$. A represented target has $`r_n\le R_n`$ at every rank, which gives the converse in (1).

For every $`R`$ the rounding errors satisfy

<a id="eq:twenty-one-rounding"></a>

``` math
\begin{equation}
 \left|x-X_{D_R}(2)-\frac{s_R}{4^R}\right|
 \le\frac{R+1}{4^R}.
 \label{eq:twenty-one-rounding}
\end{equation}
```
Thus $`s_R\le2^R`$ at unbounded ranks gives finite subseries sums tending to $`x`$, and since $`\mathcal A`$ is closed this proves (2), with no compatibility required between the sets $`D_R`$; by Section [8](#sec%3Aperiod) the representation obtained is infinite.

On $`\mathcal F_{21}`$ the eventual agreement gives $`D_R=G\cap\{2,\ldots,R\}`$ and $`D_{R+1}=D_R\cup\{R+1\}`$, and the rounding bound implies $`s_R/4^R\to\delta>0`$. Finally, for $`d\in D_R`$ (so $`d\ge2`$) we use $`q_{M+2}(d)=4q_M(d)+2\mathbf1_{d\mid M+1}+\mathbf1_{d\mid M+2}`$, together with the analogous identity for the target and $`q_{2R+2}(R+1)=2^{R+1}+1`$, to obtain (3). The full comparison induction and both quotient identities are given in [the companion paper’s integer-quotient proof for $`1/21`$](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=record257:twenty-one-quotients). ◻

</div>

In the list $`q_{2R}(2),\ldots,q_{2R}(R)`$ each weight exceeds the sum of its successors by at least $`2^R+1`$, so distinct subset sums are separated by more than $`2^R`$, and the greedy sum is the largest one not exceeding the target. Thus, if $`D\subseteq\{2,\ldots,R\}`$ and an integer $`s`$ satisfy $`\sum_{d\in D}q_{2R}(d)+s=T_{2R}`$ with $`0\le s\le2^R`$, then $`D=D_R`$ and $`s=s_R`$ ([uniqueness of a finite representation with the stated remainder bound](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L231)). Under their alignment hypotheses, the finite crossing lemmas cited below have two further consequences: an earlier finite prefix cannot occur, and a real greedy exponent must be skipped ([the missing-prefix consequence of an aligned crossing](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L5179), [the real greedy skip forced by that crossing](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L5223)).

<a id="approximation-to-12-by-finite-supports."></a>

#### Approximation to $`1/2`$ by finite supports.

For $`A\subseteq\{2,\ldots,M\}`$ and $`1\le m\le M`$, define the integer
``` math
K_A(m)=2^{m-1}-\sum_{j=2}^{m}2^{m-j}c_A(j).
```
It is the error of the truncated divisor-coefficient sum, multiplied by $`2^m`$, and it satisfies $`K_A(1)=1`$ and $`K_A(m+1)=2K_A(m)-c_A(m+1)`$.

<div id="res:terminalhalf" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/74163c42aff9214b1199ff9bd5408721b78f0251/lean/ErdosProblems/Erdos257/PaperCompleteR20/TerminalSetCorrespondence.lean#L185">Lean</a></p>

**Theorem 11** (finite approximations with vanishing scaled error). *Suppose there are integers $`M_j\ge1`$ tending to infinity and sets $`A_j\subseteq\{2,\ldots,M_j\}`$ such that*
``` math
\frac{|K_{A_j}(M_j)|}{2^{M_j}}\longrightarrow0.
```
*Then $`X_A(2)=1/2`$ for some infinite set $`A\subseteq\mathbb{N}_{>0}`$.*

</div>

Only the terminal coefficient error needs control, because the omitted tail obeys the following uniform bound, whatever the supports $`A_j`$ and the earlier values of $`K_{A_j}`$:
``` math
\left|X_{A_j}(2)-\frac12\right|
 \le \frac{|K_{A_j}(M_j)|+2\sqrt{M_j}+4}{2^{M_j}}.
```
Indeed, $`c_{A_j}(n)\le\tau(n)\le2\sqrt n`$ and $`\sqrt{M+r}\le\sqrt M+r`$ bound the normalised tail by $`\sum_{r\ge1}2^{-r}(2\sqrt M+2r)=2\sqrt M+4`$. Thus $`X_{A_j}(2)\to1/2`$, the closedness of $`\mathcal A`$ gives a representing support, and the odd reduced denominators of finite sums make that support infinite. A terminal error of size $`O(\sqrt{M_j})`$ suffices, although the theorem allows any error of size $`o(2^{M_j})`$. For a finite $`D\subseteq\{2,\ldots,M\}`$, the floor-quotient identity gives
``` math
K_D(M)=2^{M-1}-\sum_{d\in D}
                \left\lfloor\frac{2^M}{2^d-1}\right\rfloor.
```
The exact quotient rows considered in the companion paper satisfy $`\sum_{d\in D}q_M(d)=2^{M-1}-1`$, so they have $`K_D(M)=1`$, whereas the terminal criterion allows a larger error of either sign. At a fixed depth these are different conditions, although the cofinal existence of either kind of approximation characterises $`1/2\in\mathcal A`$.

Conversely, if $`X_A(2)=1/2`$, then $`1\notin A`$, and the prefixes $`A_M=A\cap\{2,\ldots,M\}`$ satisfy
``` math
K_{A_M}(M)=\sum_{r\ge1}c_A(M+r)2^{-r}
       \le 2\sqrt M+4.
```
The right-hand side uses the full support $`A`$, since truncation leaves its coefficients through $`M`$ unchanged. Thus the existence hypothesis of Theorem [11](#res%3Aterminalhalf) is equivalent to $`1/2\in\mathcal A`$, and a proof that such approximations exist at unbounded depths would give a negative answer to Problem [1](#res%3Aproblem).

<a id="finite-families-with-a-shared-prefix."></a>

#### Finite families with a shared prefix.

Put $`B(m)=2\lfloor\sqrt m\rfloor+4`$. For $`0\le K\le M`$, consider a family $`A_1,\ldots,A_{B(M)}\subseteq\{2,\ldots,M\}`$ with
``` math
1\le K_{A_k}(m)\le B(m)\quad(1\le m\le M),
 \qquad K_{A_k}(M)=k.
```
Require that all the $`A_k`$ agree on $`\{1,\ldots,K\}`$ and that some integer $`E\ge B(M)`$ satisfies
``` math
\sum_{j=K+1}^{M}1_{A_k}(j)\,2^{M-j}+k=E
 \qquad(1\le k\le B(M)).
```
Thus the binary suffixes take the consecutive values $`E-k`$, and the hypothesis asks for a whole family at each available depth, where Theorem [11](#res%3Aterminalhalf) asks for one approximant.

<div id="res:cylinderhalf" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/74163c42aff9214b1199ff9bd5408721b78f0251/lean/Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L287">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md#res-cylinderhalf-comparator">Comparator</a></p>

**Theorem 12** (unbounded shared-prefix families represent one half). *Suppose that for every $`N`$ there are $`M,K`$ with $`\max\{N,1\}\le M`$, $`0\le K\le M`$, and a family satisfying all the conditions in the preceding paragraph. Then $`X_A(2)=1/2`$ for some infinite set $`A\subseteq\mathbb{N}_{>0}`$.*

</div>

For the proof, choose at each available depth $`M`$ the member with terminal carry $`1`$. Its scaled terminal error is $`2^{-M}`$, so Theorem [11](#res%3Aterminalhalf) applies along unbounded depths; the other shared-prefix conditions play no part in this compactness step. We have no construction of such families at unbounded depths.

The tests above leave three kinds of arithmetic information to be supplied: returns of the actual greedy sequence, finite approximants at unbounded depths, or the exclusion of a possible final skip. The following questions specify these missing inputs.

<div id="prob:one-over-twenty-one-membership" class="problem">

**Problem 13** (membership of 1/21 in the Mersenne achievement set). For the greedy remainder of $`1/21`$, prove that arbitrarily large $`N`$ satisfy
``` math
2^{N+1}r_N(1/21)<\frac{2^{N+1}}{2^{N+1}-1},
 \quad\text{equivalently}\quad
 r_N(1/21)<\frac1{2^{N+1}-1}.
```
Equivalently, exclude the condition $`\mathcal F_{21}`$ defined above. It would suffice to rule out the eventual recurrence in Theorem [10](#res%3Aone-over-twenty-one-frontier)(3) together with $`s_R>2^R`$, or to prove $`s_R\le2^R`$ at arbitrarily large ranks; we do not know whether either of these sufficient conditions is necessary.

</div>

<div id="prob:scaled-return" class="problem">

**Problem 14** (bounded returns of the scaled remainder). For each of the targets $`x=1/2`$ and $`x=1/21`$, does the greedy remainder $`r_N(x)`$ return to one bounded interval after scaling by $`2^N`$?
``` math
\exists B<\infty\ \forall K\ \exists N\ge K:
 \qquad 2^N r_N(x)\le B.
```

</div>

<div id="prob:actual-invariant" class="problem">

**Problem 15** (arithmetic tests for the greedy sequence). Can a finite-memory, $`2`$-adic or discrepancy argument prove $`s_R\le2^R`$ at arbitrarily large ranks, or rule out the eventual recurrence in Theorem [10](#res%3Aone-over-twenty-one-frontier)(3)? Any such argument must use the divisor counts of the actual greedy support. Can a bounded window of data, consisting of $`R\bmod6`$, residues of $`s_R`$, divisor counts at the endpoints and the finite set of eventual skips, force a decrease or a contradiction? Or can one show instead that such bounded-memory data cannot distinguish the actual sequence from sequences that stay above $`2^R`$ without coming from any support?

</div>

<div id="prob:fatal-interval" class="problem">

**Problem 16** (final-skip Diophantine exclusion). Let $`E=\sum_{n\ge1}(2^n-1)^{-1}`$. If $`1/21\notin\mathcal A`$, let $`M`$ be the last skipped exponent, $`S_M`$ its finite skipped prefix, and
``` math
a_M=\frac1{21}+\sum_{d\in S_M}\frac1{2^d-1}.
```
Write $`\operatorname{gap}_M=(2^M-1)^{-1}-R_M>0`$. Can the arithmetic restrictions on this last skipped exponent be used to prove $`|E-a_M|\ge\operatorname{gap}_M`$, which would contradict
``` math
0<a_M-E<\operatorname{gap}_M?
```

</div>

<a id="app:elementary-details"></a>

# Elementary details used in the proofs

<a id="cyclotomic-prime-power-fact."></a>

#### Cyclotomic prime-power fact.

Let $`b\ge2`$, $`n\ge2`$, $`\ell\mid\Phi_n(b)`$ be prime and $`e=v_\ell(b^n-1)`$. Then $`\operatorname{ord}_{\ell^e}(b)=n`$; the statement includes the case $`\ell=2`$. For odd $`\ell`$, put $`d=\operatorname{ord}_{\ell}(b)`$ and $`s=v_\ell(b^d-1)`$. The elementary lifting identity $`v_\ell(b^{dt}-1)=s+v_\ell(t)`$ follows by factoring a geometric sum when $`\ell\nmid t`$ and by a binomial expansion for a factor $`\ell`$. In the factorisation $`b^n-1=\prod_{r\mid n}\Phi_r(b)`$, subtracting these valuations over the proper divisors gives
``` math
v_\ell(\Phi_n(b))=
 \begin{cases}s&n=d,\\1&n=d\ell^j,\ j\ge1,\\0&\text{otherwise.}\end{cases}
```
If $`n=d`$, then $`d`$ is already the least positive exponent with $`b^m\equiv1\pmod\ell`$. If $`n=d\ell^j`$, the full valuation is $`e=s+j`$, and the same lifting identity shows that the least exponent giving valuation $`e`$ is $`d\ell^j=n`$. For $`\ell=2`$ the base $`b`$ is odd, and factoring $`b^{2t}-1`$ gives
``` math
v_2(b^{2^j}-1)=v_2(b-1)+v_2(b+1)+j-1\qquad(j\ge1).
```
The only possible indices $`n\ge2`$ are the powers $`n=2^j`$, with $`v_2(\Phi_2(b))=v_2(b+1)`$ and $`v_2(\Phi_{2^j}(b))=1`$ for $`j\ge2`$, and all other indices have valuation zero. The displayed identity again makes $`2^j`$ the least exponent with the full valuation, which proves the fact. Finally, $`\Phi_n(b)>1`$, so the prime $`\ell`$ exists: each primitive $`n`$th root of unity $`\zeta`$ satisfies $`|b-\zeta|>1`$, and their product is $`\Phi_n(b)`$.

<a id="exact-scalar-cover-cost."></a>

#### Exact scalar cover cost.

For $`t\ge1`$ put $`z=\log_2t`$. The substitution $`y=2^\alpha`$ turns the infimum defining $`\Psi(t)`$ into the infimum of $`y^z/(y-1)`$ over $`1<y\le2`$, whose derivative has the sign of $`(z-1)y-z`$. Hence
``` math
\Psi(t)=
 \begin{cases}t,&1\le t\le4,\\
 z^z/(z-1)^{z-1},&t>4.
 \end{cases}
```
The minimum is attained at $`\alpha=1`$ for $`t\le4`$ and in the interior for $`t>4`$, and the quotient diverges as $`\alpha\downarrow0`$. This scalar identity gives no converse to the positive-cover criterion.

<a id="the-cost-for-a-finite-set-of-divisors"></a>

## The cost for a finite set of divisors

For the following finite divisor sets the lower bound is attained asymptotically. Here $`K_*(F)`$ is the infimum of the cost $`K`$ of Section [5](#sec%3Acomparison) over finite or countable covers of $`F`$, their majorants and exponents, and positive weights of total one; in particular a one-set cover has weight $`1`$ and carries no dyadic index factor as in (V). For $`F(q,P)=\{qd:d\mid\prod_{p\in P}p\}`$, where $`q\ge2`$ and no $`p\in P`$ divides $`q`$, put $`S=\sum_{p\in P}1/p`$. If $`S\ge1`$, then

<a id="eq:optimal-cube-cost"></a>

``` math
\begin{equation}
 \frac{e(S-1)}q\le K_*\bigl(F(q,P)\bigr)\le\frac{eS}q.
 \label{eq:optimal-cube-cost}
\end{equation}
```
For the lower bound we condition on $`q\mid n`$ and write $`f_F(n)=2^Z`$; the Chinese remainder theorem gives $`\mathbb EZ=S`$. For $`z\ge0`$ and $`v=\alpha\log2>0`$,
``` math
\frac{2^{\alpha z}}{2^\alpha-1}
 \ge\frac{e^{(z-1)v}}v\ge e(z-1)\quad(z>1);
```
for $`0\le z\le1`$ the claimed lower bound is nonpositive. Thus $`\Psi(2^z)\ge e(z-1)`$, and averaging and multiplying by the density $`1/q`$ gives the lower bound. For the upper bound we use the one-set cover with $`z=1/S`$ and $`\alpha=\log_2(1+z)`$, whose exact positive expansion has cost
``` math
\frac1{qz}\prod_{p\in P}(1+z/p)\le\frac{eS}q.
```
In particular $`1-1/S\le qK_*(F(q,P))/(eS)\le1`$, so that $`K_*(F(q,P))\sim eS/q`$ as $`S\to\infty`$, uniformly over the permitted choices of $`q`$ and $`P`$.

<a id="app:sources"></a>

# Sources and formal verification

Erdős’s reciprocal-summable extension and his fractional-part argument are on pp. 222 and 226 of \[erdos1968\]. For the periodic theorem of Luca and Tachiya \[lucatachiya2014periodic\] we used their own account \[lucatachiya2017, Theorem A and Example 2, pp. 139–140\], and for Hornich’s strict-tail theorem we used Nitecki’s proof \[nitecki2013, Theorem 4(1)\]; we have not consulted the two original articles. The *Formal Conjectures* file \[formalconjectures257\] gives a Lean statement of Problem [1](#res%3Aproblem), and no proof here depends on it. We make no claim of priority for the comparison of the support classes.

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/dea7b5eba11890a0aaa9cf92f5d334bae4dcd64a/evidence/erdos-257-mersenne-support-subseries.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

Theorem [2](#res%3Aweighted-support) is proved in Lean 4 with Mathlib as the declarations `divisibilityWeightedClaim` and `finitePrimeWeighted_fixedBase_hereditary`, and the mixed theorem has a Lean proof as well; a separate Lean construction of a separating support $`V`$ uses finite sets of squarefree divisors. Among the auxiliary results, Lean proofs are also available for the [finite estimate (S)](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR8/DyadicKernel.lean#L206), the [scalar bound behind [\[eq:cover-log-obstruction\]](#eq%3Acover-log-obstruction)](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR7/CoverKernel.lean#L170), and the [tail comparison](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L30), [injectivity](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L54) and [measure dichotomy](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L397) for achievement sets. The formal proofs establish the stated theorems, and the printed arguments are ordinary proofs written for the reader. The calculation for $`A_\star`$, the construction with fresh primes, Corollary [6](#res%3Astrict-mixed-supports), the signed extension of Theorem [8](#res%3Aperiod) and Theorem [10](#res%3Aone-over-twenty-one-frontier) are proved here by ordinary arguments, and Corollary [6](#res%3Astrict-mixed-supports) also has a Lean proof. The remaining supporting declarations are listed in [the final source section of the companion paper](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=record257:supplementary-sources), grouped by support criteria, finite denominators, integer recurrences and achievement sets.

<div class="thebibliography">

99 D. Duverney and Y. Tachiya, [*Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf), Forum Math. 31 (2019), no. 6, 1557–1566, [DOI](https://doi.org/10.1515/forum-2018-0299). Page numbers refer to the linked author preprint. H. Kaneko, Y. Suzuki, and Y. Tachiya, [*Refinements of Erdős’s irrationality criterion for certain sparse infinite series*](https://arxiv.org/abs/2601.20743v1), arXiv:2601.20743v1 (2026). T. Tao and J. Teräväinen, [*Quantitative correlations and some problems on prime factors of consecutive integers*](https://arxiv.org/abs/2512.01739v2), arXiv:2512.01739v2 (submitted December 2025, revised April 2026). V. Kovač and T. Tao, *On several irrationality problems for Ahmes series*, Acta Math. Hungar. 175 (2025), no. 2, 572–608, [DOI](https://doi.org/10.1007/s10474-025-01528-0). Page numbers refer to arXiv:2406.17593v4. P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. 12 (1948), 63–66. The Formal Conjectures Authors, [*FormalConjectures.ErdosProblems.`257`*](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/257.lean), Lean source file, 2025, accessed 13 September 2026.

P. Erdős, [*On the irrationality of certain series*](https://users.renyi.hu/~p_erdos/1969-09.pdf), Math. Student 36 (1968), 222–226 (issued 1969); [five-page scan](https://www.renyi.hu/~p_erdos/1969-09.pdf). P. Erdős, *Some problems and results on the irrationality of the sum of infinite series*, J. Math. Sci. 10 (1975), 1–7. K. Barreto, J. Kang, S.-H. Kim, V. Kovač, and S. Zhang, [*Irrationality of rapidly converging series: a problem of Erdős and Graham*](https://arxiv.org/abs/2601.21442v3), arXiv:2601.21442v3 (2026), to appear in Bull. London Math. Soc. Z. Nitecki, [*Subsum sets: intervals, Cantor sets, and Cantorvals*](https://arxiv.org/abs/1106.3779v2), arXiv:1106.3779v2 (2013). F. Luca and Y. Tachiya, [*Linear independence results for the values of divisor functions series*](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2014-14.pdf), RIMS Kôkyûroku No. 2014 (2017), 138–150. Theorem A restates their periodic-sequence theorem ([DOI](https://doi.org/10.1142/S1793042113501121)). F. Luca and Y. Tachiya, *Irrationality of Lambert series associated with a periodic sequence*, International Journal of Number Theory **10** (2014), no. 3, 623–636. [doi:10.1142/S1793042113501121](https://doi.org/10.1142/S1793042113501121).

F. Luca and Y. Tachiya, *Linear independence of certain Lambert series*, Proceedings of the American Mathematical Society **142** (2014), no. 10, 3411–3419. [doi:10.1090/S0002-9939-2014-12102-2](https://doi.org/10.1090/S0002-9939-2014-12102-2).

W. Van Assche, *Little $`q`$-Legendre polynomials and irrationality of certain Lambert series*, The Ramanujan Journal **5** (2001), 295–310. [doi:10.1023/A:1012930828917](https://doi.org/10.1023/A:1012930828917); [arXiv:math/0101187v1](https://arxiv.org/abs/math/0101187v1).

H. Hornich, *Über beliebige Teilsummen absolut konvergenter Reihen*, Monatshefte für Mathematik und Physik **49** (1941), 316–320. [doi:10.1007/BF01707309](https://doi.org/10.1007/BF01707309).

W. van Doorn and V. Kovač, *Lacunary sequences whose reciprocal sums represent all rational numbers in an interval*, Acta Arith. 223 (2026), 275–295. [DOI](https://doi.org/10.4064/aa251001-13-1). Page references use <https://arxiv.org/abs/2509.24971v3>.

</div>
