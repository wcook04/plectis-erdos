<a id="erdos-257-mersenne-support-subseries"></a>

# Irrationality criteria for Lambert subseries

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We prove that $`\sum_{a\in A}(b^a-1)^{-1}`$ is irrational for every integer $`b\ge2`$ and every infinite $`A\subseteq E\cup V`$ under two hypotheses. The set $`E`$ satisfies a finite-prime weighted summability condition at base two, while $`V`$ admits a summable positive divisor cover. The two support classes are incomparable, both extend beyond reciprocal-summable supports, and the union criterion reaches supports in neither class. The proof turns on a second average over dyadic lengths: it restores the reciprocal factor lost by incomplete residue periods and, because both estimates use one finite distribution, yields a single index at which both displacements are small. The arbitrary infinite-support problem in base two remains open.

<a id="sec:problem"></a>

# Introduction

For a set $`A`$ of positive integers and a real number $`b>1`$, write
``` math
X_A(b)=\sum_{a\in A}\frac1{b^a-1}.
```
This series converges by comparison with a geometric series, since $`(b^a-1)^{-1}\le b^{1-a}/(b-1)`$. Erdős proved irrationality for full support at integer bases \[erdos1948\], and later proved the same conclusion for pairwise coprime supports of finite reciprocal sum \[erdos1968, p. 222\]. On that page he stated that the coprimality assumption could be removed, without giving the details. The question for arbitrary infinite support in base two is Problem #257:

<div id="res:problem" class="problem">

**Problem 1** (Erdős \#257). Is $`X_A(2)`$ irrational for every infinite $`A\subseteq\mathbb{N}_{>0}`$?

</div>

The conditions below are hereditary: if a set satisfies one of them, so does each of its infinite subsets. For the first condition, consider an exponent $`a=2^km`$ with $`m`$ odd. We replace its reciprocal weight $`1/(2^km)`$ by $`1/[m(b^{2^k}-1)]`$, so that a large power of $`2`$ in $`a`$ reduces its contribution to the sum. More generally, for a finite set $`P`$ of primes, let the *$`P`$-part* of $`a`$ be $`h(a)=\prod_{p\in P}p^{v_p(a)}`$, where $`v_p(a)`$ is the exponent of $`p`$ in $`a`$.

<div id="res:weighted-support" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-257-mersenne-support-subseries.md#res-weighted-support">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-257-mersenne-support-subseries.md#res-weighted-support-comparator">Comparator</a></p>

**Theorem 2** (a weighted condition on the support). *Let $`b\ge2`$ be an integer, let $`A\subseteq\mathbb{N}_{>0}`$ be infinite, and let $`P`$ be a finite nonempty set of primes. Set $`h(a)=\prod_{p\in P}p^{v_p(a)}`$. If
``` math
\begin{equation}
\label{eq:weighted-fixed-base}
 W_{b,P}(A):=\sum_{a\in A}
 \frac{h(a)}{a(b^{h(a)}-1)}<\infty,
\end{equation}
```
then $`X_A(b)`$ is irrational. In particular, the base-two condition
``` math
\begin{equation*}
\label{eq:weighted-return}
 \sum_{a\in A}\frac{h(a)}{a(2^{h(a)}-1)}<\infty
 \tag{W}
\end{equation*}
```
implies that $`X_A(b)`$ is irrational for every integer $`b\ge2`$. Both conclusions are hereditary under passage to infinite subsets.*

</div>

Consider the support
``` math
A_\star=\{2^km:k\ge1,\ m\text{ odd},\ m\le2^{2^k}\}.
```
For a fixed $`k`$, the sum of $`1/m`$ over the odd cofactors is of order $`2^k`$. Thus the corresponding terms contribute at least $`1/4`$ to $`\sum_{a\in A_\star}1/a`$, but at most $`2^{1-k}`$ to <a href="#eq:weighted-return" data-reference-type="eqref" data-reference="eq:weighted-return">[eq:weighted-return]</a>. The calculation in Section <a href="#sec:eight-return-extensions" data-reference-type="ref" data-reference="sec:eight-return-extensions">2</a> proves both bounds. Every infinite subset of $`A_\star`$ consequently gives an irrational value at every integer base. Since $`h/(2^h-1)\le1`$, the same theorem also includes reciprocal-summable supports. Section <a href="#sec:reciprocal-support" data-reference-type="ref" data-reference="sec:reciprocal-support">7</a> gives a direct proof of Erdős’s stated extension.

The divisor-cover condition instead bounds fractional powers of finite divisor counts by positive sums over divisors (Theorem <a href="#thm:variable-fractional-cover" data-reference-type="ref" data-reference="thm:variable-fractional-cover">3</a>). We prove that the two conditions are incomparable and that their union gives a further irrationality criterion: if $`E`$ satisfies the weighted condition and $`V`$ has a summable divisor cover, every infinite subset of $`E\cup V`$ has irrational sum (Theorem <a href="#res:mixed-supports" data-reference-type="ref" data-reference="res:mixed-supports">4</a>). This conclusion is not obtained by adding two separately irrational subseries: their sum could be rational. What combines are the two small-displacement estimates, once both have been placed on the same finite distribution. The separating constructions in Proposition <a href="#res:weighted-cover-incomparability" data-reference-type="ref" data-reference="res:weighted-cover-incomparability">5</a> then give a union outside both individual classes (Corollary <a href="#res:strict-mixed-supports" data-reference-type="ref" data-reference="res:strict-mixed-supports">6</a>). These are sufficient hypotheses for Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a>; the arbitrary support in that problem need not satisfy them.

The proofs compare a multiple of $`X_A(b)`$ with an integer. For a positive integer $`N`$, put
``` math
\begin{equation}
 \Delta_{b,A}(N)=\sum_{a\in A}\frac{b^{N\bmod a}-1}{b^a-1}
 =(b^N-1)X_A(b)-J_{b,A}(N),\qquad
 J_{b,A}(N)=\sum_{\substack{a\in A\\a\le N}}
             \sum_{j=1}^{\lfloor N/a\rfloor}b^{N-ja}.
 \label{eq:intro-displacement}\tag{D}
\end{equation}
```
The identity follows by division of $`N`$ by $`a`$. If $`A`$ is infinite, then $`\Delta_{b,A}(N)>0`$, since some $`a\in A`$ exceeds $`N`$. Suppose that $`b\ge2`$ is an integer and $`X_A(b)=p/q`$, with $`p\in\mathbb Z`$ and $`q\ge1`$ an integer. Then $`q\Delta_{b,A}(N)`$ is a positive integer, and hence $`\Delta_{b,A}(N)\ge1/q`$. To obtain a contradiction, it therefore suffices to make $`\Delta_{b,A}(N)`$ arbitrarily small. Erdős also proposed using fractional parts of powers times the series value \[erdos1968, p. 226\].

We average over multiples of a modulus divisible by a finite subset of $`A`$, whose terms in <a href="#eq:intro-displacement" data-reference-type="eqref" data-reference="eq:intro-displacement">[eq:intro-displacement]</a> then vanish. For each remaining exponent, the mean contribution over a complete residue period is small when its gcd with the modulus is large. The incomplete period causes the difficulty: its bound lacks the factor $`1/a`$ needed to sum over the exponents. A second average, over dyadic lengths, restores this factor. Indeed, an exponent contributes only at lengths that reach it, and the reciprocals of those lengths have a geometrically decreasing sum. Keeping the dependence on the modulus explicit allows both criteria to use the same finite average.

Section <a href="#sec:eight-return-extensions" data-reference-type="ref" data-reference="sec:eight-return-extensions">2</a> proves the weighted estimate. Section <a href="#sec:common-kernel" data-reference-type="ref" data-reference="sec:common-kernel">3</a> introduces divisor covers through a finite example and proves their averaging estimate. Section <a href="#sec:mixed" data-reference-type="ref" data-reference="sec:mixed">4</a> combines the criteria. We construct the separating supports in Section <a href="#sec:comparison" data-reference-type="ref" data-reference="sec:comparison">5</a> and discuss the limits of the argument in Section <a href="#sec:map" data-reference-type="ref" data-reference="sec:map">6</a>. Appendix <a href="#sec:reciprocal-support" data-reference-type="ref" data-reference="sec:reciprocal-support">7</a> gives the direct reciprocal-summable proof, and Appendix <a href="#app:elementary-details" data-reference-type="ref" data-reference="app:elementary-details">8</a> supplies the remaining cover-cost calculation. The [long record](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=scope-finite-periods) develops the separate denominator and rational-membership questions.

<a id="sec:eight-return-extensions"></a>

# Finite averages and the weighted criterion

Fix the integer base $`b`$ and the finite prime set $`P`$. We average $`\Delta_{b,A}`$ over multiples of a modulus $`Q`$. The mean contribution of an exponent $`a`$ depends on $`(Q,a)`$. For example, when $`b=2`$, $`Q=4`$ and $`a=6`$, the residues are $`4,2,0`$, and
``` math
\frac13\left(\frac{2^4-1}{63}+\frac{2^2-1}{63}+0\right)
 =\frac2{21}\le\frac{2}{6(2^2-1)}=\frac19.
```
The final expression is the mean of $`2^{4m\bmod6}/63`$ over the same period. If $`6\mid Q`$, the term with exponent $`6`$ vanishes at every multiple of $`Q`$. In the proof, divisibility removes finitely many exponents, and the gcd estimate bounds the remaining terms.

<div class="proof">

*Proof of Theorem <a href="#res:weighted-support" data-reference-type="ref" data-reference="res:weighted-support">2</a>.* *The contribution of one exponent.* Put $`d_a(m)=(b^{m\bmod a}-1)/(b^a-1)`$ and $`g=(Q,a)`$. For positive integers $`Q,a,T`$, the orbit has length $`a/g`$. Splitting $`1,\ldots,T`$ into full orbits and a remainder gives
``` math
\begin{equation}
\label{eq:weighted-finite-orbit}
 \frac1T\sum_{t=1}^T d_a(tQ)
 \le \frac{g}{a(b^g-1)}+\frac1{T(b^g-1)}.
\end{equation}
```
The sum over one orbit is $`\sum_{t=1}^{a/g}b^{tQ\bmod a}/(b^a-1)=1/(b^g-1)`$. The first term in <a href="#eq:weighted-finite-orbit" data-reference-type="eqref" data-reference="eq:weighted-finite-orbit">[eq:weighted-finite-orbit]</a> accounts for complete orbits; the second allows one extra orbit for the remaining indices. The complete-orbit bound explains the weight in the theorem: replacing $`g`$ by the $`P`$-part $`h(a)`$ gives its summand. The modulus chosen below will permit this replacement for $`h(a)\le H`$; the remaining exponents need a separate estimate. Also, for $`Y=QT`$,
``` math
\begin{equation}
\label{eq:weighted-outer-short}
 \frac1T\sum_{t=1}^T\sum_{\substack{a\in A\\a>Y}}d_a(tQ)
 \le\frac4T,
\end{equation}
```
because $`d_a(tQ)\le2\,2^{tQ-a}`$ when $`a>QT`$ and $`\sum_{t=1}^T2^{tQ-QT}\le2`$.

*Recovering the reciprocal factor.* The error in <a href="#eq:weighted-finite-orbit" data-reference-type="eqref" data-reference="eq:weighted-finite-orbit">[eq:weighted-finite-orbit]</a> tends to zero for each fixed $`a`$, but it has no factor $`1/a`$ to justify summing over the increasing range $`a\le QT`$. We therefore take $`T=2^j`$ and sum first over $`j`$. For a fixed $`a`$, only lengths $`2^j\ge a/Q`$ contribute, and the sum of their reciprocals is at most $`2Q/a`$. Thus, for integers $`Q,M\ge1`$ and $`\alpha_a\ge0`$ with $`\sum_a\alpha_a/a<\infty`$,
``` math
\begin{equation}
\label{eq:weighted-dyadic-short}
 \sum_{j=M}^{2M-1}\frac1{2^j}\sum_{a\le Q2^j}\alpha_a
 \le2Q\sum_{a\ge1}\frac{\alpha_a}{a};
\end{equation}
```
the estimate is unchanged if the available dyadic lengths start later. Dividing by $`M`$ will turn the cost $`2Q`$ into $`2Q/M`$.

*Choosing the modulus.* Fix $`\varepsilon>0`$. Choose finite nonempty $`F\subseteq A`$ so that the sum in <a href="#eq:weighted-fixed-base" data-reference-type="eqref" data-reference="eq:weighted-fixed-base">[eq:weighted-fixed-base]</a> over $`A\setminus F`$ is below $`\varepsilon`$, and let $`L`$ be any fixed positive common multiple of $`F`$. Besides cancelling $`F`$, the modulus should contain every $`P`$-prime power up to a growing threshold $`H`$. Truncating each prime power separately keeps its size polynomial in $`H`$. With $`p_*=\max P`$ and $`H\ge2p_*`$, set
``` math
Q=L\prod_{p\in P}p^{\lfloor\log_pH\rfloor},\qquad
 G=\left\lfloor\frac H{p_*}\right\rfloor.
```
For $`a\in F`$ the displacement term vanishes, since $`a\mid Q`$. For $`a\notin F`$ with $`h(a)\le H`$, we have $`h(a)\mid Q`$ and hence $`(Q,a)\ge h(a)`$. The complete-period term in <a href="#eq:weighted-finite-orbit" data-reference-type="eqref" data-reference="eq:weighted-finite-orbit">[eq:weighted-finite-orbit]</a> is therefore bounded by $`h(a)/[a(b^{h(a)}-1)]`$, using the monotonicity of $`n/(b^n-1)`$. The complete-period contributions therefore sum to less than $`\varepsilon`$. The dyadic estimate will control their incomplete periods.

For $`h(a)>H`$, we instead have $`(Q,a)\ge G`$. Sum the complete-period bounds over $`a\le QT`$, using $`\sum_{a\le QT}1/a\le1+\log(QT)`$. There are at most $`QT`$ incomplete-period terms, each at most $`1/[T(b^G-1)]`$. The total contribution from these exponents is thus at most
``` math
\frac{G(1+\log(QT))+Q}{b^G-1}.
```
For the gcd claim, either every $`P`$-prime-power component of $`h(a)`$ is at most $`H`$, in which case $`h(a)\mid Q`$, or some $`p^{v_p(a)}>H`$ contributes $`p^{\lfloor\log_pH\rfloor}>H/p\ge H/p_*\ge G`$ to the gcd. *Choosing the number of scales.* A longer dyadic average reduces the incomplete-period cost $`Q/M`$. It also increases the largest observation length: since $`T=2^j`$ and $`j<2M`$, the logarithm in the large-gcd bound contributes a term of order $`GM/b^G`$. We must therefore make both $`Q/M`$ and $`GM/b^G`$ tend to zero. With $`F`$ and $`L`$ fixed, $`Q\le LH^{|P|}`$ and $`G=H/p_*+O(1)`$, so the choice $`M=\lfloor b^{G/2}\rfloor`$ lies between the two required scales. Here $`M`$ is the number of dyadic scales, not an observation length. At scale $`j`$, the inner average contains $`T=2^j`$ sampled multiples, with $`M\le j<2M`$. Combining the preceding estimates with <a href="#eq:weighted-outer-short" data-reference-type="eqref" data-reference="eq:weighted-outer-short">[eq:weighted-outer-short]</a>, averaging over $`T=2^j`$ for $`M\le j<2M`$, and using <a href="#eq:weighted-dyadic-short" data-reference-type="eqref" data-reference="eq:weighted-dyadic-short">[eq:weighted-dyadic-short]</a> with $`\alpha_a={\bf1}_A(a)/(b^{h(a)}-1)`$ yields
``` math
\begin{equation}
\label{eq:weighted-main-bound}
 \frac1M\sum_{j=M}^{2M-1}\frac1{2^j}
 \sum_{t=1}^{2^j}\Delta_{b,A}(tQ)
 \le \varepsilon+\frac{2QW_{b,P}(A)}M
 +\frac{G(1+\log Q+2M\log2)+Q}{b^G-1}+4\,2^{-M}.
\end{equation}
```
The four terms respectively bound the weighted tail over complete periods, the incomplete periods, the exponents with large gcd, and the exponents beyond $`QT`$. With $`F`$ and $`L`$ fixed, every term after $`\varepsilon`$ tends to zero as $`H\to\infty`$. The left-hand side is an average with nonnegative weights summing to one: each of the $`M`$ lengths has weight $`1/M`$, distributed uniformly among its $`2^j`$ indices. For large $`H`$, some $`N=Qt`$ therefore satisfies $`\Delta_{b,A}(N)<2\varepsilon`$. This argument gives no rate of decay in $`N`$. Since $`\varepsilon`$ is arbitrary, this contradicts the lower bound $`1/q`$ under rationality. Finally $`W_{b,P}(A)\le W_{2,P}(A)`$ for $`b\ge2`$, and the weighted sum decreases on taking subsets. ◻

</div>

<a id="an-example-beyond-reciprocal-summability"></a>

## An example beyond reciprocal summability

For the support in the introduction, the two sums can be compared layer by layer. Recall that
``` math
A_\star=\{2^k m:k\ge1,\ m\text{ odd},\ m\le2^{2^k}\}.
```
The layers are disjoint, since their elements have different $`2`$-adic valuations. For $`r\ge2`$, put
``` math
S_r=\sum_{\substack{m\le2^r\\m\text{ odd}}}\frac1m.
```
Each block $`2^j\le m<2^{j+1}`$, $`1\le j<r`$, contains $`2^{j-1}`$ odd integers, with reciprocal sum between $`1/4`$ and $`1/2`$. Including $`m=1`$ gives $`r/4\le S_r\le r`$. The sum of reciprocals in the $`k`$th layer is $`2^{-k}S_{2^k}\ge1/4`$, so $`\sum_{a\in A_\star}1/a`$ diverges. For $`P=\{2\}`$, its contribution to the weighted sum satisfies
``` math
\frac{S_{2^k}}{2^{2^k}-1}
 \le\frac{2^k}{2^{2^k}-1}
 \le2^{1-k}.
```
The last bound uses $`2^{2^k}-1\ge2^{2^k-1}`$ and $`2^k\ge2k`$. Summation proves <a href="#eq:weighted-return" data-reference-type="eqref" data-reference="eq:weighted-return">[eq:weighted-return]</a>. The lower bound $`1/4`$ in every layer has already excluded reciprocal summability.

A related selection of a term from an average over an arithmetic progression occurs in Duverney–Tachiya \[duverneytachiya, Section 2, (2.3)–(2.9)\]. In the criteria of Kaneko–Suzuki–Tachiya \[kanekosuzukitachiya, Theorems 1 and 3\], sparsity concerns the positions of nonzero power-series coefficients, not the set of selected Lambert denominators. The divisor counts $`c_A(n)=\#\{a\in A:a\mid n\}`$ are positive on every multiple of $`\min A`$ for nonempty $`A`$, so those criteria do not apply directly. The corresponding density calculation, and the distinction between their remote-tail average and our displacement, are given in [Section 1.2 of the companion paper](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=record257:weighted-proof).

The sets of primes for which the weighted sum converges can also be prescribed. Let $`E`$ be a finite set of primes and let $`\mathcal U`$ be an upward-closed family of subsets of $`E`$ containing $`E`$ but not $`\varnothing`$. A finite union of the constructions just described has divergent reciprocal sum, and, for every $`b\ge2`$ and finite prime set $`P`$, its weighted sum $`W_{b,P}`$ is finite exactly when $`P\cap E\in\mathcal U`$. Taking $`P=E`$ shows that every infinite subset has an irrational sum at every integer base. The construction is given in [Section 1.3 of the companion paper](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=record257:witness-rules).

<a id="sec:common-kernel"></a>

# Positive divisor majorants

The weighted criterion treats exponents individually. A divisor cover can take advantage of correlations between several exponents. The relevant quantity is how many members of a finite set divide the same integer.

We shall also use the divisor counts
``` math
\begin{equation}
 c_A(n)=\#\{a\in A:a\mid n\},\qquad
 X_A(b)=\sum_{n\ge1}c_A(n)b^{-n}.
 \label{eq:incidence}
\end{equation}
```
Expanding $`(b^a-1)^{-1}=\sum_{j\ge1}b^{-aj}`$ and interchanging nonnegative sums gives the identity. Although $`\mathbf1_A`$ takes only the values zero and one, its divisor transform may take larger values, with $`0\le c_A(n)\le\tau(n)`$.

<a id="a-finite-divisor-set-and-the-cover-condition"></a>

## A finite divisor set and the cover condition

For finite $`F\subseteq\mathbb{N}_{>0}`$, write $`f_F(n)=\#\{a\in F:a\mid n\}`$. Consider the four exponents $`F=\{2,6,10,30\}`$. If $`2\nmid n`$, the count is zero. Otherwise each of the primes $`3`$ and $`5`$ that divides $`n`$ doubles the count. Thus
``` math
f_F(n)=\mathbf1_{2\mid n}(1+\mathbf1_{3\mid n})(1+\mathbf1_{5\mid n}).
```
For $`0<\alpha\le1`$, put $`z=2^\alpha-1`$. Taking the fractional power and expanding gives a positive divisor sum:
``` math
f_F(n)^\alpha
 =\mathbf1_{2\mid n}+z\mathbf1_{6\mid n}
  +z\mathbf1_{10\mid n}+z^2\mathbf1_{30\mid n},\qquad
 C=\frac12\left(1+\frac z3\right)\left(1+\frac z5\right).
```
Here $`C`$ is the sum of each coefficient divided by its divisor. These reciprocals are the densities of the divisibility events, so $`C`$ is also the complete-period mean of this majorant. The same expansion applies to $`\{qd:d\mid\prod_{p\in P}p\}`$ when no prime in $`P`$ divides $`q`$.

The fractional power replaces each factor $`2`$ in the divisor count by $`1+z`$. When the set involves many primes and $`\alpha`$ is small, this reduces the coefficients in the positive expansion. The tail estimate below also contains the factor $`(2^\alpha-1)^{-1}=1/z`$, which grows as $`\alpha`$ decreases. The criterion therefore requires summability of the full expression, including this factor, over a sequence of finite sets.

<div id="thm:variable-fractional-cover" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos257/PaperCompleteR8/PositiveCoverReturn.lean#L241">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-257-mersenne-support-subseries.md#thm-variable-fractional-cover-comparator">Comparator</a></p>

**Theorem 3** (a summable divisor-cover criterion). *For each $`j\ge1`$, let $`F_j\subseteq\mathbb{N}_{>0}`$ be finite, let $`0<\alpha_j\le1`$, and let $`c_{j,d}\ge0`$ satisfy
``` math
f_{F_j}(n)^{\alpha_j}\le\sum_{d\mid n}c_{j,d}\quad(n\ge1).
```
Set $`C_j=\sum_{d\ge1}c_{j,d}/d`$. If
``` math
\begin{equation*}
 \sum_{j\ge1}\frac{C_j2^{j\alpha_j}}{2^{\alpha_j}-1}<\infty,
 \tag{V}\label{eq:strengthened-cover}
\end{equation*}
```
then $`X_A(b)`$ is irrational for every infinite $`A\subseteq\bigcup_jF_j`$ and every integer $`b\ge2`$.*

</div>

For example, take $`F_j=\{4^j\}`$, $`\alpha_j=1`$ and $`c_{j,4^j}=1`$, with all other coefficients zero. Then $`C_j=4^{-j}`$, and the cost in <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a> is $`\sum_j2^{-j}`$. A majorant exists for any finite $`F_j`$: the choice $`\alpha_j=1`$ and $`c_{j,d}=\mathbf1_{F_j}(d)`$ suffices. What restricts an infinite support is summability of the entire sequence of costs. Section <a href="#sec:comparison" data-reference-type="ref" data-reference="sec:comparison">5</a> gives a necessary condition that applies to every possible cover.

<a id="a-finite-mean-for-shifted-divisor-tails"></a>

## A finite mean for shifted divisor tails

A divisor majorant becomes a sum of geometric tails, one for each divisor. Indeed, the positive offsets $`r`$ with $`d\mid N+r`$ are $`d-(N\bmod d),2d-(N\bmod d),\ldots`$, so
``` math
\sum_{\substack{r\ge1\\d\mid N+r}}B^{-r}
 =\frac{B^{N\bmod d}}{B^d-1}.
```
Raising a base-two tail to the power $`\alpha`$ replaces its geometric factor by $`B=2^\alpha`$. We therefore need to estimate this expression for $`1<B\le2`$, including $`B`$ close to $`1`$. In the mixed theorem, the weighted construction will choose the modulus and dyadic scales after the finite covering sets have been fixed. The estimate must therefore retain these parameters.

For $`1<B\le2`$, positive integers $`L,d,M`$, and an integer $`R\ge0`$, put
``` math
w_{B,d}(n)=\frac{B^{n\bmod d}}{B^d-1},\qquad
 \mathscr D_{L;R,M}F
 =\frac1M\sum_{j=R}^{R+M-1}\frac1{2^j}
      \sum_{m=1}^{2^j}F(Lm).
```
This is a two-stage average: choose the scale $`j`$ uniformly from $`R,\ldots,R+M-1`$, then choose $`m`$ uniformly from $`1,\ldots,2^j`$ and observe $`N=Lm`$. Each scale receives equal total weight, although the longer scales contain more observations. The same integer $`N`$ can occur at several scales, with its contributions added in the displayed sum.

The finite estimate
``` math
\begin{equation*}
 \mathscr D_{L;R,M}w_{B,d}
 \le\frac{1+4L/M}{d(B-1)}
 \tag{S}\label{eq:mixed-finite-kernel}
\end{equation*}
```
equivalently bounds $`(B-1)\mathscr D_{L;R,M}w_{B,d}`$ by $`(1+4L/M)/d`$. This normalised bound is uniform as $`B\downarrow1`$; the unnormalised right side grows like $`(B-1)^{-1}`$. With $`B=2^\alpha`$, this is the factor $`(2^\alpha-1)^{-1}`$ in <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a>. The error depends on $`L/M`$, independently of the starting scale $`R`$. Consequently the bound will still be useful on the weighted proof’s windows, provided their number dominates the chosen modulus.

Fix $`T=2^j`$. We divide the proof according to how $`d`$ compares with $`LT`$, which is the largest sampled multiple. When $`d\le LT`$, the complete orbit has length $`d/g`$, with $`g=(L,d)`$, and total weight $`1/(B^g-1)`$. Complete cycles and one remaining piece give
``` math
\frac1T\sum_{m=1}^T w_{B,d}(Lm)
 \le\frac{g}{d(B^g-1)}+\frac1{T(B^g-1)}
 \le\frac1{d(B-1)}+\frac1{T(B-1)}.
```
Across dyadic lengths satisfying $`d\le L2^j`$, the reciprocal-length errors sum to at most $`2L/[d(B-1)]`$. When $`d>2LT`$, we have $`Lm\bmod d=Lm`$ and $`2Lm\le d-1`$; hence $`\sum_{i=0}^{d-1}B^i\ge dB^{(d-1)/2}\ge dB^{Lm}`$. Each term $`w_{B,d}(Lm)`$ is then at most $`1/[d(B-1)]`$. Only the transition range $`LT<d\le2LT`$ remains. For fixed $`d`$, doubling $`T`$ moves from $`d>2LT`$ to $`d\le LT`$ after at most one intermediate scale, so this range occurs for at most one dyadic length. For that length, the geometric sum and convexity give
``` math
\frac1T\sum_{m=1}^T w_{B,d}(Lm)
 =\frac{B^L}{T(B^L-1)}\frac{B^{LT}-1}{B^d-1}
 \le\frac{LB^L}{d(B^L-1)}
 \le\frac{2L}{d(B-1)}.
```
The first inequality uses the convexity of $`x\mapsto B^x-1`$ and its value $`0`$ at the origin to bound the ratio by $`LT/d`$. For the last inequality we used $`(B^L-1)/(B-1)=\sum_{i=0}^{L-1}B^i\ge B^{L-1}`$ and $`B\le2`$. Summing the main terms and the two error bounds proves <a href="#eq:mixed-finite-kernel" data-reference-type="eqref" data-reference="eq:mixed-finite-kernel">[eq:mixed-finite-kernel]</a>. The corresponding [source estimate](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR8/DyadicKernel.lean#L206) uses the same finite average. Nonnegative interchange permits summation against any coefficients $`c_d`$ with $`\sum_dc_d/d<\infty`$.

<a id="proof-of-the-cover-criterion"></a>

## Proof of the cover criterion

<div class="proof">

*Proof of Theorem <a href="#thm:variable-fractional-cover" data-reference-type="ref" data-reference="thm:variable-fractional-cover">3</a>.* Write $`B_j=2^{\alpha_j}`$ and
``` math
U_j(N)=\sum_{r\ge1}2^{-r}f_{F_j}(N+r),\qquad
 V_j(N)=\sum_{d\ge1}c_{j,d}w_{B_j,d}(N).
```
We first pass from divisor counts to the shifted tails $`U_j`$. The power $`\alpha_j`$ changes their geometric factor to $`B_j^{-r}`$, so subadditivity and the assumed majorant yield
``` math
U_j(N)^{\alpha_j}
 \le\sum_{r\ge1}B_j^{-r}f_{F_j}(N+r)^{\alpha_j}
 \le\sum_{d\ge1}c_{j,d}
       \sum_{\substack{r\ge1\\d\mid N+r}}B_j^{-r}
 =V_j(N).
```
Summing the progression in each residue class gives the last equality. For the displacement itself, the geometric-series identity gives
``` math
\Delta_{2,F_j}(N)=U_j(N)-X_{F_j}(2)\le U_j(N).
```
We will make the displacements of the first $`J`$ finite sets vanish by divisibility, then use $`U_j(N)`$ to bound the terms from the remaining sets. The early tails themselves need not vanish: the displayed identity then gives $`U_j(N)=X_{F_j}(2)`$ for $`j\le J`$.

Fix $`\varepsilon>0`$ and allot $`t_j=\varepsilon2^{-j}`$ to the $`j`$th tail; these allowances sum to $`\varepsilon`$. Since $`U_j^{\alpha_j}\le V_j`$, it suffices to make $`t_j^{-\alpha_j}V_j<1`$. This normalisation explains the factor $`2^{j\alpha_j}`$ in the cover condition. Choose $`J`$ with
``` math
K_J:=\sum_{j>J}\frac{C_jt_j^{-\alpha_j}}{B_j-1}<\frac14.
```
This is possible since $`\varepsilon^{-\alpha_j}\le\max(1,\varepsilon^{-1})`$. Choose $`L`$ divisible by every member of the first $`J`$ finite sets. Equation <a href="#eq:mixed-finite-kernel" data-reference-type="eqref" data-reference="eq:mixed-finite-kernel">[eq:mixed-finite-kernel]</a> bounds the finite mean of $`S_J(N):=\sum_{j>J}t_j^{-\alpha_j}V_j(N)`$ by $`(1+4L/M)K_J<1/2`$ whenever $`M\ge4L`$. We choose a sample with $`S_J(N)<1`$. Every summand is nonnegative, so this one choice gives $`U_j(N)<t_j`$ for all $`j>J`$ simultaneously. Every exponent in the first $`J`$ finite sets divides $`L`$, so those terms have zero displacement. Consequently,
``` math
0<\Delta_{2,A}(N)\le\sum_{j>J}U_j(N)\le\varepsilon.
```
Equation <a href="#eq:intro-displacement" data-reference-type="eqref" data-reference="eq:intro-displacement">[eq:intro-displacement]</a> now excludes rationality at base two. For $`0\le r<d`$, the function $`(b^r-1)/(b^d-1)`$ is nonincreasing on $`b>1`$. For $`r>0`$, cancel $`b-1`$ and write it as $`A(b)/(A(b)+C(b))`$, where $`A(b)=\sum_{i<r}b^i`$ and $`C(b)=\sum_{r\le j<d}b^j`$. Its derivative has the sign of $`A'C-AC'=\sum_{i<r\le j<d}(i-j)b^{i+j-1}<0`$. Thus $`\Delta_{b,A}(N)\le\Delta_{2,A}(N)`$ for every real $`b\ge2`$; when $`b`$ is an integer, this contradicts the lower bound obtained from <a href="#eq:intro-displacement" data-reference-type="eqref" data-reference="eq:intro-displacement">[eq:intro-displacement]</a> under rationality. Any prescribed positive integer can be included as a divisor of $`L`$, so the chosen indices can also be required to be arbitrarily large. ◻

</div>

The same proof permits any positive weights $`\eta_j`$ with $`\sum_j\eta_j=1`$: replace $`2^{j\alpha_j}`$ in <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a> by $`\eta_j^{-\alpha_j}`$ and take $`t_j=\varepsilon\eta_j`$. The stronger condition $`\sum_jC_j2^{j\alpha_j}2^{\alpha_j}/(2^{\alpha_j}-1)^2<\infty`$ implies <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a>, since each of its summands is the corresponding summand of <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a> multiplied by $`2^{\alpha_j}/(2^{\alpha_j}-1)>1`$. This proves inclusion of the hypotheses for a given cover; after optimisation over all covers, the inclusion of support classes is strict by a [formal proof](https://github.com/wcook04/plectis-erdos/blob/3973d3b10bce72017b8f60093f0d6c3f4f592d80/lean/ErdosProblems/Erdos257/PaperCompleteR8/AnalyticIncomparability.lean#L41).

<a id="sec:mixed"></a>

# A common index for the two criteria

The cover estimate retains its dependence on the modulus so that it can use the larger modulus chosen by the weighted construction. This lets us add the two nonnegative errors on one finite distribution and only then choose an index. We work at base two and obtain the all-base conclusion by the displacement comparison proved above.

<div class="samepage">

<div id="res:mixed-supports" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-257-mersenne-support-subseries.md#res-mixed-supports">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-257-mersenne-support-subseries.md#res-mixed-supports-comparator">Comparator</a></p>

**Theorem 4** (mixed weighted and cover supports). *Let $`E,V\subseteq\mathbb{N}_{>0}`$. Suppose $`E`$ satisfies <a href="#eq:weighted-return" data-reference-type="eqref" data-reference="eq:weighted-return">[eq:weighted-return]</a> for a finite nonempty prime set $`P`$, and $`V\subseteq\bigcup_jF_j`$ for finite sets and nonnegative majorants satisfying the hypotheses of Theorem <a href="#thm:variable-fractional-cover" data-reference-type="ref" data-reference="thm:variable-fractional-cover">3</a>, with either <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a> or its positive-weight variant. Then $`X_A(b)`$ is irrational for every infinite $`A\subseteq E\cup V`$ and every integer $`b\ge2`$.*

</div>

</div>

<div class="proof">

*Proof.* Fix $`\varepsilon>0`$ and an integer $`N_0\ge1`$, and put $`\rho=\varepsilon/3`$. Use the cover notation $`B_j,U_j,V_j`$ above, with $`\eta_j=2^{-j}`$ in the case <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a>. Set $`t_j=\rho\eta_j`$ and choose $`J`$ so that
``` math
K_J=\sum_{j>J}\frac{C_jt_j^{-\alpha_j}}{B_j-1}<\frac1{16}.
```
Choose a finite $`F\subseteq E`$ so that the weighted sum over $`E\setminus F`$ is $`\kappa<\rho/16`$. Let $`L`$ be a positive common multiple of $`N_0`$, all members of $`F`$, and all members of the first $`J`$ finite sets. The order of these choices matters: first $`J`$, $`F`$ and hence $`L`$ are fixed; then the weighted argument enlarges $`L`$ to a modulus $`Q`$ and chooses its dyadic scales; the sample is selected only after both estimates have been placed on that distribution. With $`J`$, $`F`$ and $`L`$ fixed, use the base-two choices
``` math
Q=L\prod_{p\in P}p^{\lfloor\log_pH\rfloor},\qquad
 G=\lfloor H/\max P\rfloor,\qquad M=\lfloor2^{G/2}\rfloor.
```
Both estimates below use $`\mathscr D_{Q;M,M}`$: the scale runs from $`M`$ to $`2M-1`$, and each observation is a multiple $`N=Qm`$. We keep this average fixed while estimating the two contributions. The proof of <a href="#eq:weighted-main-bound" data-reference-type="eqref" data-reference="eq:weighted-main-bound">[eq:weighted-main-bound]</a> allows any multiple of $`F`$ as $`L`$, including the extra divisors imposed by the cover. The estimate also holds for finite or empty $`E`$, since infinitude was used only to make the final displacement positive. Consequently
``` math
\mathscr D_{Q;M,M}(\Delta_{2,E}/\rho)<\frac18
```
for sufficiently large $`H`$. For the same finite distribution, (S) and nonnegative interchange give
``` math
\mathscr D_{Q;M,M}S_J\le(1+4Q/M)K_J<\frac18,
 \qquad S_J=\sum_{j>J}t_j^{-\alpha_j}V_j,
```
because $`Q/M\to0`$. The dependence on the modulus in (S) is essential here: the covering sets fixed $`L`$, whereas the actual samples use the larger modulus $`Q`$. Adding on this one distribution gives
``` math
\mathscr D_{Q;M,M}\bigl(\Delta_{2,E}/\rho+S_J\bigr)<\frac14.
```
Choose a sampled $`N=Qm`$ for which the nonnegative sum is less than $`1`$. Then $`\Delta_{2,E}(N)<\rho`$, and each summand of $`S_J(N)`$ is less than $`1`$. Since $`U_j^{\alpha_j}\le V_j`$, the same choice gives $`U_j(N)<t_j`$ for every $`j>J`$. The displacement terms from the first $`J`$ finite sets vanish because their exponents divide $`L`$, and hence divide $`N`$. Therefore
``` math
\Delta_{2,A}(N)\le\Delta_{2,E}(N)+\Delta_{2,V}(N)<2\rho<\varepsilon,
 \qquad N\ge Q\ge L\ge N_0.
```
This inequality remains valid when $`E`$ and $`V`$ overlap. Since $`A`$ is infinite, $`\Delta_{2,A}(N)>0`$. The comparison $`0<\Delta_{b,A}(N)\le\Delta_{2,A}(N)`$ proved in the cover argument therefore gives arbitrarily small positive values at every integer base. Equation <a href="#eq:intro-displacement" data-reference-type="eqref" data-reference="eq:intro-displacement">[eq:intro-displacement]</a> rules out rationality. ◻

</div>

<a id="sec:comparison"></a>

# Comparison of the support classes

Write $`\mathcal W_b`$ for supports satisfying the finite-prime weighted hypothesis at base $`b`$, and $`\mathcal C`$ for supports admitting a divisor cover satisfying <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a>. Neither condition includes the other.

<div id="res:weighted-cover-incomparability" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-257-mersenne-support-subseries.md#res-weighted-cover-incomparability">Lean</a></p>

**Proposition 5** (incomparable support criteria). *There are infinite positive supports $`E`$ and $`V`$ such that
``` math
E\in\mathcal W_2,\quad E\notin\mathcal C,\qquad
 V\in\mathcal C,\quad V\notin\mathcal W_b\ (b\ge2),\qquad
 \sum_{a\in V}\frac1a=\infty.
```*

</div>

Both constructions use finite sets of the form $`\{qd:d\mid\prod_{p\in P}p\}`$. For $`E`$, we take $`q`$ to be a growing power of $`2`$. This makes the weighted sum converge, while the many simultaneous divisors force the lower bound for any cover to diverge. For $`V`$, we use disjoint sets of primes in successive finite sets. For any fixed finite set of primes, all sufficiently late sets contain only exponents coprime to those primes, so the weighted sum diverges. Fractional powers of the divisor counts will nevertheless give a summable cover cost.

<a id="a-lower-bound-independent-of-the-cover"></a>

## A lower bound independent of the cover

To prove that $`E`$ has no cover, it is not enough to make one choice of majorants expensive. We need a lower bound depending only on finite subsets of $`E`$. For finite $`F`$, let $`\mathbb E_F`$ denote the uniform mean modulo $`\operatorname{lcm}(F)`$, with $`\operatorname{lcm}(\varnothing)=1`$ and $`f_{\varnothing}=0`$. Allow arbitrary weights $`\eta_j>0`$ with $`\sum_j\eta_j=1`$, so that the lower bound also survives reweighting the cover. Set
``` math
K=\sum_j\frac{C_j\eta_j^{-\alpha_j}}{2^{\alpha_j}-1},\qquad
 \Psi(0)=0,\quad
 \Psi(t)=\inf_{0<\alpha\le1}\frac{t^\alpha}{2^\alpha-1}\quad(t\ge1).
```
Here $`\log^+t=\log\max\{1,t\}`$. For every finite $`F`$ contained in $`\bigcup_jF_j`$,
``` math
\begin{equation}
 K\ge\mathbb E_F\Psi(f_F)\ge e\,\mathbb E_F\log^+f_F.
 \label{eq:cover-log-obstruction}
\end{equation}
```
Indeed, if $`f_F(n)=t>0`$, coverage gives $`\sum_jf_{F_j}(n)\ge t`$, so some $`j`$ satisfies $`f_{F_j}(n)\ge\eta_jt`$. Its weighted majorant is at least $`t^{\alpha_j}/(2^{\alpha_j}-1)\ge\Psi(t)`$. The index $`j`$ may depend on $`n`$: it is the sum of all weighted majorants that bounds $`\Psi(f_F(n))`$ at every $`n`$. Average this pointwise inequality over $`1\le n\le X`$. Each divisor indicator has mean $`\lfloor X/d\rfloor/X\le1/d`$, so the mean of the sum of majorants is at most $`K`$. As $`X\to\infty`$, the mean of $`\Psi(f_F)`$ tends to $`\mathbb E_F\Psi(f_F)`$. Only this finite-support function needs a period; the covering moduli need not divide $`\operatorname{lcm}(F)`$. This proves the first inequality. The second is immediate for $`t=0,1`$; for $`t>1`$, use $`2^\alpha-1\le\alpha`$ and $`e^u/u\ge e`$ with $`u=\alpha\log t`$. The scalar inequality $`t^\alpha/(2^\alpha-1)\ge e\log t`$ also has a [formal proof](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR7/CoverKernel.lean#L170).

The lower bound is asymptotically attained on the sets $`\{qd:d\mid\prod_{p\in P}p\}`$: <a href="#eq:optimal-cube-cost" data-reference-type="eqref" data-reference="eq:optimal-cube-cost">[eq:optimal-cube-cost]</a> in Appendix <a href="#app:elementary-details" data-reference-type="ref" data-reference="app:elementary-details">8</a> gives the sharp leading constant. The separation below uses only the lower bound <a href="#eq:cover-log-obstruction" data-reference-type="eqref" data-reference="eq:cover-log-obstruction">[eq:cover-log-obstruction]</a>.

<a id="two-separating-constructions"></a>

## Two separating constructions

<div class="proof">

*Proof of Proposition <a href="#res:weighted-cover-incomparability" data-reference-type="ref" data-reference="res:weighted-cover-incomparability">5</a>.* The reciprocal sum over odd primes diverges, even after finitely many are removed. Otherwise $`\prod_{p\text{ odd}}(1+1/p)`$ would bound the sum of reciprocals of odd squarefree integers; the decomposition $`n=ds^2`$ would then make the odd harmonic series converge.

For the first construction, the $`k`$th group of exponents will carry a factor $`2^k`$. The event $`v_2(n)=k`$ has density $`2^{-(k+1)}`$, so a prime reciprocal sum of order $`2^k`$ will give a fixed contribution to the mean logarithmic count. Taking its leading constant below $`\log2`$ leaves exponential decay in the weighted sum. Choose pairwise disjoint finite sets $`P_k`$ of odd primes such that $`2^k/4\le S_k:=\sum_{p\in P_k}1/p<2^k/4+1`$. Put $`M_k=\prod_{p\in P_k}p`$ and $`E=\bigcup_{k\ge1}\{2^kd:d\mid M_k\}`$. For $`P=\{2\}`$ the weighted sum is
``` math
\sum_{k\ge1}\frac{\prod_{p\in P_k}(1+1/p)}{2^{2^k}-1}
 \le 2e\sum_{k\ge1}
       \exp\bigl(-(\log2-1/4)2^k\bigr)<\infty.
```
For $`F_m=\bigcup_{k=1}^m\{2^kd:d\mid M_k\}`$, average $`\log^+ f_{F_m}`$ over one period. On $`v_2(n)=k<m`$, the set $`\{2^kd:d\mid M_k\}`$ contributes $`2^{Z_k(n)}`$ divisors, where $`Z_k(n)=\sum_{p\in P_k}\mathbf1_{p\mid n}`$. This event has density $`2^{-(k+1)}`$ and is independent of odd-prime divisibility. Thus
``` math
\mathbb E_{F_m}\log^+f_{F_m}
 \ge(\log2)\sum_{k=1}^{m-1}2^{-(k+1)}S_k
 \ge\frac{m-1}{8}\log2.
```
Bound <a href="#eq:cover-log-obstruction" data-reference-type="eqref" data-reference="eq:cover-log-obstruction">[eq:cover-log-obstruction]</a> makes these means uniformly bounded for every strengthened cover, so $`E\notin\mathcal C`$.

For the reverse direction, choose unused odd primes $`q_j\ge4^j`$ and disjoint finite sets $`P_j`$ of unused odd primes. Stop each $`P_j`$ at the first prefix with $`R_j:=\prod_{p\in P_j}(1+1/p)\ge q_j`$. Prime reciprocal divergence permits this, and minimality gives $`q_j\le R_j<4q_j/3`$. Put $`S_j=\sum_{p\in P_j}1/p`$, $`M_j=\prod_{p\in P_j}p`$, and $`V=\bigcup_{j\ge1}F_j`$, where $`F_j=\{q_jd:d\mid M_j\}`$. No prime divides exponents in two different sets $`F_j`$, and
``` math
\sum_{a\in F_j}\frac1a=\frac{R_j}{q_j}\in[1,4/3).
```
Thus $`\sum_{a\in V}1/a`$ diverges. Given a finite set $`P`$ of primes, all exponents in all but finitely many $`F_j`$ are coprime to $`\prod_{p\in P}p`$. On each such $`F_j`$ we have $`h_P(a)=1`$, so its contribution to the base-$`b`$ weighted sum is $`R_j/[q_j(b-1)]\ge1/(b-1)`$. Hence $`V\notin\mathcal W_b`$ for every integer $`b\ge2`$.

For the full infinite-cover cost, from $`\log(1+x)\ge x-x^2/2`$ and $`\sum_{p\in P_j}p^{-2}\le1`$ we have $`S_j\le\log R_j+1/2<\log q_j+1`$. In the $`j`$th term of the cover cost, the factor $`2^{j\alpha_j}`$ becomes $`(1+z_j)^j`$, and the divisor sum contributes $`\prod_{p\in P_j}(1+z_j/p)`$. Their product is at most $`\exp(z_j(j+S_j))`$, which we keep bounded by choosing $`z_j(j+S_j)=1`$. Set
``` math
z_j=(j+S_j)^{-1},\qquad
 \alpha_j=\log_2(1+z_j),\qquad
 c_{j,q_jd}=z_j^{\omega(d)}\quad(d\mid M_j),
```
with other coefficients zero and $`\omega(d)`$ the number of prime factors of $`d`$. If $`q_j\mid n`$ and $`Z`$ primes in $`P_j`$ divide $`n`$, the divisor majorant equals $`(1+z_j)^Z=f_{F_j}(n)^{\alpha_j}`$; otherwise both sides vanish. The sum defining $`C_j`$ is $`C_j=q_j^{-1}\prod_{p\in P_j}(1+z_j/p)`$, whence
``` math
\frac{C_j2^{j\alpha_j}}{2^{\alpha_j}-1}
 =\frac{(1+z_j)^j}{q_jz_j}
    \prod_{p\in P_j}(1+z_j/p)
 \le\frac{e(j+S_j)}{q_j}
 \le e\bigl((1+\log4)j+1\bigr)4^{-j}.
```
The last bound uses that $`(j+\log x+1)/x`$ decreases for $`x\ge4^j`$. The bound is summable in $`j`$ and includes the factor $`2^{j\alpha_j}`$ required by <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a>; hence $`V\in\mathcal C`$. ◻

</div>

<a id="a-strict-enlargement-and-finite-unions"></a>

## A strict enlargement and finite unions

The union of the two separating supports requires the mixed theorem.

<div id="res:strict-mixed-supports" class="corollary">

**Corollary 6** (a support requiring the mixed criterion). *There is an infinite positive support $`U`$ with $`U\notin\mathcal C`$ and $`U\notin\mathcal W_b`$ for every integer $`b\ge2`$, such that $`X_A(b)`$ is irrational for every infinite $`A\subseteq U`$ and every integer $`b\ge2`$.*

</div>

<div class="proof">

*Proof.* Let $`U=E\cup V`$, with $`E,V`$ as in Proposition <a href="#res:weighted-cover-incomparability" data-reference-type="ref" data-reference="res:weighted-cover-incomparability">5</a>. A cover of $`U`$ is also a cover of $`E`$, while convergence of the weighted sum over $`U`$ would imply convergence of the sum over $`V`$ for the same prime set, since all summands are nonnegative. Thus $`U`$ belongs to neither individual class. Theorem <a href="#res:mixed-supports" data-reference-type="ref" data-reference="res:mixed-supports">4</a> gives irrationality for every infinite subset of $`U`$ at every integer base $`b\ge2`$. ◻

</div>

The fixed-dyadic cover class in (V) is closed under finite unions. When interleaving two covers, we must control the index-dependent factor $`2^{j\alpha_j}`$. Place their $`j`$th finite sets at positions $`2j-1,2j`$ and halve each exponent; this factor then does not increase. The old majorant coefficients still work, since $`f^{\alpha/2}\le f^\alpha`$ for every nonnegative integer $`f`$. It remains to compare the denominators in the cost. Writing $`T_j=C_j2^{j\alpha_j}/(2^{\alpha_j}-1)`$ for the original $`j`$th cost, its new cost is at most
``` math
\frac{C_j2^{j\alpha_j}}{2^{\alpha_j/2}-1}
 =(1+2^{\alpha_j/2})T_j\le(1+\sqrt2)T_j.
```
For $`r`$ covers, interleave at positions at most $`rj`$ and divide each exponent by $`r`$; the cost ratio is $`(2^\alpha-1)/(2^{\alpha/r}-1)<2r`$. Weighted supports are likewise closed under finite unions: take the union of their finite prime sets. The prime part $`h_P(a)`$ can only increase, and $`h/(b^h-1)`$ decreases with $`h`$. Finite supports satisfy both criteria, and each criterion is inherited by subsets. Thus the mixed class is closed under finite unions and finite changes with the fixed dyadic weights in (V); arbitrary cover weights are not needed. The summability hypothesis cannot be omitted for countable unions. Every prime singleton is admitted, but for the full prime support $`\mathcal P`$ one has $`\Delta_{2,\mathcal P}(N)>1/3`$ for every $`N\ge1`$: indeed $`\sum_{r\ge1}2^{-r}\omega(N+r)\ge1`$, whereas $`X_{\mathcal P}(2)\le\sum_{a\ge2}(2^a-1)^{-1}<2/3`$. Here $`\omega(n)`$ is the number of distinct prime divisors of $`n`$. The reciprocal-summable class is contained in the weighted class, since $`h/(2^h-1)\le1`$. A direct averaging proof of this special case is given in Section <a href="#sec:reciprocal-support" data-reference-type="ref" data-reference="sec:reciprocal-support">7</a>.

For comparison, Tao–Teräväinen prove the full-prime case at base $`2`$ \[taoteravainen2025, Theorem 1.3, p. 4\]. The paragraph following it states extensions to prime support at every integer base and to full prime-power support at base $`2`$, leaving the modifications to the reader. It does not treat arbitrary infinite thinnings.

<a id="sec:map"></a>

# Limits of the small-displacement criterion

The small-displacement condition does not cover even every support whose sum is already known to be irrational. For full support we have
``` math
\Delta_{2,\mathbb{N}_{>0}}(N)
 >(2^N-1)\sum_{a>N}2^{-a}=1-2^{-N}\ge\frac12
 \qquad(N\ge1).
```
The full-support value is nevertheless [irrational](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L8328) \[erdos1948\]. Thus a proof for arbitrary support would have to use more than this particular family of small displacements. The example leaves other integer linear forms and averaging arguments available.

The logarithmic lower bound <a href="#eq:cover-log-obstruction" data-reference-type="eqref" data-reference="eq:cover-log-obstruction">[eq:cover-log-obstruction]</a> is not a converse: a logarithmic majorant need not control averages on multiples of a prescribed modulus. The [long record’s arithmetic-sampling counterexample](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=record257:logarithmic-sampling) identifies this failure and proves an estimate on ordinary initial intervals. The universal infinite-support problem therefore remains open; these limitations concern the estimates used here.

<a id="sec:reciprocal-support"></a>

# Reciprocal-summable supports

Erdős stated the following extension of his pairwise-coprime theorem \[erdos1968, p. 222\]. It follows from Theorem <a href="#res:weighted-support" data-reference-type="ref" data-reference="res:weighted-support">2</a>, since $`h/(2^h-1)\le1`$, but the direct argument explains why reciprocal summability makes the averaging simpler.

<div id="res:reciprocal-support" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean#L395">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-257-mersenne-support-subseries.md#res-reciprocal-support-comparator">Comparator</a></p>

**Theorem 7** (reciprocal-summable supports). *Let $`A\subseteq\mathbb{N}_{>0}`$ be infinite. If
``` math
\sum_{a\in A}\frac1a<\infty,
```
then $`X_A(b)`$ is irrational for every integer $`b\ge2`$.*

</div>

Erdős also discussed weaker conditions \[erdos1968, pp. 222, 226\]. We do not identify our weighted hypothesis with the conditions he suggested.

Here we can take the observation length to infinity while holding the modulus fixed: reciprocal summability supplies a summable bound for all the remaining exponents. We then enlarge the modulus to make each fixed exponent divide it. No common period for the whole infinite support is required.

Fix the integer base $`b\ge2`$ and put
``` math
w_{b,d}(N)=\frac{b^{N\bmod d}}{b^d-1},\qquad
 T_N^{(b)}=\sum_{d\in A}w_{b,d}(N).
```
Then $`T_N^{(b)}-T_0^{(b)}=\Delta_{b,A}(N)`$. For a fixed positive integer $`Q`$, the orbit of $`Q`$ modulo $`d`$ consists of $`d/g`$ residues, where $`g=(Q,d)`$. Summing the geometric progression gives
``` math
\begin{equation}
 M_{Q,b}(d):=\lim_{X\to\infty}\frac1X\sum_{m=1}^Xw_{b,d}(Qm)
 =\frac{g}{d(b^g-1)}\le\frac1d.
 \label{eq:gcd-orbit-mean}
\end{equation}
```
The orbit $`4,2,0`$ modulo $`6`$ used in Section <a href="#sec:eight-return-extensions" data-reference-type="ref" data-reference="sec:eight-return-extensions">2</a> illustrates this mean: its average of $`w_{2,6}(4m)`$ is $`1/9`$, while the average of $`w_{2,6}(4m)-w_{2,6}(0)`$ is $`2/21`$. When $`d\mid Q`$, we have $`w_{b,d}(Qm)=w_{b,d}(0)`$, so this exponent contributes zero to the displacement.

To interchange the sum over exponents and this limit, we use a bound summable in $`d`$ for the fixed modulus $`Q`$. Counting positive multiples of $`d`$ gives
``` math
\begin{align*}
 \frac1X\sum_{m=1}^Xw_{b,d}(Qm)
 &=\sum_{r\ge1}b^{-r}
       \frac{\#\{1\le m\le X:d\mid Qm+r\}}X\\
 &\le\sum_{r\ge1}b^{-r}\frac{Q+r}{d}
 =\frac{Q/(b-1)+b/(b-1)^2}{d}\le\frac{Q+2}{d}.
\end{align*}
```
Indeed, the counted multiples are distinct and at most $`QX+r`$. For this fixed $`Q`$, the majorant $`(Q+2)/d`$ is summable over $`A`$. Dominated convergence therefore takes the observation-length limit inside the sum over $`d`$, giving the Cesàro mean $`\sum_{d\in A}M_{Q,b}(d)`$. This majorant is not uniform in growing $`Q`$.

Next let $`Q_t=\operatorname{lcm}(1,\ldots,t)`$. For each fixed $`d`$, eventually $`d\mid Q_t`$ and $`M_{Q_t,b}(d)=(b^d-1)^{-1}`$. A second dominated-convergence argument, using $`M_{Q_t,b}(d)\le1/d`$, yields
``` math
\begin{equation}
 \sum_{d\in A}M_{Q_t,b}(d)\longrightarrow X_A(b).
 \label{eq:lcm-prefix-orbit-limit}
\end{equation}
```
Thus the limiting averages of the nonnegative displacements $`\Delta_{b,A}(Q_tm)`$ tend to zero. Choose $`t`$, then a sufficiently long finite average, and finally a term no larger than that average. This gives arbitrarily small positive displacements, contradicting the lower bound $`1/q`$ obtained from <a href="#eq:intro-displacement" data-reference-type="eqref" data-reference="eq:intro-displacement">[eq:intro-displacement]</a>. This proves Theorem <a href="#res:reciprocal-support" data-reference-type="ref" data-reference="res:reciprocal-support">7</a> directly at every integer base.

The order of limits is essential: the observation length tends to infinity with the modulus fixed, and only then does the modulus increase. Reciprocal summability controls both interchanges.

For example, every powerful integer (each prime factor occurs to exponent at least two) has the form $`u^2v^3`$. Hence its reciprocal sum is at most $`\zeta(2)\zeta(3)`$, and the theorem applies to every infinite subset of the powerful integers. For full perfect-power supports, compare Duverney–Tachiya \[duverneytachiya, Corollary 1.2, p. 4\] and the earlier linear-independence results of Luca–Tachiya \[lucatachiya2014independence\].

<a id="app:elementary-details"></a>

# Elementary details used in the proofs

<a id="exact-scalar-cover-cost."></a>

#### Exact scalar cover cost.

For $`t\ge1`$, put $`z=\log_2t`$. The substitution $`y=2^\alpha`$ reduces the infimum defining $`\Psi(t)`$ to $`y^z/(y-1)`$ on $`1<y\le2`$. Its derivative has the sign of $`(z-1)y-z`$. Hence
``` math
\Psi(t)=
 \begin{cases}t,&1\le t\le4,\\
 z^z/(z-1)^{z-1},&t>4.
 \end{cases}
```
The endpoint and the open lower bound $`\alpha>0`$ are both included in this calculation. This scalar identity does not supply a converse to the positive-cover criterion.

<a id="the-cost-for-a-finite-set-of-divisors"></a>

## The cost for a finite set of divisors

For the following finite divisor sets, the lower bound is asymptotically attained. Here $`K_*(F)`$ is the infimum of the cover cost $`K`$ from Section <a href="#sec:comparison" data-reference-type="ref" data-reference="sec:comparison">5</a>, taken over finite or countable covers of $`F`$ and all positive weights of total one. For $`F(q,P)=\{qd:d\mid\prod_{p\in P}p\}`$, where $`q\ge2`$ and no $`p\in P`$ divides $`q`$, put $`S=\sum_{p\in P}1/p`$. If $`S\ge1`$, then
``` math
\begin{equation}
 \frac{e(S-1)}q\le K_*\bigl(F(q,P)\bigr)\le\frac{eS}q.
 \label{eq:optimal-cube-cost}
\end{equation}
```
For the lower bound, we condition on $`q\mid n`$ and write $`f_F(n)=2^Z`$. The Chinese remainder theorem gives $`\mathbb EZ=S`$. For $`z\ge0`$ and $`v=\alpha\log2>0`$,
``` math
\frac{2^{\alpha z}}{2^\alpha-1}
 \ge\frac{e^{(z-1)v}}v\ge e(z-1)\quad(z>1);
```
for $`0\le z\le1`$ the claimed lower bound is nonpositive. Thus $`\Psi(2^z)\ge e(z-1)`$. For the upper bound, use the one-set cover, whose weight is one, with $`z=1/S`$ and $`\alpha=\log_2(1+z)`$; its exact positive expansion has cost
``` math
\frac1{qz}\prod_{p\in P}(1+z/p)\le\frac{eS}q.
```
In particular, $`1-1/S\le qK_*(F(q,P))/(eS)\le1`$. Thus $`K_*(F(q,P))\sim eS/q`$ as $`S\to\infty`$, uniformly over the permitted choices of $`q`$ and $`P`$.

<a id="verification"></a>

# Verification

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-257-mersenne-support-subseries.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

The weighted, cover and mixed implications have formal proofs. The printed fresh-prime construction and strictness corollary have ordinary proofs; the corresponding formal separating construction uses different parameters. The [long record’s verification section](../../../paper/257/erdos257-mersenne-reasoning-surface.pdf#nameddest=scope-verification) gives the exact correspondence, review status and reproduction commands.

<a id="acknowledgements"></a>

# Acknowledgements

I thank Wouter van Doorn for advice on mathematical exposition, in particular on explaining restrictive hypotheses, avoiding unnecessary notation, and writing for a first-time reader. His comments concerned a note on Problem 243; this acknowledgement does not imply that he reviewed the mathematics of the present paper.

<div class="thebibliography">

99 D. Duverney and Y. Tachiya, [*Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf), Forum Math. 31 (2019), no. 6, 1557–1566, [DOI](https://doi.org/10.1515/forum-2018-0299). Page numbers refer to the linked author preprint. H. Kaneko, Y. Suzuki, and Y. Tachiya, [*Refinements of Erdős’s irrationality criterion for certain sparse infinite series*](https://arxiv.org/abs/2601.20743v1), arXiv:2601.20743v1 (2026). T. Tao and J. Teräväinen, [*Quantitative correlations and some problems on prime factors of consecutive integers*](https://arxiv.org/abs/2512.01739v2), arXiv:2512.01739v2 (submitted December 2025, revised April 2026). P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. 12 (1948), 63–66. P. Erdős, [*On the irrationality of certain series*](https://users.renyi.hu/~p_erdos/1969-09.pdf), Math. Student 36 (1968), 222–226 (issued 1969); [five-page scan](https://www.renyi.hu/~p_erdos/1969-09.pdf). F. Luca and Y. Tachiya, *Linear independence of certain Lambert series*, Proceedings of the American Mathematical Society **142** (2014), no. 10, 3411–3419. [doi:10.1090/S0002-9939-2014-12102-2](https://doi.org/10.1090/S0002-9939-2014-12102-2).

</div>
