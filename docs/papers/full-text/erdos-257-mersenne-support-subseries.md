<a id="erdos-257-mersenne-support-subseries"></a>

# Weighted Support Criteria for Reciprocal Mersenne Subseries

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

For a finite nonempty prime set $`P`$, put $`h(a)=\prod_{p\in P}p^{v_p(a)}`$. We prove that every infinite $`A`$ with
``` math
\sum_{a\in A}\frac{h(a)}{a(2^{h(a)}-1)}<\infty
```
has irrational $`\sum_{a\in A}(b^a-1)^{-1}`$ at every integer base $`b\ge2`$. The condition is hereditary and strictly weaker than reciprocal summability: an explicit host has divergent $`\sum_{a\in A}1/a`$ while satisfying the weighted condition. Finite gcd-orbit averages and a second average over dyadic observation lengths produce arbitrarily small positive displacements, which rationality would confine to a fixed lattice. Erdős already stated the weaker coprimality-free reciprocal-summable theorem, including its all-base quantifier, leaving its proof unprinted; an independent complete proof is printed here. A uniform finite averaging estimate also combines the weighted criterion with positive divisor covers: their union has the same hereditary irrationality property. These are sufficient support criteria, not a resolution for arbitrary infinite support. The finite arithmetic and rational-target questions are kept distinct from the irrationality results.

<a id="sec:problem"></a>

# Introduction and main results

For $`A\subseteq\mathbb{N}_{>0}`$ and a real $`b>1`$, write
``` math
X_A(b)=\sum_{a\in A}\frac1{b^a-1}.
```
All these series converge: $`(b^a-1)^{-1}\le b^{1-a}/(b-1)`$. Our main sufficient condition uses a finite nonempty set $`P`$ of primes and its prime part $`h(a)=\prod_{p\in P}p^{v_p(a)}`$.

<div id="res:weighted-support" class="theorem">

**Theorem 1** (finite prime-part weighted mass). *Let $`b\ge2`$ be an integer and let $`A\subseteq\mathbb{N}_{>0}`$ be infinite. If
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

The proof is in Section <a href="#sec:eight-return-extensions" data-reference-type="ref" data-reference="sec:eight-return-extensions">3</a>. Its conclusion is obtained by finite averaging, not by passing to an uncontrolled infinite mean. The reciprocal-summable theorem below supplies a simpler model for the argument. Since $`h/(2^h-1)\le1`$ for integers $`h\ge1`$, its hypothesis implies the base-two weighted condition. Strictness is witnessed by the host constructed after the proof of Theorem <a href="#res:weighted-support" data-reference-type="ref" data-reference="res:weighted-support">1</a>.

<div id="res:reciprocal-support" class="theorem">

**Theorem 2** (reciprocal-summable supports). *Let $`A\subseteq\mathbb{N}_{>0}`$ be infinite. If
``` math
\sum_{a\in A}\frac1a<\infty,
```
then $`X_A(b)`$ is irrational for every integer $`b\ge2`$.*

</div>

Theorem <a href="#res:reciprocal-support" data-reference-type="ref" data-reference="res:reciprocal-support">2</a>, including its all-base quantifier, is attributed to Erdős \[erdos1968, p. 222\]; the printed coprime argument and the stated coprimality-free extension must not be conflated. The proof below is supplied independently, without identifying it with his omitted argument. The historical source-access limitation and the formal counterparts are recorded in Appendix <a href="#app:sources" data-reference-type="ref" data-reference="app:sources">11</a>. The supplied release at `52f29ad173b0` includes solution wrappers for reciprocal support, weighted support, variable-exponent covers and the mixed criterion. Their selected source files and statement comparisons are distributed with this revision. The existential weighted host wrapper must not be cited as a proof of the particular explicit host $`A_\star`$. The latter has its own ordinary proof above. Historical links below are retained as source locators, not presented as newly verified URLs.

The nearby [pairwise-coprime support theorem](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L10776) keeps an extra pairwise-coprimality hypothesis together with summable reciprocal mass, and is therefore a structured-support theorem, not Theorem <a href="#res:reciprocal-support" data-reference-type="ref" data-reference="res:reciprocal-support">2</a>. Full support at every integer base is the separate [full-support irrationality theorem](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L8328). Arbitrary infinite support remains open.

Erdős remarks that without coprimality the proof becomes more complicated and uses the fact that $`\alpha`$ is irrational when the fractional parts of $`t^n\alpha`$ take infinitely many values \[erdos1968, p. 226\]. For infinite $`A`$ and $`N>0`$, division of $`N`$ by each $`a\in A`$ gives
``` math
0<\Delta_{b,A}(N)
 :=\sum_{a\in A}\frac{b^{N\bmod a}-1}{b^a-1}
 =(b^N-1)X_A(b)-J_{b,A}(N),\qquad J_{b,A}(N)\in\mathbb{Z}.
 \label{eq:intro-displacement}\tag{D}
```
Here the integer is the evaluation of the finite polynomial
``` math
J_A(N;x)=\sum_{\substack{a\in A\\a\le N}}
             \sum_{j=1}^{\lfloor N/a\rfloor}x^{N-ja},
 \qquad J_{b,A}(N)=J_A(N;b).
```
The identity holds for every real $`b>1`$; integrality uses the integer-base hypothesis. Every summand in the displacement is nonnegative, and an exponent $`a>N`$ gives a positive summand; such an exponent exists because $`A`$ is infinite. Rationality $`X_A(b)=p/q`$ would force every positive displacement to be at least $`1/q`$. The proof makes these positive displacements arbitrarily small by averaging along multiples of a growing divisibility modulus.

The conclusion is hereditary: every infinite subset of such an $`A`$ satisfies the theorem at every base. For example, every powerful integer can be written as $`u^2v^3`$, so
``` math
\sum_{\substack{a\ge1\\a\text{ powerful}}}\frac1a
 \le\zeta(2)\zeta(3)<\infty.
```
Thus arbitrary infinite thinnings of the powerful integers are included. For the full set of perfect $`i`$th powers, $`i\ge2`$, irrationality at every integer base is also a case of Corollary 1.2 of Duverney and Tachiya, taken with $`E`$ the primes and $`s=\infty`$ \[duverneytachiya, p. 4\]. Their refinement belongs to the linear-independence line that includes Luca and Tachiya’s earlier paper \[lucatachiya2014independence\]; the hereditary thinning conclusion above should still be stated separately from full-support instances.

<div id="res:problem" class="problem">

**Problem 3** (Erdős \#257). Is $`X_A(2)`$ irrational for every infinite $`A\subseteq\mathbb{N}_{>0}`$?

</div>

Theorem <a href="#res:weighted-support" data-reference-type="ref" data-reference="res:weighted-support">1</a> gives the principal support criterion; Theorem <a href="#res:mixed-supports" data-reference-type="ref" data-reference="res:mixed-supports">5</a> combines it with positive divisor covers by producing a common small displacement. Sections <a href="#sec:forced" data-reference-type="ref" data-reference="sec:forced">5</a> and <a href="#sec:actual-repairs" data-reference-type="ref" data-reference="sec:actual-repairs">8</a> distinguish irrationality tests from the membership problem for a specified rational. Claims depending on missing supplements are catalogued separately, not used as premises of these proofs.

Erdős proved the pairwise-coprime case at every integer base and stated that the coprimality condition could be removed, leaving the details unprinted \[erdos1968, p. 222\]. Theorem <a href="#res:reciprocal-support" data-reference-type="ref" data-reference="res:reciprocal-support">2</a> gives a complete proof of that stated extension, obtained independently. The all-base quantifier is already in Erdős’s statement. No priority over Erdős is claimed and no identification with his omitted argument is asserted. Erdős also wrote that the condition $`\sum1/n_i<\infty`$ could be replaced by a weaker but more complicated condition, and that for pairwise coprime supports Brun’s method could probably replace it by $`\sum_{n_i<x}1/n_i=o(\log\log x)`$ \[erdos1968, pp. 222 and 226\]. Theorem <a href="#res:weighted-support" data-reference-type="ref" data-reference="res:weighted-support">1</a> proves irrationality under one explicit weaker condition, without coprimality; no identification with the conditions he suggested is asserted.

The coefficient sequence throughout is the divisor transform of one Boolean selector:
``` math
\begin{equation}
 c_A(n)=\#\{a\in A:a\mid n\},\qquad
 X_A(b)=\sum_{n\ge1}\frac{c_A(n)}{b^n}.
 \label{eq:incidence}
\end{equation}
```
Tonelli’s theorem applied to $`(b^a-1)^{-1}=\sum_{j\ge1}b^{-aj}`$ proves the identity. Moreover $`0\le c_A(n)\le\tau(n)`$. The coefficients need not be Boolean: it is the selector $`1_A`$, not its divisor transform $`c_A`$, that takes values in $`\{0,1\}`$. All subsequent orbit conditions must retain that common origin.

<a id="sec:reciprocal-support"></a>

# Reciprocal-summable supports at every integer base

The proof freezes a finite portion of the support and averages the rest. Making the shift divisible by the frozen exponents makes their displacement exactly zero. The remaining exponents need not have a common period of manageable size: reciprocal summability bounds their total average directly.

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
For example, at $`b=2`$, $`Q=4`$ and $`d=6`$, the orbit is $`4,2,0`$ modulo $`6`$. Its mean atom is $`(16+4+1)/(3\cdot63)=1/9`$, whereas its zero-shift atom is $`1/63`$. If $`6\mid Q`$, the orbit instead stays at zero and the mean is exactly $`1/63`$. This is the effect of freezing an exponent; the infinite tail still requires the bound that follows. The passage from individual atoms to their infinite sum needs a uniform bound. Counting positive multiples of $`d`$ gives
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
Thus the limiting averages of the nonnegative displacements $`\Delta_{b,A}(Q_tm)`$ tend to zero. Choose $`t`$, then a sufficiently long finite average, and finally a term no larger than that average. This gives arbitrarily small positive displacements, contradicting the rational lattice in <a href="#eq:intro-displacement" data-reference-type="eqref" data-reference="eq:intro-displacement">[eq:intro-displacement]</a>. This proves Theorem <a href="#res:reciprocal-support" data-reference-type="ref" data-reference="res:reciprocal-support">2</a> directly at every integer base.

The order of limits is essential: the observation length tends to infinity with the modulus fixed, and only then does the modulus increase. Reciprocal summability controls both interchanges.

The weighted proof cannot use the same summable $`1/d`$ majorant. Its replacement is a finite estimate that keeps both the modulus and the observation length visible until the parameters have been chosen.

<a id="sec:eight-return-extensions"></a>

# Extensions beyond reciprocal summability

Three inputs are used in order: a finite orbit estimate for each exponent, a dyadic average controlling incomplete periods, and a summable weighted tail after a finite head has been frozen. The estimate (S) below supplies the uniformity needed to use the same finite distribution for covers.

<a id="finite-prime-part-weighted-mass"></a>

## Finite prime-part weighted mass

For a finite nonempty prime set $`P`$, put $`h(a)=\prod_{p\in P}p^{v_p(a)}`$.

Theorem <a href="#res:weighted-support" data-reference-type="ref" data-reference="res:weighted-support">1</a> was stated in the introduction. We prove its fixed-base version; the base-two condition implies every integer-base instance because $`b^{h(a)}-1\ge2^{h(a)}-1`$.

<div class="proof">

*Proof.* The rational-lattice obstruction is <a href="#eq:intro-displacement" data-reference-type="eqref" data-reference="eq:intro-displacement">[eq:intro-displacement]</a>: if $`X_A(b)=p/q`$, every positive $`\Delta_{b,A}(m)`$ is at least $`1/q`$. For $`d_a(m)=(b^{m\bmod a}-1)/(b^a-1)`$ and $`g=(Q,a)`$, one complete orbit of $`Qm\bmod a`$ gives, for $`Q,a,T\ge1`$,
``` math
\begin{equation}
\label{eq:weighted-finite-orbit}
 \frac1T\sum_{t=1}^T d_a(tQ)
 \le \frac{g}{a(b^g-1)}+\frac1{T(b^g-1)}.
\end{equation}
```
Indeed, the orbit has length $`a/g`$ and $`\sum_{t=1}^{a/g}b^{tQ\bmod a}/(b^a-1)=1/(b^g-1)`$; an incomplete orbit costs at most one more complete orbit. Also, for $`Y=QT`$,
``` math
\begin{equation}
\label{eq:weighted-outer-short}
 \frac1T\sum_{t=1}^T\sum_{\substack{a\in A\\a>Y}}d_a(tQ)
 \le\frac4T,
\end{equation}
```
because $`d_a(tQ)\le2\,2^{tQ-a}`$ when $`a>QT`$ and $`\sum_{t=1}^T2^{tQ-QT}\le2`$.

The incomplete-orbit errors are controlled by a second finite average. For $`\alpha_a\ge0`$ with $`\sum_a\alpha_a/a<\infty`$,
``` math
\begin{equation}
\label{eq:weighted-dyadic-short}
 \sum_{j=M}^{2M-1}\frac1{2^j}\sum_{a\le Q2^j}\alpha_a
 \le2Q\sum_{a\ge1}\frac{\alpha_a}{a};
\end{equation}
```
for each fixed $`a`$, the admissible geometric tail is at most $`2Q/a`$.

Fix $`\varepsilon>0`$. Choose finite nonempty $`F\subseteq A`$ so that the <a href="#eq:weighted-fixed-base" data-reference-type="eqref" data-reference="eq:weighted-fixed-base">[eq:weighted-fixed-base]</a> mass outside $`F`$ is below $`\varepsilon`$, and let $`L`$ be any fixed positive common multiple of $`F`$. With $`p_*=\max P`$, $`r=|P|`$, and large $`H\ge2p_*`$, set
``` math
Q=L\prod_{p\in P}p^{\lfloor\log_pH\rfloor},\qquad
 G=\left\lfloor\frac H{p_*}\right\rfloor.
```
The set $`F`$ is frozen. If $`h(a)\le H`$, then $`h(a)\mid Q`$, so <a href="#eq:weighted-finite-orbit" data-reference-type="eqref" data-reference="eq:weighted-finite-orbit">[eq:weighted-finite-orbit]</a> is paid by the weighted tail plus its incomplete-orbit term. If $`h(a)>H`$, then $`(Q,a)\ge G`$, and monotonicity of $`n/(b^n-1)`$ bounds that part by
``` math
\frac{G(1+\log(QT))+Q}{b^G-1}.
```
For the gcd claim, either every $`P`$-prime-power component of $`h(a)`$ is at most $`H`$, in which case $`h(a)\mid Q`$, or some $`p^{v_p(a)}>H`$ contributes $`p^{\lfloor\log_pH\rfloor}>H/p\ge H/p_*\ge G`$ to the gcd. Combining this with <a href="#eq:weighted-outer-short" data-reference-type="eqref" data-reference="eq:weighted-outer-short">[eq:weighted-outer-short]</a>, taking $`M=\lfloor b^{G/2}\rfloor`$, averaging over $`T=2^j`$ for $`M\le j<2M`$, and using <a href="#eq:weighted-dyadic-short" data-reference-type="eqref" data-reference="eq:weighted-dyadic-short">[eq:weighted-dyadic-short]</a> with $`\alpha_a={\bf1}_A(a)/(b^{h(a)}-1)`$ yields
``` math
\begin{equation}
\label{eq:weighted-main-bound}
 \frac1M\sum_{j=M}^{2M-1}\frac1{2^j}
 \sum_{t=1}^{2^j}\Delta_{b,A}(tQ)
 \le \varepsilon+\frac{2QW_{b,P}(A)}M
 +\frac{G(1+\log Q+2M\log2)+Q}{b^G-1}+4\,2^{-M}.
\end{equation}
```
The choices have the following order: fix the tail budget $`\varepsilon`$, choose the finite head and its common multiple $`L`$, and only then let $`H\to\infty`$. With $`L`$ fixed, $`Q\le LH^r`$, $`G=H/p_*+O(1)`$ and $`M\asymp b^{G/2}`$, so every term after $`\varepsilon`$ tends to zero. This proves existence of small returns, not a specified decay rate in the final index $`N=Qt`$. The left side is a finite average of positive displacements, so one is below $`2\varepsilon`$ for large $`H`$; rerunning with $`\varepsilon/2`$ gives the required bound. This contradicts the rational lattice. Finally $`W_{b,P}(A)\le W_{2,P}(A)`$ for $`b\ge2`$, and weighted mass decreases on taking subsets. ◻

</div>

The hypothesis is genuinely weaker than reciprocal summability. Let
``` math
A_\star=\{2^k m:k\ge1,\ m\text{ odd},\ m\le2^{2^k}\}.
```
If $`N_k=2^{2^k}`$, the reciprocal mass in its $`k`$th layer is
``` math
R_k=2^{-k}\sum_{\substack{m\le N_k\\m\text{ odd}}}\frac1m
 =2^{-k}\bigl(H_{N_k}-\tfrac12H_{N_k/2}\bigr)
 \longrightarrow\frac{\log2}{2},
```
so $`\sum_{a\in A_\star}1/a`$ diverges. For $`P=\{2\}`$ the weighted mass of that layer is
``` math
\frac{2^k}{2^{2^k}-1}R_k,
```
and these terms are summable. Thus every infinite subset of $`A_\star`$ has irrational $`X_A(b)`$ at every integer base. This example establishes strictness only; the stronger previously proposed host with $`O(\log\log a)`$ gaps is not asserted here.

The theorem and this example have the ordinary proofs just given. The explicit host calculation is separate from the existential host statements in the supplied formal release; they are not identified solely by name. The arbitrary-chain, quantitative and prime-power extensions remain separate from Theorem <a href="#res:weighted-support" data-reference-type="ref" data-reference="res:weighted-support">1</a>.

The proofs of Theorems <a href="#res:reciprocal-support" data-reference-type="ref" data-reference="res:reciprocal-support">2</a> and <a href="#res:weighted-support" data-reference-type="ref" data-reference="res:weighted-support">1</a> select a term no larger than a finite average. Duverney and Tachiya select their index in the same way in their refinement of the Chowla–Erdős method. They average a local coefficient mass over an arithmetic progression built by the Chinese remainder theorem, and a term attaining the minimum supplies the bounds that control the tail beyond it \[duverneytachiya, Section 2, (2.3)–(2.9), pp. 5–6\]. Kaneko, Suzuki and Tachiya measure the average decay of scaled tails by the quantity $`R_c(q,x,z)`$ of their (1.7). Under a counting condition on the support and a bound on $`R_c`$ they show that most scaled tails in a range are small, and arbitrarily small nonzero scaled tails give irrationality \[kanekosuzukitachiya, p. 3; Lemmas 1 and 2, pp. 6–8\]. The incidence coefficients <a href="#eq:incidence" data-reference-type="eqref" data-reference="eq:incidence">[eq:incidence]</a> are positive on every multiple of $`\min A`$. For any splitting of $`c_A`$ into two sequences the two coefficient supports therefore cover a set of positive lower density, which is incompatible with the support-counting conditions \[kanekosuzukitachiya, Theorem 1(iii), p. 3, and Theorem 3(iv), p. 5\] requiring both counts to be $`o(x_n/z_n)`$ with $`z_n\ge1`$. Their remote-tail quantity $`R_c(q,x,z)`$ sums only offsets $`j\ge z`$, whereas the full scaled tail
``` math
\sum_{r\ge1}\frac{c_A(N+r)}{b^r}
 =\sum_{a\in A}\frac{b^{N\bmod a}}{b^a-1}
 =X_A(b)+\Delta_{b,A}(N)
```
is at least $`X_A(b)`$ for every $`N\ge1`$, which gives no lower bound for $`R_c`$. The proofs above average the displacement $`\Delta_{b,A}(N)`$ instead, along multiples of a modulus that freezes a finite part of $`A`$; the weighted proof adds a second average over dyadic observation lengths.

<a id="claimed-quantitative-criterion-unassessed-here"></a>

## Claimed quantitative criterion (unassessed here)

The absent analytic supplement claims a second criterion admitting reciprocal-divergent supports. Put $`H_A(x)=\sum_{a\in A,\ a\le x}1/a`$, $`T_0=2`$, $`T_{j+1}=2^{T_j}`$, and $`\ell(x)=\min\{j:x\le T_j\}`$. The condition $`H_A(x)=o(\ell(x))`$ is claimed to imply all-base irrationality, with no positive density assumption on $`A`$. Neither a proof of this implication nor the claimed sharper rational-phase lower bound is present in this checkout.

<a id="sec:common-kernel"></a>

## A finite estimate on common observation scales

For $`1<B\le2`$, positive integers $`L,d,M`$, and an integer $`R\ge0`$, put
``` math
w_{B,d}(n)=\frac{B^{n\bmod d}}{B^d-1},\qquad
 \mathscr D_{L;R,M}F
 =\frac1M\sum_{j=R}^{R+M-1}\frac1{2^j}
      \sum_{m=1}^{2^j}F(Lm).
```
The finite estimate
``` math
\begin{equation*}
 \mathscr D_{L;R,M}w_{B,d}
 \le\frac{1+4L/M}{d(B-1)}
 \tag{S}\label{eq:mixed-finite-kernel}
\end{equation*}
```
is uniform in $`d`$, $`R`$, and $`B`$ as $`B`$ decreases to one. The ratio $`L/M`$ measures the cost of incomplete modular periods.

To prove it, fix $`T=2^j`$ and average over $`1\le m\le T`$. When $`d\le LT`$, the complete orbit has length $`d/g`$, with $`g=(L,d)`$, and total weight $`1/(B^g-1)`$. Complete cycles and one remaining piece give
``` math
\frac1T\sum_{m=1}^T w_{B,d}(Lm)
 \le\frac{g}{d(B^g-1)}+\frac1{T(B^g-1)}
 \le\frac1{d(B-1)}+\frac1{T(B-1)}.
```
Across dyadic lengths satisfying $`d\le L2^j`$, the reciprocal-length errors sum to at most $`2L/[d(B-1)]`$. When $`d>2LT`$, there is no wrap and $`2Lm\le d-1`$; hence $`\sum_{i=0}^{d-1}B^i\ge dB^{(d-1)/2}\ge dB^{Lm}`$. Each atom is then at most $`1/[d(B-1)]`$. Finally, at most one dyadic length satisfies $`LT<d\le2LT`$. For that length the geometric sum and convexity give
``` math
\frac1T\sum_{m=1}^T w_{B,d}(Lm)
 =\frac{B^L}{T(B^L-1)}\frac{B^{LT}-1}{B^d-1}
 \le\frac{LB^L}{d(B^L-1)}
 \le\frac{2L}{d(B-1)}.
```
Summing the main terms and these two error budgets proves <a href="#eq:mixed-finite-kernel" data-reference-type="eqref" data-reference="eq:mixed-finite-kernel">[eq:mixed-finite-kernel]</a>. The release snapshot contains a proof body for the full estimate in [*DyadicKernel*, `dyadicMean_kernelWeight_le`](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos257/PaperCompleteR8/DyadicKernel.lean#L207). Its complete-cycle and no-wrap scalar ingredients are in [*CoverKernel*](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos257/PaperCompleteR7/CoverKernel.lean#L130). These are source locators, not a fresh compilation or axiom-audit receipt; the argument displayed here is an ordinary proof. Nonnegative interchange permits summation against any coefficients $`c_d`$ with $`\sum_dc_d/d<\infty`$.

<a id="positive-fractional-divisor-covers"></a>

## Positive fractional divisor covers

For a finite set $`F`$, put $`f_F(n)=\#\{a\in F:a\mid n\}`$. Let $`F_j`$ be finite sets of positive integers, let $`0<\alpha_j\le1`$, and suppose $`c_{j,d}\ge0`$ satisfy
``` math
f_{F_j}(n)^{\alpha_j}\le\sum_{d\mid n}c_{j,d},\qquad
 C_j=\sum_{d\ge1}\frac{c_{j,d}}d.
```

<div id="thm:variable-fractional-cover" class="theorem">

**Theorem 4** (strengthened positive covers). *If
``` math
\begin{equation*}
 \sum_{j\ge1}\frac{C_j2^{j\alpha_j}}{2^{\alpha_j}-1}<\infty,
 \tag{V}\label{eq:strengthened-cover}
\end{equation*}
```
then $`X_A(b)`$ is irrational for every infinite $`A\subseteq\bigcup_jF_j`$ and every integer $`b\ge2`$.*

</div>

<div class="proof">

*Proof.* Write $`B_j=2^{\alpha_j}`$ and
``` math
U_j(N)=\sum_{r\ge1}2^{-r}f_{F_j}(N+r),\qquad
 V_j(N)=\sum_{d\ge1}c_{j,d}w_{B_j,d}(N).
```
Subadditivity of the fractional powers and the positive majorants give $`U_j(N)^{\alpha_j}\le V_j(N)`$. The geometric-series identity also gives
``` math
\Delta_{2,F_j}(N)=U_j(N)-X_{F_j}(2)\le U_j(N).
```
Consequently, once the first $`J`$ frames have zero displacement, nonnegativity bounds the displacement of their union by $`\sum_{j>J}U_j(N)`$.

Fix $`\varepsilon>0`$, set $`t_j=\varepsilon2^{-j}`$, and choose $`J`$ with
``` math
K_J:=\sum_{j>J}\frac{C_jt_j^{-\alpha_j}}{B_j-1}<\frac14.
```
This is possible since $`\varepsilon^{-\alpha_j}\le\max(1,\varepsilon^{-1})`$. Choose $`L`$ divisible by every member of the first $`J`$ frames. Equation <a href="#eq:mixed-finite-kernel" data-reference-type="eqref" data-reference="eq:mixed-finite-kernel">[eq:mixed-finite-kernel]</a> bounds the finite mean of $`S_J(N):=\sum_{j>J}t_j^{-\alpha_j}V_j(N)`$ by $`(1+4L/M)K_J<1/2`$ whenever $`M\ge4L`$. One sample therefore has $`S_J(N)<1`$, forcing $`U_j(N)<t_j`$ for every $`j>J`$. The frozen frames have zero displacement, so
``` math
0<\Delta_{2,A}(N)\le\sum_{j>J}U_j(N)\le\varepsilon.
```
The fixed rational lattice excludes rationality at base two. For $`0\le r<d`$, the function $`(b^r-1)/(b^d-1)`$ is nonincreasing on $`b>1`$. For $`r>0`$, cancel $`b-1`$ and write it as $`A(b)/(A(b)+C(b))`$, where $`A(b)=\sum_{i<r}b^i`$ and $`C(b)=\sum_{r\le j<d}b^j`$. Its derivative has the sign of $`A'C-AC'=\sum_{i<r\le j<d}(i-j)b^{i+j-1}<0`$. Thus $`\Delta_{b,A}(N)\le\Delta_{2,A}(N)`$ for every real $`b\ge2`$; when $`b`$ is an integer, the same rational-lattice argument applies. Any prescribed positive divisor can be included in $`L`$, so the witnesses can also be required to be arbitrarily large. ◻

</div>

The same proof permits any positive weights $`\eta_j`$ with $`\sum_j\eta_j=1`$: replace $`2^{j\alpha_j}`$ in <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a> by $`\eta_j^{-\alpha_j}`$ and take $`t_j=\varepsilon\eta_j`$. The condition strengthens the earlier two-inverse-power cost $`\sum_jC_j2^{j\alpha_j}2^{\alpha_j}/(2^{\alpha_j}-1)^2<\infty`$. The unavailable *Strengthened Variable-Exponent Cover* supplement claims a squarefree support $`A^\star`$ satisfying <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a> for which every cover with that older cost, and every finite-prime weighted criterion, fails. Its construction is not in this checkout and is not a result of the present release.

<a id="what-every-positive-cover-must-pay"></a>

## What every positive cover must pay

The strengthening has a cover-independent boundary. For finite $`F`$, write $`\mathbb E_F`$ for the uniform mean modulo $`\operatorname{lcm}(F)`$, with $`\operatorname{lcm}(\varnothing)=1`$ and $`f_{\varnothing}=0`$. More generally allow weights $`\eta_j>0`$ with $`\sum_j\eta_j=1`$, and set
``` math
K=\sum_j\frac{C_j\eta_j^{-\alpha_j}}{2^{\alpha_j}-1},\qquad
 \Psi(0)=0,\quad
 \Psi(t)=\inf_{0<\alpha\le1}\frac{t^\alpha}{2^\alpha-1}\quad(t\ge1).
```
For every finite $`F`$ covered by the frames,
``` math
\begin{equation}
 K\ge\mathbb E_F\Psi(f_F)\ge e\,\mathbb E_F\log^+f_F.
 \label{eq:cover-log-obstruction}
\end{equation}
```
Indeed, at a point where $`f_F(n)=t>0`$, some frame has $`f_{F_j}(n)\ge\eta_jt`$. Otherwise summing contradicts coverage. The corresponding weighted majorant is at least $`\Psi(t)`$. Averaging and using $`\lfloor X/d\rfloor/X\le1/d`$ proves the first inequality. Convexity gives $`2^\alpha-1\le\alpha`$, and $`e^u/u\ge e`$ proves the second. Those scalar steps have corresponding source bodies in [*CoverKernel*, lines 170–214](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos257/PaperCompleteR7/CoverKernel.lean#L170), including the bound $`t^\alpha/(2^\alpha-1)\ge e\log t`$. This does not by itself formalise the assembled averaging argument, and no fresh Lean verification is claimed.

This bound survives optimisation over all covers. For $`F(q,P)=\{qd:d\mid\prod_{p\in P}p\}`$, where $`q\ge2`$ and no $`p\in P`$ divides $`q`$, put $`S=\sum_{p\in P}1/p`$. If $`S\ge1`$, the infimum $`K_*`$ over all covers satisfies
``` math
\begin{equation}
 \frac{e(S-1)}q\le K_*\bigl(F(q,P)\bigr)\le\frac{eS}q.
 \label{eq:optimal-cube-cost}
\end{equation}
```
For the lower bound, condition on $`q\mid n`$ and write $`f_F(n)=2^Z`$. The Chinese remainder theorem gives $`\mathbb EZ=S`$. For $`z\ge0`$ and $`v=\alpha\log2>0`$,
``` math
\frac{2^{\alpha z}}{2^\alpha-1}
 \ge\frac{e^{(z-1)v}}v\ge e(z-1)\quad(z>1);
```
for $`0\le z\le1`$ the claimed lower bound is nonpositive. This proves $`\Psi(2^z)\ge e(z-1)`$ without an unstated minimisation. For the upper bound, use the single frame, $`z=1/S`$, and $`\alpha=\log_2(1+z)`$; its exact positive expansion has cost
``` math
\frac1{qz}\prod_{p\in P}(1+z/p)\le\frac{eS}q.
```
Thus the optimised cost is asymptotically $`eS/q`$.

<a id="arithmetic-sampling-and-logarithmic-cost."></a>

#### Arithmetic sampling and logarithmic cost.

The cube-family upper bound is specific to that family. To state the limitation, let $`F`$ be finite and nonempty, put $`Q=\operatorname{lcm}(F)`$, and use natural logarithms to define
``` math
\kappa_1(F;t)=\min\left\{\sum_{d\mid Q}\frac{c_d}{d}:c_d\ge0,\quad
 \log(1+f_F(s)/t)\le\sum_{d\mid s}c_d\quad(s\mid Q)\right\},
 \qquad 0<t\le1.
```
Write $`U_F(N)=\sum_{r\ge1}2^{-r}f_F(N+r)`$ and let $`\mathbb P_L`$ be uniform sampling of $`N=Lm`$ over a complete period. Here $`K_*(F)`$ is the infimum of the cost $`K`$ above over all finite or countable fractional covers of $`F`$, including the choice of frames, exponents and positive weights. The arithmetic form of the cover lower bound is
``` math
K_*(F)\ge\max_{\ell\mid Q}
     \mathbb P\bigl(U_F(N)>1\mid\ell\mid N\bigr),
```
with $`N`$ uniform modulo $`Q`$. Indeed, every cover gives $`\mathbf1_{\{U_F>1\}}\le\sum_{j,d}\eta_j^{-\alpha_j}c_{j,d}w_{2^{\alpha_j},d}`$. Apply <a href="#eq:mixed-finite-kernel" data-reference-type="eqref" data-reference="eq:mixed-finite-kernel">[eq:mixed-finite-kernel]</a>, first let $`R\to\infty`$ with $`L,M`$ fixed, then let $`M\to\infty`$, and finally take the infimum over covers.

For every integer $`H\ge2`$ and cutoff $`A_0\ge0`$, there are a squarefree $`L`$ and a finite nonempty set $`F`$ of distinct squarefree exponents with
``` math
\min F>\max\{L,A_0\},\qquad
 \kappa_1(F;1)\le\frac{30\log2}{H},\qquad
 \mathbb P_L(U_F>1)\ge1-e^{-1}.
```
For these examples $`L\mid Q`$, so $`K_*(F)\ge1-e^{-1}`$. Parent primes and disjoint tag primes encode all subsets by least common multiples; on multiples of $`L`$ many divisor conditions become automatic, while the remaining tag events are independent. Their incidence is exponential in the number of successful tags, although its logarithmic majorant pays only linearly. Complete-period approximation then gives $`\mathscr D_{L;R,L}\mathbf1_{\{U_F>1\}}>1/2`$ for sufficiently large $`R`$. Thus neither $`K_*(F)\le C\kappa_1(F;1)`$ nor $`\mathscr D_{L;R,M}\mathbf1_{\{U_F>t\}}\le C(1+L/M)\kappa_1(F;t)`$ holds with an absolute $`C`$.

Ordinary initial intervals nevertheless satisfy
``` math
\frac1X\#\{1\le N\le X:U_F(N)>t\}
 \le\frac{2}{\log(4/3)}\kappa_1(F;t)
 \qquad(X\ge1,\ 0<t\le1).
```
The complete construction and proofs are in the companion record, Section *Logarithmic cost under arithmetic sampling*, and \[endpoint2026, Theorem 1, Corollary 3 and Proposition 4\]. These are ordinary arguments, without independent review or fresh Lean verification. The $`L=1`$ bound cannot replace a uniform arithmetic bound when a finite initial support must be frozen. The finite-functional separation neither refutes <a href="#eq:mixed-finite-kernel" data-reference-type="eqref" data-reference="eq:mixed-finite-kernel">[eq:mixed-finite-kernel]</a> nor compares the infinite-support irrationality classes.

The fixed-base Lambert object and its strict-tail geometry already occur in Kovač–Tao \[kovactao, Section 2.1.2 and Remark 4.1\]. Van Doorn–Kovač’s lacunary reciprocal-sum results concern finite representations in a freely chosen denominator sequence \[vandoornkovac, Theorem 1, Lemma 4 and Corollary 5\]; that distinct setting supplies no fixed-base rational-membership conclusion here.

The proposed cover-only host $`A^\star`$ is not established by the arguments here. In the reverse direction, the release snapshot contains [an end-to-end weighted non-cover host declaration](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos257/PaperCompleteR8/AnalyticSeparationReturn.lean#L16), with transport to the literal strengthened-cover predicate, rather than only a differently typed logarithmic obstruction. This corrects the source-availability record; it is not a fresh Lean verification or a proof here of two-way incomparability. This infinite-host statement is separate from the finite-functional separation above.

<a id="combining-the-two-support-criteria"></a>

## Combining the two support criteria

Separate small-displacement witnesses need not occur at the same index. For example, a sequence small only at even indices and one small only at odd indices need never have a small sum. The useful feature of (S) is its uniformity in the moving modulus: the positive-cover argument can use the exact observation window selected by the weighted proof.

<div id="res:mixed-supports" class="theorem">

**Theorem 5** (mixed weighted and cover supports). *Suppose $`E`$ has finite weighted mass <a href="#eq:weighted-return" data-reference-type="eqref" data-reference="eq:weighted-return">[eq:weighted-return]</a> for a finite nonempty prime set $`P`$, and $`V`$ admits a strengthened positive cover <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a>, or its positive-weight variant above. Then $`X_A(b)`$ is irrational for every infinite $`A\subseteq E\cup V`$ and every integer $`b\ge2`$.*

</div>

<div class="proof">

*Proof.* Fix $`\varepsilon>0`$ and an integer $`N_0\ge1`$, and put $`\rho=\varepsilon/3`$. Use the cover notation $`B_j,U_j,V_j`$ above, with $`\eta_j=2^{-j}`$ in the case <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a>. Set $`t_j=\rho\eta_j`$ and choose $`J`$ so that
``` math
K_J=\sum_{j>J}\frac{C_jt_j^{-\alpha_j}}{B_j-1}<\frac1{16}.
```
Choose a finite $`F\subseteq E`$ whose complementary weighted mass is $`\kappa<\rho/16`$. Let $`L`$ be a positive common multiple of $`N_0`$, all members of $`F`$, and all members of the first $`J`$ cover frames. For large $`H`$, take exactly the binary weighted schedule
``` math
Q=L\prod_{p\in P}p^{\lfloor\log_pH\rfloor},\qquad
 G=\lfloor H/\max P\rfloor,\qquad M=\lfloor2^{G/2}\rfloor.
```
The finite estimate <a href="#eq:weighted-main-bound" data-reference-type="eqref" data-reference="eq:weighted-main-bound">[eq:weighted-main-bound]</a>, with tail budget $`\kappa`$, remains valid for this $`L`$: its proof requires only that $`L`$ freeze $`F`$. It also applies to finite or empty $`E`$, since positivity was used only after the averaging estimate. Thus
``` math
\mathscr D_{Q;M,M}(\Delta_{2,E}/\rho)<\frac18
```
for sufficiently large $`H`$. For the same finite distribution, (S) and nonnegative interchange give
``` math
\mathscr D_{Q;M,M}S_J\le(1+4Q/M)K_J<\frac18,
 \qquad S_J=\sum_{j>J}t_j^{-\alpha_j}V_j,
```
because $`Q/M\to0`$. Hence some sample $`N=Qm`$ satisfies $`\Delta_{2,E}(N)/\rho+S_J(N)<1`$. At this one index the weighted displacement is below $`\rho`$ and every unfrozen cover frame has $`U_j(N)<t_j`$. Therefore
``` math
\Delta_{2,A}(N)\le\Delta_{2,E}(N)+\Delta_{2,V}(N)<2\rho<\varepsilon,
 \qquad N\ge Q\ge L\ge N_0.
```
Overlaps between the supports only improve the inequality. Infinitude of $`A`$ makes its displacement positive. The atom comparison used in the cover proof transfers arbitrarily small displacements to every integer base; the fixed rational lattice then excludes rationality. ◻

</div>

This is a complete ordinary proof. It does not establish the unavailable constructions $`A_W,A^\star`$ or strict enlargement over both individual classes. Those separation claims retain the boundary stated above.

With arbitrary positive cover weights, the class of subsets of such mixed hosts is closed under finite unions and finite changes. For weighted supports use the union of the two finite prime sets: the prime part grows and $`h/(2^h-1)`$ decreases. For two covers, interleave their frames with weights $`\eta_j/2`$ and $`\theta_j/2`$; the total cost grows by at most two, since $`2^{\alpha_j}\le2`$. Subsets inherit the same hosts, and finite sets have finite weighted mass. This argument uses the positive-weight variant; it does not silently reindex the dyadic weights in (V). Countable unions require a tail budget. Every prime singleton is admitted, but for the full prime support $`\mathcal P`$ one has $`\Delta_{2,\mathcal P}(N)>1/3`$ for every $`N\ge1`$: indeed $`\sum_{r\ge1}2^{-r}\omega(N+r)\ge1`$, whereas $`X_{\mathcal P}(2)\le\sum_{a\ge2}(2^a-1)^{-1}<2/3`$. Here $`\omega(n)`$ is the number of distinct prime divisors of $`n`$. The reciprocal-summable class is contained in the weighted class, since $`h/(2^h-1)\le1`$. Theorem <a href="#res:reciprocal-support" data-reference-type="ref" data-reference="res:reciprocal-support">2</a> supplies the direct proof of that baseline case.

<a id="the-prime-power-regime."></a>

#### The prime-power regime.

A further claimed extension would give irrationality for every infinite subset of the prime powers, at every integer base, including fixed dilations and finite modifications. Its intended analytic input is Tao–Teräväinen \[taoteravainen2025, Theorem 3.1, p. 24\]. The argument would use the reciprocal mass of the selected primes as its scale, so arbitrarily slow divergence is retained; higher prime powers produce errors only on prime-square events. The equidistribution, small-prime, progression and exceptional-set hypotheses are referred to a supplement that is not in this checkout. Tao and Teräväinen prove the full-prime case at base $`2`$ \[taoteravainen2025, Theorem 1.3, p. 4\], and in the paragraph after it state that the method extends to every integer base and to the full prime-power support, leaving the details to the reader. No arbitrary thinning argument is promoted from this release.

The actual greedy membership problem is treated in Section <a href="#sec:actual-repairs" data-reference-type="ref" data-reference="sec:actual-repairs">8</a>; its repair inequality has a different logical role from the sufficient irrationality criteria above.

<a id="sec:period"></a>

# Finite-support denominator periods

For a finite nonempty $`F\subseteq\mathbb{N}_{>0}`$, let $`D_F`$ be the positive reduced denominator of $`x_F(b)=\sum_{n\in F}(b^n-1)^{-1}`$. We use $`\operatorname{ord}_1(b)=1`$.

<div id="res:period" class="theorem">

**Theorem 6** (finite-period noncollapse). *Let $`F\subseteq\mathbb{N}_{>0}`$ be finite and nonempty, let $`b\ge2`$ be an integer, and let $`D_F>0`$ be the denominator of $`x_F(b)`$ in lowest terms. Then $`D_F`$ is coprime to $`b`$, and
``` math
\operatorname{ord}_{D_F}(b)=\operatorname{lcm}\{n:n\in F\}.
```
If moreover $`\operatorname{lcm}(F)\ge2`$, then $`\operatorname{lcm}(F)<D_F`$. We use $`\operatorname{ord}_1(b)=1`$, so the statement includes $`F=\{1\}`$ at $`b=2`$.*

</div>

Coprimality is [base coprimality of the reduced denominator](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L5221), the order statement is [the exact multiplicative order](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L5246), and the size bound is [the strict denominator inequality](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L5260). The three clauses are the CertificateKernel declarations just cited; `PaperCompleteR7/Assemblies.lean` is not in this checkout.

Put $`L=\operatorname{lcm}(F)`$. Clearing denominators gives $`D_F\mid b^L-1`$, so the upper divisibility for the order is immediate. For the reverse, choose $`n\ge2`$ maximal under divisibility in $`F`$ and a prime $`\ell\mid\Phi_n(b)`$. If $`e=v_\ell(b^n-1)`$, the full prime power $`\ell^e`$ has $`\operatorname{ord}_{\ell^e}(b)=n`$. Every other selected exponent $`m`$ has $`n\nmid m`$, hence $`v_\ell(b^m-1)<e`$. The $`n`$th summand has uniquely smallest $`\ell`$-adic valuation and cannot cancel. Thus $`\ell^e\mid D_F`$ and $`n\mid\operatorname{ord}_{D_F}(b)`$. Taking all maximal selected exponents proves the order statement; the size bound follows from $`\operatorname{ord}_{D_F}(b)\mid\varphi(D_F)<D_F`$ when $`L\ge2`$. The case $`F=\{1\}`$ has order one directly.

The same unique-valuation argument permits any signs $`\pm1`$ on the finite summands; that signed extension is ordinary in this note (`SignedFinitePeriodNoncollapse.lean` is not in this checkout). The required cyclotomic prime-power fact is proved in Appendix <a href="#app:elementary-details" data-reference-type="ref" data-reference="app:elementary-details">10</a>; no unavailable supplement is needed for this argument. The distinction between primes and prime powers is visible in
``` math
X_{\{2,3\}}(2)=\frac{10}{21},\qquad
 X_{\{2,6\}}(2)=\frac{22}{63}.
```
Both denominators have order six. The first combines orders two and three, while the second retains the order-six prime power $`9`$; no prime divisor of $`63`$ itself has order six. The boundary $`F=\{1\}`$ at base two has $`D_F=L=1`$. These lower denominator bounds give no upper height control for infinite partial sums and do not decide an infinite-support value. By contrast, Van Assche constructs approximants for the full Lambert series and proves both nonvanishing and decay of the associated integer linear forms \[vanassche2001, Lemma 1 and (34)–(35)\]. That approximation mechanism does not follow from denominator survival alone.

<a id="sec:forced"></a>

# Rational values and scaled tails

The displacement identity gives a fixed arithmetic lattice under rationality. Its recurrence is
``` math
z_{N+1}=2z_N-vc_A(N+1),\qquad
 z_N=v\sum_{r\ge1}c_A(N+r)2^{-r}\in\mathbb{Z}
```
when $`X_A(2)=p/v`$. The sequence $`c_A`$ is determined by one Boolean selector.

Two elementary facts explain why size information alone has little force here. If $`a_0=\min A`$, every $`a_0`$ consecutive integers contain a multiple of $`a_0`$, so a divisor-incidence zero window has length at most $`a_0-1`$. If $`A`$ is infinite, choose $`k`$ exponents and a common multiple $`L`$; then $`c_A(L)\ge k`$ and $`T_{L-1}^{(2)}\ge k/2`$. Both facts hold without rationality. The arithmetic information lies in the lattice and in the compatibility of all coefficients with the same selector.

Precisely, Dirichlet convolution gives $`\mu*c_A=\mathbf1_A`$, where $`\mu`$ is the Möbius function. A putative recurrence with integral forcing must therefore satisfy $`(\mu*c_A)(n)\in\{0,1\}`$ for all $`n`$. The complete Boolean–Möbius scaled-tail correspondence and its finite example are retained in the long record, under *Exact descriptions of a rational-valued support* (Theorem `thm:bmc`). The correspondence permits finite supports; infinitude remains a separate requirement for a counterexample to Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">3</a>.

<a id="sec:map"></a>

# Where the return mechanism stops

The preceding criteria establish irrationality through small positive returns. This mechanism already fails at the full support:
``` math
\Delta_{2,\mathbb{N}_{>0}}(N)
 >(2^N-1)\sum_{a>N}2^{-a}=1-2^{-N}\ge\frac12
 \qquad(N\ge1).
```
The full-support value is nevertheless [irrational](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L8328) \[erdos1948\]. A universal proof must therefore control arithmetic behaviour beyond small returns.

The distinction also appears in the squarefree support. Its series is irrational at every base $`2^j`$, $`j\ge1`$, by Corollary 1.2 and Example 1.1 of Duverney and Tachiya \[duverneytachiya, p. 4\]. Their corollary covers the $`s`$-free products of any pairwise coprime sequence of polynomial growth, and they present it as support for the conjecture of Erdős and Graham stated here as Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">3</a>. The zero-window obstruction for one normalised certificate scheme concerns that scheme’s hypotheses. It gives no obstruction to irrationality of the value. The precise normalisation counterexamples are retained in the long record, together with the complete catalogue of known support families.

A separate sufficient condition family is stated in terms of growth alone. Erdős proved irrationality of $`\sum_n1/a_n`$ for increasing integers with $`a_n>n^{1+\tau}`$ for some $`\tau>0`$ and all large $`n`$, together with $`\limsup_na_n^{1/2^n}=\infty`$ \[erdos1975, Theorem 1, p. 1\]. At $`a_n=2^{c_n}-1`$ the polynomial hypothesis is automatic, since $`c_n\ge n`$ gives $`a_n\ge2^n-1`$, and $`\log_2(2^{c_n}-1)`$ differs from $`c_n`$ by at most $`1`$, so the growth hypothesis reduces to $`\limsup_nc_n/2^n=\infty`$. The criterion therefore proves irrationality, at every integer base, for every support with $`\limsup_nc_n/2^n=\infty`$. That class and the reciprocal-summable class of Theorem <a href="#res:reciprocal-support" data-reference-type="ref" data-reference="res:reciprocal-support">2</a> are incomparable. The squares are reciprocal summable, and $`c_n=n^2`$ gives $`c_n/2^n\to0`$. In the other direction, take blocks of consecutive integers, the $`k`$th block being the $`4^{n_k}`$ integers from $`4^{n_k}`$ to $`2\cdot4^{n_k}-1`$ starting at index $`n_k`$, with $`n_{k+1}=n_k+4^{n_k}`$; then $`c_{n_k}/2^{n_k}=2^{n_k}\to\infty`$ while each block contributes reciprocal mass tending to $`\log2`$, so $`\sum_{a\in A}1/a`$ diverges. The extension of this lane to products of consecutive terms \[bkkkz2026\] settles Erdős Problem 1051 at the golden-ratio exponent and adds nothing beyond the $`d=1`$ case used above. Its rational-valued counterexamples are built by interval filling, which selects each term from a full discrete interval $`[\beta_n,\gamma_n]\cap\mathbb{N}`$ with $`\beta_n/\gamma_n\to0`$, so that consecutive choices differ by one and the attainable sums cover an interval. The strict tail inequality of Section <a href="#sec:geometry" data-reference-type="ref" data-reference="sec:geometry">7</a> makes the Mersenne achievement set totally disconnected, so no interval is ever attained and interval filling is unavailable here, on terms and on exponents alike. This excludes that construction here and does not decide the problem.

A related independence boundary concerns prime-incidence arguments. Writing $`f_A(n)=\sum_{a\in A}{\bf1}_{a\mid n}`$, the local identity
``` math
f_A(an)-f_A(n)=1-{\bf1}_{a\mid n}\quad(n\ge1)
```
for a fixed $`a\in A`$ holds exactly when $`a`$ is coprime to every other member of $`A`$. To see this, every summand $`\mathbf1_{t\mid an}-\mathbf1_{t\mid n}`$ is nonnegative. The term $`t=a`$ is the displayed right side; all others vanish if $`(a,t)=1`$. Conversely, if $`g=(a,t)>1`$ for some $`t\ne a`$, then $`n=t/g`$ gives an additional positive term, contradicting the identity. Already for the dilated prime support $`2\mathcal P`$,
``` math
\operatorname{Cov}({\bf1}_{2p\mid n},{\bf1}_{2q\mid n})
 =\frac1{4pq}\qquad(p\ne q\text{ odd primes}),
```
where covariance is taken over a common arithmetic period: the joint mean is $`1/(2pq)`$ and the product of the means is $`1/(4pq)`$. Thus multiplicative size conditions alone do not supply the independence used by the prime argument. These are elementary ordinary calculations.

<a id="sec:geometry"></a>

# Unique coding and arithmetic membership

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
shows that every represented value has a unique selector. The middle inequality follows by writing $`w_n=2^{-n}+4^{-n}/(1-2^{-n})`$ and using $`n\ge N+1\ge2`$. Since every weight exceeds its tail, Hornich’s theorem \[hornich1941\], as proved by Nitecki \[nitecki2013, Theorem 4(1), p. 9\], shows that the coding image is a Cantor set of measure $`\lim_N2^NR_N`$; the estimate above gives $`2^NR_N\to1`$, so $`\lambda(\mathcal A)=1`$. Kovač–Tao record this strict-tail inequality and the Cantor conclusion in the fixed-base setting \[kovactao, Remark 4.1\]. The long record proves the restricted-volume dichotomy and records the formula $`\dim_H\mathcal A_J=\liminf_N\#(J\cap[1,N])/N`$, together with the periodic-stride measure refinements. For a specified rational target, the useful consequence here is uniqueness of its possible selector.

<a id="sec:actual-repairs"></a>

# The actual greedy return inequality

For $`x\ge0`$, the greedy rule starts with $`r_0=x`$ and, at rank $`n\ge1`$, selects $`n`$ when $`r_{n-1}\ge(2^n-1)^{-1}`$, subtracting that weight if selected. Let $`A_x`$ be the resulting support and $`c_x(n)=\#\{a\in A_x:a\mid n\}`$. Set
``` math
P_0=0,\qquad P_{N+1}=2P_N+c_x(N+1),\qquad
 Q_N=\lfloor2^Nx\rfloor-P_N.
```
The nonnegative integer defect obeys
``` math
\begin{equation}
 Q_{N+1}=2Q_N+\beta_N-c_x(N+1),\qquad
 \beta_N=\lfloor2^{N+1}x\rfloor-2\lfloor2^Nx\rfloor\in\{0,1\}.
 \label{eq:actual-repair-recurrence}
\end{equation}
```

<div id="res:general-repair" class="theorem">

**Theorem 7** (general greedy repair criterion). *For every real $`x\ge0`$, the following are equivalent:
``` math
\begin{gathered}
 x\in\mathcal A;\\
 \forall K\ge0\ \exists N\ge K:\quad Q_{N+1}\le Q_N;\\
 \forall K\ge0\ \exists N\in[K,K+2\lfloor\sqrt K\rfloor+12):
 \quad Q_{N+1}\le Q_N.
 \end{gathered}
```*

</div>

The following is an ordinary proof. The supplied solution wrapper `Solutions/PalomarCorpus/E257/GeneralRepairCriterion.lean` contains the two named equivalences, with explicit bridges to the challenge definitions and the same square-root window. Its provenance is the separate release `52f29ad173b0`. This static comparison is not a new replay; a challenge declaration alone is not cited as a proof.

<div class="proof">

*Proof.* Strict domination of each Mersenne weight over its tail implies that a represented target is recovered by the greedy rule. For such a target,
``` math
0\le Q_N\le\sum_{r\ge1}c_x(N+r)2^{-r}
 \le2\sqrt N+4,
```
since $`c_x(n)\le\tau(n)\le2\sqrt n`$ and $`\sqrt{N+r}\le\sqrt N+\sqrt r\le\sqrt N+r`$. Put $`s=\lfloor\sqrt K\rfloor`$ and $`T=2s+12`$. Strict increase at all $`T`$ steps would imply $`Q_{K+T}\ge T`$. But $`K+T<(s+4)^2`$ gives $`Q_{K+T}<2s+12=T`$. This proves the window condition and hence cofinal nonincreases.

Conversely, if $`x\notin\mathcal A`$, then $`\delta=x-X_{A_x}(2)>0`$. The Lambert prefix is at most $`2^NX_{A_x}(2)`$, so $`Q_N\ge2^N\delta-1`$. Eventually this exceeds $`c_x(N+1)\le N+1`$. Equation <a href="#eq:actual-repair-recurrence" data-reference-type="eqref" data-reference="eq:actual-repair-recurrence">[eq:actual-repair-recurrence]</a> then makes $`Q_N`$ strictly increasing, contradicting cofinal nonincreases. ◻

</div>

The explicit square-root estimate is uniform in the target. The ordinary subpower refinement replaces its window length by $`\lceil C_\varepsilon(K+1)^\varepsilon\rceil`$ for every $`0<\varepsilon<1`$, using $`\tau(n)=O_\delta(n^\delta)`$. This changes the permissible deadline without proving any occurrence for a specified target.

The supplied release source `Solutions/PalomarCorpus/E257/GeneralRepairCriterion.lean` contains the cofinal-repair and square-root-window equivalences after explicit definition bridges. This is a static statement match, not a fresh replay. The subpower refinement above remains an ordinary argument; it is not identified with that square-root declaration.

At $`x=1/2`$, the digits $`\beta_N`$ vanish for $`N\ge1`$; at $`x=1/21`$ they are six-periodic. Thus the unresolved arithmetic input is
``` math
\begin{equation}
 \boxed{\quad
 \forall K\ \exists N\ge K:\qquad
 c_x(N+1)\ge Q_N+\beta_N,
 \qquad x\in\{1/2,1/21\}.
 \quad}\label{eq:actual-selector-obligation}
\end{equation}
```
Both $`Q_N`$ and $`c_x`$ must arise from the same greedy selector. The long record retains exact counterexamples to fixed-multiplier repair schedules and the finite phase masks used to test them. Neither target is decided here.

<a id="sec:open"></a>

# Further questions

<a id="two-extension-tests."></a>

#### Two extension tests.

Small real-base returns alone do not reproduce the integer-base proof. For $`\beta=(3+\sqrt5)/2`$, $`u=\beta^{-1}`$, the finite prefix identity and an algebraic norm show that $`\Delta_{\beta,H}(N)(1+J_H(N;u))\to0`$ along a sequence would exclude $`X_A(\beta)`$ from $`\mathbb{Q}(\sqrt5)`$ for every infinite $`A\subseteq H`$. Here $`H=\{2^km:k\ge2,\ m\text{ odd},\ m\le2^{2^k}\}`$. The conjugate prefix is essential; the stated product estimate is unproved. The accompanying research note gives the finite norm calculation and isolates the remaining off-diagonal terms.

A different extension requires squarefree remote-tail control and a weighted displacement to be small at the same indices. CRT establishes compatibility of the finite opening divisibility conditions, but not this simultaneous smallness. Neither extension is asserted as a theorem here.

The preceding arguments isolate two different tasks. For new irrational supports, one needs a summable or uniformly averaged control of the shifted divisor atoms, or an arithmetic functional that also detects supports whose positive displacements stay separated from zero. For a proposed rational target, one needs the actual-selector inequality <a href="#eq:actual-selector-obligation" data-reference-type="eqref" data-reference="eq:actual-selector-obligation">[eq:actual-selector-obligation]</a>; synthetic recurrences satisfying only growth and integrality conditions do not provide it.

<div id="res:one-over-twenty-one-frontier" class="theorem">

**Theorem 8** (fatal-branch quotient refinement at $`1/21`$). *The following statements hold.*

1.  *$`1/21\in\mathcal A`$ if and only if $`\mathcal F_{21}`$ does not hold.*

2.  *If there is an unbounded sequence of ranks $`R`$ with $`s_R\le 2^R`$, then $`1/21\in\mathcal A`$.*

3.  *On $`\mathcal F_{21}`$, eventually $`s_R>2^R`$, the boundary rank $`R+1`$ belongs to $`D_{R+1}`$, and $`(D_R,s_R)`$ follows one exact affine recurrence.*

</div>

The equivalence is [one div twenty one mem iff not fatal Aligned Branch](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L3507); the closed-row compactness step is [twenty One Cofinal Even Quotient Greedy Decay of closed Rows](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L5554); and the eventual affine regime is [twenty One Fatal Aligned Branch eventually affine supercapacity](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L5658). The denominator-specific separation theorem additionally proves that every closed Boolean quotient row is exactly the canonical quotient-greedy row ([twenty One Closed Row forces quotient Greedy](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L231)). An aligned crossing from saturation into strict supercapacity forces a missing canonical ancestor and a real skipped exponent ([ancestor hole](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L5179), [scaled skip](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L5223)).

<div id="res:terminalhalf" class="theorem">

**Theorem 9** (terminal scaled vanishing implies the half-value). *Let $`S`$ be a `HalfTerminalOnlyScaledVanishingSequence`: its finite words exclude ranks $`0`$ and $`1`$, their depths tend to infinity, and the absolute terminal carry divided by $`2^M`$ tends to zero along the depths $`M`$. Then there is an infinite set $`A\subseteq\mathbb{N}`$ with*

*``` math
\sum_{a\in A}\frac1{2^a-1}=\frac12.
```
Consequently the universal irrationality assertion in Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">3</a> is false under this hypothesis. This is a conditional implication, not a construction of $`S`$ and not a solution of Problem #257.*

</div>

<div id="res:cylinderhalf" class="theorem">

**Theorem 10** (cofinal cylinders imply an infinite half-support). *Suppose that for every $`N`$ there are $`M,K`$ with $`\max\{N,1\}\le M`$ and a nonempty `CylinderStage` $`K~M`$. Then there is an infinite set $`A\subseteq\mathbb{N}`$ with $`0\notin A`$ and*

*``` math
\sum_{a\in A}\frac{1}{2^a-1}=\frac12.
```
Thus the universal irrationality assertion in Problem #257 is false under this cofinal-stage hypothesis. The formal proof does not construct the cofinal family of full-cylinder stages.*

</div>

<div id="prob:one-over-twenty-one-membership" class="problem">

**Problem 11** (membership of 1/21 in the Mersenne achievement set). Prove cofinal crossings of the exact moving lower separatrix
``` math
2\,\operatorname{scaledGreedyRemainder}(1/21,N)
 <\operatorname{mersenneScale}(N+1).
```
Equivalently, exclude the explicit fatal/cofinite/aligned branch $`\mathcal F_{21}`$. It is sufficient either to contradict the eventual permanent affine-supercapacity recurrence forced by that branch or to force an unbounded sequence of closed canonical quotient rows; neither sufficient route is claimed to be equivalent by itself.

</div>

<div id="prob:scaled-return" class="problem">

**Problem 12** (weakest native recurrence criterion). Does the scaled actual greedy remainder return cofinally to one bounded interval?
``` math
\exists B<\infty\ \forall K\ \exists N\ge K:
 \qquad 2^N r_N\le B.
```

</div>

<div id="prob:actual-invariant" class="problem">

**Problem 13** (actual-orbit invariant). Is there a finite-memory, $`2`$-adic or discrepancy invariant, using the correlated divisor pulses of the actual support, that forces a closed return or forbids permanent supercapacity? More precisely, can one use a bounded window of $`R\bmod6`$, residues of $`s_R`$, endpoint divisor counts and the finite set of eventual skips to force descent or a forbidden state? Alternatively, can one prove that no bounded-memory invariant distinguishes the true orbit from synthetic permanent-supercapacity controls?

</div>

<div id="prob:fatal-interval" class="problem">

**Problem 14** (final-skip Diophantine exclusion). Let $`E=\sum_{n\ge1}(2^n-1)^{-1}`$. If $`1/21\notin\mathcal A`$, let $`M`$ be the last skipped exponent, $`S_M`$ its finite skipped prefix, and
``` math
a_M=\frac1{21}+\sum_{d\in S_M}\frac1{2^d-1}.
```
Can the complete final-skip signatures be used to prove $`|E-a_M|\ge\operatorname{gap}_M`$, contradicting
``` math
0<a_M-E<\operatorname{gap}_M?
```

</div>

The logarithmic obstruction <a href="#eq:cover-log-obstruction" data-reference-type="eqref" data-reference="eq:cover-log-obstruction">[eq:cover-log-obstruction]</a> remains necessary for a finite-cost positive cover, but there is no uniform finite-functional comparison $`K_*(F)\le C\kappa_1(F;1)`$. This does not identify or compare the corresponding infinite-support irrationality classes. The mixed class is a finite-union ideal. Countable gluing needs an explicit tail budget: every prime singleton is admitted, while the full prime support has displacement greater than $`1/3`$ at every positive shift.

<a id="proof-and-verification-scope"></a>

# Proof and verification scope

The 1968 Erdős full text was not recovered in this pass. The historical attribution is retained from the supplied source trail, and its page references have not been upgraded to a fresh primary-text audit. The original Luca–Tachiya publisher PDFs and Hornich paper were likewise not fully retrieved; the exact statements used were checked in the identified later expositions. The source register records these differences. All proofs asserted in the body are ordinary mathematical arguments. Appendix <a href="#app:sources" data-reference-type="ref" data-reference="app:sources">11</a> maps selected statements to the supplied formal source snapshots. A declaration in a challenge file is not, by itself, a solution proof; the corresponding solution wrapper and its hypotheses must be inspected. Conversely, a missing old filename does not show that a later counterpart is absent. No Lean replay or new axiom audit was run for this revision.

The release snapshot also contains end-to-end bodies for the strengthened cover conclusion in [*PositiveCoverReturn*](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos257/PaperCompleteR8/PositiveCoverReturn.lean#L241) and for the weighted and mixed conclusions in [*WeightedReturn*](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L98). The arbitrary-positive-weight variants and the newly added logarithmic counterexample arguments are ordinary deductions here. No independent review of the new arguments or fresh Lean build is asserted.

The periodic support cases are attributed to Luca and Tachiya’s original periodic-sequence paper \[lucatachiya2014periodic\]; the precise statement used here was checked in their own later account \[lucatachiya2017, Theorem A and Example 2, pp. 139–140\]. The *Formal Conjectures* record \[formalconjectures257\] is statement-level prior art, not a proof dependency. Neither that record nor any result in this paper resolves arbitrary infinite support.

<a id="app:elementary-details"></a>

# Elementary details used in the proofs

<a id="cyclotomic-prime-power-fact."></a>

#### Cyclotomic prime-power fact.

Let $`b\ge2`$, $`n\ge2`$, $`\ell\mid\Phi_n(b)`$ be prime and $`e=v_\ell(b^n-1)`$. Then $`\operatorname{ord}_{\ell^e}(b)=n`$. Here is a proof including the exceptional $`2`$-adic behaviour. For odd $`\ell`$, put $`d=\operatorname{ord}_{\ell}(b)`$ and $`s=v_\ell(b^d-1)`$. The elementary lifting identity $`v_\ell(b^{dt}-1)=s+v_\ell(t)`$ follows by factoring a geometric sum when $`\ell\nmid t`$ and by a binomial expansion for a factor $`\ell`$. In the factorisation $`b^n-1=\prod_{r\mid n}\Phi_r(b)`$, subtracting these valuations over proper divisors gives
``` math
v_\ell(\Phi_n(b))=
 \begin{cases}s&n=d,\\1&n=d\ell^j,\ j\ge1,\\0&\text{otherwise.}\end{cases}
```
If $`n=d`$, no smaller positive exponent gives $`b^m\equiv1\pmod\ell`$. If $`n=d\ell^j`$, the full valuation is $`e=s+j`$; the same lifting identity shows that the least exponent giving valuation $`e`$ is $`d\ell^j=n`$. For $`\ell=2`$, $`b`$ is odd. Factoring $`b^{2t}-1`$ gives
``` math
v_2(b^{2^j}-1)=v_2(b-1)+v_2(b+1)+j-1\qquad(j\ge1).
```
The only possible indices $`n\ge2`$ are $`n=2^j`$: $`v_2(\Phi_2(b))=v_2(b+1)`$ and $`v_2(\Phi_{2^j}(b))=1`$ for $`j\ge2`$; all other indices have valuation zero. The displayed identity again makes $`2^j`$ the least exponent with the full valuation. This proves the fact. Finally $`\Phi_n(b)>1`$: each primitive $`n`$th root $`\zeta`$ satisfies $`|b-\zeta|>1`$, and their product is $`\Phi_n(b)`$.

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

<a id="app:sources"></a>

# Guide to the formal sources

The source annotations retain the historical public revisions and now also identify the release snapshot `52f29ad173b0`. Links produced by the standard note macros use `99f4bf47422a`; across this note and its long reasoning surface, fourteen paper-local coordinates link revision `f36a98bf3d3e`. These families are audited separately; a historical aggregate reference count is not asserted to be an exact inventory of this PDF.

The following source links are the public snapshot used by this note.

[finite period noncollapse](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L5091), [finite period noncollapse rat den](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L5246), [coprime base den finite Erdos Sum](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L5221), [lcm lt den finite Erdos Sum](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L5260). ([binary Coeff Series rational iff exists tempered Binary Orbit](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L426)). [exists unbounded shifted odd tail nat state of support fraction](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L2383). [support Coeff Zero Window length le eps logb add](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SublogDivisorCoverage.lean#L392). [one div odd Order le reciprocal Mass of support fraction](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L1480). [dyadic support fraction reciprocal Mass diverges or gt one](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L2210). [exists normalized support fraction iff exists boolean Mobius Carry](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L949). [irrational erdos Support Series univ](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L9045)\
([irrational erdos Support Series multiples](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L9103))\
[irrational rat Weight Series eventually Periodic](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L12811); above ([residue class](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L11672), [odd](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L11686)); [factorial support](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L6035)\
[powers-of-two support](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L6059)\
[factorial-support instance](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L6082)\
[powers-of-two-support instance](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L6090)\
[pairwise-coprime support](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L10776)\
[full-support irrationality](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L8328); ([lcm gap hypothesis fails full support](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L6272)). ([irrational or bpow mul eq int Cast int Weighted Erdos Series periodic](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L14175)). [card squarefree Divisors](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L94), [squarefree Incidence eq](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L111), [odd squarefree Incidence](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L140). ([squarefree Divisors eq image](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L71)), [the carry-aware no-go](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L274) [the digitwise no-go](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L292). [$`2^{\omega(n)}`$ incidence](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L314) [the shift iff](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L335). [for $`\omega`$](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L441) [for the shifted incidence](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L485). [irrational erdos Support Series of tail](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L9467) [irrational erdos Support Series tail of irrational](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L9476). [compact](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L656), [perfect](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1656), [totally disconnected](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1672), [nowhere dense](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1681), [of measure one](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L996). ([mem mersenne Achievement Set iff greedy survival](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1458)). ([three fourths not mem mersenne Achievement Set](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1784)). ([selected Mersenne Tail](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L20), [summable selected Mersenne Tail](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L24)). ([selected Mersenne Tail lt weight](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L30)), ([supported Mersenne Digit Value injective](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L54)), [digit strings vanishing off $`J`$](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L45) [restricted digit map](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L49), [supported digit set](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L63), [closed](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L66). [restricted achievement set](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L76); [the image theorem](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L79). [compact](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L90) [closed](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L96). [support restriction](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L103) [nowhere dense](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L112). [preperfect](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L120); [$`\mathcal A_J`$](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L150), [perfect](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L167). [controls digit terms](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L175), [the update formula](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L182). [exactly](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L203). [disjoint](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L262), [doubles the volume](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L286). [by definition](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L300). [multiplies the face volume by $`2^{|F|}`$](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L313) [gives $`2^{-|F|}`$](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L349). [supported Mersenne Achievement Set mono](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L358). [measure zero](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L368). [the formal dichotomy](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L397). [the greedy form](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L2583), [the terminal-bit form](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L126), [the skipped-rank form](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L213), [the fatal-gap equivalence](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFatalGapRightTail.lean#L781), [its transfer to non-membership](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFatalGapRightTail.lean#L787), [the finite-support exclusion](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L589). [the local row constructor](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L55). [the upper-half Boolean fill](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkippedCoreExactRow.lean#L228). [the strict-positivity theorem](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L32); [the cofinal-skip hypothesis](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L22), [the row fan-in](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L84). [the closed-set step](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCofinalExactRows.lean#L71). [forward endpoint theorem](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L97) [the checked equivalence](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L110). [achievement-set conclusion](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TerminalOnlyScaledVanishing.lean#L165), [infinite-support lift](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TerminalOnlyScaledVanishing.lean#L221). [rational half counterexample](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/HalfCounterexampleFrontier.lean#L31), [universal-claim refutation](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/HalfCounterexampleFrontier.lean#L39). [general band localization](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyTwoThirdsBand.lean#L88), [two-thirds band](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyTwoThirdsBand.lean#L127), [odd numerator bound](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyTwoThirdsBand.lean#L231). [integral safety](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyTwoThirdsBand.lean#L185). [forced carry supply](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SupportSunflowerDichotomy.lean#L531) [irrationality endpoint](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SupportSunflowerDichotomy.lean#L540). [uniform tail selector](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SupportSunflowerDichotomy.lean#L406). [exact dilation identity](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CompositeDilationDefect.lean#L30). [prime-support no-defect](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CompositeDilationDefect.lean#L103), [prime specialization](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CompositeDilationDefect.lean#L119). [foreign-divisor classification](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CompositeDilationDefect.lean#L133) [defect bound](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CompositeDilationDefect.lean#L151). ([two-six witness](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CompositeDilationDefect.lean#L218)). [terminal-only bridge](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L264), [infinite half-support](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L277), [positive-support lift](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L287). ([identity](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MobiusSignSupportNoGo.lean#L111), [bound](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MobiusSignSupportNoGo.lean#L150)). [the formal theorem](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/HalfCounterexampleFrontier.lean#L61). ([exists primitive23 solution of eleven le](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/Primitive23Multiplicity.lean#L52)), ([no primitive23 solution ten](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/Primitive23Multiplicity.lean#L26)). ([rank eleven](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/Primitive23Multiplicity.lean#L38), [multiples of ten](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/Primitive23Multiplicity.lean#L86)). [mersenne Achievement Set eq scaled Greedy Trap](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyTrapDynamics.lean#L262), [scaled Greedy Remainder tendsto at Top of not mem](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyTrapDynamics.lean#L189), [mem mersenne Achievement Set iff scaled Remainder cofinally Bounded](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyTrapDynamics.lean#L225). [rat mem mersenne Achievement Set iff scaled Lower Branch Cofinally](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyTrapDynamics.lean#L152), [one div twenty One mem iff scaled Lower Branch Cofinally](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyTrapDynamics.lean#L283). ([twenty One Greedy Defect add mod div eq scaled remainder add tail](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L2117)). ([support](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L32), [remainder](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L39)). [one div twenty one mem iff not fatal Aligned Branch](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L3507); [twenty One Cofinal Even Quotient Greedy Decay of closed Rows](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L5554); [twenty One Fatal Aligned Branch eventually affine supercapacity](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L5658). ([twenty One Closed Row forces quotient Greedy](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L231)). ([ancestor hole](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L5179), [scaled skip](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L5223)). ([one div twenty One mem iff scaled Remainder cofinally Bounded](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyTrapDynamics.lean#L275)). ([sufficient condition](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L2843)) ([twenty One Greedy Defect add six](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L1892)). [the exact equivalence](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L1927). [an exact one-sided approximation](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L3735). ([order identity](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L3569), [lower bound](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TwentyOneQuotientGreedy.lean#L3583)).

<div class="thebibliography">

99 D. Duverney and Y. Tachiya, [*Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf), Forum Math. 31 (2019), no. 6, 1557–1566, [DOI](https://doi.org/10.1515/forum-2018-0299). Page numbers refer to the linked author preprint. Theorem 1.1 (pp. 2–3) is the refined Chowla–Erdős criterion; its proof in Section 2 (pp. 5–7) selects an index by minimising a local coefficient mass along an arithmetic progression, (2.3)–(2.9). Corollary 1.2 gives the general $`F_s(E)`$ theorem and its monomial images under $`|q|\operatorname{lcm}(1,\dots,\ell)\le s`$, and at every integer base when $`s=\infty`$; Example 1.1 gives the joint squarefree family at all bases $`2^j`$, $`j\ge1`$. Both are on p. 4, which also relates Corollary 1.2 to the conjecture of Erdős and Graham; the proof of Corollary 1.2 is on pp. 10–11. H. Kaneko, Y. Suzuki, and Y. Tachiya, [*Refinements of Erdős’s irrationality criterion for certain sparse infinite series*](https://arxiv.org/abs/2601.20743v1), arXiv:2601.20743v1 (2026). The averaged tail $`R_c(q,x,z)`$, a sum over offsets $`j\ge z`$, is (1.7) and Theorem 1 is on p. 3; its rational-integer form, Theorem 3, is on p. 5. Lemma 1 (pp. 6–7) derives irrationality from arbitrarily small nonzero scaled tails, and Lemma 2 (pp. 7–8) shows that most scaled tails in a range are small under a counting condition on the support. Their criteria assume sparse coefficient supports. T. Tao and J. Teräväinen, [*Quantitative correlations and some problems on prime factors of consecutive integers*](https://arxiv.org/abs/2512.01739v2), arXiv:2512.01739v2 (submitted December 2025, revised April 2026). Theorem 1.3 (p. 4) proves $`\sum_{n\ge1}\omega(n)/2^n=\sum_p(2^p-1)^{-1}`$ irrational, settling the prime-support case of \#257 at base $`2`$; the paragraph after it states that the method extends to every integer base and to the prime-power support, leaving the modifications to the reader. Theorem 3.1 is on p. 24, and the proof of Theorem 1.3 is Section 5, pp. 44–56. V. Kovač and T. Tao, *On several irrationality problems for Ahmes series*, Acta Math. Hungar. 175 (2025), no. 2, 572–608, [DOI](https://doi.org/10.1007/s10474-025-01528-0). Page numbers refer to arXiv:2406.17593v4. Remark 4.1 (p. 13) records the strict tail inequality and the Cantor structure. Theorem 2.3 (p. 5; proof pp. 13–14) constructs rational merged sums from several bases under its mass hypothesis; the construction merges several bases and leaves fixed-base \#257 untouched. P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. 12 (1948), 63–66. The Formal Conjectures Authors, [*FormalConjectures.ErdosProblems.`257`*](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/257.lean), Lean source at commit `f776d2f`, 2025, accessed 13 September 2026. Its statement of the problem ends in `sorry`; the Lambert identity `tsum_top_eq` is proved there and the full-support irrationality variant `tsum_top` ends in `sorry`. P. Erdős, [*On the irrationality of certain series*](https://users.renyi.hu/~p_erdos/1969-09.pdf), Math. Student 36 (1968), 222–226 (issued 1969). The theorem on p. 222 treats pairwise-coprime support with convergent reciprocal sum at every integer base $`b\ge2`$; the claimed removal of pairwise coprimality is stated without proof. The same page says the reciprocal-sum condition could be replaced by a weaker but more complicated condition, and p. 226 suggests $`\sum_{n_i<x}1/n_i=o(\log\log x)`$ for pairwise coprime supports. P. Erdős, *Some problems and results on the irrationality of the sum of infinite series*, J. Math. Sci. 10 (1975), 1–7. Theorem 1 (p. 1) proves irrationality of $`\sum_k1/n_k`$ for increasing integers with $`\limsup_kn_k^{1/2^k}=\infty`$ and $`n_k>k^{1+\varepsilon}`$ for some $`\varepsilon>0`$ and all large $`k`$; Remark 4(4) of \[bkkkz2026\] restates it. K. Barreto, J. Kang, S.-H. Kim, V. Kovač, and S. Zhang, [*Irrationality of rapidly converging series: a problem of Erdős and Graham*](https://arxiv.org/abs/2601.21442v3), arXiv:2601.21442v3 (2026), to appear in Bull. London Math. Soc. Theorem 2 (pp. 2–3) settles Erdős Problem 1051 at the golden-ratio exponent and Theorem 5 (p. 5) shows the threshold is sharp; Remark 4(4) (p. 5) identifies the case $`d=1`$ of its Theorem 3 with \[erdos1975, Theorem 1\]; Lemma 14 (p. 13) is the interval-filling lemma. The paper does not treat Problem 257. Z. Nitecki, [*Subsum sets: intervals, Cantor sets, and Cantorvals*](https://arxiv.org/abs/1106.3779v2), arXiv:1106.3779v2 (2013). Theorem 4 (p. 9) shows that when every term exceeds its tail the subsum set is a Cantor set of Lebesgue measure $`\lim_n2^nX_n`$, where $`X_n`$ is the $`n`$th tail, and credits this to H. Hornich (1941). F. Luca and Y. Tachiya, [*Linear independence results for the values of divisor functions series*](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2014-14.pdf), RIMS Kôkyûroku No. 2014 (2017), 138–150. Theorem A (p. 139) restates Theorem 1.1 of their paper *Irrationality of Lambert series associated with a periodic sequence*, Int. J. Number Theory 10 (2014), no. 3, 623–636, [DOI](https://doi.org/10.1142/S1793042113501121): for a purely periodic integer sequence $`a(n)`$, not identically zero, $`\sum_{n\ge1}a(n)/(q^n-1)`$ is irrational for every integer $`q`$ with $`|q|>1`$. Example 2 (p. 140) treats the odd support. F. Luca and Y. Tachiya, *Irrationality of Lambert series associated with a periodic sequence*, International Journal of Number Theory **10** (2014), no. 3, 623–636. [doi:10.1142/S1793042113501121](https://doi.org/10.1142/S1793042113501121).

F. Luca and Y. Tachiya, *Linear independence of certain Lambert series*, Proceedings of the American Mathematical Society **142** (2014), no. 10, 3411–3419. [doi:10.1090/S0002-9939-2014-12102-2](https://doi.org/10.1090/S0002-9939-2014-12102-2).

W. Van Assche, *Little $`q`$-Legendre polynomials and irrationality of certain Lambert series*, The Ramanujan Journal **5** (2001), 295–310. [doi:10.1023/A:1012930828917](https://doi.org/10.1023/A:1012930828917); [arXiv:math/0101187v1](https://arxiv.org/abs/math/0101187v1).

H. Hornich, *Über beliebige Teilsummen absolut konvergenter Reihen*, Monatshefte für Mathematik und Physik **49** (1941), 316–320. [doi:10.1007/BF01707309](https://doi.org/10.1007/BF01707309).

*The logarithmic endpoint fails under arithmetic sampling*, AI-assisted ordinary proof note, 17 September 2026. Theorem 1, Corollary 3 and Proposition 4. Unpublished working note; independent review and fresh Lean verification are outstanding. W. van Doorn and V. Kovač, *Lacunary sequences whose reciprocal sums represent all rational numbers in an interval*, arXiv:2509.24971v3 (3 December 2025). <https://arxiv.org/abs/2509.24971v3>. Theorem 1 is on p. 2; Lemma 4 and Corollary 5 are on pp. 5–7.

</div>

*Companion system context.* The [claim and trust boundary](../../../paper/systems/claim-faithful-publication-systems-paper.pdf#nameddest=systems-trust), [cold-clone route to proof authority](../../../paper/systems/cold-clone-to-proof-receipt.pdf#nameddest=cold-clone-authority), and [public contribution protocol](../../../paper/systems/open-source-mathematics-strategy.pdf#nameddest=strategy-protocol) are described in sibling papers. Those descriptions do not change the mathematical status of this note.
