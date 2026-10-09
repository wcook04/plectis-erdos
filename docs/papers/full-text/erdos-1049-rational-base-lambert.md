<a id="erdos-1049-rational-base-lambert"></a>

# Hankel Determinants of Geometric Moments and Rational Lambert Values

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

For fixed $`0<q<1`$, we determine the asymptotic of Zudilin’s normalised Hankel determinants as their size $`N`$ grows, including the constant and the factor $`N^{-8F(1/q)}`$, where $`F(t)=\sum_{n\ge1}(t^n-1)^{-1}`$. A general theorem for positive geometric moments separates the node geometry from the weight product; two finite convolutions determine its power correction. Independently, Zudilin’s 2004 polynomial forms give irrationality of $`F(a/b)`$ for coprime $`a>b\ge1`$ with $`\log b/\log a<0.4056830213840605\ldots`$. This extends the sufficient region of Bundschuh and Väänänen and includes every positive integral power of $`31/4`$, but not $`3/2`$.

<a id="sec:problem"></a>

# Introduction

Fix $`q\in(0,1)`$. Write $`(z;q)_m=\prod_{j=0}^{m-1}(1-zq^j)`$ and $`F(t)=\sum_{n\ge1}(t^n-1)^{-1}`$ for $`t>1`$. At the auxiliary parameters $`x=z=1`$, the normalisation in \[zudilin2016, (6), §4\] gives
``` math
\begin{equation}
\label{eq:normalised-moments}
 v_m^*(q)=\sum_{t\ge0}q^{(m+1)t}
 \frac{(q;q)_m^3(q^{t+1};q)_m}{(q^{m+1+t};q)_{m+1}},
 \qquad V_N^*(q)=\det(v_{i+j}^*(q))_{0\le i,j<N}.
\end{equation}
```
The sums converge for $`0<q<1`$. They also define formal series, since the $`t`$th summand has $`q`$-order $`(m+1)t`$.

<div id="res:sharp-fixed-base" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/SharpFixedBaseShort.lean#L53">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1049-rational-base-lambert.md#res-sharp-fixed-base-comparator">Comparator</a></p>

**Theorem 1** (the size of $`V_N^*`$ at a fixed base). *Fix $`0<q<1`$ and write $`P=(q;q)_\infty`$, $`B_N=N(N-1)(2N-1)/6`$ and $`C_N=(N!)^2(N+1)!/2^N`$. There is a $`K(q)>0`$ with
``` math
V_N^*(q)\sim K(q)\,C_Nq^{B_N}P^{2N}N^{-8F(1/q)}
 \qquad(N\to\infty).
```*

</div>

The constant $`K(q)`$ is the convergent product in <a href="#eq:fixed-constant" data-reference-type="eqref" data-reference="eq:fixed-constant">[eq:fixed-constant]</a>. Zudilin proved $`\operatorname{ord}_q V_N^*\ge B_N`$ and the estimate $`|V_N^*|\le q^{N^3/3}\exp(O_q(N^2))`$ \[zudilin2016, Lemma 1 and §4\]. Theorem <a href="#res:sharp-fixed-base" data-reference-type="ref" data-reference="res:sharp-fixed-base">1</a> determines the factorial, exponential and power factors contained in this estimate. We also recover the exact first formal term $`C_Nq^{B_N}`$. The formal calculation fixes $`N`$ and expands at $`q=0`$; the asymptotic fixes $`q`$ and lets $`N`$ grow. Neither limit can be substituted for the other: multiplication by $`(1-q)^{N^3}`$ preserves the first formal term but changes the fixed-base logarithm by a cubic quantity. No uniformity as $`q\to1`$ is asserted.

The proof compares the moments with constant-weight geometric moments. We write $`v_m^*=\sum_{k\ge0}a_kq^{(m+1)k}`$ with $`a_k>0`$: the measure has mass $`a_kq^k`$ at $`q^k`$. Heine’s identity expresses the determinant as a positive sum of squared Vandermondes over choices of $`N`$ nodes \[zudilin2017det, §2, (2)–(5)\]. The first $`N`$ nodes normalise this sum but do not exhaust it; moving the last node gives a comparable contribution. Partitions encode all such displacements. For each fixed partition, only finitely many weight ratios change, at indices tending to infinity, so those ratios tend to $`1`$. A summable bound independent of $`N`$ then makes the whole normalised sum asymptotically independent of the weights. Cauchy’s determinant formula evaluates its limit in the constant-weight case.

The weights retain a different contribution. Their factorisation involves two-fold and three-fold convolutions of $`1/(q;q)_k`$, with relative corrections $`-2F(1/q)/(k+1)`$ and $`-6F(1/q)/(k+2)`$. In the logarithm of the weight product these give a harmonic sum, hence $`N^{-8F(1/q)}`$; the summable errors affect only the constant. Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">2</a> separates the determinant argument from this calculation and also treats entries $`(1-q^{i+j+1})^{-2}`$.

Chowla’s conjecture, recorded by Erdős \[erdos1988, p. 102\], asks whether $`F(t)`$ is irrational for every rational $`t>1`$. This is a related arithmetic question, and the fixed-base asymptotic alone does not answer it. In Section <a href="#sec:rational-base-irrationality" data-reference-type="ref" data-reference="sec:rational-base-irrationality">4</a> we instead specialise the polynomial forms of Zudilin’s 2004 construction \[zudilin2004, §5\]. They prove irrationality for coprime $`a>b\ge1`$ satisfying
``` math
\frac{\log b}{\log a}<\theta^*
 =0.4056830213840605\ldots,
```
where <a href="#eq:threshold-constants" data-reference-type="eqref" data-reference="eq:threshold-constants">[eq:threshold-constants]</a> defines $`\theta^*`$ exactly. The constants are inherited from Zudilin; the degree calculation after polynomial cancellation supplies the rational-base estimate. The resulting region includes every positive integral power of $`31/4`$, which lies outside the earlier sufficient region of Bundschuh and Väänänen \[bv1994, Theorem 2\]. Neither argument here settles $`3/2`$.

Sections <a href="#sec:geometric-moments" data-reference-type="ref" data-reference="sec:geometric-moments">2</a>–<a href="#sec:weights" data-reference-type="ref" data-reference="sec:weights">3</a> prove Theorem <a href="#res:sharp-fixed-base" data-reference-type="ref" data-reference="res:sharp-fixed-base">1</a>; Section <a href="#sec:rational-base-irrationality" data-reference-type="ref" data-reference="sec:rational-base-irrationality">4</a> gives the independent arithmetic argument. Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">5</a> links further questions to the companion. All logarithms are natural, empty products and determinants equal $`1`$, and constants in $`O_q(\cdot)`$ may depend on the fixed $`q`$.

<a id="sec:geometric-moments"></a>

# Geometric moment determinants

For constant weights, the moments are geometric series: $`M_m=\sum_{k\ge0}q^{(m+1)k}=(1-q^{m+1})^{-1}`$. Cauchy’s determinant formula evaluates their determinant exactly. Writing
``` math
P=(q;q)_\infty,\qquad
 \mathcal M(q)=\prod_{d\ge1}(1-q^d)^{-d},\qquad
 B_N=\sum_{j<N}j^2,
```
we obtain
``` math
\begin{equation}
\label{eq:cauchy-model}
 D_N^{(0)}:=\det\left(\frac1{1-q^{i+j+1}}\right)_{0\le i,j<N}
 =\frac{q^{B_N}\Delta_N}{\prod_{0\le i,j<N}(1-q^{i+j+1})},
 \qquad
 \Delta_N=\prod_{d=1}^{N-1}(1-q^d)^{2(N-d)}.
\end{equation}
```
For each fixed $`d`$, the multiplicity of $`1-q^d`$ in the denominator increases to $`d`$, giving the factor $`\mathcal M(q)`$ in the limit. The numerator supplies two more copies:
``` math
\frac{\Delta_N}{P^{2N}}
 =\prod_{d<N}(1-q^d)^{-2d}\prod_{d\ge N}(1-q^d)^{-2N}
 \longrightarrow\mathcal M(q)^2.
```
Indeed, $`\sum d|\log(1-q^d)|<\infty`$, and the logarithm of the second product is $`O_q(Nq^N)`$. Thus
``` math
\begin{equation}
\label{eq:cauchy-model-limit}
 D_N^{(0)}\sim\mathcal M(q)^3q^{B_N}P^{2N}.
\end{equation}
```
Replacing the constant weights by $`a_k`$ will contribute $`\prod_{k<N}a_k`$. The two hypotheses below do different jobs: the ratio limit handles each fixed displacement; the polynomial bound permits summation over all displacements.

<div id="thm:geometric-moments" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/GeometricUniversality.lean#L1324">Lean</a></p>

**Theorem 2** (geometric moment determinants). *Let $`0<q<1`$ and $`a_k>0`$ for $`k\ge0`$. Suppose that, for fixed constants $`C>0`$ and $`\kappa\ge0`$,
``` math
\begin{equation}
\label{eq:automatic-shift-bound}
 \frac{a_{k+h}}{a_k}\longrightarrow1\quad(k\to\infty)
 \text{ for each fixed }h\ge0,
 \qquad
 \frac{a_{k+h}}{a_k}\le C(1+h)^\kappa\quad(k,h\ge0).
\end{equation}
```
For $`M_m=\sum_{k\ge0}a_kq^{(m+1)k}`$ and $`D_N=\det(M_{i+j})_{0\le i,j<N}`$, we have
``` math
\begin{equation}
\label{eq:geometric-limit}
 D_N\sim\mathcal M(q)^3q^{B_N}P^{2N}\prod_{k=0}^{N-1}a_k
 \qquad(N\to\infty).
\end{equation}
```*

</div>

For every real $`s`$, the weights $`a_k=(k+1)^s`$ satisfy <a href="#eq:automatic-shift-bound" data-reference-type="eqref" data-reference="eq:automatic-shift-bound">[eq:automatic-shift-bound]</a> with $`C=1`$ and $`\kappa=\max(s,0)`$, and their first $`N`$ terms have product $`(N!)^s`$. Taking $`s=1`$ and summing the moments gives
``` math
\begin{equation}
\label{eq:squared-cauchy-example}
 \det\left(\frac1{(1-q^{i+j+1})^2}\right)_{0\le i,j<N}
 \sim\mathcal M(q)^3N!q^{B_N}P^{2N}.
\end{equation}
```
The polynomial bound excludes $`a_k=e^{\sqrt{k}}`$, although its adjacent ratio tends to $`1`$. The companion’s [ordinary ratio-limit argument](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-ratio-extension) allows $`a_{k+1}/a_k\to\rho\in(0,q^{-1})`$ and, at $`\rho=1`$, gives <a href="#eq:geometric-limit" data-reference-type="eqref" data-reference="eq:geometric-limit">[eq:geometric-limit]</a> without that bound. This broader claim remains unformalised and is not used here: the theorem and its applications retain both hypotheses in <a href="#eq:automatic-shift-bound" data-reference-type="eqref" data-reference="eq:automatic-shift-bound">[eq:automatic-shift-bound]</a>.

<div class="proof">

*Proof of Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">2</a>.* The bound $`a_h\le Ca_0(1+h)^\kappa`$ makes $`\sum_{k\ge0}a_kq^k\delta_{q^k}`$ a finite positive measure with moments $`M_m`$. Apply Cauchy–Binet to its finite truncations. The entries, hence the determinants, converge; the nonnegative tuple sums increase. Passing to the limit gives
``` math
\begin{equation}
\label{eq:heine-geometric}
 D_N=\sum_{0\le k_0<\cdots<k_{N-1}}
 \prod_{i<N}a_{k_i}q^{k_i}
 \prod_{i<j<N}(q^{k_i}-q^{k_j})^2.
\end{equation}
```
The tuple $`k_i=i`$ contributes $`q^{B_N}\Delta_N\prod_{i<N}a_i`$. It does not account for the whole asymptotic. For example, replace $`(0,1,\ldots,N-2,N-1)`$ by $`(0,1,\ldots,N-2,N)`$. The ratio of its contribution to that of the original tuple is
``` math
\begin{equation}
\label{eq:last-node-shift}
 q\frac{a_N}{a_{N-1}}
 \prod_{d=1}^{N-1}\left(\frac{1-q^{d+1}}{1-q^d}\right)^2
 =q\frac{a_N}{a_{N-1}}\left(\frac{1-q^N}{1-q}\right)^2
 \longrightarrow\frac{q}{(1-q)^2}.
\end{equation}
```
Only pairs involving the moved node change, and their product telescopes. At $`q=1/2`$ the displaced tuple is asymptotically twice as large as the normalising tuple.

Subtracting $`(0,1,\ldots,N-1)`$ gives the shifts $`\lambda_i=k_i-i`$. Since $`k_{i+1}\ge k_i+1`$, these are nonnegative and weakly increasing; reversing their order gives a partition. For $`N=4`$, for example,
``` math
\underbrace{(0,1,3,5)}_{(k_i)}
 \longmapsto\underbrace{(0,0,1,2)}_{(\lambda_i)}
 \longmapsto\underbrace{(2,1,0,0)}_{(\mu_j)}.
```
In general, put $`\mu_j=\lambda_{N-j}`$ for $`1\le j\le N`$, so that $`\mu_1\ge\cdots\ge\mu_N\ge0`$. Division by the contribution of $`k_i=i`$ turns the summand for this tuple into
``` math
\begin{equation}
\label{eq:partition-summand}
\begin{split}
 W_N(\mu)={}&q^{\sum_{j\le N}(2j-1)\mu_j}
 \prod_{j\le N}\frac{a_{N-j+\mu_j}}{a_{N-j}}\\
 &\hspace{2mm}\cdot\prod_{1\le j<k\le N}
 \left(\frac{1-q^{k-j+\mu_j-\mu_k}}{1-q^{k-j}}\right)^2.
\end{split}
\end{equation}
```
The $`j`$th index from the right enters once through the mass $`q^{k_i}`$ and twice through each of its $`j-1`$ pairs with later indices. This gives the exponent $`1+2(j-1)=2j-1`$. “Right” refers to increasing indices, not to the nodes $`q^{k_i}`$, which decrease towards zero.

Set $`W_N(\mu)=0`$ for partitions with more than $`N`$ positive parts, giving every sum the same index set. A fixed partition with $`\ell`$ positive parts affects only the last $`\ell`$ indices of $`(0,1,\ldots,N-1)`$. These indices tend to infinity while their displacements stay fixed, so the weight ratios in <a href="#eq:partition-summand" data-reference-type="eqref" data-reference="eq:partition-summand">[eq:partition-summand]</a> tend to $`1`$.

The Vandermonde quotient still contains a growing number of factors, but its dependence on $`N`$ telescopes. The factors with $`j<k\le\ell`$ are fixed, and those with $`j>\ell`$ equal $`1`$. For $`N\ge\ell`$ and each $`j\le\ell`$, the remaining factors satisfy
``` math
\begin{equation}
\label{eq:partition-tail}
 \prod_{k=\ell+1}^{N}
 \frac{1-q^{k-j+\mu_j}}{1-q^{k-j}}
 =\frac{(q^{N+1-j};q)_{\mu_j}}{(q^{\ell+1-j};q)_{\mu_j}}
 \longrightarrow\frac1{(q^{\ell+1-j};q)_{\mu_j}}.
\end{equation}
```
Thus each $`W_N(\mu)`$ has the same limit as for constant weights.

The fixed-partition limit does not yet control partitions whose length or parts grow with $`N`$. For a uniform bound, group the Vandermonde factors by $`j`$. Only $`j\le\ell`$ contribute; each group’s denominator product is at least $`P`$ and its numerator product at most $`1`$. The polynomial shift bound therefore gives
``` math
W_N(\mu)\le(CP^{-2})^\ell
 \prod_{j=1}^\ell(1+\mu_j)^\kappa q^{(2j-1)\mu_j}.
```
Let $`A=\sum_{u\ge1}(1+u)^\kappa q^{u-1}<\infty`$. Dropping the ordering of the positive parts, we obtain
``` math
\begin{align*}
 \sum_{\ell(\mu)=\ell}\sup_N W_N(\mu)
 &\le(CP^{-2})^\ell\prod_{j=1}^\ell
       \sum_{u\ge1}(1+u)^\kappa q^{(2j-1)u}\\
 &\le(CP^{-2}A)^\ell q^{\ell^2}.
\end{align*}
```
Here $`q^{(2j-1)u}\le q^{2j-1}q^{u-1}`$ and $`1+3+\cdots+(2\ell-1)=\ell^2`$. The size of each part is absorbed in $`A`$; their number is controlled by $`q^{\ell^2}`$, which dominates $`(CP^{-2}A)^\ell`$. Thus the bound is summable over $`\ell`$ and independent of $`N`$.

Dominated convergence gives the same limit for $`\sum_\mu W_N(\mu)`$ as for $`a_k=1`$. Equation <a href="#eq:cauchy-model" data-reference-type="eqref" data-reference="eq:cauchy-model">[eq:cauchy-model]</a> evaluates that limit as $`\mathcal M(q)`$, without a separate partition identity. Restoring the normalising tuple supplies the weight product and, through $`\Delta_N/P^{2N}`$, the other two copies of $`\mathcal M(q)`$. Hence
``` math
\frac{D_N}{D_N^{(0)}\prod_{k<N}a_k}\longrightarrow1.
```
Combining this limit with <a href="#eq:cauchy-model-limit" data-reference-type="eqref" data-reference="eq:cauchy-model-limit">[eq:cauchy-model-limit]</a> proves the theorem. ◻

</div>

<a id="sec:weights"></a>

# The weights of Zudilin’s moments

We apply Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">2</a> by collecting the dependence on $`m`$ in <a href="#eq:normalised-moments" data-reference-type="eqref" data-reference="eq:normalised-moments">[eq:normalised-moments]</a> into the single variable $`w=q^{m+1}`$. For this purpose, set
``` math
\begin{equation}
\label{eq:weight-generating-function}
 G_q(w)=\frac1{(w;q)_\infty^3}
 \sum_{t\ge0}\frac{w^t}{(q;q)_t}
       \frac{(q^tw^2;q)_\infty}{(q^tw;q)_\infty^2},
 \qquad a_k(q)=[w^k]P^4G_q(w).
\end{equation}
```
The product identities $`(q;q)_m=P/(q^{m+1};q)_\infty`$ and $`(q^a;q)_m=(q^a;q)_\infty/(q^{a+m};q)_\infty`$ give
``` math
\begin{equation}
\label{eq:positive-moments}
 v_m^*=P^4G_q(q^{m+1})=\sum_{k\ge0}a_k(q)q^{(m+1)k}.
\end{equation}
```
These identities hold formally in $`\mathbb{Z}[[q,w]]`$ and, for fixed $`0<q<1`$, analytically for $`|w|<1`$. In the formal identity only finitely many $`t`$ contribute to any $`w`$-coefficient. For the analytic identity, we use the absence of denominator zeros in that disc and the locally uniform bounds on the product tails. The factor $`w^t`$ then gives locally uniform convergence of the sum. The signs of the coefficients are not evident from this product. The finite factorisation below gives positive weights and a uniform shift bound. Its two convolutions then give the accuracy needed to multiply the first $`N`$ weights.

<a id="sec:weight-factorisation"></a>

## Positive weights

For $`r\ge1`$ and $`k\ge0`$, set
``` math
R_k^{(r)}(q)=\sum_{n_1+\cdots+n_r=k}
              \frac{(q;q)_k}{\prod_{j=1}^r(q;q)_{n_j}},
```
over $`r`$ nonnegative parts. These are the multivariate Rogers–Szegő polynomials at unit arguments, written as sums of Gaussian multinomial polynomials \[vinroot2010\]. At $`q=0`$, every Gaussian multinomial equals $`1`$, so they count weak compositions (zero parts are allowed), and
``` math
c_k:=R_k^{(2)}(0)R_k^{(3)}(0)=\frac{(k+1)^2(k+2)}2,
 \qquad \prod_{k<N}c_k=C_N.
```

<div class="samepage">

<div id="prop:weight-factorisation" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RogersFactorisationAnalytic.lean#L1312">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1049-rational-base-lambert.md#prop-weight-factorisation-comparator">Comparator</a></p>

**Proposition 3** (the positive moment weights). *For every $`k\ge0`$,
``` math
a_k=P^4\frac{R_k^{(2)}R_k^{(3)}}{(q;q)_k}.
```
At fixed $`0<q<1`$ these weights satisfy
``` math
P^5c_k\le a_k\le P^{-1}c_k,
 \qquad \frac{a_{k+h}}{a_k}\le P^{-6}(1+h)^3\quad(k,h\ge0).
```*

</div>

</div>

<div class="proof">

*Proof.* We use the Gaussian binomial coefficients $`\genfrac{[}{]}{0pt}{}{n}{j}_q=(q;q)_n/((q;q)_j(q;q)_{n-j})`$ for $`0\le j\le n`$, and put $`\mathcal E(z)=(z;q)_\infty^{-1}`$. Euler’s expansion gives $`\mathcal E(z)^r=\sum_{n\ge0}R_n^{(r)}z^n/(q;q)_n`$. The desired factorisation multiplies two coefficients at the same index $`k`$, rather than taking a coefficient of $`\mathcal E^5`$. We obtain it by splitting $`k=n+j`$: the factor $`R_k^{(3)}`$ stays fixed, and summing the two factorial denominators supplies $`R_k^{(2)}`$. To produce this split, use the unnormalised $`q`$-difference operator $`\partial_qf(z)=(f(z)-f(qz))/z`$. Since $`\partial_qz^j=(1-q^j)z^{j-1}`$, it cancels the last factor of $`(q;q)_j`$ and shifts the numerator index:
``` math
\partial_q\mathcal E=\mathcal E,\qquad
 \partial_q^n\mathcal E(z)^3
 =\sum_{j\ge0}\frac{R_{n+j}^{(3)}}{(q;q)_j}z^j.
```
The $`q`$-Leibniz rule, obtained by induction from the product rule, is
``` math
\partial_q^n(fg)(z)=\sum_{j=0}^n\genfrac{[}{]}{0pt}{}{n}{j}_q
 (\partial_q^jf)(q^{n-j}z)\,(\partial_q^{n-j}g)(z).
```
Let $`h_k(z)=\sum_{j=0}^k\genfrac{[}{]}{0pt}{}{k}{j}_q(z;q)_j`$. Applying the rule to $`\mathcal E\cdot\mathcal E`$ and using $`\mathcal E(q^mz)=(z;q)_m\mathcal E(z)`$, we obtain $`\partial_q^k\mathcal E(z)^2=\mathcal E(z)^2h_k(z)`$ (for $`k=1`$, both sides equal $`\mathcal E(z)^2(2-z)`$). A second application, this time to $`\mathcal E\cdot\mathcal E^2`$, gives
``` math
\partial_q^n\mathcal E(z)^3
 =\mathcal E(z)^3\sum_{k=0}^n\genfrac{[}{]}{0pt}{}{n}{k}_q(z;q)_kh_k(z),
```
and hence
``` math
\sum_{n\ge0}\frac{w^n}{(q;q)_n}\partial_q^n\mathcal E(z)^3
 =\mathcal E(w)\mathcal E(z)^3
  \sum_{k\ge0}\frac{w^k(z;q)_k}{(q;q)_k}h_k(z).
```
The left-hand side is $`\sum_{n,j\ge0}R_{n+j}^{(3)}w^nz^j/((q;q)_n(q;q)_j)`$. Putting $`z=w`$ collects all pairs with the same sum $`n+j`$. The coefficient of $`w^k`$ is consequently $`R_k^{(3)}\sum_{j\le k}\bigl((q;q)_j(q;q)_{k-j}\bigr)^{-1}
=R_k^{(2)}R_k^{(3)}/(q;q)_k`$. On the right-hand side, put $`z=w`$, expand $`h_k`$, and write $`k=j+t`$. The identity $`(w;q)_{j+t}=(w;q)_j(wq^j;q)_t`$ gives
``` math
\mathcal E(w)^4\sum_{j\ge0}\frac{w^j(w;q)_j^2}{(q;q)_j}
       \sum_{t\ge0}\frac{(wq^j;q)_t}{(q;q)_t}w^t.
```
The inner sum is evaluated by the $`q`$-binomial theorem:
``` math
\sum_{t\ge0}\frac{(wq^j;q)_t}{(q;q)_t}w^t
 =\frac{(w^2q^j;q)_\infty}{(w;q)_\infty}.
```
Finally, $`(w;q)_j=(w;q)_\infty/(wq^j;q)_\infty`$ cancels two of the five factors $`\mathcal E(w)`$, leaving
``` math
\mathcal E(w)^3\sum_{j\ge0}\frac{w^j}{(q;q)_j}
       \frac{(w^2q^j;q)_\infty}{(wq^j;q)_\infty^2}
 =G_q(w).
```
We may read each identity coefficientwise, or as an absolutely convergent expansion when $`|z|`$ and $`|w|`$ are sufficiently small.

For the bounds, we write $`b_k^{(r)}=[z^k](z;q)_\infty^{-r}`$, so that $`R_k^{(r)}=(q;q)_kb_k^{(r)}`$ and $`a_k=P^4(q;q)_kb_k^{(2)}b_k^{(3)}`$. By Euler’s expansion, $`b_k^{(r)}`$ is an $`r`$-fold convolution of $`1/(q;q)_n`$, whose terms lie in $`[1,P^{-1}]`$. There are $`\binom{k+r-1}{r-1}`$ compositions of $`k`$ into $`r`$ nonnegative parts, and we deduce
``` math
\binom{k+r-1}{r-1}\le b_k^{(r)}\le P^{-r}\binom{k+r-1}{r-1}.
```
Combining these at $`r=2,3`$ with $`P\le(q;q)_k\le1`$ and $`c_k=(k+1)\binom{k+2}2`$ gives $`P^5c_k\le a_k\le P^{-1}c_k`$. The shift bound follows from $`c_{k+h}/c_k\le(1+h)^3`$. ◻

</div>

Positivity holds at each fixed real $`q\in(0,1)`$, not coefficientwise in the formal $`q`$-series: $`a_0(q)=P^4=1-4q+O(q^2)`$. The bounds control shifted ratios, but do not determine the weight product. A relative error of order $`1/k`$ accumulates logarithmically; one of order $`1/k^2`$ is summable. Computing $`a_k/c_k`$ to first order will therefore determine the power of $`N`$ and give the fixed-shift limit.

<a id="sec:coefficient-asymptotic"></a>

## The coefficient asymptotic

<div class="proof">

*Proof of Theorem <a href="#res:sharp-fixed-base" data-reference-type="ref" data-reference="res:sharp-fixed-base">1</a>.* Put $`L=F(1/q)`$, $`e_k=(q;q)_k^{-1}`$ and $`E=P^{-1}`$. Replacing every $`e_k`$ by $`E`$ gives $`E^2(k+1)`$ and $`E^3\binom{k+2}{2}`$, counting nonnegative pairs and triples with sum $`k`$. Terms with one deficit $`E-e_i`$ give the first correction. That coordinate has two possible positions in a pair and three in a triple; fixing it at $`i`$ leaves one pair or $`k-i+1`$ triples. Thus the same total deficit produces a constant correction in the first convolution and a linear correction in the second. We calculate it and control its first moment.

Writing $`d_k=E-e_k`$, the identity $`e_{k+1}-e_k=q^{k+1}e_{k+1}`$ gives
``` math
d_k=\sum_{j>k}q^je_j,\qquad
 0\le d_k\le\frac{E q^{k+1}}{1-q}.
```
Thus $`\sum d_k`$ and $`\sum k d_k`$ converge. To evaluate the former, use Euler’s identity $`\mathcal E(z)=\sum_{k\ge0}e_kz^k=(z;q)_\infty^{-1}`$ for $`|z|<1`$. Tonelli’s theorem and logarithmic differentiation at $`z=q`$ give
``` math
S:=\sum_{k\ge0}d_k
 =\sum_{j\ge1}j q^je_j
 =q\mathcal E'(q)
 =E\sum_{r\ge1}\frac{q^r}{1-q^r}=EL.
```
In the double sum, $`q^je_j`$ occurs once for each $`k=0,\ldots,j-1`$, which explains the factor $`j`$. Logarithmic differentiation is justified by locally uniform convergence on $`|z|<1`$.

Let $`b_k^{(r)}=[z^k]\mathcal E(z)^r`$. The finite-sum formula in Proposition <a href="#prop:weight-factorisation" data-reference-type="ref" data-reference="prop:weight-factorisation">3</a> becomes
``` math
a_k=P^4(q;q)_k b_k^{(2)}b_k^{(3)}.
```
We expand each finite convolution using $`e_k=E-d_k`$. For two factors,
``` math
b_k^{(2)}=E^2(k+1)-2E\sum_{i=0}^k d_i
              +\sum_{i=0}^k d_i d_{k-i}
 =E^2(k+1-2L)+O_q((k+1)q^k).
```
For three factors, the terms with one $`d_i`$ contribute $`-3E^2\sum_{i=0}^k(k-i+1)d_i`$. Here the sum equals $`(k+1)S+O_q(1)`$ because $`\sum i d_i<\infty`$. Terms with two $`d_i`$ are bounded by $`3E S^2`$, and the term with three is $`O_q((k+1)^2q^k)`$. It follows that
``` math
b_k^{(3)}=E^3\left(\binom{k+2}{2}-3L(k+1)\right)+O_q(1).
```
Division by $`\binom{k+2}{2}`$ turns $`-3L(k+1)`$ into the relative correction $`-6L/(k+2)`$; the two-fold sum gives $`-2L/(k+1)`$. Since $`(q;q)_k=P(1+O_q(q^k))`$, the leading constants in $`a_k`$ cancel: $`P^5E^5=1`$. Replacing $`(k+2)^{-1}`$ by $`(k+1)^{-1}`$ costs only $`O_q((k+1)^{-2})`$. The two corrections therefore add, and with $`c_k=(k+1)^2(k+2)/2`$ we obtain
``` math
\begin{align*}
 \frac{a_k}{c_k}
 &=\left(1-\frac{2L}{k+1}+O_q(q^k)\right)
   \left(1-\frac{6L}{k+2}+O_q((k+1)^{-2})\right)
   \left(1+O_q(q^k)\right)\\
 &=1-\frac{8L}{k+1}+O_q((k+1)^{-2}).
\end{align*}
```
In particular $`a_{k+1}/a_k\to1`$, and multiplication of finitely many adjacent ratios gives $`a_{k+h}/a_k\to1`$ for each fixed $`h`$. The uniform shift bound follows from Proposition <a href="#prop:weight-factorisation" data-reference-type="ref" data-reference="prop:weight-factorisation">3</a>, so Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">2</a> applies.

Let $`\gamma_{\!E}`$ denote Euler’s constant and put
``` math
\begin{equation}
\label{eq:fixed-constant}
 \mathcal A(q)=e^{-8\gamma_{\!E}L}
 \prod_{k\ge0}\left(\frac{a_k}{c_k}e^{8L/(k+1)}\right),
 \qquad K(q)=\mathcal A(q)\mathcal M(q)^3.
\end{equation}
```
For sufficiently large $`k`$, $`\log(1+u)=u+O(u^2)`$ gives $`\log(a_k/c_k)+8L/(k+1)=O_q((k+1)^{-2})`$. This tail is summable, and the finitely many initial factors are positive by Proposition <a href="#prop:weight-factorisation" data-reference-type="ref" data-reference="prop:weight-factorisation">3</a>. Thus $`0<\mathcal A(q)<\infty`$. Using $`\prod_{k<N}c_k=C_N`$, separate the harmonic sum from this convergent remainder:
``` math
\log\frac{\prod_{k<N}a_k}{C_N}
 =-8L\sum_{k<N}\frac1{k+1}
  +\sum_{k<N}\left(\log\frac{a_k}{c_k}+\frac{8L}{k+1}\right).
```
The second sum tends to $`\log\mathcal A(q)+8\gamma_{\!E}L`$. Using $`\sum_{k<N}(k+1)^{-1}=\log N+\gamma_{\!E}+o(1)`$, the Euler-constant terms cancel, giving $`\prod_{k<N}a_k\sim\mathcal A(q)C_NN^{-8L}`$. Substitution in <a href="#eq:geometric-limit" data-reference-type="eqref" data-reference="eq:geometric-limit">[eq:geometric-limit]</a> proves the theorem, or equivalently
``` math
\log V_N^*=B_N\log q+\log C_N+2N\log P
             -8L\log N+\log K(q)+o(1).
```
 ◻

</div>

The scales are now separate: the node geometry gives the cubic term $`B_N\log q`$; the cubic growth of the weights gives $`\log C_N`$ of order $`N\log N`$; their first relative correction gives $`-8F(1/q)\log N`$. The other terms are linear and constant. In particular, the power correction does not change the cubic rate.

<a id="sec:hankel-order"></a>

## The first nonzero formal term

The order of a nonzero formal series is the least exponent with nonzero coefficient. We now fix $`N`$ and determine the first term in the formal $`q`$-expansion. The shifted term in <a href="#eq:last-node-shift" data-reference-type="eqref" data-reference="eq:last-node-shift">[eq:last-node-shift]</a> then has an extra factor of $`q`$. More generally, every nonempty partition has positive displacement exponent. Thus a single tuple determines the first formal term, although all partitions were needed for the fixed-base constant.

<div id="res:zudilin-sharp-qorder" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1049-rational-base-lambert.md#res-zudilin-sharp-qorder">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1049-rational-base-lambert.md#res-zudilin-sharp-qorder-comparator">Comparator</a></p>

**Theorem 4** (the first nonzero term of the Hankel determinant). *For every $`N\ge1`$,
``` math
\operatorname{ord}_q V_N^*=\frac{N(N-1)(2N-1)}6,
```
and the coefficient of the first nonzero monomial is
``` math
[q^{N(N-1)(2N-1)/6}]V_N^*
   =\frac{(N!)^2(N+1)!}{2^N}.
```*

</div>

<div class="proof">

*Proof.* At $`q=0`$, the $`t=0`$ term of $`G_q(w)`$ is $`(1-w^2)/(1-w)^5`$, while the remaining terms sum to $`w/(1-w)^4`$. Thus
``` math
G_0(w)=\frac{1+2w}{(1-w)^4},\qquad a_k(0)=c_k>0.
```
We compute modulo $`q^{M+1}`$ by truncating each moment sum in <a href="#eq:positive-moments" data-reference-type="eqref" data-reference="eq:positive-moments">[eq:positive-moments]</a> at $`k=M`$. Since all omitted terms are divisible by $`q^{M+1}`$, multilinearity leaves the determinant unchanged modulo that power. Applying finite Cauchy–Binet and then allowing $`M`$ to increase, we obtain the coefficientwise identity
``` math
V_N^*=\sum_{k_0<\cdots<k_{N-1}}
 \left(\prod_{i<N}a_{k_i}(q)q^{k_i}\right)
 \prod_{i<j<N}(q^{k_i}-q^{k_j})^2.
```
The order of the summand indexed by $`(k_i)`$ is $`\sum_{i<N}(2N-1-2i)k_i`$. Because $`k_i\ge i`$ and all the weights $`2N-1-2i`$ are positive, we obtain the unique minimum at $`k_i=i`$, with order and coefficient
``` math
\sum_{i<N}(2N-1-2i)i=B_N,\qquad \prod_{i<N}c_i=C_N.
```
No other tuple has this order, so no coefficient from another tuple can cancel it. This argument needs the positive constant terms $`a_k(0)=c_k`$, not nonnegativity of all their formal coefficients. For $`N=2`$, the pair $`(0,1)`$ contributes $`6q+O(q^2)`$, and every other increasing pair has order at least two. ◻

</div>

This proves equality in Zudilin’s bound \[zudilin2016, §4, pp. 6–7\]. An alternative argument, which computes the first nonzero term of every transformed row, is given in [the companion paper](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-formal-rows).

<a id="sec:rational-base-irrationality"></a>

# Rational bases

We now use the 2004 coefficient family. For $`U,V\in\mathbb{Z}[X]`$ of degree at most $`W`$, multiplying $`U(a/b)`$ and $`V(a/b)`$ by $`b^W`$ makes them integers. This is a sufficient clearing factor, not in general the smallest one. Cancelling a common nonconstant polynomial factor first lowers the degree bound. For example, at $`3/2`$ the pair $`(X+1)(X+2),(X+1)(X+3)`$ gives $`(35,45)`$ after clearing to degree $`2`$. After cancelling $`X+1`$, clearing to degree $`1`$ gives $`(7,9)`$. For Zudilin’s forms, let $`K_n`$ be the original coefficient degree and $`W_n`$ its degree after cancellation; both grow quadratically with $`n`$. The uncancelled remainder stays between positive constants. The normalising multiplier creates the decay, with leading scale $`x^{-(K_n-W_n)}`$ at fixed $`x>1`$. Clearing at $`x=a/b`$ then gives
``` math
\begin{equation}
\label{eq:degree-balance}
 b^{W_n}(a/b)^{-(K_n-W_n)}
 =\frac{b^{K_n}}{a^{K_n-W_n}}.
\end{equation}
```
Net degree removal is therefore measured in powers of $`a`$, while the original degree costs powers of $`b`$. The remaining logarithmic terms are $`o(n^2)`$, so $`K_n/n^2\to C_1`$ and $`(K_n-W_n)/n^2\to C_0`$ give $`C_1\log b<C_0\log a`$. The proof must establish both the degree estimates and cancellation in $`\mathbb{Z}[X]`$, before evaluation.

We use the parameter direction from Zudilin’s construction \[zudilin2004, §5, pp. 161–162\], together with its thirteen intervals and constants $`C_1,C_0`$. At integer bases his theorem gives the irrationality-exponent bound $`C_1/C_0=2.46497868\ldots`$ \[zudilin2004, Thm. 1, p. 154\]. Let $`\psi_1(u)=\sum_{k\ge0}(k+u)^{-2}`$ for $`u>0`$, and let $`\mathcal I`$ consist of the thirteen intervals listed in the proof. We put
``` math
\begin{equation}
\label{eq:threshold-constants}
 C_1=\frac{1091}{2},\qquad
 J=\sum_{[u,v)\in\mathcal I}\bigl(\psi_1(u)-\psi_1(v)\bigr),\qquad
 C_0=266-\frac3{\pi^2}(225-J).
\end{equation}
```
The intervals are disjoint and lie in $`[1/14,1)`$, so $`0\le J\le\psi_1(1/14)-\psi_1(1)<196`$. Together with $`\pi>3`$, these bounds give $`0<C_0<266<C_1/2`$. Thus $`\theta^*=C_0/C_1`$ and $`\mu=C_1/C_0`$ are positive reciprocal constants. The notation $`\mu_{\rm irr}(\xi)`$ instead denotes the irrationality exponent of a value. The estimates below give a sufficient cutoff; its optimality is unknown.

<div id="res:rational-base-threshold" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1049-rational-base-lambert.md#res-rational-base-threshold">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1049-rational-base-lambert.md#res-rational-base-threshold-comparator">Comparator</a></p>

**Theorem 5** (rational-base region for Zudilin’s forms). *Let $`a>b\ge1`$ be coprime integers with
``` math
\begin{gathered}
 b^{\mu}<a,\qquad\text{equivalently}\qquad
 \frac{\log b}{\log a}<\theta^*,\\
 \theta^*=\frac{C_0}{C_1}=0.4056830213840605\ldots,\\
 \mu=\frac{C_1}{C_0}=2.4649786835749750\ldots.
\end{gathered}
```
Then $`F(a/b)`$ is irrational.*

</div>

Every integer base qualifies, since $`b=1`$ gives $`\log b/\log a=0`$. For each fixed $`b>1`$, the restriction $`a>b^{2.46497868\ldots}`$ is much stronger than $`a>b`$, but still admits infinitely many coprime numerators. It includes $`31/4`$ and its positive integral powers, whose logarithmic ratio is unchanged. It excludes $`3/2`$, since $`\theta^*<1/2<\log2/\log3`$. At equality the quadratic exponent vanishes and the estimates give no conclusion.

<div class="proof">

*Proof of Theorem <a href="#res:rational-base-threshold" data-reference-type="ref" data-reference="res:rational-base-threshold">5</a>.* *The source forms and polynomial cancellation.* Fix $`n\ge1`$ and set
``` math
a_0=14n+1,\quad a_1=12n+1,\quad a_2=14n+1,\quad\beta=27n+2,
 \qquad N=15n.
```
In this proof $`N`$ denotes the cyclotomic cutoff. We use the coefficient pair $`A_n,B_n`$ of the source identities \[zudilin2004, (8)–(11), pp. 156–157\], with $`H_n=A_nF-B_n`$. Let $`\Phi_\ell`$ be the cyclotomic polynomial whose roots are the primitive $`\ell`$th roots of unity. Put $`D_N(X)=\prod_{\ell=1}^{N}\Phi_\ell(X)`$, $`M_n=266n^2+34n+1`$, and
``` math
\Omega_n(X)=\prod_{\ell=2}^{N}\Phi_\ell(X)^{\nu_\ell},
 \qquad \nu_\ell=\omega(n/\ell),
```
where the periodic function
``` math
\begin{split}
\omega(x)=\max\{0,&\ \lfloor14x\rfloor+\lfloor13x\rfloor
                  -\lfloor12x\rfloor-\lfloor15x\rfloor,\\
                &\ 2\lfloor14x\rfloor-\lfloor13x\rfloor
                  -\lfloor15x\rfloor\}
\end{split}
```
has period $`1`$: the coefficients of the floor arguments in each difference have equal sums, $`14+13=12+15`$ and $`2\cdot14=13+15`$. On $`[0,1)`$ it is zero or one, with support
``` math
\begin{gathered}
\,[1/14,1/12),\ [1/7,1/6),\ [3/14,1/4),\ [2/7,1/3),\\
[5/14,2/5),\ [3/7,7/15),\ [1/2,8/15),\ [4/7,3/5),\\
[9/14,2/3),\ [5/7,11/15),\ [11/14,4/5),\\
[6/7,13/15),\ [13/14,14/15).
\end{gathered}
```
These are the intervals $`\mathcal I`$ used to define $`J`$. The function $`\omega`$, these thirteen intervals and the exponents $`\nu_\ell=\omega(n/\ell)`$ of the source’s (22) are printed at \[zudilin2004, pp. 161–162\].

First isolate the part that does not create decay. At $`x>1`$, put $`q=1/x`$. Identity (9) on p. 156 of the source gives
``` math
H_n(x)=\sum_{t\ge0}q^{a_0t}
 \frac{(q^{t+1};q)_{a_1-1}}{(q;q)_{a_1-1}}
 \frac{(q;q)_{\beta-a_2-1}}{(q^{a_2+t};q)_{\beta-a_2}}.
```
The denominator length is $`\beta-a_2`$, as in the gamma expression (7) and residues (8) of \[zudilin2004, p. 156\]; the unnumbered display of $`R(T)`$ on that page has length $`\beta-a_2-1`$ instead. Each finite product lies in $`[P,1]`$, where $`P=(q;q)_\infty>0`$. The $`t=0`$ term gives the lower bound; summing $`q^{a_0t}`$ gives the upper bound:
``` math
P^2\le H_n(x)\le\frac{P^{-2}}{1-q^{a_0}}.
```
In particular $`H_n(x)>0`$ and $`\log H_n(x)=O_x(1)`$.

The required polynomial integrality is the inclusion in Zudilin’s Lemma 7, display (23) \[zudilin2004, p. 161\]. Its comparison of cyclotomic valuations under six admissible parameter permutations gives divisibility in $`\mathbb{Z}[X]`$, not merely at integer values of $`X`$. Its parameter vector is $`n(13,14,12,14,15,13)`$, its maximum is $`15n`$, and $`\beta-a_1-a_2=n>0`$, which is the positivity condition $`s>0`$ of the lemma. The conditions (14) of \[zudilin2004, p. 157\], $`a_1\le a_2`$ and $`a_1+a_2\le\beta\le a_0+a_2`$, hold as well, so the exponent in (23) is the integer (16), which equals $`M_n`$. Lemma 7 therefore gives, for every $`n\ge1`$,
``` math
\Lambda_n(X)=X^{-M_n}\frac{D_N(X)}{\Omega_n(X)}H_n(X)
            =U_n(X)F(X)-V_n(X),\qquad U_n,V_n\in\mathbb Z[X].
```
This is the polynomial conclusion before integer specialisation in the source’s (24), p. 162. The coefficients are the cancelled source coefficients:
``` math
U_n=X^{-M_n}(D_N/\Omega_n)A_n,\qquad
 V_n=X^{-M_n}(D_N/\Omega_n)B_n.
```
Indeed, coefficients of $`F`$ and $`1`$ over $`\mathbb{Q}(X)`$ are unique because $`F`$ is not a rational function. To see this, we split $`F(e^h)`$ at $`m=1/h`$ as $`h\downarrow0`$. For $`m\le1/h`$, the inequalities $`y^{-1}-1\le(e^y-1)^{-1}\le y^{-1}`$ for $`0<y\le1`$ give $`h^{-1}\sum_{m\le1/h}m^{-1}+O(h^{-1})`$. Bounding the remaining terms by a geometric tail gives a further $`O(h^{-1})`$, and therefore $`F(e^h)=h^{-1}\log(1/h)+O(h^{-1})`$, which has no rational-function pole order at $`X=1`$. This establishes uniqueness of the coefficient functions; it assumes nothing about an individual value $`F(a/b)`$. The cancelled remainder is positive for $`x>1`$, since $`D_N/\Omega_n`$ is a product of cyclotomic polynomials positive there.

*The degrees after cancellation.* The Gaussian binomial polynomial $`\genfrac{[}{]}{0pt}{}{m}{k}_X=\prod_{j=1}^k(1-X^{m-k+j})/(1-X^j)`$ is monic of degree $`k(m-k)`$ for integers $`0\le k\le m`$. The source’s (8) and (10) on p. 156 give the coefficient whose degree we need:
``` math
A_n(X)=\sum_{k=a_2}^{\beta-1}(-1)^{a_1+a_2+k+1}
 X^{a_0k+\binom{a_1}{2}-\binom{\beta-a_2}{2}+\binom{\beta-k}{2}}
 \genfrac{[}{]}{0pt}{}{k-1}{a_1-1}_X
 \genfrac{[}{]}{0pt}{}{\beta-a_2-1}{\beta-k-1}_X.
```
Let $`d_{n,k}`$ be the degree of the $`k`$th summand. Adding the monomial exponent and the degrees of the two Gaussian factors gives
``` math
\begin{aligned}
 d_{n,k}
 &=a_0k+\binom{a_1}{2}-\binom{\beta-a_2}{2}+\binom{\beta-k}{2}\\
 &\quad +(a_1-1)(k-a_1)+(\beta-k-1)(k-a_2)\\
 &=\frac{-k^2+80kn+3k-340n^2-26n}{2}.
 \end{aligned}
```
Hence $`d_{n,k+1}-d_{n,k}=40n+1-k>0`$ for $`a_2\le k\le\beta-2=27n`$. The last summand alone therefore determines the leading term, giving
``` math
K_n:=\deg A_n=\frac{1091n^2+81n+2}{2},\qquad
 W_n:=\deg U_n=K_n-M_n+\sum_{\ell\le15n}(1-\nu_\ell)\varphi(\ell).
```
Here $`\varphi(\ell)=\deg\Phi_\ell`$ is Euler’s totient function, and $`\nu_1=\omega(n)=0`$. In particular,
``` math
K_n-W_n=M_n-\deg(D_N/\Omega_n).
```
The monomial removes $`M_n`$ degrees and the surviving cyclotomic product restores $`\deg(D_N/\Omega_n)`$; their difference is the net removal $`K_n-W_n`$.

To determine the other coefficient’s degree, fix $`n`$ and let $`x\to\infty`$. The bounds for $`H_n`$ are uniform for $`x\ge2`$, since $`P\ge\prod_{j\ge1}(1-2^{-j})>0`$ and $`(1-x^{-a_0})^{-1}\le2`$. Hence $`H_n(x)=O(1)`$ and $`\Lambda_n(x)=O(x^{W_n-K_n})`$. The unique top summand of $`A_n`$ has leading coefficient $`(-1)^{a_1+a_2+\beta}=(-1)^n`$. Since the Gaussian factors and $`D_N/\Omega_n`$ are monic, $`U_n`$ has that leading coefficient too. Moreover $`F(x)=x^{-1}+O(x^{-2})`$ and $`K_n\ge2`$, so
``` math
V_n(x)=U_n(x)F(x)-\Lambda_n(x)
       =(-1)^n x^{W_n-1}+O(x^{W_n-2}).
```
Here $`W_n\ge K_n-M_n=(559n^2+13n)/2>0`$. Thus $`\deg V_n=W_n-1`$, with the same unit leading coefficient as $`U_n`$. For every prime $`p\mid b`$, reduction of the cleared first coordinate gives
``` math
b^{W_n}U_n(a/b)\equiv(-1)^n a^{W_n}\not\equiv0\pmod p.
```
Thus $`U_n(a/b)`$ has reduced denominator exactly $`b^{W_n}`$, which is the least common clearing denominator for the pair. Any common integer divisor of the cleared pair is coprime to $`b`$. This exact cost concerns these coefficients only: common factors at other primes and combinations of rows remain separate questions.

*The quadratic degree limits.* We now keep the base fixed and let $`n\to\infty`$, extracting the quadratic part of the net degree removal. These are the cyclotomic limits of \[zudilin2004, Lemmas 1–2, p. 155\]. We use the reciprocal intervals, summatory totient estimate and trigamma function from \[zudilin2002, Lemma 1, p. 466\], truncating the block sum before passing to the limit. The elementary summatory estimate $`\sum_{\ell\le y}\varphi(\ell)=3y^2/\pi^2+O(y\log y)`$ gives
``` math
\frac1{n^2}\sum_{\ell\le15n}\varphi(\ell)\longrightarrow\frac{675}{\pi^2}.
```
For $`[u,v)\in\mathcal I`$, the condition $`\{n/\ell\}\in[u,v)`$ is the disjoint union of intervals $`n/(k+v)<\ell\le n/(k+u)`$ for $`k\ge0`$. Apply the summatory estimate to finitely many blocks. Instead of summing its errors over all $`k`$, bound the omitted blocks together: for $`k\ge K\ge1`$, all their indices satisfy $`\ell\le n/(K+u)`$. The bound $`\sum_{\ell\le y}\varphi(\ell)\le y^2`$ gives
``` math
\frac1{n^2}\sum_{\ell\le n/(K+u)}\varphi(\ell)
 \le\frac1{(K+u)^2}.
```
For $`y\ge1`$, sum $`\varphi(\ell)\le\ell`$; for $`0\le y<1`$ the sum is empty. The tail bound is uniform in $`n`$, so we may let $`n`$ and then $`K`$ tend to infinity:
``` math
\frac1{n^2}\sum_{\ell\le15n}\nu_\ell\varphi(\ell)
 \longrightarrow\frac3{\pi^2}
 \sum_{[u,v)\in\mathcal I}\sum_{k\ge0}
 \left(\frac1{(k+u)^2}-\frac1{(k+v)^2}\right)=\frac{3J}{\pi^2}.
```
Here no contributing index exceeds $`14n`$, since $`u\ge1/14`$. Consequently
``` math
K_n/n^2\longrightarrow C_1,\qquad
 (K_n-W_n)/n^2\longrightarrow C_0.
```

*The cleared remainder.* It remains to turn polynomial degrees into values at fixed $`x>1`$. Writing $`\mu_{\rm Mob}`$ for the Möbius function, we have
``` math
\log\Phi_\ell(x)-\varphi(\ell)\log x
 =\sum_{d\mid\ell}\mu_{\rm Mob}(d)\log(1-x^{-\ell/d}).
```
Each $`-\log(1-x^{-d})`$ occurs only for multiples $`\ell`$ of $`d`$, at most $`15n/d`$ times. The total absolute error is therefore at most
``` math
15n\sum_{d\ge1}\frac{-\log(1-x^{-d})}{d}.
```
The series converges because $`-\log(1-x^{-d})\le x^{-d}/(1-x^{-1})`$, so the error is $`O_x(n)`$. Using $`0\le1-\nu_\ell\le1`$ and $`\log H_n(x)=O_x(1)`$ gives
``` math
\log\Lambda_n(x)=-(K_n-W_n)\log x+O_x(n).
```

At $`x=a/b`$, the coefficients $`b^{W_n}U_n(a/b)`$ and $`b^{W_n}V_n(a/b)`$ are integers, and
``` math
\begin{split}
 \log\bigl(b^{W_n}\Lambda_n(a/b)\bigr)
 &=K_n\log b-(K_n-W_n)\log a+O_{a/b}(n)\\
 &=\bigl(C_1\log b-C_0\log a\bigr)n^2+o(n^2).
\end{split}
```
The quadratic coefficient is negative under the hypothesis. If $`F(a/b)=r/s`$ with integers $`r,s`$ and $`s>0`$, then $`s b^{W_n}\Lambda_n(a/b)`$ would be a positive integer tending to zero. This contradiction uses positivity of the same remainder, not independence of successive forms. ◻

</div>

<div id="res:thirtyone-four" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L117">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1049-rational-base-lambert.md#res-thirtyone-four-comparator">Comparator</a></p>

**Corollary 6**. *$`F\bigl((31/4)^r\bigr)`$ is irrational for every integer $`r\ge1`$.*

</div>

<div class="proof">

*Proof.* The exact inequalities $`31^2<4^5`$ and $`4^{200}<31^{81}`$ give $`2/5<\log4/\log31<81/200`$. The first term of each trigamma difference yields
``` math
J\ge\sum_{[u,v)\in\mathcal I}(u^{-2}-v^{-2})
   =\frac{2015640690251}{25971865920}.
```
Using $`\pi>157/50`$ gives the rational lower bound
``` math
\theta^*>\frac{2359630009523263}{5820307922172744}
           >\frac{81}{200}.
```
Taking a common positive integer power preserves both the logarithmic ratio and coprimality, so the same criterion applies for every $`r\ge1`$. ◻

</div>

<div id="cor:rational-base-measure" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1049-rational-base-lambert.md#cor-rational-base-measure">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1049-rational-base-lambert.md#cor-rational-base-measure-comparator">Comparator</a></p>

**Corollary 7** (an irrationality measure uniform over powers). *For coprime $`a>b\ge1`$ with $`\theta=\log b/\log a<\theta^*`$ and every integer $`r\ge1`$,
``` math
\mu_{\rm irr}\!\left(F((a/b)^r)\right)
 \le\frac{1-\theta}{\theta^*-\theta}.
```
Here $`\mu_{\rm irr}(\xi)`$ is the supremum of the exponents $`\nu`$ for which $`|\xi-p/q|<q^{-\nu}`$ has infinitely many reduced rational solutions. In particular, $`\mu_{\rm irr}(F((31/4)^r))<301`$ for every $`r\ge1`$.*

</div>

<div class="proof">

*Proof.* We use Zudilin’s passage from linear forms to an exponent bound \[zudilin2004, p. 162\], at each fixed base $`(a/b)^r`$. Take $`U_n,V_n`$ and $`W_n=\deg U_n`$ from Theorem <a href="#res:rational-base-threshold" data-reference-type="ref" data-reference="res:rational-base-threshold">5</a>. A measure needs more than positive remainders tending to zero: it must bound how small they are relative to their coefficients. The logarithmic remainder asymptotic supplies a lower bound; we now bound $`U_n`$ above. In that construction the coefficient of $`F`$ before cancellation is a sum of $`O(n)`$ Laurent monomials times two Gaussian binomial polynomials. Each Gaussian polynomial has nonnegative coefficients summing to at most $`2^{27n+2}`$. Thus the sum of the absolute coefficients is $`\exp(O(n))`$. Its largest exponent is $`K_n=(1091n^2+81n+2)/2`$, so its absolute value at a fixed $`x>1`$ is at most $`x^{K_n}\exp(O(n))`$. The cyclotomic estimate in the same proof bounds the normalising multiplier by $`x^{W_n-K_n}\exp(O_x(n))`$. Multiplication gives
``` math
|U_n(x)|\le x^{W_n}\exp(O_x(n))\qquad(x>1\text{ fixed}).
```
Set $`\xi=F(a/b)`$, $`Q_n=b^{W_n}U_n(a/b)`$ and $`P_n=b^{W_n}V_n(a/b)`$. With
``` math
\alpha=(C_1-C_0)\log a,\qquad
 \tau=C_0\log a-C_1\log b>0,
```
we have $`\log(Q_n\xi-P_n)=-\tau n^2+o(n^2)`$ and $`|Q_n|\le\exp(\alpha n^2+o(n^2))`$.

Here $`q`$ denotes an approximation denominator, not the geometric base of Sections <a href="#sec:geometric-moments" data-reference-type="ref" data-reference="sec:geometric-moments">2</a> and <a href="#sec:weights" data-reference-type="ref" data-reference="sec:weights">3</a>. The comparison uses the integer $`Ap-Bq`$, allowing it to vanish. For integers $`A,B,p,q`$ with $`q>0`$, if $`L=A\xi-B`$ and $`2q|L|\le1`$, then
``` math
|L|\le |A|\,|\xi-p/q|.
```
If $`Ap-Bq=0`$, this is equality; otherwise $`1/q\le |L|+|A|\,|\xi-p/q|`$ gives the inequality. Thus no rational $`p/q`$ is excluded from the comparison. Fix $`0<\eta<\tau`$ and write
``` math
e^{-(\tau+\eta)n^2}\le Q_n\xi-P_n\le e^{-(\tau-\eta)n^2},
 \qquad |Q_n|\le e^{(\alpha+\eta)n^2}
```
for all sufficiently large $`n`$. The upper remainder bound determines our choice: for a sufficiently large denominator $`q`$, take $`n=\lceil\sqrt{\log(2q)/(\tau-\eta)}\rceil`$. Then $`2q(Q_n\xi-P_n)\le1`$. The preceding integer argument now applies to $`(A,B)=(Q_n,P_n)`$ for every numerator $`p`$. Also $`Q_n\ne0`$: otherwise $`Q_n\xi-P_n`$ would be an integer strictly between $`0`$ and $`1`$. The lower remainder bound and the coefficient bound now give
``` math
|\xi-p/q|\ge e^{-(\alpha+\tau+2\eta)n^2}
             =q^{-(\alpha+\tau+2\eta)/(\tau-\eta)-o(1)},
```
since $`n^2=\log(2q)/(\tau-\eta)+O_\eta(\sqrt{\log q}+1)`$. The rounding error is $`o(\log q)`$, so it does not change the exponent. This choice covers every sufficiently large approximation denominator $`q`$; no monotonicity assumption on the coefficients $`Q_n`$ is used.

Letting $`\eta\downarrow0`$, we deduce the bound $`1+\alpha/\tau=(1-\theta)/(\theta^*-\theta)`$. A common power multiplies $`\alpha`$ and $`\tau`$ by $`r`$, so the quotient is unchanged, although the constants in the approximation inequality may depend on $`r`$. For $`31/4`$, the exact interval bounds in the companion record, [Section 2.5](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-regionbracket), give $`\theta<0.4036982`$ and $`\theta^*>0.40568`$. The quotient increases with $`\theta`$ and decreases with $`\theta^*`$ in this range, so
``` math
\frac{1-\theta}{\theta^*-\theta}
 <\frac{1-0.4036982}{0.40568-0.4036982}
 =\frac{2981509}{9909}<301.
```
The same section gives the rational certificates for these bounds and sharper enclosures of the constants. ◻

</div>

<a id="comparison-with-earlier-criteria"></a>

## Comparison with earlier criteria

Bundschuh and Väänänen’s Theorem 2 at $`\alpha=-1`$ \[bv1994, p. 177\] gives irrationality for $`\log b/\log a<\theta_{\rm BV}:=1/2-1/\pi^2`$. Their $`q`$ is the base $`a/b>1`$, not its reciprocal. Their logarithmic derivative is $`L_q(z)=\sum_{j\ge1}(q^j+z)^{-1}`$, so the value at $`z=\alpha=-1`$ is exactly $`F(a/b)`$. The rational height is $`h(q)=a`$, and their parameter $`\lambda=\log h(q)/\log q`$ is $`1/(1-\log b/\log a)`$, which gives the displayed cutoff. Since $`\pi^2<10`$, one has $`\theta_{\rm BV}<2/5<\log4/\log31`$, so $`31/4`$ lies outside that sufficient region. The two sufficient regions differ on $`[\theta_{\rm BV},\theta^*)`$. Zudilin also notes an extension to noninteger rational bases $`p=r/s`$ for the generalized $`q`$-logarithm when $`\log|r|>c\log|s|`$, with $`c>0`$ computable but unspecified \[zudilin2016, Sec. 2, p. 4\]. The value $`c=\mu`$ here comes from the 2004 forms \[zudilin2004, p. 162\], not from evaluating the unspecified constant in the 2016 construction.

The positive-remainder estimates require $`x>1`$, so they give no statement for negative bases. The series diverges at $`x=1`$. The companion’s height-criterion section also applies Bundschuh and Väänänen’s cited theorem at $`7/2`$.

<a id="sec:open"></a>

# Further questions

The determinant asymptotic still needs a coefficient-denominator estimate to give an integer contradiction. The companion’s [rational-value model](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-countermodel) has the same formal orders, leading coefficients and type of fixed-base power correction, but a rational target value. Its denominator calculation shows why clearing need not yield small nonzero integer forms. The model and its denominator argument have ordinary proofs only and are not used above.

The approximants’ polynomial coefficients pose a separate moment problem. The normalisation matters in Van Assche’s little-$`q`$-Legendre construction \[vanassche2001, §3\] and the multiple-orthogonality construction of Postelmans and Van Assche \[postelmansvanassche2007, §2\]. In the 2016 family, the companion paper proves positivity of the first matrix of a coefficient pencil for sizes $`N\le8`$, with real, interlacing roots below $`F(p)`$ for $`p>1`$. The shifted minors and coefficientwise positivity are supported by the stated finite polynomial computations. The [coefficient-moment section](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-coefficients) gives the definitions and the precise ranges. Positivity for every $`N`$ and convergence of the largest root remain open. The general moment criteria of Wang and Zhu \[wangzhu2016\] and Sokal and Walrad \[sw2024\], Berg’s factorial-power example \[berg2007, Theorem 5.1\], and the quadrature construction of Golub and Welsch \[golubwelsch1969\] provide the relevant comparisons. Using a recurrence from another family would require a proof that it holds for these coefficients. The root-of-unity method of Krattenthaler, Rochev, Väänänen and Zudilin \[krvz2009\], for example, concerns a separate construction.

<a id="sec:round8-transfer-boundaries"></a>

## Congruences and divided forms

For $`Q\in\mathbb{Z}[X]`$ of degree at most $`W`$, the homogenised value $`H_W(Q)=2^WQ(3/2)`$ is integral. The companion treats its congruences at powers of $`2`$ and $`3`$, including [integer rescaling](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-arithmetic) and [endpoint congruences and signed sums](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-endpoints), with the rank-one case. Smith normal form counts the residue image \[stanley2016, Theorems 2.3–2.4\]. To obtain a small nonzero remainder after division, the count must also distinguish nearby real values from repeated ones.

Let $`M`$ integral rows $`(A_j,B_j)`$ have remainders $`e_j=A_jF(3/2)-B_j`$, and let $`D`$ be a positive integer. Suppose the subset sums $`\sum_{j\in I}(A_j,B_j)`$ take $`Q`$ values in $`(\mathbb Z/D\mathbb Z)^2`$, with at most $`k`$ subsets giving any fixed real remainder within a residue class. Put $`T=\sum_j|e_j|`$. The least and greatest subset remainders are
``` math
\sum_{e_j<0}e_j\quad\text{and}\quad\sum_{e_j>0}e_j;
```
their difference is $`T`$. For a positive integer $`n`$, divide this whole range into half-open intervals of width $`D/n`$, starting at its least value. At most $`\lfloor nT/D\rfloor+1`$ intervals suffice, including a last interval when the greatest value is an endpoint. If every residue–interval pair contained only one remainder value, it would contain at most $`k`$ subsets. Hence
``` math
\begin{equation}
\label{eq:quantitative-selector-budget}
 2^M>Qk\left(\left\lfloor\frac{nT}{D}\right\rfloor+1\right)
\end{equation}
```
forces two different remainders in one residue–interval pair. Subtracting the subset sums and dividing by $`D`$ gives an integral linear form of nonzero absolute value less than $`1/n`$: the residue condition gives integrality, the interval gives smallness, and the multiplicity bound prevents a zero difference. The [quantitative lemma and its proof](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-selectors) state the finite-set result independently of Lambert series. Distinct input rows do not rule out equal subset remainders; $`k`$ bounds repetitions within a residue class. No family of bounds on $`Q,T,k`$ satisfying <a href="#eq:quantitative-selector-budget" data-reference-type="eqref" data-reference="eq:quantitative-selector-budget">[eq:quantitative-selector-budget]</a> for arbitrarily large $`n`$ at $`3/2`$ is supplied here.

The elementary integer-base method provides a different comparison. Vandehey \[vandehey2013\] and Duverney and Tachiya \[duverneytachiya2019\] use integer-base expansions. At a noninteger rational base the [cleared-tail recurrence](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L187) has a growing denominator contribution. The [clearing and tail-recurrence calculations](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-clearing) in the companion paper include the [coordinatewise obstruction at $`3/2`$](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L155). They make no assertion about other approximation families. At the function level, Bell and Smertnig \[bellsmertnig2026, Theorem 1.3\] exclude Mahler equations for the divisor generating series, while leaving the arithmetic of a single rational argument undecided.

<a id="prob:kernel"></a>

#### A construction problem.

The unrestricted request for primitive polynomial rows and a signed combination with divided remainder strictly between $`0`$ and $`1/n`$ is equivalent to irrationality of the target; the companion’s [section on divided linear forms](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-open-construction) states and proves the equivalence. A more specific problem must prescribe a family: for the 2004 forms, the question is whether a parameter direction improves $`\theta^*`$. The [all-base degree restriction](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-region-extensions) bounds the degree cutoff by $`1/2`$. It assumes one polynomial family, with common leading constants in its degree, coefficient-height and remainder estimates at every fixed real base $`x>1`$; errors may depend on $`x`$. A cutoff above $`1/2`$ would make remainder decay outpace coefficient growth at a sufficiently large fixed integer base. Consecutive integer row determinants would then tend to zero and eventually vanish, forcing the rational row ratios to stabilise. The remainders would be either zero or bounded away from zero, contradicting nonzero decay. Estimates only at $`3/2`$ do not permit that choice of base.

Under the same hypotheses, the [nondecay corollary](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-no-decay) excludes decay of the denominator-cleared, undivided forms whenever $`b<a<b^2`$, including $`3/2`$, without assuming a quadratic degree limit. If that limit exists, their absolute values tend to infinity throughout this strict region. Further division by base-dependent content and families outside these hypotheses remain unclassified, as does equality in the cutoff of Section <a href="#sec:rational-base-irrationality" data-reference-type="ref" data-reference="sec:rational-base-irrationality">4</a>.

<a id="app:index"></a>

# Verification and reproducibility

The [evidence record](https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1049-rational-base-lambert.md) lists Lean proofs for all seven numbered results and Comparator checks for six, with their checked revisions. Beside the [main source revision](https://github.com/wcook04/plectis-erdos/tree/7380b7871687b6bcc41ca0143c61f232e8af6500), Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">2</a> uses the later [geometric-moment proof](https://github.com/wcook04/plectis-erdos/blob/035c414b25fda09ae0d2e56358b8716d321ebd99/lean/ErdosProblems/Erdos1049/PaperCompleteR21/GeometricUniversality.lean#L1324); its Comparator association remains pending. Neither the broader ratio-limit argument nor the rational-value model is a dependency; both have ordinary proofs only. This expository revision changes no result statement and has no fresh Lean or Comparator run or independent review.

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1049-rational-base-lambert.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

<a id="data-availability."></a>

#### Data availability.

The cited source revision contains the Lean sources, toolchain and library manifest. The companion paper supplies the longer algebraic arguments and the precise scope of the finite computations.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem numbering follows the catalogue maintained by Thomas Bloom \[erdosproblems\].

<div class="thebibliography">

99

P. Erdős, *On the irrationality of certain series: problems and results*, in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). P. Bundschuh and K. Väänänen, [*Arithmetical investigations of a certain infinite product*](https://numdam.org/item/CM_1994__91_2_175_0.pdf), Compositio Math. **91** (1994), no. 2, 175–199. W. Zudilin, *Remarks on irrationality of $`q`$-harmonic series*, Manuscripta Math. **107** (2002), no. 4, 463–477, doi:[10.1007/s002290200249](https://doi.org/10.1007/s002290200249). W. Zudilin, [*Heine’s basic transform and a permutation group for $`q`$-harmonic series*](https://geodesic.mathdoc.fr/articles/10.4064/aa111-2-4/), Acta Arith. **111** (2004), no. 2, 153–164, doi:[10.4064/aa111-2-4](https://doi.org/10.4064/aa111-2-4). Page references are to the printed journal pages. W. Zudilin, [*On the irrationality of generalized $`q`$-logarithm*](https://arxiv.org/abs/1601.02688v2), arXiv:1601.02688; Res. Number Theory **2** (2016), Art. 15, doi:[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x). Page references are to arXiv:1601.02688v2. The remark that the results extend to non-integer $`p=r/s`$, $`|p|>1`$, under an assumption $`\log|r|>c\log|s|`$ for a computable $`c>0`$, is in Section 2, p. 4, in the paragraph beginning “Finally, we remark”; no value of $`c`$ is computed there, and the remark is made for the generalized $`q`$-logarithm of that paper. R. P. Stanley, *Smith normal form in combinatorics*, J. Combin. Theory Ser. A **144** (2016), 476–495, doi:[10.1016/j.jcta.2016.06.013](https://doi.org/10.1016/j.jcta.2016.06.013); arXiv:[1602.00166v1](https://arxiv.org/abs/1602.00166v1). Page references are to arXiv:1602.00166v1. W. Zudilin, *A determinantal approach to irrationality*, Constr. Approx. **45** (2017), no. 2, 301–310, doi:[10.1007/s00365-016-9333-7](https://doi.org/10.1007/s00365-016-9333-7); arXiv:[1507.05697v1](https://arxiv.org/abs/1507.05697v1). Page and equation references are to arXiv:1507.05697v1. T. F. Bloom, [*Erdős Problem \#1049*](https://www.erdosproblems.com/1049), `erdosproblems.com/1049`. Accessed 28 July 2026, when the page displayed “last edited 28 September 2025”. J. Bell and D. Smertnig, [*Mahler series with multiplicative coefficient sequences*](https://arxiv.org/abs/2603.23456v1), arXiv:2603.23456v1, 24 March 2026. Theorem 1.3 is on pp. 2–3; its stated consequences on p. 3 include that the divisor and totient generating series are not $`k`$-Mahler for any $`k\ge2`$. J. Vandehey, [*On an incomplete argument of Erdős on the irrationality of Lambert series*](https://arxiv.org/abs/1206.0340v1), Integers **13** (2013), Paper A58. Page references are to arXiv:1206.0340v1 (2012). D. Duverney and Y. Tachiya, *Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*, Forum Math. **31** (2019), no. 6, 1557–1566, doi:[10.1515/forum-2018-0299](https://doi.org/10.1515/forum-2018-0299). Page references are to the [authors’ version](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf). W. Van Assche, [*Little $`q`$-Legendre polynomials and irrationality of certain Lambert series*](https://arxiv.org/abs/math/0101187v1), Ramanujan J. **5** (2001), no. 3, 295–310, doi:[10.1023/A:1012930828917](https://doi.org/10.1023/A:1012930828917). Page references are to arXiv:math/0101187v1. K. Postelmans and W. Van Assche, [*Irrationality of $`\zeta_q(1)`$ and $`\zeta_q(2)`$*](https://arxiv.org/abs/math/0604312v1), J. Number Theory **126** (2007), no. 1, 119–154, doi:[10.1016/j.jnt.2006.11.011](https://doi.org/10.1016/j.jnt.2006.11.011). Page references are to arXiv:math/0604312v1 (2006). C. Krattenthaler, I. Rochev, K. Väänänen and W. Zudilin, *On the non-quadraticity of values of the $`q`$-exponential function and related $`q`$-series*, Acta Arith. **136** (2009), no. 3, 243–269, doi:[10.4064/aa136-3-4](https://doi.org/10.4064/aa136-3-4); arXiv:[0812.2921v1](https://arxiv.org/abs/0812.2921v1). Page references are to arXiv:0812.2921v1. Y. Wang and B.-X. Zhu, [*Log-convex and Stieltjes moment sequences*](https://arxiv.org/abs/1612.04114v1), Adv. Appl. Math. **81** (2016), 115–127, doi:[10.1016/j.aam.2016.06.008](https://doi.org/10.1016/j.aam.2016.06.008). Page references are to arXiv:1612.04114v1. C. Berg, *On powers of Stieltjes moment sequences, II*, J. Comput. Appl. Math. **199** (2007), 23–38; arXiv:[math/0412340v1](https://arxiv.org/abs/math/0412340v1). Theorem references use the preprint; Theorem 5.1 treats factorial powers. A. D. Sokal and J. Walrad, *Continued-fraction characterization of Stieltjes moment sequences with support in $`[\xi,\infty)`$*, [arXiv:2404.12131v1](https://arxiv.org/abs/2404.12131v1), 2024. The classical Stieltjes criterion is recalled on pp. 1–2. G. H. Golub and J. H. Welsch, *Calculation of Gauss Quadrature Rules*, Math. Comp. **23** (1969), no. 106, 221–230, doi:[10.1090/S0025-5718-69-99647-1](https://doi.org/10.1090/S0025-5718-69-99647-1). C. R. Vinroot, [*Multivariate Rogers–Szegő polynomials and flags in finite vector spaces*](https://arxiv.org/abs/1011.0984), arXiv:1011.0984v1, 3 November 2010, abstract accessed 20 September 2026. Cited for the identification of the sum of all $`q`$-multinomial coefficients of fixed degree and length with a flag count, and for its recursion generalising the Galois numbers. The factorisation of the moment weights is proved here.

</div>
