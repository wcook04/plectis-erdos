<a id="erdos-1049-rational-base-lambert"></a>

# Hankel Determinants of Geometric Moments and Rational Lambert Values

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We determine the fixed-base asymptotic of Zudilin’s normalised Hankel determinants, including the constant and the factor $`N^{-8F(1/q)}`$, where $`F(t)=\sum_{n\ge1}(t^n-1)^{-1}`$. The proof uses positive geometric moments and a bound on the partition sum independent of $`N`$. Separately, we extend the rational-base irrationality region for $`F`$ by calculating the degrees after cancellation in Zudilin’s 2004 forms. The region includes every positive integral power of $`31/4`$, but excludes $`3/2`$.

<a id="sec:problem"></a>

# Introduction

For each fixed real $`q\in(0,1)`$, we determine the asymptotic size of the Hankel determinants arising from Zudilin’s $`q`$-logarithm approximations. Write $`(z;q)_m=\prod_{j=0}^{m-1}(1-zq^j)`$ and $`F(t)=\sum_{n\ge1}(t^n-1)^{-1}`$ for $`t>1`$. At the auxiliary parameters $`x=z=1`$, the normalisation in \[zudilin2016, (6), §4\] gives
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
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/SharpFixedBaseShort.lean#L53">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-1049-rational-base-lambert.md#res-sharp-fixed-base-comparator">Comparator</a></p>

**Theorem 1** (the size of $`V_N^*`$ at a fixed base). *Fix $`0<q<1`$ and write $`P=(q;q)_\infty`$, $`B_N=N(N-1)(2N-1)/6`$ and $`C_N=(N!)^2(N+1)!/2^N`$. There is a $`K(q)>0`$ with
``` math
V_N^*(q)\sim K(q)\,C_Nq^{B_N}P^{2N}N^{-8F(1/q)}
 \qquad(N\to\infty).
```*

</div>

The constant $`K(q)`$ is the convergent product in <a href="#eq:fixed-constant" data-reference-type="eqref" data-reference="eq:fixed-constant">[eq:fixed-constant]</a>. Zudilin proved $`\operatorname{ord}_q V_N^*\ge B_N`$ and the estimate $`|V_N^*|\le q^{N^3/3}\exp(O_q(N^2))`$ \[zudilin2016, Lemma 1 and §4\]. Theorem <a href="#res:sharp-fixed-base" data-reference-type="ref" data-reference="res:sharp-fixed-base">1</a> determines the factorial, exponential and power factors contained in this estimate. The long record also determines the exact first formal term $`C_Nq^{B_N}`$. These are different limiting questions: multiplying by $`(1-q)^{N^3}`$ preserves that first term and changes the fixed-base logarithm by a cubic quantity. No uniformity as $`q\to1`$ is asserted.

We represent $`v_m^*`$ as $`\sum_{k\ge0}a_kq^{(m+1)k}`$ with $`a_k>0`$. These are the moments of a positive measure supported on $`1,q,q^2,\ldots`$. Heine’s identity then expresses the determinant as a sum over choices of $`N`$ nodes, with a squared Vandermonde factor for each choice \[zudilin2017det, §2, (2)–(5)\]. The contribution of the first $`N`$ nodes has size $`q^{B_N}P^{2N}\prod_{k<N}a_k`$ up to a positive limiting factor. Moving the last node one place still gives a contribution of comparable size, so we must sum over displaced tuples. We index them by partitions. For each fixed partition, the weight ratios tend to $`1`$; a summable bound independent of $`N`$ then permits passage to the limit in the sum. The resulting limit is the same as for constant weights, for which Cauchy’s determinant formula gives an exact evaluation.

The remaining calculation concerns the weights themselves. Their factorisation involves a two-fold and a three-fold convolution of the sequence $`1/(q;q)_k`$. Their first relative corrections are $`-2F(1/q)/(k+1)`$ and $`-6F(1/q)/(k+2)`$. Adding these corrections and then multiplying the weights over $`k<N`$ gives the power $`N^{-8F(1/q)}`$. Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">2</a> isolates the determinant argument from this coefficient calculation; it also evaluates the determinant with entries $`(1-q^{i+j+1})^{-2}`$.

Chowla’s conjecture, recorded by Erdős \[erdos1988, p. 102\], asks whether $`F(t)`$ is irrational for every rational $`t>1`$. This is a related arithmetic question, and the fixed-base asymptotic alone does not answer it. In Section <a href="#sec:rational-base-irrationality" data-reference-type="ref" data-reference="sec:rational-base-irrationality">4</a> we use the different 2004 construction \[zudilin2004, §5\] to prove irrationality for coprime $`a>b\ge1`$ satisfying
``` math
\frac{\log b}{\log a}<\theta^*
 =0.4056830213840605\ldots,
```
where <a href="#eq:threshold-constants" data-reference-type="eqref" data-reference="eq:threshold-constants">[eq:threshold-constants]</a> defines $`\theta^*`$ exactly. The calculation cancels the common polynomial factors before clearing denominators at $`a/b`$. It includes every positive integral power of $`31/4`$. Neither this region nor the determinant argument settles the case $`3/2`$.

Section <a href="#sec:geometric-moments" data-reference-type="ref" data-reference="sec:geometric-moments">2</a> proves the general determinant formula. Section <a href="#sec:weights" data-reference-type="ref" data-reference="sec:weights">3</a> constructs the weights and proves Theorem <a href="#res:sharp-fixed-base" data-reference-type="ref" data-reference="res:sharp-fixed-base">1</a>. The rational-base argument is self-contained in Section <a href="#sec:rational-base-irrationality" data-reference-type="ref" data-reference="sec:rational-base-irrationality">4</a>, with longer calculations and complementary questions linked in Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">5</a>. All logarithms are natural, empty products and determinants equal $`1`$, and constants in $`O_q(\cdot)`$ may depend on the fixed $`q`$.

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
Under the following hypotheses, replacing the constant weights by $`a_k`$ multiplies the asymptotic by $`\prod_{k<N}a_k`$. The ratio limit controls each fixed displacement of a node, while the polynomial bound controls the sum over all displacements. The power weights $`a_k=(k+1)^s`$, with $`s\in\mathbb R`$, satisfy both conditions.

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

<div class="proof">

*Proof of Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">2</a>.* The bound $`a_h\le Ca_0(1+h)^\kappa`$ ensures convergence of every moment. Apply Cauchy–Binet to a finite set of nodes and let its size tend to infinity. The matrix entries converge, while positivity permits passage to the limit in the sum, giving
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
Only pairs involving the moved node change, so the product telescopes. At $`q=1/2`$ the limiting ratio is $`2`$: the displaced tuple contributes twice as much asymptotically as $`(0,1,\ldots,N-1)`$.

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
The $`j`$th index from the right contributes once through $`q^{k_i}`$ and twice through each of its $`j-1`$ pairs with later indices in the squared Vandermonde. Its displacement therefore has exponent $`1+2(j-1)=2j-1`$.

Set $`W_N(\mu)=0`$ when $`\mu`$ has more than $`N`$ positive parts, so that every sum has the same index set. Fix a partition with $`\ell`$ positive parts. It affects only the last $`\ell`$ indices of $`(0,1,\ldots,N-1)`$: for instance, $`(2,1)`$ affects the last two for every $`N\ge2`$. Those indices tend to infinity, so the weight ratios in <a href="#eq:partition-summand" data-reference-type="eqref" data-reference="eq:partition-summand">[eq:partition-summand]</a> tend to $`1`$ by the fixed-shift hypothesis.

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

To pass this limit through the sum over partitions, we need a bound independent of $`N`$ that remains summable as both the number and size of the parts grow. Only factors with $`j\le\ell`$ can differ from $`1`$. For each such $`j`$, the denominator product in the Vandermonde quotient is at least $`P`$, and its numerator product is at most $`1`$. Together with the polynomial shift bound, this gives
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
Here $`q^{(2j-1)u}\le q^{2j-1}q^{u-1}`$ and $`1+3+\cdots+(2\ell-1)=\ell^2`$. Since $`q<1`$, the bound $`(CP^{-2}A)^\ell q^{\ell^2}`$ is summable over $`\ell`$, independently of $`N`$.

Dominated convergence now shows that $`\sum_\mu W_N(\mu)`$ has the same limit as for $`a_k=1`$. This common limit is positive, since the empty partition contributes $`1`$. Restoring the contribution of $`(0,1,\ldots,N-1)`$ gives
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
These identities hold formally in $`\mathbb{Z}[[q,w]]`$ and, for fixed $`0<q<1`$, analytically for $`|w|<1`$. In the formal identity only finitely many $`t`$ contribute to any $`w`$-coefficient. For the analytic identity, we use the absence of denominator zeros in that disc and the locally uniform bounds on the product tails. The factor $`w^t`$ then gives locally uniform convergence of the sum. To prove positivity and obtain a bound uniform in the shift, we express its coefficients as finite sums.

<a id="sec:weight-factorisation"></a>

## Positive weights

For $`r\ge1`$ and $`k\ge0`$, set
``` math
R_k^{(r)}(q)=\sum_{n_1+\cdots+n_r=k}
              \frac{(q;q)_k}{\prod_{j=1}^r(q;q)_{n_j}},
```
over $`r`$ nonnegative parts. These are the multivariate Rogers–Szegő polynomials at unit arguments, written as sums of Gaussian multinomial polynomials \[vinroot2010\]. At $`q=0`$ they count compositions, and
``` math
c_k:=R_k^{(2)}(0)R_k^{(3)}(0)=\frac{(k+1)^2(k+2)}2,
 \qquad \prod_{k<N}c_k=C_N.
```

<div class="samepage">

<div id="prop:weight-factorisation" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RogersFactorisationAnalytic.lean#L1312">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-1049-rational-base-lambert.md#prop-weight-factorisation-comparator">Comparator</a></p>

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

*Proof.* We use the Gaussian binomial coefficients $`\genfrac{[}{]}{0pt}{}{n}{j}_q=(q;q)_n/((q;q)_j(q;q)_{n-j})`$ for $`0\le j\le n`$, and put $`\mathcal E(z)=(z;q)_\infty^{-1}`$. Euler’s expansion gives $`\mathcal E(z)^r=\sum_{n\ge0}R_n^{(r)}z^n/(q;q)_n`$. To obtain $`R_k^{(2)}R_k^{(3)}`$, we shift the coefficients of $`\mathcal E^3`$ and sum over decompositions of the index. The unnormalised $`q`$-difference operator $`\partial_qf(z)=(f(z)-f(qz))/z`$ is convenient because $`\partial_qz^j=(1-q^j)z^{j-1}`$ cancels the last factor of $`(q;q)_j`$. In particular,
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

It remains to prove the fixed-shift limit and determine the product $`\prod_{k<N}a_k`$. Both follow from the first-order asymptotic of $`a_k/c_k`$.

<a id="sec:coefficient-asymptotic"></a>

## The coefficient asymptotic

<div class="proof">

*Proof of Theorem <a href="#res:sharp-fixed-base" data-reference-type="ref" data-reference="res:sharp-fixed-base">1</a>.* Put $`L=F(1/q)`$, $`e_k=(q;q)_k^{-1}`$ and $`E=P^{-1}`$. Replacing every $`e_k`$ by $`E`$ in the two convolution sums gives $`E^2(k+1)`$ and $`E^3\binom{k+2}{2}`$. The factors $`k+1`$ and $`\binom{k+2}{2}`$ count nonnegative pairs and triples with sum $`k`$. For a fixed $`i`$, one pair and $`k-i+1`$ triples have first coordinate $`i`$. Consequently, the summable differences $`E-e_i`$ produce a constant correction in the two-fold convolution and a linear correction in the three-fold convolution. The terms containing two or more such differences contribute to the error bounds below.

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
The differentiation is justified by locally uniform convergence on $`|z|<1`$.

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
Dividing the correction $`-3L(k+1)`$ by the leading term $`\binom{k+2}{2}`$ gives the relative correction $`-6L/(k+2)`$. The two-fold convolution contributes $`-2L/(k+1)`$ in the same way. Since $`(q;q)_k=P(1+O_q(q^k))`$, the leading constants in $`a_k=P^4(q;q)_k b_k^{(2)}b_k^{(3)}`$ multiply to $`P^5E^5=1`$. With $`c_k=(k+1)^2(k+2)/2`$, the two relative corrections therefore give
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
Positivity of $`a_k`$ and summability of $`\log(a_k/c_k)+8L/(k+1)=O_q((k+1)^{-2})`$ show that $`\mathcal A(q)`$ converges to a positive number. Since $`\prod_{k<N}c_k=C_N`$, we can separate these contributions exactly:
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

Thus the product of the cubic weights $`c_k`$ gives $`C_N`$, whereas the first correction to $`a_k/c_k`$ determines $`N^{-8F(1/q)}`$.

The corresponding formal-series calculation, including the exact first term $`C_Nq^{B_N}`$, is given in the [long record](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=scope-formal-order). It concerns the limit $`q\to0`$ and is separate from the fixed-$`q`$ asymptotic proved above.

<a id="sec:rational-base-irrationality"></a>

# Rational bases

We now use the 2004 coefficient family. If $`U,V\in\mathbb{Z}[X]`$ have degree at most $`W`$, evaluation at $`a/b`$ requires the factor $`b^W`$ to produce integer coefficients. A common polynomial factor should therefore be cancelled first. For example, at $`3/2`$ the pair $`(X+1)(X+2),(X+1)(X+3)`$ gives $`(35,45)`$ after clearing to degree $`2`$. After cancelling $`X+1`$, clearing to degree $`1`$ gives $`(7,9)`$. For Zudilin’s forms, the degrees are of quadratic order in the index $`n`$. Write $`K_n`$ for the degree of the original coefficient and $`W_n`$ for its degree after cancellation. The cancelled remainder has leading size $`x^{-(K_n-W_n)}`$ at a fixed real base $`x>1`$. At $`x=a/b`$, clearing the coefficients therefore has the balance
``` math
\begin{equation}
\label{eq:degree-balance}
 b^{W_n}(a/b)^{-(K_n-W_n)}
 =\frac{b^{K_n}}{a^{K_n-W_n}}.
\end{equation}
```
The proof below shows that the remaining factors contribute only $`o(n^2)`$ to the logarithm. Hence the limits $`K_n/n^2\to C_1`$ and $`(K_n-W_n)/n^2\to C_0`$ give the sufficient inequality $`C_1\log b<C_0\log a`$. We first justify cancellation in $`\mathbb{Z}[X]`$ and calculate the degrees, before specialising $`X`$ to $`a/b`$.

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
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-1049-rational-base-lambert.md#res-rational-base-threshold">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-1049-rational-base-lambert.md#res-rational-base-threshold-comparator">Comparator</a></p>

**Theorem 4** (rational-base region for Zudilin’s forms). *Let $`a>b\ge1`$ be coprime integers with
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

The condition holds for every integer base, since $`b=1`$ gives $`\log b/\log a=0`$. For a fixed denominator $`b>1`$, it requires $`a>b^{2.46497868\ldots}`$, much more than $`a>b`$; nevertheless it gives infinitely many reduced noninteger rational bases for each such $`b`$. The base $`31/4`$ satisfies the condition, and taking a common positive integer power of the numerator and denominator leaves their logarithmic ratio unchanged. Since $`\theta^*<1/2<\log2/\log3`$, the condition fails at $`3/2`$. At equality $`\log b/\log a=\theta^*`$ the quadratic exponent vanishes, so the estimates below give no conclusion.

<div class="proof">

*Proof of Theorem <a href="#res:rational-base-threshold" data-reference-type="ref" data-reference="res:rational-base-threshold">4</a>.* We first identify the integral polynomials obtained by cancellation. We then compute their degrees and the size of the cleared remainder, which will justify <a href="#eq:degree-balance" data-reference-type="eqref" data-reference="eq:degree-balance">[eq:degree-balance]</a> to quadratic order.

*The source forms and polynomial cancellation.* Fix $`n\ge1`$ and set
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

We first bound the remainder before cancellation. For $`x>1`$ we put $`q=1/x`$ and use identity (9) on p. 156 of the source, which gives the positive representation
``` math
H_n(x)=\sum_{t\ge0}q^{a_0t}
 \frac{(q^{t+1};q)_{a_1-1}}{(q;q)_{a_1-1}}
 \frac{(q;q)_{\beta-a_2-1}}{(q^{a_2+t};q)_{\beta-a_2}}.
```
The denominator length is $`\beta-a_2`$, as in the gamma expression (7) and residues (8) of \[zudilin2004, p. 156\]; the unnumbered display of $`R(T)`$ on that page has length $`\beta-a_2-1`$ instead. Each of the four finite products displayed above lies between $`P=(q;q)_\infty>0`$ and $`1`$, so
``` math
P^2\le H_n(x)\le\frac{P^{-2}}{1-q^{a_0}}.
```
In particular $`H_n(x)>0`$ and $`\log H_n(x)=O_x(1)`$.

To identify the integral polynomials we use the inclusion in Zudilin’s Lemma 7, display (23) \[zudilin2004, p. 161\]. The proof compares the cyclotomic valuations of the coefficient polynomials under six admissible parameter permutations, and gives the divisibility in $`\mathbb{Z}[X]`$ that we need before evaluation. Its parameter vector is $`n(13,14,12,14,15,13)`$, its maximum is $`15n`$, and $`\beta-a_1-a_2=n>0`$, which is the positivity condition $`s>0`$ of the lemma. The conditions (14) of \[zudilin2004, p. 157\], $`a_1\le a_2`$ and $`a_1+a_2\le\beta\le a_0+a_2`$, hold as well, so the exponent in (23) is the integer (16), which equals $`M_n`$. Lemma 7 therefore gives, for every $`n\ge1`$,
``` math
\Lambda_n(X)=X^{-M_n}\frac{D_N(X)}{\Omega_n(X)}H_n(X)
            =U_n(X)F(X)-V_n(X),\qquad U_n,V_n\in\mathbb Z[X].
```
This is the polynomial conclusion before integer specialisation in the source’s (24), p. 162. The coefficients are the cancelled source coefficients:
``` math
U_n=X^{-M_n}(D_N/\Omega_n)A_n,\qquad
 V_n=X^{-M_n}(D_N/\Omega_n)B_n.
```
Indeed, coefficients of $`F`$ and $`1`$ over $`\mathbb{Q}(X)`$ are unique because $`F`$ is not a rational function. To see this, we split $`F(e^h)`$ at $`m=1/h`$ as $`h\downarrow0`$. For $`m\le1/h`$, the inequalities $`y^{-1}-1\le(e^y-1)^{-1}\le y^{-1}`$ for $`0<y\le1`$ give $`h^{-1}\sum_{m\le1/h}m^{-1}+O(h^{-1})`$. Bounding the remaining terms by a geometric tail gives a further $`O(h^{-1})`$, and therefore $`F(e^h)=h^{-1}\log(1/h)+O(h^{-1})`$, which has no rational-function pole order at $`X=1`$. The cancelled remainder is positive for $`x>1`$, since $`D_N/\Omega_n`$ is a product of cyclotomic polynomials positive there.

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
The factor $`X^{-M_n}`$ lowers the degree by $`M_n`$, whereas the remaining cyclotomic factors increase it by $`\deg(D_N/\Omega_n)`$. Their difference will determine the decay of the cancelled remainder.

The bounds for $`H_n`$ are uniform for $`x\ge2`$: then $`P\ge\prod_{j\ge1}(1-2^{-j})>0`$ and $`(1-x^{-a_0})^{-1}\le2`$. For fixed $`n`$, therefore, $`H_n(x)=O(1)`$ and $`\Lambda_n(x)=O(x^{W_n-K_n})`$ as $`x\to\infty`$. The unique top summand of $`A_n`$ has leading coefficient $`(-1)^{a_1+a_2+\beta}=(-1)^n`$. Since the Gaussian factors and $`D_N/\Omega_n`$ are monic, $`U_n`$ has that leading coefficient too. Moreover $`F(x)=x^{-1}+O(x^{-2})`$ and $`K_n\ge2`$, so
``` math
V_n(x)=U_n(x)F(x)-\Lambda_n(x)
       =(-1)^n x^{W_n-1}+O(x^{W_n-2}).
```
Here $`W_n\ge K_n-M_n=(559n^2+13n)/2>0`$. Thus $`\deg V_n=W_n-1`$, with the same unit leading coefficient as $`U_n`$. For every prime $`p\mid b`$, reduction of the cleared first coordinate gives
``` math
b^{W_n}U_n(a/b)\equiv(-1)^n a^{W_n}\not\equiv0\pmod p.
```
Thus $`U_n(a/b)`$ has reduced denominator exactly $`b^{W_n}`$, the least common clearing denominator for this pair. Every common integer divisor of the cleared row is consequently coprime to $`b`$. This leaves common factors at other primes and savings from combinations of different rows to be analysed separately.

*The quadratic degree limits.* The degree calculation kept $`n`$ fixed and let $`x\to\infty`$. For the irrationality argument we now keep $`x`$ fixed and let $`n\to\infty`$. We first find the quadratic part of the degree removed by cancellation. The limits below are the cyclotomic limits of \[zudilin2004, Lemmas 1–2, p. 155\]. The proof uses the argument through reciprocal intervals, the summatory totient estimate and the trigamma function from the proof of \[zudilin2002, Lemma 1, p. 466\], with an explicit truncation of the block sum. The elementary summatory estimate $`\sum_{\ell\le y}\varphi(\ell)=3y^2/\pi^2+O(y\log y)`$ gives
``` math
\frac1{n^2}\sum_{\ell\le15n}\varphi(\ell)\longrightarrow\frac{675}{\pi^2}.
```
For $`[u,v)\in\mathcal I`$, the condition $`\{n/\ell\}\in[u,v)`$ is the disjoint union of intervals $`n/(k+v)<\ell\le n/(k+u)`$ for $`k\ge0`$. We may apply the same summatory estimate term by term to any finite set of $`k`$. If we stop before $`k=K`$, with $`K\ge1`$, every omitted block has $`\ell\le n/(K+u)`$. Thus the elementary bound $`\sum_{\ell\le y}\varphi(\ell)\le y^2`$ for $`y\ge0`$ gives the uniform estimate
``` math
\frac1{n^2}\sum_{\ell\le n/(K+u)}\varphi(\ell)
 \le\frac1{(K+u)^2}.
```
Indeed, for $`y\ge1`$ one can bound $`\varphi(\ell)`$ by $`\ell`$ and sum; for $`0\le y<1`$ the sum is empty. This bound is uniform in $`n`$. We can now let $`n`$ and then $`K`$ tend to infinity, obtaining
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

*The cleared remainder.* We return to a fixed real base $`x>1`$ and estimate the cyclotomic product. Writing $`\mu_{\rm Mob}`$ for the Möbius function, we have
``` math
\log\Phi_\ell(x)-\varphi(\ell)\log x
 =\sum_{d\mid\ell}\mu_{\rm Mob}(d)\log(1-x^{-\ell/d}).
```
The total absolute error over $`\ell\le15n`$ is $`O_x(n)`$, since it is at most
``` math
15n\sum_{d\ge1}\frac{-\log(1-x^{-d})}{d}.
```
The series converges because $`-\log(1-x^{-d})\le x^{-d}/(1-x^{-1})`$. Since $`0\le1-\nu_\ell\le1`$, it follows that
``` math
\log\Lambda_n(x)=-(K_n-W_n)\log x+O_x(n).
```

We can now clear the denominators at the rational base. Since $`U_n,V_n\in\mathbb{Z}[X]`$ and their degrees are at most $`W_n`$, the numbers $`b^{W_n}U_n(a/b)`$ and $`b^{W_n}V_n(a/b)`$ are integers. Moreover
``` math
\begin{split}
 \log\bigl(b^{W_n}\Lambda_n(a/b)\bigr)
 &=K_n\log b-(K_n-W_n)\log a+O_{a/b}(n)\\
 &=\bigl(C_1\log b-C_0\log a\bigr)n^2+o(n^2).
\end{split}
```
The coefficient is negative under the theorem’s hypothesis. The positive values of these integer-coefficient forms therefore tend to zero. If $`F(a/b)=r/s`$ with integers $`r,s`$ and $`s\ne0`$, every nonzero value would have absolute value at least $`1/|s|`$, a contradiction. ◻

</div>

<div id="res:thirtyone-four" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L117">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-1049-rational-base-lambert.md#res-thirtyone-four-comparator">Comparator</a></p>

**Corollary 5**. *$`F\bigl((31/4)^r\bigr)`$ is irrational for every integer $`r\ge1`$.*

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

The same forms also give an irrationality-exponent bound uniform over positive integral powers of the base. Its statement and proof are in the [long record’s quantitative extension](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=scope-measure).

<a id="comparison-with-earlier-criteria"></a>

## Comparison with earlier criteria

Bundschuh and Väänänen’s Theorem 2 at $`\alpha=-1`$ \[bv1994, p. 177\] gives irrationality for $`\log b/\log a<\theta_{\rm BV}:=1/2-1/\pi^2`$. Their $`q`$ is the base $`a/b>1`$, not its reciprocal. Their logarithmic derivative is $`L_q(z)=\sum_{j\ge1}(q^j+z)^{-1}`$, so the value at $`z=\alpha=-1`$ is exactly $`F(a/b)`$. The rational height is $`h(q)=a`$, and their parameter $`\lambda=\log h(q)/\log q`$ is $`1/(1-\log b/\log a)`$, which gives the displayed cutoff. Since $`\pi^2<10`$, one has $`\theta_{\rm BV}<2/5<\log4/\log31`$, so $`31/4`$ lies outside that sufficient region. The two sufficient regions differ on $`[\theta_{\rm BV},\theta^*)`$. Zudilin also notes an extension to noninteger rational bases $`p=r/s`$ for the generalized $`q`$-logarithm when $`\log|r|>c\log|s|`$, with $`c>0`$ computable but unspecified \[zudilin2016, Sec. 2, p. 4\]. For $`F`$, the specialisation above gives $`c=\mu`$, the exponent bound of \[zudilin2004, p. 162\].

The positive-remainder estimates require $`x>1`$, so they give no statement for negative bases. The series diverges at $`x=1`$. The companion record also checks the parameters at $`7/2`$ in its section on Bundschuh and Väänänen’s height criterion. The analytic irrationality result used there is their cited theorem.

<a id="sec:open"></a>

# Scope and verification

The fixed-base determinant asymptotic and the rational-base region answer different questions about the same Lambert series. Neither establishes irrationality at $`3/2`$, and the region’s boundary is not decided by the strict inequality used in its proof. The [long record’s further questions](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=scope-further-questions) develops the remaining congruence and approximation questions.

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-1049-rational-base-lambert.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">2</a> is the polynomial-bound specialisation of the geometric-moment proof identified in the [verification section](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=scope-verification); its Comparator association remains pending. That section distinguishes formal coverage from the ordinary extensions and gives the source and reproduction details.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem numbering follows the catalogue maintained by Thomas Bloom \[erdosproblems\]. I thank Wouter van Doorn for advice on writing for a first-time reader and explaining the force of a hypothesis.

<div class="thebibliography">

99

P. Erdős, *On the irrationality of certain series: problems and results*, in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). P. Bundschuh and K. Väänänen, [*Arithmetical investigations of a certain infinite product*](https://numdam.org/item/CM_1994__91_2_175_0.pdf), Compositio Math. **91** (1994), no. 2, 175–199. W. Zudilin, *Remarks on irrationality of $`q`$-harmonic series*, Manuscripta Math. **107** (2002), no. 4, 463–477, doi:[10.1007/s002290200249](https://doi.org/10.1007/s002290200249). W. Zudilin, [*Heine’s basic transform and a permutation group for $`q`$-harmonic series*](https://geodesic.mathdoc.fr/articles/10.4064/aa111-2-4/), Acta Arith. **111** (2004), no. 2, 153–164, doi:[10.4064/aa111-2-4](https://doi.org/10.4064/aa111-2-4). Page references are to the printed journal pages. W. Zudilin, [*On the irrationality of generalized $`q`$-logarithm*](https://arxiv.org/abs/1601.02688v2), arXiv:1601.02688; Res. Number Theory **2** (2016), Art. 15, doi:[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x). Page references are to arXiv:1601.02688v2. The remark that the results extend to non-integer $`p=r/s`$, $`|p|>1`$, under an assumption $`\log|r|>c\log|s|`$ for a computable $`c>0`$, is in Section 2, p. 4, in the paragraph beginning “Finally, we remark”; no value of $`c`$ is computed there, and the remark is made for the generalized $`q`$-logarithm of that paper. W. Zudilin, *A determinantal approach to irrationality*, Constr. Approx. **45** (2017), no. 2, 301–310, doi:[10.1007/s00365-016-9333-7](https://doi.org/10.1007/s00365-016-9333-7); arXiv:[1507.05697v1](https://arxiv.org/abs/1507.05697v1). Page and equation references are to arXiv:1507.05697v1. T. F. Bloom, [*Erdős Problem \#1049*](https://www.erdosproblems.com/1049), `erdosproblems.com/1049`. Accessed 28 July 2026, when the page displayed “last edited 28 September 2025”. C. R. Vinroot, [*Multivariate Rogers–Szegő polynomials and flags in finite vector spaces*](https://arxiv.org/abs/1011.0984), arXiv:1011.0984v1, 3 November 2010, abstract accessed 20 September 2026. Cited for the identification of the sum of all $`q`$-multinomial coefficients of fixed degree and length with a flag count, and for its recursion generalising the Galois numbers. The factorisation of the moment weights is proved here.

</div>
