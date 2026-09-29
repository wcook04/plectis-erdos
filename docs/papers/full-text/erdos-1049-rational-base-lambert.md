<a id="erdos-1049-rational-base-lambert"></a>

# Hankel Determinants of Geometric Moments and Rational Lambert Values

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We obtain an asymptotic formula for Hankel determinants of positive moments on a geometric sequence, allowing an exponential factor in the weights. For Zudilin’s normalised $`q`$-logarithm moments, it gives the leading constant and the correction $`N^{-8F(1/q)}`$, where $`F(t)=\sum_{n\ge1}(t^n-1)^{-1}`$. We also calculate the denominator cost of his 2004 forms at rational bases. It follows that $`F(a/b)`$ is irrational when $`a>b\ge1`$ are coprime and $`\log b/\log a<0.4056830213840605\ldots`$, with the constant defined below. This includes every positive integral power of $`31/4`$. The case $`3/2`$ remains open.

<a id="sec:problem"></a>

# Introduction

Heine’s identity expresses a Hankel determinant as an integral of a squared Vandermonde product. For moments supported on $`1,q,q^2,\ldots`$ it becomes a sum over increasing tuples of nonnegative integers \[zudilin2017det, §2, (2)–(5)\]. We use this expansion to determine the asymptotic determinant when the ratio of adjacent positive weights has a limit below $`q^{-1}`$.

For $`0<q<1`$ and $`0<\rho<q^{-1}`$, write
``` math
P=(q;q)_\infty=\prod_{d\ge1}(1-q^d),\qquad
 \mathcal M(\rho;q)=\prod_{d\ge1}(1-\rho q^d)^{-d},\qquad
 B_N=\frac{N(N-1)(2N-1)}6.
```
Here $`\rho`$ describes the growth of the weights and $`q`$ fixes the nodes. Both products converge, since their logarithms have summable tails.

<div id="thm:geometric-moments" class="theorem">

**Theorem 1** (geometric moment determinants). *Let $`0<q<1`$ and let $`a_k>0`$ for $`k\ge0`$ satisfy $`a_{k+1}/a_k\to\rho\in(0,q^{-1})`$ as $`k\to\infty`$. For the moments $`M_m=\sum_{k\ge0}a_kq^{(m+1)k}`$, define $`D_N=\det(M_{i+j})_{0\le i,j<N}`$. Then, as $`N\to\infty`$,
``` math
\begin{equation}
\label{eq:geometric-limit}
 D_N\sim \mathcal M(1;q)^2\mathcal M(\rho;q)\,
 q^{B_N}P^{2N}\prod_{k=0}^{N-1}a_k.
\end{equation}
```*

</div>

For $`a_k=\rho^k(k+1)^s`$, where $`s`$ is any real number, we have $`a_{k+1}/a_k=\rho((k+2)/(k+1))^s\to\rho`$ and the product in <a href="#eq:geometric-limit" data-reference-type="eqref" data-reference="eq:geometric-limit">[eq:geometric-limit]</a> is $`\rho^{N(N-1)/2}(N!)^s`$. In particular, by taking $`s=1`$ and summing the moments we obtain
``` math
\begin{equation}
\label{eq:squared-cauchy-example}
 \det\left(\frac1{(1-\rho q^{i+j+1})^2}\right)_{0\le i,j<N}
 \sim \mathcal M(1;q)^2\mathcal M(\rho;q)\,
 \rho^{N(N-1)/2}N!q^{B_N}P^{2N}.
\end{equation}
```
The same theorem applies to $`a_k=\rho^k\exp(\sqrt{k})`$, whose relative growth need not have a polynomial bound in the shift. No rate of convergence of $`a_{k+1}/a_k`$ is required.

To prove Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">1</a>, we compare an increasing tuple of node indices with $`(0,1,\ldots,N-1)`$. Reversing its displacements gives a partition. For each fixed partition the ratios of the weights tend to those obtained from $`a_k=\rho^k`$, whose moments are $`(1-\rho q^{m+1})^{-1}`$ and whose determinant is a Cauchy determinant. The interchange of this limit with the partition sum requires a bound uniform in the rank. We obtain a summable majorant $`C_*^{\ell}q^{\ell^2}`$ for partitions with $`\ell`$ positive parts. In this way we obtain the factor $`\mathcal M(\rho;q)`$, while normalising the Vandermonde product of the least tuple supplies the remaining factor $`\mathcal M(1;q)^2`$.

Our application concerns the Lambert series
``` math
F(t)=\sum_{n\ge1}\frac1{t^n-1}
     =\sum_{n\ge1}\frac{\tau(n)}{t^n},\qquad t>1,
```
where $`\tau(n)`$ is the number of positive divisors of $`n`$. The rearrangement follows by summing nonnegative geometric series, and convergence follows from $`\tau(n)\le n`$. Write $`(z;q)_m=\prod_{j=0}^{m-1}(1-zq^j)`$. Zudilin’s normalised moments, at the auxiliary parameters $`x=z=1`$ in his 2016 construction \[zudilin2016, (6), §4\], are
``` math
\begin{equation}
\label{eq:normalised-moments}
 v_m^*(q)=\sum_{t\ge0}q^{(m+1)t}
 \frac{(q;q)_m^3(q^{t+1};q)_m}{(q^{m+1+t};q)_{m+1}},
 \qquad V_N^*(q)=\det(v_{i+j}^*(q))_{0\le i,j<N}.
\end{equation}
```
For $`0<q<1`$ these sums converge. They also define formal series in $`q`$, since the $`t`$th summand has order $`(m+1)t`$.

<div id="res:sharp-fixed-base" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/SharpFixedBaseShort.lean#L53">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1049-rational-base-lambert.md#res-sharp-fixed-base-comparator">Comparator</a></p>

**Theorem 2** (the size of $`V_N^*`$ at a fixed base). *Fix $`0<q<1`$ and write $`P=(q;q)_\infty`$, $`B_N=N(N-1)(2N-1)/6`$ and $`C_N=(N!)^2(N+1)!/2^N`$. There is a $`K(q)>0`$ with
``` math
V_N^*(q)\sim K(q)\,C_Nq^{B_N}P^{2N}N^{-8F(1/q)}
 \qquad(N\to\infty).
```*

</div>

We give $`K(q)`$ as a convergent product in <a href="#eq:fixed-constant" data-reference-type="eqref" data-reference="eq:fixed-constant">[eq:fixed-constant]</a>. Zudilin proved the lower bound $`\operatorname{ord}_q V_N^*\ge B_N`$ \[zudilin2016, Lemma 1 and §4\]. The moment representation below shows that this order is attained with coefficient $`C_N`$, and then Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">1</a> with $`\rho=1`$ gives the fixed-base asymptotic. The distinction between these limits matters: multiplication by $`(1-q)^{N^3}`$ preserves the first formal term but changes the logarithm at fixed $`q`$ by a cubic quantity. We keep $`q`$ fixed throughout the analytic argument, without asserting uniformity as $`q\to1`$.

Chowla’s conjecture, recorded by Erdős \[erdos1988, p. 102\], asks whether $`F(t)`$ is irrational for every rational $`t>1`$. A separate argument in Section <a href="#sec:rational-base-irrationality" data-reference-type="ref" data-reference="sec:rational-base-irrationality">4</a> proves irrationality when $`\log b/\log a<\theta^*=0.4056830213840605\ldots`$ for coprime $`a>b\ge1`$. We use Zudilin’s 2004 forms and constants \[zudilin2004, §5\], cancel their common polynomial factors, and calculate the degree that remains to be cleared at $`a/b`$. This extends their use from integer bases to the stated rational region. The determinant estimates for the 2016 family provide no corresponding denominator calculation at $`3/2`$.

The proof of Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">1</a> is in Section <a href="#sec:geometric-moments" data-reference-type="ref" data-reference="sec:geometric-moments">2</a>. Section <a href="#sec:weights" data-reference-type="ref" data-reference="sec:weights">3</a> constructs the positive weights in <a href="#eq:normalised-moments" data-reference-type="eqref" data-reference="eq:normalised-moments">[eq:normalised-moments]</a> and derives their first two asymptotic terms. The rational-base argument follows in Section <a href="#sec:rational-base-irrationality" data-reference-type="ref" data-reference="sec:rational-base-irrationality">4</a>, and Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">5</a> discusses its limitations and the complementary results in the longer paper. All logarithms are natural. Empty products and determinants have value $`1`$, and the constants in $`O_q(\cdot)`$ may depend on the fixed $`q`$.

<a id="sec:geometric-moments"></a>

# Proof of the geometric moment theorem

<div class="proof">

*Proof of Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">1</a>.* We first choose $`\widehat\rho`$ with $`\rho<\widehat\rho<q^{-1}`$ and then $`K`$ so large that $`a_{j+1}/a_j\le\widehat\rho`$ whenever $`j\ge K`$. With
``` math
C=\prod_{j<K}\max\left(1,\frac{a_{j+1}}{\widehat\rho a_j}\right),
```
we obtain, by multiplying adjacent ratios,
``` math
\begin{equation}
\label{eq:automatic-shift-bound}
 \frac{a_{k+h}}{a_k}\le C\widehat\rho^{\,h}\qquad(k,h\ge0).
\end{equation}
```
In particular, $`a_h\le Ca_0\widehat\rho^{\,h}`$ and every moment converges, since $`q\widehat\rho<1`$. We apply Cauchy–Binet to a finite set of nodes and let its size tend to infinity. The entries of the moment matrix converge, and on the other side every term is positive, so we obtain the discrete Heine identity
``` math
\begin{equation}
\label{eq:heine-geometric}
 D_N=\sum_{0\le k_0<\cdots<k_{N-1}}
 \prod_{i<N}a_{k_i}q^{k_i}
 \prod_{i<j<N}(q^{k_i}-q^{k_j})^2.
\end{equation}
```
The tuple $`k_i=i`$ contributes
``` math
q^{B_N}\Delta_N\prod_{i<N}a_i,\qquad
 \Delta_N=\prod_{d=1}^{N-1}(1-q^d)^{2(N-d)}.
```
We write $`k_i=i+\lambda_i`$ and reverse the displacements by putting $`\mu_j=\lambda_{N-j}`$ for $`1\le j\le N`$. Thus $`\mu_1\ge\cdots\ge\mu_N\ge0`$, and division by the least-tuple contribution turns the summand into
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
By setting $`W_N(\mu)=0`$ for partitions of length greater than $`N`$, we regard all these sums as indexed by the same countable set.

Suppose that $`\mu`$ has $`\ell`$ positive parts. We need only estimate the factors with $`j\le\ell`$, since all the others equal $`1`$. For each such $`j`$, the denominators in the Vandermonde quotient multiply to at least $`P`$, whereas its numerators are at most $`1`$. Together with <a href="#eq:automatic-shift-bound" data-reference-type="eqref" data-reference="eq:automatic-shift-bound">[eq:automatic-shift-bound]</a>, this gives the rank-independent bound
``` math
W_N(\mu)\le (CP^{-2})^\ell
 \prod_{j=1}^{\ell}\widehat\rho^{\,\mu_j}q^{(2j-1)\mu_j}.
```
We sum this majorant by first fixing $`\ell`$ and then dropping the ordering condition on the positive parts. This gives
``` math
\begin{align*}
 \sum_{\ell(\mu)=\ell}\sup_N W_N(\mu)
 &\le(CP^{-2})^\ell\prod_{j=1}^{\ell}
        \sum_{u\ge1}\widehat\rho^{\,u} q^{(2j-1)u}\\
 &\le C_*^{\ell}q^{\ell^2},\qquad
 C_*=\frac{C\widehat\rho P^{-2}}{1-\widehat\rho q}.
\end{align*}
```
Here $`\sum_{j\le\ell}(2j-1)=\ell^2`$ and $`1-\widehat\rho q^{2j-1}\ge1-\widehat\rho q>0`$. The series $`\sum_{\ell\ge0}C_*^{\ell}q^{\ell^2}`$ converges.

For each fixed $`h`$ we have $`a_{k+h}/a_k\to\rho^h`$, by multiplying $`h`$ adjacent ratios. Hence the weight ratios in <a href="#eq:partition-summand" data-reference-type="eqref" data-reference="eq:partition-summand">[eq:partition-summand]</a>, for any fixed partition, tend to the same values as for $`a_k=\rho^k`$. The Vandermonde quotient also converges, since only finitely many first indices occur and the logarithms of the remaining factors have geometrically summable tails. We may therefore pass to the limit by dominated convergence and evaluate it using $`a_k=\rho^k`$.

For these weights we have $`M_m=(1-\rho q^{m+1})^{-1}`$, so Cauchy’s determinant formula gives
``` math
D_N=\frac{\rho^{N(N-1)/2}q^{B_N}\Delta_N}
 {\prod_{0\le i,j<N}(1-\rho q^{i+j+1})}.
```
Since the multiplicity of $`1-\rho q^d`$ in the denominator increases to $`d`$, the normalised sum tends to $`\mathcal M(\rho;q)`$. We finish by observing that
``` math
\frac{\Delta_N}{P^{2N}}
 =\prod_{d<N}(1-q^d)^{-2d}\prod_{d\ge N}(1-q^d)^{-2N}
 \longrightarrow\mathcal M(1;q)^2,
```
since the logarithm of the second product is $`O_q(Nq^N)`$. Combining the two limits proves <a href="#eq:geometric-limit" data-reference-type="eqref" data-reference="eq:geometric-limit">[eq:geometric-limit]</a>. ◻

</div>

<a id="sec:weights"></a>

# The weights of Zudilin’s moments

We apply Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">1</a> by collecting the dependence on $`m`$ in <a href="#eq:normalised-moments" data-reference-type="eqref" data-reference="eq:normalised-moments">[eq:normalised-moments]</a> into the single variable $`w=q^{m+1}`$. For this purpose, set
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

For $`r\ge1`$ and $`k\ge0`$ define the finite sum
``` math
R_k^{(r)}(q)=\sum_{n_1+\cdots+n_r=k}
              \frac{(q;q)_k}{\prod_{j=1}^r(q;q)_{n_j}},
```
over $`r`$ nonnegative parts. These are the multivariate Rogers–Szegő polynomials at unit arguments, written as sums of Gaussian multinomial polynomials \[vinroot2010\]. At $`q=0`$ they count compositions, and
``` math
c_k:=R_k^{(2)}(0)R_k^{(3)}(0)=\frac{(k+1)^2(k+2)}2,
 \qquad \prod_{k<N}c_k=C_N.
```

<div id="prop:weight-factorisation" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RogersFactorisationAnalytic.lean#L1312">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1049-rational-base-lambert.md#prop-weight-factorisation-comparator">Comparator</a></p>

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

<div class="proof">

*Proof.* We use the Gaussian binomial coefficients $`\genfrac{[}{]}{0pt}{}{n}{j}_q=(q;q)_n/((q;q)_j(q;q)_{n-j})`$ for $`0\le j\le n`$, and put $`\mathcal E(z)=(z;q)_\infty^{-1}`$. For $`\partial_qf(z)=(f(z)-f(qz))/z`$ we have $`\partial_q\mathcal E=\mathcal E`$ and $`\mathcal E(z)^r=\sum_{n\ge0}R_n^{(r)}z^n/(q;q)_n`$ by Euler’s expansion. The $`q`$-Leibniz rule, which follows by induction from the product rule, is
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
We now put $`z=w`$. The coefficient of $`w^n`$ on the left is $`R_n^{(3)}\sum_{j\le n}\bigl((q;q)_j(q;q)_{n-j}\bigr)^{-1}
=R_n^{(2)}R_n^{(3)}/(q;q)_n`$. To evaluate the right-hand side, we expand $`h_k`$, put $`k=j+t`$, and use the $`q`$-binomial theorem in the form
``` math
\sum_{t\ge0}\frac{(wq^j;q)_t}{(q;q)_t}w^t
 =\frac{(w^2q^j;q)_\infty}{(w;q)_\infty}.
```
The resulting expression is $`G_q(w)`$, as required. We may read each identity coefficientwise, or as an absolutely convergent expansion when $`|z|`$ and $`|w|`$ are sufficiently small.

For the bounds, we write $`b_k^{(r)}=[z^k](z;q)_\infty^{-r}`$, so that $`R_k^{(r)}=(q;q)_kb_k^{(r)}`$ and $`a_k=P^4(q;q)_kb_k^{(2)}b_k^{(3)}`$. By Euler’s expansion, $`b_k^{(r)}`$ is an $`r`$-fold convolution of $`1/(q;q)_n`$, whose terms lie in $`[1,P^{-1}]`$. There are $`\binom{k+r-1}{r-1}`$ compositions of $`k`$ into $`r`$ nonnegative parts, and we deduce
``` math
\binom{k+r-1}{r-1}\le b_k^{(r)}\le P^{-r}\binom{k+r-1}{r-1}.
```
Combining these at $`r=2,3`$ with $`P\le(q;q)_k\le1`$ and $`c_k=(k+1)\binom{k+2}2`$ gives $`P^5c_k\le a_k\le P^{-1}c_k`$. The shift bound follows from $`c_{k+h}/c_k\le(1+h)^3`$. ◻

</div>

The coefficient estimate in Section <a href="#sec:coefficient-asymptotic" data-reference-type="ref" data-reference="sec:coefficient-asymptotic">3.3</a> will give $`a_{k+1}/a_k\to1`$, allowing us to use Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">1</a> with $`\rho=1`$. Before doing so, we compute the first nonzero term in $`q`$ from the same representation.

<a id="sec:hankel-order"></a>

## The first nonzero formal term

The order of a nonzero formal series is the least exponent with nonzero coefficient. In Heine’s expansion for $`V_N^*`$, a single tuple attains the least order.

<div id="res:zudilin-sharp-qorder" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1049-rational-base-lambert.md#res-zudilin-sharp-qorder">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1049-rational-base-lambert.md#res-zudilin-sharp-qorder-comparator">Comparator</a></p>

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
No other tuple can cancel that coefficient. For example, at rank two the pair $`(0,1)`$ contributes $`6q+O(q^2)`$, and every other increasing pair has order at least two. ◻

</div>

This proves equality in Zudilin’s bound \[zudilin2016, §4, pp. 6–7\]. An alternative argument, which computes the first nonzero term of every transformed row, is given in [the companion paper](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-formal-rows).

<a id="sec:coefficient-asymptotic"></a>

## The coefficient asymptotic

Fix $`0<q<1`$ and put $`L=F(1/q)`$. To evaluate the product of the weights we need one term beyond their cubic growth. A relative term of order $`1/k`$ contributes a power of $`N`$ to that product.

<div class="proof">

*Proof of Theorem <a href="#res:sharp-fixed-base" data-reference-type="ref" data-reference="res:sharp-fixed-base">2</a>.* We isolate the pole at $`w=1`$ by writing $`\Pi(w)=(qw;q)_\infty`$, so that $`(w;q)_\infty=(1-w)\Pi(w)`$, and, for $`t\ge1`$, put
``` math
f_t(w)=\frac{(q^tw^2;q)_\infty}{(q;q)_t(q^tw;q)_\infty^2},
 \qquad
 \mathcal S(w)=\sum_{t\ge1}w^t\bigl(f_t(w)-P^{-1}\bigr).
```
The bracket is $`O_q(q^t)`$ uniformly on each compact subset of $`|w|<q^{-1}`$, so $`\mathcal S`$ is analytic there. We separate the summand $`t=0`$, whose denominator contains $`(1-w)^2`$, and subtract the constant part of the remaining summands to obtain
``` math
\mathcal D(w):=P^4(1-w)^4G_q(w)
 =\frac{P^4}{\Pi(w)^3}
 \left((1+w)\frac{(qw^2;q)_\infty}{\Pi(w)^2}+\frac wP
       +(1-w)\mathcal S(w)\right).
```
Hence $`\mathcal D`$ is analytic on a disc of radius greater than $`1`$.

At $`w=1`$ one has $`\Pi(1)=P`$ and $`\Pi'(1)/\Pi(1)=-L`$, since $`\Pi'/\Pi=-\sum_{j\ge1}q^j/(1-q^jw)`$. Also $`(qw^2;q)_\infty`$ equals $`P`$ at $`w=1`$, and the logarithmic derivative of $`(qw^2;q)_\infty/\Pi(w)^2`$ at $`w=1`$ is $`-2L+2L=0`$. It follows that the bracket has value $`3/P`$ and derivative $`(2-L)/P`$ at $`w=1`$. In this calculation we used $`\mathcal S(1)=L/P`$, which follows from $`f_t(1)=\bigl(P(1-q^t)\bigr)^{-1}`$ and $`\sum_{t\ge1}\bigl((1-q^t)^{-1}-1\bigr)=L`$. Including the factor $`P^4\Pi^{-3}`$, whose logarithmic derivative at $`1`$ is $`3L`$, we obtain
``` math
\mathcal D(1)=3,\qquad
 \mathcal D'(1)=3\left(3L+\frac{2-L}3\right)=2+8L.
```
We subtract the principal part of $`\mathcal D(w)(1-w)^{-4}`$ at $`w=1`$. The remainder is analytic on a larger disc, from which we read off
``` math
a_k=3\binom{k+3}3-(2+8L)\binom{k+2}2+O_q(k),
 \qquad
 \frac{a_k}{c_k}=1-\frac{8L}{k+1}+O_q\bigl((k+1)^{-2}\bigr),
```
the second line because $`3\binom{k+3}3=c_k(k+3)/(k+1)`$ and $`\binom{k+2}2=c_k/(k+1)`$.

In particular $`a_{k+1}/a_k\to1`$. Proposition <a href="#prop:weight-factorisation" data-reference-type="ref" data-reference="prop:weight-factorisation">3</a> then verifies the remaining hypothesis of Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">1</a>, with $`\rho=1`$.

Let $`\gamma_{\!E}`$ denote Euler’s constant, and define
``` math
\begin{equation}
\label{eq:fixed-constant}
 \mathcal A(q)=e^{-8\gamma_{\!E}L}
 \prod_{k\ge0}\left(\frac{a_k}{c_k}e^{8L/(k+1)}\right),
 \qquad K(q)=\mathcal A(q)\mathcal M(1;q)^3.
\end{equation}
```
Since $`\log(a_k/c_k)+8L/(k+1)=O_q((k+1)^{-2})`$ is summable, we obtain a convergent product $`\mathcal A(q)>0`$. Since $`\sum_{k<N}(k+1)^{-1}=\log N+\gamma_{\!E}+o(1)`$,
``` math
\prod_{k<N}a_k\sim\mathcal A(q)\,C_NN^{-8L}.
```
Applying Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">1</a> gives $`V_N^*\sim\mathcal M(1;q)^3q^{B_N}P^{2N}\prod_{k<N}a_k`$. Substituting the product asymptotic proves the assertion. Equivalently,
``` math
\log V_N^*=B_N\log q+\log C_N+2N\log P-8L\log N+\log K(q)+o(1).
```
 ◻

</div>

The power $`N^{-8L}`$ comes from the second coefficient of the pole at $`w=1`$. The leading coefficient gives the cubic growth of $`a_k`$, but leaves this factor undetermined.

<a id="sec:rational-base-irrationality"></a>

# Rational bases

We now use the 2004 coefficient family. If $`U,V\in\mathbb{Z}[X]`$ have degree at most $`W`$, evaluation at $`a/b`$ requires the factor $`b^W`$ to produce integer coefficients. A common polynomial factor should therefore be cancelled first. For example, at $`3/2`$ the pair $`(X+1)(X+2),(X+1)(X+3)`$ gives $`(35,45)`$ after clearing to degree $`2`$. After cancelling $`X+1`$, clearing to degree $`1`$ gives $`(7,9)`$. For Zudilin’s forms, cyclotomic cancellation has a degree of quadratic order, and this degree determines the rational-base criterion.

We use the parameter direction from Zudilin’s construction \[zudilin2004, §5, pp. 161–162\], together with its thirteen intervals and constants $`C_1,C_0`$. At integer bases his theorem gives the irrationality-exponent bound $`C_1/C_0=2.46497868\ldots`$ \[zudilin2004, Thm. 1, p. 154\]. Let $`\psi_1(u)=\sum_{k\ge0}(k+u)^{-2}`$ for $`u>0`$, and let $`\mathcal I`$ consist of the thirteen intervals listed in the proof. We put
``` math
C_1=\frac{1091}{2},\qquad
 J=\sum_{[u,v)\in\mathcal I}\bigl(\psi_1(u)-\psi_1(v)\bigr),\qquad
 C_0=266-\frac3{\pi^2}(225-J).
```
The intervals are disjoint and lie in $`[1/14,1)`$, so $`0\le J\le\psi_1(1/14)-\psi_1(1)<196`$. Together with $`\pi>3`$, these bounds give $`0<C_0<266<C_1/2`$. Thus $`\theta^*=C_0/C_1`$ and $`\mu=C_1/C_0`$ are positive reciprocal constants. The notation $`\mu_{\rm irr}(\xi)`$ instead denotes the irrationality exponent of a value. The estimates below give a sufficient cutoff; its optimality is unknown.

<div id="res:rational-base-threshold" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1049-rational-base-lambert.md#res-rational-base-threshold">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1049-rational-base-lambert.md#res-rational-base-threshold-comparator">Comparator</a></p>

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

The condition holds for every integer base, since $`b=1`$ gives $`\log b/\log a=0`$. For a fixed denominator $`b>1`$, it requires $`a>b^{2.46497868\ldots}`$, much more than $`a>b`$; nevertheless it gives infinitely many reduced noninteger rational bases for each such $`b`$. The base $`31/4`$ satisfies the condition, and taking a common positive integer power of the numerator and denominator leaves their logarithmic ratio unchanged. Since $`\theta^*<1/2<\log2/\log3`$, the condition fails at $`3/2`$. At equality $`\log b/\log a=\theta^*`$ the quadratic exponent vanishes, so the estimates below give no conclusion.

<div class="proof">

*Proof of Theorem <a href="#res:rational-base-threshold" data-reference-type="ref" data-reference="res:rational-base-threshold">5</a>.* We shall calculate the degree $`W_n`$ of the cancelled coefficient and show that $`b^{W_n}\Lambda_n(a/b)`$ is positive and tends to zero. We fix $`n\ge1`$ and set
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

The Gaussian binomial polynomial $`\genfrac{[}{]}{0pt}{}{m}{k}_X=\prod_{j=1}^k(1-X^{m-k+j})/(1-X^j)`$ is monic of degree $`k(m-k)`$ for integers $`0\le k\le m`$. The source’s (8) and (10) on p. 156 give the coefficient whose degree we need:
``` math
A_n(X)=\sum_{k=a_2}^{\beta-1}(-1)^{a_1+a_2+k+1}
 X^{a_0k+\binom{a_1}{2}-\binom{\beta-a_2}{2}+\binom{\beta-k}{2}}
 \genfrac{[}{]}{0pt}{}{k-1}{a_1-1}_X
 \genfrac{[}{]}{0pt}{}{\beta-a_2-1}{\beta-k-1}_X.
```
On comparing successive summands, we find that the degree increases by $`40n+1-k>0`$ for $`a_2\le k\le\beta-2`$. The last summand alone therefore determines the leading term, giving
``` math
K_n:=\deg A_n=\frac{1091n^2+81n+2}{2},\qquad
 W_n:=\deg U_n=K_n-M_n+\sum_{\ell\le15n}(1-\nu_\ell)\varphi(\ell).
```
Here $`\varphi(\ell)=\deg\Phi_\ell`$ is Euler’s totient function, and $`\nu_1=\omega(n)=0`$. The bounds for $`H_n`$ are uniform for $`x\ge2`$: then $`P\ge\prod_{j\ge1}(1-2^{-j})>0`$ and $`(1-x^{-a_0})^{-1}\le2`$. For fixed $`n`$, therefore, $`H_n(x)=O(1)`$ and $`\Lambda_n(x)=O(x^{W_n-K_n})`$ as $`x\to\infty`$. The unique top summand of $`A_n`$ has leading coefficient $`(-1)^{a_1+a_2+\beta}=(-1)^n`$. Since the Gaussian factors and $`D_N/\Omega_n`$ are monic, $`U_n`$ has that leading coefficient too. Moreover $`F(x)=x^{-1}+O(x^{-2})`$ and $`K_n\ge2`$, so
``` math
V_n(x)=U_n(x)F(x)-\Lambda_n(x)
       =(-1)^n x^{W_n-1}+O(x^{W_n-2}).
```
Here $`W_n\ge K_n-M_n=(559n^2+13n)/2>0`$. Thus $`\deg V_n=W_n-1`$, with the same unit leading coefficient as $`U_n`$. For every prime $`p\mid b`$, reduction of the cleared first coordinate gives
``` math
b^{W_n}U_n(a/b)\equiv(-1)^n a^{W_n}\not\equiv0\pmod p.
```
Thus $`U_n(a/b)`$ has reduced denominator exactly $`b^{W_n}`$, the least common clearing denominator for this pair. Every common integer divisor of the cleared row is consequently coprime to $`b`$. This leaves common factors at other primes and savings from combinations of different rows to be analysed separately.

Having computed the degree by keeping $`n`$ fixed and letting $`x\to\infty`$, we now estimate decay with $`x`$ fixed and $`n\to\infty`$.

It remains to find the quadratic part of the degree removed by cancellation. The limits below are the cyclotomic limits of \[zudilin2004, Lemmas 1–2, p. 155\]. The proof uses the argument through reciprocal intervals, the summatory totient estimate and the trigamma function from the proof of \[zudilin2002, Lemma 1, p. 466\], with an explicit truncation of the block sum. The elementary summatory estimate $`\sum_{\ell\le y}\varphi(\ell)=3y^2/\pi^2+O(y\log y)`$ gives
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

We return to a fixed real base $`x>1`$ and estimate the cyclotomic product. Writing $`\mu_{\rm Mob}`$ for the Möbius function, we have
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
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L117">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1049-rational-base-lambert.md#res-thirtyone-four-comparator">Comparator</a></p>

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
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1049-rational-base-lambert.md#cor-rational-base-measure">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1049-rational-base-lambert.md#cor-rational-base-measure-comparator">Comparator</a></p>

**Corollary 7** (an irrationality measure uniform over powers). *For coprime $`a>b\ge1`$ with $`\theta=\log b/\log a<\theta^*`$ and every integer $`r\ge1`$,
``` math
\mu_{\rm irr}\!\left(F((a/b)^r)\right)
 \le\frac{1-\theta}{\theta^*-\theta}.
```
Here $`\mu_{\rm irr}(\xi)`$ is the supremum of the exponents $`\nu`$ for which $`|\xi-p/q|<q^{-\nu}`$ has infinitely many reduced rational solutions. In particular, $`\mu_{\rm irr}(F((31/4)^r))<301`$ for every $`r\ge1`$.*

</div>

<div class="proof">

*Proof.* We follow the passage from linear forms to an exponent bound used by Zudilin at integer bases \[zudilin2004, p. 162\]. Applying the estimates separately at each fixed base $`(a/b)^r`$ will give a bound independent of $`r`$. We use the polynomials $`U_n,V_n`$ from Theorem <a href="#res:rational-base-threshold" data-reference-type="ref" data-reference="res:rational-base-threshold">5</a>, with $`W_n=\deg U_n`$. In that construction the coefficient of $`F`$ before cancellation is a sum of $`O(n)`$ Laurent monomials times two Gaussian binomial polynomials. Each Gaussian polynomial has nonnegative coefficients summing to at most $`2^{27n+2}`$. Thus the sum of the absolute coefficients is $`\exp(O(n))`$. Its largest exponent is $`K_n=(1091n^2+81n+2)/2`$, so its absolute value at a fixed $`x>1`$ is at most $`x^{K_n}\exp(O(n))`$. The cyclotomic estimate in the same proof bounds the normalising multiplier by $`x^{W_n-K_n}\exp(O_x(n))`$. Multiplication gives
``` math
|U_n(x)|\le x^{W_n}\exp(O_x(n))\qquad(x>1\text{ fixed}).
```
Set $`\xi=F(a/b)`$, $`Q_n=b^{W_n}U_n(a/b)`$ and $`P_n=b^{W_n}V_n(a/b)`$. With
``` math
\alpha=(C_1-C_0)\log a,\qquad
 \tau=C_0\log a-C_1\log b>0,
```
we have $`\log(Q_n\xi-P_n)=-\tau n^2+o(n^2)`$ and $`|Q_n|\le\exp(\alpha n^2+o(n^2))`$.

For integers $`A,B,p,q`$ with $`q>0`$, if $`L=A\xi-B`$ and $`2q|L|\le1`$, then
``` math
|L|\le |A|\,|\xi-p/q|.
```
When $`Ap-Bq=0`$ this is equality. Otherwise the nonzero integer $`Ap-Bq`$ gives $`1/q\le |L|+|A|\,|\xi-p/q|`$, which proves the inequality. We fix $`0<\eta<\tau`$ and use the preceding estimates in the form
``` math
e^{-(\tau+\eta)n^2}\le Q_n\xi-P_n\le e^{-(\tau-\eta)n^2},
 \qquad |Q_n|\le e^{(\alpha+\eta)n^2}
```
for all sufficiently large $`n`$. Given a sufficiently large denominator $`q`$, we choose $`n=\lceil\sqrt{\log(2q)/(\tau-\eta)}\rceil`$, so that $`2q(Q_n\xi-P_n)\le1`$. The preceding integer argument now applies to $`(A,B)=(Q_n,P_n)`$ for every numerator $`p`$. Also $`Q_n\ne0`$: otherwise $`Q_n\xi-P_n`$ would be an integer strictly between $`0`$ and $`1`$. It follows that
``` math
|\xi-p/q|\ge e^{-(\alpha+\tau+2\eta)n^2}
             =q^{-(\alpha+\tau+2\eta)/(\tau-\eta)-o(1)},
```
since $`n^2=\log(2q)/(\tau-\eta)+O_\eta(\sqrt{\log q}+1)`$.

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

Bundschuh and Väänänen’s Theorem 2 at $`\alpha=-1`$ \[bv1994, p. 177\] gives irrationality for $`\log b/\log a<\theta_{\rm BV}:=1/2-1/\pi^2`$. Their $`q`$ is the base $`a/b>1`$, not its reciprocal. Their logarithmic derivative is $`L_q(z)=\sum_{j\ge1}(q^j+z)^{-1}`$, so the value at $`z=\alpha=-1`$ is exactly $`F(a/b)`$. The rational height is $`h(q)=a`$, and their parameter $`\lambda=\log h(q)/\log q`$ is $`1/(1-\log b/\log a)`$, which gives the displayed cutoff. Since $`\pi^2<10`$, one has $`\theta_{\rm BV}<2/5<\log4/\log31`$, so $`31/4`$ lies outside that sufficient region. The two sufficient regions differ on $`[\theta_{\rm BV},\theta^*)`$. Zudilin also notes an extension to noninteger rational bases $`p=r/s`$ for the generalized $`q`$-logarithm when $`\log|r|>c\log|s|`$, with $`c>0`$ computable but unspecified \[zudilin2016, Sec. 2, p. 4\]. For $`F`$, the specialisation above gives $`c=\mu`$, the exponent bound of \[zudilin2004, p. 162\].

Negative bases are not treated: the positive-remainder estimates assume $`x>1`$. At $`x=1`$ the Lambert series diverges. The separate $`7/2`$ parameter check for Bundschuh and Väänänen’s theorem is retained in the companion record, Theorem 8.1; that cited analytic irrationality theorem is supported here by that source citation.

<a id="sec:open"></a>

# Further questions

The determinant theorem uses positivity and the relative growth of the moment weights. Applying it to irrationality at a rational base would also require integer coefficients after clearing, with a denominator estimate compatible with the small determinant. The [rational counterexample in the companion paper](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-countermodel) has positive geometric moments, the same formal orders and leading coefficients, and a fixed-base power correction of the same form. Its target value is rational. Thus these analytic properties alone cannot supply the missing arithmetic estimate.

The polynomial coefficient sequence is another possible source of information. Van Assche’s little-$`q`$-Legendre construction \[vanassche2001, §3\] and the multiple-orthogonality construction of Postelmans and Van Assche \[postelmansvanassche2007, §2\] make the normalisation important. In the 2016 family, the companion paper proves positivity of the first matrix of a coefficient pencil through rank eight, with real, interlacing roots below $`F(p)`$ for $`p>1`$. The shifted minors and coefficientwise positivity are supported by the stated finite polynomial computations. The [coefficient-moment section](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-coefficients) gives the definitions and the precise ranges. It leaves all-rank positivity and convergence of the largest root open. The general moment criteria of Wang and Zhu \[wangzhu2016\] and Sokal and Walrad \[sw2024\], Berg’s factorial-power example \[berg2007, Theorem 5.1\], and the quadrature construction of Golub and Welsch \[golubwelsch1969\] provide the relevant comparisons. Using a recurrence from another family would require a proof that it holds for these coefficients. The root-of-unity method of Krattenthaler, Rochev, Väänänen and Zudilin \[krvz2009\], for example, concerns a separate construction.

<a id="sec:round8-transfer-boundaries"></a>

## Congruences and divided forms

At $`3/2`$, a polynomial $`Q`$ of degree at most $`W`$ has integral homogenised value $`H_W(Q)=2^WQ(3/2)`$. Congruences at powers of $`2`$ and $`3`$ give finite counting criteria for combinations of such values. The companion paper proves the [endpoint and residue statements](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-arithmetic) for integer rescaling and signed sums. It also treats the rank-one case and proves the quantitative finite-fibre estimate used below. Equal residues give a useful irrationality form only when the divided remainder is also nonzero and small. Smith normal form describes the image of the evaluated lattice \[stanley2016, Theorems 2.3–2.4\], but does not estimate these real remainders.

For example, suppose that $`M`$ integral rows $`(A_j,B_j)`$ have remainders $`e_j=A_jF(3/2)-B_j`$, and that the subset sums take $`Q`$ residue values modulo a positive integer $`D`$. Put $`T=\sum_j|e_j|`$ and suppose that at most $`k`$ selectors give the same exact remainder within a residue class. For each positive integer $`n`$, the sufficient inequality
``` math
\begin{equation}
\label{eq:quantitative-selector-budget}
 2^M>Qk\left(\left\lfloor\frac{nT}{D}\right\rfloor+1\right)
\end{equation}
```
gives two equal-residue selectors whose remainders differ by a nonzero quantity of absolute value less than $`D/n`$. Indeed, in each residue class partition the interval of attained remainders into bins of width $`D/n`$, beginning at its least value. If every bin contained only one real value, its multiplicity would be at most $`k`$, contrary to <a href="#eq:quantitative-selector-budget" data-reference-type="eqref" data-reference="eq:quantitative-selector-budget">[eq:quantitative-selector-budget]</a>. Subtracting the selectors and dividing by $`D`$ gives an integral linear form of nonzero absolute value less than $`1/n`$. The [quantitative lemma and its proof](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-selectors) state the finite-set version without assumptions about Lambert series.

The elementary integer-base method provides a different comparison. Vandehey \[vandehey2013\] and Duverney and Tachiya \[duverneytachiya2019\] use integer-base expansions. At a noninteger rational base the cleared tails satisfy a recurrence with a growing denominator contribution. The [clearing and tail-recurrence calculations](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-clearing) in the companion paper rule out one coordinatewise scheme at $`3/2`$. They make no assertion about other approximation families. At the function level, Bell and Smertnig \[bellsmertnig2026, Theorem 1.3\] exclude Mahler equations for the divisor generating series, while leaving the arithmetic of a single rational argument undecided.

<a id="prob:kernel"></a>

#### A construction problem.

The unrestricted request for primitive polynomial rows and a signed combination whose divided remainder lies strictly between $`0`$ and $`1/n`$ is equivalent to the irrationality of the target. The companion paper retains the full statement and proves this equivalence in its [section on divided linear forms](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-open-construction). A more specific question must prescribe the approximation family. For the 2004 family one can instead ask whether a parameter direction improves $`\theta^*`$. The [all-base degree restriction](../../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf#nameddest=long1049-region-extensions) proves the upper bound $`1/2`$ for the degree cutoff under its stated uniform-in-base hypotheses. Thus this sufficient criterion does not include $`3/2`$. When the degrees have a quadratic limit, the stronger conclusion there excludes decay of the undivided forms at $`3/2`$. Division by additional base-dependent content and other families remain unclassified. Equality in the rational-base cutoff is also unresolved by the estimates of Section <a href="#sec:rational-base-irrationality" data-reference-type="ref" data-reference="sec:rational-base-irrationality">4</a>.

<a id="app:index"></a>

# Proofs and source records

The ordinary proofs are in the text. The margin links identify the supplied Lean declarations and their recorded Comparator comparisons for the unchanged labelled results. They are records of earlier checks, not new executions or an independent review of this revision. Theorem <a href="#thm:geometric-moments" data-reference-type="ref" data-reference="thm:geometric-moments">1</a> includes an exponential tilt absent from the recorded $`\rho=1`$ theorem; its extension and <a href="#eq:squared-cauchy-example" data-reference-type="eqref" data-reference="eq:squared-cauchy-example">[eq:squared-cauchy-example]</a> have the ordinary proofs given here and carry no formal-proof mark. The [evidence record](https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1049-rational-base-lambert.md) and the [formal-source revision](https://github.com/wcook04/plectis-erdos/tree/7380b7871687b6bcc41ca0143c61f232e8af6500) identify the individual formal statements and the computations described in the companion paper.

<a id="data-availability."></a>

#### Data availability.

The cited source revision contains the Lean sources, toolchain and library manifest. The companion paper supplies the longer algebraic arguments and the precise scope of the finite computations.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem numbering follows the catalogue maintained by Thomas Bloom \[erdosproblems\]. I thank Wouter van Doorn for advice on writing for a first-time reader and explaining the force of a hypothesis. This advice concerned another note and does not imply mathematical review or endorsement of the present results.

<div class="thebibliography">

99

P. Erdős, *On the irrationality of certain series: problems and results*, in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). P. Bundschuh and K. Väänänen, [*Arithmetical investigations of a certain infinite product*](https://numdam.org/item/CM_1994__91_2_175_0.pdf), Compositio Math. **91** (1994), no. 2, 175–199. W. Zudilin, *Remarks on irrationality of $`q`$-harmonic series*, Manuscripta Math. **107** (2002), no. 4, 463–477, doi:[10.1007/s002290200249](https://doi.org/10.1007/s002290200249). W. Zudilin, [*Heine’s basic transform and a permutation group for $`q`$-harmonic series*](https://geodesic.mathdoc.fr/articles/10.4064/aa111-2-4/), Acta Arith. **111** (2004), no. 2, 153–164, doi:[10.4064/aa111-2-4](https://doi.org/10.4064/aa111-2-4). Page references are to the printed journal pages. W. Zudilin, [*On the irrationality of generalized $`q`$-logarithm*](https://arxiv.org/abs/1601.02688v2), arXiv:1601.02688; Res. Number Theory **2** (2016), Art. 15, doi:[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x). Page references are to arXiv:1601.02688v2. The remark that the results extend to non-integer $`p=r/s`$, $`|p|>1`$, under an assumption $`\log|r|>c\log|s|`$ for a computable $`c>0`$, is in Section 2, p. 4, in the paragraph beginning “Finally, we remark”; no value of $`c`$ is computed there, and the remark is made for the generalized $`q`$-logarithm of that paper. R. P. Stanley, *Smith normal form in combinatorics*, J. Combin. Theory Ser. A **144** (2016), 476–495, doi:[10.1016/j.jcta.2016.06.013](https://doi.org/10.1016/j.jcta.2016.06.013); arXiv:[1602.00166v1](https://arxiv.org/abs/1602.00166v1). Page references are to arXiv:1602.00166v1. W. Zudilin, *A determinantal approach to irrationality*, Constr. Approx. **45** (2017), no. 2, 301–310, doi:[10.1007/s00365-016-9333-7](https://doi.org/10.1007/s00365-016-9333-7); arXiv:[1507.05697v1](https://arxiv.org/abs/1507.05697v1). Page and equation references are to arXiv:1507.05697v1. T. F. Bloom, [*Erdős Problem \#1049*](https://www.erdosproblems.com/1049), `erdosproblems.com/1049`. Accessed 28 July 2026, when the page displayed “last edited 28 September 2025”. J. Bell and D. Smertnig, [*Mahler series with multiplicative coefficient sequences*](https://arxiv.org/abs/2603.23456v1), arXiv:2603.23456v1, 24 March 2026. Theorem 1.3 is on pp. 2–3; its stated consequences on p. 3 include that the divisor and totient generating series are not $`k`$-Mahler for any $`k\ge2`$. J. Vandehey, [*On an incomplete argument of Erdős on the irrationality of Lambert series*](https://arxiv.org/abs/1206.0340v1), Integers **13** (2013), Paper A58. Page references are to arXiv:1206.0340v1 (2012). D. Duverney and Y. Tachiya, *Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*, Forum Math. **31** (2019), no. 6, 1557–1566, doi:[10.1515/forum-2018-0299](https://doi.org/10.1515/forum-2018-0299). Page references are to the [authors’ version](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf). W. Van Assche, [*Little $`q`$-Legendre polynomials and irrationality of certain Lambert series*](https://arxiv.org/abs/math/0101187v1), Ramanujan J. **5** (2001), no. 3, 295–310, doi:[10.1023/A:1012930828917](https://doi.org/10.1023/A:1012930828917). Page references are to arXiv:math/0101187v1. K. Postelmans and W. Van Assche, [*Irrationality of $`\zeta_q(1)`$ and $`\zeta_q(2)`$*](https://arxiv.org/abs/math/0604312v1), J. Number Theory **126** (2007), no. 1, 119–154, doi:[10.1016/j.jnt.2006.11.011](https://doi.org/10.1016/j.jnt.2006.11.011). Page references are to arXiv:math/0604312v1 (2006). C. Krattenthaler, I. Rochev, K. Väänänen and W. Zudilin, *On the non-quadraticity of values of the $`q`$-exponential function and related $`q`$-series*, Acta Arith. **136** (2009), no. 3, 243–269, doi:[10.4064/aa136-3-4](https://doi.org/10.4064/aa136-3-4); arXiv:[0812.2921v1](https://arxiv.org/abs/0812.2921v1). Page references are to arXiv:0812.2921v1. Y. Wang and B.-X. Zhu, [*Log-convex and Stieltjes moment sequences*](https://arxiv.org/abs/1612.04114v1), Adv. Appl. Math. **81** (2016), 115–127, doi:[10.1016/j.aam.2016.06.008](https://doi.org/10.1016/j.aam.2016.06.008). Page references are to arXiv:1612.04114v1. C. Berg, *On powers of Stieltjes moment sequences, II*, J. Comput. Appl. Math. **199** (2007), 23–38; arXiv:[math/0412340v1](https://arxiv.org/abs/math/0412340v1). Theorem references use the preprint; Theorem 5.1 treats factorial powers. A. D. Sokal and J. Walrad, *Continued-fraction characterization of Stieltjes moment sequences with support in $`[\xi,\infty)`$*, [arXiv:2404.12131v1](https://arxiv.org/abs/2404.12131v1), 2024. The classical Stieltjes criterion is recalled on pp. 1–2. G. H. Golub and J. H. Welsch, *Calculation of Gauss Quadrature Rules*, Math. Comp. **23** (1969), no. 106, 221–230, doi:[10.1090/S0025-5718-69-99647-1](https://doi.org/10.1090/S0025-5718-69-99647-1). C. R. Vinroot, [*Multivariate Rogers–Szegő polynomials and flags in finite vector spaces*](https://arxiv.org/abs/1011.0984), arXiv:1011.0984v1, 3 November 2010, abstract accessed 20 September 2026. Cited for the identification of the sum of all $`q`$-multinomial coefficients of fixed degree and length with a flag count, and for its recursion generalising the Galois numbers. The factorisation of the moment weights is proved here.

</div>
