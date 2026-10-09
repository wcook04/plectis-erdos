<a id="erdos-251-prime-gap-dyadic-series"></a>

# Sparse Congruence-Preserving Perturbations of Dyadic Series

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We perturb convergent dyadic series with nonnegative integer coefficients to attain both rational and irrational sums while preserving eventual congruences and asymptotic block statistics. Nonnegative corrections on one set of upper Banach density zero attain a nondegenerate interval above the original sum. They eventually respect any prescribed bound tending to infinity and preserve coefficient and partial-sum residues for every fixed modulus, with target-independent cutoffs. We vary adjacent correction pairs with fixed ordinary totals; growing digit ranges let later weighted choices fill the gaps between present choices. Applied to prime gaps with correction bound $`\log(n+3)`$, this preserves cumulative growth $`n\log n`$ and gives vanishing total variation error for blocks of length $`o(\log\log X)`$ sampled on $`[X,2X)`$. Cumulative positions need not be prime; irrationality of the actual prime series remains open.

<a id="sec:problem"></a>

# Introduction

Let $`p_0=2,p_1=3,\ldots`$ be the primes and put $`g_n=p_{n+1}-p_n`$. Erdős asked whether
``` math
\Pi=\sum_{n\ge0}\frac{p_n}{2^{n+1}}
```
is irrational \[erdos1958, p. 94\]\[erdosgraham1980, p. 62\] \[erdos1988, p. 103\]. Summation by parts gives $`\Pi=2+\sum_{n\ge0}g_n2^{-(n+1)}`$, with convergence justified in Section <a href="#sec:parts" data-reference-type="ref" data-reference="sec:parts">4</a>. We study which properties of the gaps survive when the latter sum is changed to a prescribed value.

The support and every modulus cutoff are fixed before the target is chosen. The interval contains rational and irrational sums with the same eventual coefficient and partial-sum residues. A block changes only when it meets the support, whereas every correction enters the dyadic sum. With polylogarithmic corrections, empirical block laws agree asymptotically at lengths $`o(\log\log X)`$; for prime gaps, cumulative growth remains $`n\log n`$. The comparison positions need not be consecutive primes.

We use a standard interval-covering argument for series with finite choices. Fridy’s generalised-base lemma \[fridy1966, p. 194\] treats prescribed digit bounds and nonincreasing weights. Crmarić and Kovač \[crmarickovac2025, Lemma 4\] give the finite-choice form used here, and Kovač and Tao \[kovactao2024, Lemma 5.1\] use analogous intervals of reciprocal choices. We must arrange these choices on a sparse set while preserving cumulative congruences. To do so, we redistribute a fixed correction between two adjacent indices. The simplest useful calculation is
``` math
\begin{array}{c|rrrr}
 (e_n,e_{n+1}) &(0,6)&(2,4)&(4,2)&(6,0)\\
 e_n+e_{n+1} &6&6&6&6\\
 2^{n+2}\bigl(e_n2^{-n-1}+e_{n+1}2^{-n-2}\bigr)&6&8&10&12.
 \end{array}
```
Moving $`2`$ from the later index to the earlier one changes the weighted sum while leaving the ordinary sum fixed. If the cumulative correction before the pair is odd, an additional $`1`$ at $`n-1`$ clears its residue modulo $`2`$. Since the four pairs have the same sum, the choice of pair leaves every later cumulative residue unchanged. We repeat this operation with nested moduli and increasingly separated pairs. The larger separations make the weighted contributions smaller, so we enlarge the range of each pair until the later contributions fill the gaps between consecutive present choices.

Throughout, $`\mathbb{N}=\{0,1,\ldots\}`$, intervals of indices contain integers, and $`\log`$ is natural unless a base is displayed. A set $`S\subseteq\mathbb{N}`$ has *upper Banach density zero* if
``` math
\lim_{H\to\infty}\sup_{u\in\mathbb{N}}\frac{|S\cap[u,u+H)|}{H}=0.
```
For integers $`X,m\ge1`$, let $`\mu_{a,X,m}`$ denote the distribution of $`(a_n,\ldots,a_{n+m-1})`$ when $`n`$ is uniform on $`[X,2X)`$. The entries are not rescaled: we sample starting indices, not distinct block values. We use $`d_{\rm TV}(\mu,\nu)=\sup_B|\mu(B)-\nu(B)|`$, with the supremum over all sets of blocks.

<div id="res:sparserationalisation" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-sparserationalisation">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-sparserationalisation-comparator">Comparator</a></p>

**Proposition 1** (sparse changes preserving congruences). *Let $`a:\mathbb{N}\to\mathbb{N}`$ satisfy $`A=\sum_{n\ge0}a_n2^{-(n+1)}<\infty`$, let $`K\in\mathbb{N}`$, and let $`f:\mathbb{N}\to\mathbb{R}`$ tend to $`+\infty`$. There exist a set $`S\subseteq[K,\infty)`$ of upper Banach density zero and a nondegenerate interval $`I\subset(A,\infty)`$ such that, for every $`r\in I`$, there is an integer correction $`e:\mathbb{N}\to\mathbb{N}`$ satisfying
``` math
\operatorname{supp}e\subseteq S,\qquad e_n\le f(n)\ \text{eventually},
 \qquad \sum_{n\ge0}(a_n+e_n)2^{-(n+1)}=r.
```
For each integer $`q\ge1`$ there is a cutoff $`N_q`$, independent of $`r`$, such that $`q\mid e_n`$ and $`q\mid\sum_{i<n}e_i`$ for all $`n\ge N_q`$. For every $`\varepsilon>0`$, the choice $`f(n)=(\log(n+3))^\varepsilon`$ can be made with
``` math
|S\cap[X,2X)|=O_\varepsilon\!\left(\frac{X}{\log\log X}\right),
 \qquad
 d_{\rm TV}(\mu_{a,X,m},\mu_{a+e,X,m})
 \le\frac{m|S\cap[X,2X+m)|}{X}.
```
In particular the distance tends to zero for every integer-valued $`m=m(X)\ge1`$ with $`m(X)=o(\log\log X)`$, uniformly over target values.*

</div>

The cutoff may depend on $`q`$, but $`S`$ and all cutoffs are fixed before $`r`$. Only $`e`$ varies with the target, and its support may occupy just part of $`S`$. Infinitely many changes are essential: finitely many integer dyadic corrections add a rational number. The allowance may grow as slowly as $`\log\log(n+3)`$, but it cannot be bounded. A modulus exceeding the bound would force $`e`$ eventually to vanish; its constant cumulative sum would then be divisible by every positive integer. Nonnegativity forces $`e=0`$. Polynomially growing coefficients satisfy the convergence hypothesis; $`a_n=2^n`$ does not.

Section <a href="#sec:construction" data-reference-type="ref" data-reference="sec:construction">2</a> proves the construction and Section <a href="#sec:prime-application" data-reference-type="ref" data-reference="sec:prime-application">3</a> transfers the stated prime-gap properties. For the actual primes, integral tail shifts characterise rationality. Two consecutive small differences with unequal gaps give a sufficient condition for irrationality. Finite enclosures certify individual witnesses without supplying arbitrarily late ones. The [companion’s literature discussion](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=context) contains the further comparisons, including finite subsums and other dyadic coefficient sequences.

<a id="sec:construction"></a>

# Proof of Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a>

<div class="proof">

*Proof.* *Fixed totals.* Use $`n_j-1`$ to cancel a cumulative residue and $`n_j,n_j+1`$ for a pair with fixed ordinary sum. Varying the pair changes its weighted contribution without altering any later residue to be cancelled. Choose an initial index $`n_{-1}\ge K`$ and centres with $`s_j=n_j-n_{j-1}\ge4`$, so the triples do not overlap. Let $`M_j`$ be positive integers with $`M_j\mid M_{j+1}`$, and let $`D_j`$ bound the digit at stage $`j`$. The spacing, moduli and digit bounds will be chosen below.

Let $`C_j`$ record the ordinary correction before the $`j`$th triple. Starting from $`C_0=0`$, prescribe
``` math
c_j=(-C_j)\bmod M_j\quad(0\le c_j<M_j),\qquad
 C_{j+1}=C_j+c_j+M_jD_j.
```
For integers $`0\le d_j\le D_j`$, set
``` math
\begin{equation}
\label{eq:correction-triple}
 e_{n_j-1}=c_j,\qquad e_{n_j}=M_jd_j,\qquad
 e_{n_j+1}=M_j(D_j-d_j),
\end{equation}
```
and put $`e_n=0`$ elsewhere. The two sums of a triple are
``` math
\begin{aligned}
 \sum_{r=n_j-1}^{n_j+1}e_r
    &=c_j+M_jD_j,\\
 \sum_{r=n_j-1}^{n_j+1}e_r2^{-r-1}
    &=c_j2^{-n_j}+M_jD_j2^{-n_j-2}+d_jM_j2^{-n_j-2}.
 \end{aligned}
```
The ordinary total contains no $`d_j`$, so the recurrence fixes every $`c_j`$ in advance. In the weighted total only the last term varies: transferring $`M_j`$ from $`n_j+1`$ to $`n_j`$ adds
``` math
w_j=M_j2^{-n_j-2}.
```

After $`c_j`$ has been inserted, the cumulative correction is divisible by $`M_j`$; the two entries of the pair preserve this divisibility. Fix $`q\mid M_J`$. At index $`n_J`$ both the coefficient correction and the cumulative correction are divisible by $`q`$. At every later triple, $`q`$ divides $`C_j`$ and $`M_j`$, so it also divides $`c_j`$ and both pair entries. The intervening corrections are zero. Hence
``` math
q\mid e_n,\qquad q\mid\sum_{i<n}e_i\qquad(n\ge n_J).
```
The entry $`c_J`$ need not be divisible by $`q`$, which is why it is placed at $`n_J-1`$, before the cutoff. The index $`n_J`$ depends on $`q`$ and the chosen moduli, but not on the digits or the value to be attained.

*Spacing and size.* The choices at stage $`j`$ are $`0,w_j,\ldots,D_jw_j`$. The covering argument will work if the later ranges total at least $`w_j`$. Taking $`D_i=2^{s_i}-1`$ compensates for separation by making each later range a scaled dyadic difference:
``` math
D_iw_i=(2^{n_i-n_{i-1}}-1)M_i2^{-n_i-2}
       =M_i\bigl(2^{-n_{i-1}-2}-2^{-n_i-2}\bigr).
```
Because $`M_i\ge M_j`$ for $`i>j`$, replacing every later modulus by $`M_j`$ gives the finite estimate
``` math
\begin{equation}
\label{eq:finite-overlap}
 \begin{aligned}
 \sum_{i=j+1}^{J}D_iw_i
 &\ge M_j\sum_{i=j+1}^{J}
       \bigl(2^{-n_{i-1}-2}-2^{-n_i-2}\bigr)\\
 &=w_j-M_j2^{-n_J-2}\qquad(J>j).
 \end{aligned}
\end{equation}
```
No monotonicity of the weights is needed. Each entry of <a href="#eq:correction-triple" data-reference-type="eqref" data-reference="eq:correction-triple">[eq:correction-triple]</a> is at most $`M_j2^{s_j}`$, so the size cost of separating the stages is exponential. We must fit this product below the allowance at all three indices, while $`s_j\to\infty`$ and every fixed positive integer eventually divides $`M_j`$.

To allow a nonmonotone bound $`f`$, put
``` math
h(n)=\inf_{m\ge n}\min(f(m),m).
```
This nondecreasing lower envelope tends to infinity even when $`f`$ oscillates. A bound at $`n_{j-1}`$ therefore controls all three later coordinates; the cap by $`m`$ ensures $`e_n\le n`$ and hence summability for every digit choice. Enlarge $`n_{-1}\ge K`$ until $`h(n_{-1})\ge32`$, and set
``` math
k_j=\max\{k\ge2:k!2^{k+2}\le h(n_{j-1})\},\qquad
 M_j=k_j!,\qquad s_j=k_j+2,\qquad n_j=n_{j-1}+s_j.
```
The maximum exists: $`k=2`$ is admissible because $`2!2^4=32`$, and $`k!2^{k+2}\to\infty`$. Since $`n_j\to\infty`$ and $`h`$ is nondecreasing and divergent, $`k_j`$ is nondecreasing and tends to infinity. Thus $`M_j\mid M_{j+1}`$, every fixed $`q`$ eventually divides $`M_j=k_j!`$, and $`s_j=k_j+2\to\infty`$. At every coordinate $`n`$ of the $`j`$th triple, this schedule also gives
``` math
0\le e_n\le M_j2^{s_j}\le h(n_{j-1})\le\min(f(n),n).
```
Let $`S=\bigcup_{j\ge0}\{n_j-1,n_j,n_j+1\}`$. For $`R\ge4`$, all sufficiently late centres are at least $`R`$ apart. Every interval of length $`H`$ contains at most $`3(H/R+2)`$ points from those triples; the earlier triples add a fixed number, independent of the interval’s position. Divide by $`H`$, take the supremum over positions, then let $`H\to\infty`$. The limiting upper bound is $`3/R`$; letting $`R\to\infty`$ proves upper Banach density zero.

*Attaining the interval.* The support and congruence requirements are now settled independently of the target. Only the digits remain to be chosen. Define
``` math
\beta=\sum_{j\ge0}\bigl(c_j2^{-n_j}+D_jw_j\bigr),\qquad
 F_j=\sum_{i\ge j}D_iw_i.
```
Even zero digits contribute $`\beta>0`$; $`F_j`$ is the maximum variable contribution from stage $`j`$ onwards. The size bound makes both finite, with $`F_0>0`$ and $`F_j\to0`$. The total correction is
``` math
\sum_ne_n2^{-n-1}=\beta+\sum_jd_jw_j.
```
Taking $`J\to\infty`$ in <a href="#eq:finite-overlap" data-reference-type="eqref" data-reference="eq:finite-overlap">[eq:finite-overlap]</a> now gives
``` math
\begin{equation}
\label{eq:overlap}
 F_{j+1}\ge M_j2^{-n_j-2}=w_j.
\end{equation}
```
These bounds do not yet prove that every point of $`[0,F_j]`$ is attained. A digit $`d`$ leaves a remainder in $`[0,F_{j+1}]`$ precisely for current remainders in
``` math
[dw_j,dw_j+F_{j+1}],\qquad d=0,\ldots,D_j.
```
These intervals meet or overlap by <a href="#eq:overlap" data-reference-type="eqref" data-reference="eq:overlap">[eq:overlap]</a>, and their union is $`[0,F_j]`$ because $`F_j=D_jw_j+F_{j+1}`$. Figure <a href="#fig:correction-and-overlap" data-reference-type="ref" data-reference="fig:correction-and-overlap">1</a> shows the two calculations.

<figure id="fig:correction-and-overlap" data-latex-placement="t">

<figcaption>Redistributing <span class="math inline"><em>M</em><sub><em>j</em></sub></span> between adjacent entries keeps their ordinary sum fixed and increases the dyadic sum by <span class="math inline"><em>w</em><sub><em>j</em></sub></span>. The candidate target intervals in the lower panel cover without gaps when <span class="math inline"><em>F</em><sub><em>j</em> + 1</sub> ≥ <em>w</em><sub><em>j</em></sub></span>. The sketch shows strict overlap; the proof also allows equality and establishes attainment by keeping the remainder in <span class="math inline">[0, <em>F</em><sub><em>j</em></sub>]</span> as <span class="math inline"><em>F</em><sub><em>j</em></sub> → 0</span>.</figcaption>
</figure>

Given $`x\in[0,F_0]`$, start with $`\rho_0=x`$. Having chosen the first $`j`$ digits, choose $`d_j`$ so that
``` math
\rho_{j+1}=\rho_j-d_jw_j\in[0,F_{j+1}].
```
The covering just proved makes this possible at every stage. Since $`0\le\rho_j\le F_j`$ and $`F_j\to0`$, we obtain
``` math
x-\sum_{i=0}^{j}d_iw_i=\rho_{j+1}\longrightarrow0.
```
Thus every $`x\in[0,F_0]`$ is attained, and we may take $`I=(A+\beta,A+\beta+F_0)`$. The target $`r\in I`$ determines only the digits, through $`x=r-A-\beta`$; it changes neither $`S`$, $`I`$ nor the cutoff $`N_q=n_J`$ chosen using $`q\mid M_J`$. This last selection is the standard finite-choice covering argument of \[crmarickovac2025, Lemma 4\]. The construction above supplies its summability and overlap hypotheses while imposing the congruences and requiring the support to lie in $`S`$.

*The logarithmic scale.* For $`f(n)=(\log(n+3))^\varepsilon`$, the size cost $`2^{s_j}`$ leads to the iterated logarithm. We choose separations of order $`\log\log n_j`$ and reserve part of the allowance for growing moduli. Keep the same triples and $`D_j=2^{s_j}-1`$, and set
``` math
\begin{aligned}
 s_j&=\left\lfloor\frac{\varepsilon}{2}
               \log_2\log(n_{j-1}+3)\right\rfloor,\\
 k_j&=\max\{k\ge2:k!\le(\log(n_{j-1}+3))^{\varepsilon/4}\},
 \end{aligned}
```
with $`M_j=k_j!`$ and $`n_j=n_{j-1}+s_j`$. Start far enough out that $`s_j\ge4`$ and all choices exist. The exponents $`\varepsilon/4`$ and $`\varepsilon/2`$ add to $`3\varepsilon/4<\varepsilon`$, so the corrections satisfy the prescribed bound:
``` math
M_j2^{s_j}\le(\log(n_{j-1}+3))^{3\varepsilon/4}
             \le(\log(n+3))^\varepsilon
```
at each coordinate $`n`$ of the triple. After enlarging the initial index, this is also at most $`n`$. The moduli remain nested, and every fixed positive integer divides all sufficiently late moduli. Summability, the congruence induction and <a href="#eq:finite-overlap" data-reference-type="eqref" data-reference="eq:finite-overlap">[eq:finite-overlap]</a> therefore apply without change. Since $`s_j\asymp_\varepsilon\log\log n_j`$, the relevant centres near $`[X,2X)`$ are separated by $`\gg_\varepsilon\log\log X`$. Each contributes at most three support points, giving
``` math
|S\cap[X,2X)|=O_\varepsilon(X/\log\log X).
```

Choose the same uniform starting index $`n\in[X,2X)`$ for both blocks. They agree when the block avoids $`S`$. A changed coordinate $`t\in S\cap[X,2X+m)`$ affects only starts in $`[t-m+1,t]`$, at most $`m`$ choices. The union bound gives
``` math
\begin{aligned}
 d_{\rm TV}(\mu_{a,X,m},\mu_{a+e,X,m})
 &\le\mathbb P\bigl(e_{n+i}\ne0\text{ for some }0\le i<m\bigr)\\
 &\le\frac{m|S\cap[X,2X+m)|}{X}.
 \end{aligned}
```
For $`m\le X`$, two dyadic bands cover $`[X,2X+m)`$, giving $`O_\varepsilon(m/\log\log X)`$. A block of length $`o(\log\log X)`$ therefore avoids $`S`$ with probability tending to one. The convergence is uniform over targets because the same $`S`$ contains every correction support. ◻

</div>

No limiting block law is assumed. A block-only test bounded in absolute value by $`B_0`$ changes its mean by at most $`2B_0d_{\rm TV}`$. For such a test also depending on the starting index, the common-index coupling gives $`2B_0m|S\cap[X,2X+m)|/X`$ instead. Vanishing absolute error can still erase a rare event; it supplies neither relative-frequency control nor a comparison of complete tails. The scale $`o(\log\log X)`$ is sufficient, not proved optimal. The companion’s [Section 2](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=sparse-construction) also distinguishes upper Banach density from ordinary density.

<a id="sec:prime-application"></a>

# Application to prime gaps

The elementary bound $`p_n\le1250(n+1)^4`$ suffices for convergence of the prime and gap series. We use the central-binomial argument of Erdős \[erdos1932, pp. 194–196\]; [Appendix A of the companion](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=prime-bound) derives the prime-power estimate and the bound. We may therefore apply Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a> to the gaps.

<div id="res:jointcountermodel" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-jointcountermodel">Lean†</a></p>

**Corollary 2** (a rational sum with the stated prime-gap statistics). *Let $`p_0=2,p_1=3,\ldots`$ be the primes and $`g_n=p_{n+1}-p_n`$. Given $`K\in\mathbb{N}`$ and $`0<\varepsilon\le1`$, there is $`b:\mathbb{N}\to\mathbb{N}`$ with rational dyadic sum such that $`b_n=g_n`$ for $`n<K`$, $`b_n\ge g_n`$, and $`b_n-g_n\le(\log(n+3))^\varepsilon`$ eventually. For every fixed positive modulus, both the coefficients and the cumulative positions eventually retain their corresponding residues. The empirical distributions of unnormalised blocks have total variation distance tending to zero for lengths $`o(\log\log X)`$, and for every fixed nonzero $`F\in\mathbb{Z}[x_0,\ldots,x_k]`$,
``` math
\bigl|\{n<N:F(b_n,\ldots,b_{n+k})=0\}\bigr|=o(N).
```
Moreover, with $`P_n=2+\sum_{i<n}b_i`$,
``` math
0\le P_n-p_n=O_\varepsilon\!\left(
       \frac{n(\log(n+3))^\varepsilon}{\log\log n}\right),
 \qquad P_n\sim n\log n.
```
These positions are not asserted to be prime.*

</div>

Lean proves this for every $`\varepsilon>0`$, assuming Schlage-Puchta’s Lemma 4 \[schlagepuchta2011\] only for the nonconcentration bound and the prime number theorem only for $`P_n\sim n\log n`$.

<div class="proof">

*Proof.* Apply Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a> to $`a=g`$, choose a rational $`r\in I`$, and fix the resulting sequence $`b=g+e`$. The correction, congruence and growing-block assertions follow at once. It remains to transfer polynomial nonconcentration and cumulative growth. For fixed $`k`$ and nonzero $`F\in\mathbb{Z}[x_0,\ldots,x_k]`$, a new zero requires a block meeting $`S`$, so
``` math
\begin{aligned}
 &\bigl|\{n<N:F(b_n,\ldots,b_{n+k})=0\}\bigr|\\
 &\quad\le\bigl|\{n<N:F(g_n,\ldots,g_{n+k})=0\}\bigr|
       +\sum_{i=0}^k|S\cap[i,N+i)|.
 \end{aligned}
```
The first count is $`o(N)`$ by Schlage-Puchta’s Lemma 4 \[schlagepuchta2011\]; the finitely many support counts are $`o(N)`$ because $`S`$ has density zero. We count the event $`F=0`$, not averages of $`F`$, so no bound on its values is needed. Since $`b`$ was chosen before $`F,k`$, the same sequence satisfies every fixed-polynomial condition.

To estimate $`P_n-p_n=\sum_{i<n}e_i`$, first observe that $`|S\cap[0,n)|=O_\varepsilon(n/\log\log n)`$. Indeed, the indices below $`\sqrt n`$ contribute at most $`\sqrt n`$ points, and on $`[\sqrt n,n)`$ we sum the dyadic support bounds, whose lengths add to $`O(n)`$ and whose $`\log\log X`$ are comparable to $`\log\log n`$. Multiplying by the pointwise correction bound gives the stated error. For $`0<\varepsilon\le1`$ this is $`o(n\log n)`$, so the prime number theorem \[mv2007, Chapter 6\] gives $`P_n\sim n\log n`$. Finally, summing nonnegative terms in the opposite order, we obtain
``` math
\sum_{n\ge0}\frac{P_n}{2^{n+1}}
 =2+\sum_{i\ge0}b_i\sum_{n>i}2^{-n-1}
 =2+\sum_{i\ge0}\frac{b_i}{2^{i+1}}=2+r\in\mathbb{Q}.
```
 ◻

</div>

For $`\varepsilon>1`$ we may use exponent $`1`$, which gives smaller corrections and the error $`O(n\log(n+3)/\log\log n)`$. Thus the conclusions extend to every $`\varepsilon>0`$. For each fixed $`y\ge2`$, eventual congruence modulo $`y!`$ also gives $`\gcd(P_n,y!)=1`$ once $`p_n>y`$. The cutoff depends on $`y`$; primality would require excluding every prime up to $`\sqrt{P_n}`$ at that same index. Even prime-valued positions could omit intervening primes.

Land’s draft \[land2026, Theorem 2\] proves conditional irrationality under a uniform Hardy–Littlewood hypothesis of the kind formulated by Kuperberg \[kuperberg2023, Conjecture 1.3\]. Ringer’s draft \[ringer2026\] obtains conditional normality. Their quantitative prime-pattern hypotheses are stronger than the absolute block comparison above and are not assumed here. The [companion’s Section 3](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=context) compares the hypotheses and sampling conventions.

<a id="sec:parts"></a>

# The prime series and its actual tails

We now study complete tails of the actual prime gaps. Put $`G=\sum_{n\ge0}g_n2^{-(n+1)}`$. The polynomial bound from Section <a href="#sec:prime-application" data-reference-type="ref" data-reference="sec:prime-application">3</a> proves convergence and makes the endpoint in finite summation by parts vanish.

<div id="res:infinite" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-infinite">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-infinite-comparator">Comparator</a></p>

**Theorem 3** (prime-to-gap identity). *The actual prime and gap series satisfy $`\Pi=2+G`$. Their complete tails
``` math
T_N=\sum_{j\ge1}g_{N+j}2^{-j}
```
satisfy $`T_0=2G-1`$ and $`T_{N+1}=2T_N-g_{N+1}`$. Thus $`\Pi`$, $`G`$ and $`T_0`$ have the same rationality status.*

</div>

<div class="proof">

*Proof.* Finite summation by parts gives
``` math
\sum_{i=0}^{n}\frac{p_i}{2^{i+1}}
 =2+\sum_{i=0}^{n-1}\frac{g_i}{2^{i+1}}-\frac{p_n}{2^{n+1}}.
```
Since $`p_n=O((n+1)^4)`$, the endpoint tends to zero and we obtain $`\Pi=2+G`$. We obtain the tail recurrence by splitting off the first term of $`T_N`$; removing $`g_0=1`$ from $`G`$ gives $`T_0=2G-1`$. ◻

</div>

Tao noted this reduction in the problem’s forum discussion \[erdosproblems251thread, 7 October 2025\].

<div id="res:irr-equivalence" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-irr-equivalence">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-irr-equivalence-comparator">Comparator</a></p>

**Corollary 4** (exact irrationality reformulation). *The prime-value dyadic series is irrational if and only if the prime-gap dyadic series is. Both series converge by the polynomial bound proved above; neither side is proved irrational.*

</div>

<div class="proof">

*Proof.* Adding the rational number $`2`$ preserves rationality and irrationality. ◻

</div>

The index $`N`$ is the last omitted coefficient, so $`T_N`$ starts with $`g_{N+1}/2`$. Rescaling distinguishes these tails from the remainders of $`G`$. The recurrence also admits an extra term $`C2^N`$; the vanishing boundary condition below excludes it.

<div id="res:true-tail" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos251/PaperCompleteR20/TrueTail.lean#L57">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-true-tail-comparator">Comparator</a></p>

**Lemma 5** (the boundary condition for the tail recurrence). *Let $`\sum_{j\ge1}|a_j|2^{-j}<\infty`$ and $`U_{N+1}=2U_N-a_{N+1}`$. Then $`U_N=\sum_{j\ge1}a_{N+j}2^{-j}`$ for every $`N`$ if and only if $`2^{-N}U_N\to0`$.*

</div>

<div class="proof">

*Proof.* Iteration gives $`2^{-N}U_N=U_0-\sum_{j=1}^Na_j2^{-j}`$. The limit is zero exactly when $`U_0`$ is the full series. Subtracting its first $`N`$ terms and multiplying by $`2^N`$ then gives the tail formula. Conversely the formula implies $`2^{-N}U_N=\sum_{k>N}a_k2^{-k}\to0`$ by absolute convergence. ◻

</div>

<a id="sec:tail"></a>

## Integral shifts

For $`U_{N+1}=2U_N-a_{N+1}`$ with $`a_n\in\mathbb{Z}`$, write $`D_h(N)=U_{N+h}-U_N`$. Modulo integers, each step doubles, so an integral shift is a return to the same fractional part. For rational $`U_0`$, the power of two in its reduced denominator determines when returns of positive length can begin; the odd part determines their lengths.

<div id="res:escape-irrational" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-escape-irrational">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-escape-irrational-comparator">Comparator</a></p>

**Theorem 6** (exact rationality classification). *For a real integer-coefficient recurrence, the following are equivalent: $`U_0\in\mathbb{Q}`$; $`D_h(N)\in\mathbb{Z}`$ for some $`h\ge1,N\ge0`$; and, for some fixed $`h\ge1`$, $`D_h(N)\in\mathbb{Z}`$ at every sufficiently large $`N`$. More precisely, if $`U_0=u/(2^sd)`$ is in lowest terms, with $`d`$ odd, then
``` math
\operatorname{den}(U_N)=2^{\max(s-N,0)}d,\qquad
 D_h(N)\in\mathbb{Z}\ \Longleftrightarrow\ N\ge s\ \text{and}\ d\mid2^h-1
 \quad(h\ge1).
```
Consequently $`U_0`$ is irrational exactly when every positive shift is nonintegral at every index, equivalently when for each fixed $`h\ge1`$ there are arbitrarily late nonintegral shifts.*

</div>

<div class="proof">

*Proof.* Iteration gives
``` math
U_N-2^NU_0\in\mathbb{Z},\qquad
 D_h(N)-2^N(2^h-1)U_0\in\mathbb{Z}.
```
An integral shift with $`h\ge1`$ makes the nonzero integer multiple $`2^N(2^h-1)U_0`$ integral, and therefore forces $`U_0\in\mathbb{Q}`$. Conversely, write $`U_0=u/(2^sd)`$ in lowest terms. Multiplication by $`2^N`$ cancels exactly $`\min(N,s)`$ powers of two from the denominator. The remaining factor $`2^h-1`$ is odd, so the second relation is integral exactly when $`N\ge s`$ and $`d\mid2^h-1`$. For $`d>1`$, Euler’s congruence provides such a shift $`h=\varphi(d)`$, and for $`d=1`$ we take $`h=1`$. This shift works for every $`N\ge s`$. Negating the pointwise and eventual criteria gives the two assertions about irrationality. ◻

</div>

The classification applies to any integer-coefficient recurrence; Lemma <a href="#res:true-tail" data-reference-type="ref" data-reference="res:true-tail">5</a> is needed only to identify complete tails. The periodicity is of fractional parts, not necessarily tail values. For the positive even coefficients $`2,4,2,4,\ldots`$ starting at $`n=1`$, the tails alternate between $`8/3`$ and $`10/3`$. Length-$`1`$ shifts are nonintegral, but length-$`2`$ shifts vanish: one shift length cannot suffice.

<a id="sec:local-certificate"></a>

# Small tail differences and finite tests

Fix $`h\ge1`$ and put $`D_N=T_{N+h}-T_N`$ and $`\delta_N=g_{N+h+1}-g_{N+1}`$. Then $`D_{N+1}=2D_N-\delta_N`$. Both gap indices are positive, so neither involves the exceptional odd gap $`g_0=1`$; hence $`\delta_N`$ is even. Two integral differences of absolute value less than one must both vanish, forcing $`\delta_N=0`$. Evenness yields the sharper signed test below.

<div id="res:signedwindow" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-signedwindow">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-signedwindow-comparator">Comparator</a></p>

**Proposition 7** (two consecutive differences of absolute value less than one). *Let $`D,D'\in\mathbb{R}`$, $`\delta\in2\mathbb{Z}`$ and $`D'=2D-\delta`$. The conditions $`|D|<1`$, $`|D'|<1`$ and $`\delta\ne0`$ hold exactly when, for some $`s\in\{-1,1\}`$,
``` math
\delta=2s,\qquad \tfrac12<sD<1.
```
In that case $`sD'\in(-1,0)`$ and both $`D`$ and $`D'`$ are nonintegral.*

</div>

<div class="proof">

*Proof.* The bounds on $`D,D'`$ imply $`-3<\delta<3`$, so a nonzero even $`\delta`$ equals $`2s`$ with $`s\in\{-1,1\}`$. Substituting in $`D'=2D-2s`$ gives $`1/2<sD<1`$. Conversely this interval gives $`sD'=2sD-2\in(-1,0)`$. ◻

</div>

The endpoints cannot be included: when $`\delta=2`$, $`D=1/2`$ gives $`D'=-1`$, and $`D=1`$ already violates $`|D|<1`$. The zero triple $`D=D'=\delta=0`$ shows why the mismatch is also required.

<div id="prob:smallpair" class="problem">

**Problem 8** (two small tail differences at arbitrarily large indices). For every integer $`h\ge1`$ and every cutoff $`N_0`$, exhibit $`N\ge N_0`$ with
``` math
\begin{equation}
\label{eq:smallpair}
 |T_{N+h}-T_N|<1,\quad |T_{N+h+1}-T_{N+1}|<1,\quad
 g_{N+h+1}\ne g_{N+1}.
\end{equation}
```

</div>

Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">6</a> requires nonintegrality, not smallness; <a href="#eq:smallpair" data-reference-type="eqref" data-reference="eq:smallpair">[eq:smallpair]</a> is only a sufficient condition. All three requirements must hold at the same arbitrarily late indices. Separate infinite sets need not intersect.

By Proposition <a href="#res:signedwindow" data-reference-type="ref" data-reference="res:signedwindow">7</a>, such an index must have $`\delta_N=\pm2`$. Schlage-Puchta’s lemma \[schlagepuchta2011, Lemma 4\], applied to $`x_h-x_0\pm2`$, shows that these eligible indices already have density zero. Density zero is compatible with arbitrarily late witnesses; it supplies no lower bound for their occurrence. The absolute block comparison in Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a> likewise gives no relative-frequency estimate for this rare event.

<a id="finite-separation-from-the-integers"></a>

## Finite separation from the integers

An enclosure certifies nonintegrality only when it misses every integer. Choose $`M(n)\ge g_n`$ with $`\sum_nM(n)2^{-n}<\infty`$, and write
``` math
S_{h,N,L}=\sum_{j=1}^L(g_{N+h+j}-g_{N+j})2^{-j},\qquad
 R_{h,N,L}(M)=\sum_{j>L}(M(N+h+j)+M(N+j))2^{-j}.
```
Splitting the complete tails after $`L`$ terms gives
``` math
D_N=S_{h,N,L}+2^{-L}D_{N+L},\qquad
 |D_N-S_{h,N,L}|\le R_{h,N,L}(M).
```
The uncomputed term is a rescaled later complete tail difference with the same shift $`h`$. An arbitrary real majorant gives an enclosure, but need not give a computable radius.

For the actual prime gaps, one computable choice is $`M(n)=1250(n+2)^4`$. For $`P(x)=x^4+8x^3+36x^2+104x+150`$, the identity $`2P(x)=(x+1)^4+P(x+1)`$ telescopes to $`\sum_{j=1}^{J}(x+j)^4 2^{-j}=P(x)-2^{-J}P(x+J)`$. The endpoint vanishes as $`J\to\infty`$, giving
``` math
R_{h,N,L}(M)=1250\,2^{-L}
             \bigl(P(N+h+L+2)+P(N+L+2)\bigr).
```

<div id="res:truncation" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos251/PaperTailBoundsR7.lean#L273">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-truncation-comparator">Comparator</a></p>

**Proposition 9** (finite separation criterion). *If for every $`h\ge1`$ and every cutoff $`N_0`$ there are $`N\ge N_0,L\ge1`$ with
``` math
\begin{equation}
\label{eq:truncation}
 \operatorname{dist}(S_{h,N,L},\mathbb{Z})>R_{h,N,L}(M),
\end{equation}
```
then $`\Pi`$ is irrational.*

</div>

<div class="proof">

*Proof.* The enclosure gives $`\operatorname{dist}(D_N,\mathbb{Z})\ge
\operatorname{dist}(S_{h,N,L},\mathbb{Z})-R_{h,N,L}(M)>0`$. Thus each fixed positive shift is nonintegral at arbitrarily large indices, and Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">6</a> applies. ◻

</div>

<div id="res:complete-truncation" class="remark">

*Remark 1* (what arbitrary truncation does not gain). Whenever $`|D-S_L|\le R_L\to0`$, nonintegrality of $`D`$ is equivalent to $`\operatorname{dist}(S_L,\mathbb{Z})>R_L`$ for some $`L`$. Indeed, for $`\delta=\operatorname{dist}(D,\mathbb{Z})>0`$, take $`R_L<\delta/2`$ and use the $`1`$-Lipschitz property of distance. Unrestricted depth therefore gives an exact reformulation, not an additional analytic estimate. At a prescribed logarithmic depth one must also control the margin from the integers as $`N`$ varies; a shrinking remainder alone does not do so. The companion, Appendix D.2, gives an explicit example distinguishing refinement at a fixed value from enclosures of changing values.

</div>

A nonintegral value need not lie in either signed interval of Proposition <a href="#res:signedwindow" data-reference-type="ref" data-reference="res:signedwindow">7</a>. To certify <a href="#eq:smallpair" data-reference-type="eqref" data-reference="eq:smallpair">[eq:smallpair]</a>, suppose $`\delta_N=2s`$, with $`s\in\{-1,1\}`$, and enclose $`D_N`$ using integers $`A,Q,B`$ with $`Q>0`$, $`B\ge0`$ and $`|QD_N-A|\le B`$. Then $`sD_N\in[(sA-B)/Q,(sA+B)/Q]`$. Placing its lower endpoint above $`1/2`$ and its upper endpoint below $`1`$ gives, respectively,
``` math
2sA-Q>2B,\qquad Q-sA>B.
```
We retain the signed numerator: reduction modulo $`Q`$ preserves distance to $`Q\mathbb{Z}`$ but loses the enclosure’s location. The gap difference fixes $`s`$, so it cannot be chosen to fit the enclosure. At $`h=1,N=2,L=40`$, one has $`\delta_2=g_4-g_3=-2`$ and
``` math
Q=2^{40},\qquad A=-662838684750,\qquad B=11764181250,\qquad s=-1.
```
Here $`A/Q=S_{1,2,40}`$ and $`B/Q=R_{1,2,40}(M)`$, and the two strict margins are $`202637379224`$ and $`424908761776`$. The [companion’s integer certificates](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=finite-certificates) give the prime-index calculation and remainder derivation. This finite pair leaves the quantifiers in Problem <a href="#prob:smallpair" data-reference-type="ref" data-reference="prob:smallpair">8</a> unresolved.

<a id="sec:open"></a>

# Further consequences and questions

We can place the interval in Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a> inside $`(A,A+\eta)`$ for any $`\eta>0`$. Choose $`K'\ge K`$ such that $`(K'+1)2^{-K'}<\eta`$, and start the construction after $`K'`$. The bound $`e_n\le n`$ from the proof gives
``` math
0<\sum_ne_n2^{-(n+1)}\le(K'+1)2^{-K'}<\eta.
```
Thus rational and irrational targets remain available arbitrarily close to $`A`$, with the prescribed prefix unchanged. The estimate controls the dyadic change, not the ordinary total.

<a id="sec:carry"></a>

## Nonperiodic coefficients

Rationality forces eventual periodicity of the binary digits obtained after carrying, not of the original integer coefficients. For example,
``` math
\sum_{i=0}^{n-1}\frac{i-1}{2^{i+1}}=-\frac{n}{2^n}\longrightarrow0.
```
Its coefficients are unbounded and its first coefficient is $`-1`$. We obtain a positive even example by taking $`c_n=2(n^2+4n+2)`$ and $`U_n=2(n+4)^2`$. Direct substitution gives $`U_{n+1}=2U_n-c_{n+1}`$, while the polynomial growth gives $`2^{-n}U_n\to0`$. Lemma <a href="#res:true-tail" data-reference-type="ref" data-reference="res:true-tail">5</a> therefore identifies $`U`$ as the complete tail and yields
``` math
\sum_{j\ge1}c_j2^{-j}=32,\qquad
 \sum_{n\ge0}c_n2^{-(n+1)}=18.
```
The coefficients increase strictly and $`c_{n+1}-c_n=4n+10`$ is never $`\pm2`$. The [companion’s Section 8](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=counterexamples) gives further examples, including a bounded nonperiodic sequence in Appendix D. None of these examples constructs consecutive primes.

<div id="res:gap-nonperiodic" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L175">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md#res-gap-nonperiodic-comparator">Comparator</a></p>

**Proposition 10** (prime gaps do not become periodic). *For every positive $`h`$, the actual consecutive-prime-gap sequence is not eventually periodic with period $`h`$.*

</div>

<div class="proof">

*Proof.* If the gaps were eventually periodic, they would be bounded. For each $`m\ge2`$, however, the $`m-1`$ integers $`m!+2,\ldots,m!+m`$ are composite. The consecutive primes on either side therefore have a gap of at least $`m`$, contradicting boundedness. ◻

</div>

The results on bounded prime gaps \[zhang2014\], clusters of each fixed size \[maynard2015; polymath2014\], and extreme large gaps \[fgkmt2018\] do not give the simultaneous inequalities in <a href="#eq:smallpair" data-reference-type="eqref" data-reference="eq:smallpair">[eq:smallpair]</a>. This remains so with Polymath’s bound $`\liminf_n g_n\le246`$ \[polymath2014, Theorem 1.4(i)\]. For fixed $`h`$ and $`\varepsilon>0`$, taking $`L=\lceil(4+\varepsilon)\log_2(N+2)\rceil`$ in the polynomial remainder gives an error $`O_{h,\varepsilon}(N^{-\varepsilon})`$. The finite sum must still clear the relevant boundary by more than this error to supply a witness for Problem <a href="#prob:smallpair" data-reference-type="ref" data-reference="prob:smallpair">8</a>. The perturbation theorem rules out no argument using additional primality information or quantitative rare-event estimates.

<a id="sec:pinned-lean-sources"></a>

# Verification and reproducibility

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-251-prime-gap-dyadic-series.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

The linked Lean declarations use Lean 4 \[lean4\] and mathlib \[mathlib\]. The formal proof of Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a> changes one coordinate at each stage, whereas the proof here uses triples. Both choose the set containing the supports, the interval and the congruence cutoffs before the value of the sum. For Corollary <a href="#res:jointcountermodel" data-reference-type="ref" data-reference="res:jointcountermodel">2</a>, the formal statement covers every $`\varepsilon>0`$ and assumes Schlage-Puchta’s lemma only for nonconcentration and the prime number theorem only for the asymptotic $`P_n\sim n\log n`$. The source links record formal support for the linked statements, rather than verification of the different printed proofs. The [companion’s Appendix G](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=short-source-index) retains the complete source index at this note’s original pin, including the finite telescoping identities and their nonperiodicity consequences. Its [Section 3](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=context) retains the broader subsum and automatic-sequence comparisons.

<a id="acknowledgements"></a>

## Acknowledgements

The author received no external funding and declares no competing interests. The numbering follows Bloom’s catalogue \[erdosproblems\].

<div class="thebibliography">

99

Paul Erdős, [*Sur certaines séries à valeur irrationnelle*](https://users.renyi.hu/~p_erdos/1958-19.pdf). L’Enseignement Mathématique **4** (1958), 93–100, doi:[10.5169/seals-34629](https://doi.org/10.5169/seals-34629). Paul Erdős and Ronald L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf). Monographies de L’Enseignement Mathématique, L’Enseignement Mathématique, 1980. Paul Erdős, [*On the irrationality of certain series: problems and results*](https://doi.org/10.1017/CBO9780511897184.009). New Advances in Transcendence Theory, Cambridge University Press, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). Kevin Ford, Ben Green, Sergei Konyagin, James Maynard and Terence Tao, [*Long gaps between primes*](https://arxiv.org/abs/1412.5029v3). Journal of the American Mathematical Society **31** (2018), 65–105, doi:[10.1090/jams/876](https://doi.org/10.1090/jams/876); arXiv:[1412.5029v3](https://arxiv.org/abs/1412.5029v3). John A. Fridy, [*Generalized bases for the real numbers*](https://www.fq.math.ca/Scanned/4-3/fridy.pdf). The Fibonacci Quarterly **4** (1966), no. 3, 193–201. Vjekoslav Kovač and Terence Tao, [*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593v4). Acta Mathematica Hungarica **175** (2025), 572–608, doi:[10.1007/s10474-025-01528-0](https://doi.org/10.1007/s10474-025-01528-0); arXiv:[2406.17593v4](https://arxiv.org/abs/2406.17593v4). Statement and section numbers refer to arXiv version 4. Vivian Kuperberg, [*Sums of singular series with large sets and the tail of the distribution of primes*](https://arxiv.org/abs/2210.09775v2). The Quarterly Journal of Mathematics **74** (2023), no. 4, 1457–1479, doi:[10.1093/qmath/haad030](https://doi.org/10.1093/qmath/haad030); arXiv:[2210.09775v2](https://arxiv.org/abs/2210.09775v2). Statement numbers refer to arXiv version 2, 15 June 2023. Johan Land, [*A conditional proof of the irrationality of $`\sum_{n\ge1}p_n2^{-n}`$ under a uniform Hardy–Littlewood prime-tuples conjecture*](https://github.com/beetree/math_erdos_251). Research draft, 5 September 2026. Formalisation material accompanies the draft. Leonardo de Moura and Sebastian Ullrich, [*The Lean 4 theorem prover and programming language*](https://doi.org/10.1007/978-3-030-79876-5_37). Automated Deduction – CADE 28, Lecture Notes in Computer Science, Springer, 2021, pp. 625–635, doi:[10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37). The mathlib Community, [*The Lean mathematical library*](https://doi.org/10.1145/3372885.3373824). Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs, ACM, 2020, pp. 367–381, doi:[10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). Describes a Lean 3-era snapshot; the repository lock identifies the library used by the present Lean 4 sources. James Maynard, [*Small gaps between primes*](https://doi.org/10.4007/annals.2015.181.1.7). Annals of Mathematics **181** (2015), 383–413, doi:[10.4007/annals.2015.181.1.7](https://doi.org/10.4007/annals.2015.181.1.7). Hugh L. Montgomery and Robert C. Vaughan, [*Multiplicative Number Theory I: Classical Theory*](https://doi.org/10.1017/CBO9780511618314). Cambridge Studies in Advanced Mathematics, Cambridge University Press, 2007, doi:[10.1017/CBO9780511618314](https://doi.org/10.1017/CBO9780511618314). Yitang Zhang, [*Bounded gaps between primes*](https://doi.org/10.4007/annals.2014.179.3.7). Annals of Mathematics **179** (2014), 1121–1174, doi:[10.4007/annals.2014.179.3.7](https://doi.org/10.4007/annals.2014.179.3.7). Thomas F. Bloom, [*Erdős Problem \#251*](https://www.erdosproblems.com/251). 2026. Accessed 6 September 2026. Erdős Problems contributors, [*Erdős Problem \#251 discussion thread*](https://www.erdosproblems.com/forum/thread/251). 2026. Accessed 6 September 2026: Tao comment of 7 October 2025 and Land comments of 6 September 2026. Stefan Ringer, [*Local gap statistics, telescoping, and normality: a local-pattern approach to Erdős problem 251*](https://github.com/StefanRinger/erdos-251). Preprint, 11 September 2026. Mutable main-branch TeX consulted 16 September 2026; the cited conditional statements were rechecked 18 September 2026. Formalisation material accompanies the draft. Tonći Crmarić and Vjekoslav Kovač, [*On the irrationality of certain super-polynomially decaying series*](https://arxiv.org/abs/2504.18712v1). Colloquium Mathematicum **179** (2025), 55–68, doi:[10.4064/cm9628-5-2025](https://doi.org/10.4064/cm9628-5-2025); arXiv:[2504.18712v1](https://arxiv.org/abs/2504.18712v1). Lemma 4 is cited using arXiv version 1. Jan-Christoph Schlage-Puchta, [*The irrationality of some number theoretical series*](https://arxiv.org/abs/1105.1451v1). Acta Arithmetica **126** (2007), no. 4, 295–303, doi:[10.4064/aa126-4-1](https://doi.org/10.4064/aa126-4-1); arXiv:[1105.1451v1](https://arxiv.org/abs/1105.1451v1). Published in 2007; arXiv upload is from 2011. Lemma and preprint page locators refer to arXiv version 1. Paul Erdős, [*Beweis eines Satzes von Tschebyschef*](https://users.renyi.hu/~p_erdos/1932-01.pdf). Acta Litterarum ac Scientiarum Szeged **5** (1932), 194–198. D. H. J. Polymath, [*Variants of the Selberg sieve, and bounded intervals containing many primes*](https://arxiv.org/abs/1407.4897v4). Research in the Mathematical Sciences **1** (2014), article 12, doi:[10.1186/s40687-014-0012-7](https://doi.org/10.1186/s40687-014-0012-7); arXiv:[1407.4897v4](https://arxiv.org/abs/1407.4897v4). Theorem 1.4(i) refers to arXiv version 4 (22 December 2014); the journal numbers it Theorem 4(i). An erratum is recorded at doi:10.1186/s40687-015-0033-x.

</div>
