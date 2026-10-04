<a id="erdos-251-prime-gap-dyadic-series"></a>

# Sparse Congruence-Preserving Perturbations of Dyadic Series

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

For each convergent dyadic series with nonnegative integer coefficients, we construct nonnegative integer perturbations whose sums fill an interval and whose supports lie in one set of upper Banach density zero. The corrections satisfy any prescribed bound tending to infinity for all sufficiently large indices; for each fixed modulus, coefficient and partial-sum residues are eventually preserved. The construction varies adjacent corrections while keeping their ordinary sum fixed. In the prime-gap application with eventual correction bound $`\log(n+3)`$, it gives vanishing total variation error for blocks of length $`o(\log\log X)`$ sampled on $`[X,2X)`$ and preserves the cumulative asymptotic $`n\log n`$. The cumulative positions need not be prime, and the irrationality question remains open.

<a id="sec:problem"></a>

# Introduction

Let $`p_0=2,p_1=3,\ldots`$ be the primes and put $`g_n=p_{n+1}-p_n`$. Erdős asked whether
``` math
\Pi=\sum_{n\ge0}\frac{p_n}{2^{n+1}}
```
is irrational \[erdos1958, p. 94\]\[erdosgraham1980, p. 62\] \[erdos1988, p. 103\]. Summation by parts gives $`\Pi=2+\sum_{n\ge0}g_n2^{-(n+1)}`$, with convergence justified in Section <a href="#sec:prime-application" data-reference-type="ref" data-reference="sec:prime-application">3</a>. We study which properties of the gaps survive when the latter sum is changed to a prescribed value.

We prove a perturbation theorem for arbitrary convergent dyadic series with nonnegative integer coefficients. All corrections are supported on one sparse set, chosen before the value of the sum. Their sizes may be eventually bounded by any prescribed function tending to infinity, while the sums still fill an interval. The construction fixes, before choosing the target, a cutoff for each modulus beyond which both the corrections and their partial sums are divisible by that modulus. For prime gaps, the original and altered empirical block distributions have total variation distance tending to zero for lengths $`o(\log\log X)`$ sampled in $`[X,2X)`$. The cumulative positions are asymptotic to $`n\log n`$. The irrationality of the actual prime series remains a distinct question: these comparison sequences need not have prime cumulative positions.

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
For integers $`X,m\ge1`$, let $`\mu_{a,X,m}`$ denote the distribution of $`(a_n,\ldots,a_{n+m-1})`$ when $`n`$ is uniform on $`[X,2X)`$. Blocks are unnormalised and counted with multiplicity. We use $`d_{\rm TV}(\mu,\nu)=\sup_B|\mu(B)-\nu(B)|`$.

<div id="res:sparserationalisation" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-251-prime-gap-dyadic-series.md#res-sparserationalisation">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-251-prime-gap-dyadic-series.md#res-sparserationalisation-comparator">Comparator</a></p>

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

The set $`S`$, the interval $`I`$ and every congruence cutoff are fixed before $`r`$ is chosen. The correction $`e`$ depends on $`r`$; its support may occupy only part of $`S`$. Polynomially growing nonnegative integer sequences satisfy the convergence hypothesis, whereas $`a_n=2^n`$ does not. The prescribed bound may grow as slowly as $`\log\log(n+3)`$. A bounded correction would have to vanish identically: a modulus exceeding the bound makes $`e`$ eventually zero, and its constant cumulative sum must then be divisible by every positive integer.

Section <a href="#sec:construction" data-reference-type="ref" data-reference="sec:construction">2</a> gives the construction, and Section <a href="#sec:prime-application" data-reference-type="ref" data-reference="sec:prime-application">3</a> applies it to prime gaps. The [long record](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=scope-actual-tails) develops the separate integral-tail criteria and finite separation tests for the actual prime series.

<a id="sec:construction"></a>

# Proof of Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a>

<div class="proof">

*Proof.* *Fixed totals.* At stage $`j`$ we put a correction at $`n_j-1`$ and a variable pair at $`n_j,n_j+1`$. We keep the pair’s ordinary sum fixed. Consequently, the residue to be cancelled at a later stage is independent of all earlier pair choices. Let $`n_{-1}\ge K`$, write $`s_j=n_j-n_{j-1}\ge4`$, and take positive integers $`M_j`$ with $`M_j\mid M_{j+1}`$. For now let $`D_j`$ be a positive integer bounding the digit at stage $`j`$. We first describe the corrections for these parameters, then choose them to obtain both sparsity and an interval of sums.

Starting from $`C_0=0`$, define
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
The first identity verifies that $`C_j`$ is the cumulative correction before $`n_j-1`$, whatever the digits are. Thus all $`C_j`$ and $`c_j`$ can be computed before choosing a single $`d_j`$. The second identity shows that increasing $`d_j`$ by one transfers $`M_j`$ from $`n_j+1`$ to $`n_j`$ and increases the weighted sum by
``` math
w_j=M_j2^{-n_j-2}.
```

After $`c_j`$ has been inserted, the cumulative correction is divisible by $`M_j`$; the two entries of the pair preserve this divisibility. Fix $`q\mid M_J`$. At index $`n_J`$ both the coefficient correction and the cumulative correction are divisible by $`q`$. At every later triple, $`q`$ divides $`C_j`$ and $`M_j`$, so it also divides $`c_j`$ and both pair entries. The intervening corrections are zero. Hence
``` math
q\mid e_n,\qquad q\mid\sum_{i<n}e_i\qquad(n\ge n_J).
```
The entry $`c_J`$ need not be divisible by $`q`$, which is why it is placed at $`n_J-1`$, before the cutoff. The index $`n_J`$ depends on $`q`$ and the chosen moduli, but not on the digits or the value to be attained.

*Spacing and size.* The variable part at stage $`j`$ takes the values $`0,w_j,\ldots,D_jw_j`$. To fill the gaps between these choices, we need the later variable parts to have total range at least $`w_j`$. This suggests making each later range a difference of successive dyadic scales. We therefore choose $`D_i=2^{s_i}-1`$, for which
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
The digit range $`D_j=2^{s_j}-1`$ therefore gives the required overlap estimate even when the separations increase. Every entry of <a href="#eq:correction-triple" data-reference-type="eqref" data-reference="eq:correction-triple">[eq:correction-triple]</a> is at most $`M_j2^{s_j}`$, so we must keep this quantity below the prescribed bound at the three indices. We must also have $`s_j\to\infty`$ and ensure that every fixed positive integer divides all sufficiently late $`M_j`$.

To allow a nonmonotone bound $`f`$, put
``` math
h(n)=\inf_{m\ge n}\min(f(m),m).
```
This nondecreasing lower envelope tends to infinity. A bound chosen using $`h(n_{j-1})`$ is therefore valid at each of the later coordinates of the triple. The extra cap by $`m`$ serves a separate purpose: $`e_n\le n`$ will make the weighted corrections summable. Choose $`n_{-1}`$ with $`h(n_{-1})\ge32`$, and set
``` math
k_j=\max\{k\ge2:k!2^{k+2}\le h(n_{j-1})\},\qquad
 M_j=k_j!,\qquad s_j=k_j+2,\qquad n_j=n_{j-1}+s_j.
```
The maximum exists: $`k=2`$ is admissible because $`2!2^4=32`$, and $`k!2^{k+2}`$ tends to infinity. Since $`h`$ is nondecreasing, so is $`k_j`$. Moreover $`n_j\to\infty`$, hence $`h(n_j)\to\infty`$ and $`k_j\to\infty`$. It follows that $`M_j\mid M_{j+1}`$, every fixed $`q`$ divides all sufficiently late $`M_j=k_j!`$, and the separations $`s_j=k_j+2`$ tend to infinity. The same choice gives the size estimate: at each supported coordinate $`n`$ of the $`j`$th triple,
``` math
0\le e_n\le M_j2^{s_j}\le h(n_{j-1})\le\min(f(n),n).
```
This proves the size bound and convergence for every choice of digits.

Let $`S=\bigcup_{j\ge0}\{n_j-1,n_j,n_j+1\}`$. For any $`R`$, all but finitely many successive centres are at least $`R`$ apart. An interval of length $`H`$ therefore contains at most $`3(H/R+2)`$ points of $`S`$, in addition to a fixed finite set. The bound is uniform in the position of the interval. Divide by $`H`$, take the supremum over positions and let $`H\to\infty`$; then let $`R\to\infty`$. This proves upper Banach density zero.

*Attaining the interval.* We have now fixed the centres, moduli, digit ranges and residue corrections, but have left every digit free. Define
``` math
\beta=\sum_{j\ge0}\bigl(c_j2^{-n_j}+D_jw_j\bigr),\qquad
 F_j=\sum_{i\ge j}D_iw_i.
```
The first quantity is the contribution with all digits zero. The second is the maximum possible variable contribution from stage $`j`$ onwards. Both are finite by the bounds just proved, with $`\beta>0`$, $`F_0>0`$ and $`F_j\to0`$. The total correction is
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
Every variable sum from stage $`j`$ onwards lies in $`[0,F_j]`$; we must still show that every point of this interval is attained. A target in $`[0,F_j]`$ leaves a remainder in $`[0,F_{j+1}]`$ after choosing digit $`d`$ exactly when it belongs to
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

*The logarithmic scale.* For $`f(n)=(\log(n+3))^\varepsilon`$, we can choose the separations explicitly at the scale $`\log\log n`$. Keep the same triples and $`D_j=2^{s_j}-1`$, and now choose
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
at each coordinate $`n`$ of the triple. After enlarging the initial index, this is also at most $`n`$. The moduli remain nested, and every fixed positive integer divides all sufficiently late moduli. Summability, the congruence induction and <a href="#eq:finite-overlap" data-reference-type="eqref" data-reference="eq:finite-overlap">[eq:finite-overlap]</a> therefore apply without change. Here $`s_j\asymp_\varepsilon\log\log n_j`$, so
``` math
|S\cap[X,2X)|=O_\varepsilon(X/\log\log X).
```

Choose the same uniform starting index $`n\in[X,2X)`$ for the two blocks. A changed coordinate $`t`$ can affect only the starts $`n\in[t-m+1,t]`$, of which there are at most $`m`$. Only $`t\in S\cap[X,2X+m)`$ can occur in a sampled block. The union bound consequently gives
``` math
\begin{aligned}
 d_{\rm TV}(\mu_{a,X,m},\mu_{a+e,X,m})
 &\le\mathbb P\bigl(e_{n+i}\ne0\text{ for some }0\le i<m\bigr)\\
 &\le\frac{m|S\cap[X,2X+m)|}{X}.
 \end{aligned}
```
For $`m\le X`$, two dyadic bands cover $`[X,2X+m)`$ and give the bound $`O_\varepsilon(m/\log\log X)`$. In particular it tends to zero when $`m=o(\log\log X)`$, uniformly over the values attained, since the same set $`S`$ contains every correction support. The block length enters solely through the number of starts that one altered coordinate can affect. ◻

</div>

The coupling also applies to tests depending on the starting index. If their absolute value is bounded by $`B_0`$, their mean changes by at most $`2B_0m|S\cap[X,2X+m)|/X`$. For a function of the block alone, the bound is $`2B_0d_{\rm TV}`$. These are absolute errors: they give no relative estimate for an event whose probability tends to zero, nor a comparison of the complete infinite tails. The companion’s [Section 2](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=sparse-construction) also distinguishes upper Banach density from ordinary density.

<a id="sec:prime-application"></a>

# Application to prime gaps

The elementary bound $`p_n\le1250(n+1)^4`$ suffices for convergence of the prime and gap series. We use the central-binomial argument of Erdős \[erdos1932, pp. 194–196\]; [Appendix A of the companion](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=prime-bound) derives this bound, including the prime-power estimate. This supplies the convergence hypothesis needed to apply Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a> to the prime gaps.

Finite summation by parts gives
``` math
\sum_{i=0}^{n}\frac{p_i}{2^{i+1}}
 =2+\sum_{i=0}^{n-1}\frac{g_i}{2^{i+1}}-\frac{p_n}{2^{n+1}}.
```
The endpoint tends to zero by the polynomial bound, proving $`\Pi=2+\sum_{n\ge0}g_n2^{-(n+1)}`$. Thus rationality is unchanged by passing between the prime and gap series. Tao noted the reduction in the problem’s discussion \[erdosproblems251thread, 7 October 2025\].

<div id="res:jointcountermodel" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-251-prime-gap-dyadic-series.md#res-jointcountermodel">Lean†</a></p>

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

*Proof.* Since the gap series converges, we can apply Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a> to $`a=g`$. Choose a rational $`r`$ in its nondegenerate interval $`I`$ and put $`b=g+e`$. The proposition gives all the correction and congruence assertions, together with the comparison of growing blocks. Fix $`k`$ and a nonzero $`F\in\mathbb{Z}[x_0,\ldots,x_k]`$. A new zero can occur only in a block meeting $`S`$, so
``` math
\begin{aligned}
 &\bigl|\{n<N:F(b_n,\ldots,b_{n+k})=0\}\bigr|\\
 &\quad\le\bigl|\{n<N:F(g_n,\ldots,g_{n+k})=0\}\bigr|
       +\sum_{i=0}^k|S\cap[i,N+i)|.
 \end{aligned}
```
The first count is $`o(N)`$ by Schlage-Puchta’s Lemma 4 \[schlagepuchta2011\]; the finitely many support counts are $`o(N)`$ because $`S`$ has density zero. Only changed blocks are counted, so the values of $`F`$ need not be bounded. Since $`b`$ was chosen before $`F,k`$, the same sequence satisfies every fixed-polynomial condition.

To estimate $`P_n-p_n=\sum_{i<n}e_i`$, first observe that $`|S\cap[0,n)|=O_\varepsilon(n/\log\log n)`$. Indeed, the indices below $`\sqrt n`$ contribute at most $`\sqrt n`$ points, and on $`[\sqrt n,n)`$ we sum the dyadic support bounds, whose lengths add to $`O(n)`$ and whose $`\log\log X`$ are comparable to $`\log\log n`$. Multiplying by the pointwise correction bound gives the stated error. For $`0<\varepsilon\le1`$ this is $`o(n\log n)`$, so the prime number theorem \[mv2007, Chapter 6\] gives $`P_n\sim n\log n`$. Finally, summing nonnegative terms in the opposite order, we obtain
``` math
\sum_{n\ge0}\frac{P_n}{2^{n+1}}
 =2+\sum_{i\ge0}b_i\sum_{n>i}2^{-n-1}
 =2+\sum_{i\ge0}\frac{b_i}{2^{i+1}}=2+r\in\mathbb{Q}.
```
 ◻

</div>

For $`\varepsilon>1`$ we may use exponent $`1`$, which gives smaller corrections and the error $`O(n\log(n+3)/\log\log n)`$. Thus the conclusions extend to every $`\varepsilon>0`$. For each fixed $`y\ge2`$, eventual congruence modulo $`y!`$ also gives $`\gcd(P_n,y!)=1`$ once $`p_n>y`$. The cutoff depends on $`y`$, so this excludes no growing range of possible prime divisors. Even a prime-valued sequence of positions could omit primes.

Land’s draft \[land2026, Theorem 2\] proves conditional irrationality under a uniform Hardy–Littlewood hypothesis of the kind formulated by Kuperberg \[kuperberg2023, Conjecture 1.3\]. Ringer’s draft \[ringer2026\] obtains conditional normality. Their quantitative prime-pattern hypotheses are stronger than the absolute block comparison above and are not assumed here. The [companion’s Section 3](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=context) compares the hypotheses and sampling conventions.

<a id="verification"></a>

# Verification

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-251-prime-gap-dyadic-series.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

The [long record’s verification section](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=scope-verification) supplies the precise source correspondence and replay instructions. The perturbation theorem concerns comparison sequences; their cumulative positions need not be prime.

<a id="acknowledgements"></a>

## Acknowledgements

I thank Wouter van Doorn for advice on explaining unfamiliar hypotheses, removing unnecessary terminology, and using notation only when it helps the reader. His comments concerned an earlier note on Problem #243; this acknowledgement does not imply that he reviewed or endorsed the mathematics of the present paper. The author received no external funding and declares no competing interests. The numbering follows Bloom’s catalogue \[erdosproblems\].

<div class="thebibliography">

99

Paul Erdős, [*Sur certaines séries à valeur irrationnelle*](https://users.renyi.hu/~p_erdos/1958-19.pdf). L’Enseignement Mathématique **4** (1958), 93–100, doi:[10.5169/seals-34629](https://doi.org/10.5169/seals-34629). Paul Erdős and Ronald L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf). Monographies de L’Enseignement Mathématique, L’Enseignement Mathématique, 1980. Paul Erdős, [*On the irrationality of certain series: problems and results*](https://doi.org/10.1017/CBO9780511897184.009). New Advances in Transcendence Theory, Cambridge University Press, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). John A. Fridy, [*Generalized bases for the real numbers*](https://www.fq.math.ca/Scanned/4-3/fridy.pdf). The Fibonacci Quarterly **4** (1966), no. 3, 193–201. Vjekoslav Kovač and Terence Tao, [*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593v4). Acta Mathematica Hungarica **175** (2025), 572–608, doi:[10.1007/s10474-025-01528-0](https://doi.org/10.1007/s10474-025-01528-0); arXiv:[2406.17593v4](https://arxiv.org/abs/2406.17593v4). Statement and section numbers refer to arXiv version 4. Vivian Kuperberg, [*Sums of singular series with large sets and the tail of the distribution of primes*](https://arxiv.org/abs/2210.09775v2). The Quarterly Journal of Mathematics **74** (2023), no. 4, 1457–1479, doi:[10.1093/qmath/haad030](https://doi.org/10.1093/qmath/haad030); arXiv:[2210.09775v2](https://arxiv.org/abs/2210.09775v2). Statement numbers refer to arXiv version 2, 15 June 2023. Johan Land, [*A conditional proof of the irrationality of $`\sum_{n\ge1}p_n2^{-n}`$ under a uniform Hardy–Littlewood prime-tuples conjecture*](https://github.com/beetree/math_erdos_251). Research draft, 5 September 2026. Formalisation material accompanies the draft. Hugh L. Montgomery and Robert C. Vaughan, [*Multiplicative Number Theory I: Classical Theory*](https://doi.org/10.1017/CBO9780511618314). Cambridge Studies in Advanced Mathematics, Cambridge University Press, 2007, doi:[10.1017/CBO9780511618314](https://doi.org/10.1017/CBO9780511618314). Thomas F. Bloom, [*Erdős Problem \#251*](https://www.erdosproblems.com/251). 2026. Accessed 6 September 2026. Erdős Problems contributors, [*Erdős Problem \#251 discussion thread*](https://www.erdosproblems.com/forum/thread/251). 2026. Accessed 6 September 2026: Tao comment of 7 October 2025 and Land comments of 6 September 2026. Stefan Ringer, [*Local gap statistics, telescoping, and normality: a local-pattern approach to Erdős problem 251*](https://github.com/StefanRinger/erdos-251). Preprint, 11 September 2026. Mutable main-branch TeX consulted 16 September 2026; the cited conditional statements were rechecked 18 September 2026. Formalisation material accompanies the draft. Tonći Crmarić and Vjekoslav Kovač, [*On the irrationality of certain super-polynomially decaying series*](https://arxiv.org/abs/2504.18712v1). Colloquium Mathematicum **179** (2025), 55–68, doi:[10.4064/cm9628-5-2025](https://doi.org/10.4064/cm9628-5-2025); arXiv:[2504.18712v1](https://arxiv.org/abs/2504.18712v1). Lemma 4 is cited using arXiv version 1. Jan-Christoph Schlage-Puchta, [*The irrationality of some number theoretical series*](https://arxiv.org/abs/1105.1451v1). Acta Arithmetica **126** (2007), no. 4, 295–303, doi:[10.4064/aa126-4-1](https://doi.org/10.4064/aa126-4-1); arXiv:[1105.1451v1](https://arxiv.org/abs/1105.1451v1). Published in 2007; arXiv upload is from 2011. Lemma and preprint page locators refer to arXiv version 1. Paul Erdős, [*Beweis eines Satzes von Tschebyschef*](https://users.renyi.hu/~p_erdos/1932-01.pdf). Acta Litterarum ac Scientiarum Szeged **5** (1932), 194–198.

</div>
