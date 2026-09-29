<a id="erdos-251-prime-gap-dyadic-series"></a>

# Sparse Congruence-Preserving Perturbations of Dyadic Series

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We show that a convergent dyadic series with nonnegative integer coefficients can attain an interval of values under sparse nonnegative perturbations. One set of permitted indices works for every target, with arbitrarily slowly growing correction bounds and eventual congruences for coefficients and partial sums. For prime gaps, the construction also preserves empirical blocks of growing length and the asymptotic size of the cumulative positions. Those positions need not be prime, and the irrationality question remains open.

<a id="sec:problem"></a>

# Introduction

Let $`p_0=2,p_1=3,\ldots`$ be the primes and put $`g_n=p_{n+1}-p_n`$. Erdős asked whether
``` math
\Pi=\sum_{n\ge0}\frac{p_n}{2^{n+1}}
```
is irrational \[erdos1958, p. 94\]\[erdosgraham1980, p. 62\] \[erdos1988, p. 103\]. Summation by parts gives $`\Pi=2+\sum_{n\ge0}g_n2^{-(n+1)}`$, with convergence justified in Section <a href="#sec:parts" data-reference-type="ref" data-reference="sec:parts">4</a>. We study which properties of the gaps survive when the latter sum is changed to a prescribed value.

Our main result applies to any convergent dyadic series with nonnegative integer coefficients. We choose a sparse set of indices on which to add corrections. These indices are fixed before the target value, as are the cutoffs beyond which any prescribed modulus divides both the individual corrections and their partial sums. The possible values contain an interval. For prime gaps we can, in addition, retain the distributions of blocks of length $`o(\log\log X)`$ sampled in $`[X,2X)`$, while the cumulative positions remain asymptotic to $`n\log n`$. Thus the irrationality question for the actual primes is a distinct target: the construction supplies comparison integer sequences without ensuring that their cumulative positions are prime.

We use a standard interval-covering argument for series with finite choices. Fridy’s generalised-base lemma \[fridy1966, p. 194\] treats bounded digits and decreasing weights. Crmarić and Kovač \[crmarickovac2025, Lemma 4\] give the finite-choice form used here, and Kovač and Tao \[kovactao2024, Lemma 5.1\] use analogous intervals of reciprocal choices. In our construction the choices must also respect sparsity, positivity and cumulative congruences. We arrange this by varying two adjacent corrections whose ordinary total is fixed. For example, the pairs $`(0,6),(2,4),(4,2),(6,0)`$ at indices $`n,n+1`$ contribute $`6,8,10,12`$ divided by $`2^{n+2}`$, although each pair has total $`6`$. A correction at $`n-1`$ first fixes the cumulative residue. The proof chooses the spacing of these triples so that the later choices still cover the gaps between the current ones.

Throughout, $`\mathbb{N}=\{0,1,\ldots\}`$, intervals of indices contain integers, and $`\log`$ is natural unless a base is displayed. A set $`S\subseteq\mathbb{N}`$ has *upper Banach density zero* if
``` math
\lim_{H\to\infty}\sup_{u\in\mathbb{N}}\frac{|S\cap[u,u+H)|}{H}=0.
```
For integers $`X,m\ge1`$, let $`\mu_{a,X,m}`$ denote the distribution of $`(a_n,\ldots,a_{n+m-1})`$ when $`n`$ is uniform on $`[X,2X)`$. Blocks are unnormalised and counted with multiplicity. We use $`d_{\rm TV}(\mu,\nu)=\sup_B|\mu(B)-\nu(B)|`$.

<div id="res:sparserationalisation" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-sparserationalisation">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-sparserationalisation-comparator">Comparator</a></p>

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

The support of $`e`$ may depend on $`r`$ and occupy only part of $`S`$. Polynomially growing nonnegative integer sequences satisfy the convergence hypothesis, whereas $`a_n=2^n`$ does not. The allowance may grow as slowly as $`\log\log(n+3)`$. A bounded allowance would force every correction to vanish: a modulus exceeding the bound makes $`e`$ eventually zero, and its constant cumulative sum must then be divisible by every positive integer.

We prove the proposition in Section <a href="#sec:construction" data-reference-type="ref" data-reference="sec:construction">2</a> and apply it to prime gaps in Section <a href="#sec:prime-application" data-reference-type="ref" data-reference="sec:prime-application">3</a>. The remaining sections give the actual-tail identity and the finite separation tests that a proof of irrationality would have to establish. The [companion’s literature discussion](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=context) contains the further comparisons, including finite subsums and other dyadic coefficient sequences.

<a id="sec:construction"></a>

# Proof of Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a>

<div class="proof">

*Proof.* Choose centres $`n_j`$, $`j\ge0`$, after an initial index $`n_{-1}\ge K`$, and write $`s_j=n_j-n_{j-1}\ge4`$. We shall choose positive integers $`M_j`$ with $`M_j\mid M_{j+1}`$ and put $`D_j=2^{s_j}-1`$. At the $`j`$th triple let $`C_j`$ be the total correction before $`n_j-1`$. Starting with $`C_0=0`$, set
``` math
c_j=(-C_j)\bmod M_j\quad(0\le c_j<M_j),\qquad
 C_{j+1}=C_j+c_j+M_jD_j.
```
For a digit $`0\le d_j\le D_j`$, define
``` math
\begin{equation}
\label{eq:correction-triple}
 e_{n_j-1}=c_j,\qquad e_{n_j}=M_jd_j,\qquad
 e_{n_j+1}=M_j(D_j-d_j),
\end{equation}
```
and set $`e_n=0`$ at the other indices. The triples are disjoint and each has total $`c_j+M_jD_j`$. Consequently every $`C_j`$ and $`c_j`$ is determined before any digits are chosen. Since $`M_j\mid C_j+c_j`$, the cumulative sum is divisible by $`M_j`$ from index $`n_j`$ through the end of this triple.

Suppose that $`q\mid M_J`$. At every later triple, $`q\mid C_j`$ and $`q\mid M_j`$ imply $`q\mid c_j`$, and both entries of the pair are divisible by $`q`$. It follows by induction, including the zero entries between triples, that $`q\mid e_n`$ and $`q\mid\sum_{i<n}e_i`$ for $`n\ge n_J`$. The initial residue correction $`c_J`$ lies at $`n_J-1`$, before this cutoff. Thus it remains to choose the moduli so that every fixed $`q`$ eventually divides them, and to ensure that the weighted choices fill an interval.

For a possibly nonmonotone allowance, put
``` math
h(n)=\inf_{m\ge n}\min(f(m),m).
```
This is finite, nondecreasing and tends to infinity, with $`h(n)\le n`$. Choose $`n_{-1}`$ so that $`h(n_{-1})\ge32`$, and recursively set
``` math
k_j=\max\{k\ge2:k!2^{k+2}\le h(n_{j-1})\},\qquad
 M_j=k_j!,\qquad s_j=k_j+2,\qquad n_j=n_{j-1}+s_j.
```
The maximum exists because $`2!2^4=32`$ and factorials tend to infinity. Moreover, $`k_j`$ is nondecreasing and tends to infinity, so the required divisibility holds and $`s_j\to\infty`$. Every entry in <a href="#eq:correction-triple" data-reference-type="eqref" data-reference="eq:correction-triple">[eq:correction-triple]</a> is at most $`M_j2^{s_j}\le h(n_{j-1})`$. At a coordinate $`n`$ of this triple it is therefore at most $`f(n)`$ and at most $`n_{j-1}\le n`$. In particular all the weighted corrections are summable. Let $`S`$ be the union of the triples. For any fixed $`R`$, all but finitely many centres are at least $`R`$ apart. An interval of length $`H`$ contains at most $`3(H/R+2)`$ of their indices, apart from a fixed finite set. Taking the supremum over translates, then letting $`H\to\infty`$ and $`R\to\infty`$, proves that $`S`$ has upper Banach density zero.

Write
``` math
w_j=M_j2^{-n_j-2},\qquad
 \beta=\sum_{j\ge0}\bigl(c_j2^{-n_j}+D_jw_j\bigr),\qquad
 F_j=\sum_{i\ge j}D_iw_i.
```
The weighted correction is $`\beta+\sum_jd_jw_j`$. Here $`\beta>0`$, $`0<F_0<\infty`$ and $`F_j\to0`$, by the bounds just proved. The choice of $`D_i`$ gives
``` math
D_iw_i=M_i\bigl(2^{-n_{i-1}-2}-2^{-n_i-2}\bigr).
```
For $`i>j`$ we have $`M_i\ge M_j`$, so summing this identity and taking a limit yields the overlap inequality
``` math
\begin{equation}
\label{eq:overlap}
 F_{j+1}\ge M_j2^{-n_j-2}=w_j.
\end{equation}
```
Hence the intervals
``` math
[dw_j,dw_j+F_{j+1}],\qquad d=0,\ldots,D_j,
```
cover $`[0,F_j]`$. Given $`x\in[0,F_0]`$, we choose the digits successively so that $`x-\sum_{i=0}^jd_iw_i\in[0,F_{j+1}]`$. This remainder tends to zero, proving $`x=\sum_jd_jw_j`$. Taking $`I=(A+\beta,A+\beta+F_0)`$ proves the interval assertion. This is the finite-choice covering argument of \[crmarickovac2025, Lemma 4\]. Notice that $`S`$, $`I`$ and each cutoff $`n_J`$ were fixed before $`x`$.

For the quantitative assertion, use the same triples with the schedule
``` math
s_j=\left\lfloor\frac{\varepsilon}{2}
               \log_2\log(n_{j-1}+3)\right\rfloor,\qquad
 k_j=\max\{k\ge2:k!\le(\log(n_{j-1}+3))^{\varepsilon/4}\},
```
and again put $`M_j=k_j!`$, $`n_j=n_{j-1}+s_j`$ and $`D_j=2^{s_j}-1`$. Choose the initial index large enough that $`s_j\ge4`$ and all these choices exist. Then
``` math
M_j2^{s_j}\le(\log(n_{j-1}+3))^{3\varepsilon/4}
             \le(\log(n+3))^\varepsilon
```
at each coordinate $`n`$ of the triple. This bound is also at most $`n`$ after increasing the initial index. The summability, congruence and interval arguments therefore apply unchanged. Since $`s_j\asymp_\varepsilon\log\log n_j`$, the number of permitted indices in $`[X,2X)`$ is $`O_\varepsilon(X/\log\log X)`$.

We couple the two block distributions by choosing the same starting index. A changed coordinate belongs to at most $`m`$ of the sampled blocks, so the probability that the blocks differ is at most $`m|S\cap[X,2X+m)|/X`$. This proves the stated total variation bound. When $`m\le X`$, the interval $`[X,2X+m)`$ is contained in $`[X,4X)`$, and the support estimate on two dyadic intervals bounds the probability by $`O_\varepsilon(m/\log\log X)`$. The required uniform convergence follows. ◻

</div>

The coupling also applies to tests depending on the starting index. If their absolute value is bounded by $`B_0`$, their mean changes by at most $`2B_0m|S\cap[X,2X+m)|/X`$. For a function of the block alone, the bound is $`2B_0d_{\rm TV}`$. These are absolute errors: they give no relative estimate for an event whose probability tends to zero, nor a comparison of the complete infinite tails. The companion’s [Section 2](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=sparse-construction) also distinguishes upper Banach density from ordinary density.

<a id="sec:prime-application"></a>

# Application to prime gaps

The elementary bound $`p_n\le1250(n+1)^4`$ ensures convergence of the prime and gap series. For completeness, the central-binomial argument of Erdős \[erdos1932, pp. 194–196\] gives, for $`m\ge4`$,
``` math
4^m<m\binom{2m}{m}\le m(2m)^{\pi(2m)}.
```
The left inequality follows by induction. For the right inequality, the full power of any prime in $`\binom{2m}{m}`$ is at most $`2m`$. If $`m=(n+5)^4`$ and $`\pi(2m)\le n`$, these inequalities would give $`4^m<m(2m)^n\le4^m`$: with $`x=n+5`$, use $`x\le2^x`$ and $`n+4(n+1)x\le2x^4`$ for the last inequality. Thus $`p_n\le2(n+5)^4\le1250(n+1)^4`$. The full prime-power calculation is in [Appendix A of the companion](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=prime-bound).

<div id="res:jointcountermodel" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-jointcountermodel">Lean†</a></p>

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

*Proof.* Apply Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a> to $`a=g`$, choose a rational target $`r\in I`$, and put $`b=g+e`$. This gives the correction bounds, the eventual congruences and the comparison of growing blocks. Schlage-Puchta \[schlagepuchta2011, Lemma 4\] proved that the zero set of each fixed nonzero polynomial in a fixed block of prime gaps has density zero. A block of length $`k+1`$ changes only at a start in $`\bigcup_{i=0}^k(S-i)`$, which also has density zero. The conclusion for $`F(b_n,\ldots,b_{n+k})`$ follows, regardless of the sizes of its values.

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

<a id="sec:parts"></a>

# The prime series and its actual tails

Put $`G=\sum_{n\ge0}g_n2^{-(n+1)}`$. We now work with the actual primes and gaps throughout. The preceding polynomial bound justifies every series and limiting operation in the following identity.

<div id="res:infinite" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-infinite">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-infinite-comparator">Comparator</a></p>

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
The endpoint tends to zero. Splitting off the first term of $`T_N`$ gives its recurrence, and $`g_0=1`$ gives $`T_0=2G-1`$. ◻

</div>

Tao noted this reduction in the problem’s forum discussion \[erdosproblems251thread, 7 October 2025\].

<div id="res:irr-equivalence" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-irr-equivalence">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-irr-equivalence-comparator">Comparator</a></p>

**Corollary 4** (exact irrationality reformulation). *The prime-value dyadic series is irrational if and only if the prime-gap dyadic series is. Both series converge by the polynomial bound proved above; neither side is proved irrational.*

</div>

<div class="proof">

*Proof.* Adding the rational number $`2`$ preserves rationality and irrationality. ◻

</div>

An arbitrary solution of the tail recurrence can differ from the actual tails by $`C2^N`$. The following boundary condition removes this ambiguity.

<div id="res:true-tail" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos251/PaperCompleteR20/TrueTail.lean#L57">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-true-tail-comparator">Comparator</a></p>

**Lemma 5** (the boundary condition identifying a true tail). *Let $`\sum_{j\ge1}|a_j|2^{-j}<\infty`$ and $`U_{N+1}=2U_N-a_{N+1}`$. Then $`U_N=\sum_{j\ge1}a_{N+j}2^{-j}`$ for every $`N`$ if and only if $`2^{-N}U_N\to0`$.*

</div>

<div class="proof">

*Proof.* Iteration gives $`2^{-N}U_N=U_0-\sum_{j=1}^Na_j2^{-j}`$. The limit is zero exactly when $`U_0`$ is the full series. Subtracting its first $`N`$ terms and multiplying by $`2^N`$ then gives the tail formula. Conversely the formula implies $`2^{-N}U_N=\sum_{k>N}a_k2^{-k}\to0`$ by absolute convergence. ◻

</div>

<a id="sec:tail"></a>

## Integral shifts

Let $`U_{N+1}=2U_N-a_{N+1}`$ with $`a_n\in\mathbb{Z}`$, and write $`D_h(N)=U_{N+h}-U_N`$. Subtracting $`a_{N+1}`$ leaves fractional parts unchanged, so modulo integers the recurrence is repeated doubling. This determines integral shifts from the denominator of $`U_0`$ alone.

<div id="res:escape-irrational" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-escape-irrational">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-escape-irrational-comparator">Comparator</a></p>

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
Since $`2^N(2^h-1)\ne0`$, one integral positive-length shift forces $`U_0`$ to be rational. If $`U_0=u/(2^sd)`$ in lowest terms, multiplication by $`2^N`$ leaves denominator $`2^{\max(s-N,0)}d`$. Since $`2^h-1`$ is odd, the second relation gives the asserted divisibility criterion. Euler’s congruence supplies $`d\mid2^{\varphi(d)}-1`$ when $`d>1`$, and for $`d=1`$ we take $`h=1`$. Negating the resulting pointwise and eventual rationality criteria proves the last assertion. ◻

</div>

The theorem requires neither a true-tail boundary condition nor prime-gap coefficients. The eventual periodicity is that of fractional parts, and need not hold for the full tails. For instance, the positive even coefficients $`2,4,2,4,\ldots`$ starting at $`n=1`$ give tails $`8/3,10/3`$ alternately. Every shift of length $`1`$ is nonintegral and every shift of length $`2`$ is zero. This explains why a single shift length is insufficient.

<a id="sec:local-certificate"></a>

# Small tail differences and finite tests

Fix $`h\ge1`$ and put $`D_N=T_{N+h}-T_N`$ and $`\delta_N=g_{N+h+1}-g_{N+1}`$. Then $`D_{N+1}=2D_N-\delta_N`$, where $`\delta_N`$ is even. Two differences of absolute value less than one can both be integral only if they vanish, in which case $`\delta_N=0`$. More precisely, we have the following result.

<div id="res:signedwindow" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-signedwindow">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-signedwindow-comparator">Comparator</a></p>

**Proposition 7** (two consecutive differences of absolute value less than one). *Let $`D,D'\in\mathbb{R}`$, $`\delta\in2\mathbb{Z}`$ and $`D'=2D-\delta`$. The conditions $`|D|<1`$, $`|D'|<1`$ and $`\delta\ne0`$ hold exactly when, for some $`s\in\{-1,1\}`$,
``` math
\delta=2s,\qquad \tfrac12<sD<1.
```
In that case $`sD'\in(-1,0)`$ and both $`D`$ and $`D'`$ are nonintegral.*

</div>

<div class="proof">

*Proof.* The bounds on $`D,D'`$ imply $`-3<\delta<3`$, so a nonzero even $`\delta`$ equals $`2s`$ with $`s\in\{-1,1\}`$. Substituting in $`D'=2D-2s`$ gives $`1/2<sD<1`$. Conversely this interval gives $`sD'=2sD-2\in(-1,0)`$. ◻

</div>

For $`\delta=2`$, the endpoints $`D=1/2,1`$ give $`D'=-1,0`$ respectively. The zero triple $`D=D'=\delta=0`$ shows why the mismatch is required.

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

The problem is a sufficient condition for irrationality, by Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">6</a>. Its three conditions must hold at the same index arbitrarily late for each $`h`$. Schlage-Puchta’s lemma \[schlagepuchta2011, Lemma 4\], applied to $`x_h-x_0\pm2`$, shows that the eligible indices with $`\delta_N=\pm2`$ already have density zero. Separate infinite sets of small-difference and mismatch witnesses would therefore not suffice.

<a id="finite-separation-from-the-integers"></a>

## Finite separation from the integers

Choose a majorant $`M(n)\ge g_n`$ with $`\sum_nM(n)2^{-n}<\infty`$, and put
``` math
S_{h,N,L}=\sum_{j=1}^L(g_{N+h+j}-g_{N+j})2^{-j},\qquad
 R_{h,N,L}(M)=\sum_{j>L}(M(N+h+j)+M(N+j))2^{-j}.
```
Then $`|D_N-S_{h,N,L}|\le R_{h,N,L}(M)`$. A general real majorant need not give an effective remainder bound, but the polynomial choice below does.

<div id="res:truncation" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos251/PaperTailBoundsR7.lean#L273">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-truncation-comparator">Comparator</a></p>

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

*Proof.* The distance of $`D_N`$ from $`\mathbb{Z}`$ is at least $`\operatorname{dist}(S_{h,N,L},\mathbb{Z})-R_{h,N,L}(M)>0`$. Apply Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">6</a>. ◻

</div>

<div id="res:complete-truncation" class="remark">

*Remark 1* (what arbitrary truncation does not gain). Whenever $`|D-S_L|\le R_L\to0`$, nonintegrality of $`D`$ is equivalent to $`\operatorname{dist}(S_L,\mathbb{Z})>R_L`$ for some $`L`$. Indeed, for $`\delta=\operatorname{dist}(D,\mathbb{Z})>0`$, take $`R_L<\delta/2`$ and use the $`1`$-Lipschitz property of distance. Unrestricted depth therefore gives an exact reformulation, not an additional analytic estimate. At a prescribed logarithmic depth one must also control the margin from the integers as $`N`$ varies; a shrinking remainder alone does not do so. The companion, Appendix D.2, gives an explicit example distinguishing refinement at a fixed value from enclosures of changing values.

</div>

For an explicit test, take $`M(n)=1250(n+2)^4`$ and $`P(x)=x^4+8x^3+36x^2+104x+150`$. Summing the identity $`2P(x)=(x+1)^4+P(x+1)`$ with dyadic weights gives $`\sum_{j\ge1}(x+j)^4 2^{-j}=P(x)`$ and hence
``` math
R_{h,N,L}(M)=1250\,2^{-L}
             \bigl(P(N+h+L+2)+P(N+L+2)\bigr).
```
If $`\delta_N=2s`$ and $`|QD_N-A|\le B`$, with $`A\in\mathbb{Z}`$, $`Q>0`$, $`B\ge0`$ integers, the inequalities
``` math
2sA-Q>2B,\qquad Q-sA>B
```
put $`sD_N`$ in $`(1/2,1)`$. The numerator $`A`$ is signed. At $`h=1,N=2,L=40`$, one has $`\delta_2=g_4-g_3=-2`$ and
``` math
Q=2^{40},\qquad A=-662838684750,\qquad B=11764181250,\qquad s=-1.
```
Here $`A/Q=S_{1,2,40}`$ and $`B/Q=R_{1,2,40}(M)`$, and the two strict margins are $`202637379224`$ and $`424908761776`$. The [companion’s integer certificates](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=finite-certificates) give the prime-index calculation and remainder derivation. This finite pair leaves the quantifiers in Problem <a href="#prob:smallpair" data-reference-type="ref" data-reference="prob:smallpair">8</a> unresolved.

<a id="sec:open"></a>

# Further consequences and questions

The interval in Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a> can lie in $`(A,A+\eta)`$ for any $`\eta>0`$. Start after $`K'\ge K`$ with $`(K'+1)2^{-K'}<\eta`$ and use $`e_n\le n`$ from the proof. Then
``` math
0<\sum_ne_n2^{-(n+1)}\le(K'+1)2^{-K'}<\eta.
```
This bounds the dyadic change, without bounding the ordinary total.

<a id="sec:carry"></a>

## Nonperiodic coefficients

Rational binary expansions have eventually periodic digits in $`\{0,1\}`$. Integer coefficient sequences have more freedom, as the identity
``` math
\sum_{i=0}^{n-1}\frac{i-1}{2^{i+1}}=-\frac{n}{2^n}\longrightarrow0
```
shows. Its coefficients are unbounded, with first coefficient $`-1`$. For a positive even example, put $`c_n=2(n^2+4n+2)`$ and $`U_n=2(n+4)^2`$. We have $`U_{n+1}=2U_n-c_{n+1}`$ and $`2^{-n}U_n\to0`$, so Lemma <a href="#res:true-tail" data-reference-type="ref" data-reference="res:true-tail">5</a> yields
``` math
\sum_{j\ge1}c_j2^{-j}=32,\qquad
 \sum_{n\ge0}c_n2^{-(n+1)}=18.
```
The coefficients increase strictly and $`c_{n+1}-c_n=4n+10`$ is never $`\pm2`$. The [companion’s Section 8](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=counterexamples) gives further examples, including a bounded nonperiodic sequence in Appendix D. None of these examples constructs consecutive primes.

<div id="res:gap-nonperiodic" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L175">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md#res-gap-nonperiodic-comparator">Comparator</a></p>

**Proposition 10** (prime gaps do not become periodic). *For every positive $`h`$, the actual consecutive-prime-gap sequence is not eventually periodic with period $`h`$.*

</div>

<div class="proof">

*Proof.* An eventually periodic sequence is bounded. For each $`m\ge2`$, the $`m-1`$ consecutive integers $`m!+2,\ldots,m!+m`$ are composite, so the consecutive primes on either side have a gap of at least $`m`$. ◻

</div>

The results on bounded prime gaps \[zhang2014\], clusters of each fixed size \[maynard2015; polymath2014\], and extreme large gaps \[fgkmt2018\] leave the signed weighted-tail windows above uncontrolled. This remains so with Polymath’s bound $`\liminf_n g_n\le246`$ \[polymath2014, Theorem 1.4(i)\]. At a logarithmic truncation depth the explicit remainder tends to zero, but the finite sum must still be separated from the relevant boundary by a larger margin. For the actual prime series, nonintegral shifts are needed arbitrarily late for every positive length. Problem <a href="#prob:smallpair" data-reference-type="ref" data-reference="prob:smallpair">8</a> would supply them. The perturbation theorem concerns the insufficiency of the specified congruences and block statistics, and leaves possible arguments using primality or quantitative rare-event estimates untouched.

<a id="sec:pinned-lean-sources"></a>

# Sources and further comparisons

*Formal proofs.* A result with a kernel-checked Lean proof carries a mark in the margin. *Lean* opens the proof: the declaration itself when one declaration states the whole result, otherwise the list of declarations that together state it. *Comparator* opens the record of an independent check, in which the same statement, written again from Mathlib alone in a separate repository, was compared with our proof by Lean’s Comparator tool, allowing only the three standard axioms. A dagger on the Lean mark means that the Lean proof assumes an input named just below the result. A result without a mark has no Lean proof of its whole statement; what is checked is said below it. The [evidence record](https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-251-prime-gap-dyadic-series.md) gives every declaration, version and check. These checks show that the stated propositions are proved; whether they are the right propositions is a question the reader can settle by comparing them with the text.

The linked Lean declarations use Lean 4 \[lean4\] and mathlib \[mathlib\]. The formal proof of Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a> changes one coordinate at each stage, whereas the proof here uses triples. Both fix the permitted set, the interval and the congruence cutoffs before choosing the target. For Corollary <a href="#res:jointcountermodel" data-reference-type="ref" data-reference="res:jointcountermodel">2</a>, the formal statement covers every $`\varepsilon>0`$ and assumes Schlage-Puchta’s lemma only for nonconcentration and the prime number theorem only for the asymptotic $`P_n\sim n\log n`$. The source links record formal support for the linked statements, rather than verification of the different printed proofs. The [companion’s Appendix G](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=short-source-index) retains the complete source index at this note’s original pin, including the finite telescoping identities and their nonperiodicity consequences. Its [Section 3](../../../paper/251/erdos251-prime-gap-reasoning-surface.pdf#nameddest=context) retains the broader subsum and automatic-sequence comparisons.

<a id="acknowledgements"></a>

## Acknowledgements

I thank Wouter van Doorn for advice on explaining unfamiliar hypotheses, removing unnecessary terminology, and using notation only when it helps the reader. His comments concerned an earlier note on Problem #243; this acknowledgement does not imply that he reviewed or endorsed the mathematics of the present paper. The author received no external funding and declares no competing interests. The numbering follows Bloom’s catalogue \[erdosproblems\].

<div class="thebibliography">

99

Paul Erdős, [*Sur certaines séries à valeur irrationnelle*](https://users.renyi.hu/~p_erdos/1958-19.pdf). L’Enseignement Mathématique **4** (1958), 93–100, doi:[10.5169/seals-34629](https://doi.org/10.5169/seals-34629). Paul Erdős and Ronald L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf). Monographies de L’Enseignement Mathématique, L’Enseignement Mathématique, 1980. Paul Erdős, [*On the irrationality of certain series: problems and results*](https://doi.org/10.1017/CBO9780511897184.009). New Advances in Transcendence Theory, Cambridge University Press, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). Kevin Ford, Ben Green, Sergei Konyagin, James Maynard and Terence Tao, [*Long gaps between primes*](https://arxiv.org/abs/1412.5029v3). Journal of the American Mathematical Society **31** (2018), 65–105, doi:[10.1090/jams/876](https://doi.org/10.1090/jams/876); arXiv:[1412.5029v3](https://arxiv.org/abs/1412.5029v3). John A. Fridy, [*Generalized bases for the real numbers*](https://www.fq.math.ca/Scanned/4-3/fridy.pdf). The Fibonacci Quarterly **4** (1966), no. 3, 193–201. Vjekoslav Kovač and Terence Tao, [*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593v4). Acta Mathematica Hungarica **175** (2025), 572–608, doi:[10.1007/s10474-025-01528-0](https://doi.org/10.1007/s10474-025-01528-0); arXiv:[2406.17593v4](https://arxiv.org/abs/2406.17593v4). Statement and section numbers refer to arXiv version 4. Vivian Kuperberg, [*Sums of singular series with large sets and the tail of the distribution of primes*](https://arxiv.org/abs/2210.09775v2). The Quarterly Journal of Mathematics **74** (2023), no. 4, 1457–1479, doi:[10.1093/qmath/haad030](https://doi.org/10.1093/qmath/haad030); arXiv:[2210.09775v2](https://arxiv.org/abs/2210.09775v2). Statement numbers refer to arXiv version 2, 15 June 2023. Johan Land, [*A conditional proof of the irrationality of $`\sum_{n\ge1}p_n2^{-n}`$ under a uniform Hardy–Littlewood prime-tuples conjecture*](https://github.com/beetree/math_erdos_251). Research draft, 5 September 2026. Formalisation material accompanies the draft. Leonardo de Moura and Sebastian Ullrich, [*The Lean 4 theorem prover and programming language*](https://doi.org/10.1007/978-3-030-79876-5_37). Automated Deduction – CADE 28, Lecture Notes in Computer Science, Springer, 2021, pp. 625–635, doi:[10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37). The mathlib Community, [*The Lean mathematical library*](https://doi.org/10.1145/3372885.3373824). Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs, ACM, 2020, pp. 367–381, doi:[10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). Describes a Lean 3-era snapshot; the repository lock identifies the library used by the present Lean 4 sources. James Maynard, [*Small gaps between primes*](https://doi.org/10.4007/annals.2015.181.1.7). Annals of Mathematics **181** (2015), 383–413, doi:[10.4007/annals.2015.181.1.7](https://doi.org/10.4007/annals.2015.181.1.7). Hugh L. Montgomery and Robert C. Vaughan, [*Multiplicative Number Theory I: Classical Theory*](https://doi.org/10.1017/CBO9780511618314). Cambridge Studies in Advanced Mathematics, Cambridge University Press, 2007, doi:[10.1017/CBO9780511618314](https://doi.org/10.1017/CBO9780511618314). Yitang Zhang, [*Bounded gaps between primes*](https://doi.org/10.4007/annals.2014.179.3.7). Annals of Mathematics **179** (2014), 1121–1174, doi:[10.4007/annals.2014.179.3.7](https://doi.org/10.4007/annals.2014.179.3.7). Thomas F. Bloom, [*Erdős Problem \#251*](https://www.erdosproblems.com/251). 2026. Accessed 6 September 2026. Erdős Problems contributors, [*Erdős Problem \#251 discussion thread*](https://www.erdosproblems.com/forum/thread/251). 2026. Accessed 6 September 2026: Tao comment of 7 October 2025 and Land comments of 6 September 2026. Stefan Ringer, [*Local gap statistics, telescoping, and normality: a local-pattern approach to Erdős problem 251*](https://github.com/StefanRinger/erdos-251). Preprint, 11 September 2026. Mutable main-branch TeX consulted 16 September 2026; the cited conditional statements were rechecked 18 September 2026. Formalisation material accompanies the draft. Tonći Crmarić and Vjekoslav Kovač, [*On the irrationality of certain super-polynomially decaying series*](https://arxiv.org/abs/2504.18712v1). Colloquium Mathematicum **179** (2025), 55–68, doi:[10.4064/cm9628-5-2025](https://doi.org/10.4064/cm9628-5-2025); arXiv:[2504.18712v1](https://arxiv.org/abs/2504.18712v1). Lemma 4 is cited using arXiv version 1. Jan-Christoph Schlage-Puchta, [*The irrationality of some number theoretical series*](https://arxiv.org/abs/1105.1451v1). Acta Arithmetica **126** (2007), no. 4, 295–303, doi:[10.4064/aa126-4-1](https://doi.org/10.4064/aa126-4-1); arXiv:[1105.1451v1](https://arxiv.org/abs/1105.1451v1). Published in 2007; arXiv upload is from 2011. Lemma and preprint page locators refer to arXiv version 1. Paul Erdős, [*Beweis eines Satzes von Tschebyschef*](https://users.renyi.hu/~p_erdos/1932-01.pdf). Acta Litterarum ac Scientiarum Szeged **5** (1932), 194–198. D. H. J. Polymath, [*Variants of the Selberg sieve, and bounded intervals containing many primes*](https://arxiv.org/abs/1407.4897v4). Research in the Mathematical Sciences **1** (2014), article 12, doi:[10.1186/s40687-014-0012-7](https://doi.org/10.1186/s40687-014-0012-7); arXiv:[1407.4897v4](https://arxiv.org/abs/1407.4897v4). Theorem 1.4(i) refers to arXiv version 4 (22 December 2014); the journal numbers it Theorem 4(i). An erratum is recorded at doi:10.1186/s40687-015-0033-x.

</div>
