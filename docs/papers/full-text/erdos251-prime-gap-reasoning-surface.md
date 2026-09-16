<a id="erdos251-prime-gap-reasoning-surface"></a>

# Prime-Gap Dyadic Series: Perturbations, Exact Criteria and Certificates

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We study what information about an integer coefficient word can determine irrationality of its dyadic sum. Our main obstruction is a sparse perturbation theorem: for any summable nonnegative integer word and any $`f(n)\to\infty`$, one fixed support of upper Banach density zero realises an interval of target values using corrections eventually bounded by $`f`$, while preserving every fixed eventual congruence of coefficients and cumulative sums. Polylogarithmic corrections also preserve the empirical laws of literal blocks of length $`o(\log\log X)`$. These conclusions do not preserve primality.

For the actual zero-based primes and gaps we prove $`\Pi=\sum_{n\ge0}p_n2^{-(n+1)}=2+\sum_{n\ge0}g_n2^{-(n+1)}`$ and identify the complete tails $`T_N=\sum_{j\ge1}g_{N+j}2^{-j}`$. Their recurrence gives exact integral-shift criteria for irrationality. Joint small shifts with unequal associated gaps would suffice, but their required cofinal occurrence is not proved. Explicit countermodels separate this missing prime-specific input from growth, parity, congruence and fixed-block nonconcentration. We give exact finite window certificates and rational-denominator exclusions, distinguishing ordinary proofs, independently replayable integer computations and the statements covered by the supplied formal verification records. No unconditional irrationality result for the prime series is claimed.

<a id="long251:sec:problem"></a>

# Introduction

Throughout, the primes are indexed from zero: $`p_0=2`$, $`p_1=3`$, $`p_2=5`$, and $`g_n=p_{n+1}-p_n`$. Erdős Problem #251 concerns
``` math
\Pi=\sum_{n\ge0}\frac{p_n}{2^{n+1}}
     =2/2+3/4+5/8+7/16+\cdots,
```
with the question recorded in \[erdos1958, p. 94\], \[erdosgraham1980, p. 62\] and \[erdos1988, p. 103\]. The supplied catalogue snapshot records no unconditional solution \[erdosproblems\]; no refreshed status of the live catalogue is assumed in this revision. The first values are
``` math
\begin{array}{c|cccccccccc}
  i   & 0&1&2&3&4 &5 &6 &7 &8 &9\\\hline
  p_i & 2&3&5&7&11&13&17&19&23&29\\
  g_i & 1&2&2&4&2 &4 &2 &4 &6 &2
 \end{array}
```
so $`g_0=1`$ and every later gap is even, the primes after $`2`$ being odd. A second normalisation with denominator $`2^{\,i}`$ also occurs, and at every finite horizon it is exactly twice this one,
``` math
\sum_{i=0}^{n-1}\frac{p_i}{2^{\,i}}
 =2\sum_{i=0}^{n-1}\frac{p_i}{2^{\,i+1}} ,
```
the [factor-of-two normalisation](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L111). A factor of two does not change rationality, so no result below depends on the choice; the identity is stated so that the indexing cannot drift silently.

<a id="notation."></a>

#### Notation.

$`\mathbb{N}=\{0,1,2,\ldots\}`$ and $`\mathbb{N}_{>0}=\{1,2,\ldots\}`$. We write $`\varphi`$ for Euler’s totient function, $`\operatorname{den}q`$ for the denominator of a rational number $`q`$ written in lowest terms, $`\operatorname{dist}(x,\mathbb{Z})`$ for the distance from a real number $`x`$ to the nearest integer, and $`\operatorname{Irr}(x)`$ for the assertion that $`x`$ is irrational. A rational number is called *integral* when it is the image of an integer. A sequence $`(a_n)`$ is *eventually periodic with period $`h\ge1`$* when $`a_{n+h}=a_n`$ for every sufficiently large $`n`$. A set $`A\subseteq\mathbb{N}`$ has *density zero* when $`|A\cap[1,x]|=o(x)`$, and a property holds for *almost all* indices when its exceptional set has density zero. A sum over an empty range of indices is zero.

<a id="long251:sec:paired-corrections"></a>

# Sparse congruence-preserving perturbations

The sparse construction preserves cumulative residues as well as coefficient residues. Two adjacent corrections provide a free weighted digit while fixing their unweighted total. A third coordinate is needed to repair the cumulative residue before that pair. We account separately for its location, size and contribution to the series.

<a id="density-and-block-conventions."></a>

#### Density and block conventions.

Here $`\mathbb{N}=\{0,1,\ldots\}`$, all intervals of indices contain integers, and $`\log`$ is natural unless a base is displayed. Upper Banach density zero means
``` math
\lim_{H\to\infty}\sup_{u\in\mathbb{N}}\frac{|S\cap[u,u+H)|}{H}=0.
```
For integers $`X\ge1`$ and $`m\ge1`$, let $`\mu_{a,X,m}`$ be the empirical probability measure giving mass $`1/X`$ to each literal block $`(a_n,\ldots,a_{n+m-1})`$, $`X\le n<2X`$, with multiplicities. We use $`d_{\rm TV}(\mu,\nu)=\sup_B|\mu(B)-\nu(B)|`$; consequently tests bounded in absolute value by $`B_0`$ differ in mean by at most $`2B_0d_{\rm TV}(\mu,\nu)`$. No rescaling of the coefficients is implicit.

<div id="long251:res:sparse-rationalisation" class="theorem">

**Theorem 1** (sparse rationalisation and congruences). *Let $`a_n\in\mathbb{N}`$ and $`A=\sum_{n\ge0}a_n2^{-n-1}<\infty`$. For every cutoff $`K`$ and every $`f:\mathbb{N}\to\mathbb{R}`$ tending to infinity, there are a set $`S\subseteq[K,\infty)`$ of upper Banach density zero and a nondegenerate interval $`I\subset(A,\infty)`$ with the following property. Every $`r\in I`$ has the form
``` math
r=\sum_{n\ge0}(a_n+e_n)2^{-n-1},
```
where $`e_n\in\mathbb{N}`$ is supported on $`S`$, $`e_n\le f(n)`$ eventually, and, for every integer $`q\ge1`$, there is an $`N_q`$, chosen independently of $`r`$, such that
``` math
q\mid e_n\quad\hbox{and}\quad q\mid\sum_{i<n}e_i
 \qquad(n\ge N_q).
```
For every $`\varepsilon>0`$, the construction can instead be chosen with $`e_n\le(\log(n+3))^\varepsilon`$ eventually and $`|S\cap[X,2X)|=O_\varepsilon(X/\log\log X)`$. In that case the empirical distributions of original and corrected unnormalised blocks of length $`m(X)=o(\log\log X)`$, sampled at the same integer starts in $`[X,2X)`$, have total variation distance tending to zero, uniformly over $`r`$. Precisely the coupling error is at most $`m|S\cap[X,2X+m)|/X`$; with $`\|\Phi\|_\infty\le B_0`$ the bounded-test error is at most twice this quantity times $`B_0`$, also for tests depending on the starting index.*

</div>

The supplied index marks the general and polylogarithmic existential endpoints as `ci_checked`; precise declarations follow the proof. The printed buffered-triple witness and its schedule are an ordinary reconstruction, not the witness used by that formal development. The statement correspondence includes the target-independent support and the growing-block quantifiers; it does not identify the constructions.

<div class="proof">

*Proof.* Choose increasing centres $`n_j`$, indexed by $`j\ge0`$, together with an initial $`n_{-1}\ge K`$. Their spacings $`s_j=n_j-n_{j-1}`$ will be at least $`4`$. Let $`M_j`$ be positive integer moduli with $`M_j\mid M_{j+1}`$, and set $`D_j=2^{s_j}-1`$. These parameters will be specified below independently of all free digits.

*Place the buffer before the pair.* Set $`C_0=0`$ and recursively define the deterministic integers
``` math
c_j=(-C_j)\bmod M_j,\qquad C_{j+1}=C_j+c_j+M_jD_j.
```
For any choice $`d_j\in\{0,\ldots,D_j\}`$, put
``` math
\begin{equation}
\label{long251:eq:sparse-triple}
 e_{n_j-1}=c_j,\qquad e_{n_j}=M_jd_j,\qquad
 e_{n_j+1}=M_j(D_j-d_j),
\end{equation}
```
and put $`e_n=0`$ off these triples. The spacing makes the triples disjoint. Their total is $`c_j+M_jD_j`$, independent of $`d_j`$, so $`C_j`$ really is the cumulative correction $`C_j=\sum_{i<n_j-1}e_i`$ before its buffer, for every choice of free digits. The pair alone could not repair that cumulative residue: its total is already a multiple of $`M_j`$. The buffer does, since $`M_j\mid C_j+c_j`$.

For example, $`M=2,D=3`$ permits the pairs $`(0,6),(2,4),(4,2),(6,0)`$. Each has total $`6`$, but their weighted contributions have numerators $`6,8,10,12`$ over $`2^{n+2}`$. A preceding cumulative total $`C=1`$ needs the additional buffer $`c=1`$ at $`n-1`$; its weighted contribution is $`2^{-n}`$. This fixed contribution changes the location of the attainable interval, not its free-digit capacity.

*Check every late coordinate.* Assume that each fixed $`q`$ divides $`M_j`$ eventually, and choose $`J`$ with $`q\mid M_J`$. At index $`n_J`$, just after its buffer, the cumulative sum is divisible by $`q`$. Both entries of the pair are also divisible by $`q`$, so every later cumulative sum through that stage remains divisible by $`q`$. Inductively $`q\mid C_j`$ and $`q\mid M_j`$ imply $`q\mid c_j`$, since $`M_j\mid C_j+c_j`$. Thus every subsequent buffer, pair entry and zero entry is divisible by $`q`$, as is every intermediate cumulative sum. We may take $`N_q=n_J`$. The first buffer need not itself be divisible by $`q`$, and its coordinate $`n_J-1`$ is deliberately outside this eventual range.

*Choose a schedule for arbitrary $`f`$.* Define
``` math
h(n)=\inf_{m\ge n}\min(f(m),m).
```
This finite real number is nondecreasing in $`n`$, satisfies $`h(n)\le n`$, and tends to infinity. Choose $`n_{-1}\ge K`$ with $`h(n_{-1})\ge32`$ and recursively set
``` math
\begin{equation}
\label{long251:eq:sparse-general-schedule}
 \begin{split}
 k_j&=\max\{k\in\mathbb{N}:k\ge2,\ k!2^{k+2}\le h(n_{j-1})\},\\
 M_j&=k_j!,\qquad s_j=k_j+2,\qquad n_j=n_{j-1}+s_j.
 \end{split}
\end{equation}
```
The maximum exists: $`k=2`$ is eligible and $`k!2^{k+2}`$ tends to infinity. Since $`h`$ is nondecreasing, the integers $`k_j`$ are nondecreasing; since $`n_j\to\infty`$, they tend to infinity. The factorials form a divisibility chain and eventually contain every fixed divisor, as do the distinguished terms in \[vandoornkovac2025, Proposition 8\]. At each of the three coordinates $`n`$ in stage $`j`$,
``` math
0\le e_n\le M_j2^{s_j}\le h(n_{j-1})\le f(n),
 \qquad e_n\le n_{j-1}<n.
```
Here the buffer is smaller than $`M_j`$ and each pair entry is at most $`M_jD_j`$. Thus every correction series converges by comparison with $`\sum_n n2^{-n-1}`$.

Let $`S=\bigcup_j\{n_j-1,n_j,n_j+1\}`$. It is independent of the digits. To see upper Banach density zero, fix $`H>0`$. Outside a finite initial segment, consecutive centres are at least $`H`$ apart, since $`s_j\to\infty`$. An interval of length $`L`$ therefore meets at most $`3(L/H+2)`$ late support coordinates, plus the fixed finite number of early coordinates. Divide by $`L`$, take the supremum over interval positions, then let $`L\to\infty`$ and $`H\to\infty`$.

*Retain an interval of values.* Put $`w_j=M_j2^{-n_j-2}`$ and
``` math
F_j=\sum_{i\ge j}D_iw_i,\qquad
 \beta=\sum_{j\ge0}\bigl(c_j2^{-n_j}+D_jw_j\bigr).
```
The size estimates just proved give convergence of both series, $`F_j\to0`$, and $`F_0>0`$. The baseline $`\beta`$ is positive and independent of the digits. The complete weighted correction, including every buffer, is exactly
``` math
\begin{equation}
\label{long251:eq:sparse-baseline}
 \sum_n e_n2^{-n-1}=\beta+\sum_jd_jw_j.
\end{equation}
```
For $`i>j`$, we have $`M_i\ge M_j`$ and
``` math
D_iw_i=M_i\bigl(2^{-n_{i-1}-2}-2^{-n_i-2}\bigr)
 \ge M_j\bigl(2^{-n_{i-1}-2}-2^{-n_i-2}\bigr).
```
Telescoping over $`i=j+1,\ldots,J`$ and letting $`J\to\infty`$ yields $`F_{j+1}\ge w_j`$. This is the needed overlap condition. The intervals $`[dw_j,dw_j+F_{j+1}]`$, for $`0\le d\le D_j`$, cover $`[0,F_j]`$. For any $`y\in[0,F_0]`$, choose successive digits leaving each remainder in $`[0,F_{j+1}]`$. Since these capacities tend to zero, the resulting series has sum $`y`$. In the notation of Crmarić–Kovač \[crmarickovac2025, Lemma 4\], the finite menu $`X_j=\{0,w_j,\ldots,D_jw_j\}`$ has largest successive gap $`w_j`$ and diameter $`D_jw_j`$, so its covering condition is precisely $`w_j\le F_{j+1}`$. Fridy’s generalised-base lemma \[fridy1966, Lemma, p. 194\] and the reciprocal-menu argument in Kovač–Tao \[kovactao2024, Lemma 5.1\] are antecedents. No monotonicity of the weights is needed for the finite-menu proof. Equation <a href="#long251:eq:sparse-baseline" data-reference-type="eqref" data-reference="long251:eq:sparse-baseline">[long251:eq:sparse-baseline]</a> therefore realises every $`r`$ in the fixed interval $`I=(A+\beta,A+\beta+F_0)\subset(A,\infty)`$.

*Choose a polylogarithmic schedule.* Fix $`0<\varepsilon<1`$. Replace <a href="#long251:eq:sparse-general-schedule" data-reference-type="eqref" data-reference="long251:eq:sparse-general-schedule">[long251:eq:sparse-general-schedule]</a> by
``` math
\begin{equation}
\label{long251:eq:sparse-polylog-schedule}
 \begin{split}
 s_j&=\left\lfloor\frac{\varepsilon}{2}
          \log_2\log(n_{j-1}+3)\right\rfloor,\qquad n_j=n_{j-1}+s_j,\\
 k_j&=\max\{k\in\mathbb{N}:k\ge2,\ k!\le(\log(n_{j-1}+3))^{\varepsilon/4}\},
 \qquad M_j=k_j!.
 \end{split}
\end{equation}
```
Take the initial cutoff so large that $`s_j\ge4`$ and the maximum is nonempty from the first step. Again $`k_j`$ is nondecreasing and tends to infinity. Keep $`D_j=2^{s_j}-1`$ and the same buffer recursion. All triple entries obey
``` math
e_n\le M_j2^{s_j}\le(\log(n_{j-1}+3))^{3\varepsilon/4}
 \le(\log(n+3))^\varepsilon.
```
These polylogarithmic bounds still give convergence of $`F_j`$ and $`\beta`$. Every argument above concerning congruences and interval filling remains valid. Also $`s_j`$ is comparable, with constants depending on $`\varepsilon`$, to $`\log\log(n_{j-1}+3)`$, and $`s_j=o(n_{j-1})`$. Hence consecutive centres near $`X`$ are separated by at least a constant multiple of $`\log\log X`$, giving $`|S\cap[X,2X)|=O_\varepsilon(X/\log\log X)`$. The same estimate holds on $`[X,3X)`$.

Finally sample both length-$`m`$ blocks at the same uniform integer start in $`[X,2X)`$. They can differ only if that block meets $`S`$. Each changed coordinate belongs to at most $`m`$ such blocks, so the total variation distance is at most
``` math
\frac{m\,|S\cap[X,2X+m)|}{X}
 =O_\varepsilon\!\left(\frac{m}{\log\log X}\right).
```
For integer $`m=m(X)=o(\log\log X)`$ this tends to zero. This comparison uses the literal, unnormalised blocks and requires no limiting distribution for the original sequence. ◻

</div>

The pair identities, modular repair and conditional interval filling have formal counterparts in `SparseRationalisationCore.lean`. The supplied index marks [the arbitrary-word interval theorem](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/SparseAmbientR9.lean#L217), [its rational-target consequence](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/SparsePaperR11.lean#L53), [the polylogarithmic interval theorem](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/SparsePaperR11.lean#L78), [the block total-variation bound](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/GrowingBlocksR11.lean#L139) and [the uniform bounded-test theorem](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/GrowingBlocksR11.lean#L152) as `ci_checked`. The full existential conclusions are therefore covered by the supplied verification record. The formal construction is a one-site residue-feedback construction, not the buffered-triple schedule printed above. Agreement of theorem statements must not be confused with identity of these witnesses. There is no Comparator entry for this theorem. Applied to prime gaps, the construction makes no assertion that the corrected cumulative positions remain prime.

<div id="long251:res:local-targets" class="corollary">

**Corollary 2** (arbitrarily local target intervals). *For the arbitrary-word sparse theorem, the target interval can additionally be required to lie in $`(A,A+\eta)`$ for any prescribed $`\eta>0`$.*

</div>

<div class="proof">

*Proof.* In the general schedule, every supported entry satisfies $`e_n\le n`$. Start beyond an integer $`K'`$ with $`\sum_{n\ge K'}n2^{-(n+1)}=(K'+1)2^{-K'}<\eta`$. The complete interval of corrections has positive lower endpoint and upper endpoint at most this sum. This strengthens the location of the interval, not a claim that every number above $`A`$ is attainable under one fixed envelope. ◻

</div>

<a id="long251:sec:context"></a>

# Context and mathematical dependencies

<a id="relation-to-prior-work."></a>

#### Relation to prior work.

The passage from the primes to their gaps is already public. Tao posted on the problem’s forum thread on 7 October 2025 that summation by parts makes the question equivalent to irrationality of $`\sum_n(p_{n+1}-p_n)2^{-n}`$, and named the shape of the missing input as a sufficiently quantitative and uniform prime-tuples hypothesis giving statistical control of the binary expansion of about $`\log\log n`$ consecutive gaps \[erdosproblems251thread, comment of 7 October 2025\]. Theorem <a href="#long251:res:infinite" data-reference-type="ref" data-reference="long251:res:infinite">5</a> below is that reduction in exact form, with the endpoint retained, with convergence supplied by an elementary bound, and with the statement checked by the Lean kernel. The elementary bound replaces the prime number theorem in this reduction.

A sufficiently uniform Hardy–Littlewood hypothesis gives conditional results of a different kind. Land’s draft states conditional irrationality \[land2026, Conjecture 1, Theorem 2\]; Ringer’s draft states conditional normality in each integer base \[ringer2026\]. The authors supply formalisation material, which has not been independently rebuilt for this revision. The uniform hypothesis in \[kuperberg2023, Conjecture 1.3\] controls growing tuples, with constants chosen before the tuple and basepoint; qualitative fixed-tuple Hardy–Littlewood does not provide it.

The version of Ringer’s source consulted on 16 September 2026 separates a stopped first-point comparison from this stronger conjecture. Its averaged one-sided tuple error is sufficient, and a bounded-domination condition on first-point masses is weaker still; these are alternative sufficient inputs, not conclusions of presently invoked unconditional prime-gap results. The signs matter: both an undercount at one parity of the truncation and an overcount at the other can be adverse. An upper sieve alone therefore does not supply that averaged input. None of these conditional inputs is assumed below.

Erdős stated on p. 93 of the 1958 article that $`\sum_n p_n^{k}/n!`$ is irrational for every $`k\ge1`$, and wrote there that the proof for $`k>1`$ is complicated enough that only the case $`k=1`$ is printed \[erdos1958, pp. 93–95\]. A proof of the full family appears in Schlage-Puchta’s Theorem 3, which gives the stronger statement that $`1,S_0,S_1,S_2,\ldots`$ are linearly independent over $`\mathbb{Q}`$, where $`S_k=\sum_{n\ge1}p_n^{k}/n!`$ \[schlagepuchta2011, Theorem 3\].

On page 103 of his 1988 problem paper Erdős separately stated the fixed-denominator problem: he could not prove that $`\sum_n p_n^{k}/2^{n}`$ is irrational for every $`k\ge1`$, and wrote that the case $`k=1`$ was probably already very difficult. He also stated the variable-denominator expectation that $`\sum_{n\ge1}p_n/(g_1\cdots g_n)`$ is irrational whenever $`g_n\ge2`$ and $`g_n=o(p_n)`$ \[erdos1988, p. 103\]. That expectation is false: on 15 April 2026 Kovač posted a note, with the printed attribution ChatGPT 5.4 Pro (orchestrated by Vjeko Kovač), constructing such a sequence $`(g_n)`$ for which the sum is exactly $`1`$ \[kovac2026, Theorem 1 and proof, pp. 1–2\].

Section 3 of the 1958 article concerns variable product denominators, not the dyadic denominator sequence \[erdos1958, pp. 96–97\]. Its printed growth condition (5) uses nonstandard asymptotic typography; we do not use that condition as an operative hypothesis or silently translate it into a modern quantified statement. The simple endpoint example is unambiguous: if $`G_n=\prod_{j=1}^n(p_j+1)`$ and $`G_0=1`$, then
``` math
\frac{p_n}{G_n}=\frac1{G_{n-1}}-\frac1{G_n},\qquad
 \sum_{n\ge1}\frac{p_n}{G_n}=1.
```
Neither this variable-denominator example nor the counterexample in \[kovac2026\] addresses fixed dyadic denominators.

There is also a genuinely adjacent proved dyadic theorem. If $`P(m)`$ denotes the largest prime factor of $`m`$, Erdős and Pomerance proved that
``` math
\sum_{m\ge2}\frac{\mathbf 1_{\{P(m)>P(m+1)\}}}{2^m}
```
is irrational \[erdospomerance1978, §7, p. 320\]. Erdős and Graham record the complementary indicator on p. 62: equality of the two largest prime factors is impossible for consecutive integers, so its series is $`1/2`$ minus the displayed one and is irrational as well. That is a theorem about a bounded prime-factor comparison digit sequence, and the numerators in $`\Pi`$ are unbounded.

Two further results of Schlage-Puchta enter below. His Theorem 2 classifies rationality for numbers whose base-$`b`$ digit string concatenates the representations of a slowly growing integer sequence, and is a different object from the tail criterion here; it was already pointed at this problem in the catalogue thread on 15 April 2026. His Lemma 4 is the input this note actually uses. It states that for every polynomial $`F\in\mathbb{Z}[x_0,\ldots,x_k]`$ which does not vanish identically, $`F(g_n,\ldots,g_{n+k})\ne0`$ for almost all $`n`$, where $`g_n`$ are the actual consecutive prime gaps \[schlagepuchta2011, Lemma 4, pp. 5–6\]. Its proof runs through Selberg’s sieve. Sections <a href="#long251:sec:obstructions" data-reference-type="ref" data-reference="long251:sec:obstructions">8</a> draws two consequences from it.

Theorems <a href="#long251:res:boundedperturbation" data-reference-type="ref" data-reference="long251:res:boundedperturbation">22</a> and <a href="#long251:res:sparse-rationalisation" data-reference-type="ref" data-reference="long251:res:sparse-rationalisation">1</a> fill intervals of attainable values. The first is a binary expansion. For the second, the direct reference is Crmarić–Kovač’s finite-choice covering lemma \[crmarickovac2025, Lemma 4\]: a menu’s largest successive gap must not exceed the total remaining diameter. They apply it to product-denominator series. Our menus are $`X_j=\{0,w_j,\ldots,D_jw_j\}`$, so the hypothesis is $`w_j\le\sum_{i>j}D_iw_i`$. Fridy’s generalised-base lemma \[fridy1966, Lemma, p. 194\] is an antecedent with nonincreasing weights; the finite-menu form avoids that additional assumption. Kovač–Tao use reciprocal menus \[kovactao2024, Lemma 5.1, Theorem 2.5\], while van Doorn–Kovač combine filling with a divisibility chain absorbing every integer \[vandoornkovac2025, Lemma 7, Proposition 8\]. Our factorial moduli use the latter absorption property to preserve eventual congruences.

A further comparison is van Doorn’s exchange $`\{21d,28d\}\leftrightarrow\{20d,30d\}`$: both reciprocal sums are $`1/(12d)`$, while the ordinary sums are $`49d`$ and $`50d`$ \[vandoorn2025, proof of Theorem 3\]. Our paired corrections preserve the ordinary sum and vary the dyadic contribution instead. This is an analogy between conserved quantities, not an application of his partition theorem. We claim no new interval-covering principle.

Binary achievement sets require care beyond these covering inequalities. Bartoszewicz–Filipczak–Szymonik use a central run of attainable integer block sums to obtain interior in a multigeometric family \[bartoszewicz2014, Theorem 2\]. Prus-Wiśniowski–Ptak construct Cantorvals for which the overlap indices $`\{n:a_n\le\sum_{i>n}a_i\}`$ have density zero \[prusptak2024, Theorem\]. Thus neither occasional separated cylinders nor failure of an eventual term-versus-tail alternative alone decides interior. The survey \[glabprus2025, §1\] records the surrounding classification. Our variable-digit proof verifies covering at every stage and does not depend on a classification theorem for binary subsums. Nitecki’s preprint \[nitecki2015, Theorem 14\] gives an exposition explicitly crediting the Guthrie–Nymann classification; its title and numbering differ from the published Monthly article.

The inequality pattern alone is insufficient even when its index set is specified exactly: Marchwicki–Miska’s construction \[marchwickimiska2021, Theorem 2.1\], with the repaired proof in \[miskaprusptak2023\], can realise any infinite strict term-dominating index set with a Cantor achievement set. The repair preserves the original uniqueness conclusion; the latter paper also gives a simpler proof of a weaker statement without uniqueness. Nowakowski’s Star Procedure \[nowakowski2025, Definition 2, Theorem 3.1\] is a different sufficient route to a Cantorval, requiring every stage of a positivity recursion. None of these results is asserted to settle the prescribed factorial binary family in the separate working note.

<a id="automatic-sequences-and-the-limit-of-the-analogy."></a>

#### Automatic sequences and the limit of the analogy.

Adamczewski–Drmota–Müllner prove computable logarithmic densities for fixed automatic sequences along primes, and give criteria for natural densities and their rationality \[adm2022, Theorems 1.2, 1.4\]. The general logarithmic densities are not all rational. The fixed finite-alphabet automaton is essential: the result is not a theorem about unbounded consecutive prime gaps, their complete dyadic tails, or a growing family of residue or carry automata. Any such application would have to specify the automaton, prove that it computes the required observable, and supply uniform errors as its state space grows. We do not infer any of those steps from the density theorem.

<a id="the-uniformity-required-from-prime-statistics."></a>

#### The uniformity required from prime statistics.

Kuperberg’s large-set singular-series estimates allow a specified growing cardinality, not arbitrary dimension \[kuperberg2023, Theorem 1.1\]. Her arithmetic-progression and smooth-weight estimates are a useful fixed-parameter comparison \[kuperbergweighted2025\]; they do not by themselves give a law for ordered consecutive-gap blocks. Jha’s revised Poisson-tail preprint \[jha2026\] concerns growing short-interval prime counts under a strong Hardy–Littlewood hypothesis. Counting primes in an interval and controlling the joint position-weighted gap-tail observable are different tasks. No growing-window estimate needed below is claimed to follow merely from these related titles or from a fixed-dimensional limit theorem.

Problem #251 also appears as the unproved declaration `erdos_251` in the *Formal Conjectures* repository \[formalconjectures251\]. Its zero-based Lean sum starts with the zeroth prime over $`2^0`$, so it is twice the displayed normalisation and has equivalent irrationality status; its proof is `sorry`.

<a id="the-strategy."></a>

#### The strategy.

The digits $`p_n`$ grow, so the series is not a digit expansion in any bounded alphabet, and the standard rationality criteria for such expansions do not apply directly. The classical elementary criteria for series of this kind instead control irrationality through the growth of the denominators. Erdős and Straus named a sum $`\sum_k 1/a_k`$ over a strictly increasing sequence of positive integers an *Ahmes series* \[erdosstraus1963\]; for such a series the condition $`a_k^{1/2^k}\to\infty`$ is sufficient for irrationality, and it is sharp, since shifted Sylvester sequences grow like $`C^{2^{k}}`$ for arbitrarily large $`C`$ and have rational reciprocal sum. Both statements and their attribution are recorded in the introduction of Kovač and Tao \[kovactao2024, §1\]. Splitting each term $`p_i/2^{\,i+1}`$ into $`p_i`$ copies of $`2^{-(i+1)}`$ writes $`\Pi`$ as a sum of unit fractions with repetitions, and the denominators occurring in it are exactly the powers of two. Even ignoring the repetitions the growth hypothesis fails by every available margin, since $`(2^{\,n})^{1/2^{\,n}}\to1`$, and every arithmetic constraint has to come from the numerators instead.

What replaces growth control is denominator control on the sequence of rescaled tails. Rationality of the sum is equivalent to an eventual integrality condition on differences of those tails, and that condition uses nothing about the numerators beyond the fact that they are integers. The condition does not by itself force the numerators to repeat: Proposition <a href="#long251:res:telescope" data-reference-type="ref" data-reference="long251:res:telescope">31</a>, applied to $`K_n=n`$, produces the integer sequence $`\kappa_n=n-1`$, which is unbounded and hence not eventually periodic, and whose dyadic sum is zero.

<a id="dependencies-and-reading-routes."></a>

#### Dependencies and reading routes.

The sparse theorem is independent of primes: modular repair and finite-menu covering give the interval, and counting changed starts gives its statistical consequences. Schlage-Puchta’s lemma and the prime number theorem enter only the prime-anchored joint corollary. The recurrence classification needs integer digits and Euler’s congruence, not any prime-tuple conjecture. The one-tail certificate adds an explicit majorant and exact finite prime data. Irrationality would require the additional cofinal prime-gap input in Section <a href="#long251:sec:open" data-reference-type="ref" data-reference="long251:sec:open">10</a>. The appendices give the finite certificates, complete moved statements and source concordance. The accompanying statement-destination table preserves the original short-note labels at these locations.

<a id="long251:sec:parts"></a>

# Summation by parts, with the endpoint retained

Summation by parts trades a sequence for its consecutive differences. The form recorded here is exact: it carries no error term, it assumes nothing about the sequence, and it retains the endpoint term. No endpoint is absorbed into an estimate. For a sequence $`P`$ of rational numbers and $`n\ge0`$ put
``` math
D(P,n)=\sum_{i=0}^{n-1}\frac{P(i)}{2^{\,i+1}},
 \qquad
 \Delta(P,n)=\sum_{i=0}^{n-1}\frac{P(i+1)-P(i)}{2^{\,i+1}} ,
```
both empty, hence zero, at $`n=0`$. We call these the [dyadic partial sum](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L101) and the [dyadic difference sum](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L121) of $`P`$.

<div id="long251:res:abel" class="proposition">

**Proposition 3** (finite summation by parts). *For every rational sequence $`P`$ and every $`n\ge0`$,
``` math
D(P,n+1)=P(0)+\Delta(P,n)-\frac{P(n)}{2^{\,n+1}} .
```*

</div>

<div class="proof">

*Proof.* A routine induction on $`n`$. At $`n=0`$ both sides equal $`P(0)/2`$. For the step, adding $`P(n+1)/2^{\,n+2}`$ to the left and $`\bigl(P(n+1)-P(n)\bigr)/2^{\,n+1}`$ to the difference sum changes the endpoint term from $`P(n)/2^{\,n+1}`$ to $`P(n+1)/2^{\,n+2}`$, and the two adjustments agree. ◻

</div>

Formalised as the [summation-by-parts identity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L138). Nothing is assumed about $`P`$: no positivity, no monotonicity, and no convergence.

Specialising to $`P(i)=p_i`$, whose first value is $`p_0=2`$, and writing $`g_i=p_{i+1}-p_i`$ for the zero-based gaps, gives the reformulation.

<div id="long251:res:parts" class="theorem">

**Theorem 4** (prime-gap reformulation). *Let $`p_0=2,p_1=3,\ldots`$ be the primes in increasing order and $`g_i=p_{i+1}-p_i`$. For every $`n\ge0`$,
``` math
\sum_{i=0}^{n}\frac{p_i}{2^{\,i+1}}
 =2+\sum_{i=0}^{n-1}\frac{g_i}{2^{\,i+1}}-\frac{p_n}{2^{\,n+1}} .
```*

</div>

Formalised as the [prime-gap summation by parts](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L172), using the [gap partial sum](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L161) and the [gap cast identity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L156); the latter records that the natural-number difference $`p_{n+1}-p_n`$ agrees with the difference taken in $`\mathbb{Q}`$, which needs $`p_n\le p_{n+1}`$, the [monotonicity step](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L152). The leading $`2`$ is the first prime, not a normalising constant. At $`n=2`$, for instance, the left side is $`2/2+3/4+5/8=19/8`$ and the right side is $`2+(1/2+2/4)-5/8=19/8`$.

<a id="long251:sec:infinite"></a>

## The infinite identity and the irrationality equivalence

Write
``` math
u_n=\frac{p_n}{2^{\,n+1}},\qquad
 v_n=\frac{g_n}{2^{\,n+1}}
```
for the terms of the prime series and of the gap series, so that $`\sum_{n\ge0}u_n=\Pi`$. The termwise identity $`v_n=2u_{n+1}-u_n`$ is the [dyadic discrete derivative](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L202). It expresses each gap term as an integer combination of two consecutive prime terms, so once $`(u_n)`$ is summable the gap series can be summed by rearranging two copies of the prime series.

<div id="long251:res:infinite" class="theorem">

**Theorem 5** (infinite prime-gap identity). *Both series converge and
``` math
\sum_{n\ge0}\frac{p_n}{2^{\,n+1}}
 \;=\;2+\sum_{n\ge0}\frac{g_n}{2^{\,n+1}} .
```*

</div>

<div class="proof">

*Proof.* The bound $`p_n\le1250(n+1)^4`$ of Appendix <a href="#long251:app:prime-bound" data-reference-type="ref" data-reference="long251:app:prime-bound">11</a> makes $`(u_n)`$ summable, and $`0<g_n\le p_{n+1}`$ then makes $`(v_n)`$ summable. The shifted sequence $`(u_{n+1})`$ is summable, so summing $`v_n=2u_{n+1}-u_n`$ and using $`u_0=1`$ gives
``` math
\sum_{n\ge0}v_n
 =2\left(\sum_{n\ge0}u_n-u_0\right)-\sum_{n\ge0}u_n
 =\sum_{n\ge0}u_n-2 . \qedhere
```
 ◻

</div>

The polynomial bound is [checked here](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L360), summability of the prime series [here](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L379), the summability transfer is the [gap-series summability theorem](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L385), and the displayed identity is the [unconditional prime-gap identity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L427). The prime number theorem is needed neither for this convergence nor for the identity; it enters later through $`p_n\sim n\log n`$ in Corollary <a href="#long251:res:nonconc-primes" data-reference-type="ref" data-reference="long251:res:nonconc-primes">25</a> and in the state-compression argument \[mv2007, Chapter 6\].

<div id="long251:res:irr-equivalence" class="corollary">

**Corollary 6** (exact irrationality reformulation). *<span id="res:irr-equivalence" label="res:irr-equivalence"></span> $`\Pi`$ is irrational if and only if $`S=\sum_{n\ge0}g_n2^{-(n+1)}`$ is irrational. The corresponding zero-based series with denominator $`2^n`$ equals $`4+2S`$ and has the same irrationality status.*

</div>

These are the [normalised irrationality equivalence](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L435), the [displayed-series identity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L444), and the [displayed-series irrationality equivalence](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L459). Concretely, $`\Pi=3.674643966\ldots`$ is irrational if and only if $`S=1.674643966\ldots`$ is, and neither is known.

<a id="long251:sec:tail"></a>

# The tail recurrence and the exact criteria

The series is not attacked directly. Suppose $`\sum_{i\ge0}a_i2^{-(i+1)}`$ converges with every $`a_i`$ an integer, and rescale its tails by putting
``` math
T_N=2^{\,N+1}\sum_{i>N}\frac{a_i}{2^{\,i+1}}
    =\sum_{j\ge1}\frac{a_{N+j}}{2^{\,j}} .
```
Two facts follow immediately. First $`T_{N+1}=2T_N-a_{N+1}`$, so moving one level along doubles the rescaled tail and subtracts a single coefficient. Second $`T_0=2\sum_{i\ge0}a_i2^{-(i+1)}-a_0`$, so the sum is rational exactly when $`T_0`$ is. This section studies that recurrence, assuming nothing about the coefficients beyond the fact that they are integers, and resumes the prime-gap instance at the end.

<div id="long251:def:rec" class="definition">

**Definition 7**. Let $`g:\mathbb{N}\to\mathbb{Z}`$ and $`T:\mathbb{N}\to\mathbb{Q}`$ or $`T:\mathbb{N}\to\mathbb{R}`$. Say $`T`$ satisfies the *dyadic tail recurrence* with *digits* $`g`$ when $`T_{N+1}=2T_N-g_{N+1}`$ for every $`N`$. Write $`\sigma_h(N)=T_{N+h}-T_N`$ for the *shift* of length $`h`$ at $`N`$, and call a rational number *integral* when it is the image of an integer.

</div>

These are the [tail recurrence](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L482), the [shift](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L544), and [integrality](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L575). One small orbit is worth having in view. Take every digit $`g_N=0`$ and $`T_0=1/12`$. Then the orbit is $`\tfrac1{12},\tfrac16,\tfrac13,\tfrac23,\tfrac43,\ldots`$ and $`\sigma_h(N)=(2^{h}-1)2^{\,N}/12`$. The shift of length $`2`$ is not integral at $`N=0`$ and is integral at $`N=2`$; the shift of length $`1`$ is never integral. Nonintegrality at one prescribed shift length therefore does not imply irrationality.

Iterating the recurrence $`h`$ times multiplies $`T_N`$ by $`2^{h}`$ and accumulates an explicit integer. Define $`B_{0,N}=0`$ and $`B_{h+1,N}=2B_{h,N}+g_{N+h+1}`$, so that $`B_{h,N}=g_{N+1}2^{\,h-1}+\cdots+g_{N+h}`$: the [tail block](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L647).

<div id="long251:res:block" class="theorem">

**Theorem 8** (block identity). *For every $`N`$ and $`h`$,
``` math
T_{N+h}=2^{h}T_N-B_{h,N},
 \qquad\text{hence}\qquad
 \sigma_h(N)=(2^{h}-1)\,T_N-B_{h,N} .
```*

</div>

<div class="proof">

*Proof.* A routine induction on $`h`$; the step is one application of the recurrence together with the recursion defining $`B`$. The second identity is the first minus $`T_N`$. ◻

</div>

Formalised as the [iterated block identity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L653) and the [scaled shift identity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L667). The shift also obeys the recurrence in its own right,
``` math
\begin{equation}
\label{long251:eq:shift-step}
 \sigma_h(N+1)=2\sigma_h(N)-\bigl(g_{N+h+1}-g_{N+1}\bigr),
\end{equation}
```
the [shift step identity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L563). Since $`B_{h,N}`$ is an integer, Theorem <a href="#long251:res:block" data-reference-type="ref" data-reference="long251:res:block">8</a> converts a question about the shift into a question about $`(2^{h}-1)T_N`$: the shift $`\sigma_h(N)`$ is integral if and only if $`(2^{h}-1)T_N`$ is, the [integral-shift criterion](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L802). The criterion holds in both directions, so once $`T_N`$ is fixed no choice of the digits after index $`N`$ can change whether $`\sigma_h(N)`$ is an integer.

For a rational orbit the denominator settles the matter exactly:
``` math
\begin{equation}
 \operatorname{den}(T_{N+1})
 =\frac{\operatorname{den}(T_N)}{\gcd(2,\operatorname{den}(T_N))},
 \qquad
 \sigma_h(N)\in\mathbb{Z}
 \iff
 \operatorname{den}(T_N)\mid 2^h-1 .
\label{long251:eq:den-law}\ltx@label{eq:shift-denominator}\ltx@label{res:shiftiff}
\end{equation}
```
Each even denominator loses exactly one factor of $`2`$ and an odd denominator is unchanged, so after finitely many steps the denominator is an odd integer $`d`$; Euler’s congruence then gives $`d\mid2^{\varphi(d)}-1`$, and the multiplicative order of $`2`$ modulo $`d`$ is the least such exponent. These are the [denominator recurrence](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1217), its [odd case](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1226) and [even case](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1236), the [denominator classification](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1279), the [totient shift](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L877), and the [propagation of an integral shift to every later index](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L900). The hypothesis that $`d`$ is odd cannot be dropped: if $`T_N=1/2`$ then $`2^{h}-1`$ is odd for every $`h\ge1`$, so no shift at $`N`$ is integral.

<div id="long251:res:escape-irrational" class="theorem">

**Theorem 9** (exact rationality classification). *Let $`T:\mathbb{N}\to\mathbb{R}`$ satisfy $`T_{N+1}=2T_N-g_{N+1}`$ with integer digits $`g`$. The following are equivalent:*

1.  *$`T_0`$ is rational;*

2.  *$`\sigma_h(N)`$ is an integer for some $`h\ge1`$ and some $`N`$;*

3.  *for some fixed $`h\ge1`$, $`\sigma_h(N)`$ is an integer at every sufficiently large $`N`$.*

*Consequently $`T_0`$ is irrational if and only if every positive-length shift is nonintegral at every index, equivalently if and only if for every $`h\ge1`$ and every cutoff some later $`N`$ has $`\sigma_h(N)\notin\mathbb{Z}`$.*

</div>

<div class="proof">

*Proof.* For <span class="upright">(i)</span>$`\Rightarrow`$<span class="upright">(iii)</span>, the block identity identifies the whole orbit with a rational recurrence starting at $`T_0`$; apply <a href="#long251:eq:den-law" data-reference-type="eqref" data-reference="long251:eq:den-law">[long251:eq:den-law]</a> at an index where the denominator has become odd, and propagate forward. The implication <span class="upright">(iii)</span>$`\Rightarrow`$<span class="upright">(ii)</span> is immediate. For <span class="upright">(ii)</span>$`\Rightarrow`$<span class="upright">(i)</span>, the block identity gives $`\sigma_h(N)=(2^h-1)T_N-B_{h,N}`$ with $`B_{h,N}`$ and $`\sigma_h(N)`$ integers and $`2^h-1\ne0`$, so $`T_N`$ is rational, and $`T_N=2^NT_0-B_{N,0}`$ then makes $`T_0`$ rational. Negating the three conditions gives the two irrationality formulations. ◻

</div>

The exact real classifiers are [one integral positive shift](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1479), [eventual integrality](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1525), [pointwise nonintegrality](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1551), and [cofinal nonintegrality](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1572).

<div id="long251:res:true-tail" class="lemma">

**Lemma 10** (the boundary condition identifying a true tail). *Let $`a_1,a_2,\ldots`$ be real numbers with $`\sum_{j\ge1}|a_j|2^{-j}<\infty`$, and let $`U_{N+1}=2U_N-a_{N+1}`$. Then
``` math
U_N=\sum_{j\ge1}a_{N+j}2^{-j}\quad\hbox{for every }N
 \quad\Longleftrightarrow\quad 2^{-N}U_N\longrightarrow0.
```*

</div>

<div class="proof">

*Proof.* Iteration gives $`2^{-N}U_N=U_0-\sum_{j=1}^{N}a_j2^{-j}`$. The limit is zero exactly when $`U_0`$ equals the full series; subtracting its first $`N`$ terms then gives the claimed tail formula. In particular, the recurrence alone leaves the homogeneous freedom $`C2^N`$. ◻

</div>

<a id="the-actual-prime-gap-orbit."></a>

#### The actual prime-gap orbit.

Put
``` math
T_N=\sum_{j\ge1}\frac{g_{N+j}}{2^{\,j}},
```
which converges by Theorem <a href="#long251:res:infinite" data-reference-type="ref" data-reference="long251:res:infinite">5</a>. The scaled tail equals its shifted-gap series, the [shifted-gap series identity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L31), and satisfies $`T_{N+1}=2T_N-g_{N+1}`$ with no rationality hypothesis, the [real tail recurrence](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L48). Since $`T_0=2S-1=2.349287932\ldots`$, the numbers $`\Pi`$, $`S`$ and $`T_0`$ have the same rationality status, and Theorem <a href="#long251:res:escape-irrational" data-reference-type="ref" data-reference="long251:res:escape-irrational">9</a> specialises to the actual series: irrationality of $`\Pi`$ is equivalent to cofinal nonintegrality of the positive shifts of $`T`$, the [escape equivalence](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L73). Nothing about the bridge from the series to its actual tail is left open; the open content is the escape hypothesis itself.

<a id="long251:sec:freepair"></a>

## The free-pair criterion and the lcm diagonal

The escape condition quantifies over a fixed shift length. Freeing the offset gives an equivalent condition with a weaker-looking producer.

<div id="long251:res:freepair" class="theorem">

**Theorem 11** (free-pair criterion). *$`S`$ is irrational if and only if for every $`t\ge1`$ and every $`N_0`$ there are $`N,M\ge N_0`$ with $`M\equiv N\pmod t`$ and $`T_M-T_N\notin\mathbb{Z}`$.*

</div>

<div class="proof">

*Proof.* If $`S`$ is irrational, take $`M=N+t`$ for the $`N`$ supplied by Theorem <a href="#long251:res:escape-irrational" data-reference-type="ref" data-reference="long251:res:escape-irrational">9</a> at shift length $`t`$. Conversely, suppose $`S`$ is rational. By <a href="#long251:eq:den-law" data-reference-type="eqref" data-reference="long251:eq:den-law">[long251:eq:den-law]</a> the orbit reaches an index $`N_0`$ beyond which the reduced denominator is a fixed odd $`d`$; let $`t`$ be the multiplicative order of $`2`$ modulo $`d`$. For $`N,M\ge N_0`$ with $`M\equiv N`$ modulo $`t`$, the difference $`T_M-T_N`$ is then an integer, contradicting the stated property at this $`t`$ and this cutoff. ◻

</div>

The offset $`M-N`$ is free, so one nonintegral congruent pair for each modulus and each cutoff suffices in place of a supply at a single fixed offset. The mechanism is exact: beyond a rational state with odd reduced denominator $`d`$, the difference $`T_M-T_N`$ is integral precisely when $`M\equiv N`$ modulo the order of $`2`$ in $`\mathbb{Z}/d\mathbb{Z}`$, the [free-pair lattice](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/FreePairReduction.lean#L92), so every rational orbit has a cutoff and a modulus at which integrality holds exactly on the congruence classes, the [lattice corollary](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/FreePairReduction.lean#L105). The criterion for the actual series is checked as the [free-pair equivalence](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/FreePairReduction.lean#L236), over the [actual real tail recurrence](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/FreePairReduction.lean#L186). The mechanism is elementary: modulo one the tail recurrence is multiplication by two, and integrality of $`T_M-T_N`$ beyond a rational state is governed by the multiplicative order of $`2`$ modulo the odd reduced denominator.

The criterion rules out two shortcuts. For the actual prime-gap tail, Section <a href="#long251:sec:xr-compression" data-reference-type="ref" data-reference="long251:sec:xr-compression">14.4</a> combines the prime number theorem with a first-moment bound to show that, under rationality, some tail value occurs $`\gg_{C,d}X/\log X`$ times in $`(X,2X]`$; here $`d`$ is the eventual odd reduced denominator and $`C>1`$ is fixed. This is specific to the prime tail, rather than a consequence of rationality for arbitrary integer-digit orbits, and equal tails have integral difference, so they do not supply the free-pair producer. Also, under the free-pair lattice the difference is an integer whenever the modulus divides the offset, and an integer cannot lie in $`(\tfrac12,1)`$, so the window component of the reduced event below is already a contradiction on its own. Both derivations are ordinary proofs, recorded in the extended record and not formalised.

A second exact reformulation collapses all shift lengths and basepoints onto a single schedule. Let $`L_0=1`$ and $`L_j=\operatorname{lcm}(1,\ldots,j)`$.

<div id="long251:res:lcmdiagonal" class="theorem">

**Theorem 12** ([lcm-diagonal criterion](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/OrderLatticeDiagonal.lean#L153)). *Let $`g:\mathbb{N}\to\mathbb{Z}`$ and $`T:\mathbb{N}\to\mathbb{R}`$ satisfy $`T_{N+1}=2T_N-g_{N+1}`$. Then $`T_0`$ is irrational if and only if $`T_{2L_j}-T_{L_j}\notin\mathbb{Z}`$ for every $`j\ge0`$.*

</div>

<div class="proof">

*Proof.* Theorem <a href="#long251:res:escape-irrational" data-reference-type="ref" data-reference="long251:res:escape-irrational">9</a> gives the forward implication. Conversely, if $`T_0`$ is rational then some positive shift length $`h`$ is integral at every basepoint beyond an index $`N_0`$. Choose $`j`$ so large that $`N_0\le L_j`$ and $`h\mid L_j`$. The cocycle identity $`\sigma_{a+b}(N)=\sigma_a(N)+\sigma_b(N+a)`$ shows by induction that every positive multiple of $`h`$ is integral at every such basepoint, so $`T_{2L_j}-T_{L_j}`$ is an integer. ◻

</div>

The factorial schedule has the same divisibility property; the lcm schedule is pointwise no larger and is the endpoint used here. Theorems <a href="#long251:res:freepair" data-reference-type="ref" data-reference="long251:res:freepair">11</a> and <a href="#long251:res:lcmdiagonal" data-reference-type="ref" data-reference="long251:res:lcmdiagonal">12</a> are exact reformulations on the class of integer-digit orbits. They change the shape of the required producer and they supply no nonintegrality statement for the actual prime gaps.

<a id="long251:sec:local-certificate"></a>

# A local certificate, and one actual pair

The classifiers reduce irrationality to a condition of infinite precision imposed on a complete tail. Inside $`(-1,1)`$ integrality is equality with zero, so on that range the shift step identity <a href="#long251:eq:shift-step" data-reference-type="eqref" data-reference="long251:eq:shift-step">[long251:eq:shift-step]</a> turns simultaneous integrality of two adjacent shifts into a single comparison of digits. What this buys is a certificate attached to one pair of adjacent indices, whose verification already contradicts integrality there. The distance of a shift from the integers never has to be estimated.

<div id="long251:res:smallpair" class="theorem">

**Theorem 13** (adjacent small-shift obstruction). *Let $`T`$ satisfy the dyadic tail recurrence with integer digits $`g`$, and fix $`h`$ and $`N`$. If
``` math
-1<\sigma_h(N)<1,\qquad -1<\sigma_h(N+1)<1,
 \qquad g_{N+h+1}\ne g_{N+1},
```
then $`\sigma_h(N)`$ and $`\sigma_h(N+1)`$ cannot both be integers. Consequently, if such a pair occurs beyond every threshold, the $`h`$-shift is not eventually integral.*

</div>

<div class="proof">

*Proof.* An integer strictly between $`-1`$ and $`1`$ is zero. If both shifts were integers, both would vanish, and <a href="#long251:eq:shift-step" data-reference-type="eqref" data-reference="long251:eq:shift-step">[long251:eq:shift-step]</a> would give $`g_{N+h+1}=g_{N+1}`$. The cofinal statement chooses one such adjacent pair after the alleged onset of integrality. ◻

</div>

<div id="long251:res:smallpair-real" class="corollary">

**Corollary 14** (real form and the sufficient condition). *The same statement holds for a real orbit, with the same proof. If for every $`h\ge1`$ and every cutoff some later $`N`$ satisfies the three displayed conditions for the actual prime gaps, then $`\Pi`$ is irrational.*

</div>

The rational finite contradiction is the [adjacent small-shift obstruction](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L979) with its [cofinal form](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1006); the real form is the [real adjacent-pair consumer](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L99), and the implication to irrationality of the actual series is the [small-mismatch criterion](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L120). The third hypothesis alone is available for the actual gaps: it reads $`g_4=2\ne4=g_3`$ at $`h=1`$, $`N=2`$, and by Proposition <a href="#long251:res:gap-nonperiodic" data-reference-type="ref" data-reference="long251:res:gap-nonperiodic">15</a> it holds for arbitrarily large $`N`$ at every fixed $`h`$. What is missing is the pair of inequalities, each of which constrains a complete infinite tail.

<div id="long251:res:gap-nonperiodic" class="proposition">

**Proposition 15** (prime gaps do not become periodic). *<span id="res:gap-nonperiodic" label="res:gap-nonperiodic"></span> For every positive $`h`$, the actual consecutive-prime-gap sequence is not eventually periodic with period $`h`$.*

</div>

<div class="proof">

*Proof.* For $`m\ge2`$ the integers $`(m+1)!+2,\ldots,(m+1)!+m+1`$ are composite, so the gaps are unbounded. An eventually periodic sequence of natural numbers has finite range after its preperiod and a bounded initial segment, hence is bounded. ◻

</div>

Lean checks the factorial argument as [unboundedness of the actual gaps](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L57) and the conclusion as [non-eventual periodicity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1023). Far stronger lower bounds for large gaps are known \[fgkmt2018, Theorem 1\]; unboundedness is all that is needed.

The conjunction in Theorem <a href="#long251:res:smallpair" data-reference-type="ref" data-reference="long251:res:smallpair">13</a> has an exact normal form. For fixed $`h`$ write $`D_N=\sigma_h(N)`$ and $`\delta_N=g_{N+h+1}-g_{N+1}`$, so that $`D_{N+1}=2D_N-\delta_N`$.

<div id="long251:res:signedwindow" class="theorem">

**Theorem 16** ([signed two-window normal form](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/AffineShiftEscape.lean#L113)). *Assume $`\delta_N`$ is even. The conjunction $`-1<D_N<1`$, $`-1<D_{N+1}<1`$, $`\delta_N\ne0`$ is equivalent to
``` math
\bigl(\delta_N=2\ \hbox{ and }\tfrac12<D_N<1\bigr)
 \quad\hbox{or}\quad
 \bigl(\delta_N=-2\ \hbox{ and }-1<D_N<-\tfrac12\bigr).
```*

</div>

<div class="proof">

*Proof.* The recurrence and the two unit windows give $`-3<\delta_N<3`$. A nonzero even integer in that interval is $`2`$ or $`-2`$. Substitution into $`D_{N+1}=2D_N-\delta_N`$ gives the stated half-window and, in the reverse direction, recovers the second unit window. ◻

</div>

For the actual gaps and $`N\ge1`$ every $`\delta_N`$ is even, so Theorem <a href="#long251:res:signedwindow" data-reference-type="ref" data-reference="long251:res:signedwindow">16</a> applies throughout the range where the local certificate is sought. The same computation for a real orbit is one line and is used in Theorem <a href="#long251:res:sparse" data-reference-type="ref" data-reference="long251:res:sparse">28</a> below.

<a id="an-explicit-remainder-and-a-certified-actual-pair"></a>

## An explicit remainder and a certified actual pair

Both window conditions involve complete infinite tails. A dominated truncation reduces each of them to a finite integer comparison.

<div id="long251:res:explicit-remainder" class="proposition">

**Proposition 17** (explicit remainder). *For integers $`h,N\ge0`$ and $`L\ge1`$ put
``` math
F_{h,N,L}=\sum_{j=1}^{L}\frac{g_{N+h+j}-g_{N+j}}{2^{\,j}},\qquad
 P(x)=x^4+8x^3+36x^2+104x+150,
```
``` math
E_{h,N,L}=\frac{1250}{2^{L}}\bigl(P(N+h+L+2)+P(N+L+2)\bigr).
```
Then $`\bigl|\sigma_h(N)-F_{h,N,L}\bigr|\le E_{h,N,L}`$. In particular $`|F_{h,N,L}|+E_{h,N,L}<1`$ certifies $`|\sigma_h(N)|<1`$, and $`\operatorname{dist}(F_{h,N,L},\mathbb{Z})>E_{h,N,L}`$ certifies $`\sigma_h(N)\notin\mathbb{Z}`$.*

</div>

<div class="proof">

*Proof.* The checked bound $`p_n\le1250(n+1)^4`$ gives $`0\le g_m\le p_{m+1}\le1250(m+2)^4`$, so the omitted absolute tail is at most
``` math
1250\sum_{j>L}\frac{(N+h+j+2)^4+(N+j+2)^4}{2^{\,j}} .
```
The polynomial identity $`2P(x)=(x+1)^4+P(x+1)`$ telescopes to $`\sum_{k=1}^{J}(m+k)^42^{-k}=P(m)-P(m+J)2^{-J}`$, whose last term tends to zero. Apply it with $`m=N+h+L+2`$ and $`m=N+L+2`$ after writing $`j=L+k`$. The two tests follow from the triangle inequality and the definition of distance to $`\mathbb{Z}`$. ◻

</div>

<div id="long251:res:finite-smallpair" class="proposition">

**Proposition 18** (a certified adjacent pair). *For the actual prime gaps, $`h=1`$ and $`N=2`$ satisfy the three hypotheses of Theorem <a href="#long251:res:smallpair" data-reference-type="ref" data-reference="long251:res:smallpair">13</a>: both $`\sigma_1(2)`$ and $`\sigma_1(3)`$ lie in $`(-1,1)`$ and are nonintegral, and $`g_4=2\ne4=g_3`$.*

</div>

<div class="proof">

*Proof.* Take $`L=40`$ and $`Q=2^{40}=1099511627776`$. Exact integer arithmetic over the first $`46`$ primes gives
``` math
\begin{array}{c|r|r}
 N&Q\,F_{1,N,40}&Q\,E_{1,N,40}\\\hline
 2&-662838684750&11764181250\\
 3& 873345886050&12805761250
\end{array}
```
In each row $`|QF|+QE<Q`$, which puts the whole certified interval inside $`(-1,1)`$, and $`QE`$ is smaller than the distance from $`QF`$ to the nearest multiple of $`Q`$, which excludes every integer. The margins are $`424908761776`$ and $`213359980476`$ respectively. These are strict integer comparisons rather than inferences from rounded numerical tails. Appendix <a href="#long251:app:certificates" data-reference-type="ref" data-reference="long251:app:certificates">12</a> replays them. ◻

</div>

This witness proves the local condition at one pair of indices. The quantifiers over every $`h`$ and every cutoff remain.

<div id="long251:res:one-tail-certificate" class="proposition">

**Proposition 19** (a one-tail signed certificate). *Let $`D_{N+1}=2D_N-\delta_N`$ with real $`D_N`$, and suppose $`\delta_N=2s`$ for $`s\in\{-1,1\}`$. If integers $`A,B,Q`$ satisfy $`Q>0`$, $`B\ge0`$, $`|QD_N-A|\le B`$, and
``` math
2sA-Q>2B,\qquad Q-sA>B,
```
then $`1/2<sD_N<1`$, $`|D_{N+1}|<1`$, and both $`D_N,D_{N+1}`$ are nonintegral. In particular the adjacent small-shift obstruction is certified from just one tail enclosure.*

</div>

<div class="proof">

*Proof.* The inequalities place the complete interval $`[(sA-B)/Q,(sA+B)/Q]`$ inside $`(1/2,1)`$. Thus $`sD_{N+1}=2sD_N-2\in(-1,0)`$, proving every assertion. ◻

</div>

For $`h=1,N=2`$, the exact data already used above give $`Q=2^{40}`$, $`A=-662838684750`$, $`B=11764181250`$ and $`s=-1`$. The two positive integer margins are respectively $`202637379224`$ and $`424908761776`$. The second enclosure in Proposition <a href="#long251:res:finite-smallpair" data-reference-type="ref" data-reference="long251:res:finite-smallpair">18</a> remains a useful independent cross-check, not a logical necessity.

<a id="long251:sec:denominator-floor"></a>

# Two denominator floors

The same polynomial bound yields an exact rational enclosure of $`\Pi`$, and any such enclosure excludes an initial range of denominators.

<div id="long251:res:denominatorfloor" class="theorem">

**Theorem 20** (kernel-decided denominator floor). *Let $`a\in\mathbb{Z}`$ and $`b\in\mathbb{N}_{>0}`$. If $`\Pi=a/b`$ then $`b\ge2^{589}>10^{177}`$, and the same floor holds for every rational equal to $`S`$.*

</div>

<div class="proof">

*Proof.* Put $`c=1229`$, the number of primes below $`10^4`$, and $`A=\sum_{i=0}^{c-1}p_i2^{\,c-i-1}`$, so that $`A/2^{c}`$ is the $`c`$th partial sum of $`\Pi`$. All terms are positive, so $`A/2^{c}\le\Pi`$. For the upper bound, $`p_{c+j}\le1250(c+j+1)^4`$ and $`(c+1+j)^4\le(c+1)^4(3/2)^{j}`$ for $`j\ge0`$, valid because $`c\ge9`$; summing the resulting geometric tail with ratio $`3/4`$ gives
``` math
\frac{A}{2^{c}}\;\le\;\Pi\;\le\;\frac{2A+5000(c+1)^4}{2^{\,c+1}} .
```
The four positive integers $`u,v,u',v'`$ printed in Appendix <a href="#long251:app:certificates" data-reference-type="ref" data-reference="long251:app:certificates">12</a> satisfy
``` math
u'v-uv'=1,\qquad
 \frac uv<\frac{A}{2^{c}},\qquad
 \frac{2A+5000(c+1)^4}{2^{\,c+1}}<\frac{u'}{v'},\qquad
 v+v'\ge2^{589},
```
all four being integer comparisons after clearing the positive denominators. If $`\Pi=a/b`$ then $`av-bu\ge1`$ and $`bu'-av'\ge1`$, and the determinant identity gives
``` math
b=b(u'v-uv')=(av-bu)v'+(bu'-av')v\ge v+v' \ge 2^{589}.
```
This is the classical bound for a rational strictly between two Farey neighbours. Since $`589\log_{10}2>177`$, the floor exceeds $`10^{177}`$. If $`S=a/b`$, apply the same argument to $`\Pi=(a+2b)/b`$. ◻

</div>

The Lean kernel decides the four inequalities on the same literals by `decide +kernel` with no `native_decide`, over a trial-division sieve it re-runs on $`[2,10^4)`$: the [certificate](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/KernelDenominatorFloor.lean#L310), the [floor for the prime series](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/KernelDenominatorFloor.lean#L316), and the [floor for the gap series](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/KernelDenominatorFloor.lean#L324). Its analytic input is the same enclosure, over the polynomial bound at [line 360](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L360). The four Farey literals have $`177`$ and $`178`$ digits.

<div id="long251:res:cfexclusion" class="theorem">

**Theorem 21** (certified continued-fraction exclusion). *Every rational equal to $`\Pi`$, and hence every rational equal to $`S`$, has reduced denominator $`q\ge2^{39997}`$, and therefore $`q>10^{12040}`$.*

</div>

*Evidence.* This is an exact finite computation and no Lean declaration carries it. The continued-fraction expansion of $`\Pi`$ is developed to $`23369`$ partial quotients at a working scale of $`80000`$ bits. Each quotient is forced by a rational bracket of width $`1`$ in those scaled integer units around the true value, and the separation $`|q_n\Pi-p_n|>0`$ is verified against that bracket, so the prefix is the true prefix. No floating-point reconstruction enters it. The bracket uses the Lean-checked tail estimate $`p_n\le1250(n+1)^4`$, so no conjecture enters. The classical theorem that a best approximation of the second kind is a convergent then converts the certified prefix into the denominator bound \[khinchin1964, §6, Theorems 16 and 17\]; Short gives an accessible statement and proof \[short2009, Theorem 1.1\]. The receipt is [`certified-cf.json`](https://github.com/wcook04/plectis-erdos/blob/dd6cc708f650f061de06594eba6ba43878f4de31/research/experiments/erdos251/receipts/certified-cf.json), which records the generating program and its digest, the power-of-two exponent $`39997`$, the bit length $`39998`$, the strict decimal power $`12040`$, the decimal digit count $`12041`$, the largest partial quotient $`973919`$ at index $`16442`$, and an arithmetic self-check of the same routine against the known expansions of $`e`$ and $`\pi`$. The certified statement is $`q\ge2^{39997}`$ and $`q>10^{12040}`$. Printing the bit length or the digit count as an exponent overstates the bound by one power of two and one decimal order.

Each floor is finite, and extending either one raises the excluded range and reproduces the same statement form. Neither decides the problem.

<a id="long251:sec:obstructions"></a>

# What cannot supply the missing input

The counterexamples in this section test which information about the gaps could force irrationality. They preserve selected growth, residue and nonconcentration properties while changing the dyadic value. The sparsity result has a different role: it rules out a positive-proportion lower bound for the two-window event, while leaving sparse-witness arguments available.

<a id="bounded-residue-preserving-perturbations"></a>

## Bounded residue-preserving perturbations

<div id="long251:res:boundedperturbation" class="theorem">

**Theorem 22** (bounded-perturbation obstruction). *Let $`a_n`$ be natural numbers with $`\sum_{n\ge0}a_n2^{-(n+1)}`$ convergent. For every integer $`M\ge1`$ and every cutoff $`K`$ there are digits $`\varepsilon_n\in\{0,1\}`$, zero for $`n<K`$, such that $`\sum_{n\ge0}(a_n+M\varepsilon_n)2^{-(n+1)}`$ is rational.*

</div>

<div class="proof">

*Proof.* Write $`A=\sum_{n\ge0}a_n2^{-(n+1)}`$ and choose a rational $`r\in\bigl(A,A+M2^{-K}\bigr)`$. A binary expansion of $`(r-A)/M`$ has the form $`\sum_{n\ge K}\varepsilon_n2^{-(n+1)}`$ with $`\varepsilon_n\in\{0,1\}`$; set $`\varepsilon_n=0`$ for $`n<K`$. The perturbed series converges and equals $`r`$. ◻

</div>

The [construction](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L193) is kernel checked. The invariant-property consequence—a property shared by every admissible perturbation cannot by itself force irrationality—is the ordinary logical reading of that construction, rather than a separately named Lean theorem. The construction is also checked at the actual consecutive prime gaps for every $`M\ge1`$ and every $`K`$, the [rational perturbed prime-gap series](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L208), with the perturbed gap lying in $`[g_n,g_n+M]`$ and congruent to $`g_n`$ modulo $`M`$, the [gap bounds](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L234). Consequently no theorem about the size or the residue of prime gaps that survives such a perturbation can suffice for Problem #251; that class includes the bounded-gap and large-gap theorems cited in Section <a href="#long251:sec:open" data-reference-type="ref" data-reference="long251:sec:open">10</a> and equidistribution of $`p_n`$ modulo any fixed $`q`$, on taking $`M=2q`$. The perturbed digits need not remain prime gaps.

<a id="algebraic-nonconcentration-survives-the-rationalising-perturbation"></a>

## Algebraic nonconcentration survives the rationalising perturbation

Fixed-block polynomial nonconcentration is a finer property than size and residue, but it too survives the bounded perturbation. The relevant input is Schlage-Puchta’s Lemma 4: for every polynomial $`F\in\mathbb{Z}[x_0,\ldots,x_k]`$ which does not vanish identically, $`F(g_n,\ldots,g_{n+k})\ne0`$ for almost all $`n`$ \[schlagepuchta2011, Lemma 4, pp. 5–6\]. Say that an integer sequence $`a`$ has *fixed-block nonconcentration* when it satisfies that conclusion for every $`k\ge0`$ and every nonzero $`F\in\mathbb{Z}[x_0,\ldots,x_k]`$. The property transfers across bounded perturbations with no independence or randomness assumption.

<div id="long251:res:shiftedcount" class="proposition">

**Proposition 23** (finite counting for shifted gap differences). *Write $`p_n`$ for the primes indexed from $`p_0=2`$ and $`g_n=p_{n+1}-p_n`$. For $`h\ge2`$ and $`r\in\mathbb{Z}`$, let $`M_{h,r}(N)`$ count $`n<N`$ with $`g_{n+h}-g_n=r`$. Let $`Q_{N,H,r}`$ count triples $`(x,d,s)`$ with $`x<p_N`$, $`0<d<s\le H`$, $`d+r>0`$, and all four integers $`x,x+d,x+s,x+s+d+r`$ prime. Then, for every $`N,H\ge0`$,
``` math
(H+1)M_{h,r}(N)\le
 (h+1)p_{N+h+1}+(H+1)Q_{N,H,r}.
```*

</div>

<div class="proof">

*Proof.* For a counted index $`n`$, put $`x=p_n`$, $`d=g_n`$ and $`s=p_{n+h}-p_n`$. If the total span $`p_{n+h+1}-p_n`$ is at most $`H`$, then $`0<d<s\le H`$, $`d+r=g_{n+h}>0`$, and the four primes are precisely $`x,x+d,x+s,x+s+d+r`$. The map is injective because $`x=p_n`$ determines $`n`$. For the remaining indices the integer span is at least $`H+1`$. Each gap appears in at most $`h+1`$ of the spans, so their total is at most $`(h+1)\sum_{i<N+h}g_i<(h+1)p_{N+h+1}`$. Multiply the resulting bound on the exceptional count by $`H+1`$ and add the small-span contribution. ◻

</div>

The displayed finite shifted-count bound is unconditional by the ordinary proof above. Its [historical source locator](https://github.com/wcook04/plectis-erdos/blob/d058b9150218ae23d2cfd975580088d6167e9da8/ErdosProblems/Erdos251/ShiftedGapCountingR9.lean#L152) is not present in the supplied declaration index, so no checked-build status is assigned to that link here. To deduce zero density one still needs, for every $`\varepsilon>0`$ and all large $`N`$, a choice of $`H`$ making the right side less than $`\varepsilon N(H+1)`$. The adjacent case $`h=1`$ instead requires the corresponding three-prime estimate, because two of the four positions would coincide. The all-shift implication records these analytic premises explicitly; it supplies neither estimate and does not prove irrationality.

<div id="long251:res:nonconcentration" class="theorem">

**Theorem 24** (nonconcentration is perturbation-stable). *Let $`a:\mathbb{N}\to\mathbb{Z}`$ have fixed-block nonconcentration, let $`E\subset\mathbb{Z}`$ be finite, and let $`b_n=a_n+e_n`$ with $`e_n\in E`$ for every $`n`$. Then $`b`$ has fixed-block nonconcentration.*

</div>

<div class="proof">

*Proof.* Fix $`k\ge0`$ and a nonzero $`F\in\mathbb{Z}[x_0,\ldots,x_k]`$. For a tuple $`\mathbf e=(e^{(0)},\ldots,e^{(k)})\in E^{k+1}`$ put $`F_{\mathbf e}(x_0,\ldots,x_k)=F(x_0+e^{(0)},\ldots,x_k+e^{(k)})`$. The substitution $`x_i\mapsto x_i+e^{(i)}`$ is a ring automorphism of $`\mathbb{Z}[x_0,\ldots,x_k]`$ with inverse $`x_i\mapsto x_i-e^{(i)}`$, so $`F_{\mathbf e}\ne0`$. If $`F(b_n,\ldots,b_{n+k})=0`$ then $`F_{\mathbf e}(a_n,\ldots,a_{n+k})=0`$ for the tuple $`\mathbf e=(e_n,\ldots,e_{n+k})`$, whence
``` math
\{\,n:F(b_n,\ldots,b_{n+k})=0\,\}
 \;\subseteq\!\!
 \bigcup_{\mathbf e\in E^{k+1}}\!\!
 \{\,n:F_{\mathbf e}(a_n,\ldots,a_{n+k})=0\,\}.
```
Each set on the right has density zero by hypothesis, and the union is over the finite index set $`E^{k+1}`$, so a finite union of density-zero sets has density zero. ◻

</div>

<div id="long251:res:nonconc-primes" class="corollary">

**Corollary 25** (nonconcentration does not force irrationality). *Fix $`M\ge1`$ and $`K\ge0`$, and let $`b`$ be the perturbed sequence supplied by Theorem <a href="#long251:res:boundedperturbation" data-reference-type="ref" data-reference="long251:res:boundedperturbation">22</a> at the actual prime gaps. Then $`\sum_{n\ge0}b_n2^{-(n+1)}`$ is rational, $`b_n=g_n`$ for $`n<K`$, $`b_n-g_n\in\{0,M\}`$ and $`b_n\equiv g_n\pmod M`$ for every $`n`$, $`b`$ has fixed-block nonconcentration, and the cumulative sequence $`P_n=2+\sum_{i<n}b_i`$ satisfies $`p_n\le P_n\le p_n+Mn`$ and hence $`P_n\sim n\log n`$.*

</div>

<div class="proof">

*Proof.* Everything except nonconcentration is Theorem <a href="#long251:res:boundedperturbation" data-reference-type="ref" data-reference="long251:res:boundedperturbation">22</a> together with $`\sum_{i<n}g_i=p_n-2`$, and $`P_n\sim n\log n`$ follows from $`p_n\sim n\log n`$ \[mv2007, Chapter 6\]. The perturbation takes values in the fixed two-element set $`E=\{0,M\}`$, so Theorem <a href="#long251:res:nonconcentration" data-reference-type="ref" data-reference="long251:res:nonconcentration">24</a> applies to the actual gaps, which have fixed-block nonconcentration by Schlage-Puchta’s lemma \[schlagepuchta2011, Lemma 4\]. ◻

</div>

Fixed-block polynomial nonconcentration, taken together with a prescribed finite prefix of actual gaps, a pointwise bound $`b_n\le g_n+M`$, every residue modulo $`M`$, positivity and cumulative growth at the prime-number-theorem scale, is therefore compatible with a rational dyadic value. Taking $`M`$ even also preserves eventual evenness. To preserve a prescribed modulus $`q`$ together with parity, take $`M=2q`$, with the corresponding pointwise bound $`b_n\le g_n+2q`$. The boundary is exact: the terms $`P_n`$ are not asserted to be prime, and the conclusion says nothing about constraints with a block length or a polynomial family growing with the index.

<div id="long251:res:sparse-nonconcentration" class="proposition">

**Proposition 26** (nonconcentration under sparse changes). *Let $`a,b:\mathbb{N}\to\mathbb{Z}`$ agree off a set $`S`$ of ordinary density zero. If $`a`$ has fixed-block nonconcentration, then so does $`b`$. No boundedness assumption on $`a-b`$ is needed.*

</div>

<div class="proof">

*Proof.* For fixed $`k`$ and a nonzero $`F\in\mathbb{Z}[x_0,\ldots,x_k]`$, a zero of $`F(b_n,\ldots,b_{n+k})`$ either is already a zero at the $`a`$-block or has $`n+i\in S`$ for some $`0\le i\le k`$. Each fixed translate of a density-zero set has density zero, and a finite union retains that property. This proves the assertion for each fixed $`F`$ and $`k`$. It gives no uniform estimate for polynomial families or lengths growing with $`n`$. ◻

</div>

<div id="long251:res:jointcountermodel" class="corollary">

**Corollary 27** (simultaneous prime-gap countermodel). *For every prescribed finite prime-gap prefix and $`0<\varepsilon\le1`$, there is an altered word $`b=g+e`$, with $`P_n=2+\sum_{i<n}b_i`$, for which one can simultaneously impose a rational dyadic value, nonnegative integer corrections eventually at most $`(\log(n+3))^\varepsilon`$, all fixed eventual coefficient and cumulative congruences, fixed-block polynomial nonconcentration, and vanishing literal block TV distance for lengths $`o(\log\log X)`$. The cumulative positions satisfy
``` math
0\le P_n-p_n=O_\varepsilon\left(
    \frac{n(\log(n+3))^\varepsilon}{\log\log n}\right),
 \qquad P_n\sim n\log n.
```*

</div>

<div class="proof">

*Proof.* Apply the sparse theorem at a rational target, then the preceding proposition and Schlage-Puchta’s Lemma 4 \[schlagepuchta2011\]. To obtain the cumulative support bound, split $`[\sqrt n,n)`$ into dyadic intervals, use $`\log\log x\asymp\log\log n`$ there, and bound the first $`\sqrt n`$ indices trivially. Thus $`|S\cap[0,n)|=O(n/\log\log n)`$. The pointwise correction bound gives the displayed estimate, including a fixed constant for the exceptional prefix. Since $`(\log n)^{\varepsilon-1}/\log\log n\to0`$ for $`0<\varepsilon\le1`$, the prime number theorem \[mv2007, Chapter 6\] gives the last conclusion. ◻

</div>

These are ordinary deductions from the sparse theorem and the stated external analytic input. The reconstructed positions need not be prime. Neither a bounded translation nor a sparse change preserves general relative frequencies of rare events; their two transfer arguments have different hypotheses and must not be conflated.

<a id="the-two-window-event-has-density-zero"></a>

## The two-window event has density zero

The same lemma bounds the event that the local certificate consumes.

<div id="long251:res:sparse" class="theorem">

**Theorem 28** (sparsity of the two-window event). *Fix $`h\ge1`$. The set of $`N\ge1`$ at which the three hypotheses of Theorem <a href="#long251:res:smallpair" data-reference-type="ref" data-reference="long251:res:smallpair">13</a> hold for the actual prime gaps has density zero. For the same $`h`$, the set of $`N`$ with $`g_{N+h+1}=g_{N+1}`$ also has density zero.*

</div>

<div class="proof">

*Proof.* For $`N\ge1`$ every gap involved is even, so $`\delta_N=g_{N+h+1}-g_{N+1}`$ is even. If $`|\sigma_h(N)|<1`$, $`|\sigma_h(N+1)|<1`$ and $`\delta_N\ne0`$, then $`\delta_N=2\sigma_h(N)-\sigma_h(N+1)`$ lies in $`(-3,3)`$, so $`\delta_N=\pm2`$. Apply Schlage-Puchta’s lemma \[schlagepuchta2011, Lemma 4\] at index $`n=N+1`$ with $`k=h`$ to the two polynomials $`F_\pm(x_0,\ldots,x_h)=x_h-x_0\mp2`$, neither of which vanishes identically: each of $`\{N:\delta_N=2\}`$ and $`\{N:\delta_N=-2\}`$ has density zero, and the event is contained in their union. The second assertion is the same lemma applied to $`F(x_0,\ldots,x_h)=x_h-x_0`$. ◻

</div>

The two halves point in opposite directions and both are useful. The mismatch hypothesis on its own holds for almost all $`N`$, which is strictly stronger than the cofinal statement Proposition <a href="#long251:res:gap-nonperiodic" data-reference-type="ref" data-reference="long251:res:gap-nonperiodic">15</a> supplies. The full conjunction is confined to a set of density zero, because the two window conditions force the mismatch to be exactly $`\pm2`$. A producer for Problem <a href="#long251:prob:smallpair" data-reference-type="ref" data-reference="long251:prob:smallpair">33</a> therefore has to be a cofinality statement about a sparse set. Consequently, this event cannot be supplied on a set of positive lower density. A sufficient producer would have to yield cofinally many witnesses in a density-zero set; density zero alone does not exclude an averaging argument capable of detecting such sparse witnesses. The finite measurements in Section <a href="#long251:sec:measurements" data-reference-type="ref" data-reference="long251:sec:measurements">9</a> show a decline across the sampled bands. They establish neither an asymptotic rate for the density nor a counting law. Prime-height cutoffs and gap-index cutoffs must also be distinguished before comparing any proposed rates.

<a id="recurring-gap-values-differing-by-two-do-not-suffice"></a>

## Recurring gap values differing by two do not suffice

Theorem <a href="#long251:res:signedwindow" data-reference-type="ref" data-reference="long251:res:signedwindow">16</a> reduces the producer to a $`\pm2`$ mismatch together with a half-window condition. It is tempting to hope that the mismatch half is the substance, and that two even values differing by $`2`$, each occurring infinitely often as a consecutive prime gap inside a common index residue class, would suffice. At the level of integer-digit recurrences that implication is false, and it stays false under growth at the scale the primes actually have.

<div id="long251:res:polignacfail" class="theorem">

**Theorem 29** (recurring values are not enough). *There is a sequence $`(a_n)_{n\ge1}`$ of positive even integers with the following properties. The values $`2`$ and $`4`$ each occur infinitely often at indices divisible by every fixed $`t\ge1`$. The sequence is unbounded, not eventually periodic, and satisfies $`a_n=O(\log n)`$. The series $`\sum_{n\ge1}a_n2^{-n}`$ equals $`6`$, and every scaled tail $`\sum_{j\ge1}a_{N+j}2^{-j}`$ is an integer, so every tail shift is integral. The increasing odd sequence $`P_n=3+\sum_{j\le n}a_j`$ satisfies $`P_n\sim n\log n`$.*

</div>

<div class="proof">

*Proof.* Let logarithms be natural and put $`b_n=2\lceil\tfrac12\log(n+64)\rceil`$, so that $`b_n`$ is even, $`b_n\ge6`$, and $`b_n=\log(n+64)+O(1)`$. Since $`\tfrac12\log(n+65)-\tfrac12\log(n+63)<1`$ for every $`n\ge1`$, consecutive increments of $`b`$ lie in $`\{0,2\}`$ and $`b_{n+1}-b_{n-1}\le2`$. Call an index $`n`$ *special* when $`n=k!`$ or $`n=2\,k!`$ for some $`k\ge5`$, and define
``` math
U_n=\begin{cases}
  2b_{n-1}-2,& n=k!,\ k\ge5,\\
  2b_{n-1}-4,& n=2\,k!,\ k\ge5,\\
  b_n,&\text{otherwise},
 \end{cases}
 \qquad a_n=2U_{n-1}-U_n\quad(n\ge1).
```
The special indices are distinct and never adjacent, since $`k!`$ and $`2\,k!`$ are even and differ by more than one from each other and from the neighbouring special indices. Each $`U_n`$ is an even integer by construction, so each $`a_n`$ is an even integer.

At an ordinary index whose predecessor is also ordinary, $`a_n=2b_{n-1}-b_n=b_{n-1}-(b_n-b_{n-1})\ge6-2=4`$. At a special index the predecessor is ordinary and $`a_n=2b_{n-1}-(2b_{n-1}-r)=r`$, which is $`2`$ at $`n=k!`$ and $`4`$ at $`n=2\,k!`$. Immediately after a special index carrying $`r`$,
``` math
a_{n+1}=2(2b_{n-1}-r)-b_{n+1}\ge4b_{n-1}-2r-(b_{n-1}+2)
 =3b_{n-1}-2r-2\ge8 .
```
Every $`a_n`$ is therefore a positive even integer, and $`U_n=O(\log n)`$ gives $`a_n=O(\log n)`$. At ordinary indices with ordinary predecessors $`a_n\ge b_{n-1}-2\to\infty`$, so $`(a_n)`$ is unbounded and hence not eventually periodic.

The definition $`a_n=2U_{n-1}-U_n`$ is exactly $`a_n2^{-n}=U_{n-1}2^{-(n-1)}-U_n2^{-n}`$, so for every $`N\ge0`$ and $`m\ge1`$
``` math
\sum_{j=1}^{m}\frac{a_{N+j}}{2^{\,j}}=U_N-\frac{U_{N+m}}{2^{\,m}} .
```
Since $`U_n=O(\log n)`$ the endpoint tends to zero, so the tail at $`N`$ equals the integer $`U_N`$; at $`N=0`$ the series equals $`U_0=b_0=6`$. Every difference $`U_{N+h}-U_N`$ is an integer, so every tail shift is integral.

For each $`t`$ and every sufficiently large $`k`$ we have $`t\mid k!`$, hence $`t\mid2\,k!`$, and $`a_{k!}=2`$ while $`a_{2k!}=4`$: both values recur infinitely often at indices congruent to $`0`$ modulo $`t`$.

Finally, summing $`a_j=2U_{j-1}-U_j`$ gives $`\sum_{j=1}^{n}a_j=2U_0+\sum_{j=1}^{n-1}U_j-U_n`$. The baseline $`\sum_{j<n}b_j=n\log n+O(n)`$. The special indices up to $`n`$ number $`O(\log n/\log\log n)`$ and each changes the summand by $`O(\log n)`$, so their total contribution is $`O((\log n)^2)=o(n)`$. Hence $`P_n=3+\sum_{j\le n}a_j\sim n\log n`$, and $`P_n`$ is odd and increasing. ◻

</div>

The factorial schedule above proves recurrence in the zero residue class. The following separate construction strengthens this to every residue class.

<a id="long251:res:all-residue-log-countermodel"></a>

## A complete countermodel in every residue class

There is a synthetic integer sequence $`(a_n)_{n\ge1}`$ with all of the following properties. Each $`a_n`$ is positive and divisible by $`2`$, and
``` math
a_n\le 4\log(n+1)+24.
```
For every $`t\ge1`$, every $`0\le r<t`$, and every cutoff $`N`$, there are $`i,j\ge N`$ such that
``` math
i\equiv j\equiv r\pmod t,\qquad a_i=2,\quad a_j=4.
```
For every integer $`B`$ and cutoff $`N`$, some $`n\ge N`$ satisfies $`a_n>B`$. For every $`h\ge1`$ there is no cutoff after which $`a_{n+h}=a_n`$ for all $`n`$. Nevertheless, all the complete tails
``` math
U_N=\sum_{j\ge1}\frac{a_{N+j}}{2^j}\quad(N\ge0)
```
are integers, $`U_0=6`$, and $`U_{N+h}-U_N\in\mathbb Z`$ for every $`N,h\ge0`$. The sequence
``` math
P_N=3+\sum_{j=1}^{N}a_j
```
is strictly increasing and odd, with $`P_N/(N\log N)\to1`$. These are synthetic positions; no $`P_N`$ is asserted to be prime.

To obtain every residue class, enumerate triples consisting of a positive modulus, a residue, and a repetition index. Choose the corresponding centres $`c_k`$ in the prescribed classes with $`c_0\ge100`$, $`c_{k+1}\ge c_k+3`$ and $`c_k\ge2^{k^2}`$ for $`k\ge1`$. The parity of the repetition index selects the desired value $`v_k=2`$ or $`4`$. Use the even baseline
``` math
b_n=6+2\left\lfloor\frac{\log(n+1)}2\right\rfloor,
 \qquad
 U_n=\begin{cases}2b_{n-1}-v_k,&n=c_k,\\b_n,&n\notin\{c_k:k\ge0\},\end{cases}
```
and define $`a_n=2U_{n-1}-U_n`$. The separation of the centres and the baseline increment bound give positivity and the displayed logarithmic bound. Finite telescoping leaves $`U_{N+m}/2^m`$, which tends to zero; thus these carries are the complete tails. The sparse changes to the baseline have negligible contribution after division by $`N\log N`$, which gives the stated growth of $`P_N`$.

The full statement is [kernel-checked in Lean](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/AllResidueLogarithmicR9.lean#L503).

This rules out an inference from these coefficient properties alone to nonintegral tail shifts. It gives no counterexample to the prime-gap problem and does not reproduce the extreme large gaps of the primes.

The consequence is exact. Positivity, evenness, unboundedness, non-eventual periodicity, a pointwise logarithmic bound, cumulative growth at the prime-number-theorem scale, and the recurrence of two even values differing by $`2`$ inside every index residue class are jointly compatible with an integral tail at every index. Any route through that input must use a property of the consecutive primes beyond this list. The sequence $`(a_n)`$ is synthetic and the $`P_n`$ are not asserted to be prime. The pointwise logarithmic bound also precludes the known large-gap behaviour, so the theorem does not speak to hypotheses that use extreme gaps.

<a id="two-further-boundaries"></a>

## Two further boundaries

<div id="long251:res:polynomialcountermodel" class="proposition">

**Proposition 30** (quadratic polynomial-shift countermodel). *Put $`c_n=2(n^2+4n+2)`$ and $`U_n=2(n+4)^2`$. Then $`c_n`$ is positive, even and strictly increasing, $`U_{n+1}=2U_n-c_{n+1}`$, every shift $`U_{N+h}-U_N`$ is integral, $`c_{n+1}-c_n=4n+10`$ is never $`\pm2`$, and
``` math
\sum_{j\ge1}\frac{c_j}{2^{\,j}}=32 .
```*

</div>

<div class="proof">

*Proof.* Direct expansion gives the recurrence, and the finite telescope is $`\sum_{j=1}^{n}c_j2^{-j}=32-2(n+4)^22^{-n}`$, whose last term tends to zero. The remaining assertions follow from the integer values of $`U_n`$ and from $`c_{n+1}-c_n=4n+10\ge10`$. ◻

</div>

The series is the one starting at $`j=1`$, whose initial tail state is $`U_0=32`$; under the opening convention $`\sum_{n\ge0}c_n2^{-(n+1)}`$ the same word has value $`18`$, and the two ranges must be kept apart. The formal construction checks the [recurrence](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1596), [strict growth](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1632), [integrality of every shift](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1654), [exclusion of adjacent differences of size two](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1644), and the [value $`32`$ for the shifted series](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PolynomialGapSeriesValue.lean#L92), whose summand is $`c_{n+1}/2^{\,n+1}`$; the rational value is recorded at [line 109](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PolynomialGapSeriesValue.lean#L109). Positivity, parity, strict growth, unboundedness and nonperiodicity are therefore jointly compatible with rationality, and the adjacent trigger of Theorem <a href="#long251:res:signedwindow" data-reference-type="ref" data-reference="long251:res:signedwindow">16</a> fails at every index. The telescoping mechanism is the one used in the note of ChatGPT 5.4 Pro (orchestrated by Vjeko Kovač) against the variable-denominator expectation of Erdős \[kovac2026, Theorem 1 and proof, pp. 1–2\]; the word is not a result about Problem #251.

Rationality also fails to force the coefficients to repeat. Let $`K:\mathbb{N}\to\mathbb{Q}`$ be arbitrary and put $`\kappa_n=2K_n-K_{n+1}`$: the [carry coefficient](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1129).

<div id="long251:res:telescope" class="proposition">

**Proposition 31** (exact telescoping). *For every $`n\ge0`$, $`\sum_{i=0}^{n-1}\kappa_i2^{-(i+1)}=K_0-K_n2^{-n}`$.*

</div>

<div class="proof">

*Proof.* A routine induction; the added term is $`(2K_n-K_{n+1})2^{-(n+1)}=K_n2^{-n}-K_{n+1}2^{-(n+1)}`$. ◻

</div>

The carry form $`\kappa_n=2K_n-K_{n+1}`$ is the case $`a_n=2`$ of the rationality criterion of Erdős and Straus: for integers $`b_n`$ and positive integers $`a_n`$ with $`a_n>1`$ for all large $`n`$ and $`|b_n|/(a_{n-1}a_n)\to0`$, the series $`\sum_nb_n/(a_1\cdots a_n)`$ is rational exactly when some positive integer $`B`$ and integers $`c_n`$ satisfy $`Bb_n=c_na_n-c_{n+1}`$ and $`|c_{n+1}|<a_n/2`$ for all large $`n`$ \[erdosstraus1974, Theorem 2.1, pp. 85–86\]. For the prime gaps the numerators $`b_n=g_n`$ are unbounded, so that hypothesis fails, and the proposition above imposes no condition on $`K`$.

Formalised as the [carry telescoping identity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1137). Taking $`K_0=\tfrac52`$ and $`K_n=2n+2`$ for $`n\ge1`$ gives $`\kappa_0=1`$ and $`\kappa_n=2n`$, so the coefficients $`1,2,4,6,8,\ldots`$ are positive, even after the first term, unbounded and not eventually periodic, while their dyadic sum is $`\tfrac52`$. Rationality alone therefore cannot imply eventual periodicity even for a positive, parity-correct integer coefficient sequence, and no argument may play periodicity of a rational value against Proposition <a href="#long251:res:gap-nonperiodic" data-reference-type="ref" data-reference="long251:res:gap-nonperiodic">15</a>.

The affine and fixed-lattice escape formulations do not create new prime-distribution information. Their full definitions and exact hypotheses are preserved in Appendix <a href="#long251:app:affine-detail" data-reference-type="ref" data-reference="long251:app:affine-detail">15</a>.

<a id="long251:sec:measurements"></a>

# What is measured

Two finite computations report on the two producers. Each covers one bounded range and supplies no cofinal statement.

Over the $`6\,841\,648`$ primes below $`1.2\times10^{8}`$ and offsets $`h=1,\ldots,16`$, the reduced two-window event of Theorem <a href="#long251:res:signedwindow" data-reference-type="ref" data-reference="long251:res:signedwindow">16</a> occurs at every offset, with density between $`0.00418`$ and $`0.008248`$ and the two signs near balanced; at $`h=1`$ there are $`56\,427`$ occurrences among $`6\,841\,564`$ candidate indices, the last at the prime $`119\,995\,753`$. Rescaled by $`\log p`$ the band densities run from $`0.17671`$ down to $`0.13148`$ with decelerating drift over the measured bands. This finite observation does not establish an asymptotic counting law or cofinality. The tails in this scan are double-precision floating-point, so an individual hit is a numerical observation and carries no certificate; the median distance from the shift to the nearer window boundary is $`0.127`$ and the worst case over $`34\,000`$ hits is $`6.1\times10^{-7}`$, eight orders above the working resolution, and $`3\,200`$ sampled hits across $`h=1,\ldots,8`$ were rechecked against the literal three-part statement with no violations. Proposition <a href="#long251:res:finite-smallpair" data-reference-type="ref" data-reference="long251:res:finite-smallpair">18</a> is the one pair certified by exact integer arithmetic. The receipt is [`adjacent-mismatch.json`](https://github.com/wcook04/plectis-erdos/blob/dd6cc708f650f061de06594eba6ba43878f4de31/research/experiments/erdos251/receipts/adjacent-mismatch.json).

Over the $`1\,270\,607`$ primes below $`2\times10^{7}`$, and for every modulus $`t\le20`$ and every residue class modulo $`t`$, the free-pair event of Theorem <a href="#long251:res:freepair" data-reference-type="ref" data-reference="long251:res:freepair">11</a> has witnesses running to the last usable index: the leanest class at $`t=20`$ carries $`90\,150`$ witnesses and the latest witness sits at index $`1\,270\,520`$ of $`1\,270\,540`$. The recorded floating-point witnesses pass the stronger two-window test over this finite range; they are numerical observations, not exact certificates or a proof of either cofinal producer. What the scan does not supply is uniformity in $`t`$ and in the cutoff. The receipt is [`free-pair.json`](https://github.com/wcook04/plectis-erdos/blob/dd6cc708f650f061de06594eba6ba43878f4de31/research/experiments/erdos251/receipts/free-pair.json). The [public computation guide](https://github.com/wcook04/plectis-erdos/blob/dd6cc708f650f061de06594eba6ba43878f4de31/research/experiments/erdos251/README.md) provides the programs, dependencies and exact replay commands for all three recorded runs, including the continued-fraction calculation above.

<a id="long251:sec:open"></a>

# The remaining obligation

Problem #251 is open. The exact unresolved condition, equivalent to irrationality by Theorem <a href="#long251:res:escape-irrational" data-reference-type="ref" data-reference="long251:res:escape-irrational">9</a> and the escape equivalence for the actual tail, is the following.

<div id="long251:prob:escape" class="problem">

**Problem 32** (universal prime-gap shift escape). For every $`h\ge1`$ and every $`N_0`$, prove that some $`N\ge N_0`$ satisfies
``` math
\begin{equation}
 \sum_{j\ge1}\frac{g_{N+h+j}-g_{N+j}}{2^{\,j}}\notin\mathbb{Z}.
\label{long251:eq:shift-escape}\ltx@label{eq:shift-escape}
\end{equation}
```

</div>

<div id="long251:prob:smallpair" class="problem">

**Problem 33** (cofinal adjacent small mismatch). For every $`h\ge1`$ and every $`N_0`$, prove that some $`N\ge N_0`$ satisfies
``` math
\begin{equation}
 \bigl|\sigma_h(N)\bigr|<1,\qquad
 \bigl|\sigma_h(N+1)\bigr|<1,\qquad
 g_{N+h+1}\ne g_{N+1} .
\label{long251:eq:smallpair}
\end{equation}
```

</div>

Corollary <a href="#long251:res:smallpair-real" data-reference-type="ref" data-reference="long251:res:smallpair-real">14</a> makes Problem <a href="#long251:prob:smallpair" data-reference-type="ref" data-reference="long251:prob:smallpair">33</a> sufficient for Problem <a href="#long251:prob:escape" data-reference-type="ref" data-reference="long251:prob:escape">32</a>, and Theorem <a href="#long251:res:freepair" data-reference-type="ref" data-reference="long251:res:freepair">11</a> supplies an equivalent target in which the offset is free. The three formulations are equivalent or ordered by implication; none of them is an analytic saving on its own.

What the proved obstructions leave. By Theorem <a href="#long251:res:boundedperturbation" data-reference-type="ref" data-reference="long251:res:boundedperturbation">22</a> no hypothesis stable under bounded residue-preserving perturbation can work; by Corollary <a href="#long251:res:nonconc-primes" data-reference-type="ref" data-reference="long251:res:nonconc-primes">25</a> adding fixed-block polynomial nonconcentration to that list does not repair it; the construction in Section <a href="#long251:res:all-residue-log-countermodel" data-reference-type="ref" data-reference="long251:res:all-residue-log-countermodel">8.5</a> shows that recurring gap values differing by $`2`$ in every residue class do not work at the level of integer recurrences; and by Theorem <a href="#long251:res:sparse" data-reference-type="ref" data-reference="long251:res:sparse">28</a> the event in <a href="#long251:eq:smallpair" data-reference-type="eqref" data-reference="long251:eq:smallpair">[long251:eq:smallpair]</a> has density zero, so it must be produced cofinally on a sparse set. Isolated small gaps, isolated large gaps and average gap estimates are insufficient. Any prescribed finite prefix can be preserved while the complete sum is rationalised, so that prefix alone cannot force irrationality or a cofinal small-tail producer. A finite block together with a proved tail bound can still certify one window: both inequalities in <a href="#long251:eq:smallpair" data-reference-type="eqref" data-reference="long251:eq:smallpair">[long251:eq:smallpair]</a> contain the complete infinite continuation, and Proposition <a href="#long251:res:explicit-remainder" data-reference-type="ref" data-reference="long251:res:explicit-remainder">17</a> supplies the corresponding finite reduction. Nor does parity help, since after the first gap every $`g_n`$ is even.

The finite reduction is available. Proposition <a href="#long251:res:explicit-remainder" data-reference-type="ref" data-reference="long251:res:explicit-remainder">17</a> turns each window condition into an integer comparison at truncation length $`L`$, and for fixed $`h`$ and $`\varepsilon>0`$ the choice $`L=\lceil(4+\varepsilon)\log_2(N+2)\rceil`$ makes $`E_{h,N,L}=O_h(N^{-\varepsilon})`$. A prescribed positive margin $`\eta_h`$ therefore converts <a href="#long251:eq:smallpair" data-reference-type="eqref" data-reference="long251:eq:smallpair">[long251:eq:smallpair]</a> into the stronger task of producing the corresponding fixed-margin finite-block events. Strict open-window membership alone need not supply such a fixed margin. The finite event concerns the joint distribution modulo powers of two of the block $`(g_{N+h+1}-g_{N+1},\ldots,g_{N+h+L}-g_{N+L})`$ over a window of logarithmic length. Deciding one instance costs $`O(\log N)`$ gaps together with the elementary prime bound; producing certified witnesses beyond every cutoff, for each fixed $`h`$, is the unproved input. Uniform constants simultaneously in all $`h`$ are not required by the irrationality criterion.

The following published results on prime gaps address a different shape of question. Zhang’s bounded-gap theorem \[zhang2014, Theorem 1, p. 1122\] produces infinitely many bounded consecutive-prime gaps. Maynard bounds $`\liminf_n(p_{n+m}-p_n)`$ for every fixed $`m`$, giving bounded clusters of every fixed size \[maynard2015, Theorem 1.1, p. 384\], with the explicit unconditional bound $`\liminf_n(p_{n+1}-p_n)\le600`$ \[maynard2015, Theorem 1.3, p. 385\]. Polymath subsequently improved this to $`246`$ \[polymath2014, Theorem 1.4(i) of arXiv v4\]; neither numerical bound controls the signed weighted tails required here. The large-gap theorem of Ford, Green, Konyagin, Maynard and Tao gives an effective lower bound for the largest single consecutive-prime gap below $`X`$ \[fgkmt2018, Theorem 1\]. A theorem giving bounded clusters at each fixed cluster size does not by itself supply a weighted condition on windows whose length grows with the basepoint, and none of these results is used as a proof input here.

Conditionally the picture is different. Tao’s comment names uniform quantitative prime-tuples control of about $`\log\log n`$ consecutive gaps as the plausible route \[erdosproblems251thread, comment of 7 October 2025\], and Land’s draft carries that out under Kuperberg’s uniform prime-tuples conjecture \[land2026\]. The obstructions of Section <a href="#long251:sec:obstructions" data-reference-type="ref" data-reference="long251:sec:obstructions">8</a> say which unconditional substitutes cannot replace that hypothesis.

<a id="verification-boundary."></a>

#### Verification boundary.

Ordinary proofs, exact executable certificates and checked proof statements are distinct evidence types. The supplied declaration index already contains formal source for some results previously described as having no Lean declaration, but source availability need not mean inclusion in the checked build. Use the per-declaration status ledger rather than that obsolete blanket claim. In particular, the larger continued-fraction computation is not promoted to a kernel-decided result merely by the existence of its verification code. The smaller kernel-decided denominator floor and the larger exact-arithmetic exclusion have different evidence types and different numerical strengths.

<a id="statements-and-declarations"></a>

## Statements and declarations

<a id="artefact-and-data-availability."></a>

#### Artefact and data availability.

Declaration links identify immutable revisions, not a live branch. The public source revision is `3d6d938d696f`; release-only declarations are linked to `52f29ad173b0`. The supplied declaration index distinguishes `ci_checked`, `outside_checked_build`, and `release_only`; presence of a file or link alone is not evidence that its proof was checked. The supplied public CI receipt is [run 35073961520](https://github.com/wcook04/plectis-erdos/actions/runs/35073961520). The companion verification ledger records the precise declaration status. This revision replayed `lake build ErdosProblems Erdos249257` on Lean 4.29.1; no new \#251 endpoints were admitted beyond that replay.

Lean 4 \[lean4\] and mathlib \[mathlib\] provide the proof-checking environment. A checked proof statement, its hypotheses and its transitive axiom report must be distinguished from a challenge containing `sorry`, an executable certificate, or an ordinary proof. Formal checking does not establish novelty, attribution, or the faithfulness of an unexamined mathematical interpretation.

The finite-computation receipts and generating programs remain separately identified in the [pinned computation guide](https://github.com/wcook04/plectis-erdos/blob/dd6cc708f650f061de06594eba6ba43878f4de31/research/experiments/erdos251/README.md). The revision packet additionally supplies an independent integer replay of the adjacent-window certificate and the denominator exclusion $`q\ge2^{39997}`$. That replay is not a Lean check and does not authenticate the original continued-fraction run.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem numbering follows the Erdős Problems catalogue maintained by Thomas Bloom \[erdosproblems\]. The logarithmic-scale construction and nonconcentration transfer are retained from the earlier review materials accompanying this project. That provenance does not constitute an independent specialist endorsement of the manuscripts. No such endorsement is claimed. Any named acknowledgement for future correspondence requires the contributor’s permission.

<a id="long251:app:prime-bound"></a>

# An elementary polynomial bound for the primes

We prove $`p_n\le1250(n+1)^4`$ for every $`n\ge0`$ by the central binomial coefficient method of Erdős’s proof of Chebyshev’s theorem \[erdos1932, §1, pp. 194–196\]. Let $`\pi(x)`$ count the primes at most $`x`$. For an integer $`m\ge4`$,
``` math
\begin{equation}
\label{long251:eq:binomial-bound}
 4^m<m\binom{2m}{m}\le m(2m)^{\pi(2m)} .
\end{equation}
```
For the first inequality, $`m\binom{2m}{m}/4^{m}`$ equals $`70/64`$ at $`m=4`$ and its ratio at successive indices is $`(2m+1)/(2m)>1`$. For the second, the exponent of a prime $`\ell`$ in $`\binom{2m}{m}`$ is $`\sum_{k\ge1}\bigl(\lfloor2m/\ell^{k}\rfloor-2\lfloor m/\ell^{k}\rfloor\bigr)`$, each summand is $`0`$ or $`1`$, and every summand with $`\ell^{k}>2m`$ vanishes; hence each prime power dividing $`\binom{2m}{m}`$ is at most $`2m`$, and there are $`\pi(2m)`$ of them.

Now fix $`n\ge0`$, put $`x=n+5`$ and $`m=x^4\ge625`$, and suppose $`\pi(2m)\le n`$. Since $`x\le2^{x}`$ and $`n+4(n+1)x=4x^2-15x-5\le2x^4`$,
``` math
m(2m)^{n}=2^{n}x^{4(n+1)}
 \le2^{\,n+4(n+1)x}\le2^{\,2x^4}=4^{m},
```
contradicting <a href="#long251:eq:binomial-bound" data-reference-type="eqref" data-reference="long251:eq:binomial-bound">[long251:eq:binomial-bound]</a>. Hence $`\pi(2m)>n`$, so at least $`n+1`$ primes lie below $`2m`$ and therefore
``` math
p_n\le2(n+5)^4\le1250(n+1)^4 ,
```
the last step because $`(n+5)\le5(n+1)`$ for $`n\ge0`$. The same bound is checked by the kernel at [line 360](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L360).

<a id="long251:app:certificates"></a>

# Integer certificates

The following calculation uses trial division and integer arithmetic only. It reproduces the two rows of Proposition <a href="#long251:res:finite-smallpair" data-reference-type="ref" data-reference="long251:res:finite-smallpair">18</a> and every inequality used in Theorem <a href="#long251:res:denominatorfloor" data-reference-type="ref" data-reference="long251:res:denominatorfloor">20</a>. The four literals are the certificate the Lean kernel decides in `KernelDenominatorFloor.lean`; their use here requires no floating-point approximation. Adjacent quoted strings are concatenated by Python.

    from math import isqrt

    primes = [n for n in range(2, 10000)
              if all(n % d for d in range(2, isqrt(n) + 1))]
    gaps = [q - p for p, q in zip(primes, primes[1:])]
    P = lambda x: x**4 + 8*x**3 + 36*x*x + 104*x + 150
    Q = 2**40
    expected = [(-662838684750, 11764181250),
                (873345886050, 12805761250)]
    for N, target in zip((2, 3), expected):
        D = sum((gaps[N+1+j] - gaps[N+j])*2**(40-j)
                for j in range(1, 41))
        B = 1250*(P(N+43) + P(N+42))
        distance = min(D % Q, Q - D % Q)
        if (D, B) != target or not (abs(D)+B < Q and B < distance):
            raise ArithmeticError("tail certificate failed")
    if gaps[4] == gaps[3]:
        raise ArithmeticError("gap mismatch failed")

    u = int(
        "8065641857152652932176019632186898003271162829171466334827"
        "3083607794415278717445033509407855988903369988525550746159"
        "7355889792250084202344821020139160956663658789718168152662"
        "0217"
    )

    v = int(
        "2194945124413663232143970924541263312422069524635615360518"
        "4247077351958221816830720189289904831662955084392690248683"
        "1216291723988537733235173040607254496838530213867781442335"
        "1745"
    )

    up = int(
        "6539437101498162626882411892470905222108260008568555445975"
        "3026163315521784668689909712759876562484620059098138417469"
        "5232839888185316374272333277389611483117334000493867584923"
        "912"
    )

    vp = int(
        "1779611075789866551198427241621709630120136323281598176637"
        "8490605249229735501968764904036152970729491656650873938580"
        "6203025466313389810291243786005499164537499383612081805160"
        "767"
    )

    c = len(primes)
    A = sum(p*2**(c-1-i) for i, p in enumerate(primes))
    checks = (c == 1229,
              u > 0 and v > 0 and up > 0 and vp > 0,
              up*v - u*vp == 1,
              u*2**c < A*v,
              (2*A + 5000*(c+1)**4)*vp < up*2**(c+1),
              v+vp >= 2**589,
              2**589 > 10**177)
    if not all(checks):
        raise ArithmeticError("denominator certificate failed")
    print("Both tail rows and the denominator floor verified.")

<a id="long251:app:index"></a>

# Guide to the formal sources

Each link identifies its own immutable source revision. Named declaration links have been refreshed from the supplied checked index; historical computation links retain their separate receipt pins. The summation-by-parts and prime-bound declarations are prime-specific. Section <a href="#long251:sec:tail" data-reference-type="ref" data-reference="long251:sec:tail">5</a> is stated for arbitrary integer digits and arbitrary rational or real orbits, while Section <a href="#long251:sec:local-certificate" data-reference-type="ref" data-reference="long251:sec:local-certificate">6</a> records the actual-gap specialisation. The concrete prime-gap tail, its unconditional convergence, its recurrence and the real-to-rational scaled-tail bridge are defined and checked in `RealPrimeGapTail.lean` and `PrimeGapDyadicTail.lean`; the free-pair lattice and its actual-series equivalence in `FreePairReduction.lean`; the kernel-decided denominator certificate in `KernelDenominatorFloor.lean`; the rational countermodels in `BoundedPerturbationCountermodel.lean` and `PolynomialGapSeriesValue.lean`; and the two circularity theorems in `AffineCylinderCollapse.lean`, with the signed normal form in `AffineShiftEscape.lean` and the lcm diagonal in `OrderLatticeDiagonal.lean`.

<a id="long251:sec:erdos-251-extended-record"></a>

# Extended record: displaced results, ordinary proofs and corrections

This section holds mathematics that belongs to the complete record for Problem #251 and sits outside the short note. Every statement here is labelled by its evidence class in the same vocabulary the note uses.

<a id="long251:sec:xr-totient"></a>

## The totient witness and forward propagation

The note states the exact denominator law <a href="#long251:eq:den-law" data-reference-type="eqref" data-reference="long251:eq:den-law">[long251:eq:den-law]</a> and uses it directly. The classical witness that produced it is worth recording, because it is the form in which the shift length first appears.

<div id="long251:xr:totient" class="proposition">

**Proposition 34** (a shift of totient length). *Let $`T:\mathbb{N}\to\mathbb{Q}`$ satisfy the dyadic tail recurrence with integer digits. If the reduced denominator $`d`$ of $`T_N`$ is odd, then $`\sigma_{\varphi(d)}(N)`$ is an integer.*

</div>

<div class="proof">

*Proof.* Since $`d`$ is odd, $`2`$ and $`d`$ are coprime, so Euler’s congruence gives $`d\mid2^{\varphi(d)}-1`$. Writing $`2^{\varphi(d)}-1=dk`$ and $`T_N=u/d`$ in lowest terms, $`(2^{\varphi(d)}-1)T_N=ku`$ is an integer, and the integral-shift criterion transfers this to the shift. ◻

</div>

<div id="long251:xr:propagate" class="proposition">

**Proposition 35** (propagation). *Let $`T:\mathbb{N}\to\mathbb{R}`$ satisfy $`T_{n+1}=2T_n-a_{n+1}`$ with integer digits, and define $`\sigma_h(N)=T_{N+h}-T_N`$. For fixed $`h,N\ge0`$, if $`\sigma_h(N)`$ is an integer, then $`\sigma_h(N+k)`$ is an integer for every $`k\ge0`$.*

</div>

<div class="proof">

*Proof.* The shift step identity gives $`\sigma_h(N+1)=2\sigma_h(N)-(g_{N+h+1}-g_{N+1})`$, an integer combination of an integer and two digits. Induct on $`k`$. ◻

</div>

These are the totient shift and the propagation theorems cited in the note. Two worked instances. If $`\operatorname{den}T_N=3`$ then $`\varphi(3)=2`$ and $`3T_N`$ is an integer, so $`\sigma_2(N)`$ is integral while $`\sigma_1(N)`$ is not; if $`\operatorname{den}T_N=5`$ then $`\sigma_4(N)`$ is integral. In the orbit with every digit zero and $`T_0=1/12`$, the denominator is $`12=2^2\cdot3`$, the orbit reaches $`T_2=1/3`$ with odd denominator at $`s=2`$, and $`h=\varphi(3)=2`$ is exactly the shift length seen to be integral from index $`2`$ onwards. The totient is a witness rather than the classification: the exact criterion is $`\operatorname{den}(T_N)\mid2^{h}-1`$, and the least admissible $`h`$ is the multiplicative order of $`2`$ modulo the odd part.

<a id="long251:sec:xr-truncation"></a>

## The finite truncation criterion

The note gives the explicit remainder bound for the actual gaps. The general truncation statement behind it, valid for any dominating majorant, is the following.

<div id="long251:xr:truncation" class="proposition">

**Proposition 36** (finite truncation). *Let $`M(n)\ge g_n`$ for every $`n`$, assume the series below converges, and put
``` math
S_{h,N,L}=\sum_{j=1}^{L}\frac{g_{N+h+j}-g_{N+j}}{2^{\,j}},\qquad
 R_{h,N,L}(M)=\sum_{j>L}\frac{M(N+h+j)+M(N+j)}{2^{\,j}} .
```
If for every $`h\ge1`$ and every $`N_0`$ there are $`N\ge N_0`$ and $`L\ge1`$ with $`\operatorname{dist}(S_{h,N,L},\mathbb{Z})>R_{h,N,L}(M)`$, then the universal shift escape of Problem <a href="#long251:prob:escape" data-reference-type="ref" data-reference="long251:prob:escape">32</a> holds.*

</div>

<div class="proof">

*Proof.* The part of $`\sum_{j\ge1}(g_{N+h+j}-g_{N+j})2^{-j}`$ omitted from $`S_{h,N,L}`$ has absolute value at most $`R_{h,N,L}(M)`$, so under the displayed inequality the full sum lies at positive distance from every integer. ◻

</div>

The truncation is an exact modular small-arc problem. Writing the integral dyadic block
``` math
D_{h,N,L}=\sum_{j=1}^{L}2^{\,L-j}(g_{N+h+j}-g_{N+j}),
 \qquad S_{h,N,L}=\frac{D_{h,N,L}}{2^{L}},
```
one has
``` math
\operatorname{dist}(S_{h,N,L},\mathbb{Z})
 =2^{-L}\min\bigl\{D_{h,N,L}\bmod2^{L},\;
 2^{L}-(D_{h,N,L}\bmod2^{L})\bigr\},
```
where $`D_{h,N,L}\bmod2^{L}`$ is the least nonnegative residue, including when $`D_{h,N,L}<0`$. The finite criterion therefore asks the residue of $`D_{h,N,L}`$ to avoid the two arcs of radius $`2^{L}R_{h,N,L}(M)`$ around $`0`$ modulo $`2^{L}`$. A one-block certificate would be a prime-gap theorem producing such an avoided arc on a logarithmic block. This rewriting is paper-level and carries no Lean declaration.

<div id="long251:res:complete-truncation" class="proposition">

**Proposition 37** (completeness of finite separation). *Suppose $`D\in\mathbb{R}`$, $`S_L\in\mathbb{R}`$ and $`R_L\ge0`$ satisfy $`|D-S_L|\le R_L`$ and $`R_L\to0`$. Then
``` math
D\notin\mathbb{Z}\quad\Longleftrightarrow\quad
 \text{there exists }L\text{ with }\operatorname{dist}(S_L,\mathbb{Z})>R_L.
```*

</div>

<div class="proof">

*Proof.* The reverse implication follows from the triangle inequality. For the forward implication put $`\delta=\operatorname{dist}(D,\mathbb{Z})>0`$ and choose $`R_L<\delta/2`$. The distance to $`\mathbb{Z}`$ is $`1`$-Lipschitz, so $`\operatorname{dist}(S_L,\mathbb{Z})\ge\delta-R_L>R_L`$. ◻

</div>

Thus existence of an arbitrarily deep finite certificate is an exact reformulation of nonintegrality, not a new prime-gap estimate. A useful analytic producer must control the separation as well as the tail.

<a id="long251:sec:xr-divisorhit"></a>

## Divisor-hitting shift escape

<div id="long251:xr:divisor-hit" class="problem">

**Problem 38** (divisor-hitting shift escape). For every $`r\ge1`$, does some positive multiple of $`r`$ escape cofinally, in the sense of <a href="#long251:eq:shift-escape" data-reference-type="eqref" data-reference="long251:eq:shift-escape">[long251:eq:shift-escape]</a> at shift length $`mr`$ for some $`m\ge1`$?

</div>

This is an exact reformulation, not a weaker mathematical target. If $`T_0`$ is irrational, every positive shift is nonintegral by the block identity, so divisor-hitting escape follows with $`m=1`$. Conversely, rationality gives a shift $`h\ge1`$ that is integral at every sufficiently late index. For each positive integer $`m`$, the identity
``` math
T_{N+mh}-T_N=\sum_{j=0}^{m-1}(T_{N+(j+1)h}-T_{N+jh})
```
makes every multiple $`mh`$ eventually integral. Taking $`r=h`$ contradicts divisor-hitting escape. This ordinary deduction uses the checked rationality classification and a finite telescope; rearranging the quantifiers supplies no new estimate for the actual prime gaps.

<a id="long251:sec:xr-compression"></a>

## Two ordinary proofs about the free-pair producer

Both arguments below are ordinary mathematical deductions. The first uses the prime number theorem, while the second consumes the free-pair lattice proved above. Neither deduction is claimed to be kernel-checked; the exact tail recurrence and free-pair statements they use have their separate linked Lean evidence.

<a id="state-compression."></a>

#### State compression.

Exchanging the order of summation gives $`\sum_{N\le X}T_N\le(p_{X+1}-p_0)+2T_X`$. The prime number theorem \[mv2007, Ch. 6\] also gives
``` math
\begin{equation}
\label{long251:eq:tail-small-relative-prime}
 \frac{T_X}{p_X}
 =\sum_{j\ge1}\frac{g_{X+j}}{2^jp_X}\longrightarrow0.
\end{equation}
```
Indeed, for each fixed $`j`$ the summand without $`2^{-j}`$ tends to zero because $`p_{X+j}/p_X\to1`$. The usual two-sided bounds $`p_n\asymp n\log n`$ dominate $`g_{X+j}/p_X`$ by $`K(1+j)^2`$, independently of $`X`$; multiplication by $`2^{-j}`$ therefore permits dominated convergence. Applying the first-moment bound at $`2X`$ and using <a href="#long251:eq:tail-small-relative-prime" data-reference-type="eqref" data-reference="long251:eq:tail-small-relative-prime">[long251:eq:tail-small-relative-prime]</a>, there is an absolute $`K_0`$ such that
``` math
\sum_{X<N\le2X}T_N\le K_0X\log X
```
for all large $`X`$. Thus, for each fixed $`C>1`$, Markov’s inequality leaves at least $`(1-1/C)X`$ indices in $`(X,2X]`$ with $`T_N\le K_0C\log X`$.

Under rationality, take $`X`$ beyond the point where the reduced denominator is the fixed odd integer $`d`$. On this set $`T_N`$ lies in $`d^{-1}\mathbb{Z}_{\ge0}`$ and takes at most $`dK_0C\log X+1`$ values. Pigeonhole therefore gives one value at $`\gg_{C,d}X/\log X`$ indices. This compression uses the growth of the actual primes. It is false for a general rational integer-digit orbit: the quadratic countermodel of Proposition <a href="#long251:res:polynomialcountermodel" data-reference-type="ref" data-reference="long251:res:polynomialcountermodel">30</a> has the strictly increasing tails $`T_N=2(N+4)^2`$. Even for the primes, equal-tail pairs have difference zero and hence do not supply the nonintegral difference required by the free-pair criterion. The naive form $`\sum_{N\le X}T_N\le p_{X+1}`$ is false.

<a id="redundancy-of-the-gap-condition."></a>

#### Redundancy of the gap condition.

Under the free-pair lattice the difference $`T_M-T_N`$ is an integer whenever the modulus divides the offset, and an integer cannot lie in $`(\tfrac12,1)`$. The half-window component of the reduced event of Theorem <a href="#long251:res:signedwindow" data-reference-type="ref" data-reference="long251:res:signedwindow">16</a> is therefore already a contradiction on its own, and the gap-mismatch condition adds nothing to it. That changes which component a proof has to produce.

<a id="long251:sec:xr-boundedpolignac"></a>

## A bounded companion to the recurring-values countermodel

Theorem <a href="#long251:res:polignacfail" data-reference-type="ref" data-reference="long251:res:polignacfail">29</a> carries a logarithmic growth profile so that its cumulative sequence matches the primes. The mechanism is visible in a much smaller example, which is recorded here because it is checkable by hand.

<div id="long251:xr:boundedpolignac" class="proposition">

**Proposition 39** (bounded recurring-values countermodel). *Put $`U_0=4`$ and, for $`n\ge1`$, $`U_n=6`$ when $`n=k!`$ for some $`k\ge3`$ and $`U_n=4`$ otherwise, and set $`a_n=2U_{n-1}-U_n`$ for $`n\ge1`$. Then $`a_n\in\{2,4,8\}`$, the value $`2`$ occurs at every index $`k!`$ and the value $`4`$ at every index $`2\,k!`$, so both recur infinitely often at indices divisible by any fixed $`t\ge1`$. The series $`\sum_{n\ge1}a_n2^{-n}`$ equals $`4`$ and every tail $`\sum_{j\ge1}a_{N+j}2^{-j}`$ equals the integer $`U_N`$.*

</div>

<div class="proof">

*Proof.* For $`k\ge3`$ the index $`k!`$ is even and at least $`6`$, and $`k!-1`$ is odd, so the predecessor of a spike is an ordinary index; hence $`a_{k!}=8-6=2`$, $`a_{k!+1}=12-4=8`$, and $`a_n=8-4=4`$ elsewhere. For $`k\ge2`$ one has $`k!<2\,k!<(k+1)!`$, so $`2\,k!`$ is not a factorial, and $`2\,k!-1`$ is odd so it is not a factorial either; therefore $`a_{2k!}=4`$. Since $`t\mid k!`$ for every large $`k`$, both values recur in the residue class $`0`$ modulo $`t`$. The identity $`a_n2^{-n}=U_{n-1}2^{-(n-1)}-U_n2^{-n}`$ telescopes to $`\sum_{j=1}^{m}a_{N+j}2^{-j}=U_N-U_{N+m}2^{-m}`$, and $`U`$ is bounded, so the endpoint vanishes. ◻

</div>

The cumulative sequence of this word grows linearly, which is the one property that separates it from the primes and the reason the note carries the logarithmic version instead. Both refute the same generic implication.

<a id="long251:sec:xr-densities"></a>

## The measured densities in full

The note reports the range of the adjacent-mismatch density. The per-offset figures below come from the same scan over the $`6\,841\,648`$ primes under $`1.2\times10^{8}`$, with double-precision tails.

<div class="center">

| $`h`$ | events |  density | $`\delta=+2`$ | $`\delta=-2`$ | last event at prime |
|------:|-------:|---------:|--------------:|--------------:|--------------------:|
|     1 | 56 427 | 0.008248 |        28 022 |        28 405 |         119 995 753 |
|     2 | 31 979 | 0.004674 |        15 742 |        16 237 |         119 993 807 |
|     3 | 30 233 | 0.004419 |        15 093 |        15 140 |         119 998 321 |
|     4 | 29 262 | 0.004277 |        14 606 |        14 656 |         119 993 473 |

</div>

Every offset $`h\le16`$ has events, with minimum density $`0.00418`$ and maximum $`0.008248`$; the two signs are near balanced at every offset. For $`h=1`$ the eight band densities, and the same figures after rescaling by the band mean of $`\log p`$, run
``` math
\begin{array}{l}
 0.011285,\;0.008951,\;0.008303,\;0.007936,\;0.007651,\;0.007507,\;0.007253,\;0.007094;\\[2pt]
 0.17671,\;0.15058,\;0.14420,\;0.14067,\;0.13766,\;0.13667,\;0.13333,\;0.13148 .
\end{array}
```
The rescaled drift is $`0.744`$ at $`h=1`$ and lies between $`0.744`$ and $`0.8121`$ across all offsets. Theorem <a href="#long251:res:sparse" data-reference-type="ref" data-reference="long251:res:sparse">28</a> proves that the limiting density is zero, so the observed decline is the expected behaviour rather than a failure of the event.

<a id="long251:sec:xr-corrections"></a>

## Corrections to earlier records

<a id="two-different-improvements-to-the-exclusion-record."></a>

#### Two different improvements to the exclusion record.

An earlier internal record gave a denominator exclusion at $`10^{602}`$. The kernel-decided floor $`2^{589}>10^{177}`$ of Theorem <a href="#long251:res:denominatorfloor" data-reference-type="ref" data-reference="long251:res:denominatorfloor">20</a> is numerically smaller but has a different verification status. It does not supersede $`10^{602}`$ in numerical strength. The continued-fraction exclusion $`2^{39997}>10^{12040}`$ of Theorem <a href="#long251:res:cfexclusion" data-reference-type="ref" data-reference="long251:res:cfexclusion">21</a> is the larger numerical bound. Its receipt’s digit count $`12041`$ must not be substituted for the exponent $`12040`$. The independent integer replay supplied with this revision reproduces the stated larger exclusion by a separate interval and Farey-neighbour calculation; it is not a new Lean replay.

<a id="the-named-missing-input."></a>

#### The named missing input.

An earlier record named Hardy-Littlewood $`k`$-tuple correlation of consecutive gaps at a fixed offset as the missing input. With the offset freed by Theorem <a href="#long251:res:freepair" data-reference-type="ref" data-reference="long251:res:freepair">11</a> the route needs, for each modulus $`t`$, cofinally many congruent pairs with certified nonintegral tail difference. A further record proposed that two even values differing by $`2`$, each occurring infinitely often inside a common index residue class, would supply the two-condition form. No proof of that implication was ever produced, and Theorem <a href="#long251:res:polignacfail" data-reference-type="ref" data-reference="long251:res:polignacfail">29</a> shows that no proof exists at the level of integer-digit recurrences. That entry is withdrawn.

<a id="the-formal-boundary."></a>

#### The formal boundary.

An earlier reading of the short note placed the real-tail bridge and the real form of the adjacent-pair consumer on the paper side. Both are kernel-checked, at [line 48](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L48) and [line 99](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L99) of the real prime-gap tail module. A second reading placed the kernel-decided denominator floor and the free-pair criterion outside the source revision the note pins. Both modules are present at that revision, and both are linked from the note.

<a id="long251:app:affine-detail"></a>

# Complete affine-lattice statement from the short note

The following expands the compact circularity statement formerly printed in the body of this record. In particular the fixed-lattice predicate and its strict growth hypothesis are stated, not left implicit.

Here $`D_N=\sigma_h(N)`$ and $`\delta_N=g_{N+h+1}-g_{N+1}`$, with $`h`$ fixed. For a longer block, set
``` math
B_{h,N,r}=\sum_{i=0}^{r-1}2^{r-1-i}\delta_{N+i};
 \qquad D_{N+r}=2^rD_N-B_{h,N,r}.
```
Call the data-dependent affine condition
``` math
\mathcal A_{N,r}:\qquad
 D_{N+r}\in -B_{h,N,r}+2^{r+1}\mathbb{Z}.
```

<div id="long251:res:affinecollapse" class="theorem">

**Theorem 40** (affine and fixed-lattice circularity). *For every rational dyadic tail recurrence and all $`h,N,r\ge0`$,
``` math
\begin{equation}
 \mathcal A_{N,r}\quad\Longleftrightarrow\quad D_N\in2\mathbb{Z}.
\label{eq:affinecollapse}\ltx@label{long251:eq:affinecollapse}
\end{equation}
```
Consequently, if every $`\delta_N`$ is even, then
``` math
\begin{equation}
 \bigl(\forall N_0\ \exists N,r:\ N_0<N\text{ and }\neg\mathcal A_{N,r}\bigr)
 \quad\Longleftrightarrow\quad
 D_N\notin\mathbb{Z}\text{ for arbitrarily large }N.
\label{eq:affinecofinal}\ltx@label{long251:eq:affinecofinal}
\end{equation}
```*

*There is a second equivalence. Let $`b:\mathbb{N}\to\mathbb{Q}`$ satisfy $`|D_N|\le b(N)`$ for every $`N`$, and suppose that for every $`N`$ and every positive integer $`q`$ there is an $`r`$ with
``` math
\begin{equation}
 2b(N+r)q<2^r.
\label{eq:dyadicscale}\ltx@label{long251:eq:dyadicscale}
\end{equation}
```
Then
``` math
\begin{equation}
 \begin{split}
 &\forall N_0\ \exists N,r:\ N_0<N\text{ and }
   \forall z\in\mathbb{Z},\quad
   b(N+r)<|B_{h,N,r}-2^rz|\\
 &\hspace{35mm}\Longleftrightarrow\quad
 D_N\notin\mathbb{Z}\text{ for arbitrarily large }N.
 \end{split}
\label{eq:fixedcollapse}\ltx@label{long251:eq:fixedcollapse}
\end{equation}
```*

</div>

<div class="proof">

*Proof.* Substituting $`D_{N+r}=2^rD_N-B_{h,N,r}`$ into $`\mathcal A_{N,r}`$ cancels the observed block from both sides and leaves $`D_N=2z`$. This proves <a href="#long251:eq:affinecollapse" data-reference-type="eqref" data-reference="long251:eq:affinecollapse">[long251:eq:affinecollapse]</a>. After one recurrence step, evenness of $`\delta_N`$ identifies even integrality at $`N+1`$ with ordinary integrality at $`N`$. The forward implication in <a href="#long251:eq:affinecofinal" data-reference-type="eqref" data-reference="long251:eq:affinecofinal">[long251:eq:affinecofinal]</a> follows, while the reverse implication chooses a nonintegral $`D_N`$ and the legal depth $`r=0`$.

For <a href="#long251:eq:fixedcollapse" data-reference-type="eqref" data-reference="long251:eq:fixedcollapse">[long251:eq:fixedcollapse]</a>, eventual integrality and the block identity give some $`z\in\mathbb{Z}`$ with
``` math
B_{h,N,r}-2^rz=-D_{N+r},
```
so the displayed strict separation contradicts $`|D_{N+r}|\le b(N+r)`$. Conversely, if $`D_N`$ is nonintegral and has reduced denominator $`q`$, then its distance from every integer is at least $`1/q`$. Choose $`r`$ from <a href="#long251:eq:dyadicscale" data-reference-type="eqref" data-reference="long251:eq:dyadicscale">[long251:eq:dyadicscale]</a>, scale this separation by $`2^r`$, and use the block identity together with $`|D_{N+r}|\le b(N+r)`$. The triangle inequality gives $`|B_{h,N,r}-2^rz|>b(N+r)`$ for every integer $`z`$. ◻

</div>

The three displayed equivalences are assembled in one declaration, [affine circularity bundle](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L241).

The first equivalence shows that the apparent affine hierarchy contains no depth-dependent information: it is the pullback of even integrality through the recurrence identity. The fixed lattice removes that data dependence, but under the stated growth condition rational denominator separation already forces every required escape. Hence neither cofinal condition is an independent source of information about consecutive primes.

<a id="sec:erdos-251-complete-family-map"></a>

# Mathematical and evidence map

<a id="perturbations."></a>

#### Perturbations.

The bounded construction and the sparse congruence-preserving theorem are existence results for altered integer words. Their conclusion is not a prime-producing construction. The ordinary sparse proof and the formal existence proof have different witnesses.

<a id="exact-criteria."></a>

#### Exact criteria.

Summation by parts identifies the actual tails. Integral-shift, free-pair and lcm-diagonal criteria then classify rationality at the recurrence level. Their equivalence does not supply the missing prime-specific witnesses.

<a id="obstructions."></a>

#### Obstructions.

Polynomial growth, bounded residues, fixed-block nonconcentration and recurring gap values do not by themselves force the needed tail behaviour. The numbered constructions above give the precise counterexamples.

<a id="certificates."></a>

#### Certificates.

Finite window comparisons and denominator exclusions are exact finite statements once the proved analytic remainder bounds are supplied. A large rational-denominator floor is not an irrationality theorem.

<a id="formal-evidence."></a>

#### Formal evidence.

The revision’s declaration ledger records the file, line, immutable revision and supplied build status of each linked declaration. The older administrative family catalogue is retained verbatim with that ledger; counts of registry rows or project-wide families do not strengthen any mathematical statement.

<div class="thebibliography">

99

Paul Erdős, [*Sur certaines séries à valeur irrationnelle*](https://users.renyi.hu/~p_erdos/1958-19.pdf). L’Enseignement Mathématique **4** (1958), 93–100, doi:[10.5169/seals-34629](https://doi.org/10.5169/seals-34629). Paul Erdős and Ronald L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf). Monographies de L’Enseignement Mathématique, L’Enseignement Mathématique, 1980. Paul Erdős and Carl Pomerance, [*On the largest prime factors of $`n`$ and $`n+1`$*](https://doi.org/10.1007/BF01818569). Aequationes Mathematicae **17** (1978), 311–321, doi:[10.1007/BF01818569](https://doi.org/10.1007/BF01818569). Paul Erdős, [*On the irrationality of certain series: problems and results*](https://doi.org/10.1017/CBO9780511897184.009). New Advances in Transcendence Theory, Cambridge University Press, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). Paul Erdős, [*Beweis eines Satzes von Tschebyschef*](https://users.renyi.hu/~p_erdos/1932-01.pdf). Acta Litterarum ac Scientiarum Szeged **5** (1932), 194–198. Paul Erdős and Ernst G. Straus, *On the irrationality of certain Ahmes series*. Journal of the Indian Mathematical Society (N.S.) **27** (1964), 129–133. Legacy citation key retained; supplied bibliography gives publication year 1964. MR0175848. Paul Erdős and Ernst G. Straus, [*On the irrationality of certain series*](https://doi.org/10.2140/pjm.1974.55.85). Pacific Journal of Mathematics **55** (1974), no. 1, 85–92, doi:[10.2140/pjm.1974.55.85](https://doi.org/10.2140/pjm.1974.55.85). Kevin Ford, Ben Green, Sergei Konyagin, James Maynard and Terence Tao, [*Long gaps between primes*](https://arxiv.org/abs/1412.5029v3). Journal of the American Mathematical Society **31** (2018), 65–105, doi:[10.1090/jams/876](https://doi.org/10.1090/jams/876); arXiv:[1412.5029v3](https://arxiv.org/abs/1412.5029v3). John A. Fridy, [*Generalized bases for the real numbers*](https://www.fq.math.ca/Scanned/4-3/fridy.pdf). The Fibonacci Quarterly **4** (1966), no. 3, 193–201. A. Ya. Khinchin, *Continued Fractions*. University of Chicago Press, 1964. Vjekoslav Kovač and Terence Tao, [*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593v4). Acta Mathematica Hungarica **175** (2025), 572–608, doi:[10.1007/s10474-025-01528-0](https://doi.org/10.1007/s10474-025-01528-0); arXiv:[2406.17593v4](https://arxiv.org/abs/2406.17593v4). Statement and section numbers refer to arXiv version 4; legacy citation key retained. Vivian Kuperberg, [*Sums of singular series with large sets and the tail of the distribution of primes*](https://arxiv.org/abs/2210.09775v2). The Quarterly Journal of Mathematics **74** (2023), no. 4, 1457–1479, doi:[10.1093/qmath/haad030](https://doi.org/10.1093/qmath/haad030); arXiv:[2210.09775v2](https://arxiv.org/abs/2210.09775v2). Statement numbers refer to arXiv version 2, 15 June 2023. Johan Land, [*A conditional proof of the irrationality of $`\sum_{n\ge1}p_n2^{-n}`$ under a uniform Hardy–Littlewood prime-tuples conjecture*](https://github.com/beetree/math_erdos_251). Research draft, 5 September 2026, 2026. The author supplies formalisation material. No independent rebuild is claimed in this revision. Leonardo de Moura and Sebastian Ullrich, [*The Lean 4 theorem prover and programming language*](https://doi.org/10.1007/978-3-030-79876-5_37). Automated Deduction – CADE 28, Lecture Notes in Computer Science, Springer, 2021, pp. 625–635, doi:[10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37). The mathlib Community, [*The Lean mathematical library*](https://doi.org/10.1145/3372885.3373824). Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs, ACM, 2020, pp. 367–381, doi:[10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). Describes a Lean 3-era snapshot; the repository lock identifies the library used by the present Lean 4 sources. James Maynard, [*Small gaps between primes*](https://doi.org/10.4007/annals.2015.181.1.7). Annals of Mathematics **181** (2015), 383–413, doi:[10.4007/annals.2015.181.1.7](https://doi.org/10.4007/annals.2015.181.1.7). Hugh L. Montgomery and Robert C. Vaughan, [*Multiplicative Number Theory I: Classical Theory*](https://doi.org/10.1017/CBO9780511618314). Cambridge Studies in Advanced Mathematics, Cambridge University Press, 2007, doi:[10.1017/CBO9780511618314](https://doi.org/10.1017/CBO9780511618314). Jan-Christoph Schlage-Puchta, [*The irrationality of some number theoretical series*](https://arxiv.org/abs/1105.1451v1). Acta Arithmetica **126** (2007), no. 4, 295–303, doi:[10.4064/aa126-4-1](https://doi.org/10.4064/aa126-4-1); arXiv:[1105.1451v1](https://arxiv.org/abs/1105.1451v1). Published in 2007; arXiv upload is from 2011. Lemma and preprint page locators refer to arXiv version 1; legacy citation key retained. Ian Short, [*Ford Circles, Continued Fractions, and Rational Approximation*](https://arxiv.org/abs/0912.1997v1). The American Mathematical Monthly **118** (2011), no. 2, 130–135, doi:[10.4169/amer.math.monthly.118.02.130](https://doi.org/10.4169/amer.math.monthly.118.02.130); arXiv:[0912.1997v1](https://arxiv.org/abs/0912.1997v1). Preprint title: Ford circles, continued fractions, and best approximation of the second kind. Preprint theorem locators refer to arXiv version 1; legacy citation key retained. Wouter van Doorn and Vjekoslav Kovač, [*Lacunary sequences whose reciprocal sums represent all rational numbers in an interval*](https://arxiv.org/abs/2509.24971v3). Acta Arithmetica **223** (2026), 275–295, doi:[10.4064/aa251001-13-1](https://doi.org/10.4064/aa251001-13-1); arXiv:[2509.24971v3](https://arxiv.org/abs/2509.24971v3). Statement numbers refer to arXiv version 3; legacy citation key retained. Yitang Zhang, [*Bounded gaps between primes*](https://doi.org/10.4007/annals.2014.179.3.7). Annals of Mathematics **179** (2014), 1121–1174, doi:[10.4007/annals.2014.179.3.7](https://doi.org/10.4007/annals.2014.179.3.7). Thomas F. Bloom, [*Erdős Problem \#251*](https://www.erdosproblems.com/251). 2026. Catalogue snapshot inherited from the supplied manuscript, accessed 6 September 2026. Live page was inaccessible to this revision on 16 September 2026; no refreshed global-status claim is inferred. Erdős Problems contributors, [*Erdős Problem \#251 discussion thread*](https://www.erdosproblems.com/forum/thread/251). 2026. Inherited snapshot accessed 6 September 2026: Tao comment of 7 October 2025 and Land comments of 6 September 2026. Live thread not reverified. ChatGPT 5.4 Pro (orchestrated by Vjeko Kovač), [*On the Erdős problem \#251*](https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_251.pdf). Unpublished note, Department of Mathematics, University of Zagreb, 2026. Printed attribution retained from the supplied bibliography; inherited access date 6 September 2026. The Formal Conjectures Authors, [*FormalConjectures.ErdosProblems.251*](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/251.lean). 2025. Pinned statement source, not a proof of Problem 251; inherited access date 28 July 2026. Stefan Ringer, [*Local gap statistics, telescoping, and normality: a local-pattern approach to Erdős problem 251*](https://github.com/StefanRinger/erdos-251). Preprint dated 11 September 2026, 2026. Mutable main-branch TeX consulted 16 September 2026. The author supplies formalisation material; this revision does not independently rebuild it. Tonći Crmarić and Vjekoslav Kovač, [*On the irrationality of certain super-polynomially decaying series*](https://arxiv.org/abs/2504.18712v1). Colloquium Mathematicum **179** (2025), 55–68, doi:[10.4064/cm9628-5-2025](https://doi.org/10.4064/cm9628-5-2025); arXiv:[2504.18712v1](https://arxiv.org/abs/2504.18712v1). Lemma 4 is cited using arXiv version 1. Boris Adamczewski, Michael Drmota and Clemens Müllner, [*(Logarithmic) densities for automatic sequences along primes and squares*](https://arxiv.org/abs/2009.14773v2). Transactions of the American Mathematical Society **375** (2022), no. 1, 455–499, doi:[10.1090/tran/8476](https://doi.org/10.1090/tran/8476); arXiv:[2009.14773v2](https://arxiv.org/abs/2009.14773v2). Theorems 1.2 and 1.4 refer to arXiv version 2, 13 April 2021; journal publication is 2022. Wouter van Doorn, [*Partitions with prescribed sum of reciprocals: asymptotic bounds*](https://arxiv.org/abs/2502.02200v2). 2025; arXiv:[2502.02200v2](https://arxiv.org/abs/2502.02200v2). Version 2, 23 July 2025. No journal publication was confirmed in this pass. Szymon Głąb and Franciszek Prus-Wiśniowski, [*Achievement sets – current results and open problems*](https://arxiv.org/abs/2512.17285v1). Real Analysis Exchange (2026), doi:[10.14321/realanalexch.1766383782](https://doi.org/10.14321/realanalexch.1766383782); arXiv:[2512.17285v1](https://arxiv.org/abs/2512.17285v1). Advance publication, first available in Project Euclid 8 June 2026. Consulted text remains arXiv:2512.17285v1 (19 December 2025); no final volume or page range was confirmed. Legacy citation key retained. Franciszek Prus-Wiśniowski and Jolanta Ptak, [*Achievable Cantorvals almost without reversed Kakeya conditions*](https://arxiv.org/abs/2412.08768v1). 2024; arXiv:[2412.08768v1](https://arxiv.org/abs/2412.08768v1). Version 1 submitted 11 December 2024. The sparse indices satisfy the overlap inequality, not its strict term-dominating reverse. Artur Bartoszewicz, Małgorzata Filipczak and Emilia Szymonik, [*Multigeometric sequences and Cantorvals*](https://arxiv.org/abs/1304.4218v2). Central European Journal of Mathematics **12** (2014), no. 7, 1000–1007, doi:[10.2478/s11533-013-0396-4](https://doi.org/10.2478/s11533-013-0396-4); arXiv:[1304.4218v2](https://arxiv.org/abs/1304.4218v2). Vivian Kuperberg, [*Sums of singular series along arithmetic progressions and with smooth weights*](https://arxiv.org/abs/2301.06095v1). International Journal of Number Theory **21** (2025), no. 1, 53–74, doi:[10.1142/S1793042125500046](https://doi.org/10.1142/S1793042125500046); arXiv:[2301.06095v1](https://arxiv.org/abs/2301.06095v1). Preprint uploaded 15 January 2023; journal publication is 2025. Abhishek Jha, [*The Poisson Tail Conjecture for primes in short intervals*](https://arxiv.org/abs/2605.23014v2). 2026; arXiv:[2605.23014v2](https://arxiv.org/abs/2605.23014v2). Substantially revised version 2, 12 September 2026, 31 pages. Conditional statements must retain their strong Hardy–Littlewood hypotheses. D. H. J. Polymath, [*Variants of the Selberg sieve, and bounded intervals containing many primes*](https://arxiv.org/abs/1407.4897v4). Research in the Mathematical Sciences **1** (2014), article 12, doi:[10.1186/s40687-014-0012-7](https://doi.org/10.1186/s40687-014-0012-7); arXiv:[1407.4897v4](https://arxiv.org/abs/1407.4897v4). Theorem 1.4(i) refers to arXiv version 4 (22 December 2014); the journal numbers it Theorem 4(i). An erratum is recorded at doi:10.1186/s40687-015-0033-x. Zbigniew Nitecki, [*Cantorvals and Subsum Sets of Null Sequences*](https://arxiv.org/abs/1106.3779v2). The American Mathematical Monthly **122** (2015), no. 9, 862–870, doi:[10.4169/amer.math.monthly.122.9.862](https://doi.org/10.4169/amer.math.monthly.122.9.862); arXiv:[1106.3779v2](https://arxiv.org/abs/1106.3779v2). Consulted preprint: Subsum Sets: Intervals, Cantor Sets, and Cantorvals, version 2 (8 July 2013). Theorem 14 is attributed there to Guthrie–Nymann; its locator is not journal pagination. Piotr Miska, Franciszek Prus-Wiśniowski and Jolanta Ptak, [*More on Kakeya Conditions for Achievement Sets*](https://ruj.uj.edu.pl/server/api/core/bitstreams/d6630f7b-e6ee-4de8-8a1b-81c7b4c59d2e/content). Results in Mathematics **78** (2023), article 113, doi:[10.1007/s00025-023-01890-x](https://doi.org/10.1007/s00025-023-01890-x). Repairs an estimate in the 2021 proof, preserving its uniqueness conclusion, and gives a simpler proof of a weaker theorem without that conclusion. Jacek Marchwicki and Piotr Miska, [*On Kakeya Conditions for Achievement Sets*](https://link.springer.com/article/10.1007/s00025-021-01479-2). Results in Mathematics **76** (2021), article 181, doi:[10.1007/s00025-021-01479-2](https://doi.org/10.1007/s00025-021-01479-2). Theorem 2.1 is to be read with the proof repair in Miska–Prus-Wiśniowski–Ptak (2023). Piotr Nowakowski, [*On a new condition implying that an achievement set is a Cantorval and its applications*](https://arxiv.org/abs/2512.17761v1). 2025; arXiv:[2512.17761v1](https://arxiv.org/abs/2512.17761v1). Version 1, 19 December 2025. Theorem 3.1 requires the Star Procedure of Definition 2 never to break; no application to the present factorial weights is asserted.

</div>
