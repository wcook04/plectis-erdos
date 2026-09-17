<a id="erdos-251-prime-gap-dyadic-series"></a>

# Sparse Congruence-Preserving Perturbations of Dyadic Series

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Let $`A=\sum_{n\ge0}a_n2^{-(n+1)}<\infty`$ with nonnegative integer coefficients. For every prescribed cutoff and every $`f(n)\to\infty`$, we construct a fixed support of upper Banach density zero and a fixed nondegenerate interval above $`A`$. Every point of that interval is realised by a nonnegative integer correction supported on this set and eventually bounded by $`f`$, while every fixed modulus eventually divides both the corrections and their cumulative sums. For $`f(n)=(\log(n+3))^\varepsilon`$, the empirical laws of literal gap blocks of length $`o(\log\log X)`$ are preserved in total variation. The construction combines finite-choice interval covering with congruence buffers. Applied to prime gaps, it shows that these congruence and block-law data, even together with fixed-block polynomial nonconcentration and the cumulative prime-growth scale, do not distinguish rational from irrational dyadic sums. It does not preserve primality. We also give exact integral-shift criteria for the actual prime-gap tails and isolate the joint small-shift recurrence that would suffice to prove irrationality. That prime-specific input is not established here.

<a id="sec:problem"></a>

# Introduction

<a id="sparse-corrections-and-local-information."></a>

#### Sparse corrections and local information.

Our main result concerns general summable nonnegative integer words, not only prime gaps. The support and target interval are chosen before the target value. A congruence buffer repairs the cumulative residue; a pair with fixed unweighted total then changes the dyadic value without undoing that repair. Sparsity ensures that almost every sufficiently short block meets no correction.

<a id="density-and-block-conventions."></a>

#### Density and block conventions.

Here $`\mathbb{N}=\{0,1,\ldots\}`$, all intervals of indices contain integers, and $`\log`$ is natural unless a base is displayed. Upper Banach density zero means
``` math
\lim_{H\to\infty}\sup_{u\in\mathbb{N}}\frac{|S\cap[u,u+H)|}{H}=0.
```
For integers $`X\ge1`$ and $`m\ge1`$, let $`\mu_{a,X,m}`$ be the empirical probability measure giving mass $`1/X`$ to each literal block $`(a_n,\ldots,a_{n+m-1})`$, $`X\le n<2X`$, with multiplicities. We use $`d_{\rm TV}(\mu,\nu)=\sup_B|\mu(B)-\nu(B)|`$; consequently tests bounded in absolute value by $`B_0`$ differ in mean by at most $`2B_0d_{\rm TV}(\mu,\nu)`$. No rescaling of the coefficients is implicit.

<div id="res:sparserationalisation" class="proposition">

**Proposition 1** (sparse congruence-preserving rationalisation). *Let $`a:\mathbb{N}\to\mathbb{N}`$ satisfy $`A=\sum_{n\ge0}a_n2^{-(n+1)}<\infty`$, let $`K\in\mathbb{N}`$, and let $`f:\mathbb{N}\to\mathbb{R}`$ tend to $`+\infty`$. There exist a set $`S\subseteq[K,\infty)`$ of upper Banach density zero and a nondegenerate interval $`I\subset(A,\infty)`$ such that, for every $`r\in I`$, there is an integer correction $`e:\mathbb{N}\to\mathbb{N}`$ satisfying
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

<div class="proof">

*Construction.* Use disjoint triples of coordinates $`n_j-1,n_j,n_j+1`$, with spacings $`s_j=n_j-n_{j-1}\ge4`$, and moduli $`M_j`$ forming a divisibility chain. Put $`D_j=2^{s_j}-1`$. The integer $`C_j`$ is the total correction in the completed triples before stage $`j`$. Starting from $`C_0=0`$, define
``` math
c_j=(-C_j)\bmod M_j\quad(0\le c_j<M_j),\qquad
 C_{j+1}=C_j+c_j+M_jD_j.
```
For a free integer digit $`d_j\in\{0,\ldots,D_j\}`$, assign all three corrections:
``` math
e_{n_j-1}=c_j,\qquad e_{n_j}=M_jd_j,\qquad
 e_{n_j+1}=M_j(D_j-d_j),
```
and set $`e_n=0`$ elsewhere. The complete triple has total $`c_j+M_jD_j`$, independent of $`d_j`$, so every buffer is fixed before the free digits are chosen. Immediately after the buffer, the cumulative correction is divisible by $`M_j`$; both pair entries preserve it. Later buffers preserve every previously imposed divisor. Thus each fixed modulus eventually divides both individual and cumulative corrections if it eventually divides $`M_j`$. More precisely, if $`q\mid M_J`$, every index $`n\ge n_J`$ has both divisibilities. The first buffer at $`n_J-1`$ need not itself be divisible by $`q`$; it is deliberately before this cutoff. The cutoff depends only on the schedule, not on the chosen free digits.

Here is an explicit schedule for an arbitrary $`f\to\infty`$. Set
``` math
h(n)=\inf_{m\ge n}\min(f(m),m),
```
choose $`n_{-1}\ge K`$ so large that $`h(n_{-1})\ge32`$, and recursively let
``` math
k_j=\max\{k\ge2:k!2^{k+2}\le h(n_{j-1})\},\quad
 M_j=k_j!,\quad s_j=k_j+2,\quad n_j=n_{j-1}+s_j.
```
The function $`h`$ is nondecreasing, tends to infinity, and satisfies $`h(n)\le n`$. Hence $`k_j`$ is nondecreasing and tends to infinity. Each triple entry is at most $`M_j2^{s_j}\le h(n_{j-1})`$, which is at most $`f(n)`$ at every coordinate of that triple and at most $`n_{j-1}`$. This proves the size bound and summability of the correction. To see uniform sparsity, fix $`R`$. Beyond finitely many triples, centres are separated by at least $`R`$. An interval of length $`H`$ therefore meets at most $`3(H/R+2)`$ supported coordinates, plus a fixed finite number. Divide by $`H`$, take the supremum over translates, let $`H\to\infty`$, and then let $`R\to\infty`$.

The fixed total of the pair is the point of using two free coordinates: for example, $`(6d,6(15-d))`$ always has ordinary sum $`90`$, but advancing $`d`$ by one changes its dyadic contribution by $`6\cdot2^{-n_j-2}`$. In general put $`w_j=M_j2^{-n_j-2}`$. The weighted correction separates as
``` math
\sum_n\frac{e_n}{2^{n+1}}=\beta+\sum_jd_jw_j,
 \qquad \beta=\sum_j\bigl(c_j2^{-n_j}+D_jw_j\bigr).
```
The buffer contribution is included in the fixed, positive number $`\beta`$. For $`i>j`$, monotonicity of the moduli gives
``` math
D_iw_i\ge M_j\bigl(2^{-n_{i-1}-2}-2^{-n_i-2}\bigr),
 \qquad \sum_{i>j}D_iw_i\ge w_j.
```
For each $`j`$ let $`X_j=\{0,w_j,\ldots,D_jw_j\}`$. Its maximal successive gap is $`w_j`$, while its diameter is $`D_jw_j`$. Thus the last displayed inequality is exactly the finite-choice covering condition
``` math
\operatorname{gap} X_j=w_j\le\sum_{i>j}\operatorname{diam}X_i.
```
Here $`\operatorname{gap} X`$ denotes the largest gap between consecutive points of a finite ordered set $`X`$. Crmarić and Kovač’s covering lemma \[crmarickovac2025, Lemma 4\] therefore gives $`\sum_jX_j=[0,F]`$, where $`F=\sum_jD_jw_j>0`$. Equivalently, choose digits successively so that each remainder lies within the remaining capacity, which tends to zero. This is a finite-menu form of Fridy’s generalised-base argument \[fridy1966, Lemma, p. 194\]; unlike Fridy’s statement, the finite-menu formulation needs no monotonicity of $`(w_j)`$. Reciprocal menus appear in Kovač–Tao \[kovactao2024, Lemma 5.1\]. Take $`I=(A+\beta,A+\beta+F)`$.

For the polylogarithmic bound, instead set, after a sufficiently large initial cutoff,
``` math
s_j=\left\lfloor\frac{\varepsilon}{2}\log_2\log(n_{j-1}+3)\right\rfloor,
 \qquad
 k_j=\max\{k\ge2:k!\le(\log(n_{j-1}+3))^{\varepsilon/4}\},
```
with $`M_j=k_j!`$, $`n_j=n_{j-1}+s_j`$ and the same $`D_j`$ and buffers. This schedule works for every $`\varepsilon>0`$; no prime-growth assertion is used here. Then $`s_j\ge4`$ and $`M_j2^{s_j}\le(\log(n_{j-1}+3))^{3\varepsilon/4}`$. The preceding congruence, convergence and interval arguments still apply. Spacing comparable to $`\log\log n_j`$ gives $`|S\cap[X,2X)|=O_\varepsilon(X/\log\log X)`$. Couple the original and corrected length-$`m`$ blocks at the same starting index in $`[X,2X)`$. At most $`m|S\cap[X,2X+m)|`$ starts meet a correction, so their empirical distributions differ in total variation by $`O_\varepsilon(m/\log\log X)`$ for $`m=o(\log\log X)`$. The companion record expands this three-coordinate construction and its all-index congruence check. The pinned formal development proves the same existential conclusion by a different, one-site residue-feedback construction. Its theorem statements, rather than identity of witnesses, are the formal correspondence; the verification boundary is recorded below. ◻

</div>

For a fixed bound $`B_0`$, this coupling also applies to tests $`\Phi_X(n,a_n,\ldots,a_{n+m-1})`$ depending on the starting index: their average difference is at most $`2B_0m|S\cap[X,2X+m)|/X`$. This is an absolute error estimate. For an event of probability $`p_X\to0`$, relative preservation would require this error to be $`o(p_X)`$; it does not follow from an error of $`o(1)`$. A cofinal but density-zero witness set can be lost altogether.

<div id="res:jointcountermodel" class="corollary">

**Corollary 2** (one rational countermodel with joint constraints). *Let $`p_0=2,p_1=3,\ldots`$ be the primes and $`g_n=p_{n+1}-p_n`$. Given $`K\in\mathbb{N}`$ and $`0<\varepsilon\le1`$, there is $`b:\mathbb{N}\to\mathbb{N}`$ with rational dyadic sum such that $`b_n=g_n`$ for $`n<K`$, $`b_n\ge g_n`$, and $`b_n-g_n\le(\log(n+3))^\varepsilon`$ eventually. For every fixed positive modulus, both the coefficients and the cumulative positions eventually retain their corresponding residues. The literal block laws agree asymptotically for lengths $`o(\log\log X)`$, and for every fixed nonzero $`F\in\mathbb{Z}[x_0,\ldots,x_k]`$,
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

<div class="proof">

*Proof.* Choose a rational target in Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a>’s interval and put $`b=g+e`$. Fixed-block nonconcentration for $`g`$ is Schlage-Puchta’s Lemma 4 \[schlagepuchta2011\]. A length-$`(k+1)`$ block changes only at a start in $`\bigcup_{i=0}^{k}(S-i)`$, a density-zero set. Thus the same zero-density conclusion holds for each fixed polynomial at $`b`$, without a bound on its values or on the values of $`e`$. Summing the dyadic support bound gives $`|S\cap[0,n)|=O_\varepsilon(n/\log\log n)`$. Multiply by the eventual pointwise bound on $`e`$ to obtain the displayed cumulative estimate. The prime number theorem gives $`p_n\sim n\log n`$ \[mv2007, Chapter 6\]; the error is $`o(n\log n)`$ even at $`\varepsilon=1`$. The congruences and growing-block conclusion are those of the proposition. ◻

</div>

This corollary is an ordinary deduction combining the sparse construction with an external nonconcentration theorem. It is not a claim that the combined statement, or Schlage-Puchta’s analytic input, was newly checked in Lean. The bounded, single-modulus alternative and its translation argument remain in the companion record.

<a id="relation-to-prior-work."></a>

#### Relation to prior work.

Erdős’s fixed-denominator question appears in \[erdos1958, p. 94\], \[erdosgraham1980, p. 62\] and \[erdos1988, p. 103\]. Neither his factorial-denominator theorem nor the variable-denominator counterexample in \[kovac2026\] decides it. The bounded prime-factor comparison digits of Erdős–Pomerance \[erdospomerance1978, §7\] are a different dyadic setting.

The closest mechanism for Proposition <a href="#res:sparserationalisation" data-reference-type="ref" data-reference="res:sparserationalisation">1</a> is the finite-choice covering lemma of Crmarić–Kovač \[crmarickovac2025, Lemma 4\], which they use for product-denominator series. Fridy \[fridy1966\] and Kovač–Tao \[kovactao2024, Lemma 5.1\] provide generalised-base and reciprocal-menu antecedents. Van Doorn–Kovač combine interval filling with a chain absorbing every integer divisor \[vandoornkovac2025, Lemma 7, Proposition 8\]. Our factorial moduli use that absorption property. Van Doorn’s reciprocal-preserving exchange \[vandoorn2025, proof of Theorem 3\] is a useful comparison: our pair instead preserves an ordinary sum while varying its dyadic weight. These are method comparisons, not claims that the present perturbation theorem is a special case of those arithmetic statements, or that interval filling is new.

Finite binary menus can have more complicated achievement sets. Central blocks of subsums can give intervals even when elementary term-versus-tail tests alternate \[bartoszewicz2014, Theorem 2\]; Cantorvals may occur when the overlap inequality $`a_n\le\sum_{i>n}a_i`$ holds only on a density-zero set of indices \[prusptak2024, Theorem\]. See \[glabprus2025, §1\] for background, and \[nitecki2015, Theorem 14 of the consulted preprint\] for Nitecki’s exposition of the Guthrie–Nymann classification. The repaired constructions in \[miskaprusptak2023, Theorem 2\] show that even a prescribed pattern of strict term-versus-tail inequalities need not determine interior. Nowakowski’s different sufficient condition requires an infinite positivity procedure, not just mixed inequalities \[nowakowski2025, Definition 2, Theorem 3.1\]. Our proof avoids that classification issue by verifying a covering inequality for every finite menu.

There is a separate boundary concerning prime statistics. Schlage-Puchta’s fixed-block polynomial nonconcentration lemma \[schlagepuchta2011, Lemma 4\] is not a growing-block distribution theorem. Adamczewski–Drmota–Müllner give effective logarithmic densities for fixed automatic sequences along primes and a criterion for natural densities \[adm2022, Theorems 1.2, 1.4\]; this does not describe the unbounded consecutive-gap word or a family of automata growing with $`X`$. In particular, logarithmic densities in their general theorem need not be rational.

Under a uniform Hardy–Littlewood hypothesis of the type stated by Kuperberg \[kuperberg2023, Conjecture 1.3\], Land’s draft proves a conditional irrationality implication \[land2026, Theorem 2\] and Ringer’s draft a conditional normality implication \[ringer2026\]. The authors supply formalisation material; no independent rebuild of those external projects is claimed here. Ringer also separates weaker averaged comparison inputs from the stronger uniform conjecture. None of these conditional hypotheses is assumed in this note, and no unconditional irrationality claim is made.

<a id="reading-the-two-papers."></a>

#### Reading the two papers.

This note gives the sparse construction, its joint consequence and the exact prime-tail criterion. The companion *Prime-Gap Dyadic Series: Perturbations, Exact Criteria and Certificates* supplies the extended algebra, complete countermodels, source concordance and certificate code. The manuscripts use stable labels rather than section numbers as the cross-reference contract.

<a id="sec:parts"></a>

# The prime series and its actual tails

Retain the zero-based primes and gaps of Corollary <a href="#res:jointcountermodel" data-reference-type="ref" data-reference="res:jointcountermodel">2</a>, and put
``` math
\Pi=\sum_{n\ge0}p_n2^{-(n+1)},\qquad
 G=\sum_{n\ge0}g_n2^{-(n+1)}.
```
Convergence needs no prime number theorem. The central-binomial argument of Erdős \[erdos1932, pp. 194–196\] gives the elementary bound $`p_n\le1250(n+1)^4`$: for $`m\ge4`$, $`4^m<m\binom{2m}{m}\le m(2m)^{\pi(2m)}`$. The first inequality follows by induction from $`m=4`$; each prime-power contribution to the binomial coefficient is at most $`2m`$, giving the second. Taking $`m=(n+5)^4`$, a supposition $`\pi(2m)\le n`$ would give
``` math
m(2m)^n=2^n(n+5)^{4(n+1)}\le4^m,
```
since $`x\le2^x`$ for $`x=n+5`$ and $`n+4(n+1)x=4x^2-15x-5\le2x^4`$. This is a contradiction. Hence $`p_n\le2(n+5)^4\le1250(n+1)^4`$; both series converge absolutely.

<div id="res:infinite" class="theorem">

**Theorem 3** (prime-to-gap identity). *The actual prime and gap series satisfy $`\Pi=2+G`$. Their complete tails
``` math
T_N=\sum_{j\ge1}g_{N+j}2^{-j}
```
satisfy $`T_0=2G-1`$ and $`T_{N+1}=2T_N-g_{N+1}`$. Thus $`\Pi`$, $`G`$ and $`T_0`$ have the same rationality status.*

</div>

<div class="proof">

*Proof.* Finite summation by parts retains the endpoint:
``` math
\sum_{i=0}^{n}\frac{p_i}{2^{i+1}}
 =2+\sum_{i=0}^{n-1}\frac{g_i}{2^{i+1}}-\frac{p_n}{2^{n+1}}.
```
The endpoint tends to zero by the polynomial bound. Splitting off the first term of the absolutely convergent tail gives its recurrence, and $`g_0=1`$ gives $`T_0=2G-1`$. ◻

</div>

This is the reduction noted by Tao in the problem’s forum discussion \[erdosproblems251thread, 7 October 2025\], with convergence and the endpoint made explicit; summation by parts itself is not a new method.

<div id="res:true-tail" class="lemma">

**Lemma 4** (the boundary condition identifying a true tail). *Let $`\sum_{j\ge1}|a_j|2^{-j}<\infty`$ and $`U_{N+1}=2U_N-a_{N+1}`$. Then $`U_N=\sum_{j\ge1}a_{N+j}2^{-j}`$ for every $`N`$ if and only if $`2^{-N}U_N\to0`$.*

</div>

<div class="proof">

*Proof.* The recurrence gives $`2^{-N}U_N=U_0-\sum_{j=1}^{N}a_j2^{-j}`$. Its limit vanishes exactly when $`U_0`$ is the full series. Without this boundary condition an arbitrary homogeneous term $`C2^N`$ remains. ◻

</div>

<a id="sec:tail"></a>

# Integral shifts: an exact algebraic classification

A real integer-digit recurrence is a sequence $`U:\mathbb{N}\to\mathbb{R}`$ satisfying $`U_{N+1}=2U_N-a_{N+1}`$, with integers $`a_n`$. Write $`D_h(N)=U_{N+h}-U_N`$. This general recurrence is distinct from the actual prime-gap tail $`T`$ until the latter is explicitly substituted.

<div id="res:escape-irrational" class="theorem">

**Theorem 5** (exact rationality classification). *For a real integer-digit recurrence, the following are equivalent: $`U_0\in\mathbb{Q}`$; $`D_h(N)\in\mathbb{Z}`$ for some $`h\ge1,N\ge0`$; and, for some fixed $`h\ge1`$, $`D_h(N)\in\mathbb{Z}`$ at every sufficiently large $`N`$. More precisely, if $`U_0=u/(2^sd)`$ is in lowest terms, with $`d`$ odd, then
``` math
\operatorname{den}(U_N)=2^{\max(s-N,0)}d,\qquad
 D_h(N)\in\mathbb{Z}\ \Longleftrightarrow\ N\ge s\ \text{and}\ d\mid2^h-1
 \quad(h\ge1).
```
Consequently $`U_0`$ is irrational exactly when every positive shift is nonintegral at every index, equivalently when for each fixed $`h\ge1`$ there are arbitrarily late nonintegral shifts.*

</div>

<div class="proof">

*Proof.* Iteration gives integers $`B_N,C_{N,h}`$ with
``` math
U_N=2^NU_0-B_N,\qquad
 D_h(N)=2^N(2^h-1)U_0-C_{N,h}.
```
The second coefficient is nonzero for $`h\ge1`$, so one integral shift forces $`U_0`$ rational. For rational $`U_0`$, cancellation in lowest terms gives the displayed denominator and divisibility formulae, since $`2^h-1`$ is odd. Euler’s congruence supplies $`d\mid2^{\varphi(d)}-1`$; for $`d=1`$ take $`h=1`$. This gives an integral fixed shift for every $`N\ge s`$. Negating the pointwise and eventual statements gives the last assertion. ◻

</div>

For instance $`U_0=1/12`$ and all digits zero gives $`U_2=1/3`$. The first admissible shift length is $`2`$, and it is integral from index $`2`$ onwards. This illustrates why a test at one preassigned shift length cannot exclude every rational denominator.

Applied to Theorem <a href="#res:infinite" data-reference-type="ref" data-reference="res:infinite">3</a>, this is an equivalence for the actual prime series, not an irrationality proof. The lcm diagonal, totient witness, forward propagation, free-pair formulation and affine-lattice reformulations are developed in the companion record. Each uses the same integer-orbit calculation; none adds prime-distribution information.

<a id="sec:local-certificate"></a>

# A local certificate and the missing prime input

For the actual tail put $`D_N=T_{N+h}-T_N`$ and $`\delta_N=g_{N+h+1}-g_{N+1}`$. Then $`D_{N+1}=2D_N-\delta_N`$. The gaps in $`\delta_N`$ are even for $`h\ge1,N\ge0`$.

<div id="res:signedwindow" class="proposition">

**Proposition 6** (signed two-window normal form). *Let $`D,D'\in\mathbb{R}`$, $`\delta\in2\mathbb{Z}`$ and $`D'=2D-\delta`$. The conditions $`|D|<1`$, $`|D'|<1`$ and $`\delta\ne0`$ hold exactly when, for some $`s\in\{-1,1\}`$,
``` math
\delta=2s,\qquad \tfrac12<sD<1.
```
In that case $`sD'\in(-1,0)`$ and both states are nonintegral.*

</div>

<div class="proof">

*Proof.* The two unit windows imply $`-3<\delta<3`$. Nonzero evenness forces $`\delta=\pm2`$, and substitution gives the signed half-window. Conversely $`sD'=2sD-2\in(-1,0)`$ recovers the second unit window. ◻

</div>

<div id="prob:smallpair" class="problem">

**Problem 7** (cofinal adjacent small mismatch). For every integer $`h\ge1`$ and every cutoff $`N_0`$, exhibit $`N\ge N_0`$ with
``` math
\begin{equation}
\label{eq:smallpair}
 |T_{N+h}-T_N|<1,\quad |T_{N+h+1}-T_{N+1}|<1,\quad
 g_{N+h+1}\ne g_{N+1}.
\end{equation}
```

</div>

This would prove irrationality by Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">5</a>. For each fixed $`h`$, Schlage-Puchta’s Lemma 4 \[schlagepuchta2011\], applied to $`x_h-x_0-2`$ and $`x_h-x_0+2`$, shows that the eligible $`\delta_N=\pm2`$ indices have density zero. A proof therefore needs arbitrarily late witnesses in a sparse set, not a positive-proportion statement. The quantifiers are per fixed $`h`$; constants may depend on $`h`$.

<a id="finite-exact-tests"></a>

## Finite, exact tests

For $`h\ge1,N\ge0,L\ge1`$, put
``` math
S_{h,N,L}=\sum_{j=1}^{L}(g_{N+h+j}-g_{N+j})2^{-j},\qquad
 R_{h,N,L}(M)=\sum_{j>L}(M(N+h+j)+M(N+j))2^{-j},
```
where $`M(n)\ge g_n`$ is a nonnegative summable dyadic majorant. Then $`|D_N-S_{h,N,L}|\le R_{h,N,L}(M)`$.

<div id="res:truncation" class="proposition">

**Proposition 8** (finite separation criterion). *If for every $`h\ge1`$ and every cutoff $`N_0`$ there are $`N\ge N_0,L\ge1`$ with
``` math
\begin{equation}
\label{eq:truncation}
 \operatorname{dist}(S_{h,N,L},\mathbb{Z})>R_{h,N,L}(M),
\end{equation}
```
then $`\Pi`$ is irrational.*

</div>

<div class="proof">

*Proof.* An integral $`D_N`$ would contradict its distance bound. The resulting cofinal nonintegrality is the criterion in Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">5</a>. ◻

</div>

<div id="res:complete-truncation" class="remark">

*Remark 1* (what arbitrary truncation does not gain). Whenever $`|D-S_L|\le R_L\to0`$, nonintegrality of $`D`$ is equivalent to $`\operatorname{dist}(S_L,\mathbb{Z})>R_L`$ for some $`L`$. Indeed, if $`\delta=\operatorname{dist}(D,\mathbb{Z})>0`$, choose $`R_L<\delta/2`$ and use the $`1`$-Lipschitz property of distance. Thus an unrestricted choice of depth is an exact reformulation, not an additional analytic estimate. A logarithmic depth requires quantitative separation from the relevant boundaries as well as a small remainder.

</div>

There is a one-tail version of the adjacent certificate. If $`\delta_N=2s`$, $`s\in\{-1,1\}`$, and $`|QD_N-A|\le B`$ with integers $`Q>0,B\ge0`$, it suffices to check
``` math
2sA-Q>2B,\qquad Q-sA>B.
```
These inequalities put the entire enclosure of $`sD_N`$ inside $`(1/2,1)`$. For $`h=1,N=2`$, one can use
``` math
Q=2^{40},\quad A=-662838684750,\quad B=11764181250,\quad s=-1.
```
The two strict margins are $`202637379224`$ and $`424908761776`$. Here $`A/Q=S_{1,2,40}`$ and $`B/Q`$ is justified by the polynomial majorant
``` math
P(x)=x^4+8x^3+36x^2+104x+150,\qquad
 R_{h,N,L}\le\frac{1250}{2^L}
     \bigl(P(N+h+L+2)+P(N+L+2)\bigr).
```
The identity $`2P(x)=(x+1)^4+P(x+1)`$ telescopes the weighted quartic tail; the bound $`g_n\le p_{n+1}\le1250(n+2)^4`$ completes its proof. The companion record and supplied integer program give all prime indices, both original enclosures and the new one-tail test. One certified pair says nothing about arbitrarily late pairs or all $`h`$.

<a id="sec:carry"></a>

# Nonperiodic coefficients with a rational sum

There is an exact finite obstruction recorded in the pinned source: a second example has finite sum $`-n/2^n`$ and non-eventually-periodic coefficients ([finite endpoint](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1157); [coefficient nonperiodicity](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1163)). The actual prime gaps are also not eventually periodic ([prime-gap nonperiodicity](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1023)), but that fact alone is insufficient. The polynomial comparison below is a synthetic countermodel, not a prime-gap construction.

<a id="sec:open"></a>

# What the countermodels exclude

The joint countermodel of Corollary <a href="#res:jointcountermodel" data-reference-type="ref" data-reference="res:jointcountermodel">2</a> shows that the stated prefix, congruence, growth, nonconcentration and growing-block properties can hold together while the dyadic value is rational. The obstruction is to deductions from those properties alone, not to arguments using exact primality or more accurate rare-event estimates. The ordinary proof can also place its target interval inside $`(A,A+\eta)`$ for any $`\eta>0`$: start beyond $`K'`$ with $`(K'+1)2^{-K'}<\eta`$ and use $`e_n\le n`$ from the general schedule.

A simple comparison displays the carry freedom explicitly. Set $`c_n=2(n^2+4n+2)`$ and $`U_n=2(n+4)^2`$. Then $`U_{n+1}=2U_n-c_{n+1}`$, every shift is integral, and
``` math
\sum_{j\ge1}c_j2^{-j}=32,
 \qquad \sum_{n\ge0}c_n2^{-(n+1)}=18.
```
The digits are positive, even and strictly increasing, and their adjacent differences $`4n+10`$ are never $`\pm2`$. Thus nonperiodicity of unbounded digits does not imply irrationality of a dyadic sum. This is a synthetic countermodel, not a prime-gap construction; the companion gives the full polynomial and carry statements and their formal locators.

Bounded gaps \[zhang2014\], bounded clusters of each fixed size \[maynard2015; polymath2014\], and extreme large gaps \[fgkmt2018\] concern different distributional data. In particular Polymath’s $`\liminf_n(p_{n+1}-p_n)\le246`$ \[polymath2014, Theorem 1.4(i)\] improves the earlier bound $`600`$; no exact small-gap bound used here supplies a signed weighted-tail window. With the polynomial majorant, $`L=\lceil(4+\eta)\log_2(N+h+2)\rceil`$ for fixed $`h`$ makes the remainder small. It certifies a window only when the finite sum also has a larger margin from the boundary. A fixed positive margin is a convenient stronger sufficient condition, not a consequence of strict membership in an open window.

The remaining task is a quantitative prime-gap estimate producing the required separation or sparse signed-window witnesses. The construction, classification and finite certificates above do not supply it. The companion includes the free-pair alternative, affine-lattice obstructions, the complete countermodels and separate denominator exclusions. A lower bound on the denominator of a hypothetical rational value is neither a proof of irrationality nor an irrationality-exponent estimate.

<div id="res:irr-equivalence" class="corollary">

**Corollary 9** (exact irrationality reformulation). *The prime-value dyadic series is irrational if and only if the prime-gap dyadic series is. The named equivalence still takes a summability hypothesis which this checkout discharges; neither side is proved irrational.*

</div>

<div id="res:gap-nonperiodic" class="proposition">

**Proposition 10** (prime gaps do not become periodic). *For every positive $`h`$, the actual consecutive-prime-gap sequence is not eventually periodic with period $`h`$.*

</div>

<a id="attribution-and-verification"></a>

## Attribution and verification

The finite-choice covering step is credited where it is used. The sparse existential results and recurrence criteria have counterparts at the pinned source revision `99f4bf47422a`; the supplied index marks the named main endpoints `ci_checked`. The buffered-triple witness printed here differs from the one-site formal construction. The new joint corollary and explanatory deductions are ordinary proofs; Schlage-Puchta’s lemma and the prime number theorem are external inputs. This revision replayed `lake build ErdosProblems Erdos249257` on Lean 4.29.1; no new \#251 endpoints were admitted beyond that replay. The companion provides the declaration-level ledger and preserves all statements moved out of this shorter presentation.

Lean 4 \[lean4\] and mathlib \[mathlib\] provide the proof-checking environment. A supplied build receipt, an ordinary argument and an executed exact-integer certificate have different evidential roles. The original production provenance macro remains required for publication. The author received no external funding and declares no competing interests. The numbering follows Bloom’s catalogue \[erdosproblems\]; private review material and future correspondence imply no specialist endorsement.

<a id="sec:pinned-lean-sources"></a>

# Pinned Lean sources

The following declarations are this note’s pin-faithful source inventory. Line numbers are those of the commit named by `\commit`.

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L47)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L51)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L101)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L121)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L138)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L111)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L172)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L183)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L192)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L202)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L385)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L404)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L188)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L196)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L435)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L444)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L459)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L360)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L379)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L427)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L482)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L544)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L647)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L653)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L667)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L563)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L677)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L802)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1279)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L695)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L877)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L888)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L900)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1217)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1226)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1236)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L723)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L756)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L830)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L853)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L489)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L527)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L510)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1479)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1525)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1551)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1572)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L979)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1006)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1112)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L57)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1023)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1129)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1137)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1157)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1163)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1097)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L106)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L124)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L129)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L152)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L156)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L161)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1133)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1177)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1180)

<div class="thebibliography">

99

Paul Erdős, [*Sur certaines séries à valeur irrationnelle*](https://users.renyi.hu/~p_erdos/1958-19.pdf). L’Enseignement Mathématique **4** (1958), 93–100, doi:[10.5169/seals-34629](https://doi.org/10.5169/seals-34629). Paul Erdős and Ronald L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf). Monographies de L’Enseignement Mathématique, L’Enseignement Mathématique, 1980. Paul Erdős and Carl Pomerance, [*On the largest prime factors of $`n`$ and $`n+1`$*](https://doi.org/10.1007/BF01818569). Aequationes Mathematicae **17** (1978), 311–321, doi:[10.1007/BF01818569](https://doi.org/10.1007/BF01818569). Paul Erdős, [*On the irrationality of certain series: problems and results*](https://doi.org/10.1017/CBO9780511897184.009). New Advances in Transcendence Theory, Cambridge University Press, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). Kevin Ford, Ben Green, Sergei Konyagin, James Maynard and Terence Tao, [*Long gaps between primes*](https://arxiv.org/abs/1412.5029v3). Journal of the American Mathematical Society **31** (2018), 65–105, doi:[10.1090/jams/876](https://doi.org/10.1090/jams/876); arXiv:[1412.5029v3](https://arxiv.org/abs/1412.5029v3). John A. Fridy, [*Generalized bases for the real numbers*](https://www.fq.math.ca/Scanned/4-3/fridy.pdf). The Fibonacci Quarterly **4** (1966), no. 3, 193–201. Vjekoslav Kovač and Terence Tao, [*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593v4). Acta Mathematica Hungarica **175** (2025), 572–608, doi:[10.1007/s10474-025-01528-0](https://doi.org/10.1007/s10474-025-01528-0); arXiv:[2406.17593v4](https://arxiv.org/abs/2406.17593v4). Statement and section numbers refer to arXiv version 4; legacy citation key retained. Vivian Kuperberg, [*Sums of singular series with large sets and the tail of the distribution of primes*](https://arxiv.org/abs/2210.09775v2). The Quarterly Journal of Mathematics **74** (2023), no. 4, 1457–1479, doi:[10.1093/qmath/haad030](https://doi.org/10.1093/qmath/haad030); arXiv:[2210.09775v2](https://arxiv.org/abs/2210.09775v2). Statement numbers refer to arXiv version 2, 15 June 2023. Johan Land, [*A conditional proof of the irrationality of $`\sum_{n\ge1}p_n2^{-n}`$ under a uniform Hardy–Littlewood prime-tuples conjecture*](https://github.com/beetree/math_erdos_251). Research draft, 5 September 2026, 2026. The author supplies formalisation material. No independent rebuild is claimed in this revision. Leonardo de Moura and Sebastian Ullrich, [*The Lean 4 theorem prover and programming language*](https://doi.org/10.1007/978-3-030-79876-5_37). Automated Deduction – CADE 28, Lecture Notes in Computer Science, Springer, 2021, pp. 625–635, doi:[10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37). The mathlib Community, [*The Lean mathematical library*](https://doi.org/10.1145/3372885.3373824). Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs, ACM, 2020, pp. 367–381, doi:[10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). Describes a Lean 3-era snapshot; the repository lock identifies the library used by the present Lean 4 sources. James Maynard, [*Small gaps between primes*](https://doi.org/10.4007/annals.2015.181.1.7). Annals of Mathematics **181** (2015), 383–413, doi:[10.4007/annals.2015.181.1.7](https://doi.org/10.4007/annals.2015.181.1.7). Hugh L. Montgomery and Robert C. Vaughan, [*Multiplicative Number Theory I: Classical Theory*](https://doi.org/10.1017/CBO9780511618314). Cambridge Studies in Advanced Mathematics, Cambridge University Press, 2007, doi:[10.1017/CBO9780511618314](https://doi.org/10.1017/CBO9780511618314). Wouter van Doorn and Vjekoslav Kovač, [*Lacunary sequences whose reciprocal sums represent all rational numbers in an interval*](https://arxiv.org/abs/2509.24971v3). Acta Arithmetica **223** (2026), 275–295, doi:[10.4064/aa251001-13-1](https://doi.org/10.4064/aa251001-13-1); arXiv:[2509.24971v3](https://arxiv.org/abs/2509.24971v3). Statement numbers refer to arXiv version 3; legacy citation key retained. Yitang Zhang, [*Bounded gaps between primes*](https://doi.org/10.4007/annals.2014.179.3.7). Annals of Mathematics **179** (2014), 1121–1174, doi:[10.4007/annals.2014.179.3.7](https://doi.org/10.4007/annals.2014.179.3.7). Thomas F. Bloom, [*Erdős Problem \#251*](https://www.erdosproblems.com/251). 2026. Catalogue snapshot inherited from the supplied manuscript, accessed 6 September 2026. Live page was inaccessible to this revision on 16 September 2026; no refreshed global-status claim is inferred. Erdős Problems contributors, [*Erdős Problem \#251 discussion thread*](https://www.erdosproblems.com/forum/thread/251). 2026. Inherited snapshot accessed 6 September 2026: Tao comment of 7 October 2025 and Land comments of 6 September 2026. Live thread not reverified. ChatGPT 5.4 Pro (orchestrated by Vjeko Kovač), [*On the Erdős problem \#251*](https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_251.pdf). Unpublished note, Department of Mathematics, University of Zagreb, 2026. Printed attribution retained from the supplied bibliography; inherited access date 6 September 2026. Stefan Ringer, [*Local gap statistics, telescoping, and normality: a local-pattern approach to Erdős problem 251*](https://github.com/StefanRinger/erdos-251). Preprint dated 11 September 2026, 2026. Mutable main-branch TeX consulted 16 September 2026. The author supplies formalisation material; this revision does not independently rebuild it. Tonći Crmarić and Vjekoslav Kovač, [*On the irrationality of certain super-polynomially decaying series*](https://arxiv.org/abs/2504.18712v1). Colloquium Mathematicum **179** (2025), 55–68, doi:[10.4064/cm9628-5-2025](https://doi.org/10.4064/cm9628-5-2025); arXiv:[2504.18712v1](https://arxiv.org/abs/2504.18712v1). Lemma 4 is cited using arXiv version 1. Boris Adamczewski, Michael Drmota and Clemens Müllner, [*(Logarithmic) densities for automatic sequences along primes and squares*](https://arxiv.org/abs/2009.14773v2). Transactions of the American Mathematical Society **375** (2022), no. 1, 455–499, doi:[10.1090/tran/8476](https://doi.org/10.1090/tran/8476); arXiv:[2009.14773v2](https://arxiv.org/abs/2009.14773v2). Theorems 1.2 and 1.4 refer to arXiv version 2, 13 April 2021; journal publication is 2022. Wouter van Doorn, [*Partitions with prescribed sum of reciprocals: asymptotic bounds*](https://arxiv.org/abs/2502.02200v2). 2025; arXiv:[2502.02200v2](https://arxiv.org/abs/2502.02200v2). Version 2, 23 July 2025. No journal publication was confirmed in this pass. Szymon Głąb and Franciszek Prus-Wiśniowski, [*Achievement sets – current results and open problems*](https://arxiv.org/abs/2512.17285v1). Real Analysis Exchange (2026), doi:[10.14321/realanalexch.1766383782](https://doi.org/10.14321/realanalexch.1766383782); arXiv:[2512.17285v1](https://arxiv.org/abs/2512.17285v1). Advance publication, first available in Project Euclid 8 June 2026. Consulted text remains arXiv:2512.17285v1 (19 December 2025); no final volume or page range was confirmed. Legacy citation key retained. Franciszek Prus-Wiśniowski and Jolanta Ptak, [*Achievable Cantorvals almost without reversed Kakeya conditions*](https://arxiv.org/abs/2412.08768v1). 2024; arXiv:[2412.08768v1](https://arxiv.org/abs/2412.08768v1). Version 1 submitted 11 December 2024. The sparse indices satisfy the overlap inequality, not its strict term-dominating reverse. Artur Bartoszewicz, Małgorzata Filipczak and Emilia Szymonik, [*Multigeometric sequences and Cantorvals*](https://arxiv.org/abs/1304.4218v2). Central European Journal of Mathematics **12** (2014), no. 7, 1000–1007, doi:[10.2478/s11533-013-0396-4](https://doi.org/10.2478/s11533-013-0396-4); arXiv:[1304.4218v2](https://arxiv.org/abs/1304.4218v2). Jan-Christoph Schlage-Puchta, [*The irrationality of some number theoretical series*](https://arxiv.org/abs/1105.1451v1). Acta Arithmetica **126** (2007), no. 4, 295–303, doi:[10.4064/aa126-4-1](https://doi.org/10.4064/aa126-4-1); arXiv:[1105.1451v1](https://arxiv.org/abs/1105.1451v1). Published in 2007; arXiv upload is from 2011. Lemma and preprint page locators refer to arXiv version 1; legacy citation key retained. Paul Erdős, [*Beweis eines Satzes von Tschebyschef*](https://users.renyi.hu/~p_erdos/1932-01.pdf). Acta Litterarum ac Scientiarum Szeged **5** (1932), 194–198. D. H. J. Polymath, [*Variants of the Selberg sieve, and bounded intervals containing many primes*](https://arxiv.org/abs/1407.4897v4). Research in the Mathematical Sciences **1** (2014), article 12, doi:[10.1186/s40687-014-0012-7](https://doi.org/10.1186/s40687-014-0012-7); arXiv:[1407.4897v4](https://arxiv.org/abs/1407.4897v4). Theorem 1.4(i) refers to arXiv version 4 (22 December 2014); the journal numbers it Theorem 4(i). An erratum is recorded at doi:10.1186/s40687-015-0033-x. Zbigniew Nitecki, [*Cantorvals and Subsum Sets of Null Sequences*](https://arxiv.org/abs/1106.3779v2). The American Mathematical Monthly **122** (2015), no. 9, 862–870, doi:[10.4169/amer.math.monthly.122.9.862](https://doi.org/10.4169/amer.math.monthly.122.9.862); arXiv:[1106.3779v2](https://arxiv.org/abs/1106.3779v2). Consulted preprint: Subsum Sets: Intervals, Cantor Sets, and Cantorvals, version 2 (8 July 2013). Theorem 14 is attributed there to Guthrie–Nymann; its locator is not journal pagination. Piotr Miska, Franciszek Prus-Wiśniowski and Jolanta Ptak, [*More on Kakeya Conditions for Achievement Sets*](https://ruj.uj.edu.pl/server/api/core/bitstreams/d6630f7b-e6ee-4de8-8a1b-81c7b4c59d2e/content). Results in Mathematics **78** (2023), article 113, doi:[10.1007/s00025-023-01890-x](https://doi.org/10.1007/s00025-023-01890-x). Repairs an estimate in the 2021 proof, preserving its uniqueness conclusion, and gives a simpler proof of a weaker theorem without that conclusion. Piotr Nowakowski, [*On a new condition implying that an achievement set is a Cantorval and its applications*](https://arxiv.org/abs/2512.17761v1). 2025; arXiv:[2512.17761v1](https://arxiv.org/abs/2512.17761v1). Version 1, 19 December 2025. Theorem 3.1 requires the Star Procedure of Definition 2 never to break; no application to the present factorial weights is asserted.

</div>

*Companion system context.* The [claim and trust boundary](../../../paper/systems/claim-faithful-publication-systems-paper.pdf#nameddest=systems-trust), [cold-clone route to proof authority](../../../paper/systems/cold-clone-to-proof-receipt.pdf#nameddest=cold-clone-authority), and [public contribution protocol](../../../paper/systems/open-source-mathematics-strategy.pdf#nameddest=strategy-protocol) are described in sibling papers. Those descriptions do not change the mathematical status of this note.
