<a id="erdos68-factorial-reasoning-surface"></a>

# The Factorial-Denominator Series: Complete Reasoning Record

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Write $`d_n=n!-1`$, $`H_M=\sum_{2\le n\le M}d_n^{-1}`$ and $`L_M=\operatorname{lcm}(d_2,\ldots,d_M)`$. For a prime $`p`$ with $`e=v_p(L_M)\ge1`$, let $`J=\{n:2\le n\le M,\ v_p(d_n)=e\}`$ and write $`d_n=p^eu_n`$ on $`J`$. Specialising the reciprocal-sum valuation formula of Louwsma and Martino gives
``` math
v_p\bigl(\operatorname{den}(H_M)\bigr)=e
 \quad\Longleftrightarrow\quad
 \sum_{n\in J}u_n^{-1}\ne0\ \hbox{ in }\mathbb F_p,
```
the inverses being taken modulo $`p`$. The prefixes through $`138`$ and $`2592`$ cancel the primes $`139`$ and $`2593`$ completely. The common denominator before reduction satisfies the quantitative bound
``` math
\liminf_{N\to\infty}\frac{\log L_N}{N^{3/2}\log N}\ \ge\ \frac{2\sqrt2}{3},
```
by an elementary segment argument that uses $`\gcd(i!-1,j!-1)\mid j!/i!-1`$ and no external multiplicity theorem. The two statements concern opposite sides of reduction, and the cancellations at $`139`$ and $`2593`$ are why the second cannot be substituted for the first.

Wilson’s theorem gives arbitrarily late first occurrences of primes among the factorial gaps, so prefix-private prime support of the denominators occurs cofinally, with no bound relating the prime to its first hit. Four exact criteria locate the irrationality of $`S=\sum_{n\ge2}d_n^{-1}`$: a strict-successor carry equivalence, a companion-orbit residue condition, a lower-interval escape condition of width $`O(m^{-2})`$, and a boundary covering the whole shifted family $`\sum_{n\ge2}1/(n!+t)`$ for every integer $`t\ge-1`$, whose member $`t=0`$ returns the irrationality of $`e`$. A finite-channel radius bound gives $`3t^3<2(R+1)`$ under the exact cancellation and factorial-size hypotheses, and the growth statement above raises the asymptotic constant in that estimate from $`3/2`$ to $`16/9`$. Two finite computations exclude denominators: $`q\nmid299999!`$ from an exact interval carry census through $`300000`$, and $`q\ge2^{39990}>10^{12038}`$ from an exact continued-fraction enclosure computed outside Lean. The factorial-grid exclusion uses the external GMP computation and remains a separate outstanding Lean obligation. The irrationality of $`S`$ is open, and the remaining arithmetic inputs are stated in the last section.

<a id="reading-route-and-dependencies."></a>

#### Reading route and dependencies.

For the main mechanism, read the survival criterion in §<a href="#long68:sec:prime-powers" data-reference-type="ref" data-reference="long68:sec:prime-powers">1</a>, the lcm argument in §<a href="#long68:sec:lcm" data-reference-type="ref" data-reference="long68:sec:lcm">2</a>, and the comparison in §<a href="#long68:sec:residue" data-reference-type="ref" data-reference="long68:sec:residue">4</a>. For the strongest finite conclusions go directly to §<a href="#long68:sec:finite" data-reference-type="ref" data-reference="long68:sec:finite">6</a>. The channel lattice in §<a href="#long68:sec:channels" data-reference-type="ref" data-reference="long68:sec:channels">5</a> is an independent explanation of a limitation, not an input to the finite computations. The research targets in §<a href="#long68:sec:open" data-reference-type="ref" data-reference="long68:sec:open">7</a> are explicitly conditional. The appendices retain longer deductions; source and execution status are recorded separately.

<a id="long68:sec:prime-powers"></a>

# Which prime powers survive reduction

<div id="long68:res:problem" class="problem">

**Problem 1** (Erdős \#68). Is $`S=\sum_{n\ge2}(n!-1)^{-1}`$ irrational?

</div>

Erdős states the question on p. 102 of his 1988 survey and, in the same passage, records the expectation that $`\sum_n1/(n!+t)`$ is irrational, indeed transcendental, for every integer $`t`$ \[erdos1988, p. 102\]. That is conjectural context. Numbering follows [Bloom’s Erdős problem catalogue](https://www.erdosproblems.com/68) \[bloom\]. The catalogue reference retains the manuscript’s historical access date; the current page could not be rechecked during this revision. No irrationality proof is supplied here.

Put
``` math
d_n=n!-1,\qquad H_M=\sum_{n=2}^{M}\frac1{d_n},\qquad
 L_M=\operatorname{lcm}(d_2,\ldots,d_M),\qquad
 A_M=\sum_{n=2}^{M}\frac{L_M}{d_n},
```
so that $`H_M=A_M/L_M`$. Throughout, $`\operatorname{den}(x)`$ is the positive denominator of a rational number in lowest terms. The first question is which prime power present in $`L_M`$ remains in $`\operatorname{den}(H_M)`$. For the largest exponent the answer is a specialisation of the reciprocal-sum valuation formula of Louwsma and Martino \[louwsma-martino, Lemma 4.1, p. 10\]; the proof below writes it out for the denominators $`d_n`$.

The general valuation mechanism is inherited. The explicit factorial specialisation, its cancellation witnesses, and its role in the scale comparison below are the contributions examined here; no priority claim for a new general reciprocal-sum valuation theorem is intended.

<span id="long68:res:lead-prime-pole" label="long68:res:lead-prime-pole"></span>

<div id="long68:res:prime-pole" class="theorem">

**Theorem 2** (maximal prime-power survival). *Let $`M\ge2`$, let $`p`$ be a prime dividing $`L_M`$, and put $`e=v_p(L_M)`$. Let $`J=\{n:2\le n\le M,\ v_p(d_n)=e\}`$ and write $`d_n=p^eu_n`$ for $`n\in J`$. Then, with inverses in $`\mathbb F_p`$,
``` math
\begin{equation}
\label{long68:eq:prime-pole-survival}
 v_p\bigl(\operatorname{den}(H_M)\bigr)=e
 \quad\Longleftrightarrow\quad
 \sum_{n\in J}u_n^{-1}\ne0\quad\hbox{in }\mathbb F_p.
\end{equation}
```*

</div>

<div class="proof">

*Proof.* Write $`L_M=p^eW`$ with $`p\nmid W`$. If $`v_p(d_n)<e`$, then $`p\mid L_M/d_n`$. If $`n\in J`$, then $`u_n(L_M/d_n)=W`$, so $`L_M/d_n\equiv Wu_n^{-1}\pmod p`$. Summing over $`2\le n\le M`$ gives
``` math
\begin{equation}
\label{long68:eq:prime-pole-residue}
 A_M\equiv \frac{L_M}{p^e}\sum_{n\in J}u_n^{-1}\pmod p.
\end{equation}
```

Finally $`\operatorname{den}(H_M)=L_M/\gcd(A_M,L_M)`$, whose $`p`$-valuation is $`e`$ exactly when $`p\nmid A_M`$. Since $`W`$ is invertible modulo $`p`$, that is exactly the stated condition. ◻

</div>

The criterion decides the survival of the full exponent $`e`$. A zero residue gives $`v_p(\operatorname{den}(H_M))<e`$, and further congruences are needed to determine the surviving exponent. The proof uses no property of factorials beyond the displayed denominators, so it applies to any finite sum of reciprocals. What is specific here is the behaviour of the actual family $`d_n=n!-1`$, and that behaviour is not generic.

<a id="two-complete-cancellations."></a>

#### Two complete cancellations.

Take $`M=p-1`$. The indices below with $`p\mid d_n`$ are all of them, and every one has valuation exactly one.

<div class="center">

|    $`p`$ | indices $`n`$         | $`d_n/p\pmod p`$       | inverses modulo $`p`$ |
|---------:|:----------------------|:-----------------------|:----------------------|
|  $`139`$ | $`69,\ 122,\ 137`$    | $`6,\ 49,\ 73`$        | $`116,\ 122,\ 40`$    |
| $`2593`$ | $`349,\ 2243,\ 2591`$ | $`1508,\ 1566,\ 1678`$ | $`1367,\ 356,\ 870`$  |

</div>

The inverse sums are $`278=2\cdot139`$ and $`2593`$. By Theorem <a href="#long68:res:prime-pole" data-reference-type="ref" data-reference="long68:res:prime-pole">2</a>, $`139\nmid\operatorname{den}(H_{138})`$ and $`2593\nmid\operatorname{den}(H_{2592})`$: each prime divides the common denominator of its prefix and vanishes from the reduced one. Both hit lists and both valuations are checked by the recurrence
``` math
r_1=1,\qquad r_n\equiv nr_{n-1}\pmod{p^2},\qquad 0\le r_n<p^2,
```
run through $`n=p-1`$. A hit is an index with $`r_n\equiv1\pmod p`$, its lifted cofactor is $`(r_n-1)/p`$ modulo $`p`$, and valuation two would mean $`r_n=1`$, which occurs at neither prime among the tested indices $`2\le n\le p-1`$. That enumeration is a finite calculation separate from the theorem.

The recurrence is run modulo $`p^2`$, not merely modulo $`p`$: reduction modulo $`p`$ would locate hits but could not establish that their valuations are exactly one. Both examples concern complete cancellation because the maximal exponent is one.

A prime is *prefix-private at $`m`$* when it divides $`d_m`$ and divides none of $`d_2,\ldots,d_{m-1}`$.

The word private is relative to that prefix, not to all future factorial gaps. Later hits can destroy uniqueness in a larger block.

<div id="long68:res:wilson-cofinality" class="proposition">

**Proposition 3** (cofinal first prime occurrences). *For every integer $`B\ge0`$ there are a prime $`q`$ and an integer $`m>B`$ with $`m<q`$, $`q\mid m!-1`$ and $`\gcd(q,k!-1)=1`$ for every $`k`$ with $`2\le k<m`$.*

</div>

<div class="proof">

*Proof.* Choose a prime $`q\ge B!+5`$. Wilson’s theorem gives $`(q-2)!\equiv1\pmod q`$, so the set of indices $`n\ge2`$ with $`q\mid n!-1`$ is nonempty and contains no element above $`q-2`$; let $`m`$ be its least element. If $`m\le B`$, then $`q\le m!-1\le B!-1`$, contradicting the choice of $`q`$. Hence $`m>B`$, and minimality gives the coprimality assertions. ◻

</div>

The construction gives no useful upper bound for $`q`$ in terms of its first hit, and that comparison is what the scale inequalities of §<a href="#long68:sec:residue" data-reference-type="ref" data-reference="long68:sec:residue">4</a> consume. Wilson reflection limits what can be inferred from a large prime factor alone: for odd $`n<q`$ with $`q\mid n!-1`$, the identity $`(q-1-n)!\,n!\equiv(-1)^{n+1}\pmod q`$ gives the reflected hit $`q-n-1`$, which differs from $`n`$ when $`q\ne2n+1`$ and is at least $`2`$ when $`n\le q-3`$. The reflection identity is classical; see Stewart \[stewart2004, p. 462, (4)\].

*Status.* The problem treated here is open, and this note does not close it. Every statement below marked as checked is a proposition that the pinned Lean kernel accepts from the sources this note links to, with no `sorry`, no added axiom, and no unchecked evaluation. That is a claim about the formal statement, not about its mathematical interest, its novelty, or the original problem. The unresolved obligations are named exactly, in their own section, and none of the finite computations, reductions, or no-go results here removes one of them.

*Companion system context.* The [claim and trust boundary](../../../paper/systems/claim-faithful-publication-systems-paper.pdf#nameddest=systems-trust), [cold-clone route to proof authority](../../../paper/systems/cold-clone-to-proof-receipt.pdf#nameddest=cold-clone-authority), and [public contribution protocol](../../../paper/systems/open-source-mathematics-strategy.pdf#nameddest=strategy-protocol) are described in sibling papers. Those descriptions do not change the mathematical status of this note.

<a id="long68:sec:lcm"></a>

# The growth of the common denominator

Theorem <a href="#long68:res:prime-pole" data-reference-type="ref" data-reference="long68:res:prime-pole">2</a> concerns the denominator after reduction. The common denominator before reduction admits an unconditional lower bound of its own, by an elementary argument.

<div id="long68:res:product-lcm" class="lemma">

**Lemma 4** (product, least common multiple, pairwise gcd). *For positive integers $`x_1,\ldots,x_k`$,
``` math
\prod_{i=1}^{k}x_i\ \Big|\ \operatorname{lcm}(x_1,\ldots,x_k)\prod_{i<j}\gcd(x_i,x_j).
```*

</div>

<div class="proof">

*Proof.* Fix a prime $`r`$ and relabel so that $`a_1\le\cdots\le a_k`$, where $`a_i=v_r(x_i)`$. The right-hand side has $`r`$-valuation $`a_k+\sum_{i<j}\min(a_i,a_j)=a_k+\sum_{i=1}^{k-1}(k-i)a_i`$, and the left-hand side has $`\sum_{i=1}^{k}a_i`$. The difference is $`\sum_{i=1}^{k-1}(k-i-1)a_i`$, which is nonnegative. ◻

</div>

The next divisibility is the case $`P=-1`$ of the relation $`\gcd(i!+P(i),j!+P(j))\mid (j!/i!)P(i)-P(j)`$ for $`P\in\mathbb{Z}[X]`$, obtained by multiplying $`i!+P(i)`$ by $`j!/i!`$ and subtracting $`j!+P(j)`$. Luca and Shparlinski use this relation to bound a common divisor of $`n!+P(n)`$ and $`(n+h)!+P(n+h)`$ in the proof of their Lemma 5 \[luca-shparlinski\], and Lai uses it for a common prime-power divisor \[lai, proof of Lemma 2.4, display (2.5)\].

The earlier spacing method of Erdős and Stewart \[erdos-stewart1976, §3, pp. 516–517\] is related background. We now state only the subtraction needed for the lcm argument, rather than importing the prime-factor estimates of those papers.

<div id="long68:res:gap-gcd" class="lemma">

**Lemma 5** (factorial-gap gcd). *For $`2\le i<j`$, the integer $`g=\gcd(i!-1,j!-1)`$ divides $`j!/i!-1`$, and $`g\le j!/i!-1<j^{\,j-i}`$.*

</div>

<div class="proof">

*Proof.* Both $`i!`$ and $`j!`$ are congruent to $`1`$ modulo $`g`$. The quotient $`j!/i!=(i+1)(i+2)\cdots j`$ is an integer, and $`j!=i!\cdot(j!/i!)`$, so $`j!/i!\equiv1\pmod g`$. Since $`j!/i!\ge i+1>1`$, the positive integer $`j!/i!-1`$ is a multiple of $`g`$, whence $`g\le j!/i!-1`$. Finally $`j!/i!`$ is a product of $`j-i`$ integers each at most $`j`$. ◻

</div>

<div id="long68:res:segment" class="lemma">

**Lemma 6** (segment inequality). *For $`2\le k\le N-1`$,
``` math
\begin{equation}
\label{long68:eq:segment}
 \sum_{n=N-k+1}^{N}\log(n!-1)
 \ \le\ \log L_N+\binom{k+1}{3}\log N.
\end{equation}
```*

</div>

<div class="proof">

*Proof.* Apply Lemma <a href="#long68:res:product-lcm" data-reference-type="ref" data-reference="long68:res:product-lcm">4</a> to $`x_n=d_n`$ for $`N-k+1\le n\le N`$. Their least common multiple divides $`L_N`$. By Lemma <a href="#long68:res:gap-gcd" data-reference-type="ref" data-reference="long68:res:gap-gcd">5</a> each pairwise gcd is smaller than $`N^{\,j-i}`$, and over a block of $`k`$ consecutive indices
``` math
\sum_{i<j}(j-i)=\sum_{d=1}^{k-1}d(k-d)=\binom{k+1}{3}.
```
Taking logarithms of the resulting divisibility gives <a href="#long68:eq:segment" data-reference-type="eqref" data-reference="long68:eq:segment">[long68:eq:segment]</a>. ◻

</div>

<div id="long68:res:lcm-growth" class="theorem">

**Theorem 7** (common-denominator growth).
*``` math
\liminf_{N\to\infty}\frac{\log L_N}{N^{3/2}\log N}
 \ \ge\ \frac{2\sqrt2}{3}.
```*

</div>

<div class="proof">

*Proof.* A terminal block keeps every factorial near $`N!`$, but increasing its length also increases the total pairwise-gcd loss. The gain is of order $`kN\log N`$ and the loss of order $`k^3\log N`$, so the useful balance is $`k`$ of order $`\sqrt N`$. Fix $`\alpha>0`$ and take $`k=\lfloor\alpha\sqrt N\rfloor`$, which satisfies $`2\le k\le N-1`$ for all large $`N`$. Put $`u=N-k+1`$.

For the left-hand side of <a href="#long68:eq:segment" data-reference-type="eqref" data-reference="long68:eq:segment">[long68:eq:segment]</a>, use $`n!-1\ge n!/2`$ and $`\log n!\ge n\log n-n`$. Since $`n\mapsto n\log n-n`$ increases,
``` math
\sum_{n=u}^{N}\log(n!-1)\ \ge\ k\,(u\log u-u)-k\log2 .
```
Here $`u\ge N-\alpha\sqrt N`$ and $`k=\alpha\sqrt N+O(1)`$, so $`k\,u\log u=\alpha N^{3/2}\log N+O(N\log N)`$, while $`k\,u=O(N^{3/2})`$ and $`k\log2=O(\sqrt N)`$. Hence the left-hand side is at least $`\alpha N^{3/2}\log N+o(N^{3/2}\log N)`$.

For the right-hand side, $`\binom{k+1}{3}\le(k+1)^3/6`$, so $`\binom{k+1}{3}\log N=\tfrac{\alpha^3}{6}N^{3/2}\log N+o(N^{3/2}\log N)`$. Therefore
``` math
\liminf_{N\to\infty}\frac{\log L_N}{N^{3/2}\log N}
 \ \ge\ \alpha-\frac{\alpha^3}{6}.
```
The right-hand side is maximised at $`\alpha=\sqrt2`$, with value $`\sqrt2-\tfrac{2\sqrt2}{6}=\tfrac{2\sqrt2}{3}`$. ◻

</div>

The displayed proof of the lcm bound uses only Lemmas <a href="#long68:res:product-lcm" data-reference-type="ref" data-reference="long68:res:product-lcm">4</a> and <a href="#long68:res:gap-gcd" data-reference-type="ref" data-reference="long68:res:gap-gcd">5</a>. Its formal counterpart is recorded in the source ledger; the status of that entry is not a blanket assertion about all linked modules. Theorem 12 of Garaev, Luca and Shparlinski \[garaev-luca-shparlinski, arXiv v1, p. 16\] supplies a different input: a uniform $`O(N^{2/3})`$ bound for a fixed nonzero factorial fibre in an interval of length $`N`$ below a prime modulus. The weaker lcm deduction from it is retained in §<a href="#long68:sec:ext-superseded" data-reference-type="ref" data-reference="long68:sec:ext-superseded">9.3</a>, not used here. The revision makes no exhaustive priority claim for the lcm estimate; its precise elementary derivation and the inherited subtraction are stated so that the claim can be assessed without relying on a search conclusion.

<div class="remark">

*Remark 1* (polynomial shifts). Fix $`P\in\mathbb{Z}[X]\setminus\{0\}`$. By Lemma 3 of Luca and Shparlinski \[luca-shparlinski\], in the form given by Lai \[lai, Lemma 2.1\], there is $`n_0\ge2`$, depending only on $`P`$, such that $`n!+P(n)>1`$ for all $`n\ge n_0`$ and $`P(n)(n+1)\cdots(n+h)\ne P(n+h)`$ for all $`n\ge n_0`$ and $`h\ge1`$. The proof of Theorem <a href="#long68:res:lcm-growth" data-reference-type="ref" data-reference="long68:res:lcm-growth">7</a> then gives
``` math
\liminf_{N\to\infty}
 \frac{\log\operatorname{lcm}\{n!+P(n):n_0\le n\le N\}}{N^{3/2}\log N}
 \ \ge\ \frac{2\sqrt2}{3}.
```
For $`n_0\le i<j\le N`$, multiplying $`i!+P(i)`$ by $`j!/i!`$ and subtracting $`j!+P(j)`$ gives
``` math
\gcd\bigl(i!+P(i),\,j!+P(j)\bigr)\ \Big|\ \frac{j!}{i!}P(i)-P(j),
```
which replaces Lemma <a href="#long68:res:gap-gcd" data-reference-type="ref" data-reference="long68:res:gap-gcd">5</a>. The right-hand side is nonzero by the choice of $`n_0`$, and its absolute value is at most $`C_PN^{\,j-i+\deg P}`$ for a constant $`C_P`$. Over a block of $`k`$ indices the pairwise loss therefore grows by $`O_P(k^2\log N)`$, which is $`O_P(N\log N)`$ when $`k=\lfloor\alpha\sqrt N\rfloor`$. Since $`n!+P(n)\ge n!/2`$ for large $`n`$, the lower estimate for the sum of logarithms is unchanged. The cutoff is needed, since for $`P=-2`$ the factor at $`n=2`$ vanishes. The hypothesis $`P\ne0`$ is needed as well, since for $`P=0`$ the least common multiple is $`N!`$ whatever the cutoff.

</div>

<a id="a-non-polynomial-comparison."></a>

#### A non-polynomial comparison.

For $`n!+2^n-1`$, Luca and Shparlinski \[luca-shparlinski-exp, Lemmas 2.1–2.3, pp. 860–862\] eliminate the exponential term using three hits; multiplicative order enters the counting. Their valuation-layer identity \[luca-shparlinski-exp, (3.2), p. 863\] records repeated prime-power divisibility. These are related tools, not inputs to Theorem <a href="#long68:res:lcm-growth" data-reference-type="ref" data-reference="long68:res:lcm-growth">7</a>, and no extension to general non-polynomial perturbations is asserted.

Within the terminal-block estimate just proved, maximising $`\alpha-\alpha^3/6`$ gives $`2\sqrt2/3`$. This is an optimisation of that one-parameter bound, not an optimality theorem for all block selections or all gcd arguments. The discarded factorial term has size $`N^{3/2}`$, so a finite normalised ratio need not be close to the limiting lower bound.

Theorem <a href="#long68:res:lcm-growth" data-reference-type="ref" data-reference="long68:res:lcm-growth">7</a> is a statement about $`L_N`$ and not about $`\operatorname{den}(H_N)`$. Consecutive denominators $`(N-1)!-1`$ and $`N!-1`$ are already coprime for $`N\ge3`$, so the qualitative failure of common-denominator clearing follows from two terms; the estimate is the quantitative growth statement. Theorem <a href="#long68:res:prime-pole" data-reference-type="ref" data-reference="long68:res:prime-pole">2</a> and the cancellations at $`139`$ and $`2593`$ show why the substitution fails: a prime may occupy the common denominator and be absent from the reduced one. One cancelled prime is not an asymptotic cancellation theorem.

For completeness, the consecutive coprimality follows because their gcd divides $`N-1`$, whereas $`(N-1)!-1`$ is coprime to $`N-1`$. Thus the two-term argument is qualitative and does not depend on the asymptotic constant.

The direction of denominator control matters. Write $`H_N=\widehat A_N/Q_N`$ in lowest terms, reserving $`A_N`$ above for the numerator over the full common denominator. Under the hypothetical identity $`S=a/q`$, with $`a\in\mathbb{Z}`$ and $`q\ge1`$, positivity of the tail gives
``` math
qQ_N(S-H_N)=aQ_N-q\widehat A_N\in\mathbb{Z}_{>0}.
```
A direct clearing contradiction therefore requires an upper estimate that makes $`qQ_N(S-H_N)<1`$ for some $`N`$; equivalently, it needs $`Q_N`$ to be small relative to the reciprocal tail. A lower bound on $`Q_N`$ points in the opposite direction. Indeed, the rational limit $`1`$ and the approximants $`1-1/Q_N`$ have arbitrarily large reduced denominators without any irrationality. The inequality $`d_N(S-H_N)<1`$ alone would not repair the argument, because $`d_N`$ generally does not clear the earlier summands of $`H_N`$. The prime-pole analysis describes which factors survive reduction, but it does not yet supply the required upper control on $`Q_N`$.

For linear forms in $`p`$-adic zeta values, with $`p\ge5`$ a fixed prime and $`n`$ the index of the form, Lai, Lupu and Sprang quantify a saving of this kind. They bound the denominators of the coefficients by powers of $`\operatorname{lcm}(1,\ldots,n)`$, show that the bound may be divided by a product $`\Phi_n`$ of prime powers, and compute the growth rate of $`\Phi_n`$ \[lai-lupu-sprang, Lemmas 5.3–5.7 and 7.3\]. That saving enters the inequality \[lai-lupu-sprang, (8.1)\] under which the rescaled forms, which have integer coefficients, meet the irrationality criterion \[lai-lupu-sprang, Lemma 2.1, p. 3\] that they quote from Lai \[lai-2adic, Lemma 2.1, p. 4\]: nonzero values whose $`p`$-adic size, multiplied by the largest absolute value of a coefficient, tends to zero. The corresponding saving for $`H_N`$ is the ratio $`L_N/Q_N`$.

This ratio is an integer. Merely naming it supplies neither its growth nor a small linear form; the analogy is about what an eventual estimate would have to accomplish. Theorem <a href="#long68:res:prime-pole" data-reference-type="ref" data-reference="long68:res:prime-pole">2</a> decides, for each prime $`p\mid L_N`$, whether $`p`$ divides this ratio; no asymptotic lower bound for the ratio is established here. This paragraph compares the two methods; no $`p`$-adic theorem is applied to $`S`$.

<a id="long68:sec:carry"></a>

# Carries and the rationality boundary

Define the strict integer successor and the predecessor gap by
``` math
Z_m=\lfloor m!H_m\rfloor+1,\qquad
 \Delta_m=Z_{m-1}-(m-1)!H_{m-1}\quad(m\ge3),
```
so $`0<\Delta_m\le1`$, and define the integer carry $`b_m`$ by
``` math
\begin{equation}
\label{long68:eq:carry-recurrence}
 Z_m=mZ_{m-1}+1-b_m .
\end{equation}
```

Call $`b_m=1`$ a *unit carry*. Put $`E_m=m!(S-H_m)`$ and $`\varepsilon_m=1/(m!-1)`$. Since $`d_{n+1}>(n+1)d_n`$, a geometric majorant gives the tail estimate
``` math
\begin{equation}
\label{long68:eq:tail-bound}
 0<E_m<\frac{2\,m!}{(m+1)!-1}<\frac2m\le1\qquad(m\ge2).
\end{equation}
```
The proof of the next theorem feeds this estimate into the factorial-tail integrality argument that Hančl and Tijdeman use for factorial series with integer coefficients \[hancl-tijdeman, Lemma 2.1 and the following remark, p. 385\].

<span id="long68:res:lead-carry-equivalence" label="long68:res:lead-carry-equivalence"></span> <span id="long68:res:strict-successor-complete-characterization" label="long68:res:strict-successor-complete-characterization"></span>

<div id="long68:res:carry-equivalence" class="theorem">

**Theorem 8** (strict-successor characterisation). *For $`m\ge3`$,
``` math
\begin{equation}
\label{long68:eq:unit-window}
 b_m=1
 \iff m\mid Z_m
 \iff 1+\varepsilon_m<m\Delta_m\le2+\varepsilon_m .
\end{equation}
```
The historical manuscript cites `Erdos68/PaperCompleteExisting.lean`, line 79. This module is absent from the retained source pin; this citation does not establish kernel verification at that pin.*

*Moreover
``` math
\begin{align}
 S\in\mathbb{Q}
 &\iff b_m=1\ \hbox{for all sufficiently large }m,
 \label{long68:eq:carry-rationality}\\
 S\notin\mathbb{Q}
 &\iff \forall B\ \exists m>B:\ m\nmid Z_m .
 \label{long68:eq:strict-misses}
\end{align}
```
If $`S=a/q`$ with $`a\in\mathbb{Z}`$, $`q\ge1`$ and $`b_m\ne1`$, then $`q\nmid(m-1)!`$ and $`q\ge m`$.*

</div>

<div class="proof">

*Proof.* From $`m!H_m=mZ_{m-1}-m\Delta_m+1+\varepsilon_m`$ one gets $`b_m=\lceil m\Delta_m-1-\varepsilon_m\rceil`$ with $`-1\le b_m\le m-1`$, which gives both equivalences in <a href="#long68:eq:unit-window" data-reference-type="eqref" data-reference="long68:eq:unit-window">[long68:eq:unit-window]</a>, endpoints included.

Suppose $`S=a/q`$ and $`q\mid(m-1)!`$. For $`j=m-1`$ and $`j=m`$ the number $`j!\,S`$ is an integer, and $`j!H_j=j!\,S-E_j`$ with $`0<E_j<1`$ by <a href="#long68:eq:tail-bound" data-reference-type="eqref" data-reference="long68:eq:tail-bound">[long68:eq:tail-bound]</a>, so $`Z_j=j!\,S`$. Substituting into <a href="#long68:eq:carry-recurrence" data-reference-type="eqref" data-reference="long68:eq:carry-recurrence">[long68:eq:carry-recurrence]</a> forces $`b_m=1`$. Every fixed $`q`$ divides $`(m-1)!`$ eventually, which gives one direction of <a href="#long68:eq:carry-rationality" data-reference-type="eqref" data-reference="long68:eq:carry-rationality">[long68:eq:carry-rationality]</a> and, by contraposition, the final assertion; $`q<m`$ would imply $`q\mid(m-1)!`$. Conversely, an eventual unit-carry tail makes $`Z_m/m!`$ eventually constant, and $`0<Z_m/m!-H_m\le1/m!`$ with $`H_m\to S`$ identifies that constant as $`S`$, which is then rational. Negating <a href="#long68:eq:carry-rationality" data-reference-type="eqref" data-reference="long68:eq:carry-rationality">[long68:eq:carry-rationality]</a> gives <a href="#long68:eq:strict-misses" data-reference-type="eqref" data-reference="long68:eq:strict-misses">[long68:eq:strict-misses]</a>. ◻

</div>

The divisibility conclusion retains prime-power multiplicities, so it constrains valuations, prime support included. It does not require a prime divisor of $`q`$ larger than $`m-1`$.

<a id="long68:sec:adjacent-unit-no-go"></a>

## Why one proposed window argument is circular

One route to cofinal non-unit carries tries to exclude two consecutive unit carries by extracting a prime-power or quotient-gcd obstruction from their cleared width-one window. The exact two-step recurrence shows what that window can deliver. Let $`U_k`$ and $`V_k`$ be the numerator and denominator of the reduced predecessor gap and let $`G_k>0`$ be the exact transition normaliser. For $`m\ge3`$, the two unit carries are equivalent to an integer offset $`\Omega_m`$ with $`0<\Omega_m\le D_m`$, the window denominator telescopes independently of the carry values,
``` math
D_m=V_{m+2}G_{m+1}G_m=V_m(m!-1)\bigl((m+1)!-1\bigr),
```
and under the pair assumption the offset factors to match, $`\Omega_m=U_{m+2}G_{m+1}G_m`$. Cancelling the common positive normaliser reduces the complete window to
``` math
0<U_{m+2}\le V_{m+2},
```
which every reduced positive gap in $`(0,1]`$ already satisfies. For that specified window, therefore, an obstruction obtained only after imposing the carry pair rewrites a bound that holds anyway. The calculation does not disprove adjacent unit carries and does not exclude an independent restriction on the transition numerators or their valuations, which would need its own argument constraining the predecessor state before the pair is assumed.

<a id="the-companion-coordinate"></a>

## The companion coordinate

Let $`C=\sum_{n\ge2}\bigl(n!(n!-1)\bigr)^{-1}`$. The identity $`1/(n!-1)=1/n!+1/(n!(n!-1))`$ and absolute convergence give
``` math
\begin{equation}
\label{long68:eq:companion-decomposition}
 S=C+e-2 .
\end{equation}
```
The canonical factorial digits of a real $`x`$ are $`a_m(x)=\lfloor m!x\rfloor-m\lfloor(m-1)!x\rfloor\in\{0,\ldots,m-1\}`$, and $`x`$ is rational exactly when they vanish from some index on. The criterion goes back to Cantor \[cantor1869\]; Galambos treats the rationality of Cantor series in \[galambos1976, Ch. II, §2.1, pp. 21–22\], and Koepf and Schmersau prove the irrationality direction for nonterminating factorial expansions whose digits are not eventually maximal \[koepf-schmersau, Example 3.2, p. 121\].

<span id="long68:res:lead-companion-orbit" label="long68:res:lead-companion-orbit"></span>

<div id="long68:res:companion-orbit" class="proposition">

**Proposition 9** (companion-orbit criterion).
*``` math
S\in\mathbb{Q}
 \quad\Longleftrightarrow\quad
 \lfloor m!C\rfloor\equiv-2\pmod m
 \quad\hbox{for all sufficiently large }m.
```*

</div>

<div class="proof">

*Proof.* Put $`J_m=\sum_{k=0}^{m}m!/k!`$. Then $`J_m`$ is an integer, every summand with $`k<m`$ is divisible by $`m`$ and the summand at $`k=m`$ is $`1`$, so $`J_m\equiv1\pmod m`$; and $`0<m!\,e-J_m<1`$ for $`m\ge2`$.

Suppose $`S`$ is rational. For all large $`m`$ both $`(m-1)!\,S`$ and $`m!\,S`$ are integers, so $`m\mid m!\,S`$. Multiplying <a href="#long68:eq:companion-decomposition" data-reference-type="eqref" data-reference="long68:eq:companion-decomposition">[long68:eq:companion-decomposition]</a> by $`m!`$ and using $`\lfloor -m!\,e\rfloor=-J_m-1`$ gives $`\lfloor m!C\rfloor=m!\,S+2\,m!-J_m-1\equiv-2\pmod m`$.

Conversely, assume the congruence from some index on. Because $`0\le a_m(C)<m`$, for $`m\ge3`$ the congruence is equivalent to $`a_m(C)=m-2`$. Choose $`N`$ beyond the exceptional indices. The canonical expansion gives
``` math
C=\frac{\lfloor N!C\rfloor}{N!}+\sum_{m>N}\frac{m-2}{m!},
```
and the telescope $`\sum_{m>N}(m-1)/m!=1/N!`$ turns this into
``` math
S=C+e-2
 =\frac{\lfloor N!C\rfloor+1}{N!}+\sum_{m=2}^{N}\frac1{m!},
```
which is rational. ◻

</div>

<a id="escape-from-a-smaller-interval"></a>

## Escape from a smaller interval

Write $`\theta_m=\{m!\,S\}`$. The exact lower interval has width $`E_m/m\in(0,2/m^2)`$, so the target shrinks quadratically.

<div id="long68:res:lower-escape" class="proposition">

**Proposition 10** (lower-interval criterion).
*``` math
\begin{equation}
\label{long68:eq:lower-escape}
 S\notin\mathbb{Q}
 \quad\Longleftrightarrow\quad
 \forall B\ \exists m>B:\ E_m\le m\theta_{m-1}.
\end{equation}
```
For $`m\ge3`$ the finite condition
``` math
\begin{equation}
\label{long68:eq:finite-escape}
 m\Delta_m\le1+\varepsilon_m
 \quad\hbox{or}\quad
 1+\varepsilon_m+\frac2m\le m\Delta_m
\end{equation}
```
implies the escape inequality in <a href="#long68:eq:lower-escape" data-reference-type="eqref" data-reference="long68:eq:lower-escape">[long68:eq:lower-escape]</a>. Cofinally many instances of <a href="#long68:eq:finite-escape" data-reference-type="eqref" data-reference="long68:eq:finite-escape">[long68:eq:finite-escape]</a> therefore imply $`S\notin\mathbb{Q}`$.*

</div>

<div class="proof">

*Proof.* If $`S`$ is rational, the remainders $`\theta_{m-1}`$ vanish eventually while $`E_m>0`$, so the escape inequality fails eventually. Conversely, suppose $`m\theta_{m-1}<E_m`$ for every sufficiently large $`m`$. By <a href="#long68:eq:tail-bound" data-reference-type="eqref" data-reference="long68:eq:tail-bound">[long68:eq:tail-bound]</a> this gives $`m\theta_{m-1}<1`$, so $`a_m(S)=0`$ and $`\theta_m=m\theta_{m-1}`$. A positive remainder grows past one under that recurrence, so the remainders vanish and $`S`$ is rational.

For the finite implication, suppose $`m\theta_{m-1}<E_m`$. The tail recurrence is $`mE_{m-1}=1+\varepsilon_m+E_m`$, so $`E_{m-1}>E_m/m>\theta_{m-1}\ge0`$, and with $`0<E_{m-1}<1`$ the strict-successor identity gives $`\Delta_m=E_{m-1}-\theta_{m-1}`$. Hence
``` math
1+\varepsilon_m<m\Delta_m=1+\varepsilon_m+E_m-m\theta_{m-1}
 \le1+\varepsilon_m+E_m<1+\varepsilon_m+\frac2m,
```
which contradicts <a href="#long68:eq:finite-escape" data-reference-type="eqref" data-reference="long68:eq:finite-escape">[long68:eq:finite-escape]</a>. ◻

</div>

Escape at a single index does not give a non-unit carry there. The exact classification is
``` math
\begin{equation}
\label{long68:eq:escape-classification}
 E_m\le m\theta_{m-1}
 \quad\Longleftrightarrow\quad
 b_m\ne1\ \hbox{ or }\ a_m(S)=m-1
 \qquad(m\ge3),
\end{equation}
```
The historical manuscript cites `Erdos68/PaperCompleteExisting.lean`, line 104. This module is absent from the retained source pin; this citation does not establish kernel verification at that pin.

so the maximal-digit branch is available. It is realised: at $`m=52`$ exact rational arithmetic gives $`b_{52}=1`$ together with $`52\,\Delta_{52}>1+\varepsilon_{52}+2/52`$, the margin being about $`0.5689674908`$. Since $`52`$ is composite, this settles nothing about prime indices, and the cofinal statement in Proposition <a href="#long68:res:lower-escape" data-reference-type="ref" data-reference="long68:res:lower-escape">10</a> does not identify escape with a non-unit carry.

<a id="the-whole-shifted-family"></a>

## The whole shifted family

Erdős asked about $`S`$ inside a family, and the same coordinate covers the family. For an integer $`t\ge-1`$ put $`S_t=\sum_{n\ge2}1/(n!+t)`$ and $`C_t=\sum_{n\ge2}1/\bigl(n!(n!+t)\bigr)`$, so that $`S_t=-tC_t+(e-2)`$.

The restriction $`t\ge-1`$ keeps every denominator positive for $`n\ge2`$. All series in this identity converge absolutely.

<div id="long68:res:shift-family" class="theorem">

**Theorem 11** (uniform family boundary). *For every integer $`t\ge-1`$, the series $`S_t`$ is rational exactly when
``` math
\bigl\lceil t\,m!\,C_t\bigr\rceil\equiv2\pmod m
```
for all sufficiently large $`m`$, and irrational exactly when that residue is missed cofinally. The member $`t=-1`$ is $`S`$, and the member $`t=0`$ is $`e-2`$, whose orbit is constantly $`0`$ and therefore misses the residue class at every $`m\ge3`$, so the boundary returns the irrationality of $`e`$.*

</div>

<div class="proof">

*Proof.* Put $`Y=-tC_t`$, so that $`S_t=Y+e-2`$. The proof of Proposition <a href="#long68:res:companion-orbit" data-reference-type="ref" data-reference="long68:res:companion-orbit">9</a> applies to any real $`Y`$: rationality of $`Y+e-2`$ forces $`\lfloor m!Y\rfloor\equiv-2\pmod m`$ eventually. Conversely, that congruence forces the canonical digits of $`Y`$ to equal $`m-2`$ eventually; adding the factorial series of $`e-2`$ leaves an eventually telescoping tail, hence a rational sum. Finally $`\lceil t m!C_t\rceil=-\lfloor m!Y\rfloor`$ translates the congruence. Negation gives the cofinal statement. For $`t=0`$, the left side is zero, which is not congruent to $`2`$ for $`m\ge3`$. ◻

</div>

The $`t=0`$ specialisation recovers the classical irrationality of $`e`$. For $`t\ne0`$ this paper supplies no cofinal estimate for the displayed orbit. This is a statement about the scope of the present argument, not an assertion that every other member has the same current literature status.

<a id="long68:sec:residue"></a>

# From denominator structure to a scale criterion

For an integer $`p\ge3`$ put $`I_p=\{2,\ldots,2p-1\}`$ and $`F_p=(p-1)!`$, and define
``` math
\begin{align*}
 D_p&=\operatorname{lcm}_{\substack{i,j\in I_p\\ i<j}}\gcd(d_i,d_j),
 &C_p&=\operatorname{lcm}(F_p,D_p),\\
 L^{\mathrm{blk}}_p&=\operatorname{lcm}(F_p,d_2,\ldots,d_{2p-1}),
 &R_p&=L^{\mathrm{blk}}_p/C_p .
\end{align*}
```
The normalised core is $`\widetilde C_p=C_p/F_p`$, so that
``` math
\begin{equation}
\label{long68:eq:core-normalisation}
 L^{\mathrm{blk}}_p=C_pR_p=F_p\widetilde C_pR_p .
\end{equation}
```
The historical manuscript cites `Erdos68/PaperCompleteExisting.lean`, line 125. This module is absent from the retained source pin; this citation does not establish kernel verification at that pin.

The factorial base $`F_p`$ belongs inside every one of these quantities, and omitting it changes the scale comparisons below by a factorial factor. Put
``` math
T_p=\sum_{i\in I_p}\frac{L^{\mathrm{blk}}_p}{d_i},\qquad
 \rho_p=(-T_p)\bmod R_p,\qquad
 K_p=2p^2(2p-1)! ,
```
with $`\rho_p`$ the least nonnegative representative. All of these depend only on a finite prefix.

In this section $`p`$ is a natural parameter, not necessarily a prime. Prime divisors used in the valuation argument are separate variables. The distinction matters when the parameter is tailored to a first hit.

The core records every prime-power layer occurring in at least two gaps, together with the base. A prime dividing $`R_p`$ therefore has a unique maximal-valuation gap above the base valuation, so the argument of Theorem <a href="#long68:res:prime-pole" data-reference-type="ref" data-reference="long68:res:prime-pole">2</a> applies to it and gives $`\gcd(T_p,R_p)=1`$. This is where the first theorem returns. Consequently, when $`R_p>1`$, the ratio $`T_p/R_p=C_pH_{2p-1}`$ is not an integer and
``` math
\begin{equation}
\label{long68:eq:gap-normalisation}
 \frac{\rho_p}{R_p}
 =\bigl\lceil C_pH_{2p-1}\bigr\rceil-C_pH_{2p-1}\in(0,1),
\end{equation}
```
a gap to the next integer.

<div id="long68:res:global-residue" class="theorem">

**Theorem 12** (complementary-residue criterion). *Suppose that for every $`B`$ there is a natural parameter $`p\ge3`$ with $`p>B`$, $`R_p>1`$, and
``` math
\begin{equation}
\label{long68:eq:global-scale}
 (2p+1)L^{\mathrm{blk}}_p<K_p\rho_p .
\end{equation}
```
Then $`S`$ is irrational.*

</div>

This natural-parameter form is also the [source form of the global complementary criterion](https://github.com/wcook04/plectis-erdos/blob/f36a98bf3d3e6f65f1074e3b800e3293d5b8a51a/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L156-L168).

<div class="proof">

*Proof.* Suppose $`S=a/q`$ with $`q\ge1`$, and take such a parameter with $`p>\max(q,3)`$ satisfying the hypotheses. Then $`q\mid F_p`$, so $`U=L^{\mathrm{blk}}_p(S-H_{2p-1})`$ is a positive integer, and $`L^{\mathrm{blk}}_pS=R_p(C_pS)`$ is a multiple of $`R_p`$; hence $`U\equiv-T_p\pmod{R_p}`$ and $`U\ge\rho_p`$. For the other side, $`1/(n!-1)<2/n!`$ for $`n\ge3`$, and a geometric majorant gives
``` math
0<S-H_{2p-1}<\frac{2}{(2p)!}\cdot\frac{2p+1}{2p}=\frac{2p+1}{K_p}.
```
Therefore $`K_p\rho_p\le K_pU<(2p+1)L^{\mathrm{blk}}_p`$, contrary to <a href="#long68:eq:global-scale" data-reference-type="eqref" data-reference="long68:eq:global-scale">[long68:eq:global-scale]</a>. ◻

</div>

Cancelling $`R_p`$ in <a href="#long68:eq:global-scale" data-reference-type="eqref" data-reference="long68:eq:global-scale">[long68:eq:global-scale]</a> through <a href="#long68:eq:core-normalisation" data-reference-type="eqref" data-reference="long68:eq:core-normalisation">[long68:eq:core-normalisation]</a> displays the quantitative issue directly:
``` math
\begin{equation}
\label{long68:eq:core-gap-scale}
 (2p+1)C_p<K_p\frac{\rho_p}{R_p}.
\end{equation}
```
The private modulus has gone. A supply of large private factors therefore supplies neither a small collision core nor a lower bound for the normalised gap $`\rho_p/R_p`$, which is at most one. That is the exact reason Proposition <a href="#long68:res:wilson-cofinality" data-reference-type="ref" data-reference="long68:res:wilson-cofinality">3</a> does not close the argument.

Writing $`\eta_p=\rho_p/R_p`$, the sufficient comparison becomes
``` math
\log\widetilde C_p-\log\eta_p
 <\log\frac{2p^2(2p-1)!}{(2p+1)(p-1)!}
 =p\log p+(2\log2-1)p+O(\log p).
```
It is a joint budget for collision loss and the real gap. The bound $`\rho_p\ge1`$ gives only $`\eta_p\ge1/R_p`$ and may be far too small.

<span id="long68:res:lead-moving-factor-split" label="long68:res:lead-moving-factor-split"></span> <span id="long68:res:moving-factor-scale-split" label="long68:res:moving-factor-scale-split"></span> The moving-factor criterion is a more specialised sufficient condition. For a prefix-private prime $`q`$ at $`m\ge4`$ the tailored block parameter is $`p=\lfloor m/2\rfloor+1`$, which need not itself be prime. For the factors $`1`$ and $`q`$ of the private modulus the factor-pair floor is $`\min(\rho_p,R_p/q)`$, and its scale inequality splits exactly:
``` math
\begin{equation}
\label{long68:eq:factor-split}
 (2p+1)L^{\mathrm{blk}}_p<K_p\min(\rho_p,R_p/q)
 \quad\Longleftrightarrow\quad
 \begin{cases}
 (2p+1)L^{\mathrm{blk}}_p<K_p\rho_p,\\
 (2p+1)C_pq<K_p .
 \end{cases}
\end{equation}
```

Testing both entries of the minimum and using <a href="#long68:eq:core-normalisation" data-reference-type="eqref" data-reference="long68:eq:core-normalisation">[long68:eq:core-normalisation]</a> gives the equivalence, so the reduction has no opaque floor premise left. Cofinal instances of both inequalities imply irrationality. The single global condition of Theorem <a href="#long68:res:global-residue" data-reference-type="ref" data-reference="long68:res:global-residue">12</a> is separately sufficient, so the pair is one sufficient route among several.

<span id="long68:res:split-factor-normalized-collision" label="long68:res:split-factor-normalized-collision"></span> <span id="long68:bdry:fixed-owner-absorption" label="long68:bdry:fixed-owner-absorption"></span> One structural limitation is worth recording beside these criteria. If the owner index $`n`$ is fixed and $`p>n!-1`$, then $`n!-1`$ divides $`(p-1)!`$, so its private quotient in the block at $`p`$ is exactly one. Large private quotients seen at small blocks, such as the factor $`719`$ owned at $`n=6`$, are therefore finite-range phenomena, and the selected factors must escape with $`p`$.

<a id="long68:sec:channels"></a>

# A limitation of finite-channel cancellation

For a finitely supported integer vector $`c=(c_i)`$ on indices $`i\ge2`$, put
``` math
M(c)=\sum_i c_i\,i!,\qquad
 W_{d,i}=\frac{i!}{(d!)^{\lfloor i/d\rfloor}},\qquad
 V_{d}(c)=\sum_i c_iW_{d,i}\quad(d\ge2).
```
Each $`W_{d,i}`$ is an integer: writing $`i=kd+r`$ with $`0\le r<d`$, the quotient $`i!/\bigl((d!)^kr!\bigr)`$ is a multinomial coefficient. Since $`i!=(d!)^{\lfloor i/d\rfloor}W_{d,i}`$ and $`d!\equiv1\pmod{d!-1}`$,
``` math
\begin{equation}
\label{long68:eq:channel-congruence}
 V_{d}(c)\equiv M(c)\pmod{d!-1}.
\end{equation}
```

<div id="long68:res:normalform" class="theorem">

**Theorem 13** (integral normal form). *For every finite integer support and every $`d\ge2`$ there is an integer $`k`$ with $`V_{d}(c)=M(c)+(d!-1)k`$.*

</div>

<div class="proof">

*Proof.* By <a href="#long68:eq:channel-congruence" data-reference-type="eqref" data-reference="long68:eq:channel-congruence">[long68:eq:channel-congruence]</a>, $`d!-1`$ divides $`V_d(c)-M(c)`$. Thus $`k=(V_d(c)-M(c))/(d!-1)`$ is an integer and gives the identity. The modulus is positive also at $`d=2`$, when it equals one. ◻

</div>

<div id="long68:res:bandbreakpoint" class="theorem">

**Theorem 14** (quotient-band breakpoint). *Let $`d\ge2`$ and $`k\ge0`$, and suppose every supported index $`i`$ satisfies $`kd\le i<(k+1)d`$. Then $`M(c)=(d!)^kV_{d}(c)`$. In particular, cancellation in the first band $`d\le i<2d`$ forces $`M(c)=0`$; and if every supported index is at least $`d`$ while $`M(c)\ne0`$ and $`V_{d}(c)=0`$, then some supported index is at least $`2d`$.*

</div>

<div class="proof">

*Proof.* Within one band the quotient $`\lfloor i/d\rfloor`$ is the constant $`k`$, so $`i!=(d!)^kW_{d,i}`$ for every supported index and the factor $`(d!)^k`$ comes out of the sum. The two consequences follow by taking $`k=1`$ and by contraposition. ◻

</div>

This is a direct consequence of the constant quotient; no valuation estimate enters. A nonzero moment therefore cannot be hidden entirely below $`2d`$ while the $`d`$-channel cancels. This is a finite-family obstruction: it constructs no cancelling family and says nothing about simultaneous channels or residual size.

Consequently a vanishing $`d`$-th channel forces $`(d!-1)\mid M(c)`$, and annihilating every channel $`2\le d\le D`$ forces $`L_D\mid M(c)`$, where $`L_D=\operatorname{lcm}_{2\le d\le D}(d!-1)`$ is the same quantity as in §<a href="#long68:sec:lcm" data-reference-type="ref" data-reference="long68:sec:lcm">2</a>. Every zero-moment variation of the support changes a normalised channel contribution by an integer only, so such variations cannot manufacture an extra fractional cancellation coordinate.

<a id="the-exact-low-channel-lattice-and-residual-class"></a>

## The exact low-channel lattice and residual class

Fix $`D\ge2`$. The low-channel equations, the support equation and the residual identity answer different questions: solvability, admissibility on $`n\ge2`$, and the remaining fractional obstruction, respectively.

The integral divisor basis makes the preceding divisibility statement exact. For the coordinate calculation only, enlarge the coefficient space to finitely supported integer vectors on $`n\ge1`$, with $`M`$ and $`V_{d}(\cdot)`$ given by the same formulas; this introduces no term $`1/(1!-1)`$ into $`S`$. Set
``` math
T_n=ne_{n-1}-e_n,\qquad
 U_n=T_n-\sum_{\substack{d\mid n\\2\le d<n}}W_{d,n}U_d\quad(n\ge2),\qquad
 K_D=L_De_1-\sum_{d=2}^{D}\frac{L_D}{d!-1}U_d .
```
The quotient $`\lfloor i/d\rfloor`$ changes between $`i=n-1`$ and $`i=n`$ exactly when $`d\mid n`$, so $`V_{d}(T_n)=(d!-1)W_{d,n}\mathbf 1_{d\mid n}`$, and induction gives $`M(U_n)=0`$ and $`V_{d}(U_n)=(d!-1)\mathbf 1_{d=n}`$. Hence $`M(K_D)=L_D`$ and $`V_{d}(K_D)=0`$ for $`2\le d\le D`$. The change from $`e_1,T_2,T_3,\ldots`$ to $`e_1,U_2,U_3,\ldots`$ is integral triangular with unit diagonal, so $`e_1,U_2,U_3,\ldots`$ is an integral basis, and applying $`M`$ and each $`V_{d}(\cdot)`$ gives the unique expansion
``` math
c=M(c)\,e_1+\sum_{d\ge2}\frac{V_{d}(c)-M(c)}{d!-1}\,U_d .
```
Consequently every vector of the enlarged space whose channels $`2,\ldots,D`$ vanish has a unique expression
``` math
\begin{equation}
\label{long68:eq:low-channel-basis}
 c=tK_D+\sum_{n>D}z_nU_n,
 \qquad M(c)=tL_D,
\end{equation}
```
with finitely many nonzero integers $`z_n`$. Write $`a_D=[e_1]K_D`$ and $`u_n=[e_1]U_n`$. Requiring support on $`n\ge2`$ adds precisely the scalar equation
``` math
\begin{equation}
\label{long68:eq:low-channel-support}
 ta_D+\sum_{n>D}z_nu_n=0.
\end{equation}
```
The scalar coefficients satisfy $`u_2=2`$ and $`u_n=-\sum_{d\mid n,\ 2\le d<n}W_{d,n}u_d`$ for $`n>2`$; in particular $`u_{2p}=-(2p)!/2^{p-1}`$ for every prime $`p`$. If $`p`$ is a prime with $`D/2<p\le D`$ and $`H=D(2p-1)`$, then
``` math
\begin{equation}
\label{long68:eq:finite-horizon}
 \gcd\{u_n:n>D\}=\gcd(u_{D+1},\ldots,u_H)>0,\qquad H<2D^2 .
\end{equation}
```
Indeed, the finite gcd $`g`$ divides $`u_{2p}\ne0`$ and hence $`(2p)!`$. For $`n>H`$ and a divisor $`d\le D`$ of $`n`$ one has $`n/d\ge2p`$, and $`(n/d)!`$ divides $`W_{d,n}`$, the quotient counting partitions of $`n`$ points into $`n/d`$ unordered blocks of size $`d`$; thus $`g\mid W_{d,n}`$. Strong induction in the recurrence handles the remaining divisors $`D<d<n`$, so $`g`$ divides every $`u_n`$ with $`n>D`$. Bertrand’s postulate supplies $`p`$ for $`D\ge3`$, and $`p=2`$ serves for $`D=2`$; finally $`H\le D(2D-1)<2D^2`$. The short note proves the same determination as its Theorem 3.2.

<div id="long68:res:moment-ideal" class="theorem">

**Theorem 15** (exact attainable moment ideal). *Fix $`D\ge2`$ and a prime $`p`$ with $`D/2<p\le D`$. Put
``` math
H=D(2p-1),\qquad
 G_D=\gcd\{|u_n|:D<n\le H\},\qquad
 \mu_D=L_D\frac{G_D}{\gcd(G_D,a_D)}.
```
The moments of finite integer vectors supported on $`n\ge2`$ and cancelling all channels $`2,\ldots,D`$ are exactly $`\mu_D\mathbb{Z}`$. The integer $`\mu_D`$ is positive, is independent of the eligible prime $`p`$, and is attained by a vector of coefficient content one, hence by a primitive vector.*

</div>

<div class="proof">

*Proof.* By <a href="#long68:eq:finite-horizon" data-reference-type="eqref" data-reference="long68:eq:finite-horizon">[long68:eq:finite-horizon]</a>, $`G_D>0`$ is the gcd of the whole tail $`\{u_n:n>D\}`$, and $`H<2D^2`$. Thus the finite integer combinations in <a href="#long68:eq:low-channel-support" data-reference-type="eqref" data-reference="long68:eq:low-channel-support">[long68:eq:low-channel-support]</a> form $`G_D\mathbb{Z}`$, so that the equation is soluble exactly when $`G_D\mid ta_D`$. Dividing by $`\gcd(G_D,a_D)`$ shows that $`t`$ is a multiple of $`G_D/\gcd(G_D,a_D)`$, and <a href="#long68:eq:low-channel-basis" data-reference-type="eqref" data-reference="long68:eq:low-channel-basis">[long68:eq:low-channel-basis]</a> gives the displayed moment ideal. Bezout coefficients attain its positive generator. If an attaining vector had a nontrivial common coefficient divisor, division by that divisor would produce a smaller positive attainable moment. Hence its content is one. The ideal itself is intrinsic, so two eligible primes give the same positive generator. ◻

</div>

For
``` math
\mathcal R(c)=\sum_{d\ge2}\frac{V_{d}(c)}{d!-1},\qquad
 H_D=\sum_{2\le d\le D}\frac1{d!-1},
```
the same coordinates retain the real information that the moment ideal alone does not see.

<div id="long68:res:residual-transparency" class="theorem">

**Theorem 16** (full residual transparency). *For the vector in <a href="#long68:eq:low-channel-basis" data-reference-type="eqref" data-reference="long68:eq:low-channel-basis">[long68:eq:low-channel-basis]</a>,
``` math
\mathcal R\!\left(tK_D+\sum_{n>D}z_nU_n\right)
 =tL_D(S-H_D)+\sum_{n>D}z_n.
```
The residual series converges for every finite vector supported away from index zero. A zero-moment vector has integral residual, and any two finite vectors with the same factorial moment have residuals differing by an integer.*

</div>

<div class="proof">

*Proof.* For $`d>D`$, the $`K_D`$ channel is $`L_D`$, while each $`U_n`$ contributes one to its isolated residual coordinate. Termwise decomposition therefore gives the factorial-gap tail $`L_D(S-H_D)`$ plus the finite coordinate mass $`\sum z_n`$. The factorial-gap tail is summable and the coordinate correction has finite support, which proves convergence. In the full divisor-basis coordinates the coefficient of the $`e_1`$ column equals the factorial moment; when that moment is zero only the integral coordinate mass remains. Subtracting two equal-moment identities proves the last assertion. ◻

</div>

The exact Lean endpoint packages are [primitive attainment of the moment-ideal generator](https://github.com/wcook04/plectis-erdos/blob/f20f727ae44d6dc3b24036bf63118b8fe591912e/ErdosProblems/Erdos68/PaperCompleteMomentIdeal.lean#L242) and [the equal-moment residual class](https://github.com/wcook04/plectis-erdos/blob/f20f727ae44d6dc3b24036bf63118b8fe591912e/ErdosProblems/Erdos68/PaperCompleteResidualIdentity.lean#L195). They determine the finite low-channel lattice and its residual class modulo $`\mathbb{Z}`$; they do not prove that the remaining real residual is nonzero along a cofinal family.

<span id="long68:res:lead-channel-radius" label="long68:res:lead-channel-radius"></span>

<div id="long68:res:channel-radius" class="theorem">

**Theorem 17** (square-subsequence radius bound). *Let $`t,M,R\in\mathbb{N}`$ satisfy
``` math
t\ge2^{32},\qquad M>0,\qquad L_{2t^2}\mid M,\qquad M<(R+1)!-1 .
```
Then $`3t^3<2(R+1)`$. Consequently no family satisfying these hypotheses for all sufficiently large $`t`$ has $`(R(t)+1)/t^3\le3/2`$ eventually, and none has $`R(t)=o(t^3)`$. The historical manuscript cites `Erdos68/PaperCompleteExisting.lean`, line 236. This module is absent from the retained source pin; this citation does not establish kernel verification at that pin.*

</div>

<div class="proof">

*Proof.* Put $`D=2t^2`$, $`k=2t`$ and $`u=D-k+1=2t^2-2t+1`$. Lemma <a href="#long68:res:segment" data-reference-type="ref" data-reference="long68:res:segment">6</a> at $`N=D`$, with $`n!-1\ge n!/2`$ and $`\log n!\ge n\log n-n`$, and with $`L_D\le M<(R+1)!`$, gives
``` math
\begin{equation}
\label{long68:eq:radius-log}
 2t\bigl(u\log u-u-\log2\bigr)
 <(R+1)\log(R+1)+\binom{2t+1}{3}\log(2t^2).
\end{equation}
```

Suppose $`R+1\le\tfrac32t^3`$. Since $`t\ge16`$ one has $`\tfrac{15}{8}t^2\le u\le2t^2`$ and $`\log u\ge2\log t`$, so the left side of <a href="#long68:eq:radius-log" data-reference-type="eqref" data-reference="long68:eq:radius-log">[long68:eq:radius-log]</a> is at least $`\tfrac{15}{2}t^3\log t-4t^3-2t\log2`$. Using $`\binom{2t+1}{3}<\tfrac43t^3`$ and $`\log\tfrac32<\log2`$, the right side is at most
``` math
\tfrac32t^3\bigl(\log2+3\log t\bigr)+\tfrac43t^3\bigl(\log2+2\log t\bigr).
```
Dividing by $`t^3`$ and rearranging, <a href="#long68:eq:radius-log" data-reference-type="eqref" data-reference="long68:eq:radius-log">[long68:eq:radius-log]</a> would require
``` math
\tfrac13\log t<4+\frac{2\log2}{t^2}+\tfrac{17}6\log2 .
```
But $`\log t\ge32\log2`$ and $`\tfrac23<\log2<1`$ give $`\tfrac13\log t-\tfrac{17}6\log2\ge\tfrac{47}6\log2>5`$, while $`4+2\log2/t^2<5`$. This contradiction proves the finite inequality, and the two sequence conclusions follow. ◻

</div>

The hypotheses concern one specified cancellation architecture. An application to $`S`$ must still produce the positive moment and the factorial-size bound from the series, and must show that the channels through $`2t^2`$ vanish for the resulting family. The theorem restricts that construction and supplies no irrationality argument.

Theorem <a href="#long68:res:lcm-growth" data-reference-type="ref" data-reference="long68:res:lcm-growth">7</a> raises the asymptotic constant in the same estimate.

<div id="long68:res:radius-constant" class="corollary">

**Corollary 18** (asymptotic radius constant). *Let $`M(t),R(t)`$ satisfy $`M(t)>0`$, $`L_{2t^2}\mid M(t)`$ and $`M(t)<(R(t)+1)!-1`$ for all sufficiently large $`t`$. Then
``` math
\liminf_{t\to\infty}\frac{R(t)+1}{t^3}\ \ge\ \frac{16}{9}.
```*

</div>

<div class="proof">

*Proof.* Put $`r=R(t)+1`$, so $`L_{2t^2}\le M(t)<r!`$ and $`\log L_{2t^2}<r\log r`$. Theorem <a href="#long68:res:lcm-growth" data-reference-type="ref" data-reference="long68:res:lcm-growth">7</a> at $`N=2t^2`$ gives, for every $`\varepsilon>0`$ and all large $`t`$,
``` math
\log L_{2t^2}
 \ \ge\ \Bigl(\tfrac{2\sqrt2}{3}-\varepsilon\Bigr)\,2\sqrt2\,t^3
   \bigl(2\log t+\log2\bigr)
 \ \ge\ \Bigl(\tfrac{16}{3}-\varepsilon'\Bigr)t^3\log t .
```
Suppose $`r\le ct^3`$ for arbitrarily large $`t`$, with $`c<16/9`$ fixed. On that subsequence $`r\log r\le ct^3(3\log t+\log c)=\bigl(3c+o(1)\bigr)t^3\log t`$, and $`3c<16/3`$ contradicts the lower bound for large $`t`$. ◻

</div>

This corollary is asymptotic, and it does not give the strict finite inequality $`R+1>\tfrac{16}9t^3`$ at every large $`t`$. The finite logarithmic constraint of the channel argument is compatible with equality $`9(R+1)=16t^3`$ for $`t\ge4`$, so that constraint alone cannot force a strict finite endpoint at $`16/9`$. The two statements are separate, and Corollary <a href="#long68:res:radius-constant" data-reference-type="ref" data-reference="long68:res:radius-constant">18</a> rests on the ordinary proof of Theorem <a href="#long68:res:lcm-growth" data-reference-type="ref" data-reference="long68:res:lcm-growth">7</a>; the finite-block Lean source does not carry the asymptotic deduction. Lean checks the corollary as [asymptotic radius constant liminf](https://github.com/wcook04/plectis-erdos/blob/0b500c7cf8e8bb7ae343484378df02f277fb8194/lean/ErdosProblems/Erdos68/PaperCompleteLiminf.lean#L54).

The congruence <a href="#long68:eq:channel-congruence" data-reference-type="eqref" data-reference="long68:eq:channel-congruence">[long68:eq:channel-congruence]</a> also explains the prime-channel corrector.

<div id="long68:res:translator" class="theorem">

**Theorem 19** (two-term prime channel corrector). *Let $`p\ge3`$ be prime and let $`c_{p-1}=p`$, $`c_p=-1`$, with every other coefficient zero. Then $`M(c)=0`$, $`V_{p}(c)=p!-1`$, and $`V_{d}(c)=0`$ for every $`d\ge2`$ with $`d\ne p`$.*

</div>

<div class="proof">

*Proof.* Since $`p\ge3`$, both indices $`p-1`$ and $`p`$ lie in the prescribed coefficient domain $`i\ge2`$. The moment is $`p\,(p-1)!-p!=0`$. For $`2\le d<p`$ the quotient identity $`\lfloor(p-1)/d\rfloor=\lfloor p/d\rfloor`$ holds, since $`d\nmid p`$, so the two channel weights carry the same power of $`d!`$ and the channel evaluates to $`p\,(p-1)!/(d!)^{\lfloor p/d\rfloor}-p!/(d!)^{\lfloor p/d\rfloor}=0`$. For $`d>p`$ both indices lie below $`d`$, so both weights are the plain factorials and the same cancellation occurs. At $`d=p`$ the weights are $`(p-1)!`$ and $`p!/p!=1`$, giving $`p\,(p-1)!-1=p!-1`$. ◻

</div>

For $`p=2`$, the same auxiliary identities would require $`c_1=2`$. They do not define an admissible corrector on the domain $`i\ge2`$, since every vector supported on that domain has $`c_1=0`$.

At zero cost in the moment this supplies a unit in the $`p`$-channel: adding an integer multiple of the corrector to any candidate kernel shifts the $`p`$-channel by multiples of $`p!-1`$ and leaves the moment and every other channel fixed. For every channel rank and every prescribed cutoff there is a factorial-grid kernel together with a remote prime-corrector pair entirely beyond that cutoff, with all requested low channels zero, nonzero moment, and residual in $`[-1/2,1/2]`$. What is missing is strict nonvanishing: nothing here rules out the rounded residual being exactly zero, and no cofinal family with a strictly nonzero rounded residual has been produced.

<a id="long68:sec:finite"></a>

# Finite denominator exclusions

<span id="long68:res:lead-denominator-exclusions" label="long68:res:lead-denominator-exclusions"></span>

Two finite computations constrain a hypothetical denominator $`q`$ in $`S=a/q`$, and they constrain different features of it:
``` math
\begin{equation}
\label{long68:eq:finite-bounds}
 q\nmid299999!,\qquad q\ge2^{39990}>10^{12038}.
\end{equation}
```
The size bound holds for every integer $`a`$ and positive natural $`q`$ with $`S=a/q`$; no reducedness assumption is needed. Its evidence is the exact continued-fraction computation described below. The stronger candidate [finite-size Lean certificate](https://github.com/wcook04/plectis-erdos/blob/27c2fc5fe3c55fe547feaeb4c9bb68b3cf63a5bf/lean/ErdosProblems/Erdos68/PaperCompleteFiniteSizeCertificate.lean#L58) is not cited as kernel verification: its source records that the computation has not yet been kernel checked. The factorial-grid exclusion $`q\nmid299999!`$ is supported separately by the external GMP computation; its full Lean certificate also remains an outstanding formal obligation.

Neither condition implies the other. A prime between $`299999`$ and $`599998`$ fails to divide $`299999!`$ but is smaller than $`2^{39990}`$, whereas $`299999!`$ satisfies the size lower bound but fails the nondivisibility condition. High powers of small primes further show why nondivisibility is not a smoothness exclusion.

The first exclusion comes from an exact interval carry census. An independently implemented GMP integer computation certifies all $`299998`$ carry cells for $`3\le m\le300000`$ with a scale of $`2^{5025679}`$ and $`96`$ guard bits, using no floating-point arithmetic; at every step the outward interval is proved to lie inside one half-open unit cell before the carry is recorded. Its unit carries occur exactly at
``` math
52,\ 591,\ 1030,\ 1407,\ 1438,\ 2164,\ 4258,\ 10991,\ 21236,
```
so $`b_{300000}\ne1`$. Theorem <a href="#long68:res:carry-equivalence" data-reference-type="ref" data-reference="long68:res:carry-equivalence">8</a> then gives $`q\nmid299999!`$ and in particular $`q\ge300000`$. The receipt is `verification/erdos68-strict-successor.json`, schema `erdos68_strict_successor_exact_interval_v1`, payload digest `044ef27a60f7294c39b8279b7f04e22e1234a942e2862e9e8c64eb66505af29b`, recording the parameters above, the digests of the driver and backend used on its own run, the event-trace digest and the final enclosure. The source packet names the driver `scripts/check_erdos68_strict_successor.py` and backend `scripts/check_erdos68_strict_successor_gmp.cpp`. This revision records a fresh full-range carry replay. The published driver digest is `f25b5bd8ffbfd66bdbb42ca6a07a936aab9b4eb7d3a57446725be55acb642191` and the backend digest is `43308ddc3902dd537b789ae6e0648054a0d752adf07e5d6e1d829811e9342083`; the payload digest is `044ef27a60f7294c39b8279b7f04e22e1234a942e2862e9e8c64eb66505af29b`. The event-trace and unit-carry certificate match the previously retained receipt. The inherited independent replay at $`m\le4000`$ reproduces the unit-carry prefix $`52,591,1030,1407,1438,2164`$ with a non-unit carry at the endpoint, which gives $`q\ge4000`$ on its own. The census is a separate computation from the Lean development, and the implication it feeds is the kernel-checked one.

The first exclusion can also be written $`\kappa(q)\ge300000`$, where $`\kappa(q)=\min\{r\ge1:q\mid r!\}`$ is the factorial index used by Sondow \[sondow2006, §3, Theorem 1\]. This is not a smoothness exclusion and uses no approximation bound for $`e`$.

The second exclusion has a short integer description. Put $`D=2^{80000}`$ and let $`N`$ be the first integer with $`N!-1>D`$. Define
``` math
\ell=\sum_{n=2}^{N-1}\left\lfloor\frac D{n!-1}\right\rfloor,
 \qquad
 u=\ell+(N-2)+\left\lfloor\frac{2D}{N!-1}\right\rfloor+1 .
```
Each rounded prefix term loses less than one, and $`(n+1)!-1>(n+1)(n!-1)`$ makes the tail from $`N`$ smaller than $`2/(N!-1)`$, so $`\ell/D<S<u/D`$.

There are exactly $`N-2`$ rounded prefix terms. The extra $`+1`$ in $`u`$ keeps the upper enclosure strict even if $`2D/(N!-1)`$ happens to be an integer; the positive omitted tail keeps the lower enclosure strict. Here $`N=7054`$ and $`u-\ell=7053`$. Apply the continued-fraction algorithm to both endpoints at once, retaining a quotient only while the integer parts agree and both remainders are nonzero, and reversing the endpoint order at each inversion. There are $`23449`$ common quotients, and the convergent denominators
``` math
Q_{-2}=1,\quad Q_{-1}=0,\quad Q_j=a_jQ_{j-1}+Q_{j-2}
```
satisfy $`Q_{23448}\ge2^{39990}`$. Every rational in the open enclosure shares this initial segment, so its reduced denominator is at least $`Q_{23448}`$. Indeed, write $`P_j`$ for the convergent numerators. Such a rational either equals $`P_{23448}/Q_{23448}`$ or has a complete quotient $`A/B>1`$ after the segment, with $`A`$ and $`B`$ coprime, and then equals $`(P_{23448}A+P_{23447}B)/(Q_{23448}A+Q_{23447}B)`$; the determinant identity $`P_jQ_{j-1}-P_{j-1}Q_j=\pm1`$ makes both fractions reduced \[nist-dlmf, §1.12(ii), (1.12.5)–(1.12.7), (1.12.20)–(1.12.21)\]. The argument is about a common prefix and does not require the last convergent to lie inside the enclosure. The integer comparison $`2^{39990}>10^{12038}`$ closes <a href="#long68:eq:finite-bounds" data-reference-type="eqref" data-reference="long68:eq:finite-bounds">[long68:eq:finite-bounds]</a>. The [integer replay](https://github.com/wcook04/plectis-erdos/blob/cd3bd6fe245867a435e15d503ccedd699c5d02e2/scripts/check_erdos68_continued_fraction.py) and its [receipt](https://github.com/wcook04/plectis-erdos/blob/cd3bd6fe245867a435e15d503ccedd699c5d02e2/verification/erdos68-continued-fraction.json) record scale $`80000`$ bits, bracket width $`7053`$, $`23449`$ certified partial quotients, power-of-two exponent $`39990`$ and strict decimal exponent $`12038`$.

Both certificates are finite. A refinement of either enlarges the excluded range and returns a statement of the same shape, and neither excludes an eventual unit-carry tail. The continued-fraction identities are classical \[nist-dlmf, §1.12(ii)\]; the enclosure, the prefix length and the exponent are outputs of the computation above.

<a id="long68:sec:open"></a>

# The remaining arithmetic inputs

The exact target is <a href="#long68:eq:strict-misses" data-reference-type="eqref" data-reference="long68:eq:strict-misses">[long68:eq:strict-misses]</a>, equivalently <a href="#long68:eq:lower-escape" data-reference-type="eqref" data-reference="long68:eq:lower-escape">[long68:eq:lower-escape]</a>.

All sufficient conditions below are to be proved for the actual factorial sequence. A model obeying selected congruences, or a successful bounded computation, is not a substitute for that requirement. The routes below are sufficient conditions for it, and their quantitative hypotheses are unproved. None of them is an equivalent reformulation of the problem.

<a id="a-recent-framework-and-a-missing-hypothesis."></a>

#### A recent framework, and a missing hypothesis.

Garaev, Luca and Shparlinski’s harmonic-sum estimate \[garaev-luca-shparlinski-harmonic, Theorem 1 and (5)\] concerns unconditioned harmonic sums, not the fibre on which $`n!\equiv1\pmod q`$. The value-set literature addresses different invariants. Banks, Luca, Shparlinski and Stichtenoth \[banks-et-al2005\] provide historical missing-value context; Klurman and Munsch \[klurman-munsch2017, Theorems 2.1–2.2\] distinguish unconditional averages from GRH-dependent improvements. Grebennikov, Sagdeev, Semchankau and Vasilevskii \[grebennikov-et-al2024, Corollaries 1.2 and 1.4\] study sizes of value and quotient sets, as do the factorial-residue and representation results of Hu \[hu2026\] and Garaev and Pardo \[garaev-pardo2026\]. None is a noncancellation theorem for the reciprocal unit weights here. A large value set alone does not upper-bound a prescribed fibre. Hu’s September preprint \[hu-september2026, Theorem 3.1\] gives $`|A|\gg\min\{M,p\}^{8/15}\mu^{-4/15}`$ for distinct reciprocal-affine maps with at least $`M`$ internal transitions, at most $`|A|`$ parameters, and nonidentity quotient multiplicity at most $`\mu`$. Its incidence input is Stevens and de Zeeuw \[stevens-dezeeuw2017, Theorem 4\]. A proposed transfer to a factorial-conditioned harmonic fibre must first construct such internal transitions and bound their multiplicity; neither is supplied by an unconditioned value-set estimate.

<a id="weighted-collisions-and-complementary-residues."></a>

#### Weighted collisions and complementary residues.

On the tailored moving-factor blocks, the local half of <a href="#long68:eq:factor-split" data-reference-type="eqref" data-reference="long68:eq:factor-split">[long68:eq:factor-split]</a> is
``` math
\begin{equation}
\label{long68:eq:weighted-target}
 \log\widetilde C_p
 <\log\left(\frac{2p^2}{2p+1}\cdot
       \frac{\prod_{j=p}^{2p-1}j}{q}\right),
\end{equation}
```
and the global half is <a href="#long68:eq:global-scale" data-reference-type="eqref" data-reference="long68:eq:global-scale">[long68:eq:global-scale]</a>. Both must hold on the same cofinal family.

The order of quantifiers is part of the proposed result: for every bound, one parameter must satisfy both inequalities. Two unrelated infinite subsequences would not prove the combined criterion. For a prime $`r`$ absent from the base $`F_p`$, the contribution to $`v_r(\widetilde C_p)`$ counts the levels $`e\ge1`$ at which at least two gaps in $`I_p`$ are divisible by $`r^e`$; for a prime dividing $`F_p`$ the base valuation must first be removed, so the layer count is $`v_r(\widetilde C_p)=\#\{e\ge1:h_{r,\,e+v_r(F_p)}(p)>1\}`$ with $`h_{r,e}(p)=\#\{i\in I_p:r^e\mid i!-1\}`$. A spacing bound $`h_{r,e}(p)(e+1)\le2p+e-2`$ is available. An unweighted count of collisions does not establish <a href="#long68:eq:weighted-target" data-reference-type="eqref" data-reference="long68:eq:weighted-target">[long68:eq:weighted-target]</a>, and reflected hits may not be discarded, since Wilson reflection produces genuine collision primes. Theorem 12 of Garaev, Luca and Shparlinski \[garaev-luca-shparlinski, arXiv v1, Thm. 12, p. 16\] is a multiplicity bound and supplies no lower bound for the complementary residue in <a href="#long68:eq:global-scale" data-reference-type="eqref" data-reference="long68:eq:global-scale">[long68:eq:global-scale]</a>.

<a id="two-narrower-exploratory-reductions."></a>

#### Two narrower exploratory reductions.

For $`F_h(X)=\prod_{j=1}^h(X+j)`$, joint factorial–harmonic hits a distance $`h`$ apart require $`F_h(x)=1`$ and $`F'_h(x)=0`$. An exact calculation gives
``` math
\gcd(F_{12}-1,F'_{12})
 =(X-4626)(X-7848)\quad\hbox{in }\mathbb F_{12487}[X].
```
Thus the earlier small-prime observation of at most one critical root is not a uniform theorem. These two roots have factorial values $`442`$ and $`6300`$, not $`1`$, so the unconditioned critical-root count is genuinely a relaxation of the desired fibre count. The derivation, compressed even-gap polynomial and exact replay are in the accompanying research note.

There is also a useful distinction for the gap products in Stewart’s method \[stewart2004, Lemma 2, (21)–(24)\]. Products from adjacent gaps $`i<j<k`$ are unequal: equality $`j!/i!=k!/j!`$ would make $`k!/i!`$ a square, contrary to the classical non-power theorem \[erdos-selfridge1975, Theorem 1\]. Selecting two short gaps with nearly equal lengths does not preserve adjacency. The wider equal-product problem has a separate history \[macleod-barrodale1970\]; the doubled-length theorem discussed by Nguyen Xuan Tho \[nguyen-tho2026, Theorem 1\] is another special case, not arbitrary near-equal-length nonvanishing. No stronger lcm exponent is inferred from these local observations.

<a id="repeated-support-valuation-amplification."></a>

#### Repeated-support valuation amplification.

Write $`\Delta_n=u_n/v_n`$ in lowest terms, let $`B_n`$ be the part of $`n!-1`$ supported on primes occurring in an earlier gap, and put
``` math
A_n=\prod_{\substack{r\mid B_n\\ v_r(v_n)<v_r(n!-1)}}r^{\,v_r(n!-1)} .
```
What is established is $`A_n\mid v_{n+1}`$ and, when $`A_n>1`$, $`u_{n+1}\not\equiv0\pmod{A_n}`$. A sufficient quantitative goal, at cofinally many genuinely nonterminal indices $`n`$, is the following with $`m=n+1`$ and $`d=A_n`$:
``` math
\begin{equation}
\label{long68:eq:amplification-target}
 \bigl((m+2)m!-2\bigr)v_m
 \le m^2(m!-1)\,(u_m\bmod d).
\end{equation}
```
It implies the upper alternative of <a href="#long68:eq:finite-escape" data-reference-type="eqref" data-reference="long68:eq:finite-escape">[long68:eq:finite-escape]</a>. A nonzero least representative can equal one while the modulus is enormous, so divisibility and logarithmic mass do not by themselves bound that representative. A lower bound for $`\log A_n`$, and an infinitude of square lifts, are separate possible inputs, and each needs a further implication to reach <a href="#long68:eq:amplification-target" data-reference-type="eqref" data-reference="long68:eq:amplification-target">[long68:eq:amplification-target]</a>.

<a id="lower-interval-escape."></a>

#### Lower-interval escape.

Prove <a href="#long68:eq:finite-escape" data-reference-type="eqref" data-reference="long68:eq:finite-escape">[long68:eq:finite-escape]</a> at arbitrarily large indices; restricting to primes is sufficient. The upper alternative is exactly $`\bigl((m+2)m!-2\bigr)v_m\le m^2(m!-1)u_m`$. Replacing $`u_m`$ by its least nonnegative residue modulo a specified divisor of $`v_m`$ gives a stronger sufficient test. Congruence recurrences alone do not count: synthetic models satisfy the available congruences while remaining in the unit-carry branch, and a zero canonical digit is a different event from membership in this Archimedean interval.

<a id="doubled-prime-branch-failure."></a>

#### Doubled-prime branch failure.

For an odd prime $`p`$, the carry range and $`Z_{2p}=2pZ_{2p-1}+1-b_{2p}`$ give
``` math
\begin{equation}
\label{long68:eq:doubled-prime}
 p^2\mid Z_{2p}
 \quad\Longleftrightarrow\quad
 \begin{cases}
 b_{2p}=1\ \hbox{and}\ p\mid Z_{2p-1},\ \hbox{or}\\
 b_{2p}=1+p\ \hbox{and}\ p\mid2Z_{2p-1}-1 .
 \end{cases}
\end{equation}
```

Reduction modulo $`p`$ forces $`b_{2p}\equiv1\pmod p`$, and the two displayed values are the only possibilities in $`[-1,2p-1]`$; division by $`p`$ gives the predecessor conditions. For rational $`S=a/q`$ and $`p>q`$ the tail estimate gives $`Z_{2p}=(2p)!\,S`$, which is divisible by $`p^2`$. Ruling out both branches for infinitely many $`p`$ therefore proves irrationality. The two conditions must be coupled; controlling only the predecessor residue or only the carry does not meet the hypotheses.

The two branches are disjunctive alternatives for divisibility. To force its failure one must rule out both at each chosen prime, not rule out one branch on each of two different subsequences.

<a id="a-remote-cramer-residual."></a>

#### A remote Cramer residual.

Put $`s_n=((n+2)!)^2`$ and $`i_j=(t+j)s_n`$ for $`0\le j\le n+1`$. Form the integer matrix $`A`$ with moment row $`(i_j!)_j`$ and channel rows $`(W_{d,i_j})_j`$ for $`2\le d\le n+2`$, let $`c`$ be the cofactor vector of the moment row, and let $`N_d`$ be the determinant obtained by replacing that row with $`(W_{d,i_j})_j`$. Cofactor expansion gives $`M(c)=\det A`$, $`V_{d}(c)=N_d`$, and $`V_{d}(c)=0`$ for $`2\le d\le n+2`$. By <a href="#long68:eq:channel-congruence" data-reference-type="eqref" data-reference="long68:eq:channel-congruence">[long68:eq:channel-congruence]</a> each $`(V_{d}(c)-M(c))/(d!-1)`$ is an integer and vanishes for $`d>\max_ji_j`$, so
``` math
\mathcal R_{n,t}:=\sum_{d>n+2}\frac{N_d}{d!-1}
 =\det(A)\,S+K_{n,t},\qquad K_{n,t}\in\mathbb{Z}.
```
Seek a family with $`\min_ji_j=t\,s_n\to\infty`$ and $`\mathcal R_{n,t}\notin\mathbb{Z}`$. Such a family proves irrationality: for a fixed denominator $`q`$, every entry of the moment row is divisible by $`q`$ once the support is sufficiently remote, so $`q\mid\det A`$. Unbounded pairs $`(n,t)`$ do not supply that remoteness, because $`t=0`$ anchors the least support index at zero. The eventual identity $`N_d=\det A`$ controls the tail and gives no control over the finite intermediate block, which changes sign; any gcd-of-minors certificate must specify a positive gcd, its rank hypotheses, and its connection to the displayed residual.

<a id="criteria-from-the-literature-that-do-not-apply."></a>

#### Criteria from the literature that do not apply.

Duverney’s Theorem 3.1 assumes the quadratic growth condition (1.3), $`cu_n^2\le u_{n+1}\le c'u_n^2`$, whereas $`u_{n+1}/u_n^2\to0`$ for $`u_n=n!-1`$; the summability condition (3.6) of his Corollary 3.2, $`\sum_n|u_{n+1}/u_n^2-1|<\infty`$, also fails, since its summands tend to one here \[duverney, pp. 275, 285–287\]. For a single denominator sequence the rapid-growth criterion goes back to Erdős \[erdos1975, Theorem 1, p. 1\]; Barreto, Kang, Kim, Kovač and Zhang treat products of consecutive denominators and weighted extensions \[barreto-et-al, Thms. 2–3 and Rem. 4\]. For $`a_n=n!-1`$, $`\log(n!-1)=O(n\log n)`$ makes $`(n!-1)^{1/\psi^n}\to1`$ for every fixed $`\psi>1`$, so neither Erdős’s hypothesis $`\limsup_na_n^{1/2^n}=\infty`$ nor the growth hypotheses of their Theorems 2 and 3 hold. These criteria do not decide $`S`$; the useful content is the target these papers identify: a low-height clearing subsequence, or enough exact cancellation in the least common multiple. Theorem <a href="#long68:res:lcm-growth" data-reference-type="ref" data-reference="long68:res:lcm-growth">7</a> bounds that cancellation from one side and Theorem <a href="#long68:res:prime-pole" data-reference-type="ref" data-reference="long68:res:prime-pole">2</a> describes it from the other.

No irrationality conclusion is obtained here. The finite conclusion is that every rational representation $`S=a/q`$, $`q>0`$, must satisfy both $`q\nmid299999!`$ and $`q\ge2^{39990}>10^{12038}`$. The remaining task is a cofinal estimate, not a larger finite census.

<a id="sources-and-evidence"></a>

# Sources and evidence

The formal counterparts below are checked by the Lean 4 kernel against Mathlib at source snapshot `92b88dc1bbe0`, with no `sorry`, added axioms, or unchecked evaluation. Theorem <a href="#long68:res:lcm-growth" data-reference-type="ref" data-reference="long68:res:lcm-growth">7</a> and Corollary <a href="#long68:res:radius-constant" data-reference-type="ref" data-reference="long68:res:radius-constant">18</a> are ordinary proofs given in full above, and Lean checks them as [common denominator growth liminf](https://github.com/wcook04/plectis-erdos/blob/0b500c7cf8e8bb7ae343484378df02f277fb8194/lean/ErdosProblems/Erdos68/PaperCompleteLiminf.lean#L42) and [asymptotic radius constant liminf](https://github.com/wcook04/plectis-erdos/blob/0b500c7cf8e8bb7ae343484378df02f277fb8194/lean/ErdosProblems/Erdos68/PaperCompleteLiminf.lean#L54). The finite-block inequality is the separate Lean source [finite terminal-block inequality](https://github.com/wcook04/plectis-erdos/blob/d788dd4b8c59f2246000f2ed98fffb8a5e8ac72e/lean/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L524-L529). The two prefix cancellations, the index-$`52`$ example and the continued-fraction enclosure are finite integer calculations with the procedures displayed above. The carry census through $`300000`$ is a separate exact-interval computation with the receipt named in §<a href="#long68:sec:finite" data-reference-type="ref" data-reference="long68:sec:finite">6</a>.

<div class="center">

| Statement | Formal counterpart |
|:---|:---|
| Theorem <a href="#long68:res:prime-pole" data-reference-type="ref" data-reference="long68:res:prime-pole">2</a> | [maximal-power survival](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimePoleCriterion.lean#L223), with the residue formula at [line 129](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimePoleCriterion.lean#L129) and the denominator form at [line 41](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimePoleDenominator.lean#L41) |
| Proposition <a href="#long68:res:wilson-cofinality" data-reference-type="ref" data-reference="long68:res:wilson-cofinality">3</a> | [cofinal private hits](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3097); reflection at [line 3139](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3139) |
| Theorem <a href="#long68:res:carry-equivalence" data-reference-type="ref" data-reference="long68:res:carry-equivalence">8</a> | [strict-successor misses](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L986); denominator exclusions at [line 812](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L812) and [line 836](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L836) |
| Proposition <a href="#long68:res:companion-orbit" data-reference-type="ref" data-reference="long68:res:companion-orbit">9</a> | [companion orbit](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/CompanionOrbitRationality.lean#L438) |
| Proposition <a href="#long68:res:lower-escape" data-reference-type="ref" data-reference="long68:res:lower-escape">10</a> | [lower-interval normal form](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ShrinkingTargetNormalForm.lean#L82); finite window at [line 122](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ShrinkingTargetNormalForm.lean#L122), cofinal consumer at [line 145](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ShrinkingTargetNormalForm.lean#L145), classification <a href="#long68:eq:escape-classification" data-reference-type="eqref" data-reference="long68:eq:escape-classification">[long68:eq:escape-classification]</a> at [line 39](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ShrinkingTargetNormalForm.lean#L39), radius at [line 158](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ShrinkingTargetNormalForm.lean#L158) |
| Theorem <a href="#long68:res:shift-family" data-reference-type="ref" data-reference="long68:res:shift-family">11</a> | [family boundary](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialShiftFamilyOrbit.lean#L139); escape form at [line 156](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialShiftFamilyOrbit.lean#L156), member $`t=-1`$ at [line 175](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialShiftFamilyOrbit.lean#L175), and the irrationality of $`e`$ at [line 211](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialShiftFamilyOrbit.lean#L211) |
| Theorem <a href="#long68:res:global-residue" data-reference-type="ref" data-reference="long68:res:global-residue">12</a> | [global complementary residue](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L6164); coprimality <a href="#long68:eq:gap-normalisation" data-reference-type="eqref" data-reference="long68:eq:gap-normalisation">[long68:eq:gap-normalisation]</a> at [line 4209](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L4209) |
| Equation <a href="#long68:eq:factor-split" data-reference-type="eqref" data-reference="long68:eq:factor-split">[long68:eq:factor-split]</a> | [unit-factor scale split](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L4766), floor identity at [line 4701](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L4701), consumer at [line 1574](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L1574) |
| Fixed-owner absorption | [absorbed owner](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L2677) |
| Theorem <a href="#long68:res:normalform" data-reference-type="ref" data-reference="long68:res:normalform">13</a> and <a href="#long68:eq:channel-congruence" data-reference-type="eqref" data-reference="long68:eq:channel-congruence">[long68:eq:channel-congruence]</a> | [integral channel weight](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L25), [exact cancellation](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L43) |
| Theorem <a href="#long68:res:channel-radius" data-reference-type="ref" data-reference="long68:res:channel-radius">17</a> | [detail note 1](#paper-table-note-898b615af01876ee) |
| Prime channel corrector | [remote reduction](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeUnitTranslator.lean#L1657), residual identity at [line 1559](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeUnitTranslator.lean#L1559) |
| Equation <a href="#long68:eq:doubled-prime" data-reference-type="eqref" data-reference="long68:eq:doubled-prime">[long68:eq:doubled-prime]</a> | [doubled-prime criterion](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean#L257) |
| Canonical factorial digits | [termination equivalence](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/CanonicalFactorialTermination.lean#L78) |
| Amplification modulus | [divisibility](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L5557), nonvanishing at [line 5572](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L5572) |

<a id="paper-table-note-898b615af01876ee"></a> **Detail note 1.** [finite radius bound](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1084); sequence form at [line 1103](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1103), little-$`o`$ form at [line 905](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L905), method ceiling ordinary in this record (`sharp_radius_satisfies_square_log_constraint` is not in this checkout)


</div>

Attribution. Wilson’s theorem and the Wilson reflection identity are classical, the latter recorded by Stewart \[stewart2004, p. 462, (4)\]. The factorial-digit termination criterion goes back to Cantor \[cantor1869\]; Koepf and Schmersau prove its irrationality direction for digits that are not eventually maximal \[koepf-schmersau, Example 3.2, p. 121\], and Galambos treats rationality criteria for Cantor series \[galambos1976, Ch. II, §2.1\]. The additions here are the telescope $`C=S-e+2`$, the identification of the digit value $`m-2`$, and the transport to the shifted family. The tail-integrality step is the argument of Hančl and Tijdeman \[hancl-tijdeman, Lemma 2.1 and the following remark, p. 385\]. The multiplicity bound is Garaev, Luca and Shparlinski’s \[garaev-luca-shparlinski\], and the lcm deduction from it is not theirs. The divisibility in Lemma <a href="#long68:res:gap-gcd" data-reference-type="ref" data-reference="long68:res:gap-gcd">5</a> is the case $`P=-1`$ of the relation used in the proof of Lemma 5 of Luca and Shparlinski \[luca-shparlinski\] and at display (2.5) of Lai \[lai\]. The nonvanishing cutoff for polynomial shifts is Lemma 3 of \[luca-shparlinski\], restated with the bound $`n!+P(n)>1`$ in \[lai, Lemma 2.1\]. The survival criterion is a specialisation of Louwsma and Martino’s valuation formula \[louwsma-martino, Lemma 4.1, p. 10\]. The single-denominator growth criterion is Erdős’s \[erdos1975, Theorem 1, p. 1\], and the continued-fraction identities are those of \[nist-dlmf, §1.12(ii)\]. No antecedent was located for the Wilson cofinality packaging, the finite radius bound or Theorem <a href="#long68:res:lcm-growth" data-reference-type="ref" data-reference="long68:res:lcm-growth">7</a>.

<a id="long68:app:sources"></a>

# Guide to the formal sources

The public `ErdosProblems.Erdos68` package carries the checked source for this note. The declarations below are the dependency chain behind the statements above, together with the subsidiary results developed alongside them; they are pinned to the formal-source commit named at the start of this note.

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L47)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L81)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L124)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L153)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L162)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L196)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L269)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/CanonicalFactorialTermination.lean#L38)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/CanonicalFactorialTermination.lean#L54)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L82)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L945)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialZeroPlateauCertificates.lean#L136)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L6099)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3047)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3231)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3252)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L1419)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L1524)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/AdjacentUnitCarryWindow.lean#L148)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/AdjacentUnitCarryWindow.lean#L215)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/AdjacentUnitCarryWindow.lean#L243)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/AdjacentUnitCarryWindow.lean#L337)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean#L71)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean#L91)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean#L101)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean#L130)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L868)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L885)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L65)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L156)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialAnalyticBoundary.lean#L52)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialAnalyticBoundary.lean#L84)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/FactorialAnalyticBoundary.lean#L131)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L556)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L586)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L698)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L739)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L800)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L2707)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3327)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3394)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3443)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3472)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3602)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3790)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3848)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3982)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L4387)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L4854)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5213)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5277)

- [](https://github.com/wcook04/plectis-erdos/blob/92b88dc1bbe099aa73bcc900c3c405e9ba5c2334/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5389)

<a id="long68:sec:extended-record"></a>

# Extended record

The short note above carries the advertised results with complete proofs. This part keeps the surrounding mathematics: the digit kernel the carry and orbit criteria run on, the exact interfaces of the collision-core reduction, the finite certificates, the superseded deductions, and the routes that were tried and closed.

<a id="long68:sec:ext-digits"></a>

## The canonical factorial digit kernel

Write $`\theta_0=\{x\}`$ and, for $`m\ge1`$,
``` math
a_m=\lfloor m\,\theta_{m-1}\rfloor,\qquad \theta_m=m\,\theta_{m-1}-a_m ,
```
so that $`\theta_m=\{m!\,x\}`$ for $`m\ge1`$. The kernel checks the floor formula, the digit bounds $`0\le a_m<m`$, the recurrence $`\theta_{m+1}=(m+1)\theta_m-a_{m+1}`$, the finite telescoping expansion
``` math
x=\lfloor x\rfloor+\sum_{m=2}^{N}\frac{a_m}{m!}+\frac{\theta_N}{N!},
```
and the rule that a zero remainder at one index forces every later digit to vanish. The rational direction is also checked: if $`q>0`$ and $`q\le n`$, then $`\operatorname{facFloor}(a/q,n)=((n!/q):\mathbb{Z})\,a`$ and the canonical digit at radix $`n+1`$ vanishes, so every rational input has an eventually zero expansion. The converse holds for every real input, and gives Cantor’s termination criterion \[cantor1869\]
``` math
x\in\mathbb{Q}\quad\Longleftrightarrow\quad a_m(x)=0\ \hbox{for all large }m .
```
If all digits after index $`N\ge1`$ vanish, the recurrence gives $`\theta_{N+k}\ge(k+1)\theta_N`$; since every remainder is below one, $`\theta_N=0`$ and $`x=\lfloor N!x\rfloor/N!`$.

A zero canonical digit is a different event from a zero-branch hit. The reported interval data contain canonical zero digits at $`m=5`$ and $`m=23`$, while the zero-branch list is empty through $`m=100000`$.

A second exact reformulation runs through a defect automaton. For a rational centre recurrence $`F_m=mF_{m-1}+1+\varepsilon_m-C_m`$, the kernel checks that the integer ceiling defect code equals $`\lfloor m\delta_{m-1}-\varepsilon_m\rfloor`$ and that $`\delta_m=m\delta_{m-1}-\varepsilon_m-q_m`$, with the specialisation $`\varepsilon_m=1/(m!-1)`$ written out. What is checked is the algebra of the automaton; proving that the finite-sum residual centre satisfies the premise is a separate step and is not done.

<a id="long68:sec:ext-literature"></a>

## Criteria from the literature, in full

Koepf and Schmersau prove that eventual equality between the floors of $`n`$ times a partial sum and $`n`$ times its limit forces irrationality \[koepf-schmersau, Thm. 1.1, p. 117\]; their rational-term version obtains that equality from the integrality condition $`np_ns_n\in\mathbb N_0`$ and the strict tail bound $`a-s_n<1/(np_n)`$ \[koepf-schmersau, (2.1) and (2.3), p. 118; Thms. 2.2–2.3, pp. 119–120\]. For the choice they record after (2.1), the least common multiple of the reduced summand denominators, here $`p_n=\operatorname{lcm}\{k!-1:2\le k\le n\}`$, the last two denominators already obstruct the tail bound:
``` math
p_n\ \ge\ \frac{(n!-1)\bigl((n-1)!-1\bigr)}{n-1},
```
because $`\gcd(n!-1,(n-1)!-1)=\gcd((n-1)!-1,n-1)\le n-1`$. For $`n\ge4`$ the first omitted summand $`1/((n+1)!-1)`$ then already exceeds $`1/(np_n)`$, so this $`p_n`$ cannot satisfy their tail hypothesis. Cancellation in the reduced prefix denominator could give a smaller scale, and proving enough cancellation is another form of the present denominator problem.

Duverney’s Theorem 3.1 assumes the quadratic growth condition (1.3), $`cu_n^2\le u_{n+1}\le c'u_n^2`$, while $`u_{n+1}/u_n^2\to0`$ for $`u_n=n!-1`$ \[duverney, (1.3), p. 275; Thm. 3.1, pp. 285–286\]; his Corollary 3.2, which allows signs $`a_n\in\{-1,1\}`$, requires the summability condition (3.6), $`\sum_n|u_{n+1}/u_n^2-1|<\infty`$, whereas those summands tend to one \[duverney, Cor. 3.2, p. 287\]. Both the ratio limit and the nonsummability are kernel-checked. The ratio proof divides numerator and denominator by $`(n!)^2`$; the resulting terms tend to zero while $`(1-1/n!)^2`$ tends to one.

For a single denominator sequence, Erdős proved that $`\sum_k1/n_k`$ is irrational when $`\limsup_kn_k^{1/2^k}=\infty`$ and $`n_k>k^{1+\varepsilon}`$ eventually \[erdos1975, Theorem 1, p. 1\]. Barreto, Kang, Kim, Kovač and Zhang treat products of consecutive denominators and weighted extensions \[barreto-et-al, Thms. 2–3 and Rem. 4, pp. 2–5\]. For $`a_n=n!-1`$ the root-growth expressions tend to one, $`(n!-1)^{1/2^n}\to1`$, so neither the limsup hypothesis of Erdős nor the growth hypotheses of their Theorems 2 and 3 hold; the limit is kernel-checked through the bound $`0\le\log(n!-1)\le n^2`$. Their proof of Theorem 3 uses the classical criterion, which they trace to Fourier’s proof that $`e`$ is irrational, that a rational sum of nonnegative rationals with infinitely many positive terms admits no prefix-clearing integers $`D_N`$ with $`\liminf_ND_Nr_N=0`$, where $`r_N`$ is the tail after $`N`$ terms \[barreto-et-al, Lem. 8, p. 6\]; their Proposition 12 produces such integers under the hypotheses of that theorem \[barreto-et-al, pp. 9–12\]. The ordinary product of the factorial-gap denominators is far too large for that estimate, so a transfer needs a low-height clearing subsequence, or enough exact cancellation in their least common multiple.

Dividing the strict-successor recurrence $`Z_m=mZ_{m-1}+1-b_m`$ by $`m!`$ and telescoping gives the exact finite identity
``` math
\frac{Z_M}{M!}=\frac{Z_2}{2!}+\sum_{m=3}^{M}\frac{1-b_m}{m!},
```
so the carry defects $`1-b_m`$ are genuine factorial-series coefficients. Hančl and Tijdeman classify the rational sums with polynomial coefficients \[hancl-tijdeman, Thm. 3.1 and Cor. 3.1, pp. 390–391\]; their denominator is the cumulative linear product $`\prod_{n\le N}(an+b)`$, and the individual number $`N!-1`$ does not occur. The criterion of Oppenheim that they reproduce \[hancl-tijdeman, Lem. 2.2, p. 385\] states that, for coefficients $`c_n`$ with $`|c_n|<an+b`$ eventually and $`\liminf_n|c_n|/n=0`$, the sum is rational exactly when $`c_n=0`$ eventually. For the carry defects $`c_m=1-b_m`$ the first condition holds, since $`-1\le b_m\le m-1`$, and the second is not established; the needed cofinal equivalence is Theorem <a href="#long68:res:carry-equivalence" data-reference-type="ref" data-reference="long68:res:carry-equivalence">8</a>, which is proved directly.

<a id="long68:sec:ext-superseded"></a>

## A superseded deduction

Before the elementary segment argument of the short note, the record derived a weaker exponent from an external multiplicity theorem. Put $`Q_N=\prod_{2\le n\le N}(n!-1)`$. For an odd prime $`r`$, let $`m_r`$ count the indices $`2\le n\le N`$ with $`r\mid n!-1`$; such an index satisfies $`n<r`$. The factorial-congruence multiplicity estimate of Garaev, Luca and Shparlinski \[garaev-luca-shparlinski, arXiv v1, Thm. 12, p. 16\], applied to the residue $`a=1`$ on $`1\le n\le\min(N,r-1)`$, gives $`m_r\ll N^{2/3}`$; the prime $`2`$ divides none of these factors. Writing $`E_r=\max_{2\le n\le N}v_r(n!-1)`$,
``` math
\log Q_N=\sum_r\sum_{n=2}^{N}v_r(n!-1)\log r
 \le\bigl(\max_r m_r\bigr)\sum_rE_r\log r
 \ll N^{2/3}\log L_N ,
```
and Stirling summation gives $`\log Q_N\asymp N^2\log N`$, whence $`\log L_N\gg N^{4/3}\log N`$. Theorem <a href="#long68:res:lcm-growth" data-reference-type="ref" data-reference="long68:res:lcm-growth">7</a> supersedes this: its exponent is $`3/2`$, its constant is explicit, and it uses no external theorem. The deduction is retained because it is the only place a multiplicity bound enters the record.

The primitive lcm divisibility survives cofactor removal: factorial valuations do not remove the channel obstruction once every common cofactor divisor has been removed. A corank-one cofactor and determinant construction for such primitive kernels has not been formalised, and the divisibility theorem does not establish it.

<a id="long68:sec:ext-plateau"></a>

## Plateaux, first exit, and the finite denominator ladder

A second argument works on the rational grid in place of the channels. Let $`H`$ be a partial sum and $`q`$ a candidate denominator. Writing $`qH=k+r`$ and $`q(S-H)=u`$, the next $`q^{-1}`$ grid point $`(k+1)/q`$ lies below $`S`$ exactly when $`1\le r+u`$. The factorial plateau theorem states that if $`H<G\le S`$, if $`n!G`$ is integral, and if $`n!(S-H)<1`$, then the strict successor of $`n!H`$ and the canonical floor of $`n!S`$ are the same grid integer. Two rigidity statements follow: consecutive plateau floors, scaled by the next radix, force the canonical digit to vanish; and any first-exit offset $`\delta\in[0,2)`$ with carry $`b=-\lfloor\delta\rfloor`$ has $`b\in\{0,-1\}`$, so the exit has exactly two alternatives.

The first-crossing argument continues to a denominator bound. For a rational grid level $`G`$ with first crossing $`\tau`$ by the literal partial sums, write $`G-H_{\tau-1}=a/v`$ with $`a,v>0`$. Then $`v\ge\tau!-1`$, and on the $`-1`$ exit branch $`v\ge\tau!(\tau!-1)`$. No coprimality hypothesis on $`a`$ and $`v`$ is needed.

There is also a direct obstruction at prime indices. With $`\Delta_m`$ as in the short note, the kernel checks for $`m\ge3`$ the criterion
``` math
m\mid Z_m
 \quad\Longleftrightarrow\quad
 1+\frac1{m!-1}<m\Delta_m\le2+\frac1{m!-1},
```
and if $`S=a/q`$ with $`q>0`$, then $`p\mid Z_p`$ for every prime $`p>q`$, so one exact missed prime $`p`$ gives $`q\ge p`$. Exact kernel reduction gives $`11\nmid Z_{11}`$, hence $`q\ge11`$; exact rational normalisation gives $`60\nmid Z_{60}`$, $`64\nmid Z_{64}`$ and $`67\nmid Z_{67}`$, and the prime index $`67`$ gives the checked bound
``` math
S=\frac aq,\ q>0\quad\Longrightarrow\quad q\ge67 .
```
The exact-interval census of the short note replaces $`67`$ by $`300000`$.

There is a finite peeling identity. For $`x\ne0,1`$ and $`K\ge0`$,
``` math
\frac1{x-1}=\sum_{j=1}^{K}\frac1{x^j}+\frac1{x^K(x-1)} .
```
When $`x=k!`$ and a chosen factorial scale is divisible by $`(k!)^K`$, the scaled finite sum is integral and only the last term retains the factor $`k!-1`$ in its denominator. The identity isolates one residual fraction before exact bounding, and it supplies no cofinal family of nonzero residuals.

One proposed strengthening is false and is recorded as false: the divisibility $`(m!-1)\mid\operatorname{den}(V_m)`$ fails at the reported strict events $`m=52`$ and $`m=591`$. Only the Archimedean first-crossing lower bound survives.

There is a second, more arithmetic mechanism at doubled prime indices, stated as <a href="#long68:eq:doubled-prime" data-reference-type="eqref" data-reference="long68:eq:doubled-prime">[long68:eq:doubled-prime]</a> in the short note. The formal theorem is not restricted to hand-reduced indices; it is the general unique-slot prime-power criterion specialised to the literal prefixes.

<a id="long68:sec:ext-collision"></a>

## The collision-core interfaces

Beyond the definitions used in the short note, the record keeps the exact interfaces of the collision-core reduction.

Write $`D(S)=\operatorname{lcm}_{i<j,\ i,j\in S}\gcd(d_i,d_j)`$, with $`D(S)=1`$ for an empty or singleton family. For each prime $`r`$, its valuation is the second-largest valuation among the $`d_i`$, counting missing values as zero; the denominator lcm has the largest valuation. This proves $`D(S)\operatorname{lcm}_{i\in S}d_i\mid\prod_{i\in S}d_i`$ prime by prime.

The collision core has an exact incremental law. For the positive factorial-gap denominators, adjoining a new index $`a\notin S`$ gives
``` math
D(S\cup\{a\})=\operatorname{lcm}\!\Bigl(D(S),\ \gcd\bigl(d_a,\operatorname{lcm}_{j\in S}d_j\bigr)\Bigr),
```
since finite-family gcd and lcm distributivity collapses the lcm of all pairwise gcds against $`d_a`$ to a single gcd. The same formula holds after adjoining the distinguished base, so each step needs only the old denominator lcm and the old core, with no pairwise rescan.

There is an exact product and lcm bound. If $`\widetilde C(S)`$ is the core after cancelling a positive distinguished base, $`L(S)=\operatorname{lcm}_{j\in S}d_j`$ and $`P(S)=\prod_{j\in S}d_j`$, then $`\widetilde C(S)L(S)\mid P(S)`$, hence $`\widetilde C(S)\le P(S)/L(S)`$. For the factorial block this specialises to
``` math
\widetilde C_p\le\frac{\prod_{n\in I_p}(n!-1)}{\operatorname{lcm}_{n\in I_p}(n!-1)},
```
an exact bridge from lower estimates for the factorial-gap lcm to upper estimates for the normalised core. It does not close the local scale bound.

The base cancellation is exact prime by prime. With $`F_p=(p-1)!`$, $`D_p=D(I_p)`$ and $`C_p=\operatorname{lcm}(F_p,D_p)`$, as in the main record,
``` math
\widetilde C_p=\frac{C_p}{F_p}=\frac{D_p}{\gcd(F_p,D_p)},\qquad
 v_r(\widetilde C_p)=\max\{0,v_r(D_p)-v_r(F_p)\} .
```
For $`e>0`$, $`r^e\mid\widetilde C_p`$ exactly when the pairwise core carries $`r^{e+v_r(F_p)}`$, which in the block forces two distinct gaps to be divisible by that higher power, by the second-largest-valuation formula. If $`i<j`$ are two such hits and $`f=v_r(F_p)`$, then $`r^{e+f}\mid j!/i!-1`$. Since $`r\mid j!-1`$ forces $`j<r`$, $`0<j!/i!-1<r^{j-i}`$, hence $`e+f<j-i`$. The sharp surviving valuation cap $`v_r(\widetilde C_p)+v_r(F_p)<r`$ then gives $`p-1<r(r-1)<r^2`$ for every support prime, and $`\widetilde C_p`$ is coprime to $`k!`$ whenever $`k(k-1)\le p-1`$. This removes every factorial channel below the moving square-root cutoff, and it does not bound the aggregate product of the remaining large prime powers.

For collision estimates that already provide an upper-half hit, no exponent is lost to normalisation: if $`r`$ divides a displayed gap at some $`n\ge p`$, then $`r\nmid F_p`$ and $`r^e\mid\widetilde C_p\iff r^e\mid C_p`$ for every $`e>0`$. This has an exact incidence-count form,
``` math
r^e\mid\widetilde C_p
 \quad\Longleftrightarrow\quad
 1<\#\{i\in I_p:r^e\mid i!-1\},
```
so a source estimate giving at most one $`r^e`$-hit deletes that exponent and yields $`v_r(\widetilde C_p)<e`$. The local aggregation is exact:
``` math
v_r(\widetilde C_p)=\#\bigl\{e\in[1,r-1]:1<\#\{i\in I_p:r^e\mid i!-1\}\bigr\},
```
and for an endpoint prime with $`2p-1<r`$ the range truncates to $`e\in[1,2p-4]`$. The same equivalence holds under the exact condition $`r\nmid F_p`$ in place of the endpoint inequality, which covers the entire moving prime range at and above the block parameter; at $`e=2`$ it gives a conditional squarefree conclusion $`v_r(\widetilde C_p)\le1`$.

The local load has a distance-sensitive witness. If $`r`$ is prime, $`e>0`$ and $`r^e\mid\widetilde C_p`$, there are $`i<j`$ in $`I_p`$ with $`r^{e+v_r(F_p)}\mid i!-1`$, $`r^{e+v_r(F_p)}\mid j!-1`$ and $`r^{e+v_r(F_p)}\le j^{\,j-i}`$; consequently $`(2p-1)^d<r^{e+v_r(F_p)}`$ forces $`d<j-i`$. The spacing hypothesis is discharged internally: any two $`r^e`$-hits $`i<j`$ satisfy $`e<j-i`$, because $`r\mid j!-1`$ already forces $`j<r`$ and the gap-power inequality converts that size relation into strict separation. The pairwise form is stronger than the selected-witness form: for arbitrary $`r,e`$ and any displayed hits $`i<j`$,
``` math
r^e\mid i!-1,\quad r^e\mid j!-1
 \quad\Longrightarrow\quad r^e\le j^{\,j-i},
```
so every prime-power hit layer is an $`e`$-separated subset of the block and
``` math
(e+1)\,\#\{i\in I_p:r^e\mid i!-1\}\ \le\ 2p+e-2 .
```
The unweighted packing step is therefore complete. Globally,
``` math
r\mid\widetilde C_p
 \quad\Longrightarrow\quad
 v_r(\widetilde C_p)+v_r(F_p)<2p-3
```
for every prime $`r`$ and $`p\ge2`$, so even primes already present in the normalisation base pay for their base valuation inside the same block-diameter budget. What remains is to bound the layer counts uniformly as $`r`$ and $`p`$ move, multiply the surviving contributions, and still close the complementary-residue coordinate.

The squarefreeness premise is not proved. An exhaustive modular scan through $`r\le2{,}000{,}000`$ and $`n\le240`$ found four individual square hits and no prime with two such hits. All $`498{,}501`$ pairs $`2\le a<b\le1000`$ have squarefree $`\gcd(a!-1,b!-1)`$, and the aggregate squarefree-collision scan through $`p=499`$ stays below $`0.374`$ of the upper-descending-factorial logarithmic scale. These are finite exact computations. They carry neither theorem authority nor an asymptotic incidence bound.

A finite variant of the cofinal private supply compares the product of a chosen set of primes, each at least $`5`$, with $`\prod_{2\le k\le B}(k!-1)`$; if the prime product is larger, at least one chosen prime has no hit through $`B`$, while Wilson still bounds its least hit by $`q-2`$. Wilson reflection limits what a linear-size divisor can be assumed to be: if $`n`$ is odd, $`n<q`$, and $`q\mid n!-1`$, then $`q\mid(q-n-1)!-1`$, and when both indices lie in one block with the reflected hit earlier, equivalently $`q<2n+1`$, the repeated hit survives predecessor-factorial normalisation and its full-block incidence count exceeds one.

Stewart states that for every $`\varepsilon>0`$ there are infinitely many odd $`n`$ whose least prime factor $`q`$ of $`n!-1`$ satisfies
``` math
n<q<\left(\frac{\sqrt{145}-1}{8}+\varepsilon\right)n ,
```
estimate (9) of Theorem 1 being stated for $`n!+1`$ \[stewart2004, p. 463\] and transferred to $`n!-1`$ in the text \[stewart2004, p. 464\]. The source controls $`q`$ relative to the later index $`n`$ and supplies no control relative to the private first-hit index, so it is collision-core input. The missing private-anchor and global product estimates are elsewhere.

One selected prime $`q`$ already furnishes the coprime factor pair $`(1,q)`$: its projection moduli are $`R_p`$ and $`R_p/q`$, whose least common multiple is $`R_p`$, so no second selected prime is needed and there is no hidden equality-or-disagreement branch in that specialisation. The underlying projection rigidity is general: if the endpoint numerator $`Z`$ is congruent to a weighted numerator $`T`$ modulo $`R`$, then every divisor $`Q`$ of $`R`$ with $`Z\le B<Q`$ satisfies $`T\bmod Q=Z`$, so two divisors above $`B`$ with unequal projected residues exclude that bounded endpoint, and unequal projections force $`\min(Q_1,Q_2)\le T`$.

<a id="long68:sec:ext-certificates"></a>

## Finite channel and carry certificates

The finite-support vector $`\lambda=2e_3-e_4`$ has, by kernel check, $`V_{2}(\lambda)=0`$, factorial moment $`-12`$, $`V_{3}(\lambda)=-2`$, $`V_{4}(\lambda)=11`$, and $`V_{d}(\lambda)=-12`$ for every $`d\ge5`$. Under the exact rational tail enclosure $`1/119<\Theta_4<1/50`$ its residual lies strictly between $`-93/575`$ and $`-309/13685`$, so it is nonzero and subunit.

In the enlarged coefficient space of §<a href="#long68:sec:channels" data-reference-type="ref" data-reference="long68:sec:channels">5</a>, exact integer computation verifies the vectors $`K_D`$ for every $`2\le D\le12`$: channels $`2`$ through $`D`$ vanish, the factorial moment is $`L_D`$, and the coefficient content is one. They lie outside the space of vectors supported on $`n\ge2`$, since $`L_D`$ is odd and every such vector has even moment. At $`D=9`$,
``` math
L_9=31540008254514077395,\qquad a_9=[e_1]K_9=-3902884074990939115 .
```
Since $`U_{11}=T_{11}`$ has $`u_{11}=0`$, the vector $`K_9-9553024718754\,U_{11}`$ keeps the coordinate $`a_9`$ and has content one. By Theorem <a href="#long68:res:residual-transparency" data-reference-type="ref" data-reference="long68:res:residual-transparency">16</a> its residual is $`L_9(S-H_9)-9553024718754`$, and exact rational arithmetic with the tail bound $`\sum_{n\ge36}1/(n!-1)<2/(36!-1)`$ places it strictly between $`1353/100000`$ and $`1354/100000`$. A different example is supported on $`n\ge2`$: the vector $`c=(-40,55,-10,1)`$ on the support $`(3,4,5,6)`$ annihilates channels $`2`$ and $`3`$, has moment $`600`$, and satisfies
``` math
0.09925341997208298<\mathcal R(c)<0.09925341997208300 ,
```
which excludes denominators dividing $`600`$.

There are two different computations at the same endpoint. A separate interval computation reports the stronger geometric statement that no zero-branch event occurs at any $`m\le100000`$; its executable and source digest are not available, so that classification remains external finite evidence. The strict-successor census through $`300000`$ used in the short note is a fresh exact GMP replay in this revision; §<a href="#long68:sec:finite" data-reference-type="ref" data-reference="long68:sec:finite">6</a> records the published driver, backend and payload digests and describes the separate replay through $`4000`$. The full range is external computational evidence outside the Lean development.

<a id="long68:sec:ext-nogo"></a>

## Limits of fixed-coordinate arguments

- Residue vectors, their recurrences, and window widths admit synthetic all-hit blocks, so they cannot prove irrationality on their own.

- Known pointwise prime congruences, prime-dilation congruences, parity, and the exact prime coefficient formula admit a synthetic rational countermodel.

- Wilson quotients, harmonic sums, $`p`$-adic gamma identities, and factorial residues do not control the required Archimedean floor without an additional coupling theorem. Every prime-window test factors into a sharp Archimedean strict-ceiling condition and a modular divisibility condition, and the missing ingredient is the coupling between them.

- For the genus-zero product $`E(z)=\prod_{n\ge2}(1-z/n!)`$, local uniform convergence and logarithmic differentiation give $`-E'(1)/E(1)=S`$. The natural termwise clearing factor $`Q_N=\prod_{2\le n\le N}(n!-1)`$ satisfies $`Q_N(S-H_N)\to\infty`$, so this clearing choice yields no small positive integer linear form. The calculation concerns this clearing factor alone; Hermite–Padé systems with other denominators are left open.

- Zero-moment variations cannot create an additional fractional cancellation coordinate, and factorial valuations cannot absorb the channel lcm obstruction.

- A fixed pair of low-index private owners cannot make the projection argument cofinal, by the absorption statement of the short note.

<a id="long68:sec:ext-generic"></a>

## The generic shape behind the lower-interval form

The cofinal statement in the short note is a case of the following immediate consequence of Cantor’s termination criterion. For a real $`x`$ and any positive sequence $`c_m`$ with $`c_m<1/m`$ eventually,
``` math
x\notin\mathbb{Q}
 \quad\Longleftrightarrow\quad
 \{(m-1)!\,x\}\ge c_m\ \hbox{for arbitrarily large }m .
```
For rational $`x`$ the fractional parts vanish eventually; if all large fractional parts lie below $`c_m`$, multiplying by $`m`$ stays below one, so the next canonical digit is zero, and eventual zero digits force rationality. The specific target $`c_m=E_m/m`$ is useful because it translates into finite predecessor-gap conditions. The smallness of the target alone establishes no metric, measure or equidistribution theorem for this orbit, and none is claimed.

<a id="sec:erdos-68-complete-family-map"></a>

# How the result families fit together

<a id="carries."></a>

#### Carries.

Tail integrality gives the necessary eventual unit carry under rationality. Telescoping gives the converse. These are exact equivalences; the finite census supplies only bounded instances of escape.

<a id="channels."></a>

#### Channels.

Integral triangular elimination solves the selected channel equations. Removing the auxiliary coordinate yields a moment ideal. The finite horizon computes that ideal at fixed depth, while the residual identity explains why zero-moment corrections do not create a new fractional degree of freedom.

<a id="common-and-reduced-denominators."></a>

#### Common and reduced denominators.

Pairwise subtraction and a terminal block give the lcm lower bound. Reciprocal-unit sums determine survival of a maximal prime-power layer after reduction. These are complementary statements about different integers.

<a id="conditional-routes."></a>

#### Conditional routes.

A remote residual must lie strictly between consecutive integers, or a collision-core estimate must be paired with a sufficiently large complementary gap. These are additional quantitative inputs, not consequences of divisibility alone.

<a id="finite-evidence."></a>

#### Finite evidence.

Carry and continued-fraction certificates exclude two incomparable sets of rational denominators. Their numerical parameters, source lineage and replay status are separately recorded. A larger certificate would not remove the need for a cofinal argument.

<div class="thebibliography">

99

Paul Erdős. [On the irrationality of certain series: problems and results](https://doi.org/10.1017/CBO9780511897184.009). In Alan Baker (ed.), *New Advances in Transcendence Theory*, Cambridge University Press (1988), pp. 102–109.

Thomas F. Bloom. [Erdős Problem \#68](https://www.erdosproblems.com/68). Online resource (2026). Historical access: 28 July 2026; present-page status not reverified.

Paul Erdős. [Some problems and results on the irrationality of the sum of infinite series](https://www.renyi.hu/~p_erdos/1976-44.pdf). *Journal of Mathematical Sciences* **10** (1975), 1–7.

Joel Louwsma and Joseph Martino. [Rational numbers with odd greedy expansion of fixed length](https://arxiv.org/abs/2309.07280v1). Preprint (2023). arXiv:2309.07280.

Georg Cantor. Über die einfachen Zahlensysteme. *Zeitschrift für Mathematik und Physik* **14** (1869), 121–128.

János Galambos. [Representations of Real Numbers by Infinite Series](https://doi.org/10.1007/BFb0081642). Lecture Notes in Mathematics 502, Springer (1976).

Moubariz Z. Garaev, Florian Luca and Igor E. Shparlinski. [Character sums and congruences with $`n!`$](https://doi.org/10.1090/S0002-9947-04-03612-8). *Transactions of the American Mathematical Society* **356** (12) (2004), 5089–5102. arXiv:math/0403422.

Cameron L. Stewart. [On the greatest and least prime factors of $`n!+1`$, II](https://doi.org/10.5486/PMD.2004.3190). *Publicationes Mathematicae Debrecen* **65** (3–4) (2004), 461–480.

Wolfram Koepf and Dieter Schmersau. [Irrationality of certain infinite series II](https://doi.org/10.1524/anly.2011.1094). *Analysis* **31** (2011), 117–124.

Daniel Duverney. [Irrationality of fast converging series of rational numbers](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf). *Journal of Mathematical Sciences, the University of Tokyo* **8** (2001), 275–316.

Jaroslav Hančl and Robert Tijdeman. [On the irrationality of factorial series](https://doi.org/10.4064/aa118-4-5). *Acta Arithmetica* **118** (4) (2005), 383–401.

Kevin Barreto, Jiwon Kang, Sang-hyun Kim, Vjekoslav Kovač and Shengtong Zhang. [Irrationality of rapidly converging series: a problem of Erdős and Graham](https://arxiv.org/abs/2601.21442v3). Preprint (2026). arXiv:2601.21442.

Florian Luca and Igor E. Shparlinski. [Prime divisors of shifted factorials](https://doi.org/10.1112/S0024609305004923). *Bulletin of the London Mathematical Society* **37** (6) (2005), 809–817.

Li Lai. [On the largest prime divisor of $`n!+1`$](https://doi.org/10.1017/S0004972725100543). *Bulletin of the Australian Mathematical Society* **113** (3) (2026), 390–403. arXiv:2103.14894.

Li Lai, Cezar Lupu and Johannes Sprang. [On the irrationality of certain $`p`$-adic zeta values](https://doi.org/10.1007/s40687-025-00559-x). *Research in the Mathematical Sciences* **12** (4) (2025), article 77. arXiv:2505.23088.

Li Lai. [On the irrationality of certain $`2`$-adic zeta values](https://doi.org/10.1142/S1793042125500113). *International Journal of Number Theory* **21** (1) (2025), 207–235. arXiv:2304.00816.

NIST Digital Library of Mathematical Functions. [Continued fractions: convergents](https://dlmf.nist.gov/1.12). Online resource (2026).

Paul Erdős and Cameron L. Stewart. [On the greatest and least prime factors of $`n!+1`$](https://doi.org/10.1112/jlms/s2-13.3.513). *Journal of the London Mathematical Society* **13** (3) (1976), 513–519.

Florian Luca and Igor E. Shparlinski. [On the largest prime factor of $`n!+2^n-1`$](https://doi.org/10.5802/jtnb.524). *Journal de Théorie des Nombres de Bordeaux* **17** (3) (2005), 859–870.

Moubariz Z. Garaev, Florian Luca and Igor E. Shparlinski. [Distribution of harmonic sums and Bernoulli polynomials modulo a prime](https://doi.org/10.1007/s00209-006-0939-5). *Mathematische Zeitschrift* **253** (2006), 855–865.

Jonathan Sondow. [A geometric proof that $`e`$ is irrational and a new measure of its irrationality](https://arxiv.org/abs/0704.1282v2). *American Mathematical Monthly* **113** (7) (2006), 637–641. arXiv:0704.1282. Addendum: *Amer. Math. Monthly* **114** (2007), 659; reading copy v2.

Xiyu Hu. [Factorial residues modulo a prime: beyond the square-root bound](https://arxiv.org/abs/2608.01781v1). Preprint (2026). arXiv:2608.01781. Version 1, 3 August 2026.

Moubariz Z. Garaev and Julio C. Pardo. [Additive congruences with factorials modulo a prime](https://doi.org/10.1090/proc/17753). *Proceedings of the American Mathematical Society* **154** (10) (2026), 4179–4190. arXiv:2508.12127. Published online 1 July 2026; assigned October 2026 issue.

Xiyu Hu. [Lower bounds for some value sets over finite fields: incidence geometry and Bourgain’s group expansion theorem](https://arxiv.org/abs/2609.05652v1). Preprint (2026). arXiv:2609.05652. Version 1, 4 September 2026.

William D. Banks, Florian Luca, Igor E. Shparlinski and Henning Stichtenoth. [On the Value Set of $`n!`$ Modulo a Prime](https://journals.tubitak.gov.tr/math/vol29/iss2/6/). *Turkish Journal of Mathematics* **29** (2) (2005), 169–174.

Oleksiy Klurman and Marc Munsch. [Distribution of factorials modulo $`p`$](https://doi.org/10.5802/jtnb.974). *Journal de Théorie des Nombres de Bordeaux* **29** (1) (2017), 169–177.

Alexandr Grebennikov, Arsenii Sagdeev, Aliaksei Semchankau and Aliaksei Vasilevskii. [On the sequence $`n!`$ mod $`p`$](https://doi.org/10.4171/RMI/1422). *Revista Matemática Iberoamericana* **40** (2) (2024), 637–648.

Sophie Stevens and Frank de Zeeuw. [An improved point-line incidence bound over arbitrary fields](https://doi.org/10.1112/blms.12077). *Bulletin of the London Mathematical Society* **49** (5) (2017), 842–858. arXiv:1609.06284.

R. A. Macleod and I. Barrodale. [On Equal Products of Consecutive Integers](https://doi.org/10.4153/CMB-1970-052-8). *Canadian Mathematical Bulletin* **13** (2) (1970), 255–259.

Nguyen Xuan Tho. [On equal products of consecutive integers](https://doi.org/10.4171/EM/556). *Elemente der Mathematik* **81** (3) (2026), 119–124. First published online 10 July 2025.

Paul Erdős and John L. Selfridge. [The product of consecutive integers is never a power](https://doi.org/10.1215/ijm/1256050816). *Illinois Journal of Mathematics* **19** (2) (1975), 292–301.

</div>
