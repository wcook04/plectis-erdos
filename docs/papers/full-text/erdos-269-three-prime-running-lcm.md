<a id="erdos-269-three-prime-running-lcm"></a>

# Distinct running least common multiples

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We give a five-map proof that the reciprocals of the distinct running least common multiples of the $`5`$-smooth integers have an irrational sum. The spacing of powers of $`5`$ separates the affine tail images; rationality would then force periodicity, contrary to the frequency of powers of $`3`$. For the sum counted with multiplicity, the tails instead give an integer recurrence and an equivalent residue criterion for irrationality. Proving that criterion for the actual coefficients remains open here.

<a id="sec:problem"></a>

# Two sums from running least common multiples

Let $`P`$ be a finite set of primes and $`\mathcal S_P`$ the positive integers with prime factors in $`P`$, including $`1`$. For $`P=\{2,3,5\}`$, the running least common multiples of these $`5`$-smooth integers begin $`1,2,6,12,60,60,120,360,360,\ldots`$. Put
``` math
\operatorname{L}(x)=\operatorname{lcm}\{u\in\mathcal S_P:u\le x\},\qquad
 \operatorname{H}_P(x)=\prod_{p\in P}p^{\lfloor\log_p x\rfloor}\quad(x\ge1).
```
Every member of the prefix divides $`\operatorname{H}_P(x)`$, while the prefix contains the largest power of each $`p\in P`$ at most $`x`$. Thus $`\operatorname{L}(x)=\operatorname{H}_P(x)`$, with a jump by $`p`$ exactly at each positive power of $`p`$. Counting distinct running LCMs or retaining multiplicities gives
``` math
\mathcal D_P=1+\sum_{\substack{t=p^n\\p\in P,\ n\ge1}}\frac1{\operatorname{H}_P(t)},
 \qquad
 \mathcal R_P=\sum_{u\in\mathcal S_P}\frac1{\operatorname{L}(u)}.
```
For $`P=\{2,3,5\}`$, $`\operatorname{L}(5)=\operatorname{L}(6)=60`$ contributes $`1/60`$ to $`\mathcal D_P`$ and $`2/60`$ to $`\mathcal R_P`$. Erdős Problem #269 asks about $`\mathcal R_P`$ \[erdosgraham1980, p. 65\] and \[erdos1988, p. 106\]. Positive powers of distinct primes never coincide; geometric growth of successive running LCMs gives convergence of $`\mathcal D_P`$. We use $`\mathbb{N}=\{0,1,2,\ldots\}`$.

<div id="r4-five-map-theorem">

</div>

<div id="res:distinct-height-235" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean#L689">Lean</a></p>

**Theorem 1** (the sum over distinct running LCMs for $`\{2,3,5\}`$). *The number $`\mathcal D_{\{2,3,5\}}`$ is irrational.*

</div>

Rationality would leave only finitely many normalised tails, but finiteness alone does not force the jumps to repeat. The decisive step is to recover the next block and the following tail from the current tail. Powers of $`2`$ delimit the blocks; the spacing of powers of $`5`$ separates their five affine images. Equal tails then have identical futures, contradicting the irrational frequency of powers of $`3`$.

Erdős asserted irrationality of $`\mathcal D_P`$ for every finite $`P`$ with $`|P|\ge2`$ in a letter dated 1 January 1973, without printing a proof \[erdos1974letter, p. 335\]. Thus the theorem above is a special case of that earlier assertion. We claim no priority for its conclusion. The [companion’s general argument](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-distinct-proof) uses an isolated interchange of jumps on a torus. That argument is retained there as an ordinary proof awaiting formalisation. The proof below is independent of that argument.

Our arguments leave the repeated sum $`\mathcal R_P`$ unresolved for finite $`P`$ with $`|P|\ge3`$. For $`P=\{p\}`$ both sums equal $`p/(p-1)`$.

After the five-map proof in Section <a href="#sec:distinct-235" data-reference-type="ref" data-reference="sec:distinct-235">[sec:distinct-235]</a>, we retain the multiplicities. The bases remain the same, but the block coefficients and tails grow quadratically. Sections <a href="#sec:lcm" data-reference-type="ref" data-reference="sec:lcm">3</a> and <a href="#sec:escape" data-reference-type="ref" data-reference="sec:escape">4</a> replace finite-state repetition by a test for excluding integer tails. For two primes, Fan’s factorisation \[fan2026comment\] reduces both sums to a Hecke–Mahler value and yields transcendence (Section <a href="#sec:two-prime" data-reference-type="ref" data-reference="sec:two-prime">5</a>). The appendices supply the running LCM identities and show why exact finite separation of the three-prime kernel cannot extend that factorisation.

<a id="sec:distinct"></a>

# Recovering the prime-power jumps

<span id="sec:distinct-235" label="sec:distinct-235"></span> Long division combines a finite set of remainders with a deterministic rule for the next digit and remainder. Here the bases vary with the prime-power jumps, so that rule must be proved. We first obtain finitely many tails under rationality, then recover the jumps from each tail.

<div class="proof">

*Proof of Theorem <a href="#res:distinct-height-235" data-reference-type="ref" data-reference="res:distinct-height-235">1</a>.* *Finitely many tails under rationality.* Write $`\operatorname{H}=\operatorname{H}_{\{2,3,5\}}`$ in this proof and put $`P_a=\operatorname{H}(2^a)`$. Every running LCM at or before $`2^a`$ divides $`P_a`$. We therefore normalise the tail after $`2^a`$ by
``` math
\begin{equation}
\label{eq:five-tail}
 Y_a=P_a\sum_{\substack{t>2^a\\t=2^n,3^n\text{ or }5^n,\ n\ge1}}
                   \frac1{\operatorname{H}(t)}.
\end{equation}
```
Each subsequent jump multiplies the running LCM by at least $`2`$, and a jump by $`3`$ eventually occurs. Comparison with $`\sum_{j\ge1}2^{-j}`$ gives $`0<Y_a<1`$.

Suppose that $`\mathcal D_{\{2,3,5\}}=N/K`$, where $`N`$ is an integer and $`K\ge1`$ is an integer. Clearing the finite prefix gives
``` math
KY_a=P_aN-K\left(P_a+
        \sum_{\substack{t\le2^a\\t=2^n,3^n\text{ or }5^n,\ n\ge1}}
                 \frac{P_a}{\operatorname{H}(t)}\right)\in\mathbb Z.
```
Thus the $`Y_a`$ lie in the finite set $`(K^{-1}\mathbb Z)\cap(0,1)`$. It remains to show why equality of two tails propagates.

*Recovering a block from its tail.* Consider the jumps between $`16`$ and $`32`$, including the last endpoint. They occur at $`25,27,32`$, multiplying the running LCM successively by $`5,3,2`$. After normalisation at $`16`$, their contribution is $`1/5+1/15+1/30`$. The remaining tail is normalised at a running LCM $`30`$ times as large, so
``` math
Y_4=\frac15+\frac1{15}+\frac1{30}+\frac{Y_5}{30}
     =\frac{9+Y_5}{30}.
```
In the block $`(64,128]`$, the interior jumps occur in the opposite order, at $`81,125`$. Its constant term is $`1/3+1/15+1/30=13/30`$. The multiplier $`30`$ records which primes occur, but not their order. The numerators $`9`$ and $`13`$ retain that order. To read it from a tail, we must also control the unknown following tail.

Every block $`(2^a,2^{a+1}]`$ contains its terminal power of $`2`$, at most one power of $`3`$ and at most one power of $`5`$. We record the interior jumps in their order by a word $`\tau_a`$ on the letters $`3,5`$, omitting the terminal $`2`$. Splitting off the block gives
``` math
\begin{equation}
\label{eq:five-maps}
 Y_a=G_{\tau_a}(Y_{a+1}),\qquad
 G_\tau(y)=\frac{\mu_\tau+y}{b_\tau},\qquad
 \begin{array}{c|ccccc}
 \tau&\varnothing&3&5&35&53\\\hline
 b_\tau&2&6&10&30&30\\
 \mu_\tau&1&3&3&13&9
 \end{array}
\end{equation}
```
Here $`b_\tau`$ is the factor by which the running LCM increases across the block, and $`\mu_\tau/b_\tau`$ is the block’s normalised contribution.

The bound $`0<Y_{a+1}<1`$ does not yet recover $`\tau_a`$: $`G_{53}([0,1])=[3/10,1/3]`$ and $`G_5([0,1])=[3/10,2/5]`$ overlap. The table improves the lower bound to $`Y_a\ge3/10`$. To separate these two images, an upper bound $`U`$ must satisfy
``` math
G_{53}(U)<G_5(3/10),\qquad
 \frac{9+U}{30}<\frac{33}{100},\qquad U<\frac9{10}.
```
The spacing of powers of $`5`$ supplies such a bound. A power $`5^f`$ belongs to block $`\lfloor f\log_2 5\rfloor`$. These indices start at $`2`$ and their successive differences are $`2`$ or $`3`$. Every three consecutive blocks therefore contain a power of $`5`$. Given $`a`$, let $`j\in\{a,a+1,a+2\}`$ be the first such block. The maps for blocks containing $`5`$ give $`Y_j\le7/15`$, since $`Y_{j+1}<1`$ and $`G_{35}(1)=7/15`$ bounds $`G_5(1)`$ and $`G_{53}(1)`$ as well. We now work *backwards* from $`j`$ to $`a`$. Each intervening block has map $`G_\varnothing`$ or $`G_3`$, and $`G_3(y)\le G_\varnothing(y)=(1+y)/2`$ for $`y\ge0`$. At most two backward steps give the successive bounds $`7/15`$, $`11/15`$, $`13/15`$. Hence
``` math
\begin{equation}
\label{eq:five-interval}
 Y_a\in I=\left[\frac3{10},\frac{13}{15}\right],\qquad
 G_\varnothing\bigl(G_\varnothing(7/15)\bigr)=\frac{13}{15}<\frac9{10}.
\end{equation}
```
This bound holds for the tails of the prime-power sequence because every three consecutive blocks contain a power of $`5`$. The interval $`I`$ is not invariant under arbitrary compositions of the five maps: for example, $`G_\varnothing(13/15)=14/15`$ lies outside $`I`$.

Figure <a href="#fig:five-map-images" data-reference-type="ref" data-reference="fig:five-map-images">1</a> gives the exact images of $`I`$. They are pairwise disjoint, with successive gaps $`1/900,17/300,79/900,1/180`$. Writing $`L=3/10`$ and $`U=13/15`$, the two narrow gaps are
``` math
G_5(L)-G_{53}(U)=\frac{3L-U}{30}=\frac1{900},\qquad
 G_\varnothing(L)-G_3(U)=\frac{3L-U}{6}=\frac1{180}.
```
Thus the same inequality $`U<3L=9/10`$ separates both pairs.

<figure id="fig:five-map-images" data-latex-placement="!htbp">

<figcaption>The five images of the arithmetic tail interval <span class="math inline"><em>I</em> = [3/10, 13/15]</span>. Their separation determines the next block from an actual tail. The full image <span class="math inline"><em>G</em><sub>⌀</sub>(<em>I</em>)</span> extends beyond <span class="math inline"><em>I</em></span>; the figure does not assert invariance under arbitrary words. Only the adjacent endpoints are shown in the two lower enlargements.</figcaption>
</figure>

Each actual $`Y_a`$ lies in exactly one image interval, identifying $`\tau_a`$ and then $`Y_{a+1}=b_{\tau_a}Y_a-\mu_{\tau_a}`$. For instance, $`Y_a\in[31/100,74/225]`$ forces $`\tau_a=53`$ and $`Y_{a+1}=30Y_a-9`$. This is the next arithmetic tail, not an arbitrary inverse image; it lies in $`I`$, so recovery can be repeated.

*Repetition would give a rational frequency.* The finitely many tail values obtained above include a repeated value $`Y_u=Y_v`$ with $`u<v`$. Since the image intervals are disjoint, this forces $`\tau_u=\tau_v`$. Applying the corresponding inverse map gives $`Y_{u+1}=Y_{v+1}`$. Induction yields $`\tau_{u+j}=\tau_{v+j}`$ for every $`j\ge0`$. Thus the entire later block word has period $`v-u`$.

To exclude this possibility, let $`\alpha=\log2/\log3`$. The number of powers of $`3`$ in block $`a`$ is $`\lfloor(a+1)\alpha\rfloor-\lfloor a\alpha\rfloor`$, and is determined by $`\tau_a`$. If the block word has eventual period $`\ell\ge1`$, let $`c`$ be the number of $`3`$-powers in one period. For every sufficiently large fixed $`a`$ and every $`n\ge1`$ we then have
``` math
\lfloor(a+n\ell)\alpha\rfloor=\lfloor a\alpha\rfloor+nc.
```
Dividing by $`n`$ and taking the limit gives $`\ell\alpha=c`$, contrary to unique factorisation, since it would imply $`2^\ell=3^c`$. ◻

</div>

<a id="sec:lcm"></a>

# The repeated three-prime sum

<span id="sec:shell" label="sec:shell"></span><span id="sec:actual-orbit" label="sec:actual-orbit"></span> We now retain every smooth integer, not just the jumps of its running LCM. Put $`P=\{2,3,5\}`$, $`S=\mathcal R_P`$ and $`\operatorname{H}=\operatorname{H}_P`$ throughout this section. The denominator changes at the same prime powers; the number of terms at each denominator is what changes the argument.

For example, $`[16,32)`$ contains the seven smooth integers $`16,18,20,24,25,27,30`$. Grouping them by their running LCM gives
``` math
\begin{array}{c|c|c}
 \text{smooth integers}&\text{running LCM}&\text{contribution}\\\hline
 16,18,20,24&720&4/720\\
 25&3600&1/3600\\
 27,30&10800&2/10800
 \end{array}
```
The distinct sum counts each displayed running LCM once; the repeated sum assigns the coefficients $`4,1,2`$. The jumps alone therefore no longer determine the block contribution. Appendix <a href="#sec:height-identities" data-reference-type="ref" data-reference="sec:height-identities">6</a> gives the general finite grouping identity.

With blocks $`[2^a,2^{a+1})`$, the tail now includes $`2^a`$. The prefix excludes the jump by $`2`$ there, so half the running LCM clears it. Put
``` math
s_a=\sum_{\substack{x\in\mathcal S_P\\2^a\le x<2^{a+1}}}\frac1{\operatorname{H}(x)},
 \qquad T_a=\sum_{j\ge0}s_{a+j},\qquad
 h_a=\frac{\operatorname{H}(2^a)}2,\qquad X_a=h_aT_a.
```
For $`a\ge1`$, each prefix LCM has exponent of $`2`$ at most $`a-1`$ and divides the integer $`h_a`$; at $`a=0`$, $`h_0=1/2`$. The factor $`1/2`$ reflects the endpoint change from Section <a href="#sec:distinct-235" data-reference-type="ref" data-reference="sec:distinct-235">[sec:distinct-235]</a>, not multiplicity.

Splitting $`T_a=s_a+T_{a+1}`$ and using $`h_{a+1}=b_ah_a`$ gives $`X_{a+1}=b_aX_a-m_a`$, where $`m_a=h_{a+1}s_a`$. Explicitly,
``` math
\begin{equation}
\label{eq:actual-digit}
 b_a=\frac{\operatorname{H}(2^{a+1})}{\operatorname{H}(2^a)},\qquad
 m_a=\sum_{\substack{x\in\mathcal S_P\\2^a\le x<2^{a+1}}}
       \frac{\operatorname{H}(2^{a+1})}{2\operatorname{H}(x)}.
\end{equation}
```
Since $`h_0=1/2`$, we also have $`h_{a+1}=(b_0\cdots b_a)/2`$ and $`m_a/(b_0\cdots b_a)=s_a/2`$. For $`[2,4)`$, the running LCMs at $`2,3`$ are $`2,6`$ and $`h_2=6`$, giving $`m_1=6(1/2+1/6)=4`$ and $`b_1=6`$. For the block displayed above, $`h_5=10800`$ and
``` math
m_4=4\cdot15+3+2\cdot1=65,\qquad b_4=30.
```

<div id="res:dyadic-alphabet" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperCompleteR20/DyadicAlphabetWhole.lean#L19">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-dyadic-alphabet-comparator">Comparator</a></p>

**Lemma 2** (integer coefficients and four possible bases). *For every $`a\ge0`$, $`m_a`$ is a positive integer and $`b_a\in\{2,6,10,30\}`$. The word “numerator” does not impose the positional-digit restriction $`m_a<b_a`$; that restriction need not hold.*

</div>

<div class="proof">

*Proof.* For $`x<2^{a+1}`$ we have $`2\operatorname{H}(x)\mid\operatorname{H}(2^{a+1})`$, so every summand in $`m_a`$ is integral. The interval contains $`2^a`$, giving positivity. Between successive powers of $`2`$ there is at most one power of $`3`$ and at most one power of $`5`$. Along with the final factor $`2`$, these give $`b_a\in\{2,6,10,30\}`$. ◻

</div>

<div id="res:actual-orbit" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7SeriesIdentification.lean#L168">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-actual-orbit-comparator">Comparator</a></p>

**Proposition 3** (the tail recurrence and a quadratic bound). *The series defining $`S,T_a`$ converge. For every $`a\ge0`$,
``` math
X_{a+1}=b_aX_a-m_a,\qquad
 0<X_a\le\frac{8640}{343}(a+1)^2<90(a+1)^2.
```
For every integer $`B\ge1`$, either $`BX_a`$ is integral at some index (and hence at every later index), or $`\operatorname{dist}(BX_a,\mathbb Z)\ge1/31`$ at arbitrarily large indices.*

</div>

<div class="proof">

*Proof.* We count at most $`(a+1)^2`$ smooth integers in $`[2^a,2^{a+1})`$: each pair of exponents of $`3,5`$, both at most $`a`$, allows at most one exponent of $`2`$. By <a href="#res:cube" data-reference-type="eqref" data-reference="res:cube">[res:cube]</a>, $`s_a\le30(a+1)^2/8^a`$. As $`h_a\le8^a/2`$ and $`a+j+1\le(a+1)(j+1)`$, we have
``` math
X_a\le15(a+1)^2\sum_{j\ge0}\frac{(j+1)^2}{8^j}
     =\frac{8640}{343}(a+1)^2.
```
This also proves convergence. Splitting off $`s_a`$ gives the recurrence, since $`h_{a+1}=b_ah_a`$ and $`m_a=h_{a+1}s_a`$.

For the final assertion, suppose that every sufficiently late distance is strictly less than $`1/31`$, and write $`BX_a=z_a+e_a`$, where $`z_a`$ is integral and $`|e_a|<1/31`$. The recurrence makes $`e_{a+1}-b_ae_a`$ an integer of absolute value less than $`(1+b_a)/31\le1`$. Thus $`e_{a+1}=b_ae_a`$. A nonzero error would therefore at least double at each step, contradicting $`|e_a|<1/31`$. All sufficiently late errors vanish; integrality then persists by the recurrence. ◻

</div>

The loss of bounded tails is genuine. For $`a\ge1`$, every odd part $`3^j5^k<2^a`$ has a unique multiple by a power of $`2`$ in $`[2^a,2^{a+1})`$. Taking $`0\le j,k\le\lfloor a/5\rfloor`$ ensures this inequality because $`15<2^5`$. Each such integer contributes at least $`1`$ to $`m_a`$, so
``` math
m_a\ge(\lfloor a/5\rfloor+1)^2,\qquad X_a>m_a/30.
```
Rationality would still put the tails in a fixed lattice, but not in a finite set. Repetition alone also gives no recovery rule: the maps $`y\mapsto(m_a+y)/b_a`$ now depend on $`a`$ and form an infinite family. The proof in Section <a href="#sec:distinct-235" data-reference-type="ref" data-reference="sec:distinct-235">[sec:distinct-235]</a> needed both finiteness and unique recovery. We instead use the quadratic bound to limit the positive integer tails required by rationality.

The Cantor-series form $`S/2=\sum_{a\ge0}m_a/(b_0\cdots b_a)`$ also explains why the criteria in \[erdosstraus1974, Theorem 2.1\] and \[hancltijdeman2004, Theorem 3.1\] do not apply: their small-numerator hypothesis $`m_a/(b_{a-1}b_a)\to0`$ fails with bounded $`b_a`$ and these unbounded $`m_a`$. The [companion’s tail estimates](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-repeated-bounds) give sharper bounds.

<div id="res:denominator-reduction" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7RationalBridge.lean#L80">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-denominator-reduction-comparator">Comparator</a></p>

**Theorem 4** (rationality gives positive integer tails). *If $`S=A/D`$ in lowest terms, where $`D=2^u3^v5^wB`$ and $`\gcd(B,30)=1`$, then for every $`a\ge a_0=u+1+2v+3w`$,
``` math
d_a=BX_a\in\mathbb Z_{>0},\qquad
 d_{a+1}=b_ad_a-Bm_a,\qquad d_a\le90B(a+1)^2.
```*

</div>

<div class="proof">

*Proof.* For $`a\ge1`$, clearing the finite prefix gives
``` math
\begin{equation}
\label{eq:prefix-lattice}
 X_a=h_aS-\sum_{\substack{x\in\mathcal S_P\\x<2^a}}
                 \frac{h_a}{\operatorname{H}(x)},\qquad
 \sum_{\substack{x\in\mathcal S_P\\x<2^a}}\frac{h_a}{\operatorname{H}(x)}\in\mathbb Z.
\end{equation}
```
If $`a\ge u+1+2v+3w`$, the exponent $`a-1`$ of $`2`$ in $`h_a`$ is at least $`u`$, and $`2^a\ge3^v,5^w`$. Therefore $`2^u3^v5^w\mid h_a`$, and $`BX_a`$ differs from $`h_aA/(2^u3^v5^w)`$ by an integer. Positivity, recurrence and the bound follow from Proposition <a href="#res:actual-orbit" data-reference-type="ref" data-reference="res:actual-orbit">3</a>. ◻

</div>

<div id="res:exact-onset" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-exact-onset">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-exact-onset-comparator">Comparator</a></p>

**Corollary 5** (the first index at which the denominator clears). *Under the same lowest-terms hypothesis, put $`M=2^u3^v5^w`$ and let $`\operatorname{den}`$ denote the positive reduced denominator. For $`a\ge1`$,
``` math
\operatorname{den}(BX_a)=\frac{M}{\gcd(M,h_a)}.
```
Consequently $`BX_a`$ is integral exactly when $`2^a\ge\max(2^{u+1},3^v,5^w)`$. The first such $`a`$ can be found by integer comparisons, without logarithmic rounding.*

</div>

<div class="proof">

*Proof.* Equation <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a> shows that $`BX_a`$ and $`h_aA/M`$ have the same reduced denominator. Since $`\gcd(A,M)=1`$, this denominator is $`M/\gcd(M,h_a)`$. Divisibility by each of $`2^u,3^v,5^w`$ gives the three stated inequalities. ◻

</div>

The two denominator parts have different roles: $`M`$ determines when clearing occurs; $`B`$ is the multiplier left after clearing. For $`D=2^3 3^2 5\cdot7`$, the first integral $`7X_a`$ would occur at $`a=4`$, not the sufficient index $`11`$ in the theorem. Thus an early nonintegral tail need not stay nonintegral. The [companion’s denominator calculation](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-denominator) also gives the reduced denominator of $`X_a`$ itself.

<a id="sec:escape"></a>

# A residue criterion

<span id="sec:open" label="sec:open"></span> A finite segment bounds the starting tail. Its integrality would constrain the endpoint tail to a residue class. The residue inequality expresses the same obstruction in either form.

For two steps the recurrence reads $`X_{\ell+2}=b_{\ell+1}b_\ell X_\ell-(b_{\ell+1}m_\ell+m_{\ell+1})`$. To keep track of the multiplicative and additive terms over $`h`$ steps, write
``` math
W_{\ell,0}=1,\quad F_{\ell,0}=0,\qquad
 W_{\ell,h+1}=b_{\ell+h}W_{\ell,h},\quad
 F_{\ell,h+1}=b_{\ell+h}F_{\ell,h}+m_{\ell+h}.
```
Induction yields
``` math
\begin{equation}
\label{eq:actual-tail}
 X_{\ell+h}=W_{\ell,h}X_\ell-F_{\ell,h}.
\end{equation}
```
Since $`b_a=h_{a+1}/h_a`$, its product telescopes to $`W_{\ell,h}=h_{\ell+h}/h_\ell`$. Thus
``` math
\frac{F_{\ell,h}}{W_{\ell,h}}
 =h_\ell\sum_{a=\ell}^{\ell+h-1}s_a,
 \qquad
 \frac{X_{\ell+h}}{W_{\ell,h}}=h_\ell T_{\ell+h}.
```
These finite and remaining contributions sum to $`X_\ell`$, both in the starting normalisation $`h_\ell`$, by <a href="#eq:actual-tail" data-reference-type="eqref" data-reference="eq:actual-tail">[eq:actual-tail]</a>. Throughout this section let
``` math
\begin{equation}
\label{eq:actual-bound}
 K(B,a)=90B(a+1)^2.
\end{equation}
```
The bound $`0<BX_{\ell+h}\le K(B,\ell+h)`$ and <a href="#eq:actual-tail" data-reference-type="eqref" data-reference="eq:actual-tail">[eq:actual-tail]</a> enclose the starting tail in the interval
``` math
\frac{BF_{\ell,h}}{W_{\ell,h}}<BX_\ell
 \le\frac{BF_{\ell,h}+K(B,\ell+h)}{W_{\ell,h}}.
```
Width below $`1`$ gives at most one integer, not necessarily none. With $`W=W_{\ell,h}`$ and $`F=F_{\ell,h}`$, the interval contains no integer exactly when
``` math
BF+K(B,\ell+h)<W\bigl(\lfloor BF/W\rfloor+1\bigr).
```
The right side is $`W`$ times the first integer strictly above $`BF/W`$. Its excess over $`BF`$ is the least positive residue of $`-BF`$ modulo $`W`$: the residue measures the gap to that integer in units of $`1/W`$.

For integers $`W\ge1,t`$, define $`\operatorname{lpr}_W(t)=1+((t-1)\bmod W)`$, with remainder in $`\{0,\ldots,W-1\}`$. Its values lie in $`\{1,\ldots,W\}`$, so the zero class is represented by $`W`$. This matches the open left endpoint: if $`W\mid BF`$, the next possible integer is one full unit above $`BF/W`$, not $`BF/W`$ itself.

<div id="res:consumer" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7BasicAssembly.lean#L138">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-consumer-comparator">Comparator</a></p>

**Lemma 6** (least positive residues). *If $`d`$ is a positive integer with $`d\le K`$ and $`d\equiv -BF\pmod W`$, where $`W\ge1`$, then $`\operatorname{lpr}_W(-BF)\le K`$.*

</div>

<div class="proof">

*Proof.* The least positive representative is at most every positive representative of its class, and in particular at most $`d`$. ◻

</div>

In <a href="#eq:actual-tail" data-reference-type="eqref" data-reference="eq:actual-tail">[eq:actual-tail]</a>, an integral $`BX_\ell`$ makes $`BX_{\ell+h}`$ such a positive representative.

For $`\ell=1,h=6`$, direct iteration gives $`W_{1,6}=648000`$ and $`F_{1,6}=524431`$. Since $`K(1,7)=5760`$, the interval is
``` math
\frac{524431}{648000}<X_1\le\frac{530191}{648000}<1.
```
Equivalently, $`\operatorname{lpr}_{W_{1,6}}(-F_{1,6})=123569>5760`$ certifies $`X_1\notin\mathbb Z`$, treating only $`B=1`$ at $`\ell=1`$. For denominators $`MB`$, varying $`B`$ covers the part coprime to $`30`$; arbitrarily late starts allow each supported part $`M`$ to clear.

<div id="r4-repeated-criterion">

</div>

<div id="res:windowconsumer" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7WindowResults.lean#L51">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-windowconsumer-comparator">Comparator</a></p>

**Theorem 7** (a residue criterion for irrationality). *The number $`S`$ is irrational if and only if
``` math
\begin{equation}
\label{eq:escape}
 \begin{gathered}
 \text{for every }B\ge1\text{ with }\gcd(B,30)=1
 \text{ and every }a_0\ge1,\\
 \text{there are }\ell\ge a_0,\ h\ge1\text{ such that}
 \operatorname{lpr}_{W_{\ell,h}}(-BF_{\ell,h})>K(B,\ell+h).
 \end{gathered}
\end{equation}
```*

</div>

<div class="proof">

*Proof.* Suppose that <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a> holds and $`S`$ is rational. By Theorem <a href="#res:denominator-reduction" data-reference-type="ref" data-reference="res:denominator-reduction">4</a>, $`d_a=BX_a`$ is a positive integer for every sufficiently large $`a`$. Choose a segment beyond that onset. Equation <a href="#eq:actual-tail" data-reference-type="eqref" data-reference="eq:actual-tail">[eq:actual-tail]</a> gives $`d_{\ell+h}\equiv-BF_{\ell,h}\pmod{W_{\ell,h}}`$, contrary to Lemma <a href="#res:consumer" data-reference-type="ref" data-reference="res:consumer">6</a> and <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>.

Conversely, suppose that $`S`$ is irrational and fix $`B,\ell\ge1`$. Equation <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a> makes $`BX_\ell`$ nonintegral. The distance upwards to the next integer, $`\delta=\lceil BX_\ell\rceil-BX_\ell\in(0,1)`$, is now fixed as the segment length $`h`$ grows. We have $`W_{\ell,h}\ge2^h`$, whereas $`X_{\ell+h}`$ has only quadratic growth. Consequently $`\delta+BX_{\ell+h}/W_{\ell,h}`$ lies in $`(0,1)`$ for sufficiently large $`h`$. This ensures that the following representative lies strictly between $`0`$ and the modulus, so it is the least positive one:
``` math
\operatorname{lpr}_{W_{\ell,h}}(-BF_{\ell,h})
 =\lceil BX_\ell\rceil W_{\ell,h}-BF_{\ell,h}
 =\delta W_{\ell,h}+BX_{\ell+h}.
```
The positive constant $`\delta`$ multiplies an exponentially growing $`W_{\ell,h}`$, so the first term eventually exceeds $`K(B,\ell+h)`$. This proves the inequality from every fixed start, and hence after every prescribed onset $`a_0`$. No bound uniform in $`B`$ or $`\ell`$ is needed for this direction. ◻

</div>

At a fixed start, success rules out integrality of $`BX_\ell`$. If $`BX_\ell`$ is integral, the recurrence, positivity and the bound prevent success at any length; for all sufficiently large $`h`$, $`\operatorname{lpr}_{W_{\ell,h}}(-BF_{\ell,h})=BX_{\ell+h}`$. If $`BX_\ell`$ is nonintegral, every sufficiently long segment succeeds, even when $`S`$ is rational with a denominator not yet cleared at $`\ell`$. Increasing the length does not remove the need for starts beyond every cutoff. A finite failed search distinguishes neither case.

The converse obtains $`\delta>0`$ from irrationality. Proving <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a> without that assumption is the remaining task. The upper-bound property of $`K`$ is essential: a zero bound would make every residue inequality automatic. The [companion’s residue analysis](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-residue) treats the fixed-start formula and smaller or more general bounds.

<div class="minipage">

The repeated three-prime question can therefore be written in three equivalent forms.

<div class="problem">

**Problem 8** (the repeated three-prime target). Prove that $`S=\mathcal R_{\{2,3,5\}}`$ is irrational.

</div>

<div id="prob:tails269" class="problem">

**Problem 9** (no reduced tail is an integer). Prove that for every $`a\ge1`$ and every integer $`B\ge1`$ coprime to $`30`$,
``` math
\begin{equation}
\label{eq:tail-nonintegrality}
 BX_a\notin\mathbb Z.
\end{equation}
```

</div>

<div id="prob:producer" class="problem">

**Problem 10** (residue inequalities after every starting index). Prove <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>.

</div>

</div>

The equivalence follows from <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a>, denominator clearing and Theorem <a href="#res:windowconsumer" data-reference-type="ref" data-reference="res:windowconsumer">7</a>; none of the three assertions is proved for $`S`$. The [companion’s discussion of the repeated sum](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-open) records finite calculations and the hypotheses missing from proposed finite-difference and function-theoretic arguments.

<a id="sec:two-prime"></a>

# Two-prime transcendence

For two primes, the distinct sum is affine in one Hecke–Mahler value; the repeated sum is quadratic in it. Fan gave the factorisation of the repeated sum and its transcendence consequence in his post of 26 June 2026 \[fan2026comment\].

<div id="res:two-prime-transcendence" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-two-prime-transcendence">Lean†</a></p>

**Theorem 11** (both two-prime sums). *<span id="res:two-prime-repeated-transcendence" label="res:two-prime-repeated-transcendence"></span> Let $`p<q`$ be distinct primes. Put $`\theta=\log p/\log q`$ and $`A=\sum_{n\ge0}p^{-n}q^{-\lfloor n\theta\rfloor}`$. Let $`\mathcal R_{p,q}`$ sum the reciprocal running LCM at every positive $`\{p,q\}`$-smooth integer, and let $`\mathcal D_{p,q}`$ count each distinct running LCM once. Then
``` math
\begin{equation}
\label{eq:two-prime-affine}
 \mathcal D_{p,q}=\frac{(q-p)A+p}{q-1},\qquad
 \mathcal R_{p,q}=\frac{(p+q-1)A-(p-1)A^2}{q-1}.
\end{equation}
```
Both numbers are transcendental.*

</div>

The Lean proof assumes the transcendence theorem of Bugeaud and Laurent; the two identities in <a href="#eq:two-prime-affine" data-reference-type="eqref" data-reference="eq:two-prime-affine">[eq:two-prime-affine]</a> are proved in Lean without it.

<div class="proof">

*Proof.* Write $`x=1/p`$, $`y=1/q`$, $`m_n=\lfloor n\theta\rfloor`$ and $`\delta_n=m_{n+1}-m_n`$. Unique factorisation makes $`\theta`$ irrational, and $`0<\theta<1`$ gives $`\delta_n\in\{0,1\}`$. The initial value and the positive powers of $`p`$ contribute $`A=\sum_{n\ge0}x^ny^{m_n}`$. There is one $`q`$-power strictly between $`p^n`$ and $`p^{n+1}`$ exactly when $`\delta_n=1`$, so the positive powers of $`q`$ contribute
``` math
B=\sum_{n\ge0}\delta_nx^ny^{m_n+1},\qquad \mathcal D_{p,q}=A+B.
```
Absolute convergence allows an index shift. Multiplying $`y^{m_{n+1}}-y^{m_n}=\delta_ny^{m_n}(y-1)`$ by $`x^{n+1}`$ and summing gives $`(A-1)-xA=x(y-1)B/y`$. Therefore
``` math
B=\frac{p-(p-1)A}{q-1}.
```
For the repeated sum, the running LCM at $`p^iq^j`$ is $`p^{i+\lfloor j/\theta\rfloor}q^{j+m_i}`$. Its reciprocal is the product of $`x^iy^{m_i}`$, which depends only on $`i`$, and $`y^jx^{\lfloor j/\theta\rfloor}`$, which depends only on $`j`$. Absolute convergence therefore gives
``` math
\mathcal R_{p,q}
 =A\sum_{j\ge0}y^jx^{\lfloor j/\theta\rfloor}=A(1+B).
```
For the last equality, $`n=\lfloor j/\theta\rfloor`$ locates $`q^j`$ between $`p^n`$ and $`p^{n+1}`$; hence $`m_n=j-1`$ and $`\delta_n=1`$. This matches the positive-$`j`$ terms with those of $`B`$, while $`j=0`$ contributes $`1`$. Substitution proves <a href="#eq:two-prime-affine" data-reference-type="eqref" data-reference="eq:two-prime-affine">[eq:two-prime-affine]</a>.

Factorisation alone would not prove transcendence of the product. The two identities instead express both sums as nonconstant polynomials over $`\mathbb Q`$ in the same $`A`$. It remains to prove $`A`$ transcendental. For this we use the Hecke–Mahler series $`F_\theta(x,y)=\sum_{n\ge1}\sum_{k=1}^{m_n}x^ny^k`$. Geometric summation gives
``` math
\begin{equation}
\label{eq:hecke-mahler-boundary}
 A=\frac1{1-x}-\frac{1-y}{y}F_\theta(x,y).
\end{equation}
```
Bugeaud and Laurent’s theorem \[bugeaudlaurent2023, Theorem 1.1\] applies with intercept $`\rho=0`$, $`\beta=x`$ and $`\alpha=y`$: the slope $`\theta`$ is irrational and lies in $`(0,1)`$, $`x`$ and $`y`$ are nonzero algebraic numbers, $`|x|<1`$ and $`|xy^\theta|=p^{-2}<1`$. Thus $`F_\theta(x,y)`$ is transcendental; this case $`\rho=0`$ is due to Loxton and van der Poorten \[loxtonvdp1977, Theorem 8, p. 40\]. Thus $`A`$ is transcendental. The displayed affine and quadratic polynomials are nonconstant, so an algebraic value of either would force $`A`$ to be algebraic. ◻

</div>

The [companion’s two-prime calculation](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-two-prime) records an ordinary extension to the monoid generated by coprime integers $`1<p<q`$, such as $`4,9`$. That monoid need not contain all integers supported on the prime divisors of $`pq`$; multiplicatively dependent generators such as $`4,8`$ require a different calculation.

For larger prime sets, the sums over pure powers $`E_p=\sum_{\alpha\ge0}\operatorname{L}(p^\alpha)^{-1}`$ satisfy $`\mathcal D_P=\sum_{p\in P}E_p-(|P|-1)`$. The [companion’s prime-power subseries argument](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-prime-subseries) treats their irrationality as a remark with an ordinary proof awaiting formalisation. The source record contains no separate priority search for this claim. Irrationality of the individual subseries would not imply irrationality of their sum. The repeated series also contains mixed products of primes, whose multiplicities change the tail estimates.

<a id="sec:height-identities"></a>

# Identities for the running LCM and multiplicities

<span id="sec:cells" label="sec:cells"></span><span id="sec:fibre" label="sec:fibre"></span> Let $`p,q,r`$ be pairwise distinct primes. Write $`\operatorname{H}=\operatorname{H}_{\{p,q,r\}}`$ and $`\operatorname{K}(i,j,k)=\operatorname{H}(p^iq^jr^k)^{-1}`$ throughout this appendix and the next. The following identities underlie the grouping of the repeated series in Section <a href="#sec:lcm" data-reference-type="ref" data-reference="sec:lcm">3</a>.

<div id="res:lcm" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L49">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-lcm-comparator">Comparator</a></p>

**Proposition 12** (the running least common multiple). *Let $`p,q,r`$ be pairwise distinct primes and $`x\ge1`$. Then the running least common multiple is given by $`\operatorname{L}(x)=\operatorname{H}(x)`$.*

</div>

<div class="proof">

*Proof.* We have $`u\mid\operatorname{H}(x)`$ for every supported $`u\le x`$. For the reverse divisibility, take the maximal powers of $`p,q,r`$ below $`x`$: they belong to the prefix and are pairwise coprime, so their product divides its LCM. ◻

</div>

For each prime, $`x/p<p^{\lfloor\log_p x\rfloor}\le x`$. Multiplying gives
``` math
\begin{equation}
\label{res:cube}
 x^3/(pqr)<\operatorname{H}(x)\le x^3.
\end{equation}
```

<div id="res:cell" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-cell">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-cell-comparator">Comparator</a></p>

**Proposition 13** (cells and jumps). *The running LCM is constant when the three integer logarithms are constant. A jump in exactly one logarithm multiplies it by the corresponding prime. The first $`n`$ positive powers of each prime, together with $`1`$, form $`3n+1`$ distinct points.*

</div>

<div class="proof">

*Proof.* The running LCM is a product of the three maximal pure powers, which proves the constancy and jump assertions. Unique factorisation separates the $`3n`$ positive pure powers from one another and from $`1`$. ◻

</div>

<div id="res:fibre-prop" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L407">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-fibre-prop-comparator">Comparator</a></p>

**Proposition 14** (grouping terms with the same running LCM). *For a finite exponent box $`\mathcal B`$, set $`F(H)=\{(i,j,k)\in\mathcal B:\operatorname{H}(p^iq^jr^k)=H\}`$. Then
``` math
\begin{equation}
\label{res:fibre}
 \sum_{(i,j,k)\in\mathcal B}\operatorname{K}(i,j,k)=\sum_H\frac{\#F(H)}H.
\end{equation}
```*

</div>

<div class="proof">

*Proof.* Partition the finite exponent box by the value of the running LCM. The terms in the part $`F(H)`$ all equal $`1/H`$. ◻

</div>

<a id="sec:rank"></a>

# The three-prime kernel

The two-prime proof separates the summand by exponents. For three primes, the carry in adding two fractional parts prevents any finite separation of $`i`$ from $`(j,k)`$. Diagonal rescaling leaves just two entry values, $`1`$ and $`1/r`$; choosing their threshold positions gives nonzero minors of every order. This concerns exact kernel identities, not identities after summation.

<div id="res:rank" class="example">

**Example 15**. For $`(p,q,r)=(2,3,5)`$, the leading two-by-two determinant is $`-1/15`$: its four entries are $`1,1/6,1/2,1/60`$, so it equals $`1/60-1/12`$.

</div>

A sum of $`d`$ separated products has rank at most $`d`$ in each layer. Thus the two-by-two example excludes only rank one; excluding every finite $`d`$ requires nonzero minors of arbitrary order. Their indices may depend on the order, but not on $`k`$.

<div id="res:infinite-rank" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7BasicAssembly.lean#L22">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-infinite-rank-comparator">Comparator</a></p>

**Theorem 16** (no finite separation of the kernel). *Let $`p,q,r`$ be primes with $`p\ne q`$, $`p\ne r`$ and $`q\ne r`$. For every $`n\ge0`$ there are injective maps $`I,J:\{0,\ldots,n-1\}\to\mathbb{N}`$ such that, for every $`k\ge0`$,
``` math
\det\bigl(\operatorname{K}(I(a),J(b),k)\bigr)_{0\le a,b<n}\ne0.
```
Consequently, for no finite $`d`$ do there exist rational-valued functions $`f_\ell(i)`$ and $`G_\ell(j,k)`$, $`0\le\ell<d`$, satisfying
``` math
\operatorname{K}(i,j,k)=\sum_{\ell<d}f_\ell(i)G_\ell(j,k)
 \qquad\hbox{for all }i,j,k.
```*

</div>

<div class="proof">

*Proof.* Fix $`k`$. The powers of $`p`$ and $`q`$ separate into row and column factors, as before. Only the power of $`r`$ retains an interaction between $`i`$ and $`j`$. Put $`c=r^{-1}`$, $`x_i=\{i\log_r p\}`$ and $`y_j=\{j\log_r q\}`$, where braces denote fractional parts. Then
``` math
\lfloor i\log_r p+j\log_r q\rfloor
 =\lfloor i\log_r p\rfloor+\lfloor j\log_r q\rfloor
   +\mathbf1_{\{x_i+y_j\ge1\}}.
```
The last term is the carry when the two fractional parts are added. Putting all the other prime powers into row and column factors gives
``` math
\operatorname{K}(i,j,k)=U_i(k)^{-1}C_{ij}V_j(k)^{-1},\qquad
 C_{ij}=c^{\mathbf1_{\{x_i+y_j\ge1\}}},
```
where
``` math
\begin{aligned}
 U_i(k)&=p^i q^{\lfloor\log_q(p^ir^k)\rfloor}
            r^{k+\lfloor\log_r p^i\rfloor},\\
 V_j(k)&=q^j p^{\lfloor\log_p(q^jr^k)\rfloor}
            r^{\lfloor\log_r q^j\rfloor}.
\end{aligned}
```
The positive factors preserve nonvanishing of minors and contain all dependence on $`k`$. In column $`j`$, the entry changes from $`1`$ to $`c`$ at the threshold $`1-y_j`$. Both $`\log_r p`$ and $`\log_r q`$ are irrational, so their fractional-part orbits are dense separately; no joint orbit is needed. For $`n\ge1`$, choose rows with $`0<x_{I(0)}<\cdots<x_{I(n-1)}<1`$. Then choose each column threshold between consecutive row phases. Writing $`s_b=1-y_{J(b)}`$, take

``` math
s_0\in(0,x_{I(0)}),\qquad
 s_b\in(x_{I(b-1)},x_{I(b)})\quad(1\le b<n).
```

The intervals for the $`s_b`$ are disjoint, so the column indices are distinct. The strict inequalities also avoid the threshold itself, and give $`x_{I(a)}+y_{J(b)}\ge1`$ exactly when $`b\le a`$. Thus multiplying row $`a`$ by $`U_{I(a)}(k)`$ and column $`b`$ by $`V_{J(b)}(k)`$ reduces the selected kernel minor to
``` math
T_n(c)=\begin{pmatrix}
 c&1&\cdots&1\\
 c&c&\cdots&1\\
 \vdots&\vdots&\ddots&\vdots\\
 c&c&\cdots&c
 \end{pmatrix},\qquad
 \det T_n(c)=c(c-1)^{n-1}.
```
Indeed, subtract each preceding row from the next, working upwards from the last row. Each row difference has just one nonzero entry, $`c-1`$, in its own column. The resulting triangular matrix has diagonal entries $`c,c-1,\ldots,c-1`$. The original determinant is therefore
``` math
c(c-1)^{n-1}
 \prod_{a<n}U_{I(a)}(k)^{-1}\prod_{b<n}V_{J(b)}(k)^{-1}\ne0.
```
The indices were chosen from $`C`$, independently of $`k`$. For $`n=0`$ the empty determinant equals $`1`$.

For the final assertion, suppose a separation with $`d`$ summands existed and fix any $`k`$. On the rows $`I(0),\ldots,I(d)`$ and columns $`J(0),\ldots,J(d)`$ its matrix would be the product of the $`(d+1)\times d`$ matrix $`(f_\ell(I(a)))_{a,\ell}`$ and the $`d\times(d+1)`$ matrix $`(G_\ell(J(b),k))_{\ell,b}`$. Its rank would be at most $`d`$, so its determinant would vanish, contrary to the minor just constructed. ◻

</div>

No continuity or boundedness is assumed for the separated factors.

<div id="res:admissible-modular-minors" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7ModularMinors.lean#L133">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-admissible-modular-minors-comparator">Comparator</a></p>

**Corollary 17** (the same minors modulo integers coprime to $`30`$). *For $`(p,q,r)=(2,3,5)`$ and every $`n\ge1`$, there are injective maps $`I,J:\{0,\ldots,n-1\}\to\mathbb{N}`$, chosen independently of $`B`$ and $`k`$, such that for every $`B\ge2`$ coprime to $`30`$ and every $`k\ge0`$, the selected $`n\times n`$ kernel matrix has unit determinant over $`\mathbb Z/B\mathbb Z`$, with each reciprocal prime power interpreted by its modular inverse.*

</div>

<div class="proof">

*Proof.* Choose the maps from Theorem <a href="#res:infinite-rank" data-reference-type="ref" data-reference="res:infinite-rank">16</a>. Every row and column factor is a unit modulo $`B`$. The normalised determinant is $`5^{-1}(-4/5)^{n-1}`$, also a unit. ◻

</div>

The modulus may be composite, for example $`49`$ or $`77`$. Coprimality with $`30`$ makes both the reciprocal entries and the determinant units: the latter introduces only a power of $`4`$ in its numerator.

<a id="leading-minors."></a>

#### Leading minors.

The leading $`4\times4`$ block at $`\{2,3,5\}`$ is singular:
``` math
\operatorname{K}(3,j,0)=\frac1{120}\operatorname{K}(0,j,0)\qquad(0\le j<4).
```
Evaluate the running LCM at $`3^j`$ and $`8\cdot3^j`$ to obtain these equalities. At $`j=4`$, however, $`\operatorname{K}(3,4,0)-\operatorname{K}(0,4,0)/120=-1/19440000`$. The selection in the theorem avoids this problem by choosing column thresholds at distinct cuts among the row phases. An arbitrary sample may miss gaps; its rank counts distinct cuts, with one exception.

<div id="res:finite-cut-rank" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7FiniteCutRank.lean#L182">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md#res-finite-cut-rank-comparator">Comparator</a></p>

**Proposition 18** (rank of a matrix of threshold columns). *Let $`m\ge1`$ and let $`c`$ lie in a field with $`c\ne 0,1`$. For $`0\le k\le m`$ write $`v_k`$ for the length-$`m`$ column with a $`1`$ in each of the first $`k`$ coordinates and $`c`$ thereafter. A matrix whose distinct columns are $`v_k`$ for $`k`$ in a nonempty set $`E`$ has rank $`|E|-\mathbf 1_{\{0,m\}\subseteq E}`$.*

</div>

The exception is the pair of constant columns, $`v_0=c v_m`$. All other distinct cuts contribute independently.

<div class="proof">

*Proof.* List $`E=\{k_1<\cdots<k_t\}`$. The $`t-1`$ differences $`v_{k_{j+1}}-v_{k_j}=(1-c)\mathbf 1_{\{k_j,\ldots,k_{j+1}-1\}}`$ have disjoint nonempty supports, hence are linearly independent. If $`k_1>0`$ or $`k_t<m`$, their union misses a coordinate where $`v_{k_1}`$ is nonzero, so the rank is $`t`$. If $`k_1=0`$ and $`k_t=m`$, then $`v_0=c\,\mathbf 1`$ lies in the span of the differences (their sum is $`(1-c)\mathbf 1`$), so the rank is $`t-1`$. ◻

</div>

Order the sampled row phases and take $`c=1/r`$ over $`\mathbb Q`$. The formula then gives the rank of every nonempty rectangular sample, independently of $`k`$: the layer changes only the nonzero diagonal factors. The [companion’s kernel analysis](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-rank) gives the exact rational comparisons.

<a id="approximation."></a>

#### Approximation.

The diagonal rescaling preserves rank but removes the kernel’s decay. Retaining rows $`i<N`$ in the original kernel gives $`N`$ separated terms; $`\operatorname{H}(x)>x^3/(pqr)`$ makes the error tend to zero uniformly and in $`\ell^1(\mathbb N^3)`$. The rescaled matrix instead has uniform distance $`(1-1/r)/2`$ from finite-rank matrices. The [companion’s approximation theorem](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-approximation) proves both statements. Neither implies irrationality of the scalar sum.

<a id="app:sources"></a>

# Verification, reproducibility and sources

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-269-three-prime-running-lcm.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

The five-map proof is in [the distinct-value development](https://github.com/wcook04/plectis-erdos/blob/5154f4c46fa5d5ab2cff8df857a0b10f310cbeeb/lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean) and [its block-series criterion](https://github.com/wcook04/plectis-erdos/blob/5154f4c46fa5d5ab2cff8df857a0b10f310cbeeb/lean/ErdosProblems/Erdos269/DistinctHeightBlockRadix.lean). Its statement has no recorded Comparator comparison. The evidence record fixes the source versions; the named input for two-prime transcendence is stated beside that theorem.

The [programs for sums over distinct values](https://github.com/wcook04/plectis-erdos/tree/10178c4df40cb27d83b5ebb1ec337dd588b82998/research/experiments/erdos269/distinct_height) calculate the interval endpoints and finite-state examples using exact arithmetic; the proof in Section <a href="#sec:distinct-235" data-reference-type="ref" data-reference="sec:distinct-235">[sec:distinct-235]</a> derives its constants directly.

The [companion](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-five-maps) compares one-jump and dyadic bounds. Its finite-state extension uses earlier blocks to sharpen the intervals. Saved exact computations satisfy the criterion for every three-prime set and $`292`$ of the $`330`$ four-prime sets of primes at most $`31`$. The criterion and computations remain remarks awaiting formalisation. For $`\{2,3,5,7\}`$, two admissible automaton words induce the same affine map, defeating first-block recovery at every refinement. Equal maps alone do not give equal arithmetic tails.

The [companion’s source inventory](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-source-inventory) covers the ordinary general and subseries arguments, the 26 September 2026 AI check and its corrections. No independent human mathematical review has been reported.

<a id="further-comparisons"></a>

## Further comparisons

The companion compares our bounded-base series with the criteria of Erdős–Straus \[erdosstraus1974\], Hančl–Tijdeman \[hancltijdeman2004\] and Diananda–Oppenheim \[dianandaoppenheim1955\]; the bounded-ratio argument with Erdős–Taylor \[erdostaylor1957, Theorem 1, p. 600\] and Fan \[fan2026strongly, Lemma 3.1, p. 7\]; and integer recurrences with Hančl–Tijdeman’s polynomial Cantor-series results \[hancltijdeman2008, Theorems 2.2, 3.1 and 4.2\]. Koutsoukou-Argyraki and Li’s Isabelle development \[afperdosstraus2020\] formalises classical criteria, not this repeated series.

The transcendence comparisons concern finite differences \[lucaouaknineworrell2025\], echoing \[kebis2024echoing\], fixed-base digit complexity \[adamczewskibugeaud2007\] and multivariate Mahler theory \[adamczewskifaverjon2026\]. The companion exhibits nonzero third-difference boundary terms and distinguishes variable-base digits from fixed-base expansions: quadratic growth supplies neither the missing cancellation nor recurrence hypotheses. Fixed-prime semigroups \[tijdemanmeijer1974; languasco2025\] and other Ahmes-series problems \[kovactao2024\] supply context, not estimates used in our counting proof.

<a id="statements-and-declarations"></a>

## Statements and declarations

<a id="authorship-and-availability."></a>

#### Authorship and availability.

AI agents carried out most of the research and drafting. The companion contains the longer proofs and exact computations, together with the hypotheses and limitations of the unsuccessful approaches.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem number and its status as of 28 July 2026 are taken from Thomas Bloom’s Erdős Problems catalogue \[erdosproblems\]. We thank Wouter van Doorn for advice on exposition, particularly on unexplained terminology, unnecessary notation and restrictive hypotheses. His advice concerned a note on Problem #243; he has not reviewed this paper’s mathematics.

<div class="thebibliography">

99 Paul Erdős and Ronald L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L’Enseignement Mathématique **28**, L’Enseignement Mathématique (1980), [source](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf). Paul Erdős, *On the irrationality of certain series: problems and results*, in *New Advances in Transcendence Theory*, Cambridge University Press (1988), 102–109, [doi:`10.1017/CBO9780511897184.009`](https://doi.org/10.1017/CBO9780511897184.009). Paul Erdős, *Letter to the Editor*, Fibonacci Quarterly **12**, no. 4 (1974), 335, [source](https://www.fq.math.ca/Scanned/12-4/letter.pdf). Thomas F. Bloom, *Erdős Problem \#269* (2026), [source](https://www.erdosproblems.com/269). Accessed 28 July 2026. Yann Bugeaud and Michel Laurent, *Transcendence and continued fraction expansion of values of Hecke–Mahler series*, Acta Arithmetica **209** (2023), 59–90, [doi:`10.4064/aa220323-18-1`](https://doi.org/10.4064/aa220323-18-1); arXiv:[2203.12901](https://arxiv.org/abs/2203.12901). John H. Loxton and Alfred J. van der Poorten, *Arithmetic properties of certain functions in several variables III*, Bulletin of the Australian Mathematical Society **16** (1977), 15–47, [doi:`10.1017/S0004972700022978`](https://doi.org/10.1017/S0004972700022978). Steve Fan, *Comment on Erdős Problem \#269, thread 269, post 7218* (2026), [source](https://www.erdosproblems.com/forum/thread/269#post-7218). Public forum post, 26 June 2026, thread 269, post 7218. P. H. Diananda and A. Oppenheim, *Criteria for irrationality of certain classes of numbers II*, American Mathematical Monthly **62**, no. 4 (1955), 222–225. Cited in the form stated by Serbenyuk, arXiv:[1706.03124](https://arxiv.org/abs/1706.03124), Theorem 1. Paul Erdős and Ernst G. Straus, *On the irrationality of certain series*, Pacific Journal of Mathematics **55**, no. 1 (1974), 85–92, [doi:`10.2140/pjm.1974.55.85`](https://doi.org/10.2140/pjm.1974.55.85). Jaroslav Hančl and Robert Tijdeman, *On the irrationality of Cantor and Ahmes series*, Publicationes Mathematicae Debrecen **65**, no. 3–4 (2004), 371–380, [doi:`10.5486/PMD.2004.3254`](https://doi.org/10.5486/PMD.2004.3254). Paul Erdős and S. James Taylor, *On the set of points of convergence of a lacunary trigonometric series and the equidistribution properties of related sequences*, Proceedings of the London Mathematical Society **s3-7**, no. 1 (1957), 598–615, [doi:`10.1112/plms/s3-7.1.598`](https://doi.org/10.1112/plms/s3-7.1.598). Steve Fan, *Strongly complete sets and a conjecture of Erdős* (2026), [source](https://arxiv.org/abs/2607.14071v1); arXiv:[2607.14071](https://arxiv.org/abs/2607.14071). The cited Lemma 3.1 is in arXiv v1, 15 July 2026. Jaroslav Hančl and Robert Tijdeman, *On the irrationality of polynomial Cantor series*, Acta Arithmetica **133**, no. 1 (2008), 37–52, [doi:`10.4064/aa133-1-3`](https://doi.org/10.4064/aa133-1-3). Florian Luca, Joël Ouaknine and James Worrell, *Transcendence of Hecke–Mahler Series*, Bulletin of the London Mathematical Society **57**, no. 5 (2025), 1360–1368, [doi:`10.1112/blms.70033`](https://doi.org/10.1112/blms.70033); arXiv:[2412.07908](https://arxiv.org/abs/2412.07908). Numbered references use the published article. Pavol Kebis, Florian Luca, Joël Ouaknine, Andrew Scoones and James Worrell, *On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words*, in *51st International Colloquium on Automata, Languages, and Programming (ICALP 2024)*, Leibniz International Proceedings in Informatics **297**, Schloss Dagstuhl – Leibniz-Zentrum für Informatik (2024), 144:1–144:15, [doi:`10.4230/LIPIcs.ICALP.2024.144`](https://doi.org/10.4230/LIPIcs.ICALP.2024.144). Robert Tijdeman and H. G. Meijer, *On integers generated by a finite number of fixed primes*, Compositio Mathematica **29**, no. 3 (1974), 273–286, [source](https://www.numdam.org/article/CM_1974__29_3_273_0.pdf). Alessandro Languasco, Florian Luca, Pieter Moree and Alain Togbé, *Sequences of integers generated by two fixed primes*, Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg **95** (2025), 123–148, [doi:`10.1007/s12188-025-00293-9`](https://doi.org/10.1007/s12188-025-00293-9); arXiv:[2309.12806](https://arxiv.org/abs/2309.12806). Vjekoslav Kovač and Terence Tao, *On several irrationality problems for Ahmes series*, Acta Mathematica Hungarica **175** (2025), 572–608, [doi:`10.1007/s10474-025-01528-0`](https://doi.org/10.1007/s10474-025-01528-0); arXiv:[2406.17593](https://arxiv.org/abs/2406.17593). Angeliki Koutsoukou-Argyraki and Wenda Li, *Irrationality Criteria for Series by Erdős and Straus*, Archive of Formal Proofs (2020), [source](https://isa-afp.org/entries/Irrational_Series_Erdos_Straus.html). Entry dated 12 May 2020; proof-document version consulted: 6 February 2026. Boris Adamczewski and Yann Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer bases*, Annals of Mathematics **165**, no. 2 (2007), 547–565, [doi:`10.4007/annals.2007.165.547`](https://doi.org/10.4007/annals.2007.165.547). Boris Adamczewski and Colin Faverjon, *Mahler’s method in several variables and finite automata*, Annals of Mathematics **204**, no. 2 (2026), 455–533, [doi:`10.4007/annals.2026.204.2.1`](https://doi.org/10.4007/annals.2026.204.2.1). Online 13 September 2026; locators here refer to the [68-page author manuscript](https://faverjon.perso.math.cnrs.fr/AdamczewskiFaverjon_MahlerFiniteAutomata.pdf).

</div>
