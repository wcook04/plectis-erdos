<a id="erdos-269-three-prime-running-lcm"></a>

# Distinct running least common multiples

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We give a five-map proof that the reciprocals of the distinct running least common multiples of the $`5`$-smooth integers have an irrational sum. The spacing of powers of $`5`$ separates the tail images, so rationality would force a periodic jump sequence. The sum counted with multiplicity is a different number; its irrationality remains open here.

<a id="sec:problem"></a>

# Two sums from running least common multiples

The $`5`$-smooth integers are the positive integers whose prime factors belong to $`\{2,3,5\}`$. Their running least common multiples begin $`1,2,6,12,60,60,120,360,360,\ldots`$. For a finite set of primes $`P`$, let $`\mathcal S_P`$ consist of $`1`$ and all positive integers whose prime factors belong to $`P`$, and put
``` math
\operatorname{L}(x)=\operatorname{lcm}\{u\in\mathcal S_P:u\le x\},\qquad
 \operatorname{H}_P(x)=\prod_{p\in P}p^{\lfloor\log_p x\rfloor}\quad(x\ge1).
```
Every integer in this finite set divides $`\operatorname{H}_P(x)`$. Conversely, the set contains the largest power of each $`p\in P`$ below or equal to $`x`$, so their product divides its least common multiple. Thus $`\operatorname{L}(x)=\operatorname{H}_P(x)`$. This value changes only at a positive prime power, where it is multiplied by that prime. Summing its distinct reciprocals gives
``` math
\mathcal D_P=1+\sum_{\substack{t=p^n\\p\in P,\ n\ge1}}\frac1{\operatorname{H}_P(t)}.
```
Positive powers of distinct primes never coincide, and geometric growth of the successive running LCMs gives convergence. We use $`\mathbb{N}=\{0,1,2,\ldots\}`$.

<div id="r4-five-map-theorem">

</div>

<div id="res:distinct-height-235" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean#L689">Lean</a></p>

**Theorem 1** (the sum over distinct running LCMs for $`\{2,3,5\}`$). *The number $`\mathcal D_{\{2,3,5\}}`$ is irrational.*

</div>

If the sum were rational, its normalised tails would take only finitely many values. We show that each such value determines both the next block of jumps and the following tail. Repetition of a tail would then force the blocks to be eventually periodic, contrary to the irrational frequency of powers of $`3`$. To recover a block from its tail, we use five affine maps whose images are separated by a bound obtained from the spacing of powers of $`5`$.

Erdős asserted irrationality of $`\mathcal D_P`$ for every finite $`P`$ with $`|P|\ge2`$ in a letter dated 1 January 1973, without printing a proof \[erdos1974letter, p. 335\]. Thus the theorem is a special case of that earlier assertion. The proof below supplies the five-map argument for $`\{2,3,5\}`$; the [long record](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-distinct-proof) gives a separate ordinary argument for general finite prime sets.

The question in Erdős Problem #269 concerns the sum with multiplicity,
``` math
\mathcal R_P=\sum_{u\in\mathcal S_P}\frac1{\operatorname{L}(u)},
```
as recorded in \[erdosgraham1980, p. 65\] and \[erdos1988, p. 106\]. For example, $`\operatorname{L}(5)=\operatorname{L}(6)=60`$ for $`P=\{2,3,5\}`$, giving $`2/60`$ in $`\mathcal R_P`$ and $`1/60`$ in $`\mathcal D_P`$. The theorem treats the sum over distinct values; the problem asks about the sum with multiplicity. Our arguments leave the latter unresolved for finite $`P`$ with $`|P|\ge3`$. For $`P=\{p\}`$ both sums equal $`p/(p-1)`$.

Section <a href="#sec:distinct-235" data-reference-type="ref" data-reference="sec:distinct-235">[sec:distinct-235]</a> proves the theorem. The [long record’s treatment of the repeated sum](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=scope-repeated) explains why its unbounded tail values require a different argument. It also gives the two-prime factorisation and the three-prime kernel results, with their full hypotheses.

<a id="sec:distinct"></a>

# Recovering the prime-power jumps

<span id="sec:distinct-235" label="sec:distinct-235"></span> For a rational number, long division has only finitely many possible remainders, and each remainder determines the next digit and remainder. The same two facts will prove useful here. Rationality bounds the number of tail values; the main work is to show that a tail determines the next block of prime-power jumps.

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
In the block $`(64,128]`$, the interior jumps occur in the opposite order, at $`81,125`$. Its constant term is $`1/3+1/15+1/30=13/30`$. The two blocks have the same multiplier $`30`$, but different numerators, $`9`$ and $`13`$. To recover the order from a tail value, we must still separate the possible values of the block maps.

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

To recover $`\tau_a`$ from $`Y_a`$, we need disjoint intervals containing the possible images. The bound $`0<Y_{a+1}<1`$ is insufficient, since $`G_{53}([0,1])=[3/10,1/3]`$ and $`G_5([0,1])=[3/10,2/5]`$ overlap. The table gives $`Y_a\ge3/10`$. With this lower bound, separation of these two images requires an upper bound $`U`$ satisfying
``` math
G_{53}(U)<G_5(3/10),\qquad
 \frac{9+U}{30}<\frac{33}{100},\qquad U<\frac9{10}.
```
It is therefore enough, for this pair of images, to improve the upper bound from $`1`$ to a number below $`9/10`$.

A power $`5^f`$ belongs to block $`\lfloor f\log_2 5\rfloor`$. These indices start at $`2`$ and their successive differences are $`2`$ or $`3`$. Every three consecutive blocks therefore contain a power of $`5`$. Given $`a`$, let $`j\in\{a,a+1,a+2\}`$ be the first such block. The maps for blocks containing $`5`$ give $`Y_j\le7/15`$, since $`Y_{j+1}<1`$ and $`G_{35}(1)=7/15`$ bounds $`G_5(1)`$ and $`G_{53}(1)`$ as well. We now work *backwards* from $`j`$ to $`a`$. Each intervening block has map $`G_\varnothing`$ or $`G_3`$, and $`G_3(y)\le G_\varnothing(y)=(1+y)/2`$ for $`y\ge0`$. At most two backward steps give the successive bounds $`7/15`$, $`11/15`$, $`13/15`$. Hence
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

Since $`Y_{a+1}\in I`$, the actual tail $`Y_a`$ belongs to exactly one of these five image intervals, identifying $`\tau_a`$. For instance, $`Y_a\in[31/100,74/225]`$ forces $`\tau_a=53`$ and gives $`Y_{a+1}=30Y_a-9`$. In general we calculate $`Y_{a+1}=b_{\tau_a}Y_a-\mu_{\tau_a}`$, identify its image interval, and continue. Each recovered value is the next arithmetic tail, so the same bound $`I`$ remains available at every step.

*Repetition would give a rational frequency.* The finitely many tail values obtained above include a repeated value $`Y_u=Y_v`$ with $`u<v`$. Since the image intervals are disjoint, this forces $`\tau_u=\tau_v`$. Applying the corresponding inverse map gives $`Y_{u+1}=Y_{v+1}`$. Induction yields $`\tau_{u+j}=\tau_{v+j}`$ for every $`j\ge0`$. Thus the entire later block word has period $`v-u`$.

To exclude this possibility, let $`\alpha=\log2/\log3`$. The number of powers of $`3`$ in block $`a`$ is $`\lfloor(a+1)\alpha\rfloor-\lfloor a\alpha\rfloor`$, and is determined by $`\tau_a`$. If the block word has eventual period $`\ell\ge1`$, let $`c`$ be the number of $`3`$-powers in one period. For every sufficiently large fixed $`a`$ and every $`n\ge1`$ we then have
``` math
\lfloor(a+n\ell)\alpha\rfloor=\lfloor a\alpha\rfloor+nc.
```
Dividing by $`n`$ and taking the limit gives $`\ell\alpha=c`$, contrary to unique factorisation, since it would imply $`2^\ell=3^c`$. ◻

</div>

<a id="scope-and-verification"></a>

# Scope and verification

The theorem concerns distinct running LCMs. In the sum with multiplicity, several smooth integers can have the same running LCM; the finite-state argument above does not apply. The three-prime repeated sum remains open. Its exact residue criterion and the supporting computations are developed in the [long record](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-residue).

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-269-three-prime-running-lcm.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

The [verification and source section](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=scope-verification) records the formal correspondence, computations and reproduction commands.

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

99 Paul Erdős and Ronald L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L’Enseignement Mathématique **28**, L’Enseignement Mathématique (1980), [source](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf). Paul Erdős, *On the irrationality of certain series: problems and results*, in *New Advances in Transcendence Theory*, Cambridge University Press (1988), 102–109, [doi:`10.1017/CBO9780511897184.009`](https://doi.org/10.1017/CBO9780511897184.009). Paul Erdős, *Letter to the Editor*, Fibonacci Quarterly **12**, no. 4 (1974), 335, [source](https://www.fq.math.ca/Scanned/12-4/letter.pdf). Thomas F. Bloom, *Erdős Problem \#269* (2026), [source](https://www.erdosproblems.com/269). Accessed 28 July 2026.

</div>
