<a id="erdos-251-prime-gap-dyadic-series"></a>

# A Denominator Floor and a Free-Pair Criterion for the Prime-Gap Dyadic Series

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Let $`p_0=2,p_1=3,\ldots`$ enumerate the primes, let $`g_n=p_{n+1}-p_n`$, and write
``` math
\Pi=\sum_{i\ge0}\frac{p_i}{2^{\,i+1}},\qquad
 S=\sum_{i\ge0}\frac{g_i}{2^{\,i+1}} .
```
Every rational number equal to $`\Pi`$, and hence every rational equal to $`S`$, has denominator at least $`2^{589}>10^{177}`$. That floor is decided inside the Lean kernel by `decide +kernel` on a single Boolean certificate over the $`1229`$ primes below $`10^{4}`$, in the module `Erdos251/KernelDenominatorFloor.lean` of the private development; that module lies outside the source revision pinned by this note, so the statement is quoted with its coordinate and without a link, and it is scheduled for the next governed build. An exact continued-fraction computation raises the floor to $`2^{39997}>10^{12040}`$: $`23369`$ partial quotients at a working scale of $`80000`$ bits, each forced by a rational bracket of width $`1`$ with the separation verified against that bracket, and with the tail controlled by the Lean-checked estimate $`p_n\le1250(n+1)^4`$ [the polynomial prime bound](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L360). That second step is an exact finite computation resting on a kernel-checked ingredient, and no Lean declaration carries it. Both bounds exclude an initial range of rationals and leave irrationality open.

The exact remaining input is a free-pair condition. Put $`T_N=2^{\,N+1}\bigl(S-\sum_{i\le N}g_i2^{-(i+1)}\bigr)`$, so that $`T_{N+1}=2T_N-g_{N+1}`$. Then $`S`$ is irrational if and only if for every modulus $`t\ge1`$ and every cutoff there are indices $`M\equiv N\pmod t`$ beyond the cutoff with $`T_M-T_N\notin\mathbb{Z}`$. The offset $`M-N`$ is free, so one nonintegral congruent pair per modulus and cutoff suffices in place of a supply at a single fixed offset. Beyond a rational state with odd reduced denominator $`d`$, integrality of $`T_M-T_N`$ holds precisely when $`M\equiv N`$ modulo the multiplicative order of $`2`$ in $`\mathbb{Z}/d\mathbb{Z}`$. The equivalence and that lattice statement are Lean theorems of the private module `Erdos251/FreePairReduction.lean`, also outside the pinned revision and also scheduled for the next governed build. The nearest located antecedent is Schlage-Puchta \[schlagepuchta2011\], whose Theorem 2 concerns periodic base-$`b`$ digit expansions and is a different object; the free-pair form is recorded as new at low confidence, with the dyadic tail-recurrence and Bézivin-style functional-equation sweep unrun.

The event the criterion consumes is measured in the actual primes. Over the $`6\,841\,648`$ primes below $`1.2\times10^{8}`$ and offsets $`h=1,\ldots,16`$ it occurs at every offset, with density between $`0.00418`$ and $`0.008248`$ and the two signs near balanced; at $`h=1`$ there are $`56\,427`$ occurrences, the last at the prime $`119\,995\,753`$. This is a finite measurement over one range and it supplies no cofinal statement. The narrowest sufficient prime-theoretic input recorded for the two-condition form is a pair of even numbers differing by $`2`$, each occurring infinitely often as a consecutive prime gap, inside a common index residue class modulo $`t`$.

Three proved boundaries constrain any argument. Raising every gap by at most $`M`$ while preserving its residue modulo $`M`$ and fixing any prescribed initial segment already makes the sum rational, so a hypothesis invariant under such perturbations cannot force irrationality ([the construction](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L163), [its invariant-property consequence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L179), and the prime-anchored instances at [lines 200](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L200) and [210](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L210)). Both block-pullback escape tests are proved equivalent to the conclusion they were introduced to supply ([the affine cylinder form](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/AffineCylinderCollapse.lean#L162) and [the fixed-lattice form](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/AffineCylinderCollapse.lean#L308)). The quadratic word $`g_n=2(n^2+4n+2)`$ has the rational value $`32`$ [by a checked telescope](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PolynomialGapSeriesValue.lean#L106), so positivity, parity, strict growth, unboundedness and nonperiodicity are jointly compatible with rationality. Its telescoping mechanism is the one Kovač used against the variable-denominator conjecture printed under the problem, published on 15 April 2026 \[kovac2026, Theorem 1 and proof, pp. 1–2\]; the word carries no priority claim and is not a result about Problem #251.

The reduction that carries the problem to the gap series is elementary and exact. The polynomial bound $`p_n\le1250(n+1)^4`$ gives summability of the prime and gap terms. Summation by parts, with the endpoint retained, yields
``` math
\sum_{i=0}^{n}\frac{p_i}{2^{\,i+1}}
 \;=\;2+\sum_{i=0}^{n-1}\frac{g_i}{2^{\,i+1}}-\frac{p_n}{2^{\,n+1}},
```
and therefore the unconditional identity and irrationality equivalence
``` math
\sum_{i\ge0}\frac{p_i}{2^{\,i+1}}
 =2+\sum_{i\ge0}\frac{g_i}{2^{\,i+1}},\qquad
 \operatorname{Irr}\!\left(\sum_{i\ge0}\frac{p_i}{2^{\,i+1}}\right)
 \Longleftrightarrow
 \operatorname{Irr}\!\left(\sum_{i\ge0}\frac{g_i}{2^{\,i+1}}\right).
```
This exact identity reduces Problem #251 to the dyadic gap series; it does not prove its irrationality.

For any real recurrence with integer digits,
``` math
T_{N+h}=2^hT_N-
 \bigl(g_{N+1}2^{h-1}+\cdots+g_{N+h}\bigr),
```
so $`T_{N+h}-T_N`$ is integral exactly when $`(2^h-1)T_N`$ is. Consequently, $`T_0`$ is rational if and only if one positive shift is integral at one index, equivalently if one fixed shift is eventually integral. Dually, $`T_0`$ is irrational exactly when every positive shift is nonintegral everywhere, equivalently when every fixed shift is nonintegral cofinally. If $`L_0=1`$ and $`L_j=\operatorname{lcm}(1,\ldots,j)`$, all shift lengths and basepoints collapse to the single diagonal criterion
``` math
\operatorname{Irr}(T_0)
 \quad\Longleftrightarrow\quad
 T_{2L_j}-T_{L_j}\notin\mathbb{Z}\quad\hbox{for every }j\ge0.
```
The missing step is to prove these nonintegralities for the actual prime-gap tails, and the free-pair form above is the weakest recorded shape of that step.

There is also an exact finite obstruction. Two adjacent $`h`$-shifts in $`(-1,1)`$ whose corresponding prime gaps differ cannot both be integral. Hence cofinally many such pairs would exclude eventual integrality [the conditional prime-gap small-mismatch theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1112). An explicit remainder bound certifies one actual adjacent pair at $`h=1`$, $`N=2`$; its cofinal occurrence is not proved. A second example has finite sum $`-n/2^n`$ and non-eventually-periodic coefficients ([finite endpoint](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1157); [coefficient nonperiodicity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1163)). The actual prime gaps are also not eventually periodic ([prime-gap nonperiodicity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1023)), and that fact alone is insufficient. Problem #251 remains open: the exact unproved input is cofinal nonintegrality in the free-pair form, or a prime-gap estimate strong enough to imply the adjacent-small-mismatch condition.

<div class="center">

<div class="minipage">

------------------------------------------------------------------------

**Denominator floor, exact criterion, and open boundary**

**Denominator floor.** Every rational equal to the prime series, and hence every rational equal to the prime-gap series, has denominator at least $`2^{589}>10^{177}`$ by a kernel-decided certificate, and at least $`2^{39997}>10^{12040}`$ by a certified continued-fraction prefix resting on a Lean-checked tail bound. **Exact criterion.** Irrationality is equivalent to a free-pair nonintegrality condition on the scaled tails, with the shift offset free. **Measured input.** The event that criterion consumes occurs at every tested offset over 6,841,648 primes; the narrowest sufficient prime-theoretic input recorded is a pair of even numbers differing by 2, each occurring infinitely often as a consecutive prime gap, inside a common index residue class. **Open boundary.** Bounded perturbations preserving every gap’s residue make the sum rational, both block-pullback escape tests are proved circular, and the polynomial word is a coarse-property countermodel citing Kovač. No result here proves cofinal nonintegrality for the actual prime gaps. **Reduction.** Summation by parts identifies the prime series with two plus the dyadic prime-gap series, and tail rationality is equivalent to one integral shift and to one diagonal lcm-tail integrality.

</div>

</div>

<a id="sec:problem"></a>

# Introduction

Let $`p_n`$ denote the $`n`$th prime. Erdős Problem #251 asks whether
``` math
\Pi=\sum_{n\ge1}\frac{p_n}{2^{\,n}}
```
is irrational \[erdos1958, p. 94\]\[erdosgraham1980, p. 62\] \[erdos1988, p. 103\]. Bloom’s catalogue records the problem as open \[erdosproblems\]. Numerically $`\Pi=2/2+3/4+5/8+7/16+11/32+\cdots=3.674643966\ldots`$.

Throughout the formal development the primes are indexed from zero, so that $`p^{(0)}_0=2`$, $`p^{(0)}_1=3`$, $`p^{(0)}_2=5`$, and the gaps are $`g_i=p^{(0)}_{i+1}-p^{(0)}_i`$. In that indexing
``` math
\Pi=\sum_{i\ge0}\frac{p^{(0)}_i}{2^{\,i+1}} ,
```
which is the convention every statement below uses; we drop the superscript from here on. The first values are
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
the [factor-of-two normalisation](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L111). A factor of two does not change rationality, so no result below depends on the choice; the identity is stated so that the indexing cannot drift silently.

<a id="notation."></a>

#### Notation.

$`\mathbb{N}=\{0,1,2,\ldots\}`$ and $`\mathbb{N}_{>0}=\{1,2,\ldots\}`$. We write $`\varphi`$ for Euler’s totient function, $`\operatorname{den}q`$ for the denominator of a rational number $`q`$ written in lowest terms, $`\operatorname{dist}(x,\mathbb{Z})`$ for the distance from a real number $`x`$ to the nearest integer, and $`\operatorname{Irr}(x)`$ for the assertion that $`x`$ is irrational. A rational number is called *integral* when it is the image of an integer. A sequence $`(a_n)`$ is *eventually periodic with period $`h\ge1`$* when $`a_{n+h}=a_n`$ for every sufficiently large $`n`$. A sum over an empty range of indices is zero.

<a id="relation-to-prior-work."></a>

#### Relation to prior work.

Erdős proved that $`\sum_n p_n^{k}/n!`$ is irrational for every $`k\ge1`$ \[erdos1958, p. 93\]. The 1958 article gives the $`k=1`$ proof on pp. 94–95 and says explicitly that the more complicated $`k>1`$ proof is omitted. On page 103 of his 1988 problem paper he separately stated the fixed-denominator problem: he could not prove that $`\sum_n p_n^{k}/2^{n}`$ is irrational for every $`k\ge1`$, and wrote that the case $`k=1`$ was probably already very difficult. He also stated the variable-denominator expectation that $`\sum_{n\ge1}p_n/(g_1\cdots g_n)`$ is irrational whenever $`g_n\ge2`$ and $`g_n=o(p_n)`$ \[erdos1988, p. 103\]. The latter expectation is false: Kovač reports a construction of such a sequence $`(g_n)`$ for which the sum is exactly $`1`$  \[kovac2026, Theorem 1 and proof, pp. 1–2\].

Under the stronger hypotheses that $`(g_n)`$ is strictly increasing and $`g_n=O(n\log^k n)`$, Erdős had already classified the rational cases: rationality holds exactly when $`g_n=q p_n+1`$ eventually for one fixed integer $`q\ge1`$ \[erdos1958, pp. 96–99\]. The endpoint $`q=1`$ is included: if $`G_n=\prod_{j=1}^{n}(p_j+1)`$, then $`p_n/G_n=1/G_{n-1}-1/G_n`$, so the corresponding series telescopes to $`1`$. The counterexample evades those hypotheses. It does not address the fixed-denominator dyadic series studied here. The current catalogue record still repeats this variable-denominator expectation without mentioning the counterexample \[erdosproblems\]. Its warning that relevant literature may be missing applies directly to this omission.

There is also a genuinely adjacent proved dyadic theorem. If $`P(m)`$ denotes the largest prime factor of $`m`$, Erdős and Pomerance proved that
``` math
\sum_{m\ge2}\frac{\mathbf 1_{\{P(m)>P(m+1)\}}}{2^m}
```
is irrational \[erdospomerance1978, §7, p. 320\]. Erdős and Graham record the complementary indicator on p. 62: equality of the two largest prime factors is impossible for consecutive integers, so its series is $`1/2`$ minus the displayed one and is irrational as well. This is a theorem about a bounded prime-factor comparison digit sequence, not the unbounded prime numerators in $`\Pi`$; it supplies nearby positive evidence without solving Problem #251.

Problem #251 also appears as the unproved declaration `erdos_251` in the *Formal Conjectures* repository \[formalconjectures251\]. Its zero-based Lean sum starts with the zeroth prime over $`2^0`$, so it is twice the displayed normalisation and has equivalent irrationality status, but it is not literally the same indexing; its proof is `sorry`.

<a id="the-strategy."></a>

#### The strategy.

The digits $`p_n`$ grow, so the series is not a digit expansion in any bounded alphabet, and the standard rationality criteria for such expansions do not apply directly. The classical elementary criteria for series of this kind instead control irrationality through the growth of the denominators. Erdős and Straus named a sum $`\sum_k 1/a_k`$ over a strictly increasing sequence of positive integers an *Ahmes series* \[erdosstraus1963\]; for such a series the condition $`a_k^{1/2^k}\to\infty`$ is sufficient for irrationality, and it is sharp, since shifted Sylvester sequences grow like $`C^{2^{k}}`$ for arbitrarily large $`C`$ and have rational reciprocal sum. Both statements and their attribution are recorded in the introduction of Kovač and Tao \[kovactao2024, §1\], who develop the elementary technology for such series much further. Splitting each term $`p_i/2^{\,i+1}`$ into $`p_i`$ copies of $`2^{-(i+1)}`$ writes $`\Pi`$ as a sum of unit fractions, but with repetitions, and the denominators occurring in it are exactly the powers of two. Even ignoring the repetitions the growth hypothesis fails by every available margin, since $`(2^{\,n})^{1/2^{\,n}}\to1`$, and every arithmetic constraint has to come from the numerators instead.

What replaces growth control is denominator control on the sequence of rescaled tails. Rationality of the sum turns out to be equivalent to an eventual integrality condition on differences of those tails, and that condition uses nothing about the numerators beyond the fact that they are integers. The condition does not by itself force the numerators to repeat: Proposition <a href="#res:telescope" data-reference-type="ref" data-reference="res:telescope">23</a>, applied to $`K_n=n`$, produces the integer sequence $`\kappa_n=n-1`$, which is unbounded and hence not eventually periodic, and whose dyadic sum $`\sum_{n\ge0}\kappa_n2^{-(n+1)}`$ is zero.

<a id="outline."></a>

#### Outline.

Section <a href="#sec:denominator-floor" data-reference-type="ref" data-reference="sec:denominator-floor">2</a> records the two denominator exclusions, the free-pair criterion that is equivalent to the target, the measurement of the event that criterion consumes, and the exact remaining prime-theoretic obligation. Section <a href="#sec:diagonal-collapse" data-reference-type="ref" data-reference="sec:diagonal-collapse">3</a> then gives the strongest exact recurrence-level conclusions: the lcm-diagonal irrationality criterion, the signed two-window normal form, the affine and fixed-lattice circularity equivalences, and the quadratic polynomial-shift countermodel. Section <a href="#sec:parts" data-reference-type="ref" data-reference="sec:parts">4</a> then replaces the primes by their consecutive gaps, the natural increments studied by prime-distribution theory. Summation by parts with the endpoint retained gives an exact finite identity, and the termwise relation $`v_n=2u_{n+1}-u_n`$ between the gap terms and the prime terms makes the passage to the limit a matter of summability alone; the explicit polynomial prime bound supplies that summability inside the formal development.

Section <a href="#sec:tail" data-reference-type="ref" data-reference="sec:tail">5</a> rescales the tails of a dyadic series into a recurrence and develops it: the block identity, the integral-shift criterion, the collapse of every rational solution onto an eventually integral shift, its contrapositive over the reals, and a local obstruction that converts an infinite-tail condition into a single comparison of gaps. Section <a href="#sec:carry" data-reference-type="ref" data-reference="sec:carry">6</a> shows that the tail constraint does not by itself make the coefficient sequence eventually periodic, and Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">7</a> states the remaining obligation. The pinned Lean 4 toolchain and Mathlib revision check the formal statements. The cited system paper identifies Lean 4 \[lean4, abstract and §1, pp. 625–626\], while the Mathlib paper documents the library’s historical Lean 3-era architecture \[mathlib, abstract and §1.1, p. 367\]; it is not authority for the current pinned revision. Linked phrases open the corresponding declaration at the pinned source revision 4ab50e144847.

The [unbounded-gap theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L57) states $`\forall M:\mathbb N,\ \exists n,\ M<\mathit{primeGap0}(n)`$, and the [prime/gap irrationality equivalence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L435) states, under $`\operatorname{Summable}(\mathit{primeDyadicTerm})`$, the equivalence between irrationality of the prime-term and prime-gap-term sums. The endpoint-proximate abstract classification is represented by [the pointwise shift classifier](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1551): for any real dyadic-tail recurrence with integer digits, irrationality of the initial state is equivalent to non-integrality of every positive shift, and hence to cofinal non-integrality of each fixed shift. Its rational-side mechanism is the exact denominator/congruence pair [denominator divisibility](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1279) and [power-of-two congruence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1291); together with the [eventual-integrality classifier](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1525), they explain why a rational initial state supplies an eventual integral shift. These are recurrence-level results; the cofinal nonintegrality property for the actual prime gaps remains unproved, so no irrationality claim for Problem #251 follows. The endpoint-adjacent specialisation [the conditional prime-gap small-mismatch theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1112) preserves the actual recurrence, the cofinal adjacent $`(-1,1)`$ hypotheses, and the unequal gap condition, and concludes failure of eventual integrality. The source does not supply those pairs, so this is a reduction exposing the missing prime-specific estimate.

*Status.* The original problem remains open. Statements marked as Lean-checked refer to the linked propositions accepted by the pinned kernel, with no `sorry`, added axioms, or unchecked evaluation. The note states the remaining mathematical obligations explicitly.

*Companion system context.* The [claim and trust boundary](../../../claim-faithful-publication-systems-paper.pdf#systems-trust), [cold-clone route to proof authority](../../../cold-clone-to-proof-receipt.pdf#cold-clone-authority), and [public contribution protocol](../../../open-source-mathematics-strategy.pdf#strategy-protocol) are described in sibling papers.

| Statement | Status | Treatment here |
|:---|:---|:---|
| Irrationality of $`\Pi`$ | Open | Not proved. |
| Denominator floor $`b\ge2^{589}`$ for every rational value | Lean-checked in the private development; outside the pinned source | Theorem <a href="#res:denominatorfloor" data-reference-type="ref" data-reference="res:denominatorfloor">1</a>; kernel-decided certificate. |
| Certified continued-fraction exclusion $`q>10^{12040}`$ | Exact computation over a Lean-checked tail bound | Theorem <a href="#res:cfexclusion" data-reference-type="ref" data-reference="res:cfexclusion">2</a>; no Lean declaration. |
| Free-pair irrationality criterion | Lean-checked in the private development; outside the pinned source; an equivalence | Theorem <a href="#res:freepair" data-reference-type="ref" data-reference="res:freepair">3</a>. |
| Actual real prime-gap tail recurrence and escape equivalence | Lean-checked unconditionally | Used in Theorem <a href="#res:freepair" data-reference-type="ref" data-reference="res:freepair">3</a>. |
| Adjacent-mismatch event in the actual primes | Finite measurement | Density over 6,841,648 primes; supplies no cofinal statement. |
| State compression and redundancy of the gap condition | Ordinary proof; not formalised | Recorded after Theorem <a href="#res:freepair" data-reference-type="ref" data-reference="res:freepair">3</a>. |
| Polignac-pair sufficient input | Proposed sufficient theorem | Not proved. |
| Lcm-diagonal irrationality criterion | Lean-checked abstractly; an equivalence | Theorem <a href="#res:lcmdiagonal" data-reference-type="ref" data-reference="res:lcmdiagonal">4</a>. |
| Signed two-window normal form | Lean-checked abstractly; an equivalence | Theorem <a href="#res:signedwindow" data-reference-type="ref" data-reference="res:signedwindow">5</a>. |
| Affine and fixed-lattice cofinal escape tests | Lean-checked abstractly; both equivalences | Theorem <a href="#res:affinecollapse" data-reference-type="ref" data-reference="res:affinecollapse">6</a>; neither supplies a prime-specific estimate. |
| Quadratic polynomial-shift countermodel | Lean-checked | Proposition <a href="#res:polynomialcountermodel" data-reference-type="ref" data-reference="res:polynomialcountermodel">8</a>. |
| Finite prime-gap identity | Proved here | Theorem <a href="#res:parts" data-reference-type="ref" data-reference="res:parts">10</a>, with the endpoint retained. |
| Infinite prime-gap identity | Lean-checked unconditionally | Theorem <a href="#res:infinite" data-reference-type="ref" data-reference="res:infinite">11</a>, with summability discharged by the polynomial prime bound. |
| Prime-series/gap-series irrationality equivalence | Lean-checked unconditionally | Corollary <a href="#res:irr-equivalence" data-reference-type="ref" data-reference="res:irr-equivalence">12</a>. |
| Block identity for the tail recurrence | Proved here | Theorem <a href="#res:block" data-reference-type="ref" data-reference="res:block">14</a>. |
| Integral shift criterion | Proved here; an equivalence | Theorem <a href="#res:shiftiff" data-reference-type="ref" data-reference="res:shiftiff">15</a>. |
| Totient shift from an odd denominator | Proved here | Theorem <a href="#res:totient" data-reference-type="ref" data-reference="res:totient">16</a>. |
| Propagation of an integral shift | Proved here | Theorem <a href="#res:propagate" data-reference-type="ref" data-reference="res:propagate">17</a>. |
| Eventual integral shift for every rational-valued recurrence | Lean-checked | Theorem <a href="#res:collapse" data-reference-type="ref" data-reference="res:collapse">18</a>. |
| Rationality/integral-shift classification | Lean-checked abstractly; an equivalence | Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">19</a>. |
| Finite-approximation gap | Paper-level | Elementary inference used in Proposition <a href="#res:truncation" data-reference-type="ref" data-reference="res:truncation">27</a>; not a named Lean declaration at the pinned revision. |
| Actual prime gaps are unbounded and not eventually periodic | Lean-checked | Proposition <a href="#res:gap-nonperiodic" data-reference-type="ref" data-reference="res:gap-nonperiodic">22</a>. |
| Adjacent small-mismatch pair excludes simultaneous integrality | Lean-checked | Theorem <a href="#res:smallpair" data-reference-type="ref" data-reference="res:smallpair">20</a>. |
| Concrete prime-gap tail recurrence and rational-candidate bridge | Lean-checked | The actual real tail satisfies the recurrence unconditionally; the rational-candidate representation of that tail assumes non-irrationality. |
| Rationality alone forces periodic integer coefficients | False | Section <a href="#sec:carry" data-reference-type="ref" data-reference="sec:carry">6</a>, Proposition <a href="#res:telescope" data-reference-type="ref" data-reference="res:telescope">23</a>. |
| Cofinal adjacent small-mismatch hypothesis | Proposed sufficient theorem | Problem <a href="#prob:smallpair" data-reference-type="ref" data-reference="prob:smallpair">26</a>; not proved. |

**Keywords.** irrationality; prime gaps; dyadic series; summation by parts; Lean 4. **MSC 2020.** 11J72 (primary); 11N05, 68V20 (secondary).

<a id="sec:denominator-floor"></a>

# A denominator floor, and the exact remaining input

The strongest statements available on this problem restrict the answer itself. Both are exclusions of rational values, and both leave irrationality open.

<div id="res:denominatorfloor" class="theorem">

**Theorem 1** (kernel-decided denominator floor). *Let $`a\in\mathbb{Z}`$ and $`b\in\mathbb{N}_{>0}`$. If $`\Pi=a/b`$ then $`b\ge2^{589}`$, and the same floor holds for every rational equal to $`S`$, because $`\Pi=2+S`$.*

</div>

*Evidence.* The statement is a Lean theorem in the private development, `kernel_denominator_floor` and `kernel_denominator_floor_primeGap` at lines $`315`$ and $`323`$ of `ErdosProblems/Erdos251/KernelDenominatorFloor.lean`. Its arithmetic core is one Boolean certificate over the $`1229`$ primes below $`10^{4}`$, accepted by `decide +kernel` at line $`309`$, with four Farey literals of $`175`$ to $`181`$ digits and no `native_decide`. Its analytic input is a rational bracket around $`\Pi`$ built from the partial sum through the $`1229`$th prime together with the polynomial tail estimate, the same estimate proved at [line 360 of the prime-gap module](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L360). That module is absent from the source revision pinned by this note, so no link is printed for it and no reader is asked to accept the statement on the pinned revision; it is scheduled for the next governed build. Since $`589\log_{10}2>177`$, the floor exceeds $`10^{177}`$.

<div id="res:cfexclusion" class="theorem">

**Theorem 2** (certified continued-fraction exclusion). *Every rational equal to $`\Pi`$, and hence every rational equal to $`S`$, has reduced denominator $`q\ge2^{39997}`$, and therefore $`q>10^{12040}`$.*

</div>

*Evidence.* This is an exact finite computation and no Lean declaration carries it. The continued-fraction expansion of $`\Pi`$ is developed to $`23369`$ partial quotients at a working scale of $`80000`$ bits. Each quotient is forced by a rational bracket of width $`1`$ around the true value, and the separation $`|q_n\Pi-p_n|>0`$ is verified against that bracket, so the prefix is the true prefix rather than a floating-point reconstruction. The bracket uses the Lean-checked tail estimate $`p_n\le1250(n+1)^4`$, so no conjecture enters. The classical theorem that a best approximation of the second kind is a convergent then converts the certified prefix into the denominator bound \[khinchin1964\]. The receipt is `state/formal_math/probes/erdos251_certified_cf_receipt.json`, which records the power-of-two exponent $`39997`$, the bit length $`39998`$, the strict decimal power $`12040`$, and the decimal digit count $`12041`$. The certified statement is $`q\ge2^{39997}`$ and $`q>10^{12040}`$. Printing the bit length or the digit count as an exponent overstates the bound by one power of two and one decimal order, and raising the printed exponent does not strengthen the proof.

Neither bound decides the problem. An exact criterion does.

<div id="res:freepair" class="theorem">

**Theorem 3** (free-pair criterion). *Let $`T_N=2^{\,N+1}\bigl(S-\sum_{i\le N}g_i2^{-(i+1)}\bigr)`$, so that $`T_{N+1}=2T_N-g_{N+1}`$ and $`T_0=2S-1`$. Then $`S`$ is irrational if and only if for every $`t\ge1`$ and every $`N_0`$ there are $`N,M\ge N_0`$ with $`M\equiv N\pmod t`$ and $`T_M-T_N\notin\mathbb{Z}`$.*

</div>

The offset $`M-N`$ is free, so one nonintegral congruent pair for each modulus and each cutoff suffices. The mechanism is exact: beyond a rational state with odd reduced denominator $`d`$, the difference $`T_M-T_N`$ is integral precisely when $`M\equiv N`$ modulo the multiplicative order of $`2`$ in $`\mathbb{Z}/d\mathbb{Z}`$, so every rational orbit has a cutoff and a modulus $`t`$ at which integrality holds exactly on the congruence classes.

*Evidence.* The equivalence, the lattice statement and the unconditional recurrence for the actual prime-gap tail are Lean theorems at lines $`236`$, $`92`$ and $`186`$ of `ErdosProblems/Erdos251/FreePairReduction.lean` in the private development. That module is also absent from the pinned formal source and is also scheduled for the next governed build. The unconditional recurrence for the actual real tail is available at the pinned revision, [the real prime-gap tail recurrence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L48), together with the fixed-offset escape equivalence [for the actual prime series](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L73), so the passage from the free-pair form to the fixed-offset form is checked here and only the free-offset lattice waits on the next build. The nearest located antecedent for the free-pair form is Schlage-Puchta \[schlagepuchta2011\], whose Theorem 2 treats periodic base-$`b`$ digit expansions and is a different object; the form is recorded as new at low confidence, and the sweep of the dyadic tail-recurrence and Bézivin-style functional-equation literature has not been run.

<a id="what-is-measured."></a>

#### What is measured.

Over the $`6\,841\,648`$ primes below $`1.2\times10^{8}`$ and offsets $`h=1,\ldots,16`$, the reduced event occurs at every offset, with density between $`0.00418`$ and $`0.008248`$ and the two signs near balanced; at $`h=1`$ there are $`56\,427`$ occurrences, the last at the prime $`119\,995\,753`$. Rescaled by $`\log p`$, the band densities run from $`0.17671`$ down to $`0.13148`$ with decelerating drift, so the count up to $`X`$ still grows like $`X/(\log X)^2`$. Of $`3\,200`$ sampled hits across $`h=1,\ldots,8`$, every one satisfies the condition as literally stated, and the median distance to a window boundary is $`0.127`$ against a worst case of $`6.1\times10^{-7}`$. This is a finite measurement over one range and it supplies no cofinal statement. The receipt is `state/formal_math/probes/erdos251_adjacent_mismatch_receipt.json`.

<a id="two-consequences-of-the-criterion-proved-on-paper."></a>

#### Two consequences of the criterion, proved on paper.

Two further statements about the criterion are ordinary proofs recorded in the private development, and neither is formalised. First, exchanging the order of summation gives $`\sum_{N\le X}T_N\le(p_{X+1}-p_0)+2T_X`$. Under rationality with reduced odd denominator $`d`$, Markov’s inequality supplies for each $`C>1`$ a set $`B\subseteq(X,2X]`$ of density at least $`1-1/C`$ on which $`T_N\le C\log p_{2X}`$; on that set $`T_N`$ lies in $`\tfrac1d\mathbb{Z}`$ and takes at most $`dC\log p_{2X}+1`$ values, so some single value is attained $`\gg X/\log X`$ times. Rationality therefore makes the tail a finite-state object at every scale, pairs with $`T_M=T_N`$ are abundant for free, and the whole difficulty in the free-pair producer is the nonintegrality of the difference. Second, under the free-pair lattice the difference $`T_M-T_N`$ is an integer whenever the modulus divides the offset, and an integer cannot lie in $`(\tfrac12,1)`$, so the first component of the reduced event is already a contradiction and the gap condition adds nothing to it. Both derivations were read and found sound by an internal audit. Neither is Lean-checked, neither carries an independent check, and the naive form $`\sum_{N\le X}T_N\le p_{X+1}`$ is false.

<a id="the-exact-remaining-obligation."></a>

#### The exact remaining obligation.

Call an even number a *Polignac number* when it occurs infinitely often as a difference of consecutive primes. The narrowest sufficient prime-theoretic input recorded for the two-condition form of the event is a pair of Polignac numbers differing by $`2`$, both realised infinitely often inside a common index residue class modulo $`t`$, for every $`t`$. That is weaker than a Hardy-Littlewood correlation at a fixed offset, and it sits beside bounded-gap technology. Whether it follows from known results is open, and nothing here proves any case of it.

<a id="sec:diagonal-collapse"></a>

# One diagonal, and two circular escape tests

We first record the strongest recurrence-level conclusions. They apply to arbitrary integer digits and therefore separate the finite algebra from the prime-specific input still missing in Problem #251.

For a real recurrence put
``` math
\Delta_hT(N)=T_{N+h}-T_N,
```
and let $`L_0=1`$, $`L_j=\operatorname{lcm}(1,\ldots,j)`$ for $`j\ge1`$.

<div id="res:lcmdiagonal" class="theorem">

**Theorem 4** ([lcm-diagonal criterion](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/OrderLatticeDiagonal.lean#L153)). *Let $`g:\mathbb{N}\to\mathbb{Z}`$ and $`T:\mathbb{N}\to\mathbb{R}`$ satisfy $`T_{N+1}=2T_N-g_{N+1}`$ for every $`N`$. Then
``` math
\operatorname{Irr}(T_0)
 \quad\Longleftrightarrow\quad
 \Delta_{L_j}T(L_j)\notin\mathbb{Z}
 \quad\hbox{for every }j\ge0.
```*

</div>

<div class="proof">

*Proof.* The exact rationality classification proved in Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">19</a> says that an irrational initial state has no integral positive shift at any basepoint. This gives the forward implication. Conversely, if $`T_0`$ is rational, some positive shift length $`h`$ is integral at every basepoint beyond an index $`N_0`$. Choose $`j`$ so large that $`N_0\le L_j`$ and $`h\mid L_j`$. The cocycle identity
``` math
\Delta_{a+b}T(N)=\Delta_aT(N)+\Delta_bT(N+a)
```
shows by induction that every positive multiple of $`h`$ is integral at every such basepoint. Hence $`\Delta_{L_j}T(L_j)`$ is integral, contradicting the right-hand side. ◻

</div>

The factorial schedule $`j!`$ has the same divisibility property, but the lcm schedule is pointwise no larger and is the canonical endpoint used here. The theorem is an exact one-sequence reformulation; it gives no non-integrality statement for the actual prime-gap recurrence.

The adjacent-small-mismatch condition also admits an exact normal form. For a rational recurrence and a fixed $`h`$, write
``` math
D_N=\Delta_hT(N),\qquad
 \delta_N=g_{N+h+1}-g_{N+1}.
```
Then $`D_{N+1}=2D_N-\delta_N`$.

<div id="res:signedwindow" class="theorem">

**Theorem 5** ([signed two-window normal form](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/AffineShiftEscape.lean#L113)). *Assume that $`\delta_N`$ is even. The conjunction
``` math
-1<D_N<1,\qquad -1<D_{N+1}<1,\qquad \delta_N\ne0
```
is equivalent to
``` math
\bigl(\delta_N=2\ \hbox{ and }\tfrac12<D_N<1\bigr)
 \quad\hbox{or}\quad
 \bigl(\delta_N=-2\ \hbox{ and }-1<D_N<-\tfrac12\bigr).
```*

</div>

<div class="proof">

*Proof.* The recurrence and the two unit windows give $`-3<\delta_N<3`$. A nonzero even integer in that interval is $`2`$ or $`-2`$. Substitution into $`D_{N+1}=2D_N-\delta_N`$ gives the stated half-window and, in the reverse direction, recovers the second unit window. ◻

</div>

For the longer block, set
``` math
B_{h,N,r}=\sum_{i=0}^{r-1}2^{r-1-i}\delta_{N+i};
 \qquad D_{N+r}=2^rD_N-B_{h,N,r}.
```
Call the data-dependent affine condition
``` math
\mathcal A_{N,r}:\qquad
 D_{N+r}\in -B_{h,N,r}+2^{r+1}\mathbb{Z}.
```

<div id="res:affinecollapse" class="theorem">

**Theorem 6** (affine and fixed-lattice circularity). *For every rational dyadic tail recurrence and all $`h,N,r\ge0`$,
``` math
\mathcal A_{N,r}\quad\Longleftrightarrow\quad D_N\in2\mathbb{Z}.
\tag{2.1}\label{eq:affinecollapse}
```
Consequently, if every $`\delta_N`$ is even, then
``` math
\bigl(\forall N_0\ \exists N,r:\ N_0<N\text{ and }\neg\mathcal A_{N,r}\bigr)
 \quad\Longleftrightarrow\quad
 D_N\notin\mathbb{Z}\text{ for arbitrarily large }N.
\tag{2.2}\label{eq:affinecofinal}
```*

*There is a second equivalence. Let $`b:\mathbb{N}\to\mathbb{Q}`$ satisfy $`|D_N|\le b(N)`$ for every $`N`$, and suppose that for every $`N`$ and every positive integer $`q`$ there is an $`r`$ with
``` math
2b(N+r)q<2^r.
\tag{2.3}\label{eq:dyadicscale}
```
Then
``` math
\begin{split}
 &\forall N_0\ \exists N,r:\ N_0<N\text{ and }
   \forall z\in\mathbb{Z},\quad
   b(N+r)<|B_{h,N,r}-2^rz|\\
 &\hspace{35mm}\Longleftrightarrow\quad
 D_N\notin\mathbb{Z}\text{ for arbitrarily large }N.
 \end{split}
\tag{2.4}\label{eq:fixedcollapse}
```*

</div>

<div class="proof">

*Proof.* Substituting $`D_{N+r}=2^rD_N-B_{h,N,r}`$ into $`\mathcal A_{N,r}`$ cancels the observed block from both sides and leaves $`D_N=2z`$. This proves <a href="#eq:affinecollapse" data-reference-type="eqref" data-reference="eq:affinecollapse">[eq:affinecollapse]</a>. After one recurrence step, evenness of $`\delta_N`$ identifies even integrality at $`N+1`$ with ordinary integrality at $`N`$. The forward implication in <a href="#eq:affinecofinal" data-reference-type="eqref" data-reference="eq:affinecofinal">[eq:affinecofinal]</a> follows, while the reverse implication chooses a nonintegral $`D_N`$ and the legal depth $`r=0`$.

For <a href="#eq:fixedcollapse" data-reference-type="eqref" data-reference="eq:fixedcollapse">[eq:fixedcollapse]</a>, eventual integrality and the block identity give some $`z\in\mathbb{Z}`$ with
``` math
B_{h,N,r}-2^rz=-D_{N+r},
```
so the displayed strict separation contradicts $`|D_{N+r}|\le b(N+r)`$. Conversely, if $`D_N`$ is nonintegral and has reduced denominator $`q`$, then its distance from every integer is at least $`1/q`$. Choose $`r`$ from <a href="#eq:dyadicscale" data-reference-type="eqref" data-reference="eq:dyadicscale">[eq:dyadicscale]</a>, scale this separation by $`2^r`$, and use the block identity together with $`|D_{N+r}|\le b(N+r)`$. The triangle inequality gives $`|B_{h,N,r}-2^rz|>b(N+r)`$ for every integer $`z`$. ◻

</div>

The formal argument gives the [pointwise affine identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/AffineCylinderCollapse.lean#L91), its [cofinal form](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/AffineCylinderCollapse.lean#L162), and the [fixed-lattice equivalence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/AffineCylinderCollapse.lean#L308). The first equivalence shows that the apparent affine hierarchy contains no depth-dependent information: it is the pullback of even integrality through the recurrence identity. The fixed lattice removes that data dependence, but under the stated growth condition rational denominator separation already forces every required escape. Hence neither cofinal condition is an independent source of information about consecutive primes.

Finally, the coarse coefficient profile itself has an exact infinite counterexample.

<a id="a-bounded-perturbation-can-change-rationality"></a>

## A bounded perturbation can change rationality

<div id="res:boundedperturbation" class="theorem">

**Theorem 7** (bounded-perturbation obstruction). *Suppose $`g_n`$ are natural numbers and $`\sum_{n\ge0}g_n/2^{n+1}`$ converges. For every integer $`M>0`$ and cutoff $`K`$, there are digits $`\delta_n\in\{0,1\}`$, zero for $`n<K`$, such that $`\sum_{n\ge0}(g_n+M\delta_n)/2^{n+1}`$ is rational.*

</div>

Choose a rational value just above the original sum and use the binary expansion of their difference, scaled by $`M`$, beyond the prescribed prefix. The [construction](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L163) and its [invariant-property consequence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L179) are kernel checked: a property shared by every admissible perturbation cannot by itself force irrationality. The perturbed digits need not remain prime gaps. The construction is also checked at the actual consecutive prime gaps, [a rational perturbed prime-gap series](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L200) for every $`M\ge1`$ and every cutoff $`K`$, with the perturbed gap lying in $`[g_n,g_n+M]`$ and congruent to $`g_n`$ modulo $`M`$ ([the gap bounds](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L220)). Consequently no theorem about the size or the residue of prime gaps that survives such a perturbation can suffice for Problem #251; that class includes the bounded-gap and large-gap theorems cited below and equidistribution of $`p_n`$ modulo any fixed $`q`$, on taking $`M=2q`$.

<div id="res:polynomialcountermodel" class="proposition">

**Proposition 8** (quadratic polynomial-shift countermodel). *Put
``` math
g_n=2(n^2+4n+2),\qquad T_n=2(n+4)^2.
```
Then $`g_n`$ is positive, even and strictly increasing, $`T_{n+1}=2T_n-g_{n+1}`$, every shift $`T_{N+h}-T_N`$ is integral, and
``` math
g_{N+2}-g_{N+1}\ne2,-2
 \qquad\hbox{for every }N.
```*

</div>

<div class="proof">

*Proof.* All assertions are checked directly. The displayed recurrence is [the exact tail recurrence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1596). The identity $`g_{n+1}-g_n=4n+10`$ gives [strict monotonicity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1632), and hence unboundedness and nonperiodicity; it also yields [the exclusion of both adjacent triggers](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1644). Finally, [every fixed tail shift is integral](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1654). ◻

</div>

The telescoping mechanism behind this word is the one Kovač used against the variable-denominator conjecture printed under the problem, published on 15 April 2026 \[kovac2026, Theorem 1 and proof, pp. 1–2\]. The word carries no priority claim, and it is recorded here as a countermodel to a class of strategies rather than as a result about Problem #251.

The corresponding dyadic series has value exactly $`32`$, as shown by the [checked rational-value theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PolynomialGapSeriesValue.lean#L89).

The formal construction checks the [recurrence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1596), [strict growth](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1632), [integrality of every shift](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1654), and [exclusion of adjacent differences of size two](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1644).

<a id="sec:parts"></a>

# Summation by parts, with the endpoint retained

Summation by parts trades a sequence for its consecutive differences. The form recorded here is exact: it carries no error term, it assumes nothing about the sequence, and it retains the endpoint term rather than absorbing it into an estimate. For a sequence $`P`$ of rational numbers and $`n\ge0`$ put
``` math
D(P,n)=\sum_{i=0}^{n-1}\frac{P(i)}{2^{\,i+1}},
 \qquad
 \Delta(P,n)=\sum_{i=0}^{n-1}\frac{P(i+1)-P(i)}{2^{\,i+1}} ,
```
both empty, hence zero, at $`n=0`$. We call these the [dyadic partial sum](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L101) and the [dyadic difference sum](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L121) of $`P`$.

<div id="res:abel" class="proposition">

**Proposition 9** (finite summation by parts). *For every rational sequence $`P`$ and every $`n\ge0`$,
``` math
D(P,n+1)=P(0)+\Delta(P,n)-\frac{P(n)}{2^{\,n+1}} .
```*

</div>

<div class="proof">

*Proof.* A routine induction on $`n`$. At $`n=0`$ both sides equal $`P(0)/2`$. For the step, adding $`P(n+1)/2^{\,n+2}`$ to the left and $`\bigl(P(n+1)-P(n)\bigr)/2^{\,n+1}`$ to the difference sum changes the endpoint term from $`P(n)/2^{\,n+1}`$ to $`P(n+1)/2^{\,n+2}`$, and the two adjustments agree. ◻

</div>

Formalised as the [summation-by-parts identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L138). Nothing is assumed about $`P`$: no positivity, no monotonicity, and no convergence.

Specialising to $`P(i)=p_i`$, whose first value is $`p_0=2`$, and writing $`g_i=p_{i+1}-p_i`$ for the zero-based gaps, gives the reformulation.

<div id="res:parts" class="theorem">

**Theorem 10** (prime-gap reformulation). *Let $`p_0=2,p_1=3,\ldots`$ be the primes in increasing order and $`g_i=p_{i+1}-p_i`$. For every $`n\ge0`$,
``` math
\sum_{i=0}^{n}\frac{p_i}{2^{\,i+1}}
 =2+\sum_{i=0}^{n-1}\frac{g_i}{2^{\,i+1}}-\frac{p_n}{2^{\,n+1}} .
```*

</div>

Formalised as the [prime-gap summation by parts](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L172), using the [gap partial sum](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L161) and the [gap cast identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L156); the latter records that the natural-number difference $`p_{n+1}-p_n`$ agrees with the difference taken in $`\mathbb{Q}`$, which needs $`p_n\le p_{n+1}`$, the [monotonicity step](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L152). The leading $`2`$ is the first prime, not a normalising constant. At $`n=2`$, for instance, the left side is $`2/2+3/4+5/8=19/8`$ and the right side is $`2+(1/2+2/4)-5/8=19/8`$.

<a id="sec:infinite"></a>

## The infinite identity and the irrationality equivalence

Write
``` math
u_n=\frac{p_n}{2^{\,n+1}},\qquad
 v_n=\frac{g_n}{2^{\,n+1}}
```
for the terms of the prime series and of the gap series, so that $`\sum_{n\ge0}u_n=\Pi`$. The termwise identity $`v_n=2u_{n+1}-u_n`$ is the [dyadic discrete derivative](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L202). It expresses each gap term as an integer combination of two consecutive prime terms, so once $`(u_n)`$ is summable the gap series can be summed by rearranging two copies of the prime series, which is what the following proof does.

<div id="res:infinite" class="theorem">

**Theorem 11** (infinite prime-gap identity). *Let $`u_n=p_n/2^{\,n+1}`$ and $`v_n=g_n/2^{\,n+1}`$. If $`(u_n)`$ is summable, then $`(v_n)`$ is summable and
``` math
\sum_{n\ge0}u_n=2+\sum_{n\ge0}v_n .
```*

</div>

<div class="proof">

*Proof.* The shifted sequence $`(u_{n+1})`$ is summable. Sum $`v_n=2u_{n+1}-u_n`$ and use $`u_0=1`$:
``` math
\sum_{n\ge0}v_n
 =2\left(\sum_{n\ge0}u_n-u_0\right)-\sum_{n\ge0}u_n
 =\sum_{n\ge0}u_n-2 .
```
 ◻

</div>

The summability transfer is the [gap-series summability theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L385), and the displayed identity is the [infinite prime-gap identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L404).

<div id="res:irr-equivalence" class="corollary">

**Corollary 12** (exact irrationality reformulation). *With $`u_n`$ and $`v_n`$ as in Theorem <a href="#res:infinite" data-reference-type="ref" data-reference="res:infinite">11</a>, and $`(u_n)`$ summable,
``` math
\operatorname{Irr}\!\left(\sum_{n\ge0}u_n\right)
 \quad\Longleftrightarrow\quad
 \operatorname{Irr}\!\left(\sum_{n\ge0}v_n\right).
```
The corresponding zero-based series with denominator $`2^n`$ is $`4+2\sum_{n\ge0}v_n`$ and has the same irrationality status.*

</div>

These are the [normalised irrationality equivalence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L435), the [displayed-series identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L444), and the [displayed-series irrationality equivalence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L459).

<a id="the-summability-hypothesis."></a>

#### The summability hypothesis.

The formal source now proves the elementary polynomial bound $`p_n\le1250(n+1)^4`$, using prime counting and central-binomial growth, and deduces summability directly ([polynomial bound](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L360), [summability](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L379)). Thus Theorem <a href="#res:infinite" data-reference-type="ref" data-reference="res:infinite">11</a> and Corollary <a href="#res:irr-equivalence" data-reference-type="ref" data-reference="res:irr-equivalence">12</a> are now unconditional Lean-checked statements; the prime number theorem remains useful context but is no longer a proof dependency of this note. The open content is exactly irrationality of the prime-gap series. Concretely, $`\Pi=3.674643966\ldots`$ is irrational if and only if $`\sum_{n\ge0}g_n2^{-(n+1)}=1.674643966\ldots`$ is, and neither is known.

<a id="sec:tail"></a>

# The tail recurrence and integral shifts

The series is not attacked directly. Suppose $`\sum_{i\ge0}a_i2^{-(i+1)}`$ converges, with every $`a_i`$ an integer, and rescale its tails by putting
``` math
T_N=2^{\,N+1}\sum_{i>N}\frac{a_i}{2^{\,i+1}}
    =\sum_{j\ge1}\frac{a_{N+j}}{2^{\,j}} .
```
Two facts follow immediately. First $`T_{N+1}=2T_N-a_{N+1}`$, so moving one level along doubles the rescaled tail and subtracts a single coefficient. Second $`T_0=2\sum_{i\ge0}a_i2^{-(i+1)}-a_0`$, so the sum is rational exactly when $`T_0`$ is. The whole of Section <a href="#sec:tail" data-reference-type="ref" data-reference="sec:tail">5</a> therefore studies that recurrence in isolation, assuming nothing about the coefficients beyond the fact that they are integers; the prime-gap instance is resumed at the end of the section. The following definition is the object so obtained, stripped of its origin.

<div id="def:rec" class="definition">

**Definition 13**. Let $`g:\mathbb{N}\to\mathbb{Z}`$ and $`T:\mathbb{N}\to\mathbb{Q}`$. Say $`T`$ satisfies the *dyadic tail recurrence* with *digits* $`g`$ when
``` math
T_{N+1}=2T_N-g_{N+1}\qquad\text{for every }N .
```
We call the sequence $`(T_N)_{N\ge0}`$ the *orbit* of $`T_0`$ under $`g`$, write $`\sigma_h(N)=T_{N+h}-T_N`$ for the *shift* of length $`h`$ at $`N`$, and call a rational number *integral* when it is the image of an integer.

</div>

These are the [tail recurrence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L482), the [shift](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L544), and [integrality](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L575). The digits are arbitrary integers. In the intended instance they are the prime gaps and $`T_N`$ is the scaled tail of $`\Pi`$ after level $`N`$, but that instantiation needs a summability argument and is not made here; every statement below is a theorem about Definition <a href="#def:rec" data-reference-type="ref" data-reference="def:rec">13</a>.

One small orbit, referred to again below, is worth having in view. Take every digit $`g_N=0`$ and $`T_0=1/12`$. Then $`T_{N+1}=2T_N`$, so the orbit is $`\tfrac1{12},\tfrac16,\tfrac13,\tfrac23,\tfrac43,\ldots`$, and $`\sigma_h(N)=(2^{h}-1)2^{\,N}/12`$. The shift of length $`2`$ is not integral at $`N=0`$, where $`\sigma_2(0)=\tfrac13-\tfrac1{12}=\tfrac14`$, and is integral at $`N=2`$, where $`\sigma_2(2)=\tfrac43-\tfrac13=1`$; the shift of length $`1`$ is $`\sigma_1(N)=2^{\,N}/12`$ and is never integral. The change at $`N=2`$ is accounted for by Theorem <a href="#res:collapse" data-reference-type="ref" data-reference="res:collapse">18</a>, and the failure at $`h=1`$ by Theorem <a href="#res:shiftiff" data-reference-type="ref" data-reference="res:shiftiff">15</a>.

Iterating the recurrence $`h`$ times multiplies $`T_N`$ by $`2^{h}`$ and accumulates an explicit integer, which we now name. Define $`B_{0,N}=0`$ and $`B_{h+1,N}=2B_{h,N}+g_{N+h+1}`$, so that $`B_{h,N}=g_{N+1}2^{\,h-1}+\cdots+g_{N+h}`$: the [tail block](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L647). Thus $`B_{1,N}=g_{N+1}`$, $`B_{2,N}=2g_{N+1}+g_{N+2}`$ and $`B_{3,N}=4g_{N+1}+2g_{N+2}+g_{N+3}`$: the block puts the weights $`2^{\,h-1},\ldots,2^{0}`$ on the $`h`$ digits following index $`N`$.

<div id="res:block" class="theorem">

**Theorem 14** (block identity). *Let $`T:\mathbb{N}\to\mathbb{Q}`$ satisfy the dyadic tail recurrence with integer digits $`g`$, and let $`B_{h,N}`$ be as above. For every $`N`$ and $`h`$,
``` math
T_{N+h}=2^{h}T_N-B_{h,N},
 \qquad\text{hence}\qquad
 \sigma_h(N)=(2^{h}-1)\,T_N-B_{h,N} .
```*

</div>

<div class="proof">

*Proof.* A routine induction on $`h`$; the step is one application of the recurrence together with $`2\cdot2^{h}=2^{h+1}`$ and the recursion defining $`B`$. The second identity is the first minus $`T_N`$. ◻

</div>

Formalised as the [iterated block identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L653) and the [scaled shift identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L667). The shift also obeys the recurrence in its own right, $`\sigma_h(N+1)=2\sigma_h(N)-(g_{N+h+1}-g_{N+1})`$, the [shift step identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L563).

Since $`B_{h,N}`$ is an integer, Theorem <a href="#res:block" data-reference-type="ref" data-reference="res:block">14</a> converts a question about the shift into a question about the single scaled term $`(2^{h}-1)T_N`$.

<div id="res:shiftiff" class="theorem">

**Theorem 15** (integral-shift criterion). *Let $`T:\mathbb{N}\to\mathbb{Q}`$ satisfy the dyadic tail recurrence with integer digits $`g`$. For every $`N`$ and $`h`$, the shift $`\sigma_h(N)`$ is integral if and only if $`(2^{h}-1)T_N`$ is integral.*

</div>

<div class="proof">

*Proof.* By Theorem <a href="#res:block" data-reference-type="ref" data-reference="res:block">14</a> the two differ by the integer $`B_{h,N}`$, and subtracting an integer does not change integrality. ◻

</div>

Formalised as the [integral-shift criterion](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L802), on the [integer-shift invariance](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L677). This is an equivalence, not a one-way reduction: the block carries no information about integrality, so the two conditions are the same condition. Informally, once $`T_N`$ is fixed no choice of the digits after index $`N`$ can change whether the shift $`\sigma_h(N)`$ is an integer; that is decided by the denominator of $`T_N`$ alone.

The denominator criterion is exact:
``` math
\sigma_h(N)\in\mathbb{Z}
  \quad\Longleftrightarrow\quad
  \operatorname{den}(T_N)\mid 2^h-1.
\tag{3.4}\label{eq:shift-denominator}
```
This is the [denominator classification](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1279). Euler’s totient supplies one admissible shift length when the denominator is odd; it is a witness, not the classification itself.

<div id="res:totient" class="theorem">

**Theorem 16** (a shift of totient length). *Let $`T:\mathbb{N}\to\mathbb{Q}`$ satisfy the dyadic tail recurrence with integer digits $`g`$, and let $`\varphi`$ be Euler’s totient function. If the reduced denominator $`d`$ of $`T_N`$ is odd, then $`\sigma_{\varphi(d)}(N)`$ is integral.*

</div>

<div class="proof">

*Proof.* Since $`d`$ is odd, $`2`$ and $`d`$ are coprime, so Euler’s congruence gives $`2^{\varphi(d)}\equiv1\pmod d`$, that is $`d\mid 2^{\varphi(d)}-1`$. Writing $`2^{\varphi(d)}-1=dk`$ and $`T_N=u/d`$ in lowest terms, $`(2^{\varphi(d)}-1)T_N=ku`$ is an integer, and Theorem <a href="#res:shiftiff" data-reference-type="ref" data-reference="res:shiftiff">15</a> transfers this to the shift. ◻

</div>

Formalised as the [totient shift](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L877) and the [Euler multiplier](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L695). For example, if $`\operatorname{den}T_N=3`$ then $`\varphi(3)=2`$ and $`(2^{2}-1)T_N=3T_N`$ is an integer, so $`\sigma_2(N)`$ is integral, while $`(2^{1}-1)T_N=T_N`$ is not; if $`\operatorname{den}T_N=5`$ then $`\varphi(5)=4`$ and $`\sigma_4(N)`$ is integral.

The hypothesis is a genuine restriction: the argument uses coprimality of $`2`$ with the denominator, and the even part of a denominator is exactly what the doubling in the recurrence acts on. It cannot be dropped. If $`T_N=1/2`$ then $`2^{h}-1`$ is odd for every $`h\ge1`$, so $`(2^{h}-1)T_N`$ is never an integer and, by Theorem <a href="#res:shiftiff" data-reference-type="ref" data-reference="res:shiftiff">15</a>, no shift at $`N`$ is integral.

<div id="res:propagate" class="theorem">

**Theorem 17** (propagation). *Let $`T:\mathbb{N}\to\mathbb{Q}`$ satisfy the dyadic tail recurrence with integer digits $`g`$, and fix $`h`$ and $`N`$. If $`\sigma_h(N)`$ is integral, then $`\sigma_h(N+k)`$ is integral for every $`k\ge0`$.*

</div>

<div class="proof">

*Proof.* By the shift step identity, $`\sigma_h(N+1)=2\sigma_h(N)-(g_{N+h+1}-g_{N+1})`$ is an integer combination of an integer and two digits; induct on $`k`$. ◻

</div>

Formalised as the [one-step propagation](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L888) and the [propagation to every later index](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L900).

The three preceding theorems combine as follows, and this is the statement the rest of the note rests on. The special case is immediate: if $`\operatorname{den}T_0`$ is already odd, then Theorem <a href="#res:totient" data-reference-type="ref" data-reference="res:totient">16</a> at $`N=0`$ makes the shift of length $`\varphi(\operatorname{den}T_0)`$ integral and Theorem <a href="#res:propagate" data-reference-type="ref" data-reference="res:propagate">17</a> keeps it integral at every later index, so one may take $`N_0=0`$. In general a denominator carries a power of two as well, and the key point is that the doubling in the recurrence annihilates exactly the $`2`$-adic part of a denominator, and nothing else: after finitely many steps the orbit therefore reaches a term with odd reduced denominator, which is precisely the situation Theorem <a href="#res:totient" data-reference-type="ref" data-reference="res:totient">16</a> handles. No control of the digits is needed anywhere.

<div id="res:collapse" class="theorem">

**Theorem 18** (exact denominator dynamics and eventual integrality). *Let $`T:\mathbb{N}\to\mathbb{Q}`$ satisfy the dyadic tail recurrence with integer digits $`g`$ (Definition <a href="#def:rec" data-reference-type="ref" data-reference="def:rec">13</a>). Then some fixed positive shift is integral from some point onwards:
``` math
\exists h\ge1\ \exists N_0\ \forall N\ge N_0,\qquad
 \sigma_h(N)\in\mathbb{Z}.
```*

</div>

<div class="proof">

*Proof.* At every step the reduced denominator obeys the exact recurrence
``` math
\operatorname{den}(T_{N+1})
 =\frac{\operatorname{den}(T_N)}{\gcd(2,\operatorname{den}(T_N))}.
```
Thus each even denominator loses exactly one factor of $`2`$, while an odd denominator is unchanged. After finitely many steps the denominator is odd. Theorem <a href="#res:totient" data-reference-type="ref" data-reference="res:totient">16</a>, applied at that index $`s`$, supplies the positive shift $`h=\varphi(\operatorname{den}T_s)`$, and Theorem <a href="#res:propagate" data-reference-type="ref" data-reference="res:propagate">17</a> keeps that shift integral at every later index. ◻

</div>

The one-step formula is the [denominator recurrence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1217), with its [odd case](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1226) and [even case](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1236).

In the orbit displayed after Definition <a href="#def:rec" data-reference-type="ref" data-reference="def:rec">13</a> the proof runs as follows: $`\operatorname{den}T_0=12=2^{2}\cdot3`$, so $`s=2`$, the orbit reaches $`T_2=1/3`$ with odd denominator, and $`h=\varphi(3)=2`$. That is exactly the shift length seen to be integral there from index $`2`$ onwards, and no shorter one works.

Three features of the argument are used later. The proof may take as its number of preparatory steps the $`2`$-adic valuation of $`\operatorname{den}T_0`$. The resulting shift length $`h`$ is the totient of the odd denominator reached from a hypothetical rational initial value, and is not known in advance for the prime-gap orbit. This is why this argument requires Problem <a href="#prob:escape" data-reference-type="ref" data-reference="prob:escape">25</a> for every $`h`$, rather than for one preassigned shift length. Finally, the digits enter only through the integer $`B_{s,0}`$, so the conclusion holds for an arbitrary integer digit sequence.

In the current formal source, denominator factorisation and cancellation are packaged directly in the [fixed-denominator theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L830), and the quantified conclusion is the [eventual integral-shift theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L853) for the actual prime-gap tail state.

The useful contrapositive is stated for a real recurrence. Call its shifts *cofinally non-integral* when, for every fixed $`h\ge1`$ and every threshold $`N_0`$, some $`N\ge N_0`$ has $`\sigma_h(N)\notin\mathbb{Z}`$. This is precisely the negation of the conclusion of Theorem <a href="#res:collapse" data-reference-type="ref" data-reference="res:collapse">18</a>: no shift length whatever becomes integral and stays integral.

<div id="res:escape-irrational" class="theorem">

**Theorem 19** (exact rationality classification). *Let $`T:\mathbb{N}\to\mathbb{R}`$ satisfy $`T_{N+1}=2T_N-g_{N+1}`$ with integer $`g`$. If its shifts are defined by $`\sigma_h(N)=T_{N+h}-T_N`$, then the following are equivalent:*

1.  *$`T_0`$ is rational;*

2.  *$`\sigma_h(N)`$ is integral for some $`h\ge1`$ and some $`N`$;*

3.  *for some fixed $`h\ge1`$, $`\sigma_h(N)`$ is integral at every sufficiently large $`N`$.*

*Consequently $`T_0`$ is irrational if and only if every positive-length shift is non-integral at every index, equivalently if and only if the shifts are cofinally non-integral.*

</div>

<div class="proof">

*Proof.* For <span class="upright">(i)</span>$`\Rightarrow`$<span class="upright">(iii)</span>, choose $`q\in\mathbb{Q}`$ whose real cast is $`T_0`$. The real block identity identifies the whole orbit with the cast of the rational recurrence starting at $`q`$; Theorem <a href="#res:collapse" data-reference-type="ref" data-reference="res:collapse">18</a> applied to that rational orbit then gives <span class="upright">(iii)</span>. The implication <span class="upright">(iii)</span>$`\Rightarrow`$<span class="upright">(ii)</span> is immediate. For <span class="upright">(ii)</span>$`\Rightarrow`$<span class="upright">(i)</span>, the real block identity gives
``` math
\sigma_h(N)=(2^h-1)T_N-B_{h,N}.
```
Here $`B_{h,N}`$ and $`\sigma_h(N)`$ are integers and $`2^h-1\ne0`$, so $`T_N`$ is rational. Iterating the recurrence backwards through the block identity then makes $`T_0`$ rational. Negating the pointwise and eventual forms gives the two irrationality formulations. ◻

</div>

Lean checks the rational actual-tail state as [rational prime-gap tail state](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L489), its [recurrence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L527), and the bridge from a hypothetical rational value to that state as [the rational-tail representation](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L510). The exact real classifiers are [one integral positive shift](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1479), [eventual integrality](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1525), [pointwise non-integrality](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1551), and [cofinal non-integrality](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1572).

<a id="the-actual-prime-gap-orbit."></a>

#### The actual prime-gap orbit.

Define, at paper level,
``` math
\mathcal T_N=\sum_{j\ge1}\frac{g_{N+j}}{2^j}.
```
The Lean-checked polynomial prime bound gives convergence. A paper-level index shift, justified by that convergence, gives
``` math
\mathcal T_{N+1}=2\mathcal T_N-g_{N+1}.
```
If $`G=\sum_{n\ge0}g_n/2^{n+1}`$, then $`\mathcal T_0=2G-g_0=2G-1=2.349287932\ldots`$. Together with Theorem <a href="#res:infinite" data-reference-type="ref" data-reference="res:infinite">11</a>, this shows that $`\Pi`$, $`G`$, and $`\mathcal T_0`$ have the same rationality status. Thus Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">19</a> identifies Problem #251 exactly with cofinal shift escape for $`\mathcal T`$. Lean checks the rational candidate recurrence unconditionally and, under non-irrationality of the series, its representation of every scaled real tail. The displayed recurrence for $`\mathcal T`$ is the elementary index-shift deduction above. What is not proved is the cofinal non-integrality needed by Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">19</a>.

<a id="sec:local-certificate"></a>

## Two adjacent small shifts cannot both be integral

The exact classifier reduces irrationality to cofinal non-integrality, a condition of infinite precision imposed on a complete tail. The key point is that inside the open interval $`(-1,1)`$ integrality is equality with zero, so on that range the one-step shift recurrence
``` math
\sigma_h(N+1)=2\sigma_h(N)-\bigl(g_{N+h+1}-g_{N+1}\bigr)
```
turns simultaneous integrality of two adjacent shifts into a single comparison of digits. What this buys is a *certificate*: a condition attached to a single pair of adjacent indices, whose verification already contradicts integrality at that pair. The point of arranging the argument this way is that the distance of a shift from the integers never has to be estimated; it suffices to know that both shifts lie in $`(-1,1)`$ and that two digits differ.

<div id="res:smallpair" class="theorem">

**Theorem 20** (adjacent small-shift obstruction). *Let $`T:\mathbb{N}\to\mathbb{Q}`$ satisfy the dyadic tail recurrence with integer digits $`g`$. Fix $`h`$ and $`N`$. If
``` math
-1<\sigma_h(N)<1,\qquad -1<\sigma_h(N+1)<1,
 \qquad g_{N+h+1}\ne g_{N+1},
```
then $`\sigma_h(N)`$ and $`\sigma_h(N+1)`$ cannot both be integral. Consequently, if such a pair occurs beyond every threshold, the $`h`$-shift is not eventually integral.*

</div>

<div class="proof">

*Proof.* An integral rational strictly between $`-1`$ and $`1`$ is zero. If both shifts were integral, both would therefore vanish, and substitution in the displayed shift step identity would give $`g_{N+h+1}=g_{N+1}`$, a contradiction. The cofinal statement chooses one such adjacent pair after the alleged onset of integrality. ◻

</div>

The finite contradiction is the [adjacent small-shift obstruction](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L979); its quantified form is the [cofinal small-mismatch theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1006); and the actual-prime-gap specialisation is the [prime-gap specialisation](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1112). Theorem <a href="#res:smallpair" data-reference-type="ref" data-reference="res:smallpair">20</a> is conditional on its two tail inequalities. Corollary <a href="#res:finite-smallpair" data-reference-type="ref" data-reference="res:finite-smallpair">29</a> below supplies one actual pair; no theorem supplies their cofinal occurrence.

All three are stated for a rational orbit, while the prime-gap tail $`\mathcal T`$ of Section <a href="#sec:tail" data-reference-type="ref" data-reference="sec:tail">5</a> is real, so the rational statement does not on its own discharge the instances that arise downstream. The same argument gives the real form directly.

<div id="res:smallpair-real" class="corollary">

**Corollary 21** (adjacent small-shift obstruction, real form). *Let $`T:\mathbb{N}\to\mathbb{R}`$ satisfy $`T_{N+1}=2T_N-g_{N+1}`$ with integer digits $`g`$, and write $`\sigma_h(N)=T_{N+h}-T_N`$. Fix $`h`$ and $`N`$. If
``` math
-1<\sigma_h(N)<1,\qquad -1<\sigma_h(N+1)<1,
 \qquad g_{N+h+1}\ne g_{N+1},
```
then $`\sigma_h(N)`$ and $`\sigma_h(N+1)`$ do not both lie in $`\mathbb{Z}`$. Consequently, if such a pair occurs beyond every threshold, the $`h`$-shift is not eventually integral.*

</div>

<div class="proof">

*Proof.* The real recurrence gives the same shift step identity $`\sigma_h(N+1)=2\sigma_h(N)-\bigl(g_{N+h+1}-g_{N+1}\bigr)`$, and an integer strictly between $`-1`$ and $`1`$ is zero. If both shifts lay in $`\mathbb{Z}`$, both would therefore vanish, and substitution in that identity would give $`g_{N+h+1}=g_{N+1}`$, a contradiction. The cofinal statement chooses one such adjacent pair after the alleged onset of integrality. ◻

</div>

Corollary <a href="#res:smallpair-real" data-reference-type="ref" data-reference="res:smallpair-real">21</a> is proved here and is not a declaration in the pinned Lean module, whose small-shift theorems are stated for the rational orbit. It is the form that applies to the real tail, and it carries the same two smallness conditions as its rational counterpart. Their cofinal occurrence remains unproved.

The third hypothesis, on its own, is available. For the actual gaps tabulated in Section <a href="#sec:problem" data-reference-type="ref" data-reference="sec:problem">1</a> it reads $`g_4=2\ne4=g_3`$ at $`h=1`$, $`N=2`$; and Proposition <a href="#res:gap-nonperiodic" data-reference-type="ref" data-reference="res:gap-nonperiodic">22</a> below says precisely that for each fixed $`h\ge1`$ the inequality $`g_{N+h+1}\ne g_{N+1}`$ holds for arbitrarily large $`N`$, since its failure from some index onwards is eventual periodicity with period $`h`$. What is missing is the pair of inequalities, each of which constrains a complete infinite tail.

<div id="res:gap-nonperiodic" class="proposition">

**Proposition 22** (prime gaps do not become periodic). *For every positive $`h`$, the actual consecutive-prime-gap sequence is not eventually periodic with period $`h`$.*

</div>

<div class="proof">

*Proof.* The gaps are unbounded, by the standard construction: the interval from $`n!+2`$ to $`n!+n`$ contains no prime. Far stronger lower bounds for large gaps are known \[fgkmt2018, Theorem 1, p. 66\], but unboundedness is all that is needed. An eventually periodic natural-valued sequence has finite range after its preperiod, while its finite initial segment is bounded as well; hence it is bounded, a contradiction. ◻

</div>

Lean checks the factorial argument as [unboundedness of the actual gaps](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L57) and the conclusion as [non-eventual periodicity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1023). Combining nonperiodicity with eventual strict smallness of one positive shift would also exclude eventual integrality, but eventual smallness at every sufficiently large index is stronger than the cofinal adjacent-pair hypothesis in Theorem <a href="#res:smallpair" data-reference-type="ref" data-reference="res:smallpair">20</a> and is not asserted here.

<a id="sec:carry"></a>

# Nonperiodic coefficients with a rational sum

Proposition <a href="#res:gap-nonperiodic" data-reference-type="ref" data-reference="res:gap-nonperiodic">22</a> shows that the prime gaps are not eventually periodic. One might therefore hope that rationality of a dyadic series forces its integer coefficients to be eventually periodic, and play the two against each other. The hoped-for implication is false, and a single explicit sequence refutes it.

The construction runs the emission of coefficients backwards. Let $`K:\mathbb{N}\to\mathbb{Q}`$ be arbitrary, read $`K_n`$ as the value carried into level $`n`$, and put $`\kappa_n=2K_n-K_{n+1}`$: the [carry coefficient](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1129). That definition is exactly the statement that
``` math
\frac{K_n}{2^{\,n}}
 =\frac{\kappa_n}{2^{\,n+1}}+\frac{K_{n+1}}{2^{\,n+1}} ,
```
so at each level the carried value splits into one emitted coefficient and a new carry. Nothing at all is assumed about $`K`$: not integrality, not positivity, not any bound. That is the sense in which the carry is free, and it is what the counterexample below exploits.

<div id="res:telescope" class="proposition">

**Proposition 23** (exact telescoping). *Let $`K:\mathbb{N}\to\mathbb{Q}`$ be arbitrary and $`\kappa_n=2K_n-K_{n+1}`$. For every $`n\ge0`$,
``` math
\sum_{i=0}^{n-1}\frac{\kappa_i}{2^{\,i+1}}=K_0-\frac{K_n}{2^{\,n}} .
```*

</div>

<div class="proof">

*Proof.* A routine induction on $`n`$; the added term is $`(2K_n-K_{n+1})/2^{\,n+1}=K_n/2^{\,n}-K_{n+1}/2^{\,n+1}`$. ◻

</div>

Formalised as the [carry telescoping identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1137), on the [carry partial sum](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1133). When $`K`$ takes natural-number values and $`K_{n+1}\le2K_n`$ for every $`n`$, the coefficients $`\kappa_n`$ are natural numbers as well, and the natural-number and rational readings of the definition agree under the cast, the [natural-carry cast](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1180).

<a id="consequence-for-the-coefficients."></a>

#### Consequence for the coefficients.

If $`K_n2^{-n}\to0`$, the emitted partial sums converge to $`K_0`$. A parity-compatible positive example is
``` math
K_0=\frac52,\qquad K_n=2n+2\ (n\ge1),\qquad
 \kappa_0=1,\quad\kappa_n=2n\ (n\ge1),
```
for which
``` math
\sum_{i=0}^{n-1}\frac{\kappa_i}{2^{\,i+1}}
   =\frac52-\frac{K_n}{2^n}\longrightarrow\frac52.
```
Thus the emitted coefficients $`1,2,4,6,8,10,\ldots`$ are positive, even after the first term, unbounded and not eventually periodic, although their dyadic sum is rational. Rationality alone therefore cannot imply eventual periodicity even for a positive, parity-correct integer coefficient sequence. The example does not claim that these coefficients are prime gaps; it isolates the additional arithmetic information any successful argument must use.

<a id="sec:open"></a>

# Complements and further questions

Problem #251 is open. The public Lean source now proves unconditional convergence of both dyadic series, their exact infinite summation-by-parts identity, and the real-to-rational scaled-tail representation ([identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L427), [tail representation](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L510)). It also proves that every rational candidate supplies one positive fixed shift which is integral at every sufficiently late tail index ([checked](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L853)). The denominator construction selects that same shift so that prime-gap nonperiodicity also rules out its eventual confinement to the open unit interval ([not eventually small](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1097)). This conclusion is compatible with rationality: it says that the rationally forced shift cannot support an eventual-smallness contradiction. It supplies neither eventual smallness nor cofinally many adjacent small mismatches for that shift. The remaining issue is recurrence or anti-concentration of the *actual* prime-gap shifts. Throughout, $`g_i=p_{i+1}-p_i`$ are the zero-based prime gaps of Section <a href="#sec:problem" data-reference-type="ref" data-reference="sec:problem">1</a>. Write $`\mathsf E(h)`$ for the cofinal escape statement in <a href="#eq:shift-escape" data-reference-type="eqref" data-reference="eq:shift-escape">[eq:shift-escape]</a> at shift $`h`$.

<div id="prob:divisor-hit" class="problem">

**Problem 24** (divisor-hitting shift escape). For every $`r\ge1`$, does some positive multiple of $`r`$ escape cofinally?
``` math
\forall r\ge1\ \exists m\ge1:\qquad \mathsf E(mr).
```

</div>

This is the weaker recurrence-level target suggested by the denominator mechanism: a hypothetical rational value produces an eventually integral fixed shift, and the tail-shift cocycle propagates integrality forward and through positive multiples of that shift. Forward propagation is Lean-checked; the short multiple-in-shift closure is an elementary paper-level derivation and has not yet been given a named declaration. Accordingly this problem is presented as a sharper proposed criterion, not as a formally registered equivalence.

<div id="prob:escape" class="problem">

**Problem 25** (universal prime-gap shift escape). For every $`h\ge1`$ and every $`N_0`$, prove that some $`N\ge N_0`$ satisfies
``` math
\sum_{j\ge1}
 \frac{g_{N+h+j}-g_{N+j}}{2^j}\notin\mathbb{Z}.
\tag{5.1}\label{eq:shift-escape}
```

</div>

The series in <a href="#eq:shift-escape" data-reference-type="eqref" data-reference="eq:shift-escape">[eq:shift-escape]</a> is exactly $`\mathcal T_{N+h}-\mathcal T_N`$. Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">19</a> makes Problem <a href="#prob:escape" data-reference-type="ref" data-reference="prob:escape">25</a> equivalent to irrationality of $`\Pi`$. This all-shifts form is pointwise stronger than the sufficient target in Problem <a href="#prob:divisor-hit" data-reference-type="ref" data-reference="prob:divisor-hit">24</a>: a hypothetical rational value chooses a shift length from the odd part of its reduced denominator, and one needs only hit a compatible multiple rather than escape at every prescribed $`h`$.

<div id="prob:smallpair" class="problem">

**Problem 26** (cofinal adjacent small mismatch). For every fixed $`h\ge1`$ and every $`N_0`$, prove that some $`N\ge N_0`$ satisfies
``` math
\begin{split}
\left|\sum_{j\ge1}
 \frac{g_{N+h+j}-g_{N+j}}{2^j}\right|&<1,\\
\left|\sum_{j\ge1}
 \frac{g_{N+h+1+j}-g_{N+1+j}}{2^j}\right|&<1,\\
g_{N+h+1}&\ne g_{N+1}.
\end{split}
\tag{5.2}\label{eq:smallpair}
```

</div>

The two sums are adjacent $`h`$-shifts. Corollary <a href="#res:smallpair-real" data-reference-type="ref" data-reference="res:smallpair-real">21</a> turns each instance of <a href="#eq:smallpair" data-reference-type="eqref" data-reference="eq:smallpair">[eq:smallpair]</a> into a finite contradiction to simultaneous integrality; Theorem <a href="#res:smallpair" data-reference-type="ref" data-reference="res:smallpair">20</a> is the Lean-checked rational case. A cofinal family of such pairs therefore proves Problem <a href="#prob:escape" data-reference-type="ref" data-reference="prob:escape">25</a>; Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">19</a> then gives irrationality of the gap series, and Corollary <a href="#res:irr-equivalence" data-reference-type="ref" data-reference="res:irr-equivalence">12</a> transfers it to $`\Pi`$. This formulation deliberately asks only for sporadic adjacent pairs; the stronger assertion that a fixed shift is eventually always smaller than one is unnecessary.

Several natural prime-distribution inputs are insufficient. Isolated small gaps, isolated large gaps, average gap estimates, and the occurrence of any one fixed finite pattern do not suffice: both inequalities in <a href="#eq:smallpair" data-reference-type="eqref" data-reference="eq:smallpair">[eq:smallpair]</a> contain the complete infinite continuation. Nor does parity: after the first gap all $`g_n`$ are even. Unboundedness and non-eventual-periodicity of the actual gaps, though now checked, do not imply the required small-tail recurrence. In particular, Section <a href="#sec:carry" data-reference-type="ref" data-reference="sec:carry">6</a> shows that no argument can deduce eventual periodicity from rationality alone.

<a id="a-finite-truncation-criterion."></a>

#### A finite truncation criterion.

Both problems above are stated in terms of infinite tails, but a dominated truncation reduces the first of them to a finite quantity. For $`L\ge1`$ put
``` math
S_{h,N,L}=\sum_{j=1}^{L}
 \frac{g_{N+h+j}-g_{N+j}}{2^j},
```
the truncation of the series in <a href="#eq:shift-escape" data-reference-type="eqref" data-reference="eq:shift-escape">[eq:shift-escape]</a> after $`L`$ terms. This is a finite sum of gap differences and can be computed; the point of the following proposition is to say how far from an integer it must be before the discarded tail is irrelevant.

Equivalently, introduce the integral dyadic block
``` math
D_{h,N,L}=\sum_{j=1}^{L}2^{L-j}
   (g_{N+h+j}-g_{N+j}),\qquad S_{h,N,L}=\frac{D_{h,N,L}}{2^L}.
```
Then
``` math
\operatorname{dist}(S_{h,N,L},\mathbb{Z})
 =2^{-L}\min\{D_{h,N,L}\bmod2^L,
 2^L-(D_{h,N,L}\bmod2^L)\}.
```
Here $`D_{h,N,L}\bmod2^L`$ denotes the least nonnegative residue, including when $`D_{h,N,L}<0`$. Thus the finite criterion below is an exact modular small-arc problem: the residue of $`D_{h,N,L}`$ must avoid the two arcs of radius $`2^LR_{h,N,L}(M)`$ around $`0`$ modulo $`2^L`$. A one-block certificate would be a prime-gap theorem producing such an avoided arc on a logarithmic block.

<div id="res:truncation" class="proposition">

**Proposition 27** (finite truncation). *Let $`M(n)\ge g_n`$ for every $`n`$, assume that the series below converges, and put
``` math
R_{h,N,L}(M)=
 \sum_{j>L}\frac{M(N+h+j)+M(N+j)}{2^j}.
```
Suppose that for every fixed $`h\ge1`$ and every $`N_0`$ there exist $`N\ge N_0`$ and $`L\ge1`$ with
``` math
\operatorname{dist}(S_{h,N,L},\mathbb{Z})>R_{h,N,L}(M).
\tag{5.3}\label{eq:truncation}
```
Then Problem <a href="#prob:escape" data-reference-type="ref" data-reference="prob:escape">25</a> holds.*

</div>

<div class="proof">

*Proof.* The part of $`\sum_{j\ge1}(g_{N+h+j}-g_{N+j})2^{-j}`$ omitted from $`S_{h,N,L}`$ has absolute value at most $`R_{h,N,L}(M)`$, so under <a href="#eq:truncation" data-reference-type="eqref" data-reference="eq:truncation">[eq:truncation]</a> the full sum lies at positive distance from every integer. ◻

</div>

<div id="res:explicit-remainder" class="proposition">

**Proposition 28** (An explicit actual-gap remainder bound). *Set $`P(x)=x^4+8x^3+36x^2+104x+150`$. For $`h,N\ge0`$ and $`L\ge1`$,
``` math
\left|\mathcal T_{N+h}-\mathcal T_N-S_{h,N,L}\right|
 \le E_{h,N,L}:=
 \frac{1250}{2^L}\bigl(P(N+h+L+2)+P(N+L+2)\bigr).
```
In particular this bound requires no conjectural estimate on prime gaps.*

</div>

<div class="proof">

*Proof.* The checked estimate $`p_n\le1250(n+1)^4`$ gives $`0\le g_n\le p_{n+1}\le1250(n+2)^4`$ [the polynomial prime bound](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L360). The omitted absolute tail is therefore at most
``` math
1250\sum_{j>L}\frac{(N+h+j+2)^4+(N+j+2)^4}{2^j}.
```
For $`m\ge0`$, the polynomial identity $`2P(m)=(m+1)^4+P(m+1)`$ telescopes to
``` math
\sum_{k=1}^{J}\frac{(m+k)^4}{2^k}
 =P(m)-\frac{P(m+J)}{2^J}.
```
The last term tends to zero. Apply this identity with $`m=N+h+L+2`$ and $`m=N+L+2`$, after writing $`j=L+k`$. ◻

</div>

<div id="res:finite-smallpair" class="corollary">

**Corollary 29** (An actual adjacent small-mismatch pair). *The shifts $`\mathcal T_3-\mathcal T_2`$ and $`\mathcal T_4-\mathcal T_3`$ both lie in $`(-1,1)`$ and neither is an integer. The corresponding gaps satisfy $`g_4=2\ne4=g_3`$.*

</div>

<div class="proof">

*Proof.* Take $`h=1`$ and $`L=40`$. Direct integer calculation from the first $`46`$ primes gives the following block numerators and error numerators, with common denominator $`Q=2^{40}=1099511627776`$:
``` math
\begin{array}{c|r|r}
 N&D_{1,N,40}&Q E_{1,N,40}\\\hline
 2&-662838684750&11764181250\\
 3& 873345886050&12805761250
\end{array}
```
For each row, writing $`D`$ and $`B`$ for the last two entries, one checks
``` math
|D|+B<Q,\qquad
 B<\min\{D\bmod Q,\ Q-(D\bmod Q)\}.
```
The first inequality puts the entire certified interval inside $`(-1,1)`$; the second excludes every integer. These are strict integer comparisons, not inferences from rounded numerical tails. The script `scripts/check_prime_gap_tail_certificate.py` regenerates the prime list, both rows, the polynomial identity and the strict margins. ◻

</div>

The remainder estimate and its assembly with the finite computation are ordinary proofs here, not new Lean declarations. The bound produces a certificate for these two actual tails; it does not produce such pairs cofinally, or for every fixed shift length. Thus it supplies an instance of the local obstruction without establishing Problem <a href="#prob:smallpair" data-reference-type="ref" data-reference="prob:smallpair">26</a>.

For fixed $`h`$, the explicit bound also gives a logarithmic truncation length: $`L=\lceil A\log_2(N+h+2)\rceil`$ with fixed $`A>4`$ makes $`E_{h,N,L}=O((N+h+2)^{4-A})`$ as $`N\to\infty`$. The familiar sharper prime-growth estimate can improve the constant in this window length, but is not needed to make the certificate finite. The unresolved work is to place the dyadic block away from the integer arcs often enough at these scales.

What <a href="#eq:truncation" data-reference-type="eqref" data-reference="eq:truncation">[eq:truncation]</a> requires is joint control of the finite block of weighted differences $`(g_{N+h+1}-g_{N+1},\ldots,g_{N+h+L}-g_{N+L})`$ modulo powers of two, along a block of logarithmic length. We do not know how to obtain such control and the finite certificate above does not establish it. The strongest results on prime gaps address a different shape of question. Zhang’s bounded-gap theorem \[zhang2014, Theorem 1, p. 1122\] produces infinitely many bounded consecutive-prime gaps. Maynard proves substantially more than an individual-gap statement: \[maynard2015, Theorem 1.1, p. 384\] bounds $`\liminf_n(p_{n+m}-p_n)`$ for every fixed $`m`$, and hence gives bounded clusters of every fixed size; \[maynard2015, Theorem 1.3, p. 385\] gives the explicit unconditional bound $`\liminf_n(p_{n+1}-p_n)\le 600`$. The large-gap theorem of Ford, Green, Konyagin, Maynard and Tao \[fgkmt2018, Theorem 1, p. 66\] bounds the largest single consecutive-prime gap below $`X`$. None of these results supplies the joint dyadic distribution of a logarithmic block of consecutive gap differences required by <a href="#eq:truncation" data-reference-type="eqref" data-reference="eq:truncation">[eq:truncation]</a>. The same introduction notes a separate sequel on chains of large gaps; the cited theorem itself supplies no residue-sensitive block estimate of the kind needed here.

<a id="what-remains-to-be-formalised."></a>

#### What remains to be formalised.

Unconditional convergence, the infinite series identity, the actual rational scaled-tail state and its recurrence, the eventual-integral-shift theorem, the abstract rationality classification, and the prime-specific local small-mismatch theorem are Lean-checked. The quadratic polynomial-shift countermodel, including its exact recurrence, strict growth, failed adjacent trigger, and integral shifts, is also Lean-checked. The identification of the concrete tail $`\mathcal T`$ with the checked recurrence is Lean-checked as well, [at line 48 of the real prime-gap tail module](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L48), and so is the real form of the small-shift obstruction in Corollary <a href="#res:smallpair-real" data-reference-type="ref" data-reference="res:smallpair-real">21</a>, [at line 99 of the same module](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L99); an earlier reading of this note placed both on the paper side, and that reading was wrong. Paper-level are the modular rewriting by $`D_{h,N,L}`$, the finite-approximation inference, and the positive carry countermodel above. The denominator floor of Theorem <a href="#res:denominatorfloor" data-reference-type="ref" data-reference="res:denominatorfloor">1</a> and the free-pair criterion of Theorem <a href="#res:freepair" data-reference-type="ref" data-reference="res:freepair">3</a> are Lean-checked in the private development and await the next governed build of the pinned source; the continued-fraction exclusion of Theorem <a href="#res:cfexclusion" data-reference-type="ref" data-reference="res:cfexclusion">2</a> and the density measurement have no Lean route at present. The explicit polynomial remainder bound and its two finite certificates above are ordinary mathematical proofs with exact integer replay; their Lean formalization remains to be supplied. The remaining producer is a cofinal anti-concentration or adjacent-mismatch theorem. The multiple-in-shift lemma used by Problem <a href="#prob:divisor-hit" data-reference-type="ref" data-reference="prob:divisor-hit">24</a> also remains to be formalised. No theorem supplies the cofinal pairs in <a href="#eq:smallpair" data-reference-type="eqref" data-reference="eq:smallpair">[eq:smallpair]</a>, and no cited prime-distribution estimate is claimed or formalised as supplying those statements.

<a id="statements-and-declarations"></a>

## Statements and declarations

<a id="artefact-and-data-availability."></a>

#### Artefact and data availability.

The [pinned formal-source revision](https://github.com/wcook04/plectis-erdos/tree/4ab50e144847a3393fb340341760e5d6907d702e) contains the Lean sources, the fixed toolchain, and the library manifest used in the verification. This manuscript provides navigation rather than proof authority.

Lean checks each proof term against the fixed library version, and the sources linked here contain no proof placeholders and no project-defined axioms; Lean does not authorise the exposition, the citation choices, or the interpretation, for which the author remains responsible.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem numbering and status follow the Erdős Problems catalogue maintained by Thomas Bloom \[erdosproblems\].

<a id="app:index"></a>

# Guide to the formal sources

Each linked phrase opens its Lean declaration at the pinned source revision 4ab50e144847. All declarations of this note live in one module. The summation-by-parts declarations are prime-specific; most of Section <a href="#sec:tail" data-reference-type="ref" data-reference="sec:tail">5</a> is stated for arbitrary integer digits and arbitrary rational or real orbits, while Section <a href="#sec:local-certificate" data-reference-type="ref" data-reference="sec:local-certificate">5.1</a> records the actual-gap specialisation. The concrete prime-gap tail, its unconditional convergence, its rational candidate state and the real-to-rational scaled-tail bridge are all defined and checked in the pinned Lean module.

<a id="checked-declarations-behind-the-actual-prime-gap-tail."></a>

#### Checked declarations behind the actual prime-gap tail.

The scaled actual prime-gap tail equals its convergent shifted-gap series, [shifted-gap series identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L31), and satisfies the real dyadic recurrence unconditionally, [real tail recurrence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L48). Irrationality of the actual prime series is equivalent to escape of its positive real tail shifts from integral values, [escape equivalence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L73), and cofinal adjacent small shifts with mismatched actual gaps imply irrationality, [small-mismatch criterion](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L120). These four declarations are kernel checked; none of them decides the escape hypothesis for the actual gaps.

<div class="thebibliography">

99

P. Erdős, [*Sur certaines séries à valeur irrationnelle*](https://users.renyi.hu/~p_erdos/1958-19.pdf), Enseign. Math. (2) **4** (1958), 93–100, doi:[10.5169/seals-34629](https://doi.org/10.5169/seals-34629). The dyadic prime series is stated as unproved on p. 94; the factorial-prime family is stated on p. 93, with only the $`k=1`$ proof printed on pp. 94–95. P. Erdős and R. L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf), Monogr. Enseign. Math. 28, Geneva, 1980, p. 62. P. Erdős and C. Pomerance, [*On the largest prime factors of $`n`$ and $`n+1`$*](https://doi.org/10.1007/BF01818569), Aequationes Math. **17** (1978), 311–321, doi:[10.1007/BF01818569](https://doi.org/10.1007/BF01818569). The unnumbered dyadic irrationality theorem and its complete proof are in §7 on p. 320. P. Erdős, *On the irrationality of certain series: problems and results*, in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). P. Erdős and E. G. Straus, *On the irrationality of certain Ahmes series*, J. Indian Math. Soc. (N.S.) **27** (1964), 129–133. MR 175848. K. Ford, B. Green, S. Konyagin, J. Maynard and T. Tao, *Long gaps between primes*, J. Amer. Math. Soc. **31** (2018), 65–105, doi:[10.1090/jams/876](https://doi.org/10.1090/jams/876). Theorem 1 on p. 66 gives the effective lower bound for the largest single consecutive-prime gap below $`X`$. A. Ya. Khinchin, *Continued Fractions*, University of Chicago Press, Chicago, 1964. Cited for the classical fact that a best approximation of the second kind is a convergent, which converts a certified partial-quotient prefix into a denominator lower bound. V. Kovač and T. Tao, [*On several irrationality problems for Ahmes series*](https://doi.org/10.1007/s10474-025-01528-0), Acta Math. Hungar. **175** (2025), 572–608. L. de Moura and S. Ullrich, [*The Lean 4 theorem prover and programming language*](https://doi.org/10.1007/978-3-030-79876-5_37), in A. Platzer and G. Sutcliffe (eds.), CADE 28, Lecture Notes in Comput. Sci. 12699, Springer, 2021, pp. 625–635, doi:[10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37). The mathlib Community, [*The Lean mathematical library*](https://doi.org/10.1145/3372885.3373824), in CPP 2020, ACM, 2020, pp. 367–381, doi:[10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). The article describes a December 2019 Lean 3-era snapshot; the repository lock owns the current revision. J. Maynard, [*Small gaps between primes*](https://doi.org/10.4007/annals.2015.181.1.7), Ann. of Math. (2) **181** (2015), 383–413. H. L. Montgomery and R. C. Vaughan, [*Multiplicative Number Theory I: Classical Theory*](https://doi.org/10.1017/CBO9780511618314.008), Cambridge Stud. Adv. Math. 97, Cambridge UP, 2007, Chapter 6, pp. 168–198; Theorem 6.9, pp. 179–181, and Exercise 6.2.5, p. 183, doi:[10.1017/CBO9780511618314.008](https://doi.org/10.1017/CBO9780511618314.008). J.-C. Schlage-Puchta, *The irrationality of some number theoretical series*, arXiv:1105.1451, 2011. Theorem 2 treats periodic base-$`b`$ digit expansions; it is recorded here as the nearest located antecedent to the free-pair form and as a different object. Y. Zhang, [*Bounded gaps between primes*](https://doi.org/10.4007/annals.2014.179.3.7), Ann. of Math. (2) **179** (2014), 1121–1174. T. F. Bloom, [*Erdős Problem \#251*](https://www.erdosproblems.com/251), `erdosproblems.com/251`, accessed 28 July 2026 (page displays “last edited 28 September 2025”). The current record labels the main dyadic problem open, cites `[Er58b]`, `[ErGr80, p. 62]` and `[Er88c, p. 103]`, and explicitly describes its status as the website owner’s present assessment rather than a literature-completeness guarantee; it does not mention the 2026 counterexample in \[kovac2026\] to the adjacent variable-denominator conjecture. ChatGPT 5.4 Pro (orchestrated by V. Kovač), [*On the Erdős problem \#251*](https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_251.pdf), unpublished note, 2026, hosted by the Department of Mathematics, University of Zagreb, `web.math.pmf.unizg.hr`, accessed 28 July 2026. The Formal Conjectures Authors, [*FormalConjectures.ErdosProblems.`251`*](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/251.lean), Lean source at commit `f776d2f`, 2025, accessed 28 July 2026.

</div>
