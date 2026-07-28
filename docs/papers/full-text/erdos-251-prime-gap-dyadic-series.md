<a id="erdos-251-prime-gap-dyadic-series"></a>

# An Integral-Shift Criterion for Dyadic Tail Recurrences

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

For an abstract dyadic tail recurrence $`T_{N+1}=2T_N-g_{N+1}`$ with integer digits we prove the block identity $`T_{N+h}=2^{h}T_N-B_{h,N}`$, with $`B_{h,N}=g_{N+1}2^{\,h-1}+\cdots+g_{N+h}`$, and hence that the shift $`T_{N+h}-T_N`$ is integral *if and only if* $`(2^{h}-1)T_N`$ is; that integrality of one shift propagates to every later index; and, by Euler’s congruence, that a state with odd reduced denominator $`d`$ has an integral shift of length $`\varphi(d)`$. Consequently every rational orbit has a fixed $`h\ge1`$ whose shifts are integral from some index onwards, and a real orbit whose shifts are cofinally non-integral has irrational initial value. The digits enter these statements only through their integrality.

Let $`p_0=2,p_1=3,\ldots`$ enumerate the primes and let $`g_n=p_{n+1}-p_n`$. We formalise in Lean both the exact finite identity
``` math
\sum_{i=0}^{n}\frac{p_i}{2^{\,i+1}}
 \;=\;2+\sum_{i=0}^{n-1}\frac{g_i}{2^{\,i+1}}-\frac{p_n}{2^{\,n+1}},
```
and, conditional only on summability, the infinite identity and irrationality equivalence
``` math
\sum_{i\ge0}\frac{p_i}{2^{\,i+1}}
 =2+\sum_{i\ge0}\frac{g_i}{2^{\,i+1}},\qquad
 \operatorname{Irr}\!\left(\sum_{i\ge0}\frac{p_i}{2^{\,i+1}}\right)
 \Longleftrightarrow
 \operatorname{Irr}\!\left(\sum_{i\ge0}\frac{g_i}{2^{\,i+1}}\right).
```
The prime number theorem supplies the summability in ordinary mathematics; that external input is not formalised here and remains an explicit hypothesis of the Lean declarations.

Problem #251 remains open. The remaining obligation is now exact: rationality would force some fixed $`h\ge1`$ for which the actual tail shifts $`T_{N+h}-T_N`$ are integers at every sufficiently large $`N`$. Thus it is enough to prove cofinal non-integrality for every fixed $`h`$. We also prove a local certificate: two adjacent shifts lying strictly between $`-1`$ and $`1`$ cannot both be integral when the corresponding prime gaps differ. Consequently it is enough to produce such adjacent small-mismatch pairs cofinally. The actual prime gaps are Lean-checked to be unbounded, hence not eventually periodic, but that fact alone supplies no tail smallness. A free-carry telescoping identity gives an explicit unbounded, nonperiodic integer coefficient stream with rational dyadic sum. Thus rationality alone cannot force eventual periodicity; the missing theorem must control the full prime-gap tails.

<a id="sec:problem"></a>

# Introduction

Let $`p_n`$ denote the $`n`$th prime. Erdős Problem #251 asks whether
``` math
\Pi=\sum_{n\ge1}\frac{p_n}{2^{\,n}}
```
is irrational \[erdos1958\]\[erdosgraham1980, p. 62\] \[erdos1988, p. 103\]. Numbering and status follow Bloom’s catalogue \[erdosproblems\]. The problem is open.

Throughout the formal development the primes are indexed from zero, so that $`p^{(0)}_0=2`$, $`p^{(0)}_1=3`$, $`p^{(0)}_2=5`$, and the gaps are $`g_i=p^{(0)}_{i+1}-p^{(0)}_i`$. In that indexing
``` math
\Pi=\sum_{i\ge0}\frac{p^{(0)}_i}{2^{\,i+1}} ,
```
which is the convention every statement below uses; we drop the superscript from here on. A second normalisation with denominator $`2^{\,i}`$ also occurs, and at every finite horizon it is exactly twice this one,
``` math
\sum_{i=0}^{n-1}\frac{p_i}{2^{\,i}}
 =2\sum_{i=0}^{n-1}\frac{p_i}{2^{\,i+1}} ,
```
the [factor-of-two normalisation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L105). A factor of two does not change rationality, so no result below depends on the choice; the identity is stated so that the indexing cannot drift silently.

<a id="relation-to-prior-work."></a>

#### Relation to prior work.

Erdős proved that $`\sum_n p_n^{k}/n!`$ is irrational for every $`k\ge1`$ \[erdos1958\]. On page 103 of his 1988 problem paper he separately posed the fixed-denominator conjecture that $`\sum_n p_n^{k}/2^{n}`$ is irrational for every $`k\ge1`$, and the variable-denominator expectation that $`\sum_{n\ge1}p_n/(g_1\cdots g_n)`$ is irrational whenever $`g_n\ge2`$ and $`g_n=o(p_n)`$ \[erdos1988, p. 103\]. The latter expectation is false: ChatGPT 5.4 Pro, orchestrated by Vjeko Kovač, constructs such a sequence $`(g_n)`$ for which the sum is exactly $`1`$ \[kovac2026\]. That construction does not address the fixed-denominator dyadic series studied here. Problem #251 also appears as the unproved declaration `erdos_251` in the *Formal Conjectures* repository \[formalconjectures251\]; no priority is claimed for anything below.

<a id="the-strategy."></a>

#### The strategy.

The digits $`p_n`$ grow, so the series is not a digit expansion in any bounded alphabet, and the standard rationality criteria for such expansions do not apply directly. The classical elementary criteria for series of this kind instead control irrationality through the growth of the denominators. Erdős and Straus named a sum $`\sum_k 1/a_k`$ over a strictly increasing sequence of positive integers an *Ahmes series* \[erdosstraus1963\]; for such a series the condition $`a_k^{1/2^k}\to\infty`$ is sufficient for irrationality, and it is sharp, since shifted Sylvester sequences grow like $`C^{2^{k}}`$ for arbitrarily large $`C`$ and have rational reciprocal sum. Both statements and their attribution are recorded in the introduction of Kovač and Tao \[kovactao2024, §1\], who develop the elementary technology for such series much further. Splitting each term $`p_i/2^{\,i+1}`$ into $`p_i`$ copies of $`2^{-(i+1)}`$ writes $`\Pi`$ as a sum of unit fractions, but with repetitions, and the denominators occurring in it are exactly the powers of two. Even ignoring the repetitions the growth hypothesis fails by every available margin, since $`(2^{\,n})^{1/2^{\,n}}\to1`$, and every arithmetic constraint has to come from the numerators instead.

What replaces growth control is denominator control on a tail orbit. Rationality of the sum turns out to be equivalent to an eventual integrality condition on differences of tails, and that condition uses nothing about the digits beyond the fact that they are integers. The condition does not by itself force periodic digits: Proposition <a href="#res:telescope" data-reference-type="ref" data-reference="res:telescope">14</a>, applied to $`K_n=n`$, gives the coefficient stream $`\kappa_n=n-1`$, whose dyadic sum is zero. This explicit counterexample is unbounded and not eventually periodic.

<a id="outline."></a>

#### Outline.

Section <a href="#sec:parts" data-reference-type="ref" data-reference="sec:parts">2</a> replaces the primes by their consecutive gaps, the natural increments studied by prime-distribution theory. Summation by parts with the endpoint retained gives an exact finite identity, and the termwise relation $`v_n=2u_{n+1}-u_n`$ makes the passage to the limit a summable coboundary; the prime number theorem supplies the summability externally. Section <a href="#sec:tail" data-reference-type="ref" data-reference="sec:tail">3</a> develops the tail orbit: the block identity, the integral-shift criterion, the collapse of every rational orbit onto an eventually integral shift, its contrapositive over the reals, and a local obstruction that converts an infinite-tail condition into a single comparison of gaps. Section <a href="#sec:carry" data-reference-type="ref" data-reference="sec:carry">4</a> shows that the tail constraint does not descend to the gap word, and Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">5</a> states the remaining obligation. The formal statements are checked by Lean 4 \[lean4\] against Mathlib \[mathlib\]; linked phrases open the corresponding declaration at the pinned source revision 7558c58afb7c.

*Status.* The problem treated here is open, and this note does not close it. Every statement below marked as checked is a proposition that the pinned Lean kernel accepts from the sources this note links to, with no `sorry`, no added axiom, and no unchecked evaluation. That is a claim about the formal statement, not about its mathematical interest, its novelty, or the original problem. The unresolved obligations are named exactly, in their own section, and none of the finite computations, reductions, or no-go results here removes one of them.

| Statement | Status | Treatment here |
|:---|:---|:---|
| Irrationality of $`\Pi`$ | Open | Not proved. |
| Finite prime-gap identity | Proved here | Theorem <a href="#res:parts" data-reference-type="ref" data-reference="res:parts">2</a>, with the endpoint retained. |
| Infinite prime-gap identity | Lean-checked conditionally | Theorem <a href="#res:infinite" data-reference-type="ref" data-reference="res:infinite">3</a>; the prime number theorem supplies the hypothesis externally. |
| Prime-series/gap-series irrationality equivalence | Lean-checked conditionally | Corollary <a href="#res:irr-equivalence" data-reference-type="ref" data-reference="res:irr-equivalence">4</a>. |
| Block identity for the tail recurrence | Proved here | Theorem <a href="#res:block" data-reference-type="ref" data-reference="res:block">6</a>. |
| Integral shift criterion | Proved here; an equivalence | Theorem <a href="#res:shiftiff" data-reference-type="ref" data-reference="res:shiftiff">7</a>. |
| Totient shift from an odd denominator | Proved here | Theorem <a href="#res:totient" data-reference-type="ref" data-reference="res:totient">8</a>. |
| Propagation of an integral shift | Proved here | Theorem <a href="#res:propagate" data-reference-type="ref" data-reference="res:propagate">9</a>. |
| Eventual integral shift for every rational orbit | Lean-checked | Theorem <a href="#res:collapse" data-reference-type="ref" data-reference="res:collapse">10</a>. |
| Cofinal shift escape implies irrationality | Lean-checked abstractly | Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">11</a>. |
| Actual prime gaps are unbounded and not eventually periodic | Lean-checked | Proposition <a href="#res:gap-nonperiodic" data-reference-type="ref" data-reference="res:gap-nonperiodic">13</a>. |
| Adjacent small-mismatch pair excludes simultaneous integrality | Lean-checked | Theorem <a href="#res:smallpair" data-reference-type="ref" data-reference="res:smallpair">12</a>. |
| Concrete prime-gap tail recurrence | Paper-proved from PNT | Not yet instantiated as a Lean infinite sum. |
| Rationality alone forces periodic integer coefficients | False | Section <a href="#sec:carry" data-reference-type="ref" data-reference="sec:carry">4</a>, Proposition <a href="#res:telescope" data-reference-type="ref" data-reference="res:telescope">14</a>. |
| Cofinal adjacent small-mismatch hypothesis | Proposed sufficient theorem | Problem <a href="#prob:smallpair" data-reference-type="ref" data-reference="prob:smallpair">16</a>; not proved. |

**Keywords.** irrationality; prime gaps; dyadic series; summation by parts; Lean 4. **MSC 2020.** 11J72 (primary); 11N05, 68V20 (secondary).

<a id="sec:parts"></a>

# Summation by parts, with the endpoint retained

Write $`\mathbb{N}_{>0}`$-indexed sums with the convention
``` math
D(P,n)=\sum_{i=0}^{n-1}\frac{P(i)}{2^{\,i+1}},
 \qquad
 \Delta(P,n)=\sum_{i=0}^{n-1}\frac{P(i+1)-P(i)}{2^{\,i+1}} ,
```
for a rational sequence $`P`$. These are the [dyadic partial sum](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L95) and the [dyadic difference sum](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L115).

<div id="res:abel" class="proposition">

**Proposition 1** (finite summation by parts). *For every rational sequence $`P`$ and every $`n\ge0`$,
``` math
D(P,n+1)=P(0)+\Delta(P,n)-\frac{P(n)}{2^{\,n+1}} .
```*

</div>

<div class="proof">

*Proof.* A routine induction on $`n`$. At $`n=0`$ both sides equal $`P(0)/2`$. For the step, adding $`P(n+1)/2^{\,n+2}`$ to the left and $`\bigl(P(n+1)-P(n)\bigr)/2^{\,n+1}`$ to the difference sum changes the endpoint term from $`P(n)/2^{\,n+1}`$ to $`P(n+1)/2^{\,n+2}`$, and the two adjustments agree. ◻

</div>

Formalised as the [summation-by-parts identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L132). Nothing is assumed about $`P`$: no positivity, no monotonicity, and no convergence.

Specialising to $`P(i)=p_i`$, whose first value is $`p_0=2`$, and writing $`g_i=p_{i+1}-p_i`$ for the zero-based gaps, gives the reformulation.

<div id="res:parts" class="theorem">

**Theorem 2** (prime-gap reformulation). *For every $`n\ge0`$,
``` math
\sum_{i=0}^{n}\frac{p_i}{2^{\,i+1}}
 =2+\sum_{i=0}^{n-1}\frac{g_i}{2^{\,i+1}}-\frac{p_n}{2^{\,n+1}} .
```*

</div>

Formalised as the [prime-gap summation by parts](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L161), using the [gap partial sum](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L155) and the [gap cast identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L150); the latter records that the natural-number difference $`p_{n+1}-p_n`$ agrees with the difference taken in $`\mathbb{Q}`$, which needs $`p_n\le p_{n+1}`$, the [monotonicity step](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L146). The leading $`2`$ is the first prime, not a normalising constant.

<a id="sec:infinite"></a>

## The infinite identity and the irrationality equivalence

Put
``` math
u_n=\frac{p_n}{2^{\,n+1}},\qquad
 v_n=\frac{g_n}{2^{\,n+1}}.
```
The termwise identity $`v_n=2u_{n+1}-u_n`$ is the [dyadic discrete derivative](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L191). It exhibits the gap series as a summable coboundary of $`(u_n)`$.

<div id="res:infinite" class="theorem">

**Theorem 3** (infinite prime-gap identity). *If $`\sum_{n\ge0}u_n`$ is summable, then $`\sum_{n\ge0}v_n`$ is summable and
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

The summability transfer is the [gap-series summability theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L202), and the displayed identity is the [infinite prime-gap identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L214).

<div id="res:irr-equivalence" class="corollary">

**Corollary 4** (exact irrationality reformulation). *Under the same summability hypothesis,
``` math
\operatorname{Irr}\!\left(\sum_{n\ge0}u_n\right)
 \quad\Longleftrightarrow\quad
 \operatorname{Irr}\!\left(\sum_{n\ge0}v_n\right).
```
The corresponding zero-based series with denominator $`2^n`$ is $`4+2\sum_{n\ge0}v_n`$ and has the same irrationality status.*

</div>

These are the [normalised irrationality equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L239), the [displayed-series identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L248), and the [displayed-series irrationality equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L263).

<a id="the-summability-hypothesis."></a>

#### The summability hypothesis.

The prime number theorem, proved by Hadamard and by de la Vallée Poussin in 1896 and presented in Chapter 6 of Montgomery and Vaughan \[mv2007, Ch. 6\], gives $`p_n\sim n\log n`$, hence $`p_n/2^n`$ is summable by comparison with any fixed exponential $`\rho^n`$ with $`1<\rho<2`$. Consequently Theorem <a href="#res:infinite" data-reference-type="ref" data-reference="res:infinite">3</a> and Corollary <a href="#res:irr-equivalence" data-reference-type="ref" data-reference="res:irr-equivalence">4</a> are unconditional paper-level consequences of a classical external theorem. The local Lean development does not formalise the prime number theorem, so its declarations retain summability as an explicit hypothesis. This is a gap in the formalisation, not in the mathematics: the open content is exactly irrationality of the prime-gap series.

<a id="sec:tail"></a>

# The tail recurrence and integral shifts

Rationality of a dyadic series constrains its tail orbit. This section proves what that constraint is, for an abstract recurrence.

<div id="def:rec" class="definition">

**Definition 5**. Let $`g:\mathbb{N}\to\mathbb{Z}`$ and $`T:\mathbb{N}\to\mathbb{Q}`$. Say $`T`$ satisfies the *dyadic tail recurrence* with digits $`g`$ when
``` math
T_{N+1}=2T_N-g_{N+1}\qquad\text{for every }N .
```
Write $`\sigma_h(N)=T_{N+h}-T_N`$ for the *shift* of length $`h`$ at $`N`$, and call a rational number *integral* when it is the image of an integer.

</div>

These are the [tail recurrence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L278), the [shift](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L282), and [integrality](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L298). The digits are arbitrary integers. In the intended instance they are the prime gaps and $`T_N`$ is the scaled tail of $`\Pi`$ after level $`N`$, but that instantiation needs a summability argument and is not made here; every statement below is a theorem about Definition <a href="#def:rec" data-reference-type="ref" data-reference="def:rec">5</a>.

Iterating the recurrence accumulates an explicit integer. Define $`B_{0,N}=0`$ and $`B_{h+1,N}=2B_{h,N}+g_{N+h+1}`$, so that $`B_{h,N}=g_{N+1}2^{\,h-1}+\cdots+g_{N+h}`$: the [tail block](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L304).

<div id="res:block" class="theorem">

**Theorem 6** (block identity). *For every $`N`$ and $`h`$,
``` math
T_{N+h}=2^{h}T_N-B_{h,N},
 \qquad\text{hence}\qquad
 \sigma_h(N)=(2^{h}-1)\,T_N-B_{h,N} .
```*

</div>

<div class="proof">

*Proof.* A routine induction on $`h`$; the step is one application of the recurrence together with $`2\cdot2^{h}=2^{h+1}`$ and the recursion defining $`B`$. The second identity is the first minus $`T_N`$. ◻

</div>

Formalised as the [iterated block identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L310) and the [scaled shift identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L324). The shift also obeys the recurrence in its own right, $`\sigma_h(N+1)=2\sigma_h(N)-(g_{N+h+1}-g_{N+1})`$, the [shift step identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L286).

Since $`B_{h,N}`$ is an integer, Theorem <a href="#res:block" data-reference-type="ref" data-reference="res:block">6</a> converts a question about the shift into a question about a single scaled state.

<div id="res:shiftiff" class="theorem">

**Theorem 7** (integral-shift criterion). *For every $`N`$ and $`h`$, the shift $`\sigma_h(N)`$ is integral if and only if $`(2^{h}-1)T_N`$ is integral.*

</div>

<div class="proof">

*Proof.* By Theorem <a href="#res:block" data-reference-type="ref" data-reference="res:block">6</a> the two differ by the integer $`B_{h,N}`$, and subtracting an integer does not change integrality. ◻

</div>

Formalised as the [integral-shift criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L380), on the [integer-shift invariance](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L334). This is an equivalence, not a one-way reduction: the block carries no information about integrality, so the two conditions are the same condition.

<div id="res:totient" class="theorem">

**Theorem 8** (a shift of totient length). *If the reduced denominator $`d`$ of $`T_N`$ is odd, then $`\sigma_{\varphi(d)}(N)`$ is integral.*

</div>

<div class="proof">

*Proof.* Since $`d`$ is odd, $`2`$ and $`d`$ are coprime, so Euler’s congruence gives $`2^{\varphi(d)}\equiv1\pmod d`$, that is $`d\mid 2^{\varphi(d)}-1`$. Writing $`2^{\varphi(d)}-1=dk`$ and $`T_N=u/d`$ in lowest terms, $`(2^{\varphi(d)}-1)T_N=ku`$ is an integer, and Theorem <a href="#res:shiftiff" data-reference-type="ref" data-reference="res:shiftiff">7</a> transfers this to the shift. ◻

</div>

Formalised as the [totient shift](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L391) and the [Euler multiplier](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L352). The hypothesis is a genuine restriction: the argument uses coprimality of $`2`$ with the denominator, and the even part of a denominator is exactly what the doubling in the recurrence acts on.

<div id="res:propagate" class="theorem">

**Theorem 9** (propagation). *If $`\sigma_h(N)`$ is integral, then $`\sigma_h(N+k)`$ is integral for every $`k\ge0`$.*

</div>

<div class="proof">

*Proof.* By the shift step identity, $`\sigma_h(N+1)=2\sigma_h(N)-(g_{N+h+1}-g_{N+1})`$ is an integer combination of an integer and two digits; induct on $`k`$. ◻

</div>

Formalised as the [one-step propagation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L402) and the [propagation to every later index](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L414).

The three preceding theorems combine as follows, and this is the statement the rest of the note rests on. The key point is that the doubling in the recurrence annihilates exactly the $`2`$-adic part of a denominator, and nothing else: after finitely many steps the orbit therefore occupies a state with odd reduced denominator, which is precisely the situation Theorem <a href="#res:totient" data-reference-type="ref" data-reference="res:totient">8</a> handles. No control of the digits is needed anywhere.

<div id="res:collapse" class="theorem">

**Theorem 10** (denominator collapse). *Every rational-valued recurrence of Definition <a href="#def:rec" data-reference-type="ref" data-reference="def:rec">5</a> has a fixed positive shift which is integral from some point onwards:
``` math
\exists h\ge1\ \exists N_0\ \forall N\ge N_0,\qquad
 \sigma_h(N)\in\mathbb{Z}.
```*

</div>

<div class="proof">

*Proof.* Write the reduced denominator of $`T_0`$ as $`2^s m`$ with $`m`$ odd. The block identity gives $`T_s=2^sT_0-B_{s,0}`$. Multiplying by $`2^s`$ clears the entire power of two from the denominator, and subtracting the integer $`B_{s,0}`$ cannot reintroduce one, so the reduced denominator of $`T_s`$ divides $`m`$ and is in particular odd. Theorem <a href="#res:totient" data-reference-type="ref" data-reference="res:totient">8</a>, applied at index $`s`$, supplies the positive shift $`h=\varphi(\operatorname{den}T_s)`$, and Theorem <a href="#res:propagate" data-reference-type="ref" data-reference="res:propagate">9</a> keeps that shift integral at every later index. ◻

</div>

Three features of the argument are used later. The proof may take as its number of preparatory steps the $`2`$-adic valuation of $`\operatorname{den}T_0`$. The resulting shift length $`h`$ is the totient of the odd denominator reached from a hypothetical rational initial value, and is not known in advance for the prime-gap orbit. This is why this argument requires Problem <a href="#prob:escape" data-reference-type="ref" data-reference="prob:escape">15</a> for every $`h`$, rather than for one preassigned shift length. Finally, the digits enter only through the integer $`B_{s,0}`$, so the conclusion holds for an arbitrary integer digit sequence.

The factorisation and cancellation are the [odd-denominator doubling lemma](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L426); the orbit form is the [odd-denominator state theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L461); and the quantified conclusion is the [eventual integral-shift theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L477).

The useful contrapositive is stated for a real recurrence. Call its shifts *cofinally non-integral* when, for every fixed $`h\ge1`$ and every threshold $`N_0`$, some $`N\ge N_0`$ has $`\sigma_h(N)\notin\mathbb{Z}`$.

<div id="res:escape-irrational" class="theorem">

**Theorem 11** (cofinal shift escape implies irrationality). *Let $`T:\mathbb{N}\to\mathbb{R}`$ satisfy $`T_{N+1}=2T_N-g_{N+1}`$ with integer $`g`$. If its shifts are cofinally non-integral, then $`T_0`$ is irrational.*

</div>

<div class="proof">

*Proof.* If $`T_0`$ were rational, the whole real orbit would be the cast of the rational orbit with that initial value. Theorem <a href="#res:collapse" data-reference-type="ref" data-reference="res:collapse">10</a> would then produce one $`h\ge1`$ whose shifts are integral at every sufficiently large index, contradicting cofinal non-integrality. ◻

</div>

Lean checks the real recurrence and shift definitions as [real dyadic recurrence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L492) and [real shift](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L496), the rational-orbit transport as the [rational-orbit cast theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L515), cofinal non-integrality as the [cofinal shift-escape predicate](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L528), and Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">11</a> as the [cofinal-escape irrationality theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L537).

<a id="the-actual-prime-gap-orbit."></a>

#### The actual prime-gap orbit.

Define, at paper level,
``` math
\mathcal T_N=\sum_{j\ge1}\frac{g_{N+j}}{2^j}.
```
The prime number theorem gives convergence, and an index shift gives
``` math
\mathcal T_{N+1}=2\mathcal T_N-g_{N+1}.
```
If $`G=\sum_{n\ge0}g_n/2^{n+1}`$, then $`\mathcal T_0=2G-g_0=2G-1`$. Together with Theorem <a href="#res:infinite" data-reference-type="ref" data-reference="res:infinite">3</a>, this shows that $`\Pi`$, $`G`$, and $`\mathcal T_0`$ have the same rationality status. Thus Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">11</a> applies directly to Problem #251 once cofinal shift escape is proved for $`\mathcal T`$. This last analytic instantiation is proved here from the classical prime number theorem; it is not yet a Lean declaration. The abstract theorem, including its real/rational transport, is kernel-checked.

<a id="sec:local-certificate"></a>

## Two adjacent small shifts cannot both be integral

Applying Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">11</a> requires cofinal non-integrality, which is a condition of infinite precision imposed on a complete tail. The key point is that inside the open interval $`(-1,1)`$ integrality is equality with zero, so on that range the one-step shift recurrence
``` math
\sigma_h(N+1)=2\sigma_h(N)-\bigl(g_{N+h+1}-g_{N+1}\bigr)
```
turns simultaneous integrality of two adjacent shifts into a single comparison of digits. An infinite-tail condition thereby becomes a bounded local certificate, and the distance of a shift from the integers never has to be estimated.

<div id="res:smallpair" class="theorem">

**Theorem 12** (adjacent small-shift obstruction). *Let $`T:\mathbb{N}\to\mathbb{Q}`$ satisfy the dyadic tail recurrence with integer digits $`g`$. Fix $`h`$ and $`N`$. If
``` math
-1<\sigma_h(N)<1,\qquad -1<\sigma_h(N+1)<1,
 \qquad g_{N+h+1}\ne g_{N+1},
```
then $`\sigma_h(N)`$ and $`\sigma_h(N+1)`$ cannot both be integral. Consequently, if such a pair occurs beyond every threshold, the $`h`$-shift is not eventually integral.*

</div>

<div class="proof">

*Proof.* An integral rational strictly between $`-1`$ and $`1`$ is zero. If both shifts were integral, both would therefore vanish, and substitution in the displayed shift step identity would give $`g_{N+h+1}=g_{N+1}`$, a contradiction. The cofinal statement chooses one such adjacent pair after the alleged onset of integrality. ◻

</div>

The finite contradiction is the [adjacent small-shift obstruction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L626); its quantified form is the [cofinal small-mismatch theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L653); and the actual-prime-gap specialisation is the [prime-gap specialisation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L723). Theorem <a href="#res:smallpair" data-reference-type="ref" data-reference="res:smallpair">12</a> is conditional on its two tail inequalities; no theorem asserting that such pairs occur is claimed here.

<div id="res:gap-nonperiodic" class="proposition">

**Proposition 13** (prime gaps do not become periodic). *For every positive $`h`$, the actual consecutive-prime-gap sequence is not eventually periodic with period $`h`$.*

</div>

<div class="proof">

*Proof.* The gaps are unbounded, by the standard construction: the interval from $`n!+2`$ to $`n!+n`$ contains no prime. Far stronger lower bounds for large gaps are known \[fgkmt2018\], but unboundedness is all that is needed. An eventually periodic natural-valued sequence has finite range after its preperiod, while its finite initial segment is bounded as well; hence it is bounded, a contradiction. ◻

</div>

Lean checks the factorial argument as [unboundedness of the actual gaps](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L51) and the conclusion as [non-eventual periodicity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L670). Combining nonperiodicity with eventual strict smallness of one positive shift would also exclude eventual integrality, but eventual smallness at every sufficiently large index is stronger than the cofinal adjacent-pair hypothesis in Theorem <a href="#res:smallpair" data-reference-type="ref" data-reference="res:smallpair">12</a> and is not asserted here.

<a id="sec:carry"></a>

# Nonperiodic coefficients with a rational sum

One might hope that rationality of a dyadic series forces its integer coefficient stream to be eventually periodic, and then try to contradict the nonperiodicity of the prime gaps. The following identity gives a direct counterexample to that first implication.

Let $`K:\mathbb{N}\to\mathbb{Q}`$ be arbitrary and put $`\kappa_n=2K_n-K_{n+1}`$: the [carry coefficient](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L738).

<div id="res:telescope" class="proposition">

**Proposition 14** (exact telescoping). *For every $`n\ge0`$,
``` math
\sum_{i=0}^{n-1}\frac{\kappa_i}{2^{\,i+1}}=K_0-\frac{K_n}{2^{\,n}} .
```*

</div>

<div class="proof">

*Proof.* A routine induction on $`n`$; the added term is $`(2K_n-K_{n+1})/2^{\,n+1}=K_n/2^{\,n}-K_{n+1}/2^{\,n+1}`$. ◻

</div>

Formalised as the [carry telescoping identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L747), on the [carry partial sum](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L742). When the carries are natural numbers and $`K_{n+1}\le2K_n`$, the coefficients are natural numbers and the two readings agree, the [natural-carry cast](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L763).

<a id="consequence-for-the-coefficient-stream."></a>

#### Consequence for the coefficient stream.

If $`K_n2^{-n}\to0`$, the emitted partial sums converge to $`K_0`$. For the explicit choice $`K_n=n`$ one has
``` math
\kappa_n=n-1,\qquad
 \sum_{i=0}^{n-1}\frac{\kappa_i}{2^{\,i+1}}
   =-\frac{n}{2^n}\longrightarrow0.
```
The coefficient stream is unbounded and therefore not eventually periodic, although its dyadic sum is rational. Thus rationality alone cannot imply eventual periodicity of an unrestricted integer coefficient stream. This does not classify which streams occur, and it does not show that a prescribed prime-gap pattern is emitted by a bounded or nonnegative carry.

<a id="sec:open"></a>

# Complements and further questions

Problem #251 is open.

<div id="prob:escape" class="problem">

**Problem 15** (minimal prime-gap shift escape). For every $`h\ge1`$ and every $`N_0`$, prove that some $`N\ge N_0`$ satisfies
``` math
\sum_{j\ge1}
 \frac{g_{N+h+j}-g_{N+j}}{2^j}\notin\mathbb{Z}.
\tag{5.1}\label{eq:shift-escape}
```

</div>

The series in <a href="#eq:shift-escape" data-reference-type="eqref" data-reference="eq:shift-escape">[eq:shift-escape]</a> is exactly $`\mathcal T_{N+h}-\mathcal T_N`$. Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">11</a> therefore turns any solution of Problem <a href="#prob:escape" data-reference-type="ref" data-reference="prob:escape">15</a> directly into irrationality of $`\Pi`$. The quantifier over $`h`$ is essential: a hypothetical rational value chooses a shift length from the odd part of its reduced denominator, and that length is not known in advance.

<div id="prob:smallpair" class="problem">

**Problem 16** (cofinal adjacent small mismatch). For every fixed $`h\ge1`$ and every $`N_0`$, prove that some $`N\ge N_0`$ satisfies
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

The two sums are adjacent $`h`$-shifts. Theorem <a href="#res:smallpair" data-reference-type="ref" data-reference="res:smallpair">12</a> turns each instance of <a href="#eq:smallpair" data-reference-type="eqref" data-reference="eq:smallpair">[eq:smallpair]</a> into a finite contradiction to simultaneous integrality. A cofinal family of such pairs therefore proves Problem <a href="#prob:escape" data-reference-type="ref" data-reference="prob:escape">15</a>; Theorem <a href="#res:escape-irrational" data-reference-type="ref" data-reference="res:escape-irrational">11</a> then gives irrationality of the gap series, and Corollary <a href="#res:irr-equivalence" data-reference-type="ref" data-reference="res:irr-equivalence">4</a> transfers it to $`\Pi`$. This formulation deliberately asks only for sporadic adjacent pairs; the stronger assertion that a fixed shift is eventually always smaller than one is unnecessary.

Several natural prime-distribution inputs are insufficient. Isolated small gaps, isolated large gaps, average gap estimates, and the occurrence of any one fixed finite pattern do not suffice: both inequalities in <a href="#eq:smallpair" data-reference-type="eqref" data-reference="eq:smallpair">[eq:smallpair]</a> contain the complete infinite continuation. Nor does parity: after the first gap all $`g_n`$ are even. Unboundedness and non-eventual-periodicity of the actual gaps, though now checked, do not imply the required small-tail recurrence. In particular, Section <a href="#sec:carry" data-reference-type="ref" data-reference="sec:carry">4</a> shows that no argument can deduce eventual periodicity from rationality alone.

<a id="a-finite-truncation-criterion."></a>

#### A finite truncation criterion.

Both problems above are stated in terms of infinite tails, but a dominated truncation reduces the first of them to a finite quantity. For $`L\ge1`$ put
``` math
S_{h,N,L}=\sum_{j=1}^{L}
 \frac{g_{N+h+j}-g_{N+j}}{2^j}.
```

<div id="res:truncation" class="proposition">

**Proposition 17** (finite truncation). *Let $`M(n)\ge g_n`$ for every $`n`$, assume that the series below converges, and put
``` math
R_{h,N,L}(M)=
 \sum_{j>L}\frac{M(N+h+j)+M(N+j)}{2^j}.
```
Suppose that for every fixed $`h\ge1`$ and every $`N_0`$ there exist $`N\ge N_0`$ and $`L\ge1`$ with
``` math
\operatorname{dist}(S_{h,N,L},\mathbb{Z})>R_{h,N,L}(M).
\tag{5.3}\label{eq:truncation}
```
Then Problem <a href="#prob:escape" data-reference-type="ref" data-reference="prob:escape">15</a> holds.*

</div>

<div class="proof">

*Proof.* The part of $`\sum_{j\ge1}(g_{N+h+j}-g_{N+j})2^{-j}`$ omitted from $`S_{h,N,L}`$ has absolute value at most $`R_{h,N,L}(M)`$, so under <a href="#eq:truncation" data-reference-type="eqref" data-reference="eq:truncation">[eq:truncation]</a> the full sum lies at positive distance from every integer. ◻

</div>

The last distance-to-integers inference is Lean-checked as the generic [finite-approximation certificate](https://github.com/wcook04/plectis-lean-erdos249-257/blob/7558c58afb7cb0046dbd3101c1b3187ccdac5909/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L772): an error at most $`R`$ cannot reach an integer when the approximation is farther than $`R`$ from every integer. The prime-gap tail bound, the convergence used above, and the existence of blocks satisfying <a href="#eq:truncation" data-reference-type="eqref" data-reference="eq:truncation">[eq:truncation]</a> are not consequences of that formal theorem.

Taking the classical bound $`M(n)\ll n\log n`$, a choice $`L=\lceil A\log_2(N+h+2)\rceil`$ with any fixed $`A>1`$ makes the right side a negative power of $`N`$ up to logarithms. Thus <a href="#eq:truncation" data-reference-type="eqref" data-reference="eq:truncation">[eq:truncation]</a> asks for a finite dyadic anti-concentration estimate on a logarithmic-length block, not control of an infinite tail and not eventual periodicity of the full gap word. For Problem <a href="#prob:smallpair" data-reference-type="ref" data-reference="prob:smallpair">16</a>, the same truncation must certify two adjacent full-tail values inside the open unit interval, together with the displayed gap mismatch. A finite prefix is useful only when its omitted tail is rigorously dominated.

What <a href="#eq:truncation" data-reference-type="eqref" data-reference="eq:truncation">[eq:truncation]</a> requires is joint control of the weighted difference word $`(g_{N+h+1}-g_{N+1},\ldots,g_{N+h+L}-g_{N+L})`$ modulo powers of two along a block of logarithmic length. We do not know how to obtain such control and we make no progress on it here. The strongest results on prime gaps address a different shape of question: the bounded-gap theorems of Zhang \[zhang2014\] and Maynard \[maynard2015\] produce infinitely many small individual gaps, and the large-gap theorem of Ford, Green, Konyagin, Maynard and Tao \[fgkmt2018\] produces extreme individual gaps, whereas <a href="#eq:truncation" data-reference-type="eqref" data-reference="eq:truncation">[eq:truncation]</a> needs the joint dyadic distribution of a whole block of consecutive gap differences. None of the cited results supplies that estimate.

<a id="what-remains-to-be-formalised."></a>

#### What remains to be formalised.

The abstract irrationality theorem and the prime-specific local small-mismatch theorem are Lean-checked, as is the generic finite-approximation certificate used in Proposition <a href="#res:truncation" data-reference-type="ref" data-reference="res:truncation">17</a>. The local source still takes summability of the prime series as a hypothesis and does not define $`\mathcal T_N`$ by an infinite sum; the prime-number-theorem comparison and the identification of that concrete tail with the checked real recurrence are paper proofs. Its prime-gap tail domination and anti-concentration hypotheses also remain paper-level obligations. No theorem supplies the cofinal pairs in <a href="#eq:smallpair" data-reference-type="eqref" data-reference="eq:smallpair">[eq:smallpair]</a>, and none of the prime-distribution estimates described above is claimed or formalised.

<a id="statements-and-declarations"></a>

## Statements and declarations

<a id="artefact-and-data-availability."></a>

#### Artefact and data availability.

The [pinned formal-source revision](https://github.com/wcook04/plectis-lean-erdos249-257/tree/7558c58afb7cb0046dbd3101c1b3187ccdac5909) contains the Lean sources, the fixed toolchain, and the library manifest used in the verification. This manuscript provides navigation rather than proof authority.

<a id="declaration-of-generative-ai-use."></a>

#### Declaration of generative AI use.

Large-language-model agents were used throughout development to draft and revise prose, formal proofs, and software. The author set the objectives and acceptance criteria, selected and reviewed the claims, and approved the published version. The author assumes responsibility for the accuracy, interpretation, and presentation of the work. Generative systems are production tools; they are not authors and supply no independent authority. Lean checks each proof term against the fixed library version, and the sources linked here contain no proof placeholders and no project-defined axioms; Lean does not authorise the exposition, the citation choices, or the interpretation, for which the author remains responsible.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem numbering and status follow the Erdős Problems catalogue maintained by Thomas Bloom \[erdosproblems\].

<a id="app:index"></a>

# Guide to the formal sources

Each linked phrase opens its Lean declaration at the pinned source revision 7558c58afb7c. All declarations of this note live in one module. The summation-by-parts declarations are prime-specific; most of Section <a href="#sec:tail" data-reference-type="ref" data-reference="sec:tail">3</a> is stated for arbitrary integer digits and arbitrary rational or real orbits, while Section <a href="#sec:local-certificate" data-reference-type="ref" data-reference="sec:local-certificate">3.1</a> records the actual-gap specialisation. The concrete prime-gap tail and its convergence are paper-level consequences of the prime number theorem; they are not definitions in the pinned Lean module.

<div class="thebibliography">

99

P. Erdős, [*Sur certaines séries à valeur irrationnelle*](https://users.renyi.hu/~p_erdos/1958-08.pdf), Enseign. Math. (2) **4** (1958), 93–100. MR 98732. P. Erdős and R. L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf), Monogr. Enseign. Math. 28, Geneva, 1980, p. 62. P. Erdős, *On the irrationality of certain series: problems and results*, in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). P. Erdős and E. G. Straus, *On the irrationality of certain Ahmes series*, J. Indian Math. Soc. (N.S.) **27** (1963), 129–133. K. Ford, B. Green, S. Konyagin, J. Maynard and T. Tao, *Long gaps between primes*, J. Amer. Math. Soc. **31** (2018), 65–105. V. Kovač and T. Tao, [*On several irrationality problems for Ahmes series*](https://doi.org/10.1007/s10474-025-01528-0), Acta Math. Hungar. **175** (2025), 572–608. L. de Moura and S. Ullrich, *The Lean 4 theorem prover and programming language*, in A. Platzer and G. Sutcliffe (eds.), CADE 28, Lecture Notes in Comput. Sci. 12699, Springer, 2021, pp. 625–635. The mathlib Community, *The Lean mathematical library*, in CPP 2020, ACM, 2020, pp. 367–381. J. Maynard, *Small gaps between primes*, Ann. of Math. (2) **181** (2015), 383–413. H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*, Cambridge Stud. Adv. Math. 97, Cambridge UP, 2007, Chapter 6. Y. Zhang, *Bounded gaps between primes*, Ann. of Math. (2) **179** (2014), 1121–1174. T. F. Bloom, [*Erdős Problem \#251*](https://www.erdosproblems.com/251), `erdosproblems.com/251`, accessed 22 July 2026. ChatGPT 5.4 Pro (orchestrated by V. Kovač), [*On the Erdős problem \#251*](https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_251.pdf), unpublished note, 2026. The Formal Conjectures Authors, [*FormalConjectures.ErdosProblems.`251`*](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/251.lean), Lean source, 2025, accessed 27 July 2026.

</div>
