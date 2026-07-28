<a id="erdos249-257-main-paper"></a>

# Tail Certificates and Achievement-Set Geometry Lean-checked exact reductions for Erdős #249 and the half-value branch of Erdős #257

<a id="abstract"></a>

## Abstract

For the totient constant $`S=\sum_{n\ge1}\varphi(n)/2^n`$ of Erdős #249 and the Mersenne support sums $`\sum_{n\in A}(2^n-1)^{-1}`$ of Erdős #257, rationality would force discrete structure. For $`S`$, its binary tails would eventually repeat. For a support sum, binary long division would give an integer carry recurrence whose Möbius-inverted quotients are all $`0`$ or $`1`$. We formalise both statements in Lean. We also express \#249 and the distinguished half-value counterexample route to \#257 in terms of finite witnesses: each of these two conclusions is equivalent to such witnesses occurring beyond every bound. This chain does not reformulate the universal \#257 assertion. A finite exact calculation excludes every rational representation $`S=p/q`$ with $`q\le Q_0\approx7.96\times10^{34}`$; hence a rational representation must have $`q>Q_0`$. Irrationality of $`S`$ is also equivalent to non-integrality of every positive binary tail difference, to complete finite certificates at fixed parameters, and to an unbounded certificate supply along a one-parameter sequence of least-common-multiple tests. Certificates are verified at the 28 changing scales through $`t=64`$ (including the initial scale); this is finite evidence only, and the unbounded supply is open. A construction using the Chinese remainder theorem and Dirichlet’s theorem also proves that the residue-class subsequences $`n\mapsto\varphi(2^j n+r)`$ span an infinite-dimensional space: a canonical level-$`e`$ family has exact dimension $`2^e+1`$. If $`S`$ were rational, binary long division would instead produce an integer state sequence of subexponential growth whose level-$`e`$ residue-class subsequences span at least $`2^e-1`$ dimensions. No matching upper bound is known, so this does not prove irrationality.

For Erdős #257, we formalise Erdős’s classical theorem for full support in every base and several structured-support cases. At base $`2`$ we prove the geometry of the achievement set (the set of all support sums) and necessary carry and gap constraints on hypothetical rational infinite supports. In particular, consecutive stretches on which the divisor-count function $`f_A(m)=\#\{a\in A:a\mid m\}`$ vanishes have sublogarithmic length, uniformly in the support. Membership of $`1/2`$, which would refute the universal statement, is exactly equivalent to infinitely many greedy skips. Nonmembership is exactly equivalent both to a finite fatal gap and to the existence of a final greedy skip.

After a putative final skip, the current argument excludes the upper transition and the carry value $`-3`$. The same finite-state analysis leaves two negative carry values, $`-2`$ and $`-1`$, and a future-tail inequality for the nonnegative carries. Both series arise from one Lambert transform; this explains their common coordinates but transfers no theorem between them. Neither the required unbounded \#249 certificate supply nor the required recurrence of \#257 greedy skips is proved. The universal \#257 statement and half-value membership remain open. Neither problem is settled.

<a id="sec:intro"></a>

# Introduction

The two questions are whether $`S=\sum_{n\ge1}\varphi(n)/2^n`$ is irrational (#249), and whether $`\sum_{n\in A}(2^n-1)^{-1}`$ is irrational for every infinite $`A\subseteq\mathbb{N}_{>0}`$ (#257). Here $`\varphi(n)`$ is Euler’s totient, the number of integers from $`1`$ to $`n`$ that are coprime to $`n`$. Problem \#249 appears on p. 61 of Erdős–Graham and p. 102 of Erdős’s survey \[erdosgraham1980, p. 61\]\[erdos1988, p. 102\]; problem \#257 appears on pp. 62 and 105, respectively \[erdosgraham1980, p. 62\] \[erdos1988, p. 105\]. Numbering follows Bloom’s catalogue \[erdosproblems\]. Neither problem is settled.

Throughout, $`\mathbb{N}=\{0,1,2,\ldots\}`$ and $`\mathbb{N}_{>0}=\{1,2,3,\ldots\}`$. A *support* $`A\subseteq\mathbb{N}_{>0}`$ selects terms of the \#257 series, and its sum belongs to the corresponding *achievement set* $`\mathcal A`$. Exponent $`0`$ is excluded because $`2^0-1=0`$. An infinite support with sum $`1/2`$ would therefore refute the universal assertion in \#257.

<a id="what-is-proved"></a>

## What is proved

The paper separates finite arithmetic from the remaining infinite quantifier. A *certificate* is a finite integer calculation that proves an exact assertion about an infinite tail. A *carry* is an integer state in binary long division, and *cofinally* means beyond every prescribed bound. The two displayed chains below connect finite statements to open cofinal statements. In both reductions, tail and carry identities separate exact finite arithmetic from one analytic or combinatorial cofinality statement:
``` math
\begin{aligned}
 \text{cofinally many lcm-diagonal certificates}
 &\quad\Longleftrightarrow\quad S\notin\mathbb{Q},\\[4pt]
 \text{cofinally many greedy terminal zeros}
 &\quad\Longleftrightarrow\quad \dfrac12\in\mathcal A,\\[-1pt]
 &\quad\Longrightarrow\quad \text{a counterexample to universal \#257}.
 \end{aligned}
```
The first line is an exact reformulation of \#249. The second is an exact reformulation of the distinguished half-value route, not of universal \#257. An unbounded certificate supply and cofinal terminal zeros are both open. The current final-skip analysis reduces the second statement further to two final-skip obligations; neither obligation is proved.

The totient constant also has the elementary form
``` math
S=\frac12+\Pr(\gcd(X,Y)=1),
```
where $`X,Y\in\mathbb{N}_{>0}`$ are independent and $`\Pr(X=n)=\Pr(Y=n)=2^{-n}`$. Both series are values of one Lambert transform, but this common description transfers no theorem from one problem to the other; Section <a href="#sec:architecture" data-reference-type="ref" data-reference="sec:architecture">6</a> gives the exact map.

<div class="center">

| Question or result | Status | What is proved |
|:---|:---|:---|
| Irrationality in \#249 | Open | No proof of $`S\notin\mathbb{Q}`$ is claimed. |
| Denominator exclusion | Proved | If $`S=p/q`$, then $`q>Q_0`$. |
| Tail and lcm-diagonal forms | Exact equivalences | The unbounded supply is equivalent to $`S\notin\mathbb{Q}`$, but remains open. |
| Diagonal computation | Finite evidence | Lean checks 28 diagonal certificates through $`t=64`$; this is not cofinal. |
| Universal assertion in \#257 | Open | No proof covers every infinite support. |
| Full and structured supports | Classical/formalised | Full support and several restricted families are proved irrational. |
| Membership of $`1/2`$ | Open; exact reductions | Greedy and carry laws identify necessary events without proving they occur. |

</div>

<a id="what-lean-checked-means-here."></a>

#### What “Lean-checked” means here.

A linked theorem statement has a proof term accepted by Lean from the pinned source and dependencies. An exact equivalence remains an equivalence even when both sides are open; a finite calculation remains finite; and a theorem with a rationality hypothesis does not prove that a rational support exists. The manuscript, its link checker, and its generated indexes help a reader find the proof but are not themselves proof authority. The release section states the additional source-pin and trust checks required for a reproducible copy.

<a id="reading-map."></a>

#### Reading map.

Section <a href="#sec:spines" data-reference-type="ref" data-reference="sec:spines">2</a> states the two exact reductions, and Section <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a> introduces their common coordinates. Sections <a href="#sec:eb" data-reference-type="ref" data-reference="sec:eb">4</a> and <a href="#sec:249" data-reference-type="ref" data-reference="sec:249">5</a> give the \#257 and \#249 results. Section <a href="#sec:architecture" data-reference-type="ref" data-reference="sec:architecture">6</a> explains the shared transform and the limits of the comparison. Sections <a href="#sec:verify" data-reference-type="ref" data-reference="sec:verify">7</a> and <a href="#sec:further" data-reference-type="ref" data-reference="sec:further">8</a> give the verification protocol and remaining open problems. The appendices contain the local arguments and audit tables. Linked phrases open the corresponding Lean proofs.

**Keywords.** irrationality; Erdős–Borwein constant; Euler totient; Lambert series; achievement sets; binary carry systems; Lean 4. **MSC 2020.** 11J72 (primary); 11A25, 68V20 (secondary).

<a id="sec:spines"></a>

# The two exact reductions

<a id="res:249story"></a>

## Erdős \#249: an exact certificate normal form

Write
``` math
R_N=\sum_{m\geq1}\frac{\varphi(N+m)}{2^m}.
```
Each $`R_N`$ is $`2^NS`$ minus an integer. Rationality of $`S`$ would force one binary period $`h`$ whose tail differences $`R_{N+h}-R_N`$ are eventually all integral; the certificates below refute exactly such candidate periods (Section <a href="#sec:reduction" data-reference-type="ref" data-reference="sec:reduction">5.3</a>).

<a id="exact-reduction."></a>

#### Exact reduction.

The formal source proves the exact chain
``` math
\begin{split}
 S\notin\mathbb{Q}
 &\quad\Longleftrightarrow\quad
   R_{N+h}-R_N\notin\mathbb{Z}
   \quad\text{for every }h>0\text{ and every }N\\
 &\quad\Longleftrightarrow\quad
   \text{for every }h>0,N\text{ there is an }L
   \text{ with }\mathsf{Sep}(h,N,L).
\end{split}
```
Here $`\mathsf{Sep}(h,N,L)`$ is a finite residue computation with a rigorous tail allowance. At fixed $`h,N`$, some depth succeeds exactly when the tail difference is non-integral; integrality of one positive-shift difference forces $`S`$ to be rational. These statements are the [tail-difference equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeFlatness.lean#L386), [pointwise certificate equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeFlatness.lean#L399), and the fixed-parameter [certificate-completeness theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeFlatness.lean#L316).

<a id="unconditional-finite-baseline."></a>

#### Unconditional finite baseline.

Independently of the unbounded certificate supply, if $`S=p/q`$, then
``` math
q>Q_0
 =79\,639\,646\,646\,701\,375\,323\,355\,774\,875\,831\,053.
```
This is the [denominator exclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L18056).

<a id="missing-theorem."></a>

#### Missing theorem.

An unbounded certificate supply is the exact open statement: for every positive $`h`$, non-integral differences $`R_{N+h}-R_N`$ occur at arbitrarily large $`N`$. Theorem <a href="#res:diag" data-reference-type="ref" data-reference="res:diag">26</a> gives the equivalent one-parameter lcm-diagonal form. The 28 changing-lcm scales through $`t=64`$ are verified, but neither this finite computation nor the denominator bound proves the unbounded supply.

<a id="res:halfstory"></a>

## Erdős \#257: the exact half-value counterexample reduction

Let
``` math
\mathcal A=\left\{\sum_{n\in A}\frac1{2^n-1}:A\subseteq\mathbb{N}_{>0}\right\}.
```

<a id="exact-reduction-and-finite-exclusion."></a>

#### Exact reduction and finite exclusion.

The weights satisfy $`w_n>\sum_{m>n}w_m`$, so a value has at most one support $`A\subseteq\mathbb{N}_{>0}`$. No finite such support can have value $`1/2`$. For $`1/2`$, the following are equivalent:
``` math
\begin{aligned}
\frac12\in\mathcal A
&\quad\Longleftrightarrow\quad
\text{the set of exponents omitted by the greedy expansion is infinite}\\
&\quad\Longleftrightarrow\quad
\text{a successor terminal bit equal to zero occurs beyond every bound}
\end{aligned}
```
(the terminal bit is defined in Section <a href="#sec:eb" data-reference-type="ref" data-reference="sec:eb">4</a>). Concretely, the greedy expansion of $`1/2`$ skips rank $`1`$, takes ranks $`2,3`$, skips $`4,5`$, and takes $`6,7`$; membership asks whether such skips recur beyond every bound.

<a id="counterexample-consequence."></a>

#### Counterexample consequence.

Membership would produce an infinite support of rational sum and refute the universal statement of Erdős #257. Thus the counterexample condition is exact: cofinally many terminal zeros, equivalently no last greedy skip. The formal statements are the [infinite-skip equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L2514), [unbounded-terminal equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L126), [no-last-skip equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L235), and the [finite-support exclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryReachability.lean#L589).

<a id="missing-theorem.-1"></a>

#### Missing theorem.

The missing input is a proof that terminal zeros occur cofinally. The current last-skip route proves that, after a putative last skip, neither the upper transition nor middle carry $`-3`$ can occur. It remains to exclude middle carries $`-2,-1`$ and to prove a future-tail inequality for the remaining nonnegative middle carries. Neither statement is known for the greedy orbit. The exact conditional implication is the [remaining-tail implication](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderLastProducerContradiction.lean#L387). Proposition <a href="#res:finalskipexclusions" data-reference-type="ref" data-reference="res:finalskipexclusions">18</a> gives the local exclusions and Corollary <a href="#res:taildominance" data-reference-type="ref" data-reference="res:taildominance">19</a> states the sufficient global hypothesis.

<a id="prior-art-boundary."></a>

#### Prior-art boundary.

Prior results are cited at their first use in the body, beginning in Section <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a>. No priority claim is made for the reductions above.

<a id="sec:ladder"></a>

# The Mersenne–Lambert ladder

Whenever $`\sum_{n\ge1}|f(n)|/(2^n-1)<\infty`$, define the Lambert transform by
``` math
L(f)\;=\;\sum_{n\ge1}\frac{f(n)}{2^n-1}\;=\;\sum_{m\ge1}\frac{(f*\mathbf 1)(m)}{2^m},
\qquad (f*\mathbf 1)(m)=\sum_{d\mid m} f(d),
```
the second equality being the absolutely convergent Lambert rearrangement (one Dirichlet convolution by the constant arithmetic function $`\mathbf 1`$); Apostol supplies the classical arithmetic-function and Dirichlet-convolution background \[apostol\]; Merca introduced a modern Lambert-series factorisation theorem \[merca2017\], and Merca–Schmidt give a synthesis/unification treatment \[mercaschmidt\]. It is convenient to read the rearrangement as a composite of two maps: the divisor transform $`f\mapsto f*\mathbf 1`$, followed by evaluation of the resulting coefficient stream at binary scales, $`\gamma\mapsto\sum_{m\ge1}\gamma(m)2^{-m}`$. Every series in this paper is the image of an arithmetic input under this composite; Section <a href="#sec:architecture" data-reference-type="ref" data-reference="sec:architecture">6</a> uses that observation to place the open questions in one frame. Three inputs form the convolution chain
``` math
\alpha \xrightarrow{*\mathbf 1} \varphi
 \xrightarrow{*\mathbf 1} \mathrm{Id},
 \qquad \alpha=\varphi*\mu,
```
whereas $`\mu`$ and $`\mathbf 1`$ are comparison inputs. The corresponding values have the following statuses.

<div class="center">

<div class="tabular">

@llll@ input $`f`$ & value & mathematical status & treatment here\
\
$`\alpha=\varphi*\mu`$ & $`L(\alpha)=S`$ & open (#249) & identities and bounds formalised\
$`\varphi`$ & $`L(\varphi)=2`$ & rational & formalised\
$`\mathrm{Id}`$ & $`L(\mathrm{Id})=\sum\sigma(m)/2^m`$ & transcendental & cited \[nesterenko\]\
\
$`\mu`$ & $`L(\mu)=1/2`$ & rational & formalised\
$`\mathbf 1`$ & $`L(\mathbf 1)=E`$ & irrational & formalised\

</div>

</div>

The transcendental row is a direct specialization of Nesterenko’s transcendence-degree theorem. Since $`E_2(q)=1-24\sum_{m\ge1}\sigma(m)q^m`$, its specialization at the algebraic point $`q=1/2`$ implies that $`L(\mathrm{Id})=\sum_{m\ge1}\sigma(m)/2^m`$ is transcendental \[nesterenko\].

The nonnegative weight $`\alpha=\varphi*\mu`$ satisfies $`\alpha*\mathbf 1=\varphi`$; for example, $`\alpha(p)=p-2`$ on primes. The rows for $`\mu`$ and $`\mathbf 1`$ are separate comparisons, not further steps in the displayed chain. Thus the known rationality or transcendence of one row does not transfer to another. In particular, $`S`$ and $`E`$ have the same Mersenne-denominator form, with weights $`\alpha`$ and $`\mathbf 1`$, but no convolution step carries one weight to the other.

<div class="proposition">

**Proposition 1** (Möbius rational rung).
*``` math
\sum_{d\ge1}\frac{\mu(d)}{2^d-1}=\frac12.
```*

</div>

Formalised as the [Möbius rung](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/MersenneLambertLadder.lean#L587). The value is transparent in the rearranged coordinates: by Möbius inversion $`(\mu*\mathbf 1)(m)=1`$ exactly when $`m=1`$, so the divisor stream of $`\mu`$ is $`1,0,0,\ldots`$ and the rearranged series is $`2^{-1}`$.

<div class="proposition">

**Proposition 2** (totient rational rung).
*``` math
\sum_{d\ge1}\frac{\varphi(d)}{2^d-1}=2.
```*

</div>

Formalised as the [totient rung](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/MersenneLambertLadder.lean#L575).

<div id="res:lift" class="proposition">

**Proposition 3** (positive lift). *With the primitive-conductor weight $`\alpha=\varphi*\mu`$,
``` math
\sum_{d\ge1}\frac{\alpha(d)}{2^d-1}\;=\;\sum_{n\ge1}\frac{\varphi(n)}{2^n}\;=\;S.
```*

</div>

The first equality is formalised as the [positive-lift identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L18117). The second is the definition of $`S`$. The proposition places $`S`$ in the same $`\sum(\cdot)/(2^d-1)`$ family as $`E`$, with the nonnegative weight $`\alpha`$.

<a id="probabilistic-reading."></a>

#### Probabilistic reading.

If $`X,Y`$ are independent fair-coin waiting times, $`\Pr(X=n)=2^{-n}`$, then
``` math
S=\tfrac12+\Pr(\gcd(X,Y)=1).
```
Thus Erdős #249 also asks whether the probability that two independent fair-coin waiting times are coprime is irrational. The exact identity is Proposition <a href="#res:coprime" data-reference-type="ref" data-reference="res:coprime">21</a>; its Möbius-square form and the periodic and finite-algebraic variants of the ladder are collected in Appendices <a href="#app:lambert-weighted" data-reference-type="ref" data-reference="app:lambert-weighted">[app:lambert-weighted]</a>–<a href="#app:lambert-algebraic" data-reference-type="ref" data-reference="app:lambert-algebraic">12.2</a>.

<a id="what-this-section-provesand-does-not-prove."></a>

#### What this section proves—and does not prove.

The exact contribution of this section is the coordinate change $`L(\alpha)=S`$, together with the two separate rational-rung propositions above. The convolution chain relates $`S`$ to rational and transcendental neighbouring values, while the comparison inputs place $`1/2`$ and $`E`$ in the same transform. No status transfers from one input to another. For \#249 the remaining issue is still the unbounded certificate supply isolated in Section <a href="#sec:249" data-reference-type="ref" data-reference="sec:249">5</a>; for \#257 the ladder supplies context rather than either the universal theorem or a rational counterexample.

<a id="sec:eb"></a>

# Erdős–Borwein-type irrationality (the \#257 direction)

There are two logically distinct directions. The universal direction asks for irrationality for every infinite support; the counterexample direction asks for one infinite support with rational value. The target $`1/2`$ gives an exact formulation of one distinguished route. This section states the classical and structured irrationality theorems, then gives the base-$`2`$ achievement-set geometry and the constraints forced by a hypothetical rational value. It ends with the exact classification of the target $`1/2`$ and the exact residual condition left by the current final-skip argument. The final-skip analysis is developed in Appendix <a href="#app:half-final-skip" data-reference-type="ref" data-reference="app:half-final-skip">9.4</a>; Appendices <a href="#app:half-conditional-producers" data-reference-type="ref" data-reference="app:half-conditional-producers">9.2</a>–<a href="#app:half-finite-cofinal" data-reference-type="ref" data-reference="app:half-finite-cofinal">9.3</a> give alternative sufficient conditions; and Appendix <a href="#app:half-evidence" data-reference-type="ref" data-reference="app:half-evidence">9.5</a> records finite evidence, coordinate changes, and eliminated special cases. These are auxiliary implications, not additional conclusions of this section.

<a id="full-support-the-erdősborwein-constant-every-base"></a>

## Full support: the Erdős–Borwein constant, every base

<div id="res:full" class="theorem">

**Theorem 4** (full-support irrationality). *For every integer $`b\ge2`$, the series $`\displaystyle\sum_{n\ge1}\frac{1}{b^n-1}`$ is irrational. In particular the Erdős–Borwein constant $`E=\sum_{n\ge1}1/(2^n-1)`$ is irrational.*

</div>

The [all-base theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L8000) and its [base-$`2`$ corollary](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L8007) are formalised. This is Erdős’s 1948 theorem \[erdos1948\]. In the ladder of Section <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a> it is the rung $`L(\mathbf 1)`$, and it is the fixed machine-checked comparison point in the same Mersenne–Lambert family as the open $`S`$; as Section <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a> notes, it is not a further convolution step from $`S`$.

The proof begins with the Lambert identity
``` math
\sum_{n\geq 1}\frac{1}{b^n-1}
   =\sum_{m\geq 1}\frac{\tau(m)}{b^m},
```
where $`\tau(m)`$ is the number of positive divisors of $`m`$; see the [Lambert identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L5865). If the right-hand side were rational with reduced denominator $`q`$, then a non-integral integer multiple could not lie at distance less than $`1/q`$ from an integer. It is therefore enough, for every $`q`$, to construct $`N`$ such that $`b^N\sum_m\tau(m)b^{-m}`$ is non-integral but lies within $`1/q`$ of an integer. This is the formal [near-integer criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L5792).

The construction of $`N`$ is divided into three finite parts. First, a bounded Bertrand argument supplies disjoint prime blocks, and the Chinese remainder theorem chooses an arithmetic progression on which
``` math
b^r\mid \tau(N+r) \qquad (1\leq r\leq K).
```
These divisibilities make the first $`K`$ terms of the shifted tail integral. The multiplicativity step that converts prescribed prime valuations into the displayed divisibility is the [prime-block divisibility lemma](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L6177). Second, divisor pairing bounds the average of the weighted middle window
``` math
\sum_{K<r\leq L}\tau(N+r)b^{L-r}
```
along that progression. A pigeonhole choice then selects one translate with a small middle contribution; see the [weighted-middle selection lemma](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L7246). Third, the elementary estimate $`\tau(n)\leq n`$ controls the infinite tail after $`L`$. The parameters are chosen so that the middle and far-tail bounds together are smaller than $`1/q`$; the shifted tail is strictly positive because every divisor count is positive, so the dilated sum is not an integer.

Thus the analytic series is used only in the Lambert identity and the geometric tail estimate. The remaining proof is a finite CRT construction, divisor counting, and explicit parameter arithmetic. The final certificate existence theorem holds for every $`b\geq2`$ and every precision $`q`$; see the [uniform certificate theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L7859). Its composition with the near-integer criterion is the theorem cited above. This is a formalisation of the classical full-support theorem, not a new irrationality result.

<a id="named-infinite-support-cases"></a>

## Named infinite-support cases

Beyond full support, the development proves irrationality for a family of infinite supports $`A`$, at every base $`b\ge2`$. Each is a formalised case of the \#257 statement family. None is the universal statement, and none is claimed as new mathematics.

<div id="res:support" class="theorem">

**Theorem 5** (support-class family). *For every integer $`b\ge2`$, the series $`\sum_{n\in A} 1/(b^n-1)`$ is irrational for each of the following infinite supports $`A`$:*

1.  *factorial support $`A=\{n! : n\ge1\}`$, giving $`\sum 1/(b^{n!}-1)`$;*

2.  *power-of-two support $`A=\{2^n : n\ge0\}`$, giving $`\sum 1/(b^{2^n}-1)`$;*

3.  *multiples $`A=d\mathbb{N}_{>0}=\{dk:k\ge1\}`$ with $`d\ge1`$;*

4.  *pairwise-coprime supports with summable reciprocals (Erdős’s condition \[erdos1968\]);*

5.  *eventually-periodic supports, residue classes, and the odd numbers.*

</div>

These sort into three groups. The classical case is (d): infinite pairwise-coprime $`A`$ with $`\sum_{a\in A}1/a<\infty`$, formalised from Erdős’s condition. The lcm-gap named cases are (a) and (b), whose support gaps outgrow the running $`\operatorname{lcm}`$; the structured families are (c) and (e).[^1] Formalised case by case by the [factorial-support theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L5707), [power-of-two-support theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L5731), [multiple-support theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L8775), [pairwise-coprime-support theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L10448), and [eventually-periodic-support theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L11276). The residue-class and odd supports in part <span class="upright">(e)</span> are direct specialisations of the last theorem; the first two theorems already hold for every base $`b\geq2`$.

The prime support is now known unconditionally: Tao and Teräväinen proved that
``` math
\sum_p\frac1{2^p-1}=\sum_{n\ge1}\frac{\omega(n)}{2^n}
```
is irrational \[taoteravainen\]. Their proof uses quantitative two-point correlations of multiplicative functions and is not formalised here. This settles an important special case, while the universal support statement remains open.

The factorial and power-of-two cases are worth a word because they are not reachable by a Liouville shortcut: the power-of-two gap $`2^k-\operatorname{lcm}`$ stays within a bounded ratio of the $`\operatorname{lcm}`$, so the terms do not decay fast enough for a transcendence-measure argument, and a uniform criterion is needed. The mechanism is *period noncollapse*: a prime-valuation-deficit witness forces the multiplicative order of the base modulo the relevant modulus not to collapse, which rules out the long repeated digit blocks a rational value would require.

<a id="transition-to-the-counterexample-direction."></a>

#### Transition to the counterexample direction.

The results above enlarge the family of supports for which irrationality is known, but they do not supply the universal quantifier. We now fix the base at $`2`$ and change coordinates: all support sums form one achievement set. The counterexample problem thereby becomes a point-membership question, with generic constraints on its rational points and a separate exact reduction at the target $`1/2`$.

<a id="the-base-2-achievement-set"></a>

## The base-$`2`$ achievement set

For $`n\geq1`$, put
``` math
w_n=\frac1{2^n-1}.
```
For $`n\geq0`$, put
``` math
T_n=\sum_{m>n}w_m,
 \qquad
 \mathcal A=\left\{\sum_{n\in A}w_n:A\subseteq\mathbb{N},\ 0\notin A\right\}.
```
For $`x\geq0`$, define the greedy residuals by $`r_0(x)=x`$ and
``` math
\varepsilon_n(x)=
 \begin{cases}
  1,&w_n\leq r_{n-1}(x),\\
  0,&w_n>r_{n-1}(x),
 \end{cases}
 \qquad
 r_n(x)=r_{n-1}(x)-\varepsilon_n(x)w_n.
```
When $`\varepsilon_n(x)=1`$ we say the expansion *takes* rank $`n`$; otherwise it *skips* rank $`n`$.

<div id="res:greedy" class="theorem">

**Theorem 6** (strict-tail greedy coding). *For every $`n\geq1`$,
``` math
T_n<w_n.
```
Hence every $`x\in\mathcal A`$ has a unique support by positive exponents (the “normalised” support in the formal source). Moreover, a real number $`x`$ lies in $`\mathcal A`$ if and only if $`x\geq0`$ and $`r_n(x)\leq T_n`$ for every $`n\geq0`$. In that case $`x=\sum_{n\geq1}\varepsilon_n(x)w_n`$.*

</div>

The strict-tail inequality and greedy criterion are the [strict-tail theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L180) and [greedy membership theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1445). Uniqueness is the [support-coding theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1527). Kovač–Tao provide the strict-tail Cantor-set context \[kovactao\].

<a id="separate-geometric-and-finite-arithmetic-consequences."></a>

#### Separate geometric and finite-arithmetic consequences.

Proposition <a href="#res:greedytopology" data-reference-type="ref" data-reference="res:greedytopology">56</a> proves that $`\mathcal A`$ is compact, perfect, totally disconnected, nowhere dense, and of Lebesgue measure $`1`$. Proposition <a href="#res:death" data-reference-type="ref" data-reference="res:death">57</a> proves soundness of exact rational evaluation and gives finite nonmembership certificates. These results use the same greedy coordinates, but neither is a clause of the membership equivalence above. Their detailed statements and one-sided boundary are in Appendix <a href="#app:carry-geometry" data-reference-type="ref" data-reference="app:carry-geometry">10.5</a>. No novelty claim is made for the strict-tail geometry.

<a id="consequence-for-the-half-value-branch."></a>

#### Consequence for the half-value branch.

Theorem <a href="#res:greedy" data-reference-type="ref" data-reference="res:greedy">6</a> makes the greedy support canonical; Proposition <a href="#res:greedytopology" data-reference-type="ref" data-reference="res:greedytopology">56</a> supplies the compactness needed to pass from cofinal finite approximations to a point of $`\mathcal A`$; and Proposition <a href="#res:death" data-reference-type="ref" data-reference="res:death">57</a> supplies one-sided finite refuters. The measure-one statement is global and does not decide whether the particular point $`1/2`$ belongs to $`\mathcal A`$. Before specialising to that point, we record the carry constraints forced by any rational $`X_A\in\mathcal A`$; these are necessary conditions in the universal direction, not yet a contradiction.

<a id="rigidity-of-a-hypothetical-rational-support"></a>

## Rigidity of a hypothetical rational support

For $`A\subseteq\mathbb{N}_{>0}`$, define
``` math
f_A(m)=\#\{a\in A:a\mid m\},
 \qquad
 X_A=\sum_{a\in A}\frac1{2^a-1}
     =\sum_{m\geq1}\frac{f_A(m)}{2^m},
 \qquad
 T_f(N)=\sum_{j\geq1}\frac{f(N+j)}{2^j}.
```
Thus $`f_A(m)`$ counts the selected exponents dividing $`m`$, $`X_A`$ is the original support sum, and $`T_f(N)`$ is the binary tail of a coefficient sequence after position $`N`$.

<div id="res:rigidity-main" class="theorem">

**Theorem 7** (rational-support carry recurrence). *Suppose that $`A\neq\varnothing`$ and
``` math
X_A=\frac{p}{2^c v},
 \qquad p\in\mathbb{Z},\quad c\in\mathbb{N},\quad v\geq1\ \text{odd}.
```
Then $`u_N=vT_{f_A}(c+N)`$ is a positive integer for every $`N`$, and
``` math
u_{N+1}+v f_A(c+N+1)=2u_N. \tag{4.1}
```*

</div>

This is formalised by [the shifted natural-state theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L668). The recurrence is binary long division: since $`2T_f(M)=f(M+1)+T_f(M+1)`$, doubling the scaled tail separates the next coefficient, and rationality is what makes the states $`u_N`$ integers. Its tail-orbit normal form is Theorem <a href="#res:rigidity" data-reference-type="ref" data-reference="res:rigidity">45</a>. A two-element support, with its explicit period-six orbit and multiplier $`21`$, is worked at the end of Appendix <a href="#app:carry-boolean" data-reference-type="ref" data-reference="app:carry-boolean">10.2</a>.

<div id="res:rigidity-unbounded-main" class="corollary">

**Corollary 8** (unbounded-state consequence). *Under the hypotheses of Theorem <a href="#res:rigidity-main" data-reference-type="ref" data-reference="res:rigidity-main">7</a>, if $`A`$ is infinite, then $`(u_N)`$ is unbounded.*

</div>

This is formalised by [the fraction-facing unbounded-state theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L2377); see also Theorem <a href="#res:unbounded" data-reference-type="ref" data-reference="res:unbounded">54</a>.

<div id="res:rigidity-sublog-main" class="corollary">

**Corollary 9** (sublogarithmic coverage consequence). *Under the hypotheses of Theorem <a href="#res:rigidity-main" data-reference-type="ref" data-reference="res:rigidity-main">7</a>, for every $`\varepsilon>0`$ there is $`B=B(\varepsilon,c,v)`$ such that every interval $`\{c+N+1,\ldots,c+N+\ell\}`$ on which $`f_A`$ vanishes satisfies
``` math
\ell\leq\varepsilon\log_2(N+1)+B;
```*

</div>

This is formalised by [the sublogarithmic zero-window theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SublogDivisorCoverage.lean#L392); see also Theorem <a href="#res:sublog" data-reference-type="ref" data-reference="res:sublog">50</a>.

<div id="res:rigidity-mass-main" class="corollary">

**Corollary 10** (odd-denominator reciprocal-mass consequence). *Under the hypotheses of Theorem <a href="#res:rigidity-main" data-reference-type="ref" data-reference="res:rigidity-main">7</a>, if $`\rho(A)=\sum_{a\in A}a^{-1}<\infty`$, $`v>1`$, and $`h=\operatorname{ord}_v(2)`$, then
``` math
\rho(A)=\frac{w}{h}
   +\lim_{M\to\infty}\frac1M\sum_{N<M}e_N\geq\frac{w}{h},
```
where $`w`$ is the number of wraps in one doubling-residue cycle and $`e_N=\lfloor u_N/v\rfloor`$ is the integral excess in the split $`u_N=ve_N+(p2^N\bmod v)`$. If $`(p,v)=1`$, then $`w\geq1`$.*

</div>

The exact excess-mean identity is [the shifted excess-mean theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L1577); see also Proposition <a href="#res:orderwrap" data-reference-type="ref" data-reference="res:orderwrap">52</a>.

<div id="res:rigidity-dyadic-mass-main" class="corollary">

**Corollary 11** (dyadic reciprocal-mass consequence). *Under the hypotheses of Theorem <a href="#res:rigidity-main" data-reference-type="ref" data-reference="res:rigidity-main">7</a>, if $`v=1`$ and $`A`$ is infinite, then either $`\rho(A)`$ diverges or $`\rho(A)>1`$.*

</div>

This is formalised by [the dyadic reciprocal-mass alternative](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L2200); see also Corollary <a href="#res:collision" data-reference-type="ref" data-reference="res:collision">53</a>.

Read together, the four statements say that rationality would force an unbounded integer state sequence for an infinite support, severely limit intervals containing no support divisor, and constrain the reciprocal mass according to whether the reduced denominator has an odd factor. They are independent necessary consequences of one rationality premise, not a contradiction. Appendices <a href="#app:carry-normal-form" data-reference-type="ref" data-reference="app:carry-normal-form">10.1</a>–<a href="#app:carry-boolean" data-reference-type="ref" data-reference="app:carry-boolean">10.2</a> supply the common recurrence and Boolean certificate; Appendices <a href="#app:carry-sublog" data-reference-type="ref" data-reference="app:carry-sublog">10.3</a> and <a href="#app:carry-mass" data-reference-type="ref" data-reference="app:carry-mass">10.4</a> supply the independent filters. No corollary above appears as a hypothesis of another; their appendix proofs do share the carry machinery, in the order displayed in Appendix <a href="#app:carry-mass" data-reference-type="ref" data-reference="app:carry-mass">10.4</a>.

<div id="res:universal-boolean-obstruction" class="corollary">

**Corollary 12** (Boolean–Möbius orbit form of universal \#257). *The universal assertion in Erdős #257 is equivalent to the following orbit statement: for every rational number $`p/q`$, every Boolean–Möbius carry certificate for $`p/q`$ reconstructs a finite support. Equivalently, the universal assertion fails exactly when one such certificate reconstructs an infinite support.*

</div>

Here a certificate is the positive, square-root-bounded integral orbit with divisibility and Boolean Möbius conditions stated in Theorem <a href="#res:carrycert" data-reference-type="ref" data-reference="res:carrycert">48</a>. That theorem is the Lean-checked fraction-by-fraction equivalence [between supports and carry certificates](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L948); the corollary merely quantifies it over $`p/q`$ and separates finite from infinite reconstructed supports. This is an exact reformulation, not a finite algorithm: the orbit condition and the support it reconstructs are infinite objects.

<a id="the-target-12"></a>

## The target $`1/2`$

<a id="why-this-target."></a>

#### Why this target.

Any infinite support with any rational value would refute the universal statement; fixing one target value turns the search into a point-membership question. The value $`1/2`$ is a canonical choice rather than a forced one: it is the value of the signed Möbius rung $`L(\mu)=1/2`$ of Section <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a>, so the question asks whether a genuinely Boolean support can attain what the signed Möbius weights attain (Proposition <a href="#res:mobiussignnogo" data-reference-type="ref" data-reference="res:mobiussignnogo">46</a> shows that the signs cannot simply be truncated); no finite support by positive exponents attains it (Proposition <a href="#res:nofinitehalf" data-reference-type="ref" data-reference="res:nofinitehalf">15</a> below); and the strict-tail coding of Theorem <a href="#res:greedy" data-reference-type="ref" data-reference="res:greedy">6</a> makes its candidate support unique.

Let
``` math
\mathcal S(x)=\{n\geq1:\varepsilon_n(x)=0\}
```
be the set of exponents omitted by the greedy expansion.

<a id="a-worked-start."></a>

#### A worked start.

The greedy expansion of $`1/2`$ begins: $`w_1=1>\tfrac12`$, so rank $`1`$ is skipped; $`w_2=\tfrac13`$ is taken, leaving $`\tfrac16`$; $`w_3=\tfrac17`$ is taken, leaving $`\tfrac1{42}`$; ranks $`4,5`$ are skipped because $`w_4=\tfrac1{15}`$ and $`w_5=\tfrac1{31}`$ exceed $`\tfrac1{42}`$; and $`w_6=\tfrac1{63}`$, $`w_7=\tfrac1{127}`$ are taken, leaving
``` math
\frac12-\Bigl(\frac13+\frac17+\frac1{63}+\frac1{127}\Bigr)
 =\frac1{16002}.
```
The next take is at rank $`14`$, and through rank $`26`$ the expansion takes exactly the ranks $`2,3,6,7,14,20,21,26`$ (the kernel-checked rank-$`26`$ prefix cited in Appendix <a href="#app:half-final-skip" data-reference-type="ref" data-reference="app:half-final-skip">9.4</a>). Membership of $`1/2`$ in $`\mathcal A`$ asks whether the complementary skips recur beyond every bound. A *last* skip is precisely a skip whose residual lies strictly above the whole remaining tail (Appendix <a href="#res:fixedtailsocket" data-reference-type="ref" data-reference="res:fixedtailsocket">9.4.6</a>), and Theorem <a href="#res:fatalright" data-reference-type="ref" data-reference="res:fatalright">17</a> below identifies nonmembership with the existence of one.

<div id="def:terminal-bit" class="definition">

**Definition 13** (finite greedy seam and terminal bit). For an integer $`s\geq6`$, set
``` math
q_{s,d}=\left\lfloor\frac{4^s}{2^d-1}\right\rfloor
 \quad(2\leq d<s),
 \qquad
 K_s=2^{2s-1}-2^s.
```
Starting from $`R_{s,2}=K_s`$, define successively, for $`2\leq d<s`$,
``` math
\beta_{s,d}=
 \begin{cases}
  1,&q_{s,d}\leq R_{s,d},\\
  0,&q_{s,d}>R_{s,d},
 \end{cases}
 \qquad
 R_{s,d+1}=R_{s,d}-\beta_{s,d}q_{s,d}.
```
The Boolean word $`(\beta_{s,2},\ldots,\beta_{s,s-1})`$ is the *finite greedy seam at row $`s`$*, and $`\tau_s=\beta_{s,s-1}`$ is its terminal bit.

</div>

Here $`q_{s,d}=\lfloor4^sw_d\rfloor`$ is the weight $`w_d`$ at resolution $`4^{-s}`$, and $`K_s=4^s\cdot\tfrac12-2^s`$ is the target $`1/2`$ at the same resolution, lowered by a guard of $`2^s`$; the word $`\beta`$ records which weights this integer greedy run takes. At $`s=7`$, for instance, $`K_7=8064`$ and the run takes $`q_{7,2}=5461`$ and $`q_{7,3}=2340`$, skips $`1092`$ and $`528`$, and takes $`q_{7,6}=260`$, leaving $`3`$: the word is $`1,1,0,0,1`$, matching the real greedy decisions at ranks $`2`$–$`6`$, with terminal bit $`\tau_7=1`$. The seam is thus an exact integer coordinate model of the real greedy process. Appendix <a href="#app:half-final-skip" data-reference-type="ref" data-reference="app:half-final-skip">9.4</a> develops the equivalence with final skips and the unresolved transition cells; the finite coordinate changes in Appendix <a href="#app:half-evidence" data-reference-type="ref" data-reference="app:half-evidence">9.5</a> do not strengthen that equivalence.

<div id="res:halfmembership" class="theorem">

**Theorem 14** (exact half-membership classification). *The following are equivalent:
``` math
\begin{aligned}
\textup{(i)}\;&\quad \frac12\in\mathcal A;\\
\textup{(ii)}\;&\quad \mathcal S(1/2)\ \text{is infinite};\\
\textup{(iii)}\;&\quad \mathcal S(1/2)\ \text{has no largest element};\\
\textup{(iv)}\;&\quad
  \text{for every }N\text{ there is }s\geq\max\{N,6\}
  \text{ with }\tau_s=0.
\end{aligned}
```*

</div>

The omitted-set equivalence is the [infinite-skip theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L2514); the terminal forms are the [unbounded-terminal theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L126) and [no-final-skip theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L235).

<div id="res:nofinitehalf" class="proposition">

**Proposition 15** (finite half-value exclusion). *No finite support $`A\subseteq\mathbb{N}_{>0}`$ has value $`1/2`$.*

</div>

This is the [finite-support theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryReachability.lean#L589).

<div id="res:halfcounterexample" class="corollary">

**Corollary 16** (counterexample from half-membership). *Any one of the equivalent conditions in Theorem <a href="#res:halfmembership" data-reference-type="ref" data-reference="res:halfmembership">14</a> produces an infinite support $`A\subseteq\mathbb{N}_{>0}`$ with $`X_A=1/2`$, and therefore refutes the universal form of Erdős #257.*

</div>

This combines the unique greedy support from Theorem <a href="#res:greedy" data-reference-type="ref" data-reference="res:greedy">6</a> with Proposition <a href="#res:nofinitehalf" data-reference-type="ref" data-reference="res:nofinitehalf">15</a>. A tempting signed-to-Boolean shortcut also fails: selecting precisely the negative Möbius indices overshoots $`1/2`$ by at least $`1/63`$. Proposition <a href="#res:mobiussignnogo" data-reference-type="ref" data-reference="res:mobiussignnogo">46</a> gives the exact sign-separation identity.

<a id="section-consequence."></a>

#### Section consequence.

Theorem <a href="#res:halfmembership" data-reference-type="ref" data-reference="res:halfmembership">14</a> replaces a search over arbitrary supports by one canonical quantifier question: does the greedy orbit of $`1/2`$ skip cofinally? It does not answer that question. The next subsection assumes a possible final skip and identifies exactly what would be required to exclude it.

<a id="the-final-skip-reduction"></a>

## The final-skip reduction

For each $`s\geq6`$, let
``` math
G_s=\{d:2\leq d<s,\ \beta_{s,d}=1\}.
```
Let $`H_s`$ be the unique subset of $`\{2,\ldots,s-1\}`$ for which $`\sum_{d\in H_s}q_{s,d}`$ is least among the subset sums strictly exceeding $`K_s`$. Informally, $`G_s`$ records what the integer greedy run has taken through row $`s`$, and $`H_s`$ is its cheapest strict overshoot of the target. The transition from row $`s`$ to row $`s+1`$ is called *upper*, *middle*, or *right* according as
``` math
G_{s+1}=H_s,\qquad G_{s+1}=G_s,\qquad
 G_{s+1}=G_s\cup\{s\},
```
respectively. Thus a final skipped exponent $`D`$ is an upper or middle transition followed only by right transitions. The explicit row-$`13`$ computation gives a false terminal bit there. Consequently, if the seam is eventually right, its last false terminal row automatically satisfies $`D\geq13`$; the lower bound is not an omitted range of cases. This is the [last-false row theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderLastProducerContradiction.lean#L178).

At a middle transition $`D\geq13`$, put
``` math
A_D=G_D\cup\{D\},\qquad
 P_D=2f_{G_D}(2D+1)+f_{G_D}(2D+2),
```
and write
``` math
C_D=4R_{D,D}-P_D-4\in\mathbb{Z},\qquad
 \Theta_D=\sum_{j\geq1}\frac{f_{A_D}(2D+2+j)}{2^j}.
```
Here $`C_D`$ is the integer transition carry and $`\Theta_D`$ its complete future divisor-incidence tail. Their comparison has an exact meaning: by the residual identity of Appendix <a href="#res:producercarry" data-reference-type="ref" data-reference="res:producercarry">9.4.7</a>,
``` math
\frac12-\sum_{a\in A_D}w_a
 =2^{-(2D+2)}\bigl(C_D-\Theta_D\bigr),
```
so the inequality $`\Theta_D<C_D`$ says exactly that the augmented support $`A_D`$ falls short of $`\tfrac12`$.

For a finite set $`u\subseteq\{1,\ldots,d\}`$, write $`V(u)=\sum_{n\in u}w_n`$. Call $`(u,d)`$ a *fatal half-gap* if
``` math
V(u)+T_{d+1}<\frac12<V(u)+w_{d+1}.
```
Such a pair certifies that no support agreeing with $`u`$ through rank $`d`$ can represent $`1/2`$.

<div id="res:fatalright" class="theorem">

**Theorem 17** (final-skip classification). *Nonmembership of $`1/2`$ in $`\mathcal A`$ is equivalent to each of the following:*

1.  *the integer seam recurrence is eventually right;*

2.  *a fatal half-gap exists;*

3.  *the real greedy expansion of $`1/2`$ has a final skipped exponent.*

</div>

The three equivalent nonmembership criteria are formalised in [fatal-gap classification](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderFatalGapRightTail.lean#L781), [nonmembership classification](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderFatalGapRightTail.lean#L787), and [final-skip classification](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderFatalGapRightTail.lean#L802).

<div id="res:finalskipexclusions" class="proposition">

**Proposition 18** (excluded final-skip branches). *At a final skipped exponent $`D\geq13`$, the upper successor is impossible. On the middle branch the value $`C_D=-3`$ is impossible. Among the three exceptional dyadic cells identified by the two-sided induction, only $`C_D=-2`$ and $`C_D=-1`$ remain unresolved.*

</div>

The upper and $`C_D=-3`$ exclusions are the [upper-branch exclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderLastProducerContradiction.lean#L250) and [middle-$`-3`$ exclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderLastProducerContradiction.lean#L315); the upper case is proved directly at the linked declaration, and Appendix <a href="#app:half-final-skip" data-reference-type="ref" data-reference="app:half-final-skip">9.4</a> sketches a prose argument only for the $`-3`$ cell. The three exceptional dyadic cells are identified by the [three-cell classification](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3090).

<div id="res:taildominance" class="corollary">

**Corollary 19** (tail-dominance membership criterion). *If every middle transition at a row $`D\geq13`$ with $`C_D\neq-3`$ satisfies
``` math
\Theta_D<C_D, \tag{4.2}
```
then no final skipped exponent exists, and hence $`1/2\in\mathcal A`$.*

</div>

This implication is the [tail-dominance theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderLastProducerContradiction.lean#L387). Because $`\Theta_D\geq0`$, the hypothesis of this corollary already rules out every actual middle transition with a negative coordinate other than the locally discharged value $`-3`$. Thus the single displayed hypothesis contains two different requirements: exclusion of the unresolved cells $`C_D\in\{-2,-1\}`$, and the future-tail bound <span class="upright">(4.2)</span> on the remaining nonnegative coordinates. Neither requirement is proved for the greedy orbit. The universal quantifier in the hypothesis also cannot be weakened to a density statement: nonmembership requires only one final middle transition, so a bound holding at all but one row would prove nothing.

<a id="logical-status-of-the-final-skip-argument."></a>

#### Logical status of the final-skip argument.

The proved levels of the argument are
``` math
\begin{array}{rcl}
 \frac12\notin\mathcal A
 &\Longleftrightarrow
   \text{a final skipped exponent exists}
 &[\text{proved}],\\
 \text{final upper, or final middle with }C_D=-3
 &\Longrightarrow\bot
 &[\text{proved}].
\end{array}
```
These lines do not imply membership. The unproved hypothesis has two parts: exclude all actual middle transitions with $`C_D\in\{-2,-1\}`$, and prove <span class="upright">(4.2)</span> at every remaining non-$`(-3)`$ middle transition. Together they establish the global hypothesis of Corollary <a href="#res:taildominance" data-reference-type="ref" data-reference="res:taildominance">19</a>; only then does Corollary <a href="#res:halfcounterexample" data-reference-type="ref" data-reference="res:halfcounterexample">16</a> produce an infinite rational-valued support and a counterexample to the universal \#257 statement.

<a id="what-remains-open"></a>

## What remains open

The two directions remain separate.

1.  The universal problem is to prove $`X_A\notin\mathbb{Q}`$ for every infinite $`A\subseteq\mathbb{N}_{>0}`$. Theorem <a href="#res:support" data-reference-type="ref" data-reference="res:support">5</a> proves several families, while Theorem <a href="#res:rigidity-main" data-reference-type="ref" data-reference="res:rigidity-main">7</a> and its four corollaries constrain a hypothetical rational support. Neither route supplies the universal quantifier.

2.  The distinguished half-value route asks whether $`1/2\in\mathcal A`$. Theorem <a href="#res:halfmembership" data-reference-type="ref" data-reference="res:halfmembership">14</a> identifies this with infinitely many greedy skips, while Theorem <a href="#res:fatalright" data-reference-type="ref" data-reference="res:fatalright">17</a> identifies nonmembership with a final skip. Proposition <a href="#res:finalskipexclusions" data-reference-type="ref" data-reference="res:finalskipexclusions">18</a> removes the final upper and middle-$`(-3)`$ branches. Corollary <a href="#res:taildominance" data-reference-type="ref" data-reference="res:taildominance">19</a> would finish the argument if every actual middle transition avoided $`C_D=-2,-1`$ and satisfied <span class="upright">(4.2)</span> in every remaining non-$`(-3)`$ cell. Neither global obligation is discharged.

Appendix <a href="#app:half-technical" data-reference-type="ref" data-reference="app:half-technical">9</a> records the exact local reductions, conditional compactness criteria, finite certificates, counterexamples to stronger local assertions, and arguments that rule out several proposed strategies. These results refine the obstruction; they do not decide either open \#257 question.

<a id="sec:249"></a>

# The totient constant $`S`$ (Erdős \#249)

Whether
``` math
S=\sum_{n\ge1}\frac{\varphi(n)}{2^n}
```
is irrational remains open. The argument has four logically distinct layers. First, a finite Farey computation excludes every rational denominator up to an explicit bound. Second, irrationality is characterised exactly by the existence of finite certificates against every possible eventual binary period. Third, many such certificates are verified at bounded parameters. Fourth, and still missing, is a theorem supplying them at unbounded parameters. Only the fourth layer would settle the problem.

The main section states this reduction. Appendix <a href="#app:totient-normal" data-reference-type="ref" data-reference="app:totient-normal">11.1</a> gives equivalent cofinal coordinates; Appendix <a href="#app:totient-finite" data-reference-type="ref" data-reference="app:totient-finite">11.2</a> separates fixed-scale mechanisms from the conditional cofinal criteria that use them as hypotheses; and Appendices <a href="#app:totient-boundaries" data-reference-type="ref" data-reference="app:totient-boundaries">11.3</a>–<a href="#app:totient-rank" data-reference-type="ref" data-reference="app:totient-rank">11.4</a> record necessary inputs, scoped no-go results, and conditional rank routes. Only the first is an exact reformulation of the open fourth layer.

<a id="sec:uncond"></a>

## Unconditional: no small denominator

<div id="res:farey" class="theorem">

**Theorem 20** (denominator exclusion). *Set
``` math
Q_0:=79\,639\,646\,646\,701\,375\,323\,355\,774\,875\,831\,053
       \approx7.96\times10^{34}.
```
For every integer $`p`$ and every $`q`$ with $`1\le q\le Q_0`$,
``` math
S \;\ne\; \frac{p}{q}.
```
Equivalently, if $`S`$ is rational then its reduced denominator exceeds that bound.*

</div>

Formalised as the [record denominator exclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L18056). The bound is reached by a ladder of finite, elementary exclusions,
``` math
4838 \;\to\; 4\,194\,304 = 2^{22} \;\to\; 2.49\times10^{17}\ (\text{Farey } K{=}120)
\;\to\; 7.96\times10^{34}\ (\text{Farey } K{=}240),
```
each a mediant/Farey argument that traps any candidate $`m/q`$ inside a forbidden gap. The mediant framework is historically associated with Farey’s 1816 note on vulgar fractions \[farey1816\]; the finite exclusions themselves are Lean-checked arguments in the formal-source checkpoint. See [denominator exclusion through 4838](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L15347) for the first rung and [120-term Farey bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GapFareyBound.lean#L88), [240-term Farey bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GapFareyBound.lean#L176) for the two Farey windows.

This is an explicit lower bound on the denominator of any rational representation, not a proof of irrationality. A rational with a larger denominator is not excluded by it.

<div class="remark">

*Remark 1* (one bound, four representations). Because the ladder identities of Section <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a> are equalities, the same finite record transfers verbatim to three other representations of the constant: to the positive lift $`\sum_d \alpha(d)/(2^d-1)`$ ([positive-lift denominator transfer](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L18145)), to the signed Möbius-square constant $`T=\sum_d\mu(d)/(2^d-1)^2`$ at half the bound ([signed-square denominator transfer](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L18159)), and to the coprimality probability of Section <a href="#sec:geom" data-reference-type="ref" data-reference="sec:geom">5.2</a> at half the bound. Half appears because $`S=\tfrac12+T`$ turns a denominator $`d`$ for $`T`$ into $`2d`$ for $`S`$.

</div>

<a id="sec:geom"></a>

## The geometric picture: $`S`$ as coprime-pair mass

Let $`X,Y`$ be independent fair-coin waiting times, $`\Pr(X=n)=2^{-n}`$ for $`n\ge1`$. Then $`\Pr(d\mid X)=1/(2^d-1)`$, so the Lambert transform is a divisor calculus of $`X`$: $`L(f)=\mathbb E[(f*\zeta)(X)]`$. The rungs read as $`L(\mu)=\Pr(X=1)=1/2`$, $`L(\varphi)=\mathbb E[X]=2`$, $`L(\mathbf 1)=\mathbb E[\tau(X)]=E`$, and $`L(\alpha)=\mathbb E[\varphi(X)]=S`$.

Counting visible lattice points $`(a,b)`$ with $`a+b=n`$, $`a\ge1`$, $`b\ge0`$, and $`\gcd(a,b)=1`$ gives exactly $`\varphi(n)`$, uniformly in $`n`$, so $`S`$ is itself a coprime-pair mass.

<div id="res:coprime" class="proposition">

**Proposition 21** (coprimality probability).
*``` math
S \;=\; \tfrac12 \;+\; \Pr\!\big(\gcd(X,Y)=1\big)
\;=\; \tfrac12 \;+\!\!\sum_{\substack{a,b\ge1\\ \gcd(a,b)=1}}\!\! 2^{-(a+b)}.
```*

</div>

Formalised: [coprime-pair representation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L18229), with the underlying lattice identity at [visible-lattice-point identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L18216). Base $`2`$ is the one point where $`\Pr(X=a)\Pr(Y=b)=2^{-(a+b)}`$ needs no normalising constant. Restricting the half-open lattice mass to positive waiting times removes $`(1,0)`$, producing the boundary term $`1/2`$. Thus \#249 asks whether two independent fair-coin waiting times are coprime with irrational probability. After reducing $`(X,Y)`$ by their gcd, the same distribution has an exact Stern–Brocot cylinder decomposition. Appendix <a href="#app:lambert-probability" data-reference-type="ref" data-reference="app:lambert-probability">12.3</a> states the resulting probability law and the sharp Fibonacci stability of its alternating runs. These are unconditional structural theorems inside one representation of $`S`$; they do not supply the denominator survival needed for irrationality.

<a id="sec:reduction"></a>

## Exact certificate characterisation

The reduction uses only the elementary bound $`\varphi(n)\le n`$, geometric tail estimates, and finite integer arithmetic. For $`t\ge1`$, write $`M_t=\operatorname{lcm}(1,\ldots,t)`$.

<a id="why-tail-differences-detect-rationality."></a>

#### Why tail differences detect rationality.

Since $`2^NS=\sum_{n\le N}\varphi(n)\,2^{N-n}+R_N`$, each scaled tail $`R_N`$ is $`2^NS`$ minus an integer. Suppose $`S=p/q`$ with $`q=2^cv`$ and $`v`$ odd. For every multiple $`h`$ of the multiplicative order of $`2`$ modulo $`v`$ and every $`N\geq c`$,
``` math
R_{N+h}-R_N
 =\frac{2^N\bigl(2^h-1\bigr)p}{q}-k
 \in\mathbb{Z}
```
for some integer $`k`$, because $`v\mid2^h-1`$ and $`2^c\mid2^N`$. Rationality therefore supplies one period $`h`$ all of whose tail differences at large $`N`$ are integral; conversely, a single integral positive-shift difference already forces $`S`$ to be rational. A finite certificate refutes one candidate integrality, and refuting every period at cofinally many $`N`$ refutes rationality outright. This is the mechanism behind the equivalences of this subsection.

<div id="def:totient-certificate" class="definition">

**Definition 22** (tail differences and finite certificates). For $`N\ge0`$, define the scaled tail
``` math
R_N \;=\; \sum_{m\ge1}\frac{\varphi(N+m)}{2^m}.
```
For $`h\in\mathbb{N}_{>0}`$ and $`N,L\in\mathbb{N}`$, define
``` math
\Delta_{h,N,L}=\sum_{j=0}^{L-1}\big(\varphi(N+h+1+j)-\varphi(N+1+j)\big)\,2^{\,L-1-j}\in\mathbb{Z},
```
with the sum empty when $`L=0`$, and say that $`(h,N,L)`$ is a *finite certificate* when
``` math
\mathsf{Sep}(h,N,L):\quad
N+h+L+2 \;<\; \big(\Delta_{h,N,L}\bmod 2^L\big) \;<\; 2^L-(N+h+L+2).
```

</div>

The integer $`\Delta_{h,N,L}`$ contains the first $`L`$ binary places of $`R_{N+h}-R_N`$; the two margins bound the omitted tail using $`\varphi(n)\le n`$. Thus each instance of the predicate is decidable by finite integer arithmetic, while its conclusion concerns the infinite tail difference. The depth-floor theorem implies that a successful instance has $`L>0`$, even though the formal existential quantifier ranges over all of $`\mathbb{N}`$. Heuristically, the two margins together occupy a proportion of about $`2(N{+}h{+}L{+}2)/2^L`$ of the modulus, which is small as soon as $`2^L`$ is large compared with $`N+h+L`$; a certificate can fail only when the residue lies exceptionally close to $`0`$ or $`2^L`$, that is, when the tail difference is exceptionally close to an integer. Nothing in this paper converts that observation into the required cofinal supply.

<div id="res:complete" class="proposition">

**Proposition 23** (certificate completeness). *For every $`h\ge1`$ and $`N\ge0`$,
``` math
\bigl(\exists L,\ \mathsf{Sep}(h,N,L)\bigr)
\quad\Longleftrightarrow\quad
R_{N+h}-R_N\notin\mathbb{Z}.
```*

</div>

This is the [certificate-completeness equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeFlatness.lean#L316). Thus the finite predicate loses no information at a fixed pair $`(h,N)`$. The certificate depth-floor lemma forces every witness to have positive depth. Searching $`L=0,1,2,\ldots`$ is therefore a complete positive semi-decision procedure for non-integrality at fixed $`(h,N)`$: it halts exactly when the difference is non-integral. When the difference is integral, completeness says that no depth succeeds, so this search does not halt. It is not a two-sided decision procedure for an infinite tail.

<div id="res:pointwisecomplete" class="theorem">

**Theorem 24** (pointwise certificate characterisation). *The following are equivalent:
``` math
\begin{aligned}
 &S\notin\mathbb{Q},\\
 &\forall\,h\ge1\ \forall\,N\ge0,\qquad R_{N+h}-R_N\notin\mathbb{Z},\\
 &\forall\,h\ge1\ \forall\,N\ge0\ \exists\,L,\qquad
      \mathsf{Sep}(h,N,L).
\end{aligned}
```*

</div>

Formalised: [all-differences equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeFlatness.lean#L386), and [pointwise certificate equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeFlatness.lean#L399). The converse direction uses the fact that integrality of even one positive-shift tail difference forces $`S`$ to be rational ([integral-difference rationality criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeFlatness.lean#L357)).

<div id="res:red21" class="theorem">

**Theorem 25** (exact tail-period characterisation). *$`S`$ is irrational if and only if, for every period $`h\ge1`$ and every threshold $`N_0`$, there exist $`N\ge N_0`$ and $`L`$ with $`\mathsf{Sep}(h,N,L)`$.*

</div>

Formalised as the [certificate-supply equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeFlatness.lean#L412). Proposition <a href="#res:complete" data-reference-type="ref" data-reference="res:complete">23</a> supplies the fixed-parameter equivalence; Theorem <a href="#res:pointwisecomplete" data-reference-type="ref" data-reference="res:pointwisecomplete">24</a> assembles all fixed pairs; and Theorem <a href="#res:red21" data-reference-type="ref" data-reference="res:red21">25</a> replaces pointwise placement by the equivalent cofinal placement quantifier.

Every multiple of an eventual period is again a period, and every fixed $`h`$ divides $`M_t`$ for all $`t\geq h`$. The least common multiple therefore provides an exact one-parameter form: the single diagonal family $`(M_t,M_t)`$ tests every candidate period at once.

<div id="res:diag" class="theorem">

**Theorem 26** (exact diagonal characterisation). *The following are equivalent:
``` math
\begin{aligned}
 &S\notin\mathbb{Q};\\
 &\forall\,t_0\in\mathbb{N}\ \exists\,t\geq t_0\ \exists\,L,\qquad
   \mathsf{Sep}(M_t,M_t,L).
\end{aligned}
```*

</div>

The complete equivalence is the [exact lcm-diagonal characterisation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeFlatness.lean#L426). Its reverse implication reuses the diagonal-supply theorem, while its forward implication uses Theorem <a href="#res:pointwisecomplete" data-reference-type="ref" data-reference="res:pointwisecomplete">24</a> at the pair $`(M_{t_0},M_{t_0})`$. The theorem replaces the two free parameters $`h,N`$ by $`(M_t,M_t)`$; producing that cofinal one-parameter family is still open.

<div id="res:deposits" class="example">

**Example 27** (verified finite range). Lean checks:

- $`\mathsf{Sep}(h,12,16)`$ for every $`1\le h\le8`$;

- a fixed-window certificate for every $`1\le h\le16`$;

- diagonal certificates $`\mathsf{Sep}(M_t,M_t,L)`$ at $`t=1`$ and every lcm-height change endpoint $`2\le t\le64`$ (that is, $`M_{t-1}<M_t`$), namely
  ``` math
  t\in\{1,2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,
  47,49,53,59,61,64\};
  ```

- a finite joint certificate refuting cone flatness at a tabulated family of vertices.

</div>

The four validation classes are formalised, in order, by the [small-window certificate family](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TotientTailPeriodKiller.lean#L404), [periods through sixteen](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CarrySurvivorExtinction.lean#L574), [28 imported diagonal certificates through scale 64](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalPincerCertificatesT64.lean#L1967), and [cone-cell certificate table](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeNonflat.lean#L506).

For example, at $`(h,N,L)=(1,12,16)`$,
``` math
\Delta_{1,12,16}=-143140,\qquad
\Delta_{1,12,16}\bmod 2^{16}=53468,
```
while the omitted-tail allowance is $`12+1+16+2=31`$. Hence
``` math
31<53468<2^{16}-31,
```
which is exactly $`\mathsf{Sep}(1,12,16)`$ and therefore proves $`R_{13}-R_{12}\notin\mathbb{Z}`$. Every row above has this exact status: it proves a particular non-integral tail difference, not an unbounded supply.

<a id="sec:249-open"></a>

## What remains open

By Theorem <a href="#res:red21" data-reference-type="ref" data-reference="res:red21">25</a>, the unresolved statement is precisely
``` math
\forall h\ge1\ \forall N_0\ge0\ \exists N\ge N_0\ \exists L\ge1,\qquad
\mathsf{Sep}(h,N,L).
\tag{5.1}\label{eq:unbounded-certificate-supply}
```
The diagonal condition in Theorem <a href="#res:diag" data-reference-type="ref" data-reference="res:diag">26</a> is an equivalent one-parameter form of this statement. The verified scales in Example <a href="#res:deposits" data-reference-type="ref" data-reference="res:deposits">27</a> form a finite set and establish neither cofinal quantifier pattern. No theorem in the formal source proves <a href="#eq:unbounded-certificate-supply" data-reference-type="eqref" data-reference="eq:unbounded-certificate-supply">[eq:unbounded-certificate-supply]</a>; consequently no irrationality claim for $`S`$ is made here.

<div class="remark">

*Remark 2* (finite inspection cannot establish the supply). The finite status of the verified scales is forced, not cautious. Fix a bound $`B\ge1`$ and a period $`P>B`$, and define $`\gamma(n)=\varphi(n)`$ for $`n\le B`$, while for $`n>B`$ let $`\gamma(n)=n-1`$ if $`P\mid n`$ and $`\gamma(n)=n`$ otherwise. Then $`0\le\gamma(n)\le n`$, and
``` math
\sum_{n\ge1}\frac{\gamma(n)}{2^n}
 =\sum_{n\le B}\frac{\varphi(n)}{2^n}+\frac{B+2}{2^B}-\frac1{2^P-1}
```
is rational, and its reduced denominator has odd part exactly $`2^P-1`$. Every finite computation that inspects only coefficients with index at most $`B`$ — in particular every certificate $`\mathsf{Sep}(h,N,L)`$ with $`N+h+L\le B`$ — returns the same result for $`\gamma`$ as for $`\varphi`$, and choosing $`P`$ with $`2^P-1>Q_0`$ makes the splice consistent with the denominator exclusion as well. This elementary splice is not formalised in the source and proves nothing about $`\varphi`$ itself; it shows that a proof of <a href="#eq:unbounded-certificate-supply" data-reference-type="eqref" data-reference="eq:unbounded-certificate-supply">[eq:unbounded-certificate-supply]</a> must use totient values at unbounded indices, so no extension of the finite record in Example <a href="#res:deposits" data-reference-type="ref" data-reference="res:deposits">27</a> can establish the supply.

</div>

Appendix <a href="#app:totient-normal" data-reference-type="ref" data-reference="app:totient-normal">11.1</a> records the exact reformulations of this open obligation. Appendix <a href="#app:totient-finite" data-reference-type="ref" data-reference="app:totient-finite">11.2</a> records fixed-scale enclosures, projections, and certificates, then states separately the conditional cofinal criteria that use them as hypotheses. Appendices  <a href="#app:totient-boundaries" data-reference-type="ref" data-reference="app:totient-boundaries">11.3</a>–<a href="#app:totient-rank" data-reference-type="ref" data-reference="app:totient-rank">11.4</a> delimit candidate unbounded routes. None supplies the missing cofinal quantifier.

<a id="sec:architecture"></a>

# One transform and the shared finite-to-cofinal bottleneck

This section collects the structure the two open reductions share and states its limits. Every mathematical assertion in it is proved elsewhere in the paper; the section adds organisation, not theorems, and its closing remark is an elementary unformalised observation, flagged as such.

<a id="sec:one-transform"></a>

## One transform, one mechanism, three questions

The Lambert rearrangement of Section <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a> factors the common transform through two maps, the divisor transform followed by binary evaluation:
``` math
f\;\longmapsto\;f*\mathbf 1\;\longmapsto\;
 \sum_{m\ge1}\frac{(f*\mathbf 1)(m)}{2^m}\;=\;L(f).
```
Every series in this paper is an instance. The primitive-conductor input $`f=\alpha`$ gives $`L(\alpha)=S`$ with divisor stream $`\alpha*\mathbf 1=\varphi`$ (Proposition <a href="#res:lift" data-reference-type="ref" data-reference="res:lift">3</a>); a support indicator $`f=\mathbf 1_A`$ gives $`L(\mathbf 1_A)=X_A`$ with divisor stream $`f_A`$ (Appendix <a href="#app:carry-boolean" data-reference-type="ref" data-reference="app:carry-boolean">10.2</a>); and the comparison inputs $`\mu`$, $`\mathbf 1`$, and $`\varphi`$ give the rungs of Section <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a>.

Rationality acts on all of these through one mechanism. For any $`\mathbb{N}`$-valued stream $`\gamma:\mathbb{N}\to\mathbb{N}`$ with $`\gamma(n)\le n`$, a class containing both $`\varphi`$ and every $`f_A`$, Theorem <a href="#res:rigidity" data-reference-type="ref" data-reference="res:rigidity">45</a> identifies rationality of $`\sum_n\gamma(n)2^{-n}`$ with the existence of a tempered integer orbit: after multiplication by one denominator, the coefficient stream is the exact one-step doubling difference $`2u(N)-u(N+1)`$ of an integer sequence of size $`o(2^N)`$. The tail differences of Section <a href="#sec:reduction" data-reference-type="ref" data-reference="sec:reduction">5.3</a> and the carry states of Theorem <a href="#res:rigidity-main" data-reference-type="ref" data-reference="res:rigidity-main">7</a> are two coordinate systems for this one orbit condition. Möbius inversion then identifies the arithmetic input beneath the coefficient stream: the fixed weight $`\alpha=\varphi*\mu`$ on the \#249 side, and the Boolean indicator $`\mu*f_A=\mathbf 1_A`$ on the \#257 side (Proposition <a href="#res:boolmob" data-reference-type="ref" data-reference="res:boolmob">47</a>).

The three open questions are then three different questions about this one map.

1.  Erdős #249 fixes the input and asks about one image point: is $`L(\alpha)=S`$ rational?

2.  Universal \#257 restricts the domain to indicators of infinite supports and asks whether the image of that domain meets $`\mathbb{Q}`$ at all.

3.  The half-value route fixes the target and asks whether the fibre over $`1/2`$ meets the same domain; by Theorem <a href="#res:greedy" data-reference-type="ref" data-reference="res:greedy">6</a> the fibre over any value contains at most one positive-exponent support, so the question concerns one canonical greedy orbit.

Figure <a href="#fig:transform" data-reference-type="ref" data-reference="fig:transform">1</a> displays the five inputs and the three question slices. The trichotomy describes where the questions sit inside one transform. It is not a theorem transferring information between them, and the next subsection records exactly why no transfer follows.

<figure id="fig:transform" data-latex-placement="H">

<figcaption>The one transform behind the paper, with the statuses of Section <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a>. Labels (i)–(iii) are the three questions of Section <a href="#sec:one-transform" data-reference-type="ref" data-reference="sec:one-transform">6.1</a>: #249 fixes the top input and asks about the single image point <span class="math inline"><em>S</em></span>; universal #257 restricts the domain to indicators of infinite supports and asks whether its image ever meets <span class="math inline">ℚ</span>; the half-value route fixes the value <span class="math inline">1/2</span>, reached by the signed Möbius input through the stream <span class="math inline">1, 0, 0, …</span>, and asks whether an infinite Boolean input reaches it as well. The figure organises statements proved in Sections <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a>–<a href="#sec:eb" data-reference-type="ref" data-reference="sec:eb">4</a> and Appendix <a href="#sec:carry" data-reference-type="ref" data-reference="sec:carry">10</a>; it asserts nothing further. Colour marks status: green rational, blue irrational, amber open.</figcaption>
</figure>

<a id="why-no-status-transfers"></a>

## Why no status transfers

The transform alone does not determine arithmetic status. The values formalised or cited in Section <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a> include rational examples $`L(\varphi)=2`$ and $`L(\mu)=1/2`$, the irrational example $`L(\mathbf 1)=E`$, the transcendental example $`L(\mathrm{Id})`$, and the open value $`L(\alpha)=S`$.

Simple properties of the input do not distinguish these cases. Both $`\varphi`$ and $`\mathbf 1`$ are positive and multiplicative with at most linear growth, yet their transforms are respectively rational and irrational. Boolean coefficients alone are also insufficient: every finite support has rational value, while the infinite supports of Theorem <a href="#res:support" data-reference-type="ref" data-reference="res:support">5</a> have irrational values. The finite example $`\{2,3\}`$, whose value is $`10/21`$, and its period-six carry orbit are worked out in Appendix <a href="#app:carry-boolean" data-reference-type="ref" data-reference="app:carry-boolean">10.2</a>.

A proof of an open case must therefore use arithmetic specific to its input: the dyadic structure of exact totient values for \#249, the interaction between the Boolean Möbius condition and infinitude for universal \#257, or the divisor feedback of the greedy orbit for the half-value fibre. Appendix <a href="#app:totient-boundaries" data-reference-type="ref" data-reference="app:totient-boundaries">11.3</a> rules out several arguments based only on generic input properties and identifies arithmetic information that a successful method would still need.

<a id="the-shared-bottleneck"></a>

## The shared bottleneck

Both reductions express their conclusions through finite events that must occur at arbitrarily large scales, but the conclusions point in opposite directions:
``` math
\begin{aligned}
 S\notin\mathbb{Q}
 &\quad\Longleftrightarrow\quad
 \text{\(\mathsf{Sep}(h,N,L)\) occurs cofinally for every \(h\)},\\
 \frac12\in\mathcal A
 &\quad\Longleftrightarrow\quad
 \text{\(\tau_s=0\) occurs cofinally}.
\end{aligned}
```
For $`S`$, Proposition <a href="#res:complete" data-reference-type="ref" data-reference="res:complete">23</a> supplies fixed completeness, Theorem <a href="#res:pointwisecomplete" data-reference-type="ref" data-reference="res:pointwisecomplete">24</a> gives the pointwise global form, and Theorem <a href="#res:red21" data-reference-type="ref" data-reference="res:red21">25</a> gives the displayed cofinal form. For $`1/2`$, Theorem <a href="#res:halfmembership" data-reference-type="ref" data-reference="res:halfmembership">14</a> identifies membership with cofinal zeros of the terminal bit $`\tau_s`$ of Definition <a href="#def:terminal-bit" data-reference-type="ref" data-reference="def:terminal-bit">13</a>. In both cases the missing step is a theorem producing the required finite events at unbounded scales. Neither such theorem is known. The classical full-support comparison is already proved: its Bertrand–CRT and averaging argument constructs the required witnesses uniformly at every precision. The coordinate identities and rational-support filters used elsewhere in the paper do not alter either missing quantifier.

Thus the comparison also gives a criterion for further progress. On the \#249 side, a new local identity affects the open problem only if it produces or rules out $`\mathsf{Sep}`$-certificates at unbounded parameters. On the half-value side of \#257, it must produce cofinal terminal zeros or prove that the greedy seam is eventually right. Further fixed-scale computation, by itself, changes neither open statement.

<a id="what-finite-witnesses-can-decide."></a>

#### What finite witnesses can decide.

The two reductions use different finite witnesses. A $`\mathsf{Sep}`$-certificate proves that one specified tail difference is non-integral; a fatal half-gap proves that no support extending one specified prefix can reach $`1/2`$. In neither case does survival of every check performed so far prove the opposite conclusion.

There is nevertheless an asymmetry. By Theorem <a href="#res:fatalright" data-reference-type="ref" data-reference="res:fatalright">17</a>, $`1/2\notin\mathcal A`$ is equivalent to the existence of a fatal half-gap. Exact rational evaluation of the greedy orbit, together with the rational tail enclosures of Proposition <a href="#res:death" data-reference-type="ref" data-reference="res:death">57</a>, can therefore certify nonmembership after a finite discovery. Membership still requires terminal zeros at arbitrarily large rows.

For $`S`$, neither rationality nor irrationality has a single finite witness in this certificate system. One $`\mathsf{Sep}`$-certificate proves one non-integral tail difference, whereas irrationality requires such certificates cofinally for every positive shift. Rationality forces eventual integrality, but failure to find a certificate at a given truncation is inconclusive: a longer truncation may still certify the same tail difference.

<div class="remark">

*Remark 3* (boundaries visible from the normal forms). Two elementary observations, neither formalised in the source, show that the missing quantifiers cannot be crossed by finite inspection or by the shared geometry alone. For \#249, a coefficient stream agreeing with $`\varphi`$ on every index inspected by any fixed finite family of computations extends to a rational series in the same class; the splice is recorded in Section <a href="#sec:249-open" data-reference-type="ref" data-reference="sec:249-open">5.4</a>. For the half-value fibre, the strict-tail axioms and any finite prefix of greedy decisions are jointly consistent with both outcomes: replacing the weights beyond the inspected range by a ratio-one-third geometric sequence with total mass below the pending residual (respectively equal to it) preserves strict tails, leaves every inspected decision unchanged, and makes the last inspected skip final (respectively realises the target as the modified system’s complete remaining sum). A membership proof must therefore use the specific Mersenne arithmetic of the tail, not only its superincreasing geometry.

</div>

<a id="sec:verify"></a>

# Formal verification and reproducibility

This section records proof authority and reproducibility; it does not add a mathematical conclusion to either reduction.

<a id="proof-authority-and-source-identity."></a>

#### Proof authority and source identity.

The Lean 4 proof assistant \[lean\] and Mathlib library \[mathlib\] check the named results. The source, exact informal-to-formal links, and build instructions are available in the [public repository](https://github.com/wcook04/plectis-lean-erdos249-257). This draft names formal-source revision `c2c5c3f0151d`, but that revision must be present in the public repository before release. Until the source commit is pushed and the source-coordinate checker is rerun, the blue links are navigation text rather than a reproducible proof-authority route. The final published revision must also pin the Lean and Mathlib versions; the intended toolchain is Lean `v4.29.1`.

<a id="reproduction-commands-and-artefact-identities."></a>

#### Reproduction commands and artefact identities.

For release, a cold clone at the published revision must pass `lake build`; the release-validation command must then check the claim registry, source coordinates, manuscript anchors, projections, trust guards, the rendered PDF, and the immutable committed reference. This draft does not carry that completed release receipt. The machine-readable corpus descriptor records SHA-256 identities for the claim registry, declaration atlas, manuscript source, rendered PDF, and toolchain projections, together with their regeneration commands. No hardware-independent build time is claimed; elapsed time depends on the Lean cache and machine, and is not part of the mathematical claim.

<a id="computational-and-expository-boundary."></a>

#### Computational and expository boundary.

Every declaration is elaborated by Lean and every proof term is checked by the kernel. Finite calculations use kernel-reducible procedures such as `decide`, `norm_num`, or explicit certificate proofs. In particular, the [finite survivor-count theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfFinalMiddlePhaseSieve.lean#L2050) uses `decide` under a finite declaration-local recursion-depth budget; its axiom audit contains no `Lean.trustCompiler` and no proof placeholder. Machine-generated certificate files are Lean source; no external certificate dataset, Python release script, generated index, or this manuscript is proof authority. Appendix <a href="#app:index" data-reference-type="ref" data-reference="app:index">13</a> explains how each displayed result is connected to its exact formal statement.

<a id="section-consequence.-1"></a>

#### Section consequence.

After the source commit is published and the committed-ref release checks pass, the linked declarations and their checked proof terms will certify the stated proved, conditional, finite, and equivalence results at that revision. That verification does not change the mathematical status of the unresolved statements: the open problems collected in Section <a href="#sec:further" data-reference-type="ref" data-reference="sec:further">8</a> remain open.

<a id="sec:further"></a>

# Exact remaining problems and further questions

Section <a href="#sec:spines" data-reference-type="ref" data-reference="sec:spines">2</a> gives the exact reductions. Here we record two concrete sufficient criteria and then state the unresolved questions. Erdős \#249 has one open obligation in two equivalent forms. Erdős \#257 has a universal statement and a counterexample route pointing in opposite directions: half-value membership would refute the universal statement, while nonmembership would decide only the half-value question.

<a id="two-concrete-scalar-criteria"></a>

## Two concrete scalar criteria

Two scalar conditions give concrete sufficient routes toward the two open directions. Both are exact arithmetic statements; neither is proved at the unbounded range needed for its final conclusion.

For \#249, retain $`M_t=\operatorname{lcm}(1,\ldots,t)`$ and write
``` math
P_L(N)=\sum_{j=0}^{L-1}\varphi(N+1+j)\,2^{L-1-j}.
```
The canonical adjacent-suffix depth and its residue are
``` math
m_t=\lfloor\log_2 M_t\rfloor+10,\qquad
 d_t=\bigl(P_{m_t}(2M_t)-P_{m_t}(M_t)\bigr)\bmod 2^{m_t},
```
where $`0\le d_t<2^{m_t}`$. Define
``` math
\sigma_t=\min\bigl(d_t-2^{m_t-5},
    (2^{m_t}-2^{m_t-5})-d_t\bigr)\in\mathbb{Z}.
```

<div id="res:slackfrontier" class="proposition">

**Proposition 28** (canonical central-band equivalence). *For every $`t\ge1`$, the canonical residue lies in the central band $`[2^{m_t-5},2^{m_t}-2^{m_t-5}]`$ if and only if $`\sigma_t\ge0`$.*

</div>

This fixed-scale equivalence and its cofinal strict-jump form are the [canonical central-band equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalFreshLossBridge.lean#L2469) and [strict-jump slack equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalFreshLossBridge.lean#L2559).

<div id="res:slackcriterion" class="corollary">

**Corollary 29** (cofinal strict-jump slack criterion). *If, for every $`t_0`$, there is a $`t\ge\max\{3,t_0\}`$ such that
``` math
M_t<M_{t+1}\qquad\text{and}\qquad \sigma_t\ge0,
```
then $`S`$ is irrational.*

</div>

This implication is the [cofinal-slack irrationality criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalFreshLossBridge.lean#L2731). The proposition identifies equivalent scalar forms; the corollary is one-way and does not prove that $`\sigma_t`$ is nonnegative cofinally. No necessity implication is proved: completeness supplies some successful depth at every non-integral diagonal difference, but nothing forces success at the canonical depth $`m_t`$. Cofinal failure would refute this route, not prove irrationality of $`S`$.

For \#257, write $`r_n`$ for the exact greedy residual of the target $`1/2`$ and put
``` math
u_n=4^n(2r_n-2^{-n}).
```
Here $`u_n`$ is the normalized phase exposing the Mersenne tail’s second geometric channel.
``` math
\frac16+\frac{37}{56}2^{-n}\le \left|u_n-\frac13\right|.
```
We call this the *second-channel separation condition*; it constrains the distance from $`1/3`$, and $`u_n`$ may be negative (as it is at $`n=3,4`$).

<div id="res:secondfrontier" class="proposition">

**Proposition 30** (finite second-channel separation). *The second-channel separation condition is decidable over $`\mathbb{Q}`$ and holds for $`1\le n\le6`$.*

</div>

This is the [finite second-channel separation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L2723).

<div id="res:secondcriterion" class="corollary">

**Corollary 31** (second-channel separation criterion). *If the second-channel separation condition holds for every $`n\ge7`$, then $`1/2`$ belongs to the Mersenne achievement set $`\mathcal A`$.*

</div>

This implication is the [from-seven membership criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L2901). The membership conclusion is itself exact:
``` math
1/2\in\mathcal A
  \quad\Longleftrightarrow\quad
  \text{the canonical greedy orbit omits infinitely many exponents}.
```
This is formalised at [half-membership–infinite-skip equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L2514). The forward implication uses the [full-support irrationality theorem](#res:full); for the reverse, if a residual ever exceeds the remaining tail, every later exponent is selected; hence only finitely many omissions remain. Thus the separation condition suffices for the infinite-skip condition. It does not prove that condition, and membership alone is not the universal \#257 theorem. The finite proposition supplies no case of the missing range $`n\ge7`$.

<a id="dependency-direction."></a>

#### Dependency direction.

The two criteria have the proved logical form
``` math
\begin{array}{c}
 \text{cofinal nonnegative slack}\\[-1pt]
 \text{at strict lcm jumps}\\
 \Downarrow\\
 \text{unbounded \#249 certificate supply}\\
 \Downarrow\\
 S\notin\mathbb{Q}
\end{array}
\qquad\qquad
\begin{array}{c}
 \text{second-channel separation}\\[-1pt]
 \text{for every }n\ge7\\
 \Downarrow\\
 \dfrac12\in\mathcal A\\
 \Updownarrow\\
 \mathcal S(1/2)\text{ is infinite}.
\end{array}
```
Neither left-hand premise is proved. The verified range $`1\le n\le6`$ establishes only the finite prefix of the second criterion; it gives no part of the missing universal range $`n\ge7`$. The first conclusion settles \#249, whereas the second would refute, not prove, the universal \#257 statement.

<a id="the-unresolved-statements"></a>

## The unresolved statements

<a id="erdős-249-one-obligation-in-two-equivalent-forms."></a>

#### Erdős \#249: one obligation in two equivalent forms.

<div class="problem">

**Problem 32** (Erdős \#249). Prove that
``` math
S=\sum_{n\ge1}\frac{\varphi(n)}{2^n}
```
is irrational.

</div>

By Theorem <a href="#res:red21" data-reference-type="ref" data-reference="res:red21">25</a>, the preceding problem is equivalent to the following exact quantifier statement.

<div class="problem">

**Problem 33** (unbounded certificate supply). Prove <a href="#eq:unbounded-certificate-supply" data-reference-type="eqref" data-reference="eq:unbounded-certificate-supply">[eq:unbounded-certificate-supply]</a>. Equivalently, prove the lcm-diagonal supply in Theorem <a href="#res:diag" data-reference-type="ref" data-reference="res:diag">26</a>. The finite scales in Example <a href="#res:deposits" data-reference-type="ref" data-reference="res:deposits">27</a> do not establish either cofinal form.

</div>

These are not two independent open problems: Theorem <a href="#res:red21" data-reference-type="ref" data-reference="res:red21">25</a> and Theorem <a href="#res:diag" data-reference-type="ref" data-reference="res:diag">26</a> identify the second as an exact certificate form of the first.

<a id="erdős-257-universal-statement-and-counterexample-route."></a>

#### Erdős \#257: universal statement and counterexample route.

<div class="problem">

**Problem 34** (universal Erdős \#257). Prove that
``` math
\sum_{n\in A}\frac{1}{2^n-1}
```
is irrational for every infinite set $`A\subseteq\mathbb{N}_{>0}`$, rather than only for the support families in Theorem <a href="#res:support" data-reference-type="ref" data-reference="res:support">5</a>.

</div>

<div class="problem">

**Problem 35** (the half-value counterexample route). Decide whether $`1/2\in\mathcal A`$. By Theorem <a href="#res:halfmembership" data-reference-type="ref" data-reference="res:halfmembership">14</a>, this is equivalent to the canonical greedy orbit omitting infinitely many exponents. A positive answer would give an infinite support of rational value $`1/2`$ and refute the universal \#257 statement; a negative answer would decide only this distinguished point-membership question.

</div>

<a id="what-the-reductions-change."></a>

#### What the reductions change.

The results above change the form, not the status, of the open problems. For \#249, the unresolved content is one unbounded certificate-supply theorem, with the pointwise and lcm-diagonal forms proved equivalent to irrationality. For the half-value route to \#257, the search over arbitrary supports has been replaced by one canonical greedy-orbit question. In the present final-skip argument that question is localised further to two obligations: exclude the middle cells $`-2,-1`$, and prove the future-tail inequality at the remaining nonnegative-carry middle transitions. A cofinal \#249 certificate theorem would prove \#249; a cofinal terminal-zero theorem would refute universal \#257; and a proof of eventual right behaviour would prove only $`1/2\notin\mathcal A`$.

<a id="two-refinements-not-pursued."></a>

#### Two refinements not pursued.

Certificate completeness guarantees a least successful depth at every non-integral pair; we prove nothing about its growth in $`(h,N)`$, and a proved bound would decide each fixed pair by a bounded computation. On the support side, the zero-window theorem is inert against supports containing a small element (Appendix <a href="#app:carry-sublog" data-reference-type="ref" data-reference="app:carry-sublog">10.3</a>); a coverage law for the support outside every finite core would remove that triviality. We have not pursued either question.

<a id="statements-and-declarations"></a>

## Statements and declarations

<a id="artefact-and-data-availability."></a>

#### Artefact and data availability.

The [archived formal-source revision](https://github.com/wcook04/plectis-lean-erdos249-257/tree/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3) contains the Lean sources, pinned toolchain, library manifest, and generated certificate data used in the verification. Repository metadata and this manuscript provide navigation rather than proof authority; Section <a href="#sec:verify" data-reference-type="ref" data-reference="sec:verify">7</a> gives the verification route.

<a id="use-of-ai-assistance."></a>

#### Use of AI assistance.

Large-language-model assistants were used during development for proof drafting, refactoring, and prose editing. Every registered formal claim is linked to a declaration in the archived source revision. Lean checks each proof term against the pinned library; the project contains no proof placeholders or project-defined axioms.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem numbering and status follow the Erdős Problems catalogue maintained by Thomas Bloom \[erdosproblems\].

<a id="app:half-technical"></a>

# Technical reductions for the half-value branch

This appendix records the local arithmetic used to reach Theorems <a href="#res:halfmembership" data-reference-type="ref" data-reference="res:halfmembership">14</a> and <a href="#res:fatalright" data-reference-type="ref" data-reference="res:fatalright">17</a>, Proposition <a href="#res:finalskipexclusions" data-reference-type="ref" data-reference="res:finalskipexclusions">18</a>, and Corollary <a href="#res:taildominance" data-reference-type="ref" data-reference="res:taildominance">19</a>. Its statements fall into four classes: exact coordinate identities, conditional compactness criteria, bounded finite certificates, and counterexamples to tempting local inductions. None changes the two open conclusions at the end of Section <a href="#sec:eb" data-reference-type="ref" data-reference="sec:eb">4</a>. The appendix is included so that the hypotheses in the main reduction can be audited without turning the main theorem section into a chronology of the formal development.

The order is by mathematical use. Appendix <a href="#app:half-localizer" data-reference-type="ref" data-reference="app:half-localizer">[app:half-localizer]</a> localises one possible unsafe skip; Appendix <a href="#app:half-conditional-producers" data-reference-type="ref" data-reference="app:half-conditional-producers">9.2</a> records conditional structured-support criteria; Appendix <a href="#app:half-finite-cofinal" data-reference-type="ref" data-reference="app:half-finite-cofinal">9.3</a> collects the finite-window and compactness implications; Appendix <a href="#app:half-final-skip" data-reference-type="ref" data-reference="app:half-final-skip">9.4</a> develops the equivalent final-skip coordinates; and Appendix <a href="#app:half-evidence" data-reference-type="ref" data-reference="app:half-evidence">9.5</a> records verified finite instances, exact coordinate translations, counterexamples, and arguments that rule out several proposed strategies. This is a dependency map, not a second route to a conclusion.

The logical chain is
``` math
\begin{array}{rcl}
 \text{cofinal half-value witnesses from A.2--A.3}
 &\Longrightarrow& \frac12\in\mathcal A,\\
 \frac12\in\mathcal A
 &\Longrightarrow& \text{an infinite rational-valued support},\\
 \text{a final greedy skip}
 &\Longleftrightarrow& \frac12\notin\mathcal A,\\
 \text{the A.4 residual cell exclusions and tail bound}
 &\Longrightarrow& \text{no final skip},\\
 \text{no final skip}
 &\Longrightarrow& \frac12\in\mathcal A.
\end{array}
```
Every displayed implication is proved; the middle line is an exact classification. The open content lies in the antecedents of the first and fourth lines, which are the unproved cofinal and exclusion hypotheses; the second and fifth lines are unconditional consequences of results already stated. Appendix <a href="#app:half-localizer" data-reference-type="ref" data-reference="app:half-localizer">[app:half-localizer]</a> only localises one transition configuration, while Appendix <a href="#app:half-evidence" data-reference-type="ref" data-reference="app:half-evidence">9.5</a> supplies bounded evidence, coordinate changes, and no-go results. Neither creates a further implication that decides an open question.

Throughout this appendix:

- a *take* (respectively a *skip*) at rank $`n`$ is the greedy decision $`\varepsilon_n=1`$ (respectively $`\varepsilon_n=0`$);

- the *finite greedy seam at row $`s`$* is the Boolean word of Definition <a href="#def:terminal-bit" data-reference-type="ref" data-reference="def:terminal-bit">13</a>; an unqualified *seam* in this appendix is an adjacent pair of such words at a branch boundary, and the compounds seam pair, one-hole seam, first-wrap seam, and rewind seam carry this pair sense;

- the *square-root strip* at depth $`N`$ is the carry interval $`[1,H_N]`$ with $`H_N=2\lfloor\sqrt N\rfloor+4`$; an interval of carries kept available by a construction is *protected*;

- a *hole* of a seam is the missing carry value in an otherwise covered protected interval;

- a *rewind* is the inverse finite recurrence of a seam;

- the *transition carry* is the integer coordinate appearing in the exact residual identity, and the *remainder* of a row is its integer greedy residual;

- the *pulse* of a rank at row $`s`$ counts its divisor incidences at $`2s+1`$ and $`2s+2`$, the first counting twice; the pulse of a word is the sum over its ranks.

These terms denote mathematical objects, not stages of a proof search. Module-local coordinates not listed here (for example the centred, lazy, or first-wrap variants) are defined in the linked formal statements.

<a id="res:twothirdsband"></a>

## Exact localiser: a band formula for the final skip between two takes

<span id="app:half-localizer" label="app:half-localizer"></span>

This subsection has one diagnostic role: it gives the exact unsafe interval for a specified take–skip–take configuration. It helps interpret the transition geometry used in the final-skip analysis, but it is neither an orbit-level exclusion nor a premise that produces half-value membership.

One local configuration admits a simple exact description in full generality. Suppose a take at rank $`b`$ is followed by the next take at $`c>b+1`$. Put $`q=2^b-1`$, $`m=2^{c-1}`$, and write the residual immediately before the first take as $`1/R`$. When $`0<R<q`$, the final intervening skip is dyadically unsafe if and only if
``` math
\frac{q(m-1)}{q+m-1}<R<\frac{qm}{q+m}.
```
The interval has exact width
``` math
\frac{q^2}{(q+m)(q+m-1)}.
```
Formalised: [the general unsafe-band equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfGreedyTwoThirdsBand.lean#L88) and [the general band-width formula](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfGreedyTwoThirdsBand.lean#L104).

For a single intervening skip, $`c=b+2`$ and $`m=2q+2`$. The band becomes
``` math
\frac{q(2q+1)}{3q+1}<R<\frac{2q(q+1)}{3q+2},
```
with width $`q^2/((3q+1)(3q+2))<1/9`$, entirely between $`2q/3`$ and $`2q/3+2/9`$. No integral reciprocal lies in this window. In the corresponding positive odd integer formulation, with residual $`p/(2D)`$, membership in the cleared band forces $`p\ge7`$. Formalised: [the one-skip band equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfGreedyTwoThirdsBand.lean#L127), [the one-skip width formula](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfGreedyTwoThirdsBand.lean#L154), [the width bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfGreedyTwoThirdsBand.lean#L163), [the integral-reciprocal exclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfGreedyTwoThirdsBand.lean#L185), and [the odd-coordinate lower bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfGreedyTwoThirdsBand.lean#L231).

These are localisers, not orbit-level eliminations. They do not show that the greedy orbit of $`1/2`$ avoids any such band, and they do not identify the two remaining exceptional transition coordinates $`-2,-1`$ with dyadically unsafe skips.

<a id="app:half-conditional-producers"></a>

## Conditional criteria and local inputs for structured supports

The results here have three distinct roles. The bouquet criterion is a conditional irrationality theorem for one structured support family. The seam, strip, and terminal criteria are sufficient hypotheses for $`1/2\in\mathcal A`$. The dilation, prime-power, and return-carry results are local algebraic inputs that prove neither an irrationality conclusion nor half-membership without an additional supply hypothesis. Nothing in this subsection is a new unconditional case.

<a id="res:sunflower"></a>

### A conditional pairwise-coprime dilation criterion

Let $`A`$ be a finite-core orthogonal-petal bouquet: outside a finite frame, its elements have the form $`c_i p_i`$, where the cores $`c_i`$ divide one fixed integer and the nontrivial petals $`p_i`$ are pairwise coprime to that frame and to one another, with summable reciprocal mass. The formal construction also contains an explicit infinite example with alternating cores $`2`$ and $`3`$ and squared prime petals; every member of this support has exactly three prime factors with multiplicity.

For such a bouquet, the remaining input is an exact tail-selection predicate: at every positive binary scale it chooses a carry slot with a normalised tail at most $`16`$. Lean proves that this predicate supplies the needed forced-carry certificates and hence irrationality of the base-$`2`$ support series. The result is [the conditional bouquet irrationality theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SupportSunflowerDichotomy.lean#L540), with the carry bridge at [the forced-carry implication](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SupportSunflowerDichotomy.lean#L531). The tail-selection predicate itself is not proved here. Thus this is a conditional reduction for one structured support family, not a further unconditional case of Erdős #257.

<a id="res:compositedefect"></a>

### Composite dilation defects

For a support divisor count $`f_A(x)=\#\{d\in A:d\mid x\}`$, multiplication by a composite support element $`a`$ has an exact correction term. Besides the distinguished divisor $`a`$, the new divisors are counted by a finite defect which excludes divisors already present at $`x`$. The formal identity is [the composite-dilation identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CompositeDilationDefect.lean#L30). For a finite-core orthogonal-petal bouquet, the defect at a ray is bounded by the finite exceptional frame plus the divisor count of the petal support: [the bouquet defect bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CompositeDilationDefect.lean#L151). This records the local correction needed when dilation is not prime. It does not prove a correlation estimate, the sunflower tail selector, or an irrationality statement.

<a id="res:mixedlayer"></a>

### Mixed prime-power layers

The one-prime-power layer has a two-signature extension. Exact $`p`$-adic and $`q`$-adic layer operators commute, and, for distinct primes with the residual argument coprime to $`pq`$, their composite extracts the iterated exact-valuation pullback of the support coefficient. This is formalised by [the two-prime layer identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/MaximalOmegaLayer.lean#L39). The singleton support $`\{12\}`$ gives a checked $`(2^2,3)`$ example with value one at residual argument $`1`$: [the singleton-support calculation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/MaximalOmegaLayer.lean#L65). These are finite coefficient identities. They do not provide a decimation transport, a bounded-$`\Omega`$ conclusion, or an irrationality theorem.

<a id="res:halftrapping"></a>

### Half-trapping return carries

If rational-linear channels vanish on every relation killed by one scalar evaluation, their evaluation matrix has rank at most one; every nontrivial square minor therefore vanishes. The all-rank determinant statement is [the rank-one determinant criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfTrappingReturnCarry.lean#L42). For two reverse carries with a common coefficient word, a $`1/0`$ seam, and a common following overlap, the terminal difference is a power of two times an odd integer. A shared nonnegative Archimedean bound then gives the matching dyadic spacing inequality, formalised at [the dyadic spacing inequality](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfTrappingReturnCarry.lean#L191). The argument does not produce reverse-carry presentations or an earlier overlapping return; it supplies only the algebraic core of that conditional criterion.

<a id="res:halfcarryreachability"></a>

### Half-carry reachability

There is also a finite-prefix criterion for the target $`1/2`$. At an unresolved even seam, the scalar transition reaches every integer terminal carry except the single value $`2\delta-c`$; this is the exact equivalence [the even-seam reachability equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryReachability.lean#L235). A canonical description of such a seam at every sufficiently large even depth is an unproved hypothesis. Under that hypothesis, the finite admissible words are cofinal, by [the cofinal-admissibility implication](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryReachability.lean#L999), and compactness then produces an infinite support with sum exactly $`1/2`$: [the half-value compactness conclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryReachability.lean#L1027). Thus the formal result is a conditional reduction. It does not establish the canonical seam supply and does not prove Erdős #257.

<a id="cofinal-strip-returns."></a>

#### Cofinal strip returns.

The all-level strip hypothesis can be weakened for the canonical greedy half carry. Its uncentred, binary-scaled form is antitone. Consequently, if it returns to the square-root strip cofinally, then one sufficiently late return bounds every later scaled carry; the strip envelope divided by $`2^N`$ tends to zero. The resulting tempered centred carry yields a support selected by the greedy expansion whose series value is $`1/2`$; the finite-support exclusion makes that support infinite.

<div id="res:cofinalstripreturn" class="proposition">

**Proposition 36** (cofinal strip-return criterion). *Let $`G_M`$ be the uncentred integer carry of the canonical greedy expansion of $`1/2`$. If
``` math
\forall N\in\mathbb{N}\;\exists M\geq N,\qquad
 G_M\leq 2\lfloor\sqrt{M+1}\rfloor+4,
```
then $`1/2\in\mathcal A`$, and its canonical greedy support is infinite.*

</div>

Formalised: [scaled-carry decay](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CofinalStripReturn.lean#L84) and [the strip-return membership criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CofinalStripReturn.lean#L157). The cofinal return condition itself is not established. It is weaker than a uniform strip bound and still does not give an unconditional membership theorem.

<a id="terminal-only-cofinal-approximation."></a>

#### Terminal-only cofinal approximation.

Coherence can be removed entirely from a further version of this reduction. At depth $`M`$, take only a normalised finite word whose terminal half carry lies in the square-root strip. Its finite support then has support-series value within
``` math
\frac{4M+12}{2^M}
```
of $`1/2`$. If such terminal witnesses occur cofinally, these finite values converge to $`1/2`$; closedness of the Mersenne achievement set supplies the limit. No control of the earlier rows, and no compatibility between the witnesses, is used.

<div id="res:terminalonlycofinal" class="proposition">

**Proposition 37** (terminal-only cofinal criterion). *Cofinal normalised terminal witnesses in the square-root strip imply that $`1/2`$ belongs to the Mersenne achievement set, and hence that an infinite support has support-series value $`1/2`$.*

</div>

Formalised: [the terminal approximation bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TerminalOnlyCofinal.lean#L68), [the terminal-strip compactness criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TerminalOnlyCofinal.lean#L134), and [the infinite-support conclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TerminalOnlyCofinal.lean#L192). The cofinal terminal-witness supply is not proved. In particular, the proposition does not establish membership of $`1/2`$ unconditionally.

<a id="scaled-terminal-vanishing."></a>

#### Scaled terminal vanishing.

The square-root strip is stronger than the analytic condition used by the terminal-only argument. Let the depths of normalised finite words tend to infinity. If their terminal carries, after division by the corresponding power of $`2`$, tend to zero, then the universal coefficient-tail error also tends to zero. The finite support values therefore converge to $`1/2`$, and closedness of the achievement set again supplies the limit. The earlier terminal-only strip condition implies this weaker sequential hypothesis.

<div id="res:terminalscaledvanishing" class="proposition">

**Proposition 38** (scaled terminal-vanishing criterion). *A normalised terminal-word sequence with depths tending to infinity and vanishing binary-scaled terminal carries yields an infinite support with support-series value $`1/2`$.*

</div>

Formalised: [the scaled terminal error bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TerminalOnlyScaledVanishing.lean#L24), [the scaled-vanishing compactness criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TerminalOnlyScaledVanishing.lean#L165), and [the scaled-vanishing support conclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TerminalOnlyScaledVanishing.lean#L221). No such scaled-vanishing sequence is constructed here; the result is a conditional reduction, not an unconditional membership theorem.

<a id="app:half-finite-cofinal"></a>

## Finite-to-cofinal criteria: windows, seams, and compactness

Every half-value route in this subsection factors as
``` math
\text{finite witness at depth }N
 \quad+\quad
 \text{a cofinal supply of such depths}
 \quad\Longrightarrow\quad
 \frac12\in\mathcal A.
```
The local identities and recurrences describe or advance one finite witness. The compactness statements turn a cofinal supply into membership. No result below proves that supply, so a verified window or seam at one depth is evidence for a possible recurrence, not an unbounded theorem.

<a id="res:halfcylindershadow"></a>

### Finite shadows of the half cylinder

For an admissible finite word, the residual from $`1/2`$ is given exactly by its terminal half carry minus the future coefficient tail, scaled by a power of two; see [the finite-shadow residual identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderFiniteShadow.lean#L55). At a first seam, avoiding the integer strip is equivalent to full scalar reachability of that strip: [the seam-escape equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderFiniteShadow.lean#L807). The rank-three greedy example is raw dyadically safe while its seam has an in-strip hole, so raw safety alone does not imply this escape. Finally, an explicit frozen-margin hypothesis implies $`1/2`$ belongs to the Mersenne achievement set, by [frozen-margin implication](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderFiniteShadow.lean#L1256). That hypothesis is unproved; this is a conditional reduction, not a proof of Erdős #257.

<a id="res:fixedcoeffrewind"></a>

### Fixed-coefficient rewind

For a finite list of common coefficients, the canonical inverse-parent map has an exact closed form with a power-of-two denominator: [the rewind closed form](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryCeilParentContraction.lean#L49). An interval of width at most that denominator contracts either to one ancestor or to two adjacent ancestors. The singleton alternative is equivalent to the explicit dyadic phase inequality, while the other alternative is a seam pair; see [the singleton-or-seam dichotomy](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryCeilParentContraction.lean#L180). Thus width alone does not justify a singleton conclusion. This is a finite rewind lemma, and supplies neither a seam exclusion nor an Erdős #257 conclusion.

<a id="res:selectedhalfwindow"></a>

### Selected half-carry windows

The selected-window construction keeps an explicit admissible word for each terminal carry in a finite protected interval. A supply of such windows at all sufficiently large levels gives cofinal admissibility and hence an infinite support with sum $`1/2`$: [selected-window cofinality](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarrySelectedWindow.lean#L831) and [the selected-window half-value conclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarrySelectedWindow.lean#L864). The unresolved input is the coherent history at each step: either a common next-row divisor cylinder, or the canonical adjacent seam. The theorem states this input exactly; it does not construct the window supply and does not prove Erdős #257.

<a id="res:rewindphase"></a>

### A realised rewind criterion

For a realised fixed-coefficient history, the dyadic rewind phase is the complementary binary suffix numeral: [the suffix-phase identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryRewindPhase.lean#L39). Consequently the singleton criterion is exactly the inequality that this suffix numeral covers the rest of the terminal interval, formalised by [the suffix-coverage criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryRewindPhase.lean#L65). This converts the phase condition into support-history coordinates, but does not prove the required coverage inequality globally.

<a id="res:protectedseam"></a>

### Localised protected seams

The compactness argument needs only one admissible word at cofinally many depths. At a localised one-hole seam, one of the two protected carries $`3`$ and $`4`$ survives; therefore a cofinal supply of realised protected seams implies cofinal admissibility by [the protected-seam cofinality implication](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryProtectedSeamConsumer.lean#L31), and hence an infinite support with sum $`1/2`$, [by compactness](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryProtectedSeamConsumer.lean#L53). The cofinal realisation supply is not proved.

<a id="res:cofinalwindowseam"></a>

### Combining the two cofinal half-carry criteria

Assume that at each requested scale there is either a selected protected window or a localised realised seam. Each alternative supplies the one admissible word needed for compactness, so this cofinal disjunction implies an infinite support with sum $`1/2`$: [by window-or-seam cofinality](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryCofinalWindowOrSeamConsumer.lean#L32) and [by the window-or-seam half-value conclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarryCofinalWindowOrSeamConsumer.lean#L58). The cofinal disjunction remains unproved.

<a id="res:integergreedy"></a>

### Integer-greedy first-wrap reduction

The first-wrap seam has exact truncated Mersenne weights with a quantitative gap-dominance property. For these weights, a small positive subset-sum defect exists exactly when the descending integer-greedy remainder is small and positive; this is formalised by [the integer-greedy remainder equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderIntegerGreedy.lean#L654). The remaining arithmetic input is an unbounded lower bound for that deterministic remainder sequence. No such lower bound is proved here.

<a id="res:concreteseam"></a>

### Exact finite recurrence for the greedy seam

The finite seam-word construction realises the abstract adjacent cut by concrete Boolean words and identifies its next word with the integer-greedy choice: [the seam-word recurrence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderConcreteSeamAdapter.lean#L667). It implements a finite recurrence, not the unbounded remainder estimate.

<a id="app:half-final-skip"></a>

## Exact final-skip reduction and its residual cells

This is the only subsection that feeds the main final-skip reduction directly. It first identifies nonmembership with a final skip and membership with cofinal terminal zeros. It then separates the terminal cells already excluded from the two unresolved middle coordinates and the unresolved future-tail inequality. The later largest-skip, pulse, and reset formulas are conditional ways to attack those residual obligations; they do not add a second conclusion.

<a id="app:fatalright-detail"></a>

### Fatal gaps and eventual right tails

For the concrete integer seam words, eventual right extension is equivalent to nonmembership of $`1/2`$ in the Mersenne achievement set: [the eventual-right nonmembership equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderFatalGapRightTail.lean#L787). The same condition is equivalent to the existence of a finite fatal half gap, by [the fatal-gap equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderFatalGapRightTail.lean#L781), and also to a final skipped exponent in the real greedy orbit, by [the final-skip equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderFatalGapRightTail.lean#L802). Thus this equivalence gives an exact classification of the nonmembership branch. It neither decides whether $`1/2`$ belongs to the achievement set nor proves the universal Erdős #257 statement.

This is the nonmembership half of the argument summarised earlier: a last greedy skip is equivalent to eventual right extension. The following paragraph records the first exceptional middle case that can be ruled out.

<a id="first-final-middle-cell."></a>

#### First final-middle cell.

The first exceptional middle cell has a separate obstruction: if the orbit extends right after the last skipped rank, then the cell with transition carry $`-3`$ makes the lazy cofinite tail strictly smaller than $`1/2`$ while its centred carry becomes negative. This is impossible by the analytic nonnegativity identity, [the middle-$`-3`$ exclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L587). It removes that one conditional terminal configuration; it does not decide the right-tail branch or the remaining two middle cells.

<a id="second-final-middle-cell."></a>

#### Second final-middle cell.

The next cell, with transition carry $`-2`$, is not eliminated. Here its *phase* means the triple of residue classes of the putative last skip $`D`$ modulo $`21`$, $`10`$, and $`13`$. The possible phases are nevertheless sharply constrained. Uniformly for seam rows $`s\ge27`$, the greedy decisions through rank $`26`$ select exactly the ranks
``` math
2,3,6,7,14,20,21,26,
```
by [the exact rank-(26) prefix](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfFinalMiddlePhaseSieve.lean#L1190).

If $`D\ge27`$ lies in this middle cell and is followed by an all-right suffix, then
``` math
D\bmod21\in\{11,14,17,20\},\qquad D\bmod10\ne8,
 \qquad D\bmod13\ne11,
```
the class $`D\bmod10=7`$ cannot pair with $`D\bmod21=11`$, and the class $`D\bmod13=10`$ cannot pair with $`D\bmod21=11`$. The orbit theorem is [the final-middle phase sieve](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfFinalMiddlePhaseSieve.lean#L1913). The three moduli are pairwise coprime, so their phase triples correspond to the $`21\cdot10\cdot13=2730`$ residue classes modulo $`2730`$. Exactly $`412`$ survive; this finite count is [the exact survivor count](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfFinalMiddlePhaseSieve.lean#L2050). This is a uniform exact reduction of the $`-2`$ cell, not its exclusion; the surviving phases, the $`-1`$ cell, and the right-tail branch remain open. A smaller survivor proportion at deeper ranks would still not exclude the cell. A nested system of nonempty residue classes can have vanishing density and a nonempty inverse limit. This route must therefore either reach finite extinction at some rank or add an Archimedean estimate at a surviving phase.

The remaining global reduction is now precise. If every genuine middle transition other than the already discharged $`C_D=-3`$ cell has transition carry larger than its complete future divisor-incidence tail, then an eventual right seam is impossible and $`1/2`$ belongs to the Mersenne achievement set: [middle-tail implication](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderLastProducerContradiction.lean#L387). The stronger square-root lower-bound hypothesis is also sufficient, [square-root sufficient condition](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderLastProducerContradiction.lean#L409). Neither hypothesis is supplied here.

For finite seam prefixes the remaining tail bound sharpens further: the future divisor-incidence tail is bounded by the cardinality of the prefix. Thus the explicit row-scale inequality $`\#G_D+\mathrm{belowPulse}_D+5<4\,\mathrm{remainder}_D`$ is sufficient for the same half-membership conclusion. The hypothesis is [the cardinality escape condition](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L111), and the resulting membership theorem is [the prefix-cardinality bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1503); it is enough in turn that every late middle remainder is at least its row, [row-scale sufficient condition](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1510). These are exact conditional reductions, not proofs of the row bound.

<a id="finite-upper-reset-band-certificates."></a>

#### Finite upper-reset band certificates.

The companion upper branch has a kernel-checked finite certificate: for every upper transition from rows $`13`$ through $`30`$, every subsequent dyadic danger band is avoided. The certificate shares each exact successor remainder across all its band indices, [the verified upper-reset certificate](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderUpperResetBandCertificates.lean#L78). It is a bounded transition check and does not supply the cofinal band-escape hypothesis.

<a id="app:halfmembership-detail"></a>

### Positive half-membership classification

The complementary branch has an equally exact seam formulation. Membership of $`1/2`$ in the Mersenne achievement set is equivalent to the occurrence, beyond every bound, of a successor terminal bit equal to zero, [the unbounded terminal-zero equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L126); equivalently, it is equivalent to a cofinal sequence of such terminal zeros, [the cofinal terminal-zero equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L203). It is also equivalent to a cofinal integer-seam sequence with skipped ranks tending to infinity, [the unbounded skipped-rank equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L213). These equivalences isolate the required cofinal skipped-rank condition; they do not establish that condition.

<a id="res:largestskip"></a>

### Largest skipped ranks

At a named largest skipped rank $`d`$, the lower seam word and its adjacent upper competitor have an exact late-range gap. In division-free form, the identity is
``` math
3L+\bigl(3\cdot2^{s+1}+2\cdot4^{s-d}+4\bigr)=3U
```
whenever $`2s<3d`$; this is formalised at [the exact late-gap identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderLargestSkipGap.lean#L259). The upper and middle successor branches create a terminal largest skipped rank, while the right branch preserves an existing one: [the terminal largest-skip branch](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderLargestSkipGap.lean#L328) and [right-branch persistence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderLargestSkipGap.lean#L339). The first-crossing branch hypothesis required to use this identity globally is not proved.

<a id="res:boundarypulse"></a>

### Boundary-pulse normalisation

Above a late largest skipped rank, every filled suffix rank has zero row pulse, so the word pulse is carried entirely by the lower prefix: [the lower-prefix pulse localisation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderBoundaryPulse.lean#L85). At the first crossing of the two-thirds boundary there are exactly two cases, $`3d=2s+1`$ and $`3d=2s+2`$, and the skipped rank has pulse respectively two or one: [the first-crossing pulse classification](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderBoundaryPulse.lean#L150). This supplies the incidence normalisation for a transition-carry estimate; it does not establish that estimate.

<a id="res:largestskipinduction"></a>

### Largest-skip induction

Assume that at the first crossing a late largest skipped rank either remains late at the next row or forces an upper-or-middle successor branch. This hypothesis propagates a late largest skipped rank from row $`14`$ onward, [largest-skip propagation step](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderLargestSkipInduction.lean#L90), and hence yields cofinal skipped ranks and membership of $`1/2`$ in the Mersenne achievement set, [largest-skip membership criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderLargestSkipInduction.lean#L167). The first-crossing hypothesis itself remains unproved.

<a id="res:fixedtailsocket"></a>

### The fixed-tail survival criterion

A skipped rank is final exactly when its post-decision remainder lies strictly above the complete remaining Mersenne tail: [the final-skip criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderFixedTailSocket.lean#L22). Consequently membership of $`1/2`$ is equivalent to the pointwise assertion that every actual skipped rank has remainder at most its full future tail, [the half-membership survival equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderFixedTailSocket.lean#L73). This is an exact local reformulation; the tail-survival inequality is not proved.

<a id="res:producercarry"></a>

### The carry identity at a non-right transition

For a finite support aligned with a non-right transition, the residual from $`1/2`$ is exactly the integer transition carry minus the complete future divisor-incidence tail, scaled by $`2^{-(2d+2)}`$: [transition-carry residual identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderProducerCarrySocket.lean#L27). Thus the carry exceeds that tail exactly when the support series lies below $`1/2`$, and a negative carry places it above $`1/2`$; [positive-carry criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderProducerCarrySocket.lean#L48) and [negative-carry criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderProducerCarrySocket.lean#L145). An upper carry at most $`-8`$ even gives a full Mersenne-gap margin, [full-gap carry criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderProducerCarrySocket.lean#L190). These are local criteria, not a proof that the required carries occur.

<a id="res:quarterband"></a>

### Quarter-band endpoint cells

For the adjacent seam recurrence, failure of the desired next-row upper bound on the middle branch is exactly one multiple-of-four pulse cell, [the middle-branch pulse-cell equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderQuarterBandEndpoints.lean#L153). On the terminal-reset branch, the same failure is exactly a constrained $`3\cdot2^{s-1}+k`$ pulse cell, [the reset-branch pulse-cell equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderQuarterBandEndpoints.lean#L175). These are arithmetic normal forms for the exceptional cells; no avoidance statement for the concrete seam orbit is proved.

<a id="res:resetdeficit"></a>

### Reset-deficit escape

At a late largest skipped rank, a right successor branch pins the integer greedy remainder between an explicit quarter threshold and a carry threshold: [the right-branch remainder window](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderResetDeficitEscape.lean#L200). Along such a branch the remainder satisfies an exact affine recurrence, [the right-branch affine recurrence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderResetDeficitEscape.lean#L218). Moreover, a doubled-scale deficit forces an upper-or-middle branch within the corresponding number of rows, [the deficit escape bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderResetDeficitEscape.lean#L261). The remaining input is the deterministic anti-concentration needed to exclude the pinned right-branch window globally; no such anti-concentration statement is proved here.

<a id="res:seamproducer"></a>

### Alignment of seam and transition carries

At a first-wrap seam, the transition carry of the left boundary support is four times the shifted seam hole, less the explicit paired incidence pulse at the next two rows: [seam–carry alignment](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderSeamProducerAlignment.lean#L24). This is an exact coordinate change between the seam and transition coordinates; it does not supply a sign or size estimate for that carry.

<a id="app:half-evidence"></a>

## Finite evidence, coordinate changes, and eliminated special cases

This subsection decides no open question. Its verified bases and stages are bounded evidence for the cofinal criteria in A.2–A.3; its coordinate changes translate one finite formulation into another; and its counterexamples and incompatibility theorems rule out shortcuts that would otherwise be mistaken for global arguments. Each item must therefore be read through the earlier criterion it supports or blocks.

<a id="res:selectedwindowbase"></a>

### A verified initial selected window

The selected half-carry construction has a checked depth-$`18`$ base: twelve Boolean words cover every terminal carry in the strip $`[1,12]`$, with all intermediate carries in the corresponding half strip. The reflected table is formalised at [the depth-$`18`$ table verification](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarrySelectedWindowBase.lean#L79); the resulting selected window is defined at [the depth-$`18`$ selected window](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarrySelectedWindowBase.lean#L129). All twelve words share the same restriction at depth $`13`$, giving the first next-row divisor-agreement certificate, [the depth-$`18`$ divisor-agreement certificate](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCarrySelectedWindowBase.lean#L172). This finite base does not provide selected windows at unbounded depths.

<a id="res:rewindseambridge"></a>

### Rewind-to-seam equivalence

For a selected window with a rewind seam, a two-value coefficient profile on the adjacent base ancestors induces the live next-row profile, [the next-row rewind profile](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RewindSeamOperationalBridge.lean#L140). Under the stated strip and buffer inequalities, that profile realises a protected one-hole seam at the next row, [the protected-seam realisation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RewindSeamOperationalBridge.lean#L217). The base-ancestor coefficient drop is an explicit input, not a theorem here, and so are the stated strip and buffer inequalities.

<a id="selected-suffix-cylinders"></a>

### Selected suffix cylinders

Put
``` math
H_N=2\lfloor\sqrt N\rfloor+4.
```
For a Boolean word $`a=(a_0,\ldots,a_N)`$, let
``` math
f_a(n)=\#\{d\leq N:d\mid n,\ a_d=1\},\qquad
 K_0(a)=1,\qquad K_{r+1}(a)=2K_r(a)-f_a(r+2).
```

<div id="def:selected-suffix-cylinder" class="definition">

**Definition 39** (selected window and suffix cylinder). A *selected window* of depth $`N`$ and radius $`R`$ is a family $`(a^{(k)})_{1\leq k\leq R}`$ of Boolean words with $`a^{(k)}_0=a^{(k)}_1=0`$ such that
``` math
1\leq K_{n-1}(a^{(k)})\leq H_n
 \quad(1\leq n\leq N),
 \qquad K_{N-1}(a^{(k)})=k.
```
For $`M\leq N`$, define the suffix numeral
``` math
\nu_{M,N}(a)=\sum_{j=M+1}^{N}a_j\,2^{N-j}.
```
The window has a *suffix cylinder at cutoff $`M`$ with endpoint $`E`$* if all $`a^{(k)}`$ have the same prefix through $`M`$ and
``` math
\nu_{M,N}(a^{(k)})+k=E
 \qquad(1\leq k\leq R).
```
A *profiled gap stage* permits one missing carry interval $`[g_-,g_+]\subseteq[1,H_N]`$: lower and upper suffix-cylinder families represent $`1,\ldots,g_--1`$ and $`g_++1,\ldots,H_N`$, with independent fixed prefixes through $`M`$. Its upper endpoint $`E_+`$ covers $`H_N`$ and satisfies $`E_+=g_++2^{N-M}`$; prefix adjacency is a separate transition hypothesis.

</div>

The results below have five different roles. The checked base feeds the ordinary one-row update. At a feedback row there is a dichotomy between a new full stage and a local gap. A separate recurrence advances such a gap when its coefficient inequalities hold. The quarter-band bound is only a necessary obstruction. Finally, the cofinal corollary is the sole step from arbitrarily deep full stages to half-membership.

<div id="res:selectsuffix" class="proposition">

**Proposition 40** (verified base and one-row cylinder update). *The depth-$`18`$ selected window has $`R=12`$ and a suffix cylinder at cutoff $`M=13`$ with endpoint $`E=17`$.*

*More generally, let a depth-$`N`$, radius-$`R`$ selected window $`(a^{(k)})_{1\leq k\leq R}`$ have a suffix cylinder at cutoff $`M\leq N`$ with endpoint $`E`$, where $`1\leq N`$ and $`R\leq E`$. Let $`1\leq R'\leq H_{N+1}`$. If
``` math
f_{a^{(k)}}(N+1)=C\qquad(1\leq k\leq R)
```
and
``` math
R'+C\leq2R,
```
then the radius-$`R'`$ successor remains a suffix cylinder, with endpoint
``` math
E'=2E-C.
```*

</div>

The base and endpoint update are the [depth-$`18`$ cylinder](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SelectedSuffixCylinder.lean#L88) and [endpoint recurrence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SelectedSuffixCylinder.lean#L136).

<div id="res:feedbackdichotomy" class="proposition">

**Proposition 41** (feedback-row dichotomy). *Let a full suffix-cylinder stage have depth $`N`$, cutoff $`M`$, with $`1\leq N`$, $`M+1\leq N`$, and
``` math
N+1=2(M+1).
```
At depth $`N+1`$, either a full stage exists at cutoff $`M+1`$, or the exceptional carries form a two-sheet profiled gap stage. If $`27\leq H_{N+1}`$, the residual alternative also realises a protected one-hole seam.*

</div>

Formalised by the [feedback dichotomy](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SuffixCylinderGlobalProducer.lean#L174) and [two-family gap alternative](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SuffixCylinderInStrip.lean#L665).

<div id="res:profiledgap" class="proposition">

**Proposition 42** (profiled-gap transition). *Suppose a profiled gap stage has lower and upper next coefficients $`C_-`$ and $`C_+`$, respectively. If
``` math
\begin{gathered}
 1\leq 2g_- -C_- -1,\qquad C_+\leq2g_+,\\
 2g_- -C_- -1\leq 2g_+ -C_+\leq H_{N+1},\\
 H_{N+1}+C_+\leq2H_N,
\end{gathered}
```
then the stage advances one row with exact child gap
``` math
[g'_-,g'_+]
   =[\,2g_- -C_- -1,\;2g_+ -C_+\,].
```
At a cutoff boundary $`N=2M+1`$, $`M\geq4`$, the lower and upper prefixes acquire the forced bits $`0`$ and $`1`$; their consecutiveness is preserved. Under the displayed child-gap conditions at the next row, this promoted stage therefore advances with coefficients determined by its retained prefixes.*

</div>

Formalised by the [two-coefficient gap recurrence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SuffixCylinderProfiledGap.lean#L124) and [promote-and-advance theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SuffixCylinderProfiledAutoStep.lean#L110).

<div id="res:cylinderswallow" class="proposition">

**Proposition 43** (quarter-band swallow obstruction). *If a two-row update swallows a protected strip of bound $`B`$, and the lower coefficient pulse is at most the upper pulse plus $`2`$, then
``` math
B\leq4(g_+-g_-+1)+2. \tag{A.1}
```
This is a necessary quarter-band condition, not a contradiction.*

</div>

Formalised as the [swallow bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SuffixCylinderProfiledSwallow.lean#L254).

<div id="res:cofinalcylinder" class="corollary">

**Corollary 44** (cofinal suffix-cylinder criterion). *If full suffix-cylinder stages exist at arbitrarily large depths, then there is an infinite set $`A\subseteq\mathbb{N}_{>0}`$ such that
``` math
\sum_{n\in A}\frac1{2^n-1}=\frac12.
```*

</div>

This is the [positive-support cofinal-cylinder criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L148).

<a id="status-and-prior-art-boundary."></a>

#### Status and prior-art boundary.

The two transition propositions do not supply their coefficient inequalities, and the finite base does not supply the cofinal family required by Corollary <a href="#res:cofinalcylinder" data-reference-type="ref" data-reference="res:cofinalcylinder">44</a>. The strict-tail achievement-set literature supplies the surrounding Cantor-set geometry \[kovactao\], not this finite carry recurrence; the comparison record makes no novelty claim for the recurrence itself.

<a id="res:prefeedback"></a>

### Verified finite suffix-cylinder stages

The finite record has three milestones.

1.  *Depth $`27`$.* Before the first half-divisor feedback row, a full selected window exists at every depth from $`18`$ through $`27`$, and the depth-$`27`$ endpoint covers the whole protected strip: [stages through depth $`27`$](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SelectedSuffixCylinderPreFeedback.lean#L118) and [depth-$`27`$ strip coverage](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SelectedSuffixCylinderPreFeedback.lean#L147).

2.  *Depth $`29`$.* The threshold-stage continuation still covers the strip and has a common suffix cylinder at every cutoff from $`14`$ through $`25`$, while cutoff $`26`$ is explicitly not common: [depth-$`29`$ strip coverage](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SuffixCylinderThreshold.lean#L700) and [cutoff-$`26`$ obstruction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SuffixCylinderThreshold.lean#L806).

3.  *Depth $`52`$.* An independent exact run reaches depth $`51`$ with endpoint $`51{,}327{,}745`$, beyond the next feedback head threshold, and the promoted successor at depth $`52`$ is checked: [depth-$`51`$ threshold margin](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SuffixCylinderStage51.lean#L536) and [depth-$`52`$ terminal-strip witness](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L118).

These are finite milestones, not an unbounded induction; they do not provide the arbitrarily large stages required by Corollary <a href="#res:cofinalcylinder" data-reference-type="ref" data-reference="res:cofinalcylinder">44</a>.

<a id="res:halfdivisordrop"></a>

### Half-divisor unit drop

At the doubled feedback row, changing only the terminal half-divisor bit from $`0`$ to $`1`$ increases the support coefficient by exactly one: [the terminal-bit unit-drop identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfDivisorUnitDrop.lean#L20). The same holds for any explicitly identified adjacent boundary pair, [the boundary-pair unit-drop identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfDivisorUnitDrop.lean#L35). The inverse-parent recurrence transfers such a pair to the next protected seam while retaining the exact unit-drop witness, [the rewind unit-drop transfer](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RewindHalfDivisorAdapter.lean#L86) and [the protected-seam transfer](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RewindHalfDivisorAdapter.lean#L147). This is the local coefficient input for the rewind-seam profile, not a global construction of such boundary pairs.

<a id="res:rewindboundarycounterexample"></a>

### A finite rewind-boundary obstruction

The scalar one-row rewind data alone still does not supply that missing boundary predicate. Lean gives a concrete depth-$`26`$ selected two-word window whose depth-$`27`$ explicit step has rewind history $`[1]`$, is a width-two seam pair, and satisfies the doubled-row identity, but has no depth-$`13`$ half-divisor boundary-pair witness: [the depth-$`27`$ boundary-pair counterexample](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RewindBoundaryPairCounterexample.lean#L169). Thus the protected-window buffer in the compactness criterion is a genuine hypothesis, not a consequence of the scalar seam facts alone.

<a id="res:producercarrycoordinates"></a>

### Explicit carry coordinates at the final non-right transition

For every adjacent cut at rank $`s\ge5`$, the transition carry of the terminal-augmented below support equals the concrete middle coordinate:
``` math
4\,\mathrm{remainder}-\mathrm{belowPulse}-4,
```
and identifies the terminal-augmented above support with the negative upper coordinate
``` math
-\bigl(4\,\mathrm{overshoot}+\mathrm{abovePulse}+4\bigr).
```
The generic row-word identity is [row-word transition identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderProducerLowerBound.lean#L105), with the below and above specialisations at [middle-coordinate identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderProducerLowerBound.lean#L150) and [upper-coordinate identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/HalfCylinderProducerLowerBound.lean#L183). These identities make the remaining quantitative task exact: they do not prove exponential lower bounds, sign persistence, or a universal escape mechanism.

<a id="res:campbellboundary"></a>

### Strategy boundary: Campbell shift synchronisation

A proposed route combines a finite Mersenne shift from a putative last greedy skip with Campbell’s quarter-exponent prime progression. The exact parameter requirements cannot be synchronised: if the combined progression modulus is $`d\ge2`$, the phase factor is at most $`d`$, the fatal-window prime cap is at most four times that phase, and Campbell’s applicability requires $`d^4`$ below the cap, then the inequalities are inconsistent. Formalised: [the period-freeze incompatibility](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CampbellShiftSynchronization.lean#L299) and [the parameter incompatibility](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CampbellShiftSynchronization.lean#L320).

The associated shifted-zero condition is not an independent hypothesis. It is exactly equivalent both to infinitely many actual greedy skips and to $`1/2\in\mathcal A`$: [the shifted-zero/skip equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CampbellShiftSynchronization.lean#L471) and [the shifted-zero/half-membership equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CampbellShiftSynchronization.lean#L488). This settles one synchronisation question and gives an equivalent reformulation; it does not decide the half-membership question stated above.

<a id="appendix-consequence."></a>

#### Appendix consequence.

This appendix supplies the local implications behind Theorems <a href="#res:halfmembership" data-reference-type="ref" data-reference="res:halfmembership">14</a> and <a href="#res:fatalright" data-reference-type="ref" data-reference="res:fatalright">17</a>, Proposition <a href="#res:finalskipexclusions" data-reference-type="ref" data-reference="res:finalskipexclusions">18</a>, and Corollary <a href="#res:taildominance" data-reference-type="ref" data-reference="res:taildominance">19</a>. It does not establish the corollary’s global hypothesis. A sufficient hypothesis is either a cofinal window, seam, or terminal approximation producing $`1/2\in\mathcal A`$, or both an exclusion of every actual middle transition with $`C_D=-2,-1`$ and a proof of $`\Theta_D<C_D`$ at every remaining non-$`(-3)`$ middle transition. The bounded checks and local no-go theorems provide neither route.

<a id="sec:carry"></a>

# Auxiliary rationality criteria from binary carry systems

This appendix supplies the general results assembled in Theorem <a href="#res:rigidity-main" data-reference-type="ref" data-reference="res:rigidity-main">7</a> and Corollaries <a href="#res:rigidity-unbounded-main" data-reference-type="ref" data-reference="res:rigidity-unbounded-main">8</a>–<a href="#res:rigidity-dyadic-mass-main" data-reference-type="ref" data-reference="res:rigidity-dyadic-mass-main">11</a>, and the detailed greedy geometry cited after Theorem <a href="#res:greedy" data-reference-type="ref" data-reference="res:greedy">6</a>. Its new working objects are a tempered integer tail orbit, its Boolean Möbius coordinate, the wrap–excess decomposition modulo the odd denominator, and exact rational death certificates for the achievement set. Appendices <a href="#app:carry-normal-form" data-reference-type="ref" data-reference="app:carry-normal-form">10.1</a>–<a href="#app:carry-mass" data-reference-type="ref" data-reference="app:carry-mass">10.4</a> describe necessary or equivalent forms of a hypothetical rational support; Appendix <a href="#app:carry-geometry" data-reference-type="ref" data-reference="app:carry-geometry">10.5</a> describes the ambient achievement set and its one-sided finite nonmembership test. None of these objects by itself excludes a rational value.

The reading order is: a generic tail-orbit rationality normal form in Appendix <a href="#app:carry-normal-form" data-reference-type="ref" data-reference="app:carry-normal-form">10.1</a>; its Boolean–Möbius specialisation in Appendix <a href="#app:carry-boolean" data-reference-type="ref" data-reference="app:carry-boolean">10.2</a>; divisor-coverage constraints in Appendix <a href="#app:carry-sublog" data-reference-type="ref" data-reference="app:carry-sublog">10.3</a>; denominator-wrap, reciprocal-mass, and unbounded-state constraints in Appendix <a href="#app:carry-mass" data-reference-type="ref" data-reference="app:carry-mass">10.4</a>; and the exact greedy geometry with one-sided finite death certificates in Appendix <a href="#app:carry-geometry" data-reference-type="ref" data-reference="app:carry-geometry">10.5</a>.

The dependency chain is
``` math
\begin{array}{rcl}
 \text{a rational support value}
 &\Longleftrightarrow& \text{a tempered integral tail orbit}
 \quad\text{(B.1)},\\
 \text{a specified support fraction \(p/q\)}
 &\Longleftrightarrow& \text{a Boolean--M\"obius carry certificate}
 \quad\text{(B.2)},\\
 \text{a nonempty rational support}
 &\Longrightarrow& \text{sublogarithmic zero gaps}\quad\text{(B.3)},\\
 \text{a nonempty support, odd part }v>1
 &\Longrightarrow& \text{wrap and reciprocal-mass bounds}
 \quad\text{(B.4)},\\
 \text{an infinite rational support}
 &\Longrightarrow& \text{unbounded carry states}
 \quad\text{(B.4)},\\
 \text{an infinite dyadic-denominator support}
 &\Longrightarrow& \text{the reciprocal-mass alternative}
 \quad\text{(B.4).}
\end{array}
```
The last four lines list independent necessary conditions, at the weakest hypotheses under which they are proved, not converses and not contradictions. Appendix <a href="#app:carry-geometry" data-reference-type="ref" data-reference="app:carry-geometry">10.5</a> is orthogonal to this rationality chain: finite greedy death proves nonmembership in the achievement set, whereas survival through any finite depth proves nothing.

The prior-art boundary is theorem-family-specific. The integral carry recurrence has a direct antecedent in Wang–Grau Ribas \[wanggrauribas\]; the strict-tail geometry is recorded by Kovač–Tao \[kovactao\]; Möbius inversion, repetend algebra, and divisor averaging are classical (see, for example, Apostol \[apostol\]). We make no claim of mathematical priority for the converse/rigidity, certificate-normal-form, or coupled reciprocal-mass/collision statements collected here.

<a id="app:carry-normal-form"></a>

## Exact normal form: tail-orbit rigidity

This subsection supplies the generic equivalence used in Appendix <a href="#app:carry-boolean" data-reference-type="ref" data-reference="app:carry-boolean">10.2</a>. It converts rationality into an integer recurrence with a boundary condition; it does not itself exclude such an orbit or impose the Boolean support constraint.

For a coefficient sequence $`\gamma:\mathbb{N}\to\mathbb{N}`$ with $`\gamma(n)\le n`$, write
``` math
X_\gamma=\sum_{n\ge1}\frac{\gamma(n)}{2^n},
\qquad
T_\gamma(N)=\sum_{j\ge1}\frac{\gamma(N+j)}{2^j},
```
the series and its scaled tail after $`N`$ binary digits. Call an integer sequence $`u`$ a *tempered orbit* for $`\gamma`$ with multiplier $`v\ge1`$ if
``` math
u(N+1)=2\,u(N)-v\,\gamma(N+1)\ \text{ for all } N,
\qquad\text{and}\qquad
u(N)/2^N\to0 .
```
The recurrence is exact binary long division against the coefficient stream; the boundary condition forbids the homogeneous solution. Wang and Grau Ribas use the integral carry recurrence forced by rationality for the weighted binary special case $`\gamma(n)=n d_n`$ \[wanggrauribas\]. The theorem below extends that forward mechanism to arbitrary nonnegative $`\gamma(n)\le n`$; its explicit converse and subexponential-orbit rigidity are the local additions, with no priority claim attached. Wang–Grau Ribas’s positive-density theorem and its Erdős \#260 corollary are not used or formalised here.

<div id="res:rigidity" class="theorem">

**Theorem 45** (tail-orbit rigidity). *Let $`\gamma(n)\le n`$ for all $`n`$. Every tempered orbit is the scaled tail, $`u(N)=v\,T_\gamma(N)`$ for all $`N`$; and $`X_\gamma`$ is rational if and only if a tempered orbit exists for some multiplier $`v\ge1`$.*

</div>

Formalised: [the scaled-tail orbit identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GenericTailOrbitRigidity.lean#L338) (rigidity) and [the rationality–orbit equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GenericTailOrbitRigidity.lean#L425) (the criterion), restated in Mathlib’s irrationality vocabulary at [the non-irrationality–orbit equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GenericTailOrbitRigidity.lean#L434). The engine is one observation: a real orbit with $`d(N+1)=2\,d(N)`$ and $`d(N)=o(2^N)`$ vanishes identically ([zero-tail rigidity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GenericTailOrbitRigidity.lean#L314)).

The tempered boundary is essential: the homogeneous parasite $`N\mapsto2^N`$ can be added to any orbit without disturbing the recurrence, so positivity of an orbit certifies nothing by itself, and positivity is nowhere advertised as an equivalent criterion. The linear-growth hypothesis covers both constants introduced in Section <a href="#sec:intro" data-reference-type="ref" data-reference="sec:intro">1</a>: $`\varphi(n)\le n`$ for the \#249 coefficients, and $`f_A(n)\le\tau(n)\le n`$ for the \#257 support coefficients $`f_A(n)=\#\{a\in A:a\mid n\}`$. The results below instantiate the criterion on supports. Its separate totient anti-compression consequence belongs to the \#249 rank route in Appendix <a href="#app:totient-rank" data-reference-type="ref" data-reference="app:totient-rank">11.4</a>.

<a id="app:carry-boolean"></a>

## Exact \#257 coordinates: Boolean–Möbius carry certificates

This subsection has one preliminary boundary result and then one exact equivalence chain. The boundary result rules out extracting the desired Boolean support directly from the signs in $`L(\mu)=1/2`$; it is not a premise of the carry equivalence that follows.

<div id="res:mobiussignnogo" class="proposition">

**Proposition 46** (Möbius-sign support no-go). *Let
``` math
A_-=\{d\ge2:\mu(d)=-1\},
 \qquad A_+=\{d\ge2:\mu(d)=1\}.
```
Then
``` math
\sum_{d\in A_-}\frac1{2^d-1}
 =\frac12+\sum_{d\in A_+}\frac1{2^d-1}
 \ge\frac12+\frac1{63}>\frac12.
```
In particular, the signed identity $`L(\mu)=1/2`$ cannot be converted into a Boolean support of value $`1/2`$ merely by selecting the negative Möbius indices.*

</div>

Formalised: [the negative-Möbius decomposition](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/MobiusSignSupportNoGo.lean#L111) and [the strict lower bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/MobiusSignSupportNoGo.lean#L150). The term $`d=6`$ supplies the displayed $`1/63`$. This rules out one sign-truncation route only; it does not exclude another infinite Boolean support with value $`1/2`$.

<a id="the-exact-coordinate-chain."></a>

#### The exact coordinate chain.

At base $`2`$ the support series of Section <a href="#sec:eb" data-reference-type="ref" data-reference="sec:eb">4</a> is itself a binary coefficient series, $`\sum_{n\in A}1/(2^n-1)=X_{f_A}`$ ([the support-series/binary-series identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L376)). Boolean Möbius inversion first identifies the support from its divisor coefficients; tail-orbit rigidity then identifies rationality with a tempered integer orbit. Theorem <a href="#res:carrycert" data-reference-type="ref" data-reference="res:carrycert">48</a> is exactly the composition of those two equivalences. The divisor transform and Möbius inversion are classical Lambert-series tools \[apostol; merca2017; mercaschmidt\]; the contribution here is their Lean-checked composition with the tempered-orbit criterion.

<div id="res:boolmob" class="proposition">

**Proposition 47** (Boolean Möbius inversion, both directions). *On positive integers, $`f_A=\mathbf 1_A*\zeta`$ and $`\mu*f_A=\mathbf 1_A`$, where $`\mathbf 1_A`$ is the indicator of $`A`$. Conversely, every integer-valued arithmetic function $`f`$ whose Möbius transform is Boolean, $`(\mu*f)(n)\in\{0,1\}`$ for all $`n\ge1`$, satisfies $`f=f_B`$ for the support $`B=\{n\ge1:(\mu*f)(n)=1\}`$ selected by that transform.*

</div>

Formalised: [the positive-support zeta identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L76), [the Möbius inversion identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L94), and, with no search or finiteness hypothesis, the converse [the Boolean reconstruction theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L180).

On the carry side, Theorem <a href="#res:rigidity" data-reference-type="ref" data-reference="res:rigidity">45</a> applies at $`\gamma=f_A`$: the support series is rational exactly when a tempered carry orbit for $`f_A`$ exists ([the rationality–carry equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L383)); a displayed fraction $`p/q`$ corresponds to an orbit $`U`$ with multiplier $`q`$ and initial value $`U(0)=p`$ ([the support-fraction carry equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L466)); and exact division recovers the coefficient from the orbit, $`\bigl(2U(N)-U(N+1)\bigr)/q=f_A(N+1)`$ ([carry-quotient recovery](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L680)). The elementary divisor-pair bound $`\tau(n)\le2\lfloor\sqrt n\rfloor`$ confines the tails to a square-root strip, $`T_{f_A}(N)\le2\sqrt N+4`$. For a nonempty support the orbit states are positive and satisfy $`U(N)\le q\,(2\sqrt N+4)`$ ([the carry upper bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L705)); and the strip is strong enough to re-derive the tempered boundary, so the analytic side condition can be traded for one inequality. The two coordinate changes compose.

<div id="res:carrycert" class="theorem">

**Theorem 48** (certificate-level equivalence). *Fix an integer $`p`$ and an integer $`q\ge1`$. There is a nonempty support $`A`$ of positive integers with $`\sum_{n\in A}1/(2^n-1)=p/q`$ if and only if there is an integer sequence $`U`$ with $`U(0)=p`$ such that: every $`U(N)`$ is positive; $`U(N)\le q\,(2\sqrt N+4)`$; $`q`$ divides $`2U(N)-U(N+1)`$ for every $`N`$; and the Möbius transform of the quotient sequence $`\bigl(2U(N)-U(N+1)\bigr)/q`$ is Boolean. The support is not guessed: it is reconstructed from the certificate by Proposition <a href="#res:boolmob" data-reference-type="ref" data-reference="res:boolmob">47</a>.*

</div>

Formalised as [the normalised support-fraction certificate equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L948).

<div class="example">

**Example 49** (the support $`\{2,3\}`$). The support $`\{2,3\}`$ has value $`\tfrac13+\tfrac17=\tfrac{10}{21}`$ ([the two-point series value](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L1054)), its orbit is the pure period-six cycle $`10,20,19,17,13,26`$ with multiplier $`21`$ ([the tempered two-point orbit](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L1103)), and the Möbius transform of the carry quotient recovers exactly $`\{2,3\}`$ ([support recovery](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/BooleanMobiusCarry.lean#L1140)).

</div>

These are coordinates, not by themselves a strategy: nothing here excludes infinite Boolean carry paths, and no finite search is promoted to a completeness argument.

<a id="app:carry-sublog"></a>

## Necessary condition I: sublogarithmic divisor coverage

This theorem is a one-way consequence of a rational support value and is used in Corollary <a href="#res:rigidity-sublog-main" data-reference-type="ref" data-reference="res:rigidity-sublog-main">9</a>. It limits zero gaps in the divisor-coefficient stream; it neither reconstructs a support nor contradicts the existence of an infinite rational support.

The coefficient $`f_A(n)`$ counts the elements of $`A`$ dividing $`n`$. Say that a zero window of length $`h`$ starts after $`c+N`$ when $`f_A(c+N+j+1)=0`$ for every $`0\le j<h`$. Thus no integer in that interval is divisible by an element of the support.

<div id="res:sublog" class="theorem">

**Theorem 50** (sublogarithmic zero windows). *Let $`A`$ contain a positive integer and suppose
``` math
\sum_{a\in A}\frac1{2^a-1}=\frac{p}{2^c v},
  \qquad p\in\mathbb{Z},\quad c\in\mathbb{N},\quad v\ge1.
```
For every $`\varepsilon>0`$ there is a constant $`B\ge0`$, depending only on $`\varepsilon,c,`$ and $`v`$, such that every zero window after $`c+N`$ satisfies
``` math
h\le \varepsilon\log_2(N+1)+B,
  \qquad \log_2 x:=\frac{\log x}{\log 2}.
```
The bound is uniform in $`A,p,N,`$ and $`h`$.*

</div>

Formalised: [sublogarithmic zero-window bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SublogDivisorCoverage.lean#L392).

The proof first establishes, for each integer $`k\ge2`$, the explicit divisor estimate
``` math
\tau(n)^k\le \bigl(k^{2^k}\bigr)^k n.
```
It transports the resulting $`n^{1/k}`$ bound through the binary tail and then uses the exact carry recurrence across a zero window. Raising the resulting inequality to the $`k`$th power absorbs the occurrence of $`h`$ on the right and leaves a coefficient $`1/(k-1)`$ in front of the binary logarithm. Choosing $`k`$ after $`\varepsilon`$ gives the theorem. This controls gaps in divisor coverage; it does not assert a subpower bound for the carry state itself.

For one fixed support the conclusion is elementary, since every zero window is shorter than the least support element. The content is uniformity: $`B`$ does not depend on $`A`$, and taking $`N=0`$ shows that a rational value with denominator data $`(c,v)`$ bounds the least element of its support in terms of $`(\varepsilon,c,v)`$ alone. Against the half-value fibre the constraint is inert: the greedy candidate support there contains $`2`$, so its divisor stream has no zero window of length above one and satisfies the bound with room to spare.

<a id="app:carry-mass"></a>

## Necessary conditions II: wraps, mass, and unbounded states

The dependency order is
``` math
\text{doubling residues}\ \longrightarrow\ \text{wrap count}\
\longrightarrow\ \text{reciprocal-mass bound}\
\longrightarrow\ \text{collision strengthening}.
```
The final unbounded-state theorem uses the same common-multiple collision mechanism without a summability hypothesis. The one-wrap classification identifies the extremal residue cycles; it is a side branch, not a premise of the general mass bound.

Suppose now the support series equals $`p/(2^c v)`$ with $`v`$ odd and $`A`$ containing a positive element. Let $`U`$ be the unshifted tempered orbit of Appendix <a href="#app:carry-boolean" data-reference-type="ref" data-reference="app:carry-boolean">10.2</a> with multiplier $`q=2^c v`$. The odd-denominator coordinate used here is
``` math
u(N)=\frac{U(c+N)}{2^c}=v\,T_{f_A}(c+N);
```
this is the state denoted $`u_N`$ in Theorem <a href="#res:rigidity-main" data-reference-type="ref" data-reference="res:rigidity-main">7</a>. Rationality makes $`u(N)`$ a positive integer satisfying $`u(N+1)+v\,f_A(c+N+1)=2\,u(N)`$. Moreover, $`u(N)`$ reduces modulo $`v`$ to the doubling residue $`\bar p_N=p\,2^N\bmod v`$ ([shifted natural-state existence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L668)). Doubling a least residue either stays under $`v`$ or wraps past it exactly once, so each step emits a wrap digit $`k_N=\lfloor2\bar p_N/v\rfloor\in\{0,1\}`$, and over any cycle length $`h`$ with $`2^h\equiv1\pmod v`$ the repetend identity holds:
``` math
\sum_{N<h}\bar p_N \;=\; v\cdot w,
\qquad
w=\sum_{N<h}k_N,
```
with $`w\ge1`$ when $`p`$ is coprime to $`v>1`$. The formal development records the displayed equality as the [wrap-count identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L171) and its non-vanishing as the [positive-wrap theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L181).

<div id="res:onewrap" class="proposition">

**Proposition 51** (one-wrap classification). *Let $`v>1`$ be odd, $`p`$ coprime to $`v`$, and $`h\ge1`$ with $`2^h\equiv1\pmod v`$. If the cycle of $`p`$ wraps exactly once, then $`v=2^h-1`$ and the starting residue is a power of two: $`\bar p_0=2^a`$ for some $`a<h`$.*

</div>

The one-wrap cycles are thus exactly the Mersenne repetends $`2^a/(2^h-1)`$. Formalised: [one-wrap classification](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L415), from the generic closed-cycle form [one-wrap cycle classification](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L353), and instantiated at the true order $`h=\operatorname{ord}_v(2)`$ ([odd-order one-wrap classification](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L478)). The classification is algebraic; a finite check of $`446`$ coprime starting residues across twelve modulus/order rows is retained as kernel-checked validation, not as the proof ([446-start finite validation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L2454)).

The analytic bridge is Cesàro averaging. Write $`\rho(A)=\sum_{a\in A}1/a`$ for the reciprocal mass. When the reciprocal family is summable, the mean of $`f_A(1),\dots,f_A(N)`$ converges to $`\rho(A)`$ — the density of the multiples of $`a`$, summed over the support — and the mean of the scaled tails has the same limit ([divisor-mean limit](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L945), [coefficient-tail mean limit](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L1036)). The divergent case is carried as an explicit disjunction, not through a default value assigned to a divergent formal sum. Each tail state splits exactly as $`u(N)=v\,e_N+\bar p_N`$ with integral excess $`e_N=\lfloor u(N)/v\rfloor\ge0`$.

<div id="res:orderwrap" class="proposition">

**Proposition 52** (order-wrap lower bound, with exact excess mean). *Let $`A\subseteq\mathbb{N}_{>0}`$ be nonempty and suppose
``` math
X_A=\frac{p}{2^cv},
 \qquad p\in\mathbb{Z},\quad c\in\mathbb{N},\quad v>1\ \text{odd}.
```
Let $`h=\operatorname{ord}_v(2)`$, let $`w`$ be the number of wraps in the least-residue cycle $`p2^N\bmod v`$ for $`0\leq N<h`$, and set
``` math
u(N)=vT_{f_A}(c+N),\qquad e_N=\left\lfloor\frac{u(N)}v\right\rfloor.
```
Then $`\sum_{a\in A}1/a`$ diverges or $`\rho(A)\ge w/h`$; if moreover $`p`$ is coprime to $`v`$, then $`w\ge1`$, so $`\rho(A)\ge1/\operatorname{ord}_v(2)`$. In the summable case the bound is the periodic part of an exact identity: the Cesàro mean of $`e_N`$ converges, and
``` math
\rho(A)\;=\;\frac{w}{h}\;+\;\lim_{N\to\infty}\frac1N\sum_{n<N}e_n .
```*

</div>

The divergent-or-bounded conclusion is formalised by the [wrap-ratio mass alternative](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L1501), its coprime specialisation by the [odd-order mass alternative](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L1517), and the automatic excess limit in the fraction-facing coordinates above by the [shifted excess-mean identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L1577). A rational value thus ties the odd part of its denominator to the sparsity of its support: a summable support with small $`\rho(A)`$ can only display denominators whose odd part has small multiplicative order of $`2`$.

<div id="res:collision" class="corollary">

**Corollary 53** (collision strengthening at common multiples). *In the summable case, let $`F\subseteq A`$ be finite and let $`L\ge1`$ be a common multiple of $`F`$. Then
``` math
\rho(A)\;\ge\;\frac{w}{h}\;+\;\frac{\lceil(|F|-1)/2\rceil}{L}.
```
In particular, an infinite support whose value is a dyadic rational $`p/2^c`$ has $`\sum_{a\in A}1/a`$ divergent or $`\rho(A)>1`$.*

</div>

The mechanism is a collision: at every positive multiple of $`L`$ at least $`|F|`$ support divisors land on the same index, so $`f_A\ge|F|`$ there, while the exact carry equation $`f_A(n)+e_n=k_{n-1}+2e_{n-1}`$ with $`k_{n-1}\le1`$ lets one step absorb at most one unit — so the preceding excess must spike to at least $`\lceil(|F|-1)/2\rceil`$, and the spikes recur with density $`1/L`$. The three steps are formalised by the [shifted common-multiple bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L1963), [shifted wrap–excess recurrence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L1868), and [dyadic reciprocal-mass alternative](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L2200).

<div id="res:unbounded" class="theorem">

**Theorem 54** (carry states are unbounded over infinite supports). *Let $`A`$ be infinite with value $`p/(2^c v)`$, $`v\ge1`$. Then the positive integer carry state $`u(N)=v\,T_{f_A}(c+N)`$ is unbounded: for every $`B`$ there is an $`N`$ with $`u(N)>B`$.*

</div>

The proof picks $`2B+1`$ positive support elements; at a common multiple $`L`$ of all of them, the local inequality $`1+v\,|F|\le2\,u(L-c-1)`$ pushes the state past $`B`$. The conclusion is the [fraction-facing unbounded-state theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L2377); its local engine is the [support-cardinality state bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/RationalSupportCarrySkeleton.lean#L2228). So a rational value over an infinite support cannot run on a bounded carry alphabet. That rules out finite-state readings of the carry system; it does not decide the problem. Nothing in the constraints above prevents an infinite support from satisfying every one of these constraints. The repetend identities and divisor averages used here are classical. We make no claim of mathematical novelty for the coupled reciprocal-mass bounds, collision strengthening, or global unboundedness statement.

<a id="app:carry-geometry"></a>

## Independent geometry and one-sided nonmembership certificates

Finally, consider the set of all values a base-$`2`$ support series can take. For $`n\ge1`$ put $`w_n=1/(2^n-1)`$, let $`T(n)`$ be the mass strictly after exponent $`n`$, and let
``` math
\mathcal A\;=\;\Bigl\{\,\sum_{n\in A}w_n \;:\; A\subseteq\mathbb{N},\ 0\notin A\Bigr\},
```
the *Mersenne achievement set*, the exponent $`0`$ being normalised away as analytically invisible. Coding by supports of positive exponents is literally the formal support series ([support-value identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L554)). In this language the base-$`2`$ \#257 statement reads: the rational members of $`\mathcal A`$ are exactly the finite subset sums. Nothing below decides that. Kovač and Tao verify, for every fixed integer $`t\ge2`$, that
``` math
\sum_{\ell>n}\frac1{t^\ell-1}<\frac1{t^n-1},
```
and deduce distinct Lambert subsums and a Cantor set \[kovactao\]. At $`t=2`$ this is the relevant Lambert-series instance of Kakeya’s classical strict-tail criterion for subsum sets \[kakeya1914\]. The local contribution is the checked greedy criterion, quantitative enclosure, and finite nonmembership certificates over that known geometry; it does not attribute those refinements to the cited sources or settle \#257.

<div id="res:greedy-details" class="theorem">

**Theorem 55** (superincreasing geometry and greedy membership). *For every $`n\ge1`$ the weight dominates the whole tail after it, $`T(n)<w_n`$, with the two-scale gap $`w_n-T(n)=\tfrac23\,4^{-n}+O(8^{-n})`$ and explicit valid $`O`$-constant $`3`$. Consequently a real $`x`$ belongs to $`\mathcal A`$ exactly when $`x\ge0`$ and every greedy residual of $`x`$ is at most the remaining tail; and normalised support coding is injective, so each member of $`\mathcal A`$ has a unique support, which the greedy recursion recovers bit by bit.*

</div>

Formalised: [strict-tail inequality](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L180), [gap big-O estimate](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L473) (explicit bound [explicit gap bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L448)), [greedy survival criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1445), and [normalised support-value injectivity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1527), transferred to the kernel series at [normalised support-series injectivity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1536). The nonnegativity guard in the membership criterion is necessary: without it a negative target would survive every level while lying outside $`\mathcal A`$.

The binary coding also permits the global geometry to be checked directly.

<div id="res:greedytopology" class="proposition">

**Proposition 56** (fat-Cantor geometry). *The achievement set $`\mathcal A`$ is compact, perfect, totally disconnected, and nowhere dense. Its Lebesgue measure is exactly one.*

</div>

Formalised: [measure-one theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L996), [perfectness](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1620), [total disconnectedness](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1636), and [nowhere density](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1645). Kovač–Tao supply the strict-tail Cantor-set context cited above. The formalisation records these exact properties without making a novelty or priority claim for them.

<div id="res:death" class="proposition">

**Proposition 57** (exact rational runs and finite nonmembership certificates). *The greedy recursion executed in exact rational arithmetic agrees step by step with the real recursion under casting. For a rational target $`x`$, write $`r_n(x)`$ for its exact rational residual after level $`n`$ and, for a lookahead $`\ell\ge0`$, put
``` math
\widehat T_{n,\ell}
  =\sum_{k=0}^{\ell-1}w_{n+k+1}+2w_{n+\ell+1}\in\mathbb{Q}.
```
The sum is empty when $`\ell=0`$, and always $`T(n)<\widehat T_{n,\ell}`$. Hence the finite inequality $`\widehat T_{n,\ell}\le r_n(x)`$ soundly proves $`x\notin\mathcal A`$; its level-one instance shows $`3/4\notin\mathcal A`$. A rational number already known to lie in $`\mathcal A`$ has computable support bits.*

</div>

Formalised: [rational–real greedy agreement](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1130), [rational tail-enclosure bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1692), [finite death-certificate soundness](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1726), [three-quarters nonmembership](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1748), and [rational-member support-bit equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GreedyAchievementSet.lean#L1832). The certificates are one-sided: survival through any finite depth proves nothing about membership, and no decidability of membership in $`\mathcal A`$ is asserted. Neither the global geometry nor the finite death certificates exclude rational values for either open series.

<a id="appendix-consequence.-1"></a>

#### Appendix consequence.

The transfer to the main text is Theorem <a href="#res:rigidity-main" data-reference-type="ref" data-reference="res:rigidity-main">7</a> followed by the four independent Corollaries <a href="#res:rigidity-unbounded-main" data-reference-type="ref" data-reference="res:rigidity-unbounded-main">8</a>–<a href="#res:rigidity-dyadic-mass-main" data-reference-type="ref" data-reference="res:rigidity-dyadic-mass-main">11</a>. Rationality yields the exact carry recurrence; any nonempty rational support must satisfy the sublogarithmic divisor-coverage bound, and the odd-part wrap and mass bounds when its denominator has odd part $`v>1`$; an infinite one must in addition satisfy the unbounded-state theorem and, at a dyadic denominator, the reciprocal-mass alternative. Appendix <a href="#app:carry-geometry" data-reference-type="ref" data-reference="app:carry-geometry">10.5</a> also supplies the finite death certificates used in Theorem <a href="#res:greedy" data-reference-type="ref" data-reference="res:greedy">6</a>. What is not proved is that the support attached to either target violates one of these necessary conditions. That contradiction, not another rational normal form, is the missing premise.

<a id="app:totient-technical"></a>

# Technical reductions for the totient-certificate branch

This appendix expands the supporting mathematics behind Proposition <a href="#res:complete" data-reference-type="ref" data-reference="res:complete">23</a>, Theorems <a href="#res:pointwisecomplete" data-reference-type="ref" data-reference="res:pointwisecomplete">24</a> and <a href="#res:red21" data-reference-type="ref" data-reference="res:red21">25</a>, and Theorem <a href="#res:diag" data-reference-type="ref" data-reference="res:diag">26</a>. It contains exact cone-flatness and target-interval reformulations, finite residue projections, denominator and bit-lifting formulae, bounded certificate families, and rigorous obstructions to several candidate strategies. Each statement retains its own hypotheses and status. None proves the unbounded certificate supply <a href="#eq:unbounded-certificate-supply" data-reference-type="eqref" data-reference="eq:unbounded-certificate-supply">[eq:unbounded-certificate-supply]</a>.

The exact chain is
``` math
\begin{array}{rcl}
 R_{N+h}-R_N\notin\mathbb{Z}
 &\Longleftrightarrow&
 \exists L\geq1,\ \mathsf{Sep}(h,N,L),\\
 S\notin\mathbb{Q}
 &\Longleftrightarrow&
 \forall h\geq1\ \forall N_0\ \exists N\geq N_0\ \exists L\geq1,\
 \mathsf{Sep}(h,N,L).
\end{array}
```
Appendix <a href="#app:totient-normal" data-reference-type="ref" data-reference="app:totient-normal">11.1</a> gives equivalent coordinates for this fixed-to-cofinal reduction. Appendix <a href="#app:totient-finite" data-reference-type="ref" data-reference="app:totient-finite">11.2</a> distinguishes one-scale mechanisms from the conditional cofinal implications that use them. Appendices <a href="#app:totient-boundaries" data-reference-type="ref" data-reference="app:totient-boundaries">11.3</a>–<a href="#app:totient-rank" data-reference-type="ref" data-reference="app:totient-rank">11.4</a> expose possible inputs to an unbounded supply theorem and rule out several shortcuts. None of the latter three sections proves the missing cofinal supply in the second line.

<a id="app:totient-normal"></a>

## Exact cofinal normal forms and cone consequences

This subsection contains two different kinds of statement. Cone flatness is a necessary consequence of rationality that a finite joint refuter may contradict at chosen vertices. The diagonal-pincer identity and its cofinal full-target-avoidance corollary are the exact fixed-scale and global normal forms of the open supply. Only the latter corollary is equivalent to the irrationality of $`S`$.

<a id="cone-flatness-and-completeness."></a>

#### Cone flatness and completeness.

On the cone $`\{kM_t:k\ge1\}`$, rationality forces a single fractional constant across the whole cone.

<div id="res:flat" class="proposition">

**Proposition 58** (cone flatness). *If $`S`$ is rational, then for every sufficiently large $`t`$ there is $`\theta_t\in[0,1)`$ such that the fractional part of the tail $`R_{kM_t}`$ equals $`\theta_t`$ for every $`k\ge1`$.*

</div>

Formalised: [cone flatness under rationality](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeFlatness.lean#L90).

Proposition <a href="#res:complete" data-reference-type="ref" data-reference="res:complete">23</a> states fixed-parameter certificate completeness, and Theorem <a href="#res:pointwisecomplete" data-reference-type="ref" data-reference="res:pointwisecomplete">24</a> gives its global pointwise form. Their additional role here is cone-level: a joint finite refuter can interrogate several cone vertices at once and is sharper than any pairwise test. It refutes the single-fractional-part model that rationality predicts on a finite sample ([finite cone-nonflatness refuter](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeNonflat.lean#L126)). This finite cone predicate is sound in the direction just stated: a certificate produces a non-integral pair and hence contradicts the sampled flatness model. No converse is proved saying that every non-flat finite sample, or every irrational value of $`S`$, must be detected by this joint predicate. It is therefore a refuter, not a complete decision procedure.

<a id="an-exact-target-interval."></a>

#### An exact target interval.

The diagonal calculation also admits a more local normal form. Put $`H_t=M_t`$ and
``` math
D_t=R_{2H_t}-R_{H_t}.
```
Separate an exact rational Möbius shadow $`Q_t=a_t/d_t`$ in lowest terms and define the remaining *foreign defect* by $`F_t=D_t-Q_t`$; the shadow collects the explicitly summed Möbius channels, and the defect is everything that explicit part does not see. The full target is the residue class of $`-a_t`$ modulo $`d_t`$:
``` math
\mathsf{Hit}(t)
 \quad\Longleftrightarrow\quad
 \exists k\in\mathbb{Z},\qquad d_tF_t=-a_t+d_tk.
```
Since $`D_t=a_t/d_t+F_t`$, this is exactly the condition $`D_t\in\mathbb{Z}`$; no complementary term is discarded or assigned a conjectural sign.

<div id="res:pincer" class="proposition">

**Proposition 59** (diagonal pincer decomposition). *For every $`t`$, diagonal integrality is equivalent to the foreign diagonal defect meeting the full target.*

</div>

This is the [full-target equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalPincerDecomposition.lean#L215).

<div id="res:fulltargetavoidance" class="corollary">

**Corollary 60** (exact full-target avoidance characterisation). *The following are equivalent:
``` math
\begin{aligned}
 &S\notin\mathbb{Q};\\
 &\forall\,t_0\in\mathbb{N}\ \exists\,t\geq t_0,\qquad
   \neg\mathsf{Hit}(t).
\end{aligned}
```*

</div>

The reverse implication is the [unbounded target-avoidance criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalPincerDecomposition.lean#L290). For the forward implication, Theorem <a href="#res:diag" data-reference-type="ref" data-reference="res:diag">26</a> supplies cofinally many non-integral diagonal differences, and Proposition <a href="#res:pincer" data-reference-type="ref" data-reference="res:pincer">59</a> converts each one into a missed full target. Thus the proposition is the fixed-scale equivalence and the corollary is its exact global form. The cofinal avoidance statement remains open.

<a id="app:totient-finite"></a>

## Fixed-scale mechanisms and conditional cofinal implications

This subsection is organised by quantifier. Its enclosures, predicates, checked certificate families, and projection equivalences are finite or one-scale mechanisms. Whenever a corollary concludes irrationality, its additional premise is an unproved cofinal supply of the relevant finite mechanism. No result here constructs such a supply or fills the missing quantifier in Appendix <a href="#app:totient-normal" data-reference-type="ref" data-reference="app:totient-normal">11.1</a>.

<a id="a-one-way-analytic-enclosure."></a>

#### A one-way analytic enclosure.

Truncate the Möbius-square identity of Proposition <a href="#res:lens" data-reference-type="ref" data-reference="res:lens">85</a> after $`D`$ terms. The resulting rational quantity gives a Lambert-projected centre $`C_{H,D}`$ for the scaled diagonal difference. The error is exactly a signed squared-Mersenne tail:
``` math
\textsf{scaledDiagonal}(H)-C_{H,D}
   =c_H\sum_{d>D}\frac{\mu(d)}{(2^d-1)^2},
```
where $`c_H`$ is the explicit diagonal coefficient in the formal source. The absolute value of the sum is bounded geometrically by $`4/[3(2^{D+1}-1)^2]`$. Thus a rational separation of the centre from every integer by more than the scaled bound proves target avoidance; the argument does not estimate the sign of the tail.

<div id="res:squareenclosure" class="proposition">

**Proposition 61** (squared-Mersenne enclosure). *The scaled diagonal tail difference differs from its Lambert-projected centre by the squared-Mersenne tail. Separation of the centre from the full target by more than the proved tail bound forces target avoidance.*

</div>

Formalised: [squared-Mersenne tail identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L116) and [Lambert-projected separation criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L237). The enclosure is one-way: separation at a chosen truncation forces target avoidance, but target avoidance is not asserted to force that separation.

<a id="a-reduced-denominator-finite-predicate."></a>

#### A reduced-denominator finite predicate.

Separately, there is a stricter finite condition for an odd reduced denominator $`u`$. Its predicate $`\mathsf{UnitGap}(u,N,K)`$ asks that every candidate integer in the associated dyadic tail interval be non-coprime to $`u`$. At a prime power $`u=p^e`$, the condition is equivalent to the exact alternative that the interval has no candidate, or that it has one candidate and $`p`$ divides that candidate. Thus such an interval has at most one candidate.

<div id="res:unitgap" class="proposition">

**Proposition 62** (prime-power unit-gap ceiling). *For every prime power $`p^e`$ with $`e>0`$, a $`\mathsf{UnitGap}(p^e,N,K)`$ has candidate count at most one. The row $`(u,N,K)=(3,3,5)`$ satisfies this predicate, although its corresponding ordinary empty-gap inequality fails.*

</div>

Formalised: [prime-power unit-gap characterisation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/PrimitiveWeightCertificate.lean#L54), [prime-power one-candidate bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/PrimitiveWeightCertificate.lean#L111), [three-window unit-gap certificate](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/PrimitiveWeightCertificate.lean#L151), and [three-window ordinary-gap failure](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/PrimitiveWeightCertificate.lean#L157). This is a finite certificate-level strengthening. We do not establish that rationality of $`S`$ supplies these predicates at unbounded parameters.

<a id="the-certificates-are-non-empty."></a>

#### The certificates are non-empty.

The initial segment of the required supply is machine-checked, so the reduction is not vacuous. By completeness, each of these is a kernel-checked proof of a specific non-integral tail difference, not a numerical experiment.

<div id="app:deposits-detail" class="example">

**Example 63** (verified finite instances, expanded record). The following are checked by the Lean kernel:

- $`\mathsf{Sep}(h,12,16)`$ for every period $`h\in[1,8]`$;

- finite certificates for every period $`h\in[1,16]`$ at a fixed window;

- diagonal certificates $`\mathsf{Sep}(M_t,M_t,L)`$ at $`t=1`$ and the 27 strict lcm-jump scales through $`64`$, namely
  ``` math
  t\in\{1,2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,
  47,49,53,59,61,64\};
  ```

- a tabulated joint cone-vertex certificate.

</div>

The four validation classes are formalised, in order, by the [small-window certificate family](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TotientTailPeriodKiller.lean#L404), [periods through sixteen](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CarrySurvivorExtinction.lean#L574), [28 imported diagonal certificates through scale 64](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalPincerCertificatesT64.lean#L1967), and [cone-cell certificate table](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/LcmConeNonflat.lean#L506). These instances show that each layer of the reduction is non-vacuous and, by completeness, exact. They are not evidence that the unbounded supply exists.

The first row of this table is worked in full following Example <a href="#res:deposits" data-reference-type="ref" data-reference="res:deposits">27</a>. The soundness theorem ([certificate soundness](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TotientTailPeriodKiller.lean#L262)) converts each successful row into one exact non-integral tail difference; no row asserts that such differences occur at unbounded scales.

<a id="finite-foreign-residue-projection."></a>

#### Finite foreign-residue projection.

There is a second finite presentation of the same obstruction. For a cutoff $`D`$, split the finite Möbius residue diagonal into the channels $`d\leq D`$ which divide $`H`$ and the remaining channels. The divisor part is exactly the truncated Möbius shadow, while every retained nondivisor channel is explicit. Above the stable cutoff $`2H`$, a finite window of omitted channels is bounded by
``` math
c_H\left(\frac{2}{2^D}+\frac{4}{3\,4^D}\right),
```
where $`c_H`$ is the diagonal coefficient. Thus, if the actual foreign defect agrees with this projection within the displayed bound, and the projected quantity is farther than that bound from every integer, then the full target is missed.

<div id="res:foreignresidue" class="proposition">

**Proposition 64** (finite foreign-residue projection). *Let $`F_H^{(D)}`$ be the retained nondivisor projection at cutoff $`D`$, let $`F_H`$ be the actual foreign defect, and let $`Q_H`$ be the scaled explicit divisor shadow. The finite residue diagonal is exactly the sum of $`F_H^{(D)}`$ and its divisor-channel complement. For $`2H\leq D`$, put
``` math
B_{H,D}=c_H\left(\frac{2}{2^D}+\frac{4}{3\,4^D}\right).
```
If
``` math
|F_H-F_H^{(D)}|\leq B_{H,D}
 \quad\text{and}\quad
 |Q_H+F_H^{(D)}-z|>B_{H,D}\quad\text{for every }z\in\mathbb{Z},
```
then the full target at height $`H`$ is not attained.*

</div>

Formalised: [foreign–divisor channel split](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/ActualForeignResidueProjection.lean#L307), [omitted-channel bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/ActualForeignResidueProjection.lean#L275), and [projected-separation criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/ActualForeignResidueProjection.lean#L348). The passage from finite windows to the analytic foreign complement, including the corresponding kernel identity, is not supplied here. Nor is an unbounded family of separated projections; these are parts of the open certificate-supply problem.

Second, the rational Möbius shadow has an exact reduced denominator. If $`r_t`$ is the square-free kernel of $`H_t`$, $`s_t=H_t/r_t`$, and $`J(r_t)=\prod_{q}(q^2-1)`$ is the odd Jordan scalar, the product running over the odd prime divisors $`q`$ of $`r_t`$, then
``` math
d_t=
 \frac{2^{r_t}-1}
 {\gcd\!\bigl(2^{r_t}-1,\,s_t\lvert J(r_t)\rvert\bigr)}.
```
For $`t\geq5`$, the product of the Mersenne factors $`2^p-1`$ over primes $`t/2<p\leq t`$ divides $`d_t`$; in particular $`d_t\geq2^{\lfloor t/2\rfloor}`$. This is a denominator theorem for $`Q_t`$ only. Cancellation by $`F_t`$ is exactly what the full-target condition retains.

<div id="res:shadowden" class="proposition">

**Proposition 65** (Mersenne-shadow denominator). *Let $`r_t`$ be the square-free kernel of $`H_t`$, let $`s_t=H_t/r_t`$, and let $`J(r_t)`$ be the odd Jordan scalar. The reduced denominator $`d_t`$ of the scaled Möbius shadow is
``` math
d_t=
 \frac{2^{r_t}-1}
 {\gcd\!\bigl(2^{r_t}-1,\,s_t\lvert J(r_t)\rvert\bigr)}.
```
If $`t\geq5`$, then
``` math
\prod_{\substack{p\ \mathrm{prime}\\ t/2<p\leq t}}(2^p-1)
 \ \mid\ d_t,
 \qquad d_t\geq2^{\lfloor t/2\rfloor}.
```*

</div>

Formalised: [upper-half Mersenne divisor bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/MersenneShadowDenominatorGrowth.lean#L99) and [exact shadow denominator](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/MersenneShadowDenominatorGrowth.lean#L147).

Finally, the remaining diagonal error can be represented by a finite integer projection and then by binary suffix data. At depth $`L`$, let
``` math
P_L(M)=\sum_{j=0}^{L-1}\varphi(M+1+j)\,2^{L-1-j}
```
be the length-$`L`$ window numerator underlying Definition <a href="#def:totient-certificate" data-reference-type="ref" data-reference="def:totient-certificate">22</a>, and define
``` math
W_{t,L}=P_L(2H_t)-P_L(H_t),\qquad
 \eta_{t,L}=W_{t,L}\bmod 2^L,
```
with the residue chosen in $`[0,2^L)`$. The finite residue certificate is the asymmetric safe interval
``` math
H_t+L+2<\eta_{t,L}<2^L-(2H_t+L+2).
```
The two unequal margins are the tail bounds at the two cone vertices $`H_t`$ and $`2H_t`$; replacing them by a symmetric slogan would lose part of the checked statement.

<div id="res:freshloss" class="corollary">

**Corollary 66** (finite residue projection). *For every $`t,L\in\mathbb{N}`$, the diagonal projection certificate is equivalent to
``` math
H_t+L+2<\eta_{t,L}<2^L-(2H_t+L+2),
```
and either condition forces full-target avoidance at height $`t`$. Consequently,
``` math
\forall t_0\in\mathbb{N}\;\exists t\geq t_0\;\exists L\in\mathbb{N},\qquad
 H_t+L+2<\eta_{t,L}<2^L-(2H_t+L+2)
```
implies that $`S`$ is irrational.*

</div>

Formalised: [residue–projection equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalFreshLossBridge.lean#L61) and [unbounded projection criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalFreshLossBridge.lean#L191). The finite equivalence is only between the residue inequality and the projection certificate. Neither condition is asserted to be necessary for full-target avoidance or for irrationality. The stronger adjacent-suffix supplies formalised in the same module imply the displayed cofinal supply; they are not additional conclusions of one finite certificate. Finite instances of this implication are proved, but no unbounded projection or suffix supply is established.

<a id="res:t64closure"></a>

#### Primality certificates at changing-lcm scales through $`t=64`$.

A finite family of Lucas certificates proves the primality facts required by the diagonal-pincer certificates at every changing-lcm scale through $`t=64`$; for example, [representative Lucas primality certificate](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalPincerPrimeCertificates/ClosureT64.lean#L51759). This is a finite theorem family, not an unbounded certificate supply or an irrationality proof.

<a id="res:t64endpoint"></a>

#### The diagonal certificate at $`t=64`$.

Using those primality facts, Lean checks the individual diagonal-pincer certificate at $`t=64`$, [scale-64 diagonal certificate](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalPincerCertificateT64Endpoint.lean#L1928). This is one finite certificate, not an unbounded supply.

<a id="app:totient-boundaries"></a>

## Candidate cofinal inputs and no-go boundaries

The three-rank condition below is a candidate cofinal sufficient condition, while its affine form exposes a precise obstruction to obtaining that condition from uniform correction bounds alone. The remaining results are independent filters, not consecutive proof steps: the fresh-prime decomposition and one-bit lift expose exact correction terms that an unbounded argument would have to control, and the parity, prime-adjunction, scalar-localisation, and square-CRT results rule out four natural shortcuts. No no-go result uses the preceding filter as a hypothesis.

<a id="res:flexibleoddwindow"></a>

#### A three-rank odd window.

At an analytically admissible odd power-of-two rank, centrality at any one of the canonical odd rank or its next two base-four successors yields the required adjacent-suffix gap condition, [three-rank suffix-gap implication](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalFlexibleOddWindowSupply.lean#L93). Thus a cofinal three-rank band supply implies irrationality, [cofinal three-rank criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalFlexibleOddWindowSupply.lean#L136); that supply is not proved.

<a id="res:flexibleoddaffine"></a>

#### Affine form of the three-rank condition.

With the stated short-correction bounds, the three central-band predicates are equivalent to one three-scale affine escape condition, [three-scale affine equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L236). A zero-start affine orbit shows that a uniform correction envelope alone does not force escape at any finite number of ranks, [zero-orbit obstruction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/DiagonalFlexibleOddWindowAffine.lean#L225).

<a id="fresh-prime-deficit-decomposition."></a>

#### Fresh-prime deficit decomposition.

The literal foreign channel also has an endpoint form suited to curvature tests. Retain only the prime support already present at $`H`$ in the two endpoints $`H+s`$ and $`2H+s`$, and write the resulting discrepancy from the actual totient as an endpoint deficit. Each such deficit is nonnegative. The actual diagonal increment then equals the old-prime increment plus the lower deficit minus the upper deficit. The second and five-point curvature operators preserve this exact split; the latter has coefficient row $`[-8,4,2,1,1]`$. Consequently, the old curvature margin loses at most the stated adverse weighted deficit.

<div id="res:freshprimedeficit" class="proposition">

**Proposition 67** (fresh-prime deficit decomposition). *The endpoint fresh deficits are nonnegative, give an exact decomposition of the foreign channel, and bound the loss from the old-prime curvature margins.*

</div>

Formalised: [endpoint-deficit nonnegativity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/FreshPrimeDeficitDecomposition.lean#L91), [foreign-increment decomposition](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/FreshPrimeDeficitDecomposition.lean#L184), and [adverse-deficit curvature bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/FreshPrimeDeficitDecomposition.lean#L269). This supplies the exact correction term for the finite evaluations. It supplies neither a cofinal deficit bound nor an irrationality criterion.

<a id="one-bit-lifting."></a>

#### One-bit lifting.

The power-of-two signed-margin condition admits a separate exact arithmetic reduction. If a signed difference is already divisible by $`2^k`$, lifting its congruence to $`2^{k+1}`$ is equivalent to evenness of the quotient after division by $`2^k`$. Failure of the lift gives the unique translated residue class. In particular, a displayed difference $`P-N=16c`$ agrees modulo $`32`$ exactly when $`c`$ is even; otherwise the residue is the offset class by $`16`$.

<div id="res:powertwobitlift" class="proposition">

**Proposition 68** (one-bit signed-margin lift). *The fifth-bit question after fourth-bit agreement is exactly one cofactor parity test, with the complementary offset class characterising failure.*

</div>

Formalised: [one-bit divisibility lift](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/PowerTwoBitLift.lean#L34), [mod-32 cofactor criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/PowerTwoBitLift.lean#L111), and [offset-16 complement](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/PowerTwoBitLift.lean#L129). The centred-state formulation identifies the signed-margin interval condition with failure of this next lift, subject to its stated correction and margin budget: [centred-lift equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/PowerTwoCenteredBitLift.lean#L121) and [centred mod-32 equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/PowerTwoCenteredBitLift.lean#L159). This is a finite arithmetic equivalence. It does not supply the required cofactors at unbounded scales and gives no irrationality conclusion.

<a id="parity-is-not-a-margin-certificate."></a>

#### Parity is not a margin certificate.

The preceding lift does not settle the reduced signed-margin interval condition. For a positive even modulus $`m`$ and integral radius parameter $`a`$ with $`16<a<8m-16`$, each parity class contains both a residue inside the interval and one outside it. The same statement applies to a positive power-of-two modulus. Thus even a fifth-bit computation, by itself, cannot decide the required margin condition.

<div id="res:paritysocket" class="proposition">

**Proposition 69** (parity does not decide the reduced margin condition). *Let $`m,a\in\mathbb{Z}`$, with $`m>0`$ even and
``` math
16<a<8m-16,
```
and put
``` math
\mathcal M_{m,a}
 =\{y\in\mathbb{Z}:\exists k\in\mathbb{Z},\ 16|y-km|<a\}.
```
Each parity class contains both a member and a nonmember of $`\mathcal M_{m,a}`$. In particular, the conclusion holds for $`m=2^j`$ whenever $`j\geq1`$.*

</div>

Formalised: [parity obstruction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/Totient827ParitySocketCeiling.lean#L73) and [power-of-two parity obstruction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/Totient827ParitySocketCeiling.lean#L110). The result is structural and proves no signed-margin certificate at any particular scale; it excludes parity as a sufficient standalone criterion.

<a id="prime-adjunction-no-go-theorem."></a>

#### Prime-adjunction no-go theorem.

One tempting way to seek an unbounded obstruction is to compare the full target at $`H`$, $`pH`$, $`qH`$, and $`pqH`$. The following affine transport law rules out this route before any projection is introduced.

<div id="res:primeadjunction" class="proposition">

**Proposition 70** (prime-adjunction transport collapse). *For every positive $`H`$ and $`k`$, the actual diagonal satisfies
``` math
D_{kH}=Q_k(H)D_H+Z_k(H),
 \qquad Q_k(H)\in\mathbb{N},\quad Z_k(H)\in\mathbb{Z}.
```
Hence integrality at $`H`$ propagates to every multiple, and the four target hits at the prime-adjunction diamond are equivalent to the single hit at its root. The corresponding transport of the complete foreign defect has zero diamond curvature: the two transport compositions around the diamond agree exactly.*

</div>

Formalised: [the prime-adjunction diamond collapse](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L196) and [the foreign-correction flatness](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L247). Thus explicit-shadow fibres alone cannot create a transport obstruction. A future positive route would need a separately defined projection together with a theorem controlling what that projection discards. This is a proved obstruction to one strategy, not progress on the unbounded-supply proposition.

<div id="res:adelic" class="proposition">

**Proposition 71** (scalar-localisation obstruction). *Let $`x\in\mathbb{Q}`$ and $`c\in\mathbb{Z}`$. If $`H\mid\operatorname{den}(x)`$ and the reduced denominator of $`cx`$ divides $`H`$, then
``` math
\frac{\operatorname{den}(x)}{H}\mid |c|.
```*

</div>

Formalised: [complementary-denominator divisibility](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/AdelicHeightObstruction.lean#L23) and [scalar-localisation identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/AdelicHeightObstruction.lean#L56). Thus a scalar localisation can move a complementary denominator factor into its coefficient, but cannot erase it. This rules out a scalar-denominator shortcut of that form. It neither proves full-target avoidance nor supplies any certificates, so it gives no irrationality criterion for $`S`$.

<div id="res:squarecrt" class="proposition">

**Proposition 72** (square-CRT correction suppression). *Let $`E`$ be a finite family indexed by distinct primes $`p_i`$, with prescribed anchors $`A_i`$ and residues $`a_i`$. There is a bounded common base $`n`$ such that, for each $`i\in E`$ and each shift $`h`$ with $`p_i\nmid a_i+h`$, one has
``` math
n=A_i+p_i(a_i+p_i t)\quad\text{and}\quad
 \varphi(n+p_i h-A_i)=(p_i-1)\varphi(a_i+p_i t+h)
```
for a suitable $`t\in\mathbb{N}`$. In particular, if every $`p_i`$ exceeds a fixed horizon $`J`$, the choice $`a_i=0`$ works simultaneously for all $`1\le h\le J`$.*

</div>

Formalised: [finite clean totient family](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SquareCRTCube.lean#L198) and [clean horizon family](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SquareCRTCube.lean#L228). The finite mechanism does not force a cube coefficient to be nonzero: there is a checked clean two-step cube with both displayed coefficients zero ([vanishing clean block](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SquareCRTCube.lean#L285)) and a separate checked clean cube with second coefficient $`-4`$ ([nonzero clean block](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SquareCRTCube.lean#L303)). Thus the result gives neither an unbounded certificate supply nor an irrationality criterion for $`S`$.

<a id="app:totient-rank"></a>

## Unconditional dyadic rank and carry anti-compression

The determinant construction in this route is unconditional. At every level, a CRT construction prescribes one target prime channel and fresh off-target prime divisors; Dirichlet’s theorem supplies the required primes in the resulting progressions. After the exact powers of two are divided from the columns, the evaluation matrix is the identity modulo two. This proves a nonzero separated minor at every level rather than merely postulating one.

<div id="res:dyadictotient" class="theorem">

**Theorem 73** (infinite dyadic totient-kernel rank). *For every $`e\geq0`$, the canonical level-$`e`$ dyadic totient-kernel family is linearly independent over $`\mathbb{Q}`$ and its span has dimension $`2^e+1`$. Consequently, the span of all sections
``` math
n\longmapsto \varphi(2^j n+r),\qquad j\geq0,\quad 0\leq r<2^j,
```
is not finite-dimensional over $`\mathbb{Q}`$.*

</div>

Formalised by the all-level minor construction [CRT–Dirichlet separated minors](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TotientMahlerDefect.lean#L847), the independence theorem [canonical kernel independence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TotientMahlerDefect.lean#L900), the exact rank formula [exact canonical rank](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TotientMahlerDefect.lean#L954), and [infinite full-kernel dimension](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TotientMahlerDefect.lean#L1014). The theorem concerns the coefficient kernel. It does not imply that $`S`$ is irrational.

<a id="prior-art-boundary-for-the-kernel-theorem."></a>

#### Prior-art boundary for the kernel theorem.

The qualitative conclusion is not new. Finite-dimensionality of the span of all sections is $`2`$-regularity of the sequence in the sense of Allouche and Shallit \[alloucheshallit\], and Coons proved in 2010 that $`\varphi`$ is not $`k`$-regular for any $`k\ge2`$, by counting poles of $`\zeta(s-1)/\zeta(s)`$ against the meromorphic continuation available to the Dirichlet series of a regular sequence \[coons2010\]. In particular the infinite-dimensionality of the full kernel span follows from Coons’s theorem. What Theorem <a href="#res:dyadictotient" data-reference-type="ref" data-reference="res:dyadictotient">73</a> adds is quantitative and constructive: the exact canonical rank $`2^e+1`$ at every level, with an explicit separated minor, proved by elementary CRT–Dirichlet arithmetic that the formal source checks without analytic continuation. Proposition <a href="#res:carryrank" data-reference-type="ref" data-reference="res:carryrank">74</a> uses exactly this level-by-level form.

<div id="res:carryrank" class="proposition">

**Proposition 74** (finite-level carry anti-compression). *If the totient coefficient series were rational, there would be a positive-multiplier tempered integral carry orbit whose canonical carry-section span has dimension at least $`2^e-1`$ for every $`e`$.*

</div>

Formalised: [the carry-kernel rank lower bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TotientCarryKernelRigidity.lean#L211) and [the unconditional unbounded-rank consequence of rationality](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TotientCarryKernelRigidity.lean#L284). No theorem bounds the dyadic section rank of every rationality-supplied tempered carry. The proposition therefore identifies an infinite rationality-side barrier, not an irrationality criterion for $`S`$.

<div class="remark">

*Remark 4* (rank alone cannot decide rationality). No converse dimension bound is available at this generality: the same coefficient class contains rational series whose tempered orbits have infinite-dimensional section span. Choose Boolean values $`a_N\in\{0,1\}`$ with $`a_0=a_1=1`$ whose dyadic sections satisfy no nontrivial rational linear relation (a routine diagonal choice on sparse index blocks); set $`u_N=N+a_N`$ and $`\gamma(N+1)=2u_N-u_{N+1}`$. Then $`0\le\gamma(n)\le n`$, the orbit $`u`$ is tempered, and Theorem <a href="#res:rigidity" data-reference-type="ref" data-reference="res:rigidity">45</a> evaluates $`\sum_{n\ge1}\gamma(n)2^{-n}=u_0=1\in\mathbb{Q}`$; yet the sections of $`u`$ span an infinite-dimensional space, because the sections of $`N\mapsto N`$ span only two dimensions. This elementary observation is not formalised in the source. It fixes the shape of the missing ingredient: a route through Proposition <a href="#res:carryrank" data-reference-type="ref" data-reference="res:carryrank">74</a> must couple carry-section rank to the arithmetic size of a totient carry, since dimension alone is compatible with rationality.

</div>

<div id="res:signedmoment" class="proposition">

**Proposition 75** (rectangular determinant expansion). *For matrices $`M:\iota\times\kappa\to R`$ and $`N:\kappa\times\iota\to R`$ over a commutative ring, the determinant of $`MN`$ is the sum over all maps $`p:\iota\to\kappa`$ of the determinant of the corresponding selected-column matrix times the diagonal product $`\prod_i N_{p(i),i}`$.*

</div>

This is the [rectangular determinant expansion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SignedQMomentObstruction.lean#L28).

<div id="res:dominantdyadic" class="proposition">

**Proposition 76** (dominant dyadic term). *If one selected integer numerator is odd and its dyadic exponent is strictly larger than every other selected exponent, then the common numerator after dyadic denominator clearing is odd and hence nonzero.*

</div>

Formalised by [dominant dyadic parity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SignedQMomentObstruction.lean#L77), and [dominant dyadic nonvanishing](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SignedQMomentObstruction.lean#L95). These are finite algebraic inputs to a signed-moment route. They do not show that any actual totient Hankel determinant is nonzero, and they give no irrationality criterion for $`S`$.

The formal proof also exposes the construction-independent [separated-minor rank criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TotientMahlerDefect.lean#L101). The two generic algebraic propositions above remain useful as possible inputs to other determinant routes, but the totient-kernel minor itself is supplied at every level by Theorem <a href="#res:dyadictotient" data-reference-type="ref" data-reference="res:dyadictotient">73</a>.

<div id="res:evenresidue" class="proposition">

**Proposition 77** (even-residue reduction). *Every even residue channel in the canonical dyadic totient-kernel family is exactly a scalar multiple of its odd-core channel.*

</div>

Formalised as the [even-residue reduction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TotientMahlerDefect.lean#L159). This removes duplicate channels before the separated minor is constructed.

<div id="res:compressedadjoint" class="proposition">

**Proposition 78** (compressed-adjoint contradiction). *A compressed-adjoint certificate whose nonzero multiple is strictly smaller in absolute value than its positive modulus is inconsistent.*

</div>

Formalised as the [compressed-adjoint contradiction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/TotientMahlerDefect.lean#L1051). This is a conditional finite contradiction, not a source of certificates at every level.

<div id="res:residualgauge" class="proposition">

**Proposition 79** (residual-gauge obstruction for monomial minors). *Let a monomial matrix have a common nonzero residual weight in each column. The residual weights act by a right diagonal gauge, and therefore preserve determinant nonvanishing. If one exponent is $`1`$, the inverse-phase locked gauge makes that row identically $`1`$ while preserving a nonzero determinant whenever the coefficient-side determinant is nonzero. If the residual is allowed to depend on both row and column, it reconstructs a consecutive-power matrix whose zeroth row is identically $`1`$.*

</div>

Formalised: [residual-gauge determinant equivalence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/ResidualGaugeObstruction.lean#L55), [locked-reconstruction nonvanishing](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/ResidualGaugeObstruction.lean#L94), and [reconstructed zero row](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/ResidualGaugeObstruction.lean#L145). Thus a residual-blind rank, determinant, or conditioning criterion alone cannot exclude the target. The proposition does not exclude a criterion that also uses an arithmetic coupling identity, and it gives no irrationality criterion for $`S`$.

<a id="appendix-consequence.-2"></a>

#### Appendix consequence.

Nothing in this appendix strengthens the fixed-parameter completeness of Proposition <a href="#res:complete" data-reference-type="ref" data-reference="res:complete">23</a> into an unbounded supply. Its remaining condition is therefore the still-open quantifier in Theorem <a href="#res:red21" data-reference-type="ref" data-reference="res:red21">25</a>:
``` math
\forall h\geq1\;\forall N_0\;\exists N\geq N_0\;\exists L\geq1,\qquad
 \mathsf{Sep}(h,N,L).
```
The one-scale mechanisms and conditional implications in Appendix <a href="#app:totient-finite" data-reference-type="ref" data-reference="app:totient-finite">11.2</a>, the candidate inputs and no-go boundaries in Appendix <a href="#app:totient-boundaries" data-reference-type="ref" data-reference="app:totient-boundaries">11.3</a>, and the conditional rank routes in Appendix <a href="#app:totient-rank" data-reference-type="ref" data-reference="app:totient-rank">11.4</a> delimit possible approaches to this statement. None provides the required cofinal certificates.

<a id="app:lambert-complements"></a>

# Lambert, probability, and finite-algebraic complements

This appendix supplies the extensions cited from the Mersenne–Lambert ladder in Section <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a> and from the coprime-pair representation after Proposition <a href="#res:coprime" data-reference-type="ref" data-reference="res:coprime">21</a>. Its new results are the periodic-weight classifications, finite denominator obstructions, the Möbius-square and squared Lambert identities, and the Stern–Brocot cylinder and continuant laws. These enlarge the two coordinate pictures; they are not additional steps in either open proof.

The three families are parallel, not cumulative. Appendix <a href="#app:lambert-weighted" data-reference-type="ref" data-reference="app:lambert-weighted">[app:lambert-weighted]</a> proves or classifies weighted Lambert series with coefficient inputs different from the open totient input. Appendix <a href="#app:lambert-algebraic" data-reference-type="ref" data-reference="app:lambert-algebraic">12.2</a> gives exact identities and finite algebraic boundaries for the squared and Möbius coordinates. Appendix <a href="#app:lambert-probability" data-reference-type="ref" data-reference="app:lambert-probability">12.3</a> develops unconditional geometry internal to the coprime-pair probability coordinate. No conclusion about a comparison input transfers irrationality to $`S`$, and none of the three families supplies the cofinal $`\mathsf{Sep}`$ supply theorem.

<a id="sec:additional-lambert"></a>

## Weighted Lambert comparison families

<span id="app:lambert-weighted" label="app:lambert-weighted"></span>

This subsection changes the coefficient input. Its eventually-periodic theorems settle or classify those comparison series, while the period-four example blocks one residue-blind shortcut. None has the totient weight defining $`S`$, so no irrationality status transfers to Erdős #249.

<a id="sec:periodicweights"></a>

#### Periodic weights.

For $`L_b(\gamma)=\sum_{a\ge1}\gamma(a)/(b^a-1)`$, the checked cases are:

<div id="res:periodicnonnegative" class="theorem">

**Theorem 80** (eventually-periodic nonnegative weights). *For every $`b\ge2`$, an eventually-periodic nonnegative rational weight that is positive at a positive index in its periodic region gives an irrational series.*

</div>

Formalised: [eventually-periodic nonnegative criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L12483). This is contained in a broader theorem of Luca–Tachiya \[lucatachiya\].

<div id="res:periodicsigned" class="theorem">

**Theorem 81** (periodic signed-weight dichotomy). *For a periodic integer weight, the series is irrational or terminating in base $`b`$.*

</div>

Formalised: [periodic signed-weight dichotomy](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L13847).

<div id="res:periodfourobstruction" class="proposition">

**Proposition 82** (residue-blind obstruction). *For the period-four weight $`1,0,-1,0`$, the divisor coefficient vanishes on $`n\equiv3\pmod4`$.*

</div>

Formalised: [period-four coefficient obstruction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L13898).

<a id="app:lambert-algebraic"></a>

## Finite algebraic boundaries and squared-Lambert coordinates

This subsection keeps the relevant coordinates but separates three roles: finite denominator-clearing obstructions, the exact Möbius-square identity for $`S`$, and comparison rows in the squared-Lambert calculus. The identity changes coordinates; the finite propositions delimit algebraic methods; and the status of one squared-Lambert row does not pass to another.

<a id="sec:primitiveindex"></a>

#### Finite algebraic boundaries.

Put $`a_n=(\varphi*\mu)(n)/n`$. If an integer $`D`$ clears these coordinates through $`N`$, the exact obstruction is:

<div id="res:primitiveindex" class="proposition">

**Proposition 83** (primitive-coordinate finite-jet obstruction). *$`D`$ is divisible by an explicit two-tier primorial $`T_N`$; hence no fixed $`D`$ clears every $`a_n`$.*

</div>

Formalised: [two-tier primorial obstruction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/PrimitiveDeterminantLift.lean#L148).

For $`d\ge1`$, define the pointed periodic atom
``` math
\omega_d(N)=\frac{2^{\,N\bmod d}}{2^d-1}.
```
It satisfies the exact carry law
``` math
2\omega_d(N)-\omega_d(N+1)=\mathbf1_{d\mid N+1}.
```

<div id="res:mersennetailatoms" class="proposition">

**Proposition 84** (finite Mersenne-atom determinant boundary). *Fix $`m\ge1`$, conductors $`d_j\ge1`$, indices $`n_{ij}\ge0`$, and integer column weights $`w_j`$, and set
``` math
W_{ij}=w_j\omega_{d_j}(n_{ij}),
 \qquad U_{ij}=2^{\,n_{ij}\bmod d_j}.
```
Then
``` math
\left(\prod_{j=1}^m(2^{d_j}-1)\right)\det W
 =\left(\prod_{j=1}^m w_j\right)\det U\in\mathbb{Z}.
```
If the integer on the right is nonzero, then the absolute value of the cleared determinant on the left is at least $`1`$.*

</div>

Formalised: [Mersenne-atom carry law](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/MersenneTailAtoms.lean#L28), [determinant-clearing identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/MersenneTailAtoms.lean#L158), and [cleared-determinant lower bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/MersenneTailAtoms.lean#L181). Thus finite Mersenne-atom determinants recover exactly their explicit column denominators; the clearing creates no additional height surplus. These are scoped finite-denominator obstructions, not irrationality criteria for $`S`$.

<div id="res:lens" class="proposition">

**Proposition 85** (the Möbius-square lens).
*``` math
S \;=\; \tfrac12 \;+\; \sum_{d\ge1}\frac{\mu(d)}{(2^d-1)^2}.
```*

</div>

Formalised: [Möbius-square identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/CertificateKernel.lean#L18126). Writing $`T=\sum_{d\ge1}\mu(d)/(2^d-1)^2`$, irrationality of $`S`$ is equivalent to irrationality of $`T`$, since $`S=\tfrac12+T`$. The factor $`1/(2^d-1)^2`$ is the probability that $`d`$ divides two independent fair-coin waiting times (Section <a href="#sec:geom" data-reference-type="ref" data-reference="sec:geom">5.2</a>). The signed constant, the coprime-pair mass, and the tail differences of Section <a href="#sec:reduction" data-reference-type="ref" data-reference="sec:reduction">5.3</a> are three readings of the same quantity.

<a id="sec:squared"></a>

#### Squared Lambert calculus.

For $`L_2(f)=\sum_{d\ge1}f(d)/(2^d-1)^2`$, the denominator is the probability that $`d`$ divides two independent geometric waiting times. The formal transfer theorem, [squared Lambert transfer](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GcdMomentCalculus.lean#L105), therefore gives a divisor calculus for their gcd.

<div id="res:gcdmoment" class="proposition">

**Proposition 86** (squared Lambert ladder). *At $`r=1/2`$, the three rows $`f=\mu,\mathbf 1,\varphi`$ yield respectively
``` math
L_2(\mu)=S-\tfrac12,\qquad
 L_2(\mathbf 1)=\sum_{n\ge1}\frac{\sigma(n)-\tau(n)}{2^n},\qquad
 L_2(\varphi)=\sum_{n\ge1}\frac{P(n)-n}{2^n},
```
where $`P`$ is Pillai’s gcd-sum function.*

</div>

Formalised: [constant-weight squared-Lambert identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GcdMomentCalculus.lean#L216) and [totient gcd-moment identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GcdMomentCalculus.lean#L235). Postelmans–Van Assche imply irrationality of the middle row: their linear independence of $`1,\zeta_q(1),\zeta_q(2)`$ over $`\mathbb{Q}`$, proved whenever $`1/q`$ is an integer at least $`2`$, applies at $`q=1/2`$, and the middle row is $`\zeta_q(2)-\zeta_q(1)`$ there \[postelmansvanassche\]. This does not transfer to the Möbius row, which is exactly the open constant $`S-\tfrac12`$.

<a id="app:lambert-probability"></a>

## Probability-coordinate geometry: reduced slopes and cylinders

These results live entirely inside the coprime-pair probability coordinate. They normalise reduced directions and quantify Stern–Brocot cylinder and run geometry. They are unconditional geometric consequences and do not imply the open certificate supply.

<a id="reduced-directions-and-cylinder-masses."></a>

#### Reduced directions and cylinder masses.

The fair-coin pair has a particularly rigid distribution after division by its gcd. For positive coprime $`a,b`$, put
``` math
\nu(a,b)=\frac1{2^{a+b}-1},
  \qquad
  M(a,b)=\frac1{(2^a-1)(2^b-1)}.
```
The first quantity is the probability that the reduced direction is $`(a,b)`$; the second is the mass of the Stern–Brocot cylinder rooted at $`(a,b)`$. Let $`M_d(a,b)`$ be the total stop mass in the first $`d`$ generations below that root, where a node $`(u,v)`$ has stop mass $`(2^{u+v}-1)^{-1}`$ and children $`(u+v,v)`$, $`(u,u+v)`$.

<div id="res:directionnormalization" class="proposition">

**Proposition 87** (reduced-direction normalisation). *The reduced directions form a probability distribution,
``` math
\sum_{\substack{a,b\ge1\\(a,b)=1}}\nu(a,b)=1.
```*

</div>

This is the [reduced-direction mass one](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GcdMomentCalculus.lean#L349).

<div id="res:sternbrocotcylinders" class="theorem">

**Theorem 88** (Stern–Brocot cylinder recursion and convergence). *At every positive node,
``` math
M(a,b)=\frac1{2^{a+b}-1}+M(a+b,b)+M(a,a+b),
```
and, uniformly in $`a,b`$ and $`d`$,
``` math
0\le M(a,b)-M_d(a,b)
  \le \left(\frac23\right)^d M(a,b).
```
Consequently $`M_d(a,b)\to M(a,b)`$; at the root $`M(1,1)=1`$.*

</div>

Formalised: [cylinder mass recursion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GcdMomentCalculus.lean#L474), [depth-$`d`$ remainder bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GcdMomentCalculus.lean#L525), and [cylinder convergence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/GcdMomentCalculus.lean#L560). The recursion is the elementary rational identity obtained after setting $`A=2^a`$, $`B=2^b`$; the quantitative point is that the two children retain at most two thirds of their parent’s mass.

<a id="alternating-run-stability."></a>

#### Alternating-run stability.

Write an alternating Stern–Brocot word as $`r`$ nonempty runs of lengths $`n_i=1+e_i`$, with $`e_i\ge0`$. Starting with $`P_\varnothing=(1,1)`$, define
``` math
P_{(n_1,\ldots,n_r)}=(n_1A+B,A)
  \quad\text{when}\quad P_{(n_2,\ldots,n_r)}=(A,B),
  \qquad H(n_1,\ldots,n_r)=P_1+P_2.
```
Thus $`H`$ is the arithmetic height of the primitive pair reached by the word. Let $`F_0=0,F_1=1`$.

<div id="res:sternbrocotruns" class="theorem">

**Theorem 89** (Fibonacci–continuant height stability). *Every $`r`$-run word satisfies
``` math
H(1+e_1,\ldots,1+e_r)
 \ge F_{r+3}+F_{r+1}\sum_{i=1}^r e_i,
```
and $`H(1,\ldots,1)=F_{r+3}`$. A defect confined to position $`i\in\{0,\ldots,r-1\}`$ has the exact size
``` math
H(\underbrace{1,\ldots,1}_{i},1+e,
   \underbrace{1,\ldots,1}_{r-i-1})
 =F_{r+3}+F_{i+2}F_{r-i+1}e.
```
More generally, the checked recurrence gives the full positive multiaffine continuant defect.*

</div>

Formalised: [Fibonacci height lower bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SternBrocotRunGeometry.lean#L185), [multiaffine run-height formula](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SternBrocotRunGeometry.lean#L263), [aggregate defect lower bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SternBrocotRunGeometry.lean#L343), [one-site defect identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SternBrocotRunGeometry.lean#L413).

<div id="res:onerunmass" class="proposition">

**Proposition 90** (one-run probability mass). *The two orientations with one nonempty Stern–Brocot run have total mass
``` math
\frac12.
```*

</div>

This is the [one-run mass](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SternBrocotRunGeometry.lean#L467).

<div id="res:rundenominator" class="proposition">

**Proposition 91** (unit-run denominator exponent). *The natural denominator exponent along the all-unit $`r`$-run is
``` math
\sum_{j=0}^{r-1}F_{j+2}=F_{r+3}-2.
```*

</div>

This is the [natural denominator exponent](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c2c5c3f0151d58c3d8f21843a9fffead4b27f8e3/Erdos249257/SternBrocotRunGeometry.lean#L491).

The Lambert and Möbius identities used above are classical  \[apostol; merca2017; mercaschmidt\], and the mediant language goes back to Farey \[farey1816\]. Postelmans–Van Assche supply the cited irrationality of the constant-weight squared-Lambert row, not these cylinder or run statements. We claim the displayed Lean-checked identities and estimates, not priority for their assembled package. In particular, the exact equality of the Fibonacci height and denominator scales is a boundary, not an irrationality argument: no theorem here proves that a run tail survives denominator clearing.

<a id="appendix-consequence.-3"></a>

#### Appendix consequence.

The transfer is coordinate extension only. Appendix <a href="#app:lambert-weighted" data-reference-type="ref" data-reference="app:lambert-weighted">[app:lambert-weighted]</a> enlarges the Mersenne–Lambert comparison family in Section <a href="#sec:ladder" data-reference-type="ref" data-reference="sec:ladder">3</a>; Appendix <a href="#app:lambert-algebraic" data-reference-type="ref" data-reference="app:lambert-algebraic">12.2</a> supplies the Möbius-square and gcd-moment coordinates; and Appendix <a href="#app:lambert-probability" data-reference-type="ref" data-reference="app:lambert-probability">12.3</a> refines the coprime-pair representation in Proposition <a href="#res:coprime" data-reference-type="ref" data-reference="res:coprime">21</a>. These are three independent coordinate extensions. None implies the cofinal $`\mathsf{Sep}`$ supply for $`S`$ or a proof of $`1/2\in\mathcal A`$. Those, rather than any result internal to this appendix, remain the missing statements identified in the main text.

<a id="app:index"></a>

# Guide to the formal sources

The paper is meant to be read as mathematics. The blue mathematical phrases following formalised statements are intended as links to exact checked theorems in the final published source revision. In this draft the common source pin is a release blocker. Exact declaration names remain in the machine-readable audit layer.

For a first reading, the principal landmarks are Theorem <a href="#res:farey" data-reference-type="ref" data-reference="res:farey">20</a> for the totient denominator exclusion; Proposition <a href="#res:complete" data-reference-type="ref" data-reference="res:complete">23</a> and Theorems <a href="#res:pointwisecomplete" data-reference-type="ref" data-reference="res:pointwisecomplete">24</a>–<a href="#res:diag" data-reference-type="ref" data-reference="res:diag">26</a> for the exact certificate normal forms; and Theorems <a href="#res:halfmembership" data-reference-type="ref" data-reference="res:halfmembership">14</a> and <a href="#res:fatalright" data-reference-type="ref" data-reference="res:fatalright">17</a> for the two half-value classifications. Theorem <a href="#res:full" data-reference-type="ref" data-reference="res:full">4</a> records the classical full-support result, and Section <a href="#sec:architecture" data-reference-type="ref" data-reference="sec:architecture">6</a> states the structure the reductions share. For the strongest independent structure beyond the two open reductions, see Theorem <a href="#res:dyadictotient" data-reference-type="ref" data-reference="res:dyadictotient">73</a>, the sublogarithmic zero-window corollary in the main \#257 results, and Theorems <a href="#res:sternbrocotcylinders" data-reference-type="ref" data-reference="res:sternbrocotcylinders">88</a> and <a href="#res:sternbrocotruns" data-reference-type="ref" data-reference="res:sternbrocotruns">89</a>. The public repository contains a complete searchable cross-reference for readers who need declaration-level detail.

<div class="thebibliography">

99

P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. (N.S.) **12** (1948), 63–66, [archive scan](https://users.renyi.hu/~p_erdos/1948-04.pdf). P. Erdős, *On the irrationality of certain series*, Math. Student **36** (1968), 222–226, [archive scan](https://users.renyi.hu/~p_erdos/1969-09.pdf). P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de l’Enseignement Mathématique, vol. 28, Université de Genève, Geneva, 1980, pp. 61–62, [author-hosted scan](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf). P. Erdős, *On the irrationality of certain series: problems and results*, in *New Advances in Transcendence Theory*, ed. A. Baker, Cambridge University Press, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). P. B. Borwein, *On the irrationality of certain series*, Math. Proc. Cambridge Philos. Soc. **112** (1992), no. 1, 141–146, doi:[10.1017/S030500410007081X](https://doi.org/10.1017/S030500410007081X). T. M. Apostol, *Introduction to Analytic Number Theory*, Undergraduate Texts in Mathematics, Springer, 1976, doi:[10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4). M. Merca, *The Lambert series factorization theorem*, Ramanujan J. **44** (2017), no. 2, 417–435, doi:[10.1007/s11139-016-9856-3](https://doi.org/10.1007/s11139-016-9856-3). M. Merca and M. D. Schmidt, *Generating special arithmetic functions by Lambert series factorizations*, Contrib. Discrete Math. **14** (2019), no. 1, 31–45, doi:[10.55016/ojs/cdm.v14i1.62425](https://doi.org/10.55016/ojs/cdm.v14i1.62425). S. Kakeya, *On the set of partial sums of an infinite series*, Proc. Tokyo Math.-Phys. Soc., 2nd ser. **7** (1914), 250–251, doi:[10.11429/ptmps1907.7.14_250](https://doi.org/10.11429/ptmps1907.7.14_250). J. Farey, *On a curious property of vulgar fractions*, Philos. Mag. **47** (1816), 385–386, doi:[10.1080/14786441608628487](https://doi.org/10.1080/14786441608628487). J.-P. Allouche and J. Shallit, *Automatic Sequences: Theory, Applications, Generalizations*, Cambridge University Press, 2003, doi:[10.1017/CBO9780511546563](https://doi.org/10.1017/CBO9780511546563). M. Coons, *(Non)automaticity of number theoretic functions*, J. Théor. Nombres Bordeaux **22** (2010), no. 2, 339–352, doi:[10.5802/jtnb.718](https://doi.org/10.5802/jtnb.718). Yu. V. Nesterenko, *Modular functions and transcendence questions*, Mat. Sb. **187** (1996), no. 9, 65–96; English transl., Sb. Math. **187** (1996), no. 9, 1319–1348, doi:[10.1070/SM1996v187n09ABEH000158](https://doi.org/10.1070/SM1996v187n09ABEH000158). K. Postelmans and W. Van Assche, *Irrationality of $`\zeta_q(1)`$ and $`\zeta_q(2)`$*, J. Number Theory **126** (2007), no. 1, 119–154, doi:[10.1016/j.jnt.2006.11.011](https://doi.org/10.1016/j.jnt.2006.11.011). F. Luca and Y. Tachiya, *Irrationality of Lambert series associated with a periodic sequence*, Int. J. Number Theory **10** (2014), no. 3, 623–636, doi:[10.1142/S1793042113501121](https://doi.org/10.1142/S1793042113501121). V. Kovač and T. Tao, *On several irrationality problems for Ahmes series*, Acta Math. Hungar. **175** (2025), 572–608, doi:[10.1007/s10474-025-01528-0](https://doi.org/10.1007/s10474-025-01528-0). H. Wang and J. M. Grau Ribas, *Positive dyadic density for rational weighted binary expansions*, arXiv:2606.24972 (2026), doi:[10.48550/arXiv.2606.24972](https://doi.org/10.48550/arXiv.2606.24972). R. Crandall, *The googol-th bit of the Erdős–Borwein constant*, Integers **12** (2012), no. 5, 811–840, doi:[10.1515/integers-2012-0007](https://doi.org/10.1515/integers-2012-0007). J. M. Campbell, *On the binary digits of the Erdős–Borwein constant*, arXiv:2605.24160 (2026), doi:[10.48550/arXiv.2605.24160](https://doi.org/10.48550/arXiv.2605.24160). T. Tao and J. Teräväinen, *Quantitative correlations and some problems on prime factors of consecutive integers*, arXiv:2512.01739v2 (2026), doi:[10.48550/arXiv.2512.01739](https://doi.org/10.48550/arXiv.2512.01739). L. de Moura, S. Kong, J. Avigad, F. van Doorn, and J. von Raumer, *The Lean theorem prover (system description)*, in *CADE-25*, LNCS 9195, Springer (2015), 378–388, doi:[10.1007/978-3-319-21401-6_26](https://doi.org/10.1007/978-3-319-21401-6_26). The mathlib Community, *The Lean mathematical library*, in *CPP 2020*, ACM (2020), 367–381, doi:[10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). T. Bloom (ed.), *Erdős Problems*, [entry 249](https://www.erdosproblems.com/249) and [entry 257](https://www.erdosproblems.com/257), accessed 18 July 2026.

</div>

[^1]: Luca–Tachiya prove the broader eventual-periodic rational-coefficient theorem; its indicator specialisation directly contains case (e) \[lucatachiya\]. Their Chowla–Erdős-style large-modulus proof is distinct from the periodic-divisor certificate route formalised here, and the full mixed-sign coefficient theorem is not claimed.
