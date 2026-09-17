<a id="erdos-243-reciprocal-tail-rigidity"></a>

# Excluding the Bounded Negative Part

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Let $`a_1<a_2<\cdots`$ be positive integers with $`a_{n+1}/a_n^2\to1`$ and rational reciprocal sum, and put $`P_n=\prod_{j<n}a_j`$. We prove that
``` math
\limsup_{n\to\infty}\frac{P_n}{a_n}
 \left(\frac{a_n^2}{a_{n+1}}-1\right)<+\infty
```
forces $`a_{n+1}=a_n^2-a_n+1`$ eventually. We use Koizumi’s integral rational-tail recurrence, extending eventual nonnegative error to an arbitrarily signed error with bounded negative part. The proof combines integer descent, stabilisation of a common divisor and a first crossing of a Chinese-remainder block. A second argument gives an LCM-weighted record criterion. These are sufficient criteria: neither the required defect bound nor the record budget is deduced from the unrestricted hypotheses.

<a id="sec:problem"></a>

# Introduction

<a id="conventions-and-reading-route."></a>

#### Conventions and reading route.

Write $`z_+=\max(z,0)`$, take empty products and least common multiples to be $`1`$, and allow deletion of a finite prefix. In a higher-order rate such as $`1+3/n+o(n^{-3})`$, retain the original index $`n`$: deleting terms does not authorise renumbering that rate. A *Sylvester tail* means eventual equality $`a_{n+1}=a_n^2-a_n+1`$, not a finite reciprocal expansion. For the main argument read the next corollary, the integer-state theorem, Section <a href="#sec:bounded" data-reference-type="ref" data-reference="sec:bounded">2</a> and the transfer in Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">4</a>. Sections <a href="#sec:mass" data-reference-type="ref" data-reference="sec:mass">5</a>–<a href="#sec:lcmrecords" data-reference-type="ref" data-reference="sec:lcmrecords">6</a> give alternative criteria; Section <a href="#sec:secondaryrate" data-reference-type="ref" data-reference="sec:secondaryrate">7</a> records ordinary consequences whose full proofs are in the companion reasoning paper.

For $`a_n>1`$, the recurrence $`a_{n+1}=a_n^2-a_n+1`$ is singled out by the telescope
``` math
\frac1{a_n-1}=\frac1{a_n}+\frac1{a_{n+1}-1}.
```
Thus a Sylvester tail has the exact value $`1/(a_n-1)`$ beginning at index $`n`$. The question is whether rationality and the asymptotic relation $`a_{n+1}\sim a_n^2`$ force that exact recurrence. The following result isolates a sufficient one-sided bound on the departure from it.

<div id="res:originalbounded" class="corollary">

**Corollary 1** (original-coordinate bounded defect). *Let $`a_1<a_2<\cdots`$ be positive integers, $`a_{n+1}/a_n^2\to1`$, and $`\sum_{n\ge1}1/a_n\in\mathbb{Q}`$. Put $`P_n=\prod_{j<n}a_j`$. If
``` math
\limsup_{n\to\infty}\frac{P_n}{a_n}
 \left(\frac{a_n^2}{a_{n+1}}-1\right)<+\infty,
```
then $`a_{n+1}=a_n^2-a_n+1`$ for all sufficiently large $`n`$.*

</div>

The upper limit is allowed to be $`-\infty`$; the condition means an eventual finite upper bound, not a bound on the absolute value. No monotonicity or summability of the growth defect is assumed.

The proof is given in Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">4</a>. The full original-coordinate implication, including the canonical analytic transfer, is also formalised as [the original-coordinate bounded-defect theorem](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos243/PaperCompleteR7/ProductDefect.lean#L211). Its hypothesis is an eventual upper bound on the displayed product defect, equivalent here to the finite-upper-limit condition. The integer-state theorem below isolates the arithmetic step; it is not the whole extent of the formalisation.

<a id="the-obstruction."></a>

#### The obstruction.

Clear the rational reciprocal tail as $`C_n/D_n`$; these are the denominator-cleared tail variables of Koizumi’s pseudo-greedy formulation \[koizumi2025, Corollary 3, p. 9; Lemma 4, pp. 11–12\]. On a Sylvester tail, $`D_n=(a_n-1)C_n`$; the integer error $`E_n=D_n-(a_n-1)C_n`$ measures the failure of this identity. Its update $`C_{n+1}=C_n-E_n`$ turns a bound on negative error into a bound on upward increments. Small increments alone are insufficient. The arithmetic input is that, after the common divisor stabilises, every old multiplier must remain coprime to every later reduced numerator. The Chinese remainder theorem then produces a block of forbidden heights that no permitted jump can cross. A numerator tending to infinity would have to cross it. Section <a href="#sec:lcmrecords" data-reference-type="ref" data-reference="sec:lcmrecords">6</a> adapts this crossing argument when only jumps setting new records are charged.

<div class="samepage">

Write $`\operatorname{ctr}(a,D,C)=D-(a-1)C`$. The following integer-state theorem implies Corollary <a href="#res:originalbounded" data-reference-type="ref" data-reference="res:originalbounded">1</a>; the ordinary tail transfer is proved in Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">4</a>. Its centring hypothesis is redundant under normalised vanishing and is retained to match the source statement.

<div id="res:bounded" class="theorem">

**Theorem 2** (bounded negative part). *Let $`a,C,D:\mathbb{N}\to\mathbb{N}`$ and $`E:\mathbb{N}\to\mathbb{Z}`$ satisfy*

1.  *$`a_n>1`$ and $`C_n>0`$ for every $`n`$;*

2.  *the exact dynamics $`C_{n+1}+D_n=a_nC_n`$ and $`D_{n+1}=a_nD_n`$;*

3.  *$`E_n=\operatorname{ctr}(a_n,D_n,C_n)`$ for every $`n`$;*

4.  **eventual strict centring*: $`|E_n|<C_n`$ for all large $`n`$;*

5.  **eventually bounded negative part*: $`-B\le E_n`$ for all large $`n`$, for some integer $`B\ge0`$;*

6.  **normalised vanishing*: for every integer $`K\ge1`$ there is an $`N`$ with $`K\,|E_n|<C_n`$ for all $`n\ge N`$.*

*Then $`E_n=0`$ for all sufficiently large $`n`$: this is the [eventual bounded-negative rigidity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2360).*

</div>

The Lean proof shifts the orbit past the centring and lower-bound thresholds and applies the [bounded-negative-part rigidity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2271), with centring and bound at every index.

</div>

<div id="res:problem" class="problem">

**Problem 3** (Erdős \#243). Let $`1\le a_1<a_2<\cdots`$ be a sequence of integers with
``` math
\lim_{n\to\infty}\frac{a_n}{a_{n-1}^{2}}=1
 \qquad\text{and}\qquad
 \sum\frac{1}{a_n}\in\mathbb{Q}.
```
Then $`a_n=a_{n-1}^{2}-a_{n-1}+1`$ for all sufficiently large $`n`$.

</div>

The question is recorded by Erdős and Graham \[erdosgraham1980\] and by Erdős \[erdos1988, p. 105\], and Bloom’s catalogue lists it as Problem #243 \[erdosproblems\].

The additional hypothesis in Theorem <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">2</a> is the lower bound on $`E_n`$. The growth and rationality assumptions already supply the other state hypotheses after a finite shift. The nonnegative-error case, Badea’s criterion \[badea1993, Corollary 2.2, p. 316\] in Koizumi’s coordinates, is integer descent \[koizumi2025, Proposition 1(2), p. 14\]; the theorem allows arbitrary sign changes with bounded negative depth. The published product-weighted criterion, stated as Koizumi’s Corollary 4(1), assumes a nonpositive upper limit \[koizumi2025, pp. 14–15\], and Corollary <a href="#res:originalbounded" data-reference-type="ref" data-reference="res:originalbounded">1</a> allows any finite upper limit. Bado’s preprint, posted in September 2026, assumes two-sided bounded errors \[bado2026, Theorem 5.1, p. 4\]; Theorem <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">2</a> needs only an eventual lower bound.

<a id="sec:bounded"></a>

# Proof of bounded-negative rigidity

The arithmetic ingredients are proved immediately afterwards. Normalised vanishing and integrality give $`C_n\to\infty`$ on a nonzero tail, while the lower error bound gives $`C_{n+1}\le C_n+B`$.

<div class="proof">

*Proof of Theorem <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">2</a>.* Suppose not. By Theorem <a href="#res:absorb" data-reference-type="ref" data-reference="res:absorb">6</a>, after the centring threshold a single zero would force every later error to be zero. Thus $`E_n\ne0`$ throughout a sufficiently late tail. If negative indices are infinite, condition (5) bounds their magnitudes. Proposition <a href="#res:gcdstab" data-reference-type="ref" data-reference="res:gcdstab">11</a> makes $`G_n=\gcd(C_n,D_n)`$ constant, say $`g>0`$, from some index onwards. On this tail $`u_n=C_n/g`$ and $`v_n=D_n/g`$ form a reduced exact orbit. Normalised vanishing and $`|E_n|\ge1`$ give $`C_n\to\infty`$, hence $`u_n\to\infty`$. Also $`u_{n+1}-u_n=-E_n/g\le B`$. Theorem <a href="#res:barrier" data-reference-type="ref" data-reference="res:barrier">9</a> contradicts these bounded upward steps; when $`B=0`$, descent alone already contradicts divergence. If negative indices are finite, the remaining error is nonnegative and Theorem <a href="#res:descent" data-reference-type="ref" data-reference="res:descent">[res:descent]</a> makes it eventually zero, again a contradiction. ◻

</div>

<div id="res:cor" class="corollary">

**Corollary 4**. *Under Theorem <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">2</a>, the multipliers satisfy $`a_{n+1}=a_n^2-a_n+1`$ eventually.*

</div>

<div class="proof">

*Proof.* Apply the two-zero implication in Corollary <a href="#res:eventual" data-reference-type="ref" data-reference="res:eventual">[res:eventual]</a> below. ◻

</div>

<a id="sec:state"></a>

# The arithmetic ingredients

<a id="sec:defect"></a>

## Error, absorption and descent

<span id="sec:descent" label="sec:descent"></span> The identities below follow algebraically from Koizumi’s state recurrence \[koizumi2025, Lemmas 2–4, pp. 10–12\]. His Lemma 3 gives absorption, and his Proposition 1(2) gives the nonnegative-error descent, credited there to Badea \[badea1993, Corollary 2.2, p. 316\]. The integer-remainder method for Cantor series is older \[erdosstraus1974, Theorem 2.1, pp. 85–86\]. Hančl and Tijdeman use a finite polynomial decomposition and the resulting shifted polynomial sum to characterise rationality of polynomial Cantor series \[hancltijdeman2008, Theorem 2.2 and its derivation, pp. 39–40\]. Their polynomial hypotheses are essential to this comparison; we do not invoke an unrestricted rearrangement of arrays of integer coefficients. These are antecedents of the remainder method, not proofs of the bounded-negative Chinese-remainder obstruction used here.

Write $`\Delta_n=a_{n+1}-(a_n^2-a_n+1)`$.

<div id="res:update" class="proposition">

**Proposition 5** (error identities). *<span id="res:defect" label="res:defect"></span> For an exact integer state,
``` math
C_{n+1}=C_n-E_n,\qquad
 \Delta_n C_{n+1}=a_n^2E_n-E_{n+1}.
```*

</div>

<div class="proof">

*Proof.* Substitute $`E_n=D_n-(a_n-1)C_n`$ and use $`D_{n+1}=a_nD_n`$, $`C_{n+1}=a_nC_n-D_n`$. ◻

</div>

Both identities are the [update law](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L57) and the [defect identity](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1775).

<div id="res:absorb" class="theorem">

**Theorem 6** (absorption and descent). *<span id="res:descent" label="res:descent"></span> For a positive exact state with strict centring, $`E_n=0`$ implies $`E_{n+1}=0`$. For any positive integer state with $`C_{n+1}=C_n-E_n`$, eventual nonnegativity of $`E_n`$ implies its eventual vanishing.*

</div>

<div class="proof">

*Proof.* When $`E_n=0`$, the second identity makes $`E_{n+1}`$ a multiple of $`C_{n+1}`$; strict centring forces that multiple to be zero. In the second assertion, $`C_n`$ is eventually a nonincreasing sequence of positive integers, so it stabilises. ◻

</div>

Both assertions are [absorption of a vanishing centred state](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2227) and [stabilisation of the nonnegative error](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1843).

<div id="res:step" class="corollary">

**Corollary 7** (two zero errors). *<span id="res:eventual" label="res:eventual"></span> If $`E_n=E_{n+1}=0`$ and $`C_{n+1}\ne0`$, then $`a_{n+1}=a_n^2-a_n+1`$. Thus eventual zero error in a positive exact state implies the eventual Sylvester recurrence.*

</div>

<div class="proof">

*Proof.* The second error identity has nonzero factor $`C_{n+1}`$. ◻

</div>

The local and eventual forms are the [local rigidity step](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1787) and the [eventual Sylvester recurrence](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1805).

Absorption holds after any eventual centring threshold. On a nonterminal tail it removes all subsequent zeros. Then $`|E_n|\ge1`$, so normalised vanishing gives $`C_n\to\infty`$.

<a id="sec:barrier"></a>

## The first-crossing obstruction

<div id="res:crt" class="lemma">

**Lemma 8** (consecutive multiples). *For pairwise coprime integers $`m_0,\ldots,m_{B-1}\ge2`$ and every lower bound, there is a larger $`t`$ such that $`m_i\mid t+i`$ for each $`i<B`$.*

</div>

<div class="proof">

*Proof.* Solve $`t\equiv-i\pmod{m_i}`$ by the Chinese remainder theorem, then add multiples of $`\prod_i m_i`$. ◻

</div>

Lemma <a href="#res:crt" data-reference-type="ref" data-reference="res:crt">8</a> matches each modulus $`m_i`$ to its own multiple $`t+i`$ inside a window of $`B`$ consecutive integers. The same forbidden block and first-crossing contradiction, under a two-sided bound on the error, appear in the proof of Bado’s Theorem 5.1 \[bado2026, pp. 4–5\]. The lemma here isolates bounded upward movement, and the gcd stabilisation below makes it applicable with only a lower bound on the error.

<div id="res:barrier" class="theorem">

**Theorem 9** (bounded-rise obstruction). *Let $`u:\mathbb{N}\to\mathbb{N}`$ tend to infinity and let $`B\ge1`$ be an integer with $`u_{n+1}\le u_n+B`$ for every $`n`$. There is no sequence of pairwise coprime integers $`m_i\ge2`$ for which $`\gcd(m_i,u_t)=1`$ whenever $`i<t`$.*

</div>

<div class="proof">

*Proof.* Choose $`m_0,\ldots,m_{B-1}`$ and use Lemma <a href="#res:crt" data-reference-type="ref" data-reference="res:crt">8</a> to find $`t>\max(u_0,\ldots,u_B)`$ with $`m_i\mid t+i`$. Since $`u_n\to\infty`$, there is a first $`n>B`$ with $`u_n\ge t`$. Minimality and the rise bound give
``` math
t\le u_n\le u_{n-1}+B<t+B.
```
Hence $`u_n=t+i`$ for some $`0\le i<B<n`$, so $`m_i\mid u_n`$. This contradicts $`\gcd(m_i,u_n)=1`$. The argument uses first crossing, not monotonicity: the numerator may fall before it reaches the block. ◻

</div>

<a id="reduction-and-stabilisation"></a>

## Reduction and stabilisation

A reduced exact tail has positive $`u_n`$, integer $`v_n\ge0`$, $`\gcd(u_n,v_n)=1`$, and
``` math
u_{n+1}=a_nu_n-v_n,\qquad v_{n+1}=a_nv_n.
```

<div id="res:reduced" class="proposition">

**Proposition 10** (persistent coprimality). *In a reduced exact tail, $`\gcd(a_n,v_n)=1`$. Distinct multipliers are pairwise coprime, and every earlier multiplier is coprime to every later numerator.*

</div>

<div class="proof">

*Proof.* A common prime divisor of $`a_n,v_n`$ would divide both $`u_{n+1}`$ and $`v_{n+1}`$. Also, $`a_i\mid v_t`$ for $`i<t`$, so reducedness gives $`\gcd(a_i,u_t)=1`$, and $`\gcd(a_t,v_t)=1`$ gives $`\gcd(a_i,a_t)=1`$. ◻

</div>

All three conclusions are the [step coprimality](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L989), the [pairwise coprimality](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1016), and the [whole-modulus avoidance](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1030).

<div id="res:gcdstab" class="proposition">

**Proposition 11** (gcd stabilisation). *For a positive exact state, if negative errors have bounded magnitudes along a cofinal set of indices, then $`G_n=\gcd(C_n,D_n)`$ eventually stabilises. Division by its stable value gives a reduced exact tail.*

</div>

<div class="proof">

*Proof.* Both updates preserve common divisors, so $`G_n\mid G_{n+1}`$. Moreover $`G_n\mid E_n`$, hence $`G_n\le -E_n`$ at a negative index. The positive divisibility chain is bounded along a cofinal set and therefore bounded everywhere; it eventually stabilises. Division by the stable value preserves both exact updates and leaves the states coprime. ◻

</div>

The stable gcd is [gcd stabilisation](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1636).

In the main proof, division by the stable gcd preserves divergence and a bounded upward increment. Theorem <a href="#res:barrier" data-reference-type="ref" data-reference="res:barrier">9</a> therefore applies to the reduced numerator: this is the [eventual reduced exclusion](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1066). With normalised vanishing the same obstruction is the [exclusion from normalised vanishing](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1754). Sparse changes of the gcd without eventual stabilisation are a different statement; the supporting record retains that distinction and its finite-block consequences.

<a id="sec:transfer"></a>

# Transfer to a reciprocal series

The variables below are Koizumi’s denominator-cleared rational tail \[koizumi2025, Lemma 4, pp. 11–12\], with the indexing and the common clearing factor used here. Let $`x_n=\sum_{k\ge n}1/a_k`$, suppose $`x_1=p/q`$ with $`q>0`$, and put
``` math
P_n=\prod_{j<n}a_j,\qquad D_n=qP_n,\qquad C_n=D_nx_n.
```
Each $`C_n`$ is a positive integer: explicitly,
``` math
C_n=pP_n-q\sum_{k<n}P_n/a_k.
```
Every quotient in the finite sum is an integer. Positivity follows from $`x_n>0`$. The identity $`x_n=1/a_n+x_{n+1}`$ now gives both exact updates; no approximation or rounding occurs in this construction.

For all large $`n`$, $`a_{n+1}\ge a_n^2/2\ge2a_n`$. Iterating the first inequality after an index with $`a_n>2`$ gives $`a_n\ge\exp(c2^n)`$ for some $`c>0`$. Summing the remaining doubled tail gives
``` math
x_n=\frac1{a_n}+\frac1{a_{n+1}}+O(a_{n+1}^{-2}).
```
Consequently
``` math
\frac{C_{n+1}}{C_n}
 =\frac{a_nx_{n+1}}{x_n}
 =\frac{a_n^2}{a_{n+1}}+O(1/a_n)\longrightarrow1,
 \qquad \frac{E_n}{C_n}\longrightarrow0.
```
Taking logarithms and averaging also gives $`\log C_n=o(n)`$; the same argument gives $`\log\max_{j\le n}C_j=o(n)`$, since a fixed initial maximum has negligible logarithm divided by $`n`$. Strict centring follows eventually. These are the ordinary canonical-tail implications of Koizumi’s work. After a finite shift the sequence is the pseudo-greedy expansion of its own tail sum, with gap sequence tending to zero \[koizumi2025, Corollary 3, p. 9\]. On that tail the integers $`c_n`$, $`d_n`$ and $`e_n`$ of his Lemma 4 \[koizumi2025, pp. 11–12\] are $`C_n`$, $`D_n`$ and $`E_n`$ up to one common positive factor, and his range $`-c_n/2\le e_n<c_n/2`$ gives $`|E_n|<C_n`$.

<div class="proof">

*Proof of Corollary <a href="#res:originalbounded" data-reference-type="ref" data-reference="res:originalbounded">1</a>.* Put $`\gamma_n=a_n^2/a_{n+1}-1`$. Since
``` math
\frac{P_{n+1}/a_{n+1}}{P_n/a_n}=1+\gamma_n\longrightarrow1,
 \qquad P_n/a_n=\exp(o(n)),
```
the two-term estimate gives
``` math
\begin{aligned}
 E_n&=\frac{qP_n}{a_n}-\frac{qP_n(a_n-1)}{a_{n+1}}
 +O\!\left(\frac{qP_na_n}{a_{n+1}^2}\right),\\
 q\frac{P_n}{a_n}\gamma_n
 &=\frac{qP_na_n}{a_{n+1}}-\frac{qP_n}{a_n}.
 \end{aligned}
```
Adding cancels the two terms of size $`qP_n/a_n`$ and leaves
``` math
\begin{equation}
\label{eq:canonical-dictionary}
 E_n+q\frac{P_n}{a_n}\gamma_n
 =\frac{qP_n}{a_{n+1}}+
 O\!\left(\frac{qP_na_n}{a_{n+1}^2}\right)=o(1).
\end{equation}
```
Indeed, quadratic growth makes the two terms on the right respectively $`\exp(o(n))/a_n`$ and $`\exp(o(n))/a_n^2`$, up to bounded factors. The assumed upper bound therefore gives an eventual lower bound on the integer $`E_n`$. After deleting a finite prefix, all hypotheses of Theorem <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">2</a> hold. Apply Corollary <a href="#res:cor" data-reference-type="ref" data-reference="res:cor">4</a>. ◻

</div>

Identity <a href="#eq:canonical-dictionary" data-reference-type="eqref" data-reference="eq:canonical-dictionary">[eq:canonical-dictionary]</a> is the product-weighted comparison used in Koizumi’s proof of his Corollary 4(1) \[koizumi2025, (11)–(12), p. 15\], written in the canonical variables.

The same estimate holds for any positive real scale $`H_n\le qP_n`$. Put $`W_n=H_nx_n`$ and $`Z_n=H_n-(a_n-1)W_n`$; these quantities need not be integers unless $`H_n`$ actually clears the denominator of $`x_n`$. Then
``` math
\begin{equation}
\label{eq:general-clearance-dictionary}
 Z_n+\frac{H_n}{a_n}\gamma_n=o(1).
\end{equation}
```
For $`H_n=L_n`$ below, denominator clearing does hold, and the resulting integral variables satisfy their own LCM update rather than the raw product update. This supplies the LCM-prefactor consequence.

<a id="sec:mass"></a>

# A scalar finite-mass criterion

<div id="res:massscalar" class="theorem">

**Theorem 12** (finite negative relative mass). *<span id="res:mass" label="res:mass"></span> Let $`C_n`$ be positive integers and $`E_n`$ integers satisfying $`C_{n+1}=C_n-E_n`$. If
``` math
\sum_n\frac{(-E_n)_+}{C_n}<\infty,
```
then $`E_n=0`$ eventually. Neither denominator dynamics nor normalised vanishing is required. Positivity and integrality of $`C_n`$ are essential.*

</div>

<div class="proof">

*Proof.* Set $`\delta_n=(-E_n)_+/C_n`$. Then
``` math
C_N\le C_0\prod_{n<N}(1+\delta_n)
 \le C_0\exp\!\left(\sum_n\delta_n\right).
```
Choose an integer upper bound $`K`$ for $`C_n`$. Each strict rise contributes at least $`1/K`$ to $`\sum\delta_n`$, so there are only finitely many rises. The remaining positive integer sequence is nonincreasing and stabilises, and the update then gives $`E_n=0`$. ◻

</div>

For comparison, the real sequence $`C_n=1+1/(n+1)`$ has $`E_n=C_n-C_{n+1}>0`$ and zero negative mass, but never stabilises. Thus the scalar conclusion is genuinely discrete.

The scalar statement, with no denominator dynamics or normalised-vanishing assumption, is formalised as [vanishing from finite scalar negative mass](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/SparseResetRecovery.lean#L612). Its exact-orbit consequence is [the Sylvester recurrence from finite scalar negative mass](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/SparseResetRecovery.lean#L690). The same three declarations on an exact reciprocal-tail orbit, with denominator dynamics and normalised vanishing, are [the exact-orbit growth bound](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/SparseResetRecovery.lean#L378), [vanishing from summable exact-orbit negative mass](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/SparseResetRecovery.lean#L488), and [the exact-orbit Sylvester recurrence from summable negative mass](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/SparseResetRecovery.lean#L510). The shorter proof above is included because this implication is an elementary product bound followed by descent of positive integers.

On an exact reciprocal-tail orbit the conclusion gives the Sylvester recurrence. For the gap sequence of the pseudo-greedy expansion, the same criterion, with the same product bound and integer descent, appears in the Erdős Problem a Day working report on Problem #243, dated 12 August 2026 \[erdosproblemaday243, A global termination criterion\]; the statement above is for any positive integer sequence with $`C_{n+1}=C_n-E_n`$. The scalar criterion and bounded negative error are distinct quantities to estimate; on the common exact-orbit class with normalised vanishing they are each equivalent to the same endpoint.

<a id="sec:lcmrecords"></a>

# Weighted first crossings of LCM records

Only steps setting an LCM numerator record need contribute. The first-crossing argument permits subtraction of a fixed baseline and any nonincreasing nonnegative weight with divergent integral. We give the ordinary proof below. The separate release also contains the full canonical weighted statement, [the real-weight criterion](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos243/PaperCompleteR8/CanonicalWeightedRecords.lean#L268); it is outside the checked main-repository build documented here. The LCM coordinates also appear in Bado’s September 2026 preprint: with his denominator parameter equal to $`q`$, his $`M_{n-1}`$, $`\Delta_{n-1}`$, $`K_{n-1}`$, $`u_n`$ and $`g_n`$ are the $`L_n`$, $`M_n`$, $`U_n`$, $`V_n`$ and $`\rho_n`$ below, and his (19) is $`\rho_nU_{n+1}=U_n-V_n`$ \[bado2026, Proposition 7.1 and (16)–(20), pp. 6–7\]. This overlap concerns both the coordinates and their update, not merely terminology.

Set
``` math
L_n=\operatorname{lcm}(q,a_1,\ldots,a_{n-1}),\quad
 M_n=D_n/L_n,\quad U_n=C_n/M_n,\quad V_n=E_n/M_n.
```
The rational tail has denominator dividing $`L_n`$, so $`U_n`$ and $`V_n`$ are integers. With $`\rho_n=\gcd(L_n,a_n)`$, the exact updates are
``` math
M_{n+1}=M_n\rho_n,\qquad
 \rho_nU_{n+1}=U_n-V_n,\qquad V_n=L_n-(a_n-1)U_n.
```
Write $`R_n=\max_{j\le n}U_j`$ and $`\mathcal R=\{n:U_{n+1}>R_n\}`$. Strict centring already gives $`U_{n+1}<U_n`$ when $`\rho_n\ge2`$, so every sufficiently late strict rise has $`\rho_n=1`$. The stronger eventual bound $`-U_n\le2V_n`$, supplied by $`V_n/U_n=E_n/C_n\to0`$, gives the quantitative estimate $`U_{n+1}\le3U_n/4`$ when $`\rho_n\ge2`$. At a sufficiently late record step, where $`\rho_n=1`$, the actual jump is $`d_n=U_{n+1}-U_n=-V_n>0`$. This identity is not asserted at a contracting step with $`\rho_n\ge2`$.

<div id="res:weightedrecord" class="theorem">

**Theorem 13** (weighted record excess). *Assume the growth and rationality hypotheses of Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">3</a>. Let $`f:[1,\infty)\to[0,\infty)`$ be finite and nonincreasing, with $`\int_1^\infty f(t)\,dt=\infty`$. Then the sequence is eventually Sylvester if and only if, for some integer $`B\ge0`$,
``` math
\sum_{n\in\mathcal R}(-V_n-B)_+f(U_n)<\infty.
```*

</div>

<div class="proof">

*Proof.* Suppose the sequence is not eventually Sylvester. Absorption and integrality give $`1/U_n\le |V_n|/U_n=|E_n|/C_n\to0`$, so there are infinitely many record steps. Here *fresh* means $`\rho_n=1`$; every sufficiently late record has this property. “Fresh” does not mean that the digit itself is prime. Their digits are pairwise coprime: an earlier digit divides the later $`L_n`$, while the digit at a fresh record is coprime to $`L_n`$. For any fixed $`B\ge1`$, choose $`B`$ such digits $`m_0,\ldots,m_{B-1}>B`$ and take $`T`$ after their indices and after the freshness threshold. Their size follows from $`a_n\to\infty`$.

Put $`P=\prod_i m_i`$ and choose $`x`$ by the Chinese remainder theorem with $`m_i\mid x+i`$. Consider all translates $`\tau=x+B+kP>R_T`$, $`k\in\mathbb{Z}`$; the first is at most $`R_T+P`$. A first crossing $`U_n\le R_n<\tau\le U_n+d_n`$ is a record step. If $`d_n\le B`$, then $`U_n\in[\tau-B,\tau)`$, so some $`m_i`$ divides $`U_n`$. It also divides $`L_n`$, hence divides $`d_n=(a_n-1)U_n-L_n`$, contradicting $`0<d_n\le B<m_i`$.

If the step first crosses $`h\ge1`$ such heights, their spacing gives $`(h-1)P<d_n`$. With $`r=d_n-B\ge1`$ and $`P\ge B+1`$, we have $`d_n=B+r\le Pr`$, whence $`h\le r`$. Monotonicity of $`f`$ now gives
``` math
\sum_{\substack{\tau\text{ first crossed}\\\text{at step }n}}f(\tau)
 \le(d_n-B)f(U_n).
```
Each selected height above $`R_T`$ has exactly one first crossing. The first selected height is at most $`R_T+P`$; each later height is $`P`$ further on. For $`R_N\ge R_T+P`$, comparison of each interval with its left endpoint gives
``` math
\begin{equation}
\label{eq:weightedcrossing}
 \sum_{\substack{T\le n<N\\n\in\mathcal R}}(-V_n-B)_+f(U_n)
 \ge\frac1P\int_{R_T+P}^{R_N} f(t)\,dt.
\end{equation}
```
Since $`R_n\to\infty`$, the right side diverges for every $`B\ge1`$; $`B=0`$ follows by domination. Conversely a Sylvester tail telescopes to $`x_n=1/(a_n-1)`$, so $`V_n=0`$ eventually. ◻

</div>

For example, $`f(t)=1/[t\log(et)]`$ gives the sufficient condition
``` math
\sum_{n\in\mathcal R}\frac{(-V_n-B)_+}{U_n\log(eU_n)}<\infty.
```
Its finite lower bound in <a href="#eq:weightedcrossing" data-reference-type="eqref" data-reference="eq:weightedcrossing">[eq:weightedcrossing]</a> is $`P^{-1}\log\bigl(\log(eR_N)/\log(e(R_T+P))\bigr)`$. Further fixed iterated logarithmic factors are allowed whenever the integral still diverges. These are specialisations of one crossing theorem.

The criterion also has an exact expression in the original growth defect. Put $`\gamma_n=a_n^2/a_{n+1}-1`$ and $`\theta_n=E_n/C_n`$. The defect identity gives
``` math
\gamma_n+\theta_n=
 \frac{(1-\theta_n)(a_n-1+\theta_{n+1})}{a_{n+1}},
 \qquad 0<\gamma_n+\theta_n<3/a_n
```
eventually. Thus the two nonnegative summands $`U_nf(U_n)(\gamma_n-B/U_n)_+`$ and $`(-V_n-B)_+f(U_n)`$ differ by at most $`3U_nf(U_n)/a_n`$. This is summable because $`U_n\le C_n=\exp(o(n))`$, $`f(U_n)\le f(1)`$, and $`a_n\ge\exp(c2^n)`$ eventually for some $`c>0`$. Consequently Theorem <a href="#res:weightedrecord" data-reference-type="ref" data-reference="res:weightedrecord">13</a> is equivalent to finiteness of
``` math
\begin{equation}
\label{eq:weightedgrowth}
 \sum_{n\in\mathcal R}U_nf(U_n)
 \left(\frac{a_n^2}{a_{n+1}}-1-\frac B{U_n}\right)_+
\end{equation}
```
for some $`B`$. The original hypotheses do not currently supply this finiteness. In particular, termwise convergence to zero is insufficient. Also, $`d_n`$ is the actual jump, including any recovery from a drawdown; it must not be replaced by $`R_{n+1}-R_n`$ in the crossing proof.

<div id="res:lcmbounded" class="corollary">

**Corollary 14** (LCM-weighted bounded defect). *Assume the hypotheses of Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">3</a>. Write $`A_n=\operatorname{lcm}(a_1,\ldots,a_{n-1})`$ with $`A_1=1`$ and
``` math
Z_n=\frac{A_n}{a_n}\Bigl(\frac{a_n^2}{a_{n+1}}-1\Bigr).
```
If $`\limsup Z_n<\infty`$, then the sequence is eventually Sylvester.*

</div>

<div class="proof">

*Proof.* Put $`t_n=L_n/A_n=q/\gcd(q,A_n)`$, so $`1\le t_n\le q`$. Equation <a href="#eq:general-clearance-dictionary" data-reference-type="eqref" data-reference="eq:general-clearance-dictionary">[eq:general-clearance-dictionary]</a>, with $`H_n=L_n`$, gives $`V_n+t_nZ_n=o(1)`$. A finite upper bound on $`Z_n`$ therefore bounds the negative part of $`V_n`$. The record series vanishes after a finite prefix for a sufficiently large baseline, so Theorem <a href="#res:weightedrecord" data-reference-type="ref" data-reference="res:weightedrecord">13</a> applies. ◻

</div>

Erdős and Straus assume a nonpositive upper limit in the corresponding next-index LCM expression \[erdosstraus1964, Theorem 3, p. 132\], and Tijdeman and Yuan give a criterion of the same kind for positive numerators \[tijdemanyuan2002\]. Here any finite upper bound suffices under the quadratic-limit assumption. Since $`A_n\mid P_n`$, this also implies Corollary <a href="#res:originalbounded" data-reference-type="ref" data-reference="res:originalbounded">1</a>: multiplication by a factor in $`(0,1]`$ preserves an upper bound, including at negative values.

Lean checks Corollary <a href="#res:lcmbounded" data-reference-type="ref" data-reference="res:lcmbounded">14</a> as [the original-coordinate LCM bounded defect](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos243/PaperCompleteR7/LcmDefect.lean#L49). That declaration takes the rational reciprocal sum and the quadratic growth limit as hypotheses, with the finite upper limsup recorded as an eventual upper bound on $`Z_n`$; it assumes no divisibility of the denominator by the prefix LCM.

Duverney proved a conditional signed form of the problem itself: for signs $`\epsilon_n\in\{-1,1\}`$, if $`\sum_{n\ge0}(a_{n+1}/a_n^{2}-1)`$ converges, then the reciprocal sum with numerators $`\epsilon_n`$ is rational if and only if
``` math
a_{n+1}=a_n^2-(\epsilon_{n+1}/\epsilon_n)a_n
             +\epsilon_{n+2}/\epsilon_{n+1}
```
for all large $`n`$ \[duverney2001, Corollary 3.2, p. 287\]. Absolute convergence is a stronger sufficient specialisation, not the hypothesis printed in that corollary. The all-positive specialisation is the form relevant here.

For a quantitative comparison, Duverney, Kurosawa and Shiokawa \[duverneykurosawashiokawa2020, Theorem 1, author-version p. 2\] compute irrationality exponents for signed reciprocal series under eventual $`x_{n+1}\ge x_n^2`$ and a denominator-growth condition on successive rational ratios. The growth-side inequality excludes a Sylvester tail; that theorem is not an unrestricted near-quadratic rigidity result.

The divisor constraint also survives integral numerator coefficients: $`d=(a_n-1)U_n-b_nL_n`$ is divisible by every divisor of both $`U_n,L_n`$. An ordinary coefficient-uniform variant gives bounded LCM height from a bounded negative part; normalised vanishing is used afterwards for stationarity. For positive numerator coefficients the classical comparators are Badea’s Corollary 2.2 \[badea1993, p. 316\] and the criterion of Tijdeman and Yuan \[tijdemanyuan2002\]. Its proof and exact bounded-height counterexamples are in the [coefficient proof supplement](https://github.com/wcook04/plectis-erdos/blob/eccd8afc6db3c02a2265d0601b727d6c5e4467d5/lean/ErdosProblems/Erdos243/CoefficientUniformBoundedHeight.md).

<a id="sec:secondaryrate"></a>

# Further consequences

<div id="res:inclusiveone" class="corollary">

**Corollary 15** (an inclusive one-sided $`1/n`$ bound). *Under the hypotheses of Corollary <a href="#res:originalbounded" data-reference-type="ref" data-reference="res:originalbounded">1</a>, suppose that for some $`K\ge0`$ and $`\varepsilon>0`$,
``` math
\gamma_n:=a_n^2/a_{n+1}-1\le \frac1n+\frac{K}{n^{1+\varepsilon}}
 \quad\hbox{for all large }n.
```
Then the sequence is eventually Sylvester. In particular, the conclusion holds under the pointwise eventual bound $`\gamma_n\le1/n`$.*

</div>

<div class="proof">

*Proof.* Set $`t_n=P_n/a_n`$, so $`t_{n+1}/t_n=1+\gamma_n`$. For all large $`n`$,
``` math
1+\gamma_n\le(1+1/n)(1+K/n^{1+\varepsilon}).
```
The first product telescopes and the second is bounded, giving $`t_n=O(n)`$. Since $`(\gamma_n)_+=O(1/n)`$, the product defect $`t_n\gamma_n`$ is bounded above. Apply Corollary <a href="#res:originalbounded" data-reference-type="ref" data-reference="res:originalbounded">1</a>. ◻

</div>

This is an ordinary corollary of the bounded-defect theorem. It does not assert that the weaker condition $`\limsup n(\gamma_n)_+\le1`$ suffices; a vanishing but nonsummable excess over $`1/n`$ is not covered by this proof.

<div id="res:cubicrate" class="theorem">

**Theorem 16** (cubic-rate irrationality). *A strictly increasing sequence of positive integers with
``` math
a_n^2/a_{n+1}=1+\frac3n+o(n^{-3})
```
has irrational reciprocal sum.*

</div>

<div class="proof">

*Proof by the polynomial exclusion.* Under rationality, Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">4</a> gives $`C_{n+1}/C_n=1+3/n+o(n^{-3})`$. Integer finite differences then give $`C_n=An(n+1)(n+2)+B`$ eventually, with $`A\in\mathbb{Q}_{>0}`$ and $`B\in\mathbb{Q}`$. The fixed-cubic exclusion contradicts this profile. The complete ordinary argument, including the finite-difference extraction and the cubic-field step, is in Section 2 of the [companion reasoning paper](https://wcook04.github.io/plectis/papers/erdos243-reciprocal-tail-reasoning-surface.pdf). The field step uses Chebotarev; see \[stevenhagenlenstra1996, Section 3, author version\] for that classical input. This paragraph is a proof by a stated companion result, not a standalone finite-congruence proof and not an assembled Lean proof. ◻

</div>

The same finite-difference extraction excludes every nonintegral $`\lambda>1`$ under the rate $`a_n^2/a_{n+1}=1+\lambda/n+o(n^{-\lambda})`$: eventual polynomial growth would force its degree to equal $`\lambda`$. The extraction uses $`\Gamma(n+\lambda)/\Gamma(n)\sim n^\lambda`$ \[dlmf_gamma, 5.11.12\]; its full proof is in the companion paper. These rates fall outside $`1+o(1/n)`$, the rate at which Koizumi notes that the Erdős–Straus criterion settles the problem \[koizumi2025, Remark 3, p. 16\], and they make Duverney’s signed series $`\sum_n(a_{n+1}/a_n^{2}-1)`$ diverge.

For $`x_1=p/q`$ the integer $`C_n`$ of Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">4</a> is $`q`$ times the linear form $`P_nx_1-P_n\sum_{k<n}1/a_k`$, whose coefficients are integers. Approximation criteria for irrationality use nonzero forms of this kind that tend to zero. At the cubic rate these forms grow: since $`a_nx_n\to1`$, the identity $`(P_{n+1}/a_{n+1})/(P_n/a_n)=1+\gamma_n`$ of Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">4</a> makes $`C_n/q=P_nx_n`$ a positive multiple of $`n(n+1)(n+2)`$ up to a factor tending to one. The proof of Theorem <a href="#res:cubicrate" data-reference-type="ref" data-reference="res:cubicrate">16</a> uses the rate at precision $`o(n^{-3})`$: for a rational sum it forces the exact profile $`C_n=An(n+1)(n+2)+B`$, which is then excluded.

There is also an ordinary quantitative extension, not an end-to-end Lean-checked theorem. Under the hypotheses of Theorem <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">2</a> other than (5), put $`\operatorname{LL}(x)=\log_2\log_2\max(4,x)`$. Each fixed $`\delta\in(0,1)`$ gives
``` math
(-E_n)_+\le(1-\delta)\operatorname{LL}(C_n)
 \quad\text{eventually}\quad\Longrightarrow\quad E_n=0\text{ eventually}.
```
Here $`D_0>0`$ follows after a shift from $`a_n>1`$, $`C_n>0`$ and normalised vanishing. The LCM version needs the corresponding bound only at late record steps. The proofs use a CRT block in $`[P,2P)`$ and the canonical multiplier scale; they are retained in [the slow-negative proof](https://github.com/wcook04/plectis-erdos/blob/eccd8afc6db3c02a2265d0601b727d6c5e4467d5/lean/ErdosProblems/Erdos243/SlowNegativePartRigidity.md) and [the record-only extension](https://github.com/wcook04/plectis-erdos/blob/eccd8afc6db3c02a2265d0601b727d6c5e4467d5/lean/ErdosProblems/Erdos243/LcmRecordExcess.md#5-record-only-subcritical-log-log-bound). These are ordinary results with stated rate hypotheses; neither establishes the general record budget.

Rapid decay alone should not be confused with the rigidity of this particular recurrence. In the different setting of Erdős Problem #270, Crmarić and Kovač \[crmarickovac2025, Theorems 1–2\] show that the sums $`\sum_n\bigl(\prod_{j=1}^{f(n)}(n+j)\bigr)^{-1}`$, with integer $`f(n)\to\infty`$, range over all positive reals. With $`f`$ nondecreasing the value set instead has measure zero, which does not establish irrationality of every such sum. Their flexible-series construction is contextual here, not an antecedent of the tail-state rigidity proof.

<a id="sec:open"></a>

# The remaining arithmetic estimate

<div id="res:frontier" class="proposition">

**Proposition 17** (necessary profile). *The canonical state of a sequence satisfying Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">3</a>’s hypotheses but not its conclusion has $`E_n\ne0`$ eventually, $`|E_n|/C_n\to0`$, unbounded negative magnitudes along negative indices, and
``` math
\sum_n\frac{(-E_n)_+}{C_n}=\infty.
```*

</div>

<div class="proof">

*Proof.* Absorption excludes late zeros, descent excludes an eventually nonnegative error, and Theorems <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">2</a> and <a href="#res:massscalar" data-reference-type="ref" data-reference="res:massscalar">12</a> exclude the two finiteness conditions. ◻

</div>

<div id="res:lcmheight" class="problem">

**Problem 18** (global overlap-height growth). For every nonterminal canonical orbit satisfying Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">3</a>, must
``` math
\limsup_{n\to\infty}\frac{\log M_n}{n}>0?
```
Equivalently, must there be a $`K\ge1`$ for which
``` math
2^n\le M_n^K
```
at infinitely many indices?

</div>

The necessary profile is proved above and is formalised as [the canonical frontier theorem](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos243/PaperCompleteR7/Frontier.lean#L151). The formal statement assumes the rational reciprocal sum, the quadratic growth limit and failure of eventual Sylvester behaviour; the last hypothesis is essential to all of its nontermination conclusions.

For $`B\ge0`$ put
``` math
F_B(X)=\sum_{\substack{n\in\mathcal R\\U_n\le X}}(-V_n-B)_+.
```
The remaining equivalent estimate is
``` math
\begin{equation}
\label{eq:remaining-record-budget}
 \exists B\in\mathbb{N}:\qquad\liminf_{X\to\infty}\frac{F_B(X)}X=0.
\end{equation}
```
On a nonterminal orbit first crossings instead give $`F_B(X)\ge X/P_B-O_B(1)`$, with an orbit-dependent CRT modulus $`P_B`$. Charges are grouped by their source height $`U_n`$, not by their record height $`R_n`$ or by their time index. Every fixed height has only finitely many late sources because $`U_n\to\infty`$. The missing step is to derive <a href="#eq:remaining-record-budget" data-reference-type="eqref" data-reference="eq:remaining-record-budget">[eq:remaining-record-budget]</a> from the canonical dynamics. Its equivalence with the existence of an admissible weight is the following elementary lemma, applied to the record charges $`u_j=U_n`$ and $`w_j=(-V_n-B)_+`$ over $`n\in\mathcal R`$ at a fixed $`B`$.

<div id="res:weights" class="lemma">

**Lemma 19** (weights and linear density). *Let $`u_j`$ be positive integers, let $`w_j\ge0`$, and put $`F(X)=\sum_{u_j\le X}w_j`$, with the sum allowed a priori to be $`+\infty`$. Then $`\liminf_{X\to\infty}F(X)/X=0`$ if and only if there is a finite nonincreasing $`f:[1,\infty)\to[0,\infty)`$ with $`\int_1^\infty f(t)\,dt=\infty`$ and $`\sum_jw_jf(u_j)<\infty`$.*

</div>

<div class="proof">

*Proof.* Suppose the lower limit vanishes. Since $`F`$ is constant on each $`[m,m+1)`$, there are integers $`X_1<X_2<\cdots`$ with $`X_k\ge2^{k}`$ and $`F(X_k)\le2^{-k}X_k`$. Put $`f=\sum_{k\ge1}X_k^{-1}\mathbf 1_{[1,X_k]}`$, which is nonincreasing and bounded by $`\sum_k2^{-k}`$. Then $`\int_1^\infty f=\sum_k(1-1/X_k)=\infty`$, while interchanging the nonnegative sums gives $`\sum_jw_jf(u_j)=\sum_kF(X_k)/X_k\le1`$.

Conversely, let $`f`$ be such a weight and suppose $`F(m)\ge cm`$ for some $`c>0`$ and all integers $`m\ge M`$. A nonincreasing nonnegative function with divergent integral is positive everywhere, so $`F(X)\le f(X)^{-1}\sum_jw_jf(u_j)`$ is finite. Partial summation gives, for $`N>M`$,
``` math
\sum_{u_j\le N}w_jf(u_j)
 =F(N)f(N)+\sum_{m=1}^{N-1}F(m)\bigl(f(m)-f(m+1)\bigr)
 \ge c\Bigl(Mf(M)+\sum_{m=M+1}^{N}f(m)\Bigr),
```
every term being nonnegative. The right side diverges as $`N\to\infty`$, because $`\sum_{m\ge1}f(m)\ge\int_1^\infty f(t)\,dt=\infty`$. ◻

</div>

The lemma converts the weighted criterion into the displayed density condition; supplying <a href="#eq:remaining-record-budget" data-reference-type="eqref" data-reference="eq:remaining-record-budget">[eq:remaining-record-budget]</a> for a canonical orbit remains open.

The obstruction is the exact unit-numerator feedback at the record sources. The scalar sequence $`C_n=n^2+1`$, $`E_n=-(2n+1)`$ has normalised vanishing, subexponential height and finite square mass, but is not an exact reciprocal-tail orbit: its numerator word $`0,0,2\pmod5`$ violates the persistent-zero transport of the exact equations. Likewise, small rises and avoidance of an arbitrary sparse coprime family do not control the canonical timing and size of the available divisors. The supporting record keeps those falsifying examples with the exact hypotheses each preserves. In particular, compatibility modulo one fixed old denominator does not control later prime arrivals. The companion paper proves that arbitrary finite words of units satisfy the reduced recurrence modulo that old denominator, while separately deriving a large odd-prime-power supply from the canonical growth. Neither fact alone supplies the missing record budget.

<a id="formal-scope-and-supporting-record."></a>

#### Formal scope and supporting record.

At revision `3d6d938d696f`, the supplied build receipt covers the bounded-negative state theorem, its original-coordinate product- and LCM-defect consequences, the scalar finite-mass theorem and the canonical frontier theorem. A proof of a state implication is not, by itself, a proof of its analytic premises; the canonical transfer is supplied in the separate `PaperCompleteR7` modules cited above. The complete weighted criterion has a proof source in the separate release, outside this main-repository build. The cubic argument has formalised extraction, normalisation and finite transport components, but no assembled declaration of the irrationality theorem is identified here. The slow-negative results likewise distinguish the checked arithmetic lemmas from the ordinary growth argument. The accompanying reasoning record retains those distinctions, the finite certificates and the unsuccessful extensions. No finite computation is used as a substitute for a universal argument. The supply, valuation and energy proofs added to the companion paper in this revision are ordinary proofs; no new Lean replay is asserted. For older formal work on integer remainders, see the Isabelle/HOL development of Koutsoukou-Argyraki and Li \[kouli2020\]; its endpoint is not Problem #243.

The authorship and AI-use statement on the first page applies to this manuscript. Code and mathematical source are available at the repository checkpoint `3d6d938d696f`. A declaration establishes only its own statement with its stated hypotheses. The finite upper bound and the global record estimate remain additional mathematical obligations, not consequences of a successful build.

<a id="app:index"></a>

# Guide to the formal sources

Each linked phrase opens its declaration at the stated immutable revision. The default checkpoint is `3d6d938d696f`; separate-release and older research-note links are explicitly identified by their destinations. `ReciprocalTailRigidity.lean` contains the state dynamics and arithmetic exclusions; `SparseResetRecovery.lean` contains the scalar finite-mass criterion; and `PaperCompleteR7` supplies the original-coordinate product-defect, LCM-defect and canonical-frontier theorems. Thus the identification with reciprocal tails is not merely an informal interpretation. The periodic exclusion still assumes $`e_n<a_n`$. The state theorem still lists strict centring and normalised vanishing, with the former following from the latter by taking $`K=1`$. Neither fact removes the additional bounded-negative hypothesis. Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">4</a> gives the ordinary analytic proof so the reader need not inspect source code to follow the argument.

<a id="app:residue"></a>

# A factorial residue reduction for forced orbits

A constant-negative error $`E_n=-m`$ with $`C_0=c`$ produces $`C_n=c+nm`$ and the shape equation
``` math
\begin{equation}
\label{eq:shape}
 D_n+m=(a_n-1)C_n.
\end{equation}
```
In the case $`m=c=1`$, where <a href="#eq:shape" data-reference-type="eqref" data-reference="eq:shape">[eq:shape]</a> reads $`D_n+1=(a_n-1)(n+1)`$, each multiplier is determined by its predecessor; we call such an orbit *forced*. At index $`n`$ the numerator of the next multiplier is
``` math
\operatorname{num}(n,a)=(n+1)a^{2}-(n+2)a+(n+3),
```
the [forced numerator](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L22), and the divisor is $`n+2`$. The orbit survives a step when that division is exact, giving a survival predicate, the [survival predicate](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L75).

<div id="ex:shape" class="example">

**Example 20** (the shape equation running until it fails). The forced orbit from $`a=3`$ reads this way: $`\operatorname{num}(0,3)=6`$ is divisible by $`2`$ and gives $`a_1=3`$, while $`\operatorname{num}(1,3)=13`$ is not divisible by $`3`$, so the orbit stops there.

</div>

Deciding survival by iteration is expensive because the orbit grows doubly exponentially, and it is unnecessary: survival over a finite horizon depends on the initial value only through a factorial residue. Computing a pseudo-greedy orbit through residues modulo a shrinking product modulus is Koizumi’s method \[koizumi2025, Remark 2 and Algorithm 1, pp. 13–14\]; for the forced numerator that product is a factorial.

<div id="res:residue" class="theorem">

**Theorem 21** (factorial residue reduction). *For all $`h`$ and all integers $`a\equiv b \pmod{(h+1)!}`$, the orbit from $`a`$ survives $`h`$ forced updates exactly when the orbit from $`b`$ does.*

</div>

<div class="proof">

*Proof.* Let $`M(0,i)=1`$ and $`M(h+1,i)=(i+2)M(h,i+1)`$, an ascending factorial with $`M(h,0)=(h+1)!`$. The numerator is a polynomial with integer coefficients, so congruences transfer; reducing the modulus gives divisibility by $`i+2`$ for one exactly when for the other, and cancelling that common factor from both values and modulus leaves the inductive hypothesis at $`M(h,i+1)`$. ◻

</div>

Formalised as the [factorial residue reduction](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L134), over the [shrinking-modulus transport](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L97), the [polynomial congruence](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L26), and the [exact-division cancellation](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L41); the modulus identifications are the [ascending-factorial form](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L59) and the [factorial value at the initial index](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L69).

At $`h=1`$ the modulus is $`2!=2`$, and surviving one update means $`2\mid a^{2}-2a+3`$, which holds exactly for odd $`a`$: for instance $`\operatorname{num}(0,3)=6`$ but $`\operatorname{num}(0,4)=11`$. So one step of survival is decided by the parity of $`a`$ alone, which is Theorem <a href="#res:residue" data-reference-type="ref" data-reference="res:residue">21</a> at its smallest nontrivial horizon.

The inherited search record reports a maximum forced-prefix length of $`17`$ among initial states below $`5000`$. This finite search was not rerun for the present revision and is not a proof of exclusion; the Lean-checked [constant exclusion at every scale](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L286) now excludes the constant-negative case outright, for every seed and at every scale. The reduction is retained because it is exact, and because the shrinking-modulus technique transfers to any forced orbit whose step is a polynomial division.

<div class="thebibliography">

99

P. Erdős and E. G. Straus, [*On the irrationality of certain Ahmes series*](https://users.renyi.hu/~p_erdos/1964-19.pdf), J. Indian Math. Soc. (N.S.) **27** (1964), 129–133. MR 175848. D. Duverney, [*Irrationality of fast converging series of rational numbers*](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf), J. Math. Sci. Univ. Tokyo **8** (2001), 275–316. MR 1837165. C. Badea, [*A theorem on irrationality of infinite series and applications*](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf), Acta Arith. **63** (1993), no. 4, 313–323, doi:[10.4064/aa-63-4-313-323](https://doi.org/10.4064/aa-63-4-313-323). R. Tijdeman and P. Yuan, *On the rationality of Cantor and Ahmes series*, Indag. Math. (N.S.) **13** (2002), no. 3, 407–418, doi:[10.1016/S0019-3577(02)80018-0](https://doi.org/10.1016/S0019-3577(02)80018-0). P. Erdős and R. L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf), Monogr. Enseign. Math. 28, Geneva, 1980, p. 64. P. Erdős, [*On the irrationality of certain series: problems and results*](https://users.renyi.hu/~p_erdos/1988-22.pdf), in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). I. O. Bado, *Prime-Support Rigidity and Primitive Pseudo-Greedy Dynamics: Partial Progress on Erdős Problem #243*, preprint posted September 2026, doi:[10.13140/RG.2.2.36612.08325](https://doi.org/10.13140/RG.2.2.36612.08325). P. White with Claude (Anthropic), [*Erdős \#243: working report*](https://erdosproblemaday.com/report/243), Erdős Problem a Day, page dated 12 August 2026. AI-assisted, unrefereed working report. P. Stevenhagen and H. W. Lenstra, Jr., [*Chebotarëv and his density theorem*](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1994c/art.pdf), Math. Intelligencer **18** (1996), no. 2, 26–37, doi:[10.1007/BF03027290](https://doi.org/10.1007/BF03027290). Page references are to the linked author version dated 23 March 1995. J. Koizumi, [*Irrationality of the reciprocal sum of doubly exponential sequences*](https://math.colgate.edu/~integers/aa28/aa28.pdf), Integers **26** (2026), Paper No. A28, 17 pp., doi:[10.5281/zenodo.18714404](https://doi.org/10.5281/zenodo.18714404). Locators refer to this published version. T. F. Bloom, [*Erdős Problem \#243*](https://www.erdosproblems.com/243), supplied snapshot of 28 July 2026; not a live status verification. P. Erdős and E. G. Straus, [*On the irrationality of certain series*](https://msp.org/pjm/1974/55-1/pjm-v55-n1-p08-s.pdf), Pacific J. Math. **55** (1974), no. 1, 85–92. J. Hančl and R. Tijdeman, [*On the irrationality of polynomial Cantor series*](https://www.impan.pl/shop/en/publication/transaction/download/product/82186), Acta Arith. **133** (2008), no. 1, 37–52, doi:[10.4064/aa133-1-3](https://doi.org/10.4064/aa133-1-3). Locators refer to the published version. D. Duverney, T. Kurosawa and I. Shiokawa, [*Irrationality exponents of certain fast converging series of rational numbers*](https://danielduverney.fr/documents/theorie-des-nombres/Tsukuba.pdf), Tsukuba J. Math. **44** (2020), no. 2, 235–250, doi:[10.21099/tkbjm/20204402235](https://doi.org/10.21099/tkbjm/20204402235). Theorem locators follow the linked 14-page author version. T. Crmarić and V. Kovač, [*On the irrationality of certain super-polynomially decaying series*](https://arxiv.org/abs/2504.18712v1), Colloq. Math. **179** (2025), 55–68, doi:[10.4064/cm9628-5-2025](https://doi.org/10.4064/cm9628-5-2025). Theorem locators follow arXiv:2504.18712v1. A. Koutsoukou-Argyraki and W. Li, [*Irrationality Criteria for Series by Erdős and Straus*](https://isa-afp.org/entries/Irrational_Series_Erdos_Straus.html), Archive of Formal Proofs, 12 May 2020. An Isabelle/HOL formalisation; the archive entry identifies the results formalised. National Institute of Standards and Technology, [*Digital Library of Mathematical Functions*, §5.11(iii), formula 5.11.12](https://dlmf.nist.gov/5.11.E12), accessed 16 September 2026.

</div>

*Companion system context.* The [claim and trust boundary](../../../paper/systems/claim-faithful-publication-systems-paper.pdf#nameddest=systems-trust), [cold-clone route to proof authority](../../../paper/systems/cold-clone-to-proof-receipt.pdf#nameddest=cold-clone-authority), and [public contribution protocol](../../../paper/systems/open-source-mathematics-strategy.pdf#nameddest=strategy-protocol) are described in sibling papers. Those descriptions do not change the mathematical status of this note.
