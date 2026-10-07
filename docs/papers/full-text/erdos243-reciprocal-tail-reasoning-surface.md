<a id="erdos243-reciprocal-tail-reasoning-surface"></a>

# Reciprocal Sums and the Sylvester Recurrence: Further Results and Proofs

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We study rational reciprocal sums with $`a_{n+1}/a_n^2\to1`$. Integer finite differences exclude nonintegral regular rates and reduce the cubic rate to a polynomial. A square condition in the cubic field and congruences modulo seven then prove irrationality. For general rational tails, we derive Sylvester recurrence criteria from persistent divisors, bounded numerator increases and weighted crossings of new maxima. We describe the arithmetic estimates still needed for Erdős Problem #243.

<a id="long243:sec:problem"></a>

# Introduction

Sylvester’s sequence $`2,3,7,43,1807,\ldots`$ has reciprocal sum $`1`$. Its recurrence $`a_n=a_{n-1}^2-a_{n-1}+1`$ gives the telescoping identity
``` math
\frac1{a_{n-1}-1}=\frac1{a_{n-1}}+\frac1{a_n-1}.
```
The tail beginning with $`1/a_{n-1}`$ therefore equals $`1/(a_{n-1}-1)`$. Erdős Problem #243 asks whether every rational reciprocal sum with $`a_n\sim a_{n-1}^2`$ must eventually have this form:

<div id="long243:res:problem" class="problem">

**Problem 1** (Erdős \#243). Let $`1\le a_1<a_2<\cdots`$ be a sequence of integers with
``` math
\lim_{n\to\infty}\frac{a_n}{a_{n-1}^{2}}=1
 \qquad\text{and}\qquad
 \sum\frac{1}{a_n}\in\mathbb{Q}.
```
Then $`a_n=a_{n-1}^{2}-a_{n-1}+1`$ for all sufficiently large $`n`$.

</div>

See \[erdosgraham1980, p. 64\] and \[erdos1988, p. 105\]. Bloom’s catalogue, accessed 28 July 2026, lists the problem as open \[erdosproblems\]. Below we index the same recurrence as $`a_{n+1}=a_n^{2}-a_n+1`$, which is the shift the formal sources use; the two forms are the same statement. The polynomial $`a^2-a+1`$ is called the [Sylvester successor](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L37).

Clearing a rational reciprocal tail gives positive integers $`C_n,D_n`$ with $`C_{n+1}=a_nC_n-D_n`$ and $`D_{n+1}=a_nD_n`$. The first update can also be written $`C_{n+1}=C_n-E_n`$, where $`E_n=D_n-(a_n-1)C_n`$. Quadratic growth makes $`E_n/C_n\to0`$. The eventual Sylvester recurrence follows once the integer error itself vanishes.

There are two ways to use this integer numerator. At a precise regular rate it grows, but a high finite difference tends to zero and must vanish. The resulting polynomial is then tested against the denominator recurrence. With bounded upward steps, a different argument applies: a stable common divisor gives reduced tails, whose numerators avoid every earlier multiplier. The Chinese remainder theorem produces a block that bounded rises cannot cross, regardless of intervening decreases. Neither argument replaces the denominator recurrence by a scalar growth estimate.

Section <a href="#long243:sec:cubicrate" data-reference-type="ref" data-reference="long243:sec:cubicrate">2</a> proves cubic and nonintegral-rate irrationality: these rates exclude the eventual Sylvester recurrence. The general question remains open. After the literature comparison in Section <a href="#long243:sec:priorwork" data-reference-type="ref" data-reference="long243:sec:priorwork">3</a>, Sections <a href="#long243:sec:state" data-reference-type="ref" data-reference="long243:sec:state">4</a>–<a href="#long243:sec:defect" data-reference-type="ref" data-reference="long243:sec:defect">5</a> develop integer tails and zero-error identities for the subsequent criteria.

The later criteria use two distinct normalisations. Section <a href="#long243:sec:lcmrecords" data-reference-type="ref" data-reference="long243:sec:lcmrecords">6</a> clears tails with an LCM: common numerator factors remain, so congruences forbid short crossings rather than numerator values. Section <a href="#long243:sec:records" data-reference-type="ref" data-reference="long243:sec:records">7</a> reduces to lowest terms, where cancellation can remove a prime that persists in the LCM. That argument must track the prime powers which survive. Sections <a href="#long243:sec:constant" data-reference-type="ref" data-reference="long243:sec:constant">9</a>–<a href="#long243:sec:periodic" data-reference-type="ref" data-reference="long243:sec:periodic">10</a> treat constant and periodic errors; Sections <a href="#long243:sec:barrier" data-reference-type="ref" data-reference="long243:sec:barrier">11</a>–<a href="#long243:sec:bounded" data-reference-type="ref" data-reference="long243:sec:bounded">12</a> prove the bounded-increase criterion, and Section <a href="#long243:sec:mass" data-reference-type="ref" data-reference="long243:sec:mass">13</a> treats scalar summability. Section <a href="#long243:sec:open" data-reference-type="ref" data-reference="long243:sec:open">14</a> separates open estimates from countermodels to weakened hypotheses. The appendices give formal sources, the finite residue calculation and a result map.

We use $`z_+=\max(z,0)`$. Deleting a finite prefix is harmless for an eventual recurrence, but not for the coefficients in a higher-order rate. In particular, the index $`n`$ in $`1+3/n+o(n^{-3})`$ is kept fixed throughout the cubic proof. The recurrence sections also use zero-based indexing, with that convention stated where the integer sequences are introduced.

**Keywords.** irrationality; Ahmes series; Sylvester’s sequence; unit fractions; Lean 4. **MSC 2020.** 11J72 (primary); 11B37, 11D68, 68V20 (secondary).

<div id="243-long-cubic">

</div>

<a id="long243:sec:cubicrate"></a>

# Irrationality at the cubic rate

A sufficiently precise rate constrains an integer tail more strongly than the quadratic limit alone. At rate $`1+3/n+o(n^{-3})`$, its numerator must eventually be cubic. The denominator recurrence will exclude every possible cubic. For the prefix product $`P_n=\prod_{1\le k<n}a_k`$, the increments of $`P_n/a_n`$ grow like a positive multiple of $`n^2`$, so the bounded-increase criterion later in the paper does not apply. The eventual Sylvester recurrence gives deviation $`O(1/a_n)`$ and is also excluded by this rate.

<div id="long243:res:cubicrate" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L70">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-cubicrate-comparator">Comparator</a></p>

**Theorem 2** (cubic-rate irrationality). *If strictly increasing positive integers satisfy $`a_n^2/a_{n+1}=1+3/n+o(n^{-3})`$, then $`\sum_n1/a_n`$ is irrational.*

</div>

The same extraction argument rules out nonintegral regular rates above one. These require no number-field calculation.

<div id="long243:res:nonintegralrate" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/NonintegralRegularRate.lean#L196">Lean</a></p>

**Theorem 3** (nonintegral regular-rate irrationality). *Let $`\lambda>1`$ be a real number that is not an integer. If strictly increasing positive integers satisfy $`a_n^2/a_{n+1}=1+\lambda/n+o(n^{-\lambda})`$, then $`\sum_n1/a_n`$ is irrational.*

</div>

The [zero-indexed Lean theorem](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/NonintegralRegularRate.lean#L196) also derives convergence of the reciprocal series from the rate.

The rates retain their stated indices throughout. Appendix <a href="#long243:app:index" data-reference-type="ref" data-reference="long243:app:index">15</a> gives the finite-prefix construction relating these one-based statements to the zero-based formal statements without changing the rate’s error term.

For a concrete sequence satisfying the hypothesis, take
``` math
a_1=8,\qquad a_{n+1}=\left\lceil\frac{n a_n^2}{n+3}\right\rceil
 \quad(n\ge1).
```
It begins $`8,16,103,5305,\ldots`$. The inequality $`a_{n+1}\ge a_n^2/4`$ gives $`a_n\ge4\cdot2^{2^{n-1}}\ge8`$ by induction. Hence $`a_{n+1}\ge a_n^2/4\ge2a_n`$, so the sequence is strictly increasing. Rounding upwards gives
``` math
0\le1+\frac3n-\frac{a_n^2}{a_{n+1}}<\frac{16}{a_n^2}=o(n^{-3}).
```
Thus its reciprocal sum is irrational. Lemma <a href="#long243:res:extraction" data-reference-type="ref" data-reference="long243:res:extraction">12</a> will turn the rate assumption into an eventual rising-factorial cubic for the integer tail numerator. We first prove the arithmetic obstruction that rules out this cubic using only the exact integer recurrences.

<div id="long243:res:cubicexclusion" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L54">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-cubicexclusion-comparator">Comparator</a></p>

**Theorem 4** (rising-factorial cubic exclusion). *Let $`a,C,D:\mathbb{N}\to\mathbb{Z}_{>0}`$ satisfy
``` math
\begin{equation}
\label{long243:eq:cubicorbit}
 C_{n+1}=a_nC_n-D_n,\qquad D_{n+1}=a_nD_n .
\end{equation}
```
Then for every $`A\in\mathbb{Q}_{>0}`$ and every $`B\in\mathbb{Q}`$,
``` math
\liminf_{X\to\infty}
 \frac{\#\{n\le X:C_n\ne A\,n(n+1)(n+2)+B\}}{X}>0 .
```
In particular no such orbit satisfies $`C_n=A\,n(n+1)(n+2)+B`$ for all large $`n`$.*

</div>

The short paper needs only to exclude eventual equality with a cubic of this form. Here we prove more: the disagreement set has positive lower density. The bound may depend on the orbit and the cubic; no uniform numerical constant is claimed.

Lower density zero does not give eventual agreement, but leaves arbitrarily late intact four-term blocks. Their third differences bound $`G_n=\gcd(C_n,D_n)`$, stabilising the divisibility chain. Dividing out its limit leaves $`m n(n+1)(n+2)/6+c`$, with $`m>0`$ integral and $`c=\pm1`$. A vanishing middle numerator modulo a prime forces the negative product of its neighbours to be a square. This condition at every root modulo almost every prime yields a square in the cubic field; traces give $`m=12`$, and four-term blocks modulo seven exclude both signs.

The density assertion comes from the same finite tests. A failed test recurs on an arithmetic progression, and each occurrence forces a disagreement in a window of bounded length. The next lemma counts those disagreements. After proving the arithmetic exclusion, we return to the rate assumption in Lemma <a href="#long243:res:extraction" data-reference-type="ref" data-reference="long243:res:extraction">12</a>.

<a id="the-integer-tail-numerator."></a>

#### The integer tail numerator.

Suppose $`\sum_{n\ge1}1/a_n=p/q`$ with positive integers $`p,q`$, and write $`x_n=\sum_{k\ge n}1/a_k`$ for the tail. Put
``` math
D_n=q\prod_{1\le k<n}a_k,\qquad C_n=D_nx_n .
```
Then $`D_n`$ is a positive integer, and
``` math
C_n=D_n\Bigl(\frac pq-\sum_{1\le k<n}\frac1{a_k}\Bigr)
    =p\prod_{1\le k<n}a_k-q\sum_{1\le k<n}\ \prod_{\substack{1\le j<n\\ j\ne k}}a_j
```
is a positive integer as well. From $`x_n=1/a_n+x_{n+1}`$,
``` math
C_{n+1}=D_{n+1}x_{n+1}=a_nD_n\Bigl(x_n-\frac1{a_n}\Bigr)=a_nC_n-D_n,
 \qquad D_{n+1}=a_nD_n,
```
which is <a href="#long243:eq:cubicorbit" data-reference-type="eqref" data-reference="long243:eq:cubicorbit">[long243:eq:cubicorbit]</a>. These are the unreduced tail variables of Koizumi’s Lemma 4 \[koizumi2025, pp. 11–12\], up to a common positive factor. Lemma <a href="#long243:res:tailratio" data-reference-type="ref" data-reference="long243:res:tailratio">13</a> uses this unreduced numerator: reducing each tail separately would introduce varying cancellation factors into the ratio and obscure the prescribed rate. Section <a href="#long243:sec:state" data-reference-type="ref" data-reference="long243:sec:state">4</a> constructs these variables together with the error $`E_n=D_n-(a_n-1)C_n`$, which this section does not need. The subsequent cubic exclusion uses only these integer recurrences; it does not assume a reciprocal sum. To apply its zero-based statement without shifting the rate hypothesis, adjoin $`a_0=1`$, $`D_0=q`$ and $`C_0=p+q`$. The recurrences at $`0`$ then give $`D_1=q`$ and $`C_1=p`$, while every original index $`n\ge1`$ is unchanged. The auxiliary term $`a_0`$ need not satisfy the increasing-sequence hypothesis of the irrationality theorem: the exclusion requires only positive multipliers.

<a id="reduction-and-lower-density"></a>

## Reduction and lower density

For $`S\subseteq\mathbb{N}`$ write $`\underline d(S)=\liminf_X\#(S\cap[1,X])/X`$. Thus $`\underline d(S)=0`$ gives cutoffs along which the exceptional proportion tends to zero, not eventual agreement. We cannot replace $`C_n`$ by its proposed polynomial at arbitrary indices; the following lemma supplies the finite windows where such a replacement is valid. For a sequence $`F`$, let $`\Delta F_n=F_{n+1}-F_n`$; higher powers of $`\Delta`$ mean repeated forward differences. This operator is distinct from the later indexed quantity $`\Delta_n`$, the Sylvester defect.

<div id="long243:res:periodicobstruction" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR11/DensityTransport.lean#L156">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-periodicobstruction-comparator">Comparator</a></p>

**Lemma 5** (periodic obstruction principle). *Let $`h,L`$ be positive integers and let $`j_1,\ldots,j_L`$ be fixed integer offsets. Suppose that for every sufficiently large $`n`$ in one residue class modulo $`h`$ at least one of $`n+j_1,\ldots,n+j_L`$ lies in $`S`$. Then $`\underline d(S)\ge1/(Lh)`$.*

</div>

<div class="proof">

*Proof.* There are $`X/h+O(1)`$ relevant starting indices below $`X`$. Their witnesses lie below $`X+O(1)`$ because the offsets are fixed, and each element of $`S`$ serves as a witness for at most $`L`$ starting indices. Hence $`L\#(S\cap[1,X])\ge X/h-O(1)`$, which gives the claimed lower density. ◻

</div>

Fix $`A\in\mathbb{Q}_{>0}`$, $`B\in\mathbb{Q}`$, and suppose for contradiction that
``` math
P(n)=A\,n(n+1)(n+2)+B,
 \qquad S=\{n:C_n\ne P(n)\},
 \qquad \underline d(S)=0 .
```
We retain this assumption through Section <a href="#long243:sec:modseven" data-reference-type="ref" data-reference="long243:sec:modseven">2.4</a>.

<div id="long243:res:gcdshape" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/CubicProfileGcdShape.lean#L103">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-gcdshape-comparator">Comparator</a></p>

**Lemma 6** (gcd stabilisation and the reduced polynomial). *Write $`G_n=\gcd(C_n,D_n)`$. Then $`6A`$ is a positive integer, $`G_n`$ divides $`6A`$ for every $`n`$, and $`G_n`$ is eventually equal to a positive integer $`g`$. On the tail where $`G_n=g`$, put $`u_n=C_n/g`$, $`v_n=D_n/g`$ and $`Q(n)=P(n)/g`$. Then
``` math
\begin{equation}
\label{long243:eq:primitivetail}
 u_{n+1}=a_nu_n-v_n,\qquad v_{n+1}=a_nv_n,\qquad \gcd(u_n,v_n)=1,
 \qquad\gcd(u_n,u_{n+1})=1,
\end{equation}
```
and there are $`m\in\mathbb{Z}_{>0}`$ and $`c\in\{-1,1\}`$ with
``` math
\begin{equation}
\label{long243:eq:Qmc}
 Q(n)=\frac m6n(n+1)(n+2)+c .
\end{equation}
```*

</div>

<div class="proof">

*Proof.* Equation <a href="#long243:eq:cubicorbit" data-reference-type="eqref" data-reference="long243:eq:cubicorbit">[long243:eq:cubicorbit]</a> gives $`G_n\mid G_{n+1}`$ and $`G_n\mid C_t`$ for every $`t\ge n`$. Since $`\underline d(S)=0`$, beyond every threshold there is a block of four consecutive indices disjoint from $`S`$: otherwise every block of four would meet $`S`$ and $`\underline d(S)\ge1/4`$. On such a block $`\Delta^3C_t=\Delta^3P(t)=6A`$, and $`G_n`$ divides each of the four values, hence divides $`6A`$. So $`6A`$ is a positive integer and the divisibility chain $`(G_n)`$ is bounded and stabilises at some $`g`$.

On the primitive tail, $`\gcd(u_n,v_n)=1`$ by construction, and a prime dividing $`u_n`$ and $`u_{n+1}`$ would divide $`v_n=a_nu_n-u_{n+1}`$, which gives $`\gcd(u_n,u_{n+1})=1`$.

Since $`g\mid6A`$, the number $`m:=6A/g`$ is a positive integer. Put $`c=B/g`$, so
``` math
Q(n)=m\binom{n+2}{3}+c.
```
Choose any sufficiently late $`n\notin S`$. Then $`Q(n)=u_n\in\mathbb{Z}`$, and the binomial term is an integer, so $`c\in\mathbb{Z}`$. This proves <a href="#long243:eq:Qmc" data-reference-type="eqref" data-reference="long243:eq:Qmc">[long243:eq:Qmc]</a> with $`c\in\mathbb{Z}`$. It also shows that $`Q`$ is integer-valued: its values at integer arguments are integers, even though its coefficients need not all be integers.

It remains to exclude $`c=0`$ and every $`c`$ with a prime factor. Let $`\ell`$ be a prime dividing $`c`$, or any prime if $`c=0`$. For $`n\equiv-1\pmod{6\ell}`$, write $`n+1=6\ell k`$; then
``` math
\frac{n(n+1)(n+2)}6=\ell k(6\ell k-1)(6\ell k+1),
 \qquad
 \frac{(n+1)(n+2)(n+3)}6=\ell k(n+2)(n+3),
```
so $`\ell`$ divides both $`Q(n)`$ and $`Q(n+1)`$. Agreement at both indices would give $`\ell\mid\gcd(u_n,u_{n+1})=1`$. Hence one of $`n,n+1`$ lies in $`S`$ for every late $`n\equiv-1\pmod{6\ell}`$, and Lemma <a href="#long243:res:periodicobstruction" data-reference-type="ref" data-reference="long243:res:periodicobstruction">5</a> with $`L=2`$, $`h=6\ell`$ gives $`\underline d(S)\ge1/(12\ell)`$. This contradiction leaves $`c=\pm1`$. ◻

</div>

<div id="long243:res:reduciblecase" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR11/PrimitiveMultiplierSupply.lean#L244">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-reduciblecase-comparator">Comparator</a></p>

**Lemma 7** (coprimality and irreducibility). *On the primitive tail, $`\gcd(a_n,v_n)=1`$, the multipliers at distinct indices are pairwise coprime, infinitely many of them exceed $`1`$, and the cubic $`Q_{m,c}`$ of <a href="#long243:eq:Qmc" data-reference-type="eqref" data-reference="long243:eq:Qmc">[long243:eq:Qmc]</a> is irreducible over $`\mathbb{Q}`$.*

</div>

<div class="proof">

*Proof.* A prime dividing $`a_n`$ and $`v_n`$ would divide $`u_{n+1}`$ and $`v_{n+1}`$, against $`\gcd(u_{n+1},v_{n+1})=1`$; and every earlier multiplier divides every later $`v_n`$, so distinct multipliers are coprime. If $`a_n=1`$ for all large $`n`$ then $`v_n`$ is eventually a positive constant and $`u_{n+1}=u_n-v_n`$ decreases without bound, against positivity. So infinitely many distinct primes divide late multipliers.

Suppose $`Q_{m,c}`$ had a rational root. Choose a prime $`\ell\nmid6m`$ dividing a late multiplier $`a_N`$, large enough that the root reduces modulo $`\ell`$. Then $`Q_{m,c}`$ vanishes modulo $`\ell`$ on a full residue class, while $`\ell\mid v_n`$ and therefore $`\ell\nmid u_n`$ for every $`n>N`$. Agreement at any late index of that class is impossible, and Lemma <a href="#long243:res:periodicobstruction" data-reference-type="ref" data-reference="long243:res:periodicobstruction">5</a> with $`L=1`$, $`h=\ell`$ gives $`\underline d(S)\ge1/\ell`$. ◻

</div>

<a id="square-specialisation"></a>

## Square specialisation

For the proposed cubic $`f(T)=T^3-T+6c/m`$, the recurrence will force $`r^2-1`$ to be a square whenever $`r`$ is a root modulo a good prime. We need the same conclusion for an algebraic root $`\alpha`$ in $`\mathbb{Q}(\alpha)`$. The issue is that a putative square root could lie in a quadratic extension of this field. Its nontrivial automorphism would fix $`\alpha`$ and change the sign of the square root. Chebotarev supplies a prime with exactly that behaviour, contradicting the finite-field condition. The following lemma isolates this passage; in the cubic application we take $`H(T)=T^2-1`$.

<div id="long243:res:squarespec" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-squarespec">Lean</a></p>

**Lemma 8** (square specialisation). *Let $`f\in\mathbb{Q}[T]`$ be irreducible with root $`\alpha`$, and let $`H\in\mathbb{Q}[T]`$ satisfy $`H(\alpha)\ne0`$. If for all but finitely many primes $`\ell`$ every root $`r\in\mathbb{F}_\ell`$ of the reduction of $`f`$ has $`H(r)`$ a square in $`\mathbb{F}_\ell^\times`$, then $`H(\alpha)`$ is a square in $`\mathbb{Q}(\alpha)^\times`$.*

</div>

<div class="proof">

*Proof.* Suppose that $`H(\alpha)`$ is a nonsquare in $`K=\mathbb{Q}(\alpha)`$, and choose $`\beta`$ with $`\beta^2=H(\alpha)`$. The nontrivial automorphism of the quadratic extension $`K(\beta)/K`$ extends to an element $`\sigma\in\mathop{\mathrm{Gal}}(L/K)`$ for a finite Galois extension $`L/\mathbb{Q}`$ containing $`K(\beta)`$. In particular $`\sigma\alpha=\alpha`$ and $`\sigma\beta=-\beta`$.

By Chebotarev’s density theorem in the form stated by Stevenhagen and Lenstra \[stevenhagenlenstra1996, §3, p. 15\], infinitely many unramified rational primes have Frobenius conjugate to $`\sigma`$. Only infinitude is needed. We discard the exceptional primes in the hypothesis and the finitely many primes at which coefficients, $`\alpha`$ or $`\beta`$ have denominators, together with $`2`$ and the primes at which $`\beta`$ reduces to zero. Above each remaining prime $`\ell`$, choose a prime of $`L`$ whose Frobenius is $`\sigma`$. Its residue field then satisfies
``` math
\overline\alpha^{\,\ell}=\overline\alpha,\qquad
 \overline\beta^{\,\ell}=-\overline\beta\ne\overline\beta.
```
Thus $`\overline\alpha\in\mathbb{F}_\ell`$ is a root of the reduction of $`f`$. Neither of the two roots $`\pm\overline\beta`$ of $`X^2-H(\overline\alpha)`$ is fixed by Frobenius, so neither belongs to $`\mathbb{F}_\ell`$. Hence $`H(\overline\alpha)`$ is a nonsquare there, contradicting the hypothesis. ◻

</div>

An alternative proof of Lemma <a href="#long243:res:squarespec" data-reference-type="ref" data-reference="long243:res:squarespec">8</a> uses zeta functions. A nonsquare algebraic integer $`b`$ in a number field $`K`$ is nonsquare modulo infinitely many degree-one primes of $`K`$. The underlying zeta-function argument first gives zero or a nonsquare. The zero case is excluded beyond the prime divisors of the nonzero constant coefficient of the minimal polynomial of $`b`$. If $`H(\alpha)`$ is not a square in $`K=\mathbb{Q}(\alpha)`$, this applies to $`b=m^2H(\alpha)`$, where the nonzero integer $`m`$ makes $`b`$ an algebraic integer, and the residue map at such a prime, of norm $`\ell`$, sends $`\alpha`$ to a root $`r\in\mathbb{F}_\ell`$ of the reduction of $`f`$ at which $`H(r)`$ is a nonsquare. The prime-reduction argument ([nonsquares modulo primes](https://github.com/wcook04/plectis-erdos/blob/e21782a3e5edf1d7e2e7bfca67341356dacfc042/lean/ErdosProblems/Shared/NonsquareModuloPrimes.lean#L160-L192)) is proved from the simple pole of the Dedekind zeta function at $`s=1`$, which is in Mathlib. If $`b`$ were a nonzero square modulo all but finitely many primes of degree one, these primes would split in $`K(\sqrt b)`$, and for real $`s>1`$ near $`1`$ the zeta function of $`K(\sqrt b)`$ would be at least a positive constant times the square of the zeta function of $`K`$, which the two simple poles forbid.

Both arguments use the condition at every root for all but finitely many primes. Testing finitely many primes supplies no such condition. The zeta-function argument is the one used in the linked formal proof.

<div id="long243:res:transportsquare" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L39">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-transportsquare-comparator">Comparator</a></p>

**Proposition 9** (the square forced by the numerator recurrence). *Write $`\kappa=m/6`$ and $`\eta=6c/m`$, so that $`Q_{m,c}(n)=\kappa f(n+1)`$ for $`f(T)=T^3-T+\eta`$. Then $`\alpha^2-1`$ is a square in $`\mathbb{Q}(\alpha)^\times`$ for a root $`\alpha`$ of $`f`$.*

</div>

<div class="proof">

*Proof.* Eliminating $`v_n`$ from <a href="#long243:eq:primitivetail" data-reference-type="eqref" data-reference="long243:eq:primitivetail">[long243:eq:primitivetail]</a> gives
``` math
\begin{equation}
\label{long243:eq:secondorderu}
 u_{n+2}=(a_n+a_{n+1})u_{n+1}-a_n^2u_n .
\end{equation}
```
Let $`\ell`$ be a prime and $`k`$ an index with $`\ell\mid u_k`$. Reading <a href="#long243:eq:secondorderu" data-reference-type="eqref" data-reference="long243:eq:secondorderu">[long243:eq:secondorderu]</a> at $`n=k-1`$ modulo $`\ell`$ gives $`u_{k+1}\equiv-a_{k-1}^2u_{k-1}`$, hence
``` math
\begin{equation}
\label{long243:eq:forcedsquare}
 -u_{k-1}u_{k+1}\equiv(a_{k-1}u_{k-1})^2 \pmod\ell,
\end{equation}
```
so $`-u_{k-1}u_{k+1}`$ is a square modulo $`\ell`$.

Let $`\ell\nmid6m`$ and let $`r\in\mathbb{F}_\ell`$ be a root of $`f`$. Then $`r\ne0`$ and $`r\ne\pm1`$, since $`f(0)=\eta\ne0`$ and $`f(\pm1)=\eta`$. Using $`\eta=r-r^3`$,
``` math
f(r-1)=-3r(r-1),\qquad f(r+1)=3r(r+1),
```
so at an index $`k\equiv r-1\pmod\ell`$ we may reduce the polynomial values in $`\mathbb{F}_\ell`$. All equalities in the following calculation are in that field: $`Q(k)=0`$, $`Q(k-1)=-3\kappa r(r-1)`$, $`Q(k+1)=3\kappa r(r+1)`$, and
``` math
\begin{equation}
\label{long243:eq:threevalue}
 -Q(k-1)Q(k+1)=9\kappa^2r^2(r^2-1).
\end{equation}
```
If $`r^2-1`$ were a nonsquare modulo $`\ell`$, then so would be the right side of <a href="#long243:eq:threevalue" data-reference-type="eqref" data-reference="long243:eq:threevalue">[long243:eq:threevalue]</a>, because $`9\kappa^2r^2`$ is a nonzero square; agreement at all three of $`k-1,k,k+1`$ would then contradict <a href="#long243:eq:forcedsquare" data-reference-type="eqref" data-reference="long243:eq:forcedsquare">[long243:eq:forcedsquare]</a>. That prohibition recurs at every index of the class $`r-1`$ modulo $`\ell`$, and Lemma <a href="#long243:res:periodicobstruction" data-reference-type="ref" data-reference="long243:res:periodicobstruction">5</a> with $`L=3`$, $`h=\ell`$ would give $`\underline d(S)\ge1/(3\ell)`$. So $`r^2-1`$ is a square in $`\mathbb{F}_\ell^\times`$ at every root of every good reduction, and Lemma <a href="#long243:res:squarespec" data-reference-type="ref" data-reference="long243:res:squarespec">8</a> applies with $`H(T)=T^2-1`$. ◻

</div>

<a id="the-square-condition-forces-m12"></a>

## The square condition forces $`m=12`$

<div id="long243:res:scaletwelve" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR20/ScaleTwelve.lean#L36">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-scaletwelve-comparator">Comparator</a></p>

**Lemma 10** (classification of the scales). *Let $`m`$ be a positive integer, let $`c\in\{-1,1\}`$ and $`\eta=6c/m`$, and suppose $`T^3-T+\eta`$ is irreducible over $`\mathbb{Q}`$ with a root $`\alpha`$ such that $`\alpha^2-1`$ is a square in $`\mathbb{Q}(\alpha)^\times`$. Then $`m=12`$.*

</div>

<div class="proof">

*Proof.* Choose $`\beta\in\mathbb{Q}(\alpha)`$ with $`\beta^2=\alpha^2-1`$. The identity $`(\alpha+\beta)(\alpha-\beta)=1`$ gives a reciprocal pair in the cubic field. Taking $`z=\alpha+\beta`$, we obtain
``` math
\begin{equation}
\label{long243:eq:zalpha}
 z^{-1}=\alpha-\beta,\qquad \alpha=\tfrac12(z+z^{-1}),
\end{equation}
```
and $`z`$ generates $`\mathbb{Q}(\alpha)`$. Write its minimal polynomial as $`p(Z)=Z^3+bZ^2+dZ+w`$ with $`b,d,w\in\mathbb{Q}`$ and $`w\ne0`$. The minimal polynomial of $`z^{-1}`$ is
``` math
\frac{Z^3p(Z^{-1})}{w}
   =Z^3+\frac dwZ^2+\frac bwZ+\frac1w.
```
Thus Newton’s identities apply directly to both $`z`$ and its inverse. We use the first two traces of $`\alpha`$ to restrict these coefficients, then the third trace to impose $`\eta=6c/m`$. All traces below are from $`\mathbb{Q}(\alpha)`$ to $`\mathbb{Q}`$. The polynomial $`T^3-T+\eta`$ gives
``` math
\begin{equation}
\label{long243:eq:alphatraces}
 \mathop{\mathrm{Tr}}\alpha=0,\qquad \mathop{\mathrm{Tr}}\alpha^2=2,\qquad \mathop{\mathrm{Tr}}\alpha^3=-3\eta .
\end{equation}
```
Newton’s identities give $`\mathop{\mathrm{Tr}}z=-b`$ and $`\mathop{\mathrm{Tr}}z^{-1}=-d/w`$, so the first equation in <a href="#long243:eq:alphatraces" data-reference-type="eqref" data-reference="long243:eq:alphatraces">[long243:eq:alphatraces]</a> and <a href="#long243:eq:zalpha" data-reference-type="eqref" data-reference="long243:eq:zalpha">[long243:eq:zalpha]</a> give
``` math
\begin{equation}
\label{long243:eq:dbw}
 d=-bw .
\end{equation}
```
For the second trace, Newton’s identities and $`d=-bw`$ give
``` math
\mathop{\mathrm{Tr}}z^2=b^2+2bw,\qquad \mathop{\mathrm{Tr}}z^{-2}=b^2-2b/w.
```
Since the trace of $`1`$ is $`3`$, squaring <a href="#long243:eq:zalpha" data-reference-type="eqref" data-reference="long243:eq:zalpha">[long243:eq:zalpha]</a> yields $`4\mathop{\mathrm{Tr}}\alpha^2=\mathop{\mathrm{Tr}}z^2+6+\mathop{\mathrm{Tr}}z^{-2}`$. Substituting $`\mathop{\mathrm{Tr}}\alpha^2=2`$ gives $`b^2+b(w-w^{-1})=1`$. Multiplication by $`w`$ factors this equation:
``` math
\begin{equation}
\label{long243:eq:factored}
 (bw-1)(b+w)=0 .
\end{equation}
```
For the third trace, the same identities give
``` math
\begin{aligned}
 \mathop{\mathrm{Tr}}z^3&=-b^3-3b^2w-3w,\\
 \mathop{\mathrm{Tr}}z^{-3}&=b^3-3b^2/w-3/w.
 \end{aligned}
```
The cross terms in $`(z+z^{-1})^3`$ have trace $`3(\mathop{\mathrm{Tr}}z+\mathop{\mathrm{Tr}}z^{-1})=0`$ by <a href="#long243:eq:dbw" data-reference-type="eqref" data-reference="long243:eq:dbw">[long243:eq:dbw]</a>. Thus $`8\mathop{\mathrm{Tr}}\alpha^3=\mathop{\mathrm{Tr}}z^3+\mathop{\mathrm{Tr}}z^{-3}`$. Using $`\mathop{\mathrm{Tr}}\alpha^3=-3\eta`$ now gives
``` math
\begin{equation}
\label{long243:eq:etatrace}
 \eta=\frac{(b^2+1)(w+w^{-1})}8 .
\end{equation}
```
By <a href="#long243:eq:factored" data-reference-type="eqref" data-reference="long243:eq:factored">[long243:eq:factored]</a>, either $`b=-w`$ or $`b=w^{-1}`$, and <a href="#long243:eq:etatrace" data-reference-type="eqref" data-reference="long243:eq:etatrace">[long243:eq:etatrace]</a> becomes
``` math
\eta=\frac{(w^2+1)^2}{8w}
 \qquad\text{or}\qquad
 \eta=\frac{(w^2+1)^2}{8w^3}.
```
Write $`w=r/s`$ with $`r\in\mathbb{Z}\mathbin{\backslash}\{0\}`$, $`s\in\mathbb{Z}_{>0}`$ and $`\gcd(r,s)=1`$. Since $`\eta=6c/m`$,
``` math
\begin{equation}
\label{long243:eq:mformula}
 m=\frac{48c\,rs^3}{(r^2+s^2)^2}
 \qquad\text{or}\qquad
 m=\frac{48c\,r^3s}{(r^2+s^2)^2}.
\end{equation}
```
Now $`\gcd(r^2+s^2,rs)=1`$, so integrality of $`m`$ and $`|c|=1`$ force $`(r^2+s^2)^2\mid48`$, hence $`r^2+s^2\in\{1,2,4\}`$. With $`r\ne0`$ and $`s\ge1`$ the value $`1`$ is too small, and $`4`$ is not a sum of two nonzero squares, so $`r^2+s^2=2`$ and $`|r|=s=1`$. Then <a href="#long243:eq:mformula" data-reference-type="eqref" data-reference="long243:eq:mformula">[long243:eq:mformula]</a> gives $`m=12cr`$, and $`m>0`$ gives $`m=12`$. ◻

</div>

The square condition leaves the two possible cubics
``` math
\begin{equation}
\label{long243:eq:survivors}
 Q_{12,\pm1}(n)=2n(n+1)(n+2)\pm1 .
\end{equation}
```
The square condition uses three consecutive numerators. The last step also uses the preceding denominator update, so it tests four consecutive numerators instead.

<a id="long243:sec:modseven"></a>

## The two remaining cubics fail modulo seven

<div id="long243:res:modseven" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-modseven">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-modseven-comparator">Comparator</a></p>

**Lemma 11** (two incompatible four-term residue patterns). *For $`Q_{12,1}`$, every sufficiently late four-index window beginning at $`n\equiv0\pmod7`$ contains an exceptional index. For $`Q_{12,-1}`$, the same holds for windows beginning at $`n\equiv1\pmod7`$. In either case, $`\underline d(S)\ge1/7`$. The specified starting residue classes are part of the assertion; no claim is made for every block of four consecutive indices.*

</div>

<div class="proof">

*Proof.* Reduce modulo $`7`$. For $`c=1`$ the values of $`Q_{12,1}`$ at $`n=0,1,2,3`$ are $`1,13,49,121`$, that is
``` math
\begin{equation}
\label{long243:eq:wordplus}
 (1,6,0,2),
\end{equation}
```
and for $`c=-1`$ the values at $`n=1,2,3,4`$ are $`11,47,119,239`$, that is
``` math
\begin{equation}
\label{long243:eq:wordminus}
 (4,5,0,1).
\end{equation}
```
Each four-term pattern recurs with period $`7`$.

Index a proposed occurrence locally by $`0,1,2,3`$, and use $`a_i`$ for the multiplier at local index $`i`$. Let $`(c_0,c_1,0,c_3)`$ be the residues of $`u`$ and $`(d_0,d_1,d_2,d_3)`$ those of $`v`$. Thus $`c_{i+1}=a_ic_i-d_i`$ and $`d_{i+1}=a_id_i`$ modulo $`7`$. The middle zero gives $`a_1c_1=d_1`$, then $`d_2=a_1d_1`$ and $`c_3=-d_2`$, so
``` math
\begin{equation}
\label{long243:eq:d1square}
 d_1^2=c_1\,a_1d_1=c_1d_2=-c_1c_3 .
\end{equation}
```
For <a href="#long243:eq:wordplus" data-reference-type="eqref" data-reference="long243:eq:wordplus">[long243:eq:wordplus]</a> this is $`-6\cdot2=2`$, and for <a href="#long243:eq:wordminus" data-reference-type="eqref" data-reference="long243:eq:wordminus">[long243:eq:wordminus]</a> it is $`-5\cdot1=2`$. The square roots of $`2`$ modulo $`7`$ are $`3`$ and $`4`$, so $`d_1\in\{3,4\}`$ in both cases.

The first step gives $`a_0=(c_1+d_0)/c_0`$ and hence $`d_1=d_0(d_0+c_1)/c_0`$, which is legitimate because $`c_0\in\{1,4\}`$ is invertible. For <a href="#long243:eq:wordplus" data-reference-type="eqref" data-reference="long243:eq:wordplus">[long243:eq:wordplus]</a> this is $`d_1=d_0(d_0+6)`$, with values
``` math
(0,0,2,6,5,6,2) \qquad\text{at } d_0=0,1,\ldots,6,
```
and for <a href="#long243:eq:wordminus" data-reference-type="eqref" data-reference="long243:eq:wordminus">[long243:eq:wordminus]</a> it is $`d_1=2d_0(d_0+5)`$, with values
``` math
(0,5,0,6,2,2,6).
```
The incompatibility also follows without enumerating $`d_0`$. Completing the square gives
``` math
d_1+2=(d_0+3)^2\quad(c=1),\qquad
 d_1+2=2(d_0-1)^2\quad(c=-1).
```
Since $`2`$ is a square modulo $`7`$, either update makes $`d_1+2`$ a square. The required values $`d_1=3,4`$ instead give the nonsquares $`5,6`$. The two displayed lists provide the same exhaustive check: both images are $`\{0,2,5,6\}`$, disjoint from $`\{3,4\}`$.

Hence every sufficiently late window $`[7k,7k+3]`$ for the plus profile, and every sufficiently late window $`[1+7k,4+7k]`$ for the minus profile, contains an element of $`S`$. Windows within each family are pairwise disjoint. There are $`X/7+O(1)`$ such windows contained in $`[0,X]`$, so choosing one exceptional index in each gives $`\#(S\cap[0,X])\ge X/7-O(1)`$ and therefore $`\underline d(S)\ge1/7`$. This stronger local bound is not promoted to a uniform lower bound for arbitrary cubic profiles. ◻

</div>

<div class="proof">

*Proof of Theorem <a href="#long243:res:cubicexclusion" data-reference-type="ref" data-reference="long243:res:cubicexclusion">4</a>.* Assume $`\underline d(S)=0`$. Lemmas <a href="#long243:res:gcdshape" data-reference-type="ref" data-reference="long243:res:gcdshape">6</a> and <a href="#long243:res:reduciblecase" data-reference-type="ref" data-reference="long243:res:reduciblecase">7</a> put the primitive tail in the shape <a href="#long243:eq:Qmc" data-reference-type="eqref" data-reference="long243:eq:Qmc">[long243:eq:Qmc]</a> with $`c=\pm1`$ and $`Q_{m,c}`$ irreducible. Each excluded branch already contradicts the assumption by producing a positive, branch-dependent lower density, namely $`1/(12\ell)`$ or $`1/\ell`$ for the relevant prime $`\ell`$. Proposition <a href="#long243:res:transportsquare" data-reference-type="ref" data-reference="long243:res:transportsquare">9</a> and Lemma <a href="#long243:res:scaletwelve" data-reference-type="ref" data-reference="long243:res:scaletwelve">10</a> force $`m=12`$, and Lemma <a href="#long243:res:modseven" data-reference-type="ref" data-reference="long243:res:modseven">11</a> then gives $`\underline d(S)\ge1/7`$, the final contradiction. ◻

</div>

The two densities play different roles. If the field element is not a square, Chebotarev supplies one witnessing prime; its periodic obstruction gives a positive density of disagreement *indices*. No lower bound uniform over cubic profiles is needed.

<a id="polynomial-extraction-at-a-regular-rate"></a>

## Polynomial extraction at a regular rate

It remains to connect the arithmetic exclusion with an asymptotic rate. For the cubic rate, the natural comparison is $`n(n+1)(n+2)`$; its successive ratio is exactly $`1+3/n`$. For a real parameter $`\lambda>1`$, the corresponding comparison sequence is $`\Gamma(n+\lambda)/\Gamma(n)`$, with ratio $`1+\lambda/n`$. The argument first leaves an error $`o(n)`$. Subtracting the two recurrences then shows that the first difference of that error tends to zero. A sufficiently high difference of the original integer sequence is therefore a small integer and must vanish. Its eventual polynomial growth also forces $`\lambda`$ to be integral.

<div id="long243:res:extraction" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-extraction">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-extraction-comparator">Comparator</a></p>

**Lemma 12** (integer extraction at a regular rate). *Let $`\lambda>1`$ and let $`C_n`$ be positive integers with
``` math
\begin{equation}
\label{long243:eq:regularrate}
 \frac{C_{n+1}}{C_n}=1+\frac\lambda n+o(n^{-\lambda}).
\end{equation}
```
Then $`\lambda`$ is an integer $`d\ge2`$, and there are $`A\in\mathbb{Q}_{>0}`$ and $`B\in\mathbb{Q}`$ with $`C_n=A\,n(n+1)\cdots(n+d-1)+B`$ for all large $`n`$.*

</div>

<div class="proof">

*Proof.* Put $`F_n=\Gamma(n+\lambda)/\Gamma(n)`$, so that $`F_{n+1}/F_n=1+\lambda/n`$ exactly and $`F_n\sim n^\lambda`$ by the gamma-ratio asymptotic \[dlmf_gamma, 5.11.12\]. Write $`\varepsilon_n=o(n^{-\lambda})`$ for the error in <a href="#long243:eq:regularrate" data-reference-type="eqref" data-reference="long243:eq:regularrate">[long243:eq:regularrate]</a> and $`z_n=C_n/F_n`$, so that $`z_{n+1}/z_n=1+\varepsilon_n/(1+\lambda/n)`$. Since $`\lambda>1`$ the errors are absolutely summable, so the product converges and $`z_n\to K`$ for some $`K>0`$, with $`z_n-K=o(n^{1-\lambda})`$. To see the stated error, put $`\eta_n=\sup_{k\ge n}k^\lambda|\varepsilon_k|\to0`$; the tail of the logarithmic product has absolute value at most $`O(\eta_n\sum_{k\ge n}k^{-\lambda})=o(n^{1-\lambda})`$. The factors are positive eventually, so the limiting product is nonzero. Hence
``` math
\begin{equation}
\label{long243:eq:dsmall}
 \delta_n:=C_n-KF_n=F_n(z_n-K)=o(n).
\end{equation}
```
We subtract the recurrences for $`C_n`$ and $`KF_n`$ to obtain $`\delta_{n+1}-\delta_n=(\lambda/n)\delta_n+\varepsilon_nC_n`$. The first term is $`o(1)`$ by <a href="#long243:eq:dsmall" data-reference-type="eqref" data-reference="long243:eq:dsmall">[long243:eq:dsmall]</a>, and the second is $`o(1)`$ because $`C_n=O(n^\lambda)`$. Hence $`\Delta\delta_n\to0`$. Every further difference is a finite linear combination of shifts of this sequence, so $`\Delta^j\delta_n\to0`$ for all $`j\ge1`$.

For the comparison sequence, the Gamma recurrence gives
``` math
\Delta F_n
 =\frac{\Gamma(n+1+\lambda)}{\Gamma(n+1)}
  -\frac{\Gamma(n+\lambda)}{\Gamma(n)}
 =\lambda\,\frac{\Gamma(n+\lambda)}{\Gamma(n+1)}.
```
Iterating this identity gives
``` math
\Delta^jF_n=\lambda(\lambda-1)\cdots(\lambda-j+1)\,
 \frac{\Gamma(n+\lambda)}{\Gamma(n+j)},
```
whose right side is $`O(n^{\lambda-j})`$. Choose an integer $`j>\lambda`$; then $`\Delta^jF_n\to0`$, so $`\Delta^jC_n\to0`$. These are integers, so $`\Delta^jC_n=0`$ for all large $`n`$. Choose $`N`$ beyond this threshold. The Newton forward-difference formula gives
``` math
C_{N+t}=\sum_{i=0}^{j-1}\binom ti\Delta^iC_N\qquad(t\ge0),
```
so $`C_n`$ agrees eventually with a polynomial with rational coefficients. Its growth $`C_n\asymp n^\lambda`$ forces the degree to be $`\lambda`$, so $`\lambda=d`$ is an integer, and $`d\ge2`$ because $`\lambda>1`$. For that integer $`F_n=n(n+1)\cdots(n+d-1)`$ exactly, so <a href="#long243:eq:dsmall" data-reference-type="eqref" data-reference="long243:eq:dsmall">[long243:eq:dsmall]</a> says that the difference of two polynomials of degree $`d`$ is $`o(n)`$, hence constant. The leading coefficient of the rational polynomial is $`K`$, so $`K\in\mathbb{Q}_{>0}`$; the constant difference is rational as well. This gives the stated shape with $`A=K`$ and $`B\in\mathbb{Q}`$. ◻

</div>

The little-oh error in <a href="#long243:eq:regularrate" data-reference-type="eqref" data-reference="long243:eq:regularrate">[long243:eq:regularrate]</a> cannot in general be replaced by a big-oh error. The positive integers $`C_n=n(n+1)(n+2)+(-1)^n`$ satisfy $`C_{n+1}/C_n=1+3/n+O(n^{-3})`$ and are not eventually polynomial. Likewise $`C_n=\lceil n^{3/2}\rceil`$ satisfies $`C_{n+1}/C_n=1+3/(2n)+O(n^{-3/2})`$: rounding contributes $`O(n^{-3/2})`$, while the unrounded ratio has error $`O(n^{-2})`$. These scalar examples obstruct weaker extraction hypotheses, not an irrationality theorem; neither is asserted to satisfy the full tail hypotheses. Extraction excludes nonintegral $`\lambda`$. Integral rates still require an arithmetic exclusion, proved here in degree three.

<div id="long243:res:tailratio" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/QuantitativeTail.lean#L204">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-tailratio-comparator">Comparator</a></p>

**Lemma 13** (comparison of the numerator and denominator ratios). *Let $`a_n`$ be strictly increasing positive integers with $`a_{n+1}/a_n^2\to1`$ and $`\sum_n1/a_n`$ rational, and let $`(C_n,D_n)`$ be the integer tail. Write $`\gamma_n=a_n^2/a_{n+1}-1`$. Then
``` math
\frac{C_{n+1}}{C_n}=1+\gamma_n+O(a_n^{-1}),
 \qquad a_n\ge\exp(c\,2^n)\ \text{eventually for some }c>0 .
```*

</div>

<div class="proof">

*Proof.* Since $`a_{n+1}/a_n^2\to1`$ and $`a_n\to\infty`$, there is an $`N`$ with $`a_{n+1}\ge a_n^2/2\ge2a_n`$ for $`n\ge N`$. Iterating $`a_{n+1}\ge a_n^2/2`$ from an index where $`a_n>2`$ gives $`a_n\ge\exp(c2^n)`$ eventually. The same doubling gives, for $`m>N`$,
``` math
\frac1{a_m}\ \le\ x_m\ =\ \sum_{k\ge m}\frac1{a_k}\ \le\ \frac2{a_m},
```
so $`x_{m}=(1+\rho_{m})/a_{m}`$ with $`0\le\rho_{m}=a_mx_{m+1}\le 2a_m/a_{m+1}\le4/a_m`$, using $`a_{m+1}\ge a_m^2/2`$. Hence
``` math
\frac{C_{n+1}}{C_n}=\frac{a_nD_nx_{n+1}}{D_nx_n}
 =a_n\cdot\frac{(1+\rho_{n+1})/a_{n+1}}{(1+\rho_n)/a_n}
 =\frac{a_n^2}{a_{n+1}}\cdot\frac{1+\rho_{n+1}}{1+\rho_n}.
```
The last factor is $`1+O(1/a_n)`$ and $`a_n^2/a_{n+1}`$ is bounded, so the product is $`a_n^2/a_{n+1}+O(a_n^{-1})`$. ◻

</div>

The exact identity in Section <a href="#long243:sec:lcmrecords" data-reference-type="ref" data-reference="long243:sec:lcmrecords">6</a> gives the same estimate: $`C_{n+1}/C_n=1-E_n/C_n`$, while $`0<\gamma_n+E_n/C_n<3/a_n`$ eventually. The identity follows from Theorem <a href="#long243:res:defect" data-reference-type="ref" data-reference="long243:res:defect">17</a>; its bound also uses vanishing relative error and near-quadratic growth. Equation <a href="#long243:eq:weightedgrowth" data-reference-type="eqref" data-reference="long243:eq:weightedgrowth">[long243:eq:weightedgrowth]</a> is the resulting weighted-sum application, not the identity itself.

<div class="proof">

*Proof of Theorem <a href="#long243:res:nonintegralrate" data-reference-type="ref" data-reference="long243:res:nonintegralrate">3</a>.* The stated rate implies $`a_{n+1}/a_n^2\to1`$ and convergence of the reciprocal series. Suppose its sum were rational, and form the positive integer tail numerators $`C_n`$. Lemma <a href="#long243:res:tailratio" data-reference-type="ref" data-reference="long243:res:tailratio">13</a> gives $`C_{n+1}/C_n=a_n^2/a_{n+1}+O(a_n^{-1})`$ and an eventual bound $`a_n\ge\exp(c2^n)`$ for some $`c>0`$. Hence $`a_n^{-1}=o(n^{-\lambda})`$ and
``` math
\frac{C_{n+1}}{C_n}=1+\frac{\lambda}{n}+o(n^{-\lambda}).
```
Lemma <a href="#long243:res:extraction" data-reference-type="ref" data-reference="long243:res:extraction">12</a> forces $`\lambda`$ to be an integer, contrary to the hypothesis. ◻

</div>

For a concrete nonintegral rate, take $`a_1=8`$ and
``` math
a_{n+1}=\left\lceil\frac{2n a_n^2}{2n+3}\right\rceil
 \quad(n\ge1).
```
The first terms are $`8,26,387,99846`$. Writing $`r_n=1+3/(2n)`$ gives $`a_{n+1}=\lceil a_n^2/r_n\rceil`$ and $`0\le r_n-a_n^2/a_{n+1}<r_n^2/a_n^2\le25/(4a_n^2)`$. Also $`a_{n+1}\ge(2/5)a_n^2`$, which from $`a_1=8`$ proves strict increase and exponential lower growth. Thus the ratio error is $`o(n^{-3/2})`$, and Theorem <a href="#long243:res:nonintegralrate" data-reference-type="ref" data-reference="long243:res:nonintegralrate">3</a> proves this reciprocal sum irrational.

<div class="proof">

*Proof of Theorem <a href="#long243:res:cubicrate" data-reference-type="ref" data-reference="long243:res:cubicrate">2</a>.* The hypothesis $`a_n^2/a_{n+1}=1+3/n+o(n^{-3})`$ gives $`a_{n+1}/a_n^2\to1`$. Suppose $`\sum_n1/a_n`$ were rational and pass to the integer tail, so that $`(a,C,D)`$ satisfies <a href="#long243:eq:cubicorbit" data-reference-type="eqref" data-reference="long243:eq:cubicorbit">[long243:eq:cubicorbit]</a> with every $`C_n`$ and $`D_n`$ a positive integer. By Lemma <a href="#long243:res:tailratio" data-reference-type="ref" data-reference="long243:res:tailratio">13</a> and $`a_n\ge\exp(c2^n)`$, the error term $`O(a_n^{-1})`$ is $`o(n^{-3})`$, so
``` math
\frac{C_{n+1}}{C_n}=1+\frac3n+o(n^{-3}).
```
Lemma <a href="#long243:res:extraction" data-reference-type="ref" data-reference="long243:res:extraction">12</a> at $`\lambda=3`$ gives $`C_n=A\,n(n+1)(n+2)+B`$ for all large $`n`$, with $`A\in\mathbb{Q}_{>0}`$ and $`B\in\mathbb{Q}`$. That contradicts Theorem <a href="#long243:res:cubicexclusion" data-reference-type="ref" data-reference="long243:res:cubicexclusion">4</a>. ◻

</div>

No restriction on the rational normalisation was assumed: the proof derives the permitted primitive leading coefficient. The two residue patterns <a href="#long243:eq:wordplus" data-reference-type="eqref" data-reference="long243:eq:wordplus">[long243:eq:wordplus]</a> and <a href="#long243:eq:wordminus" data-reference-type="eqref" data-reference="long243:eq:wordminus">[long243:eq:wordminus]</a>, the image $`\{0,2,5,6\}`$ modulo $`7`$ and the condition $`(r^2+s^2)^2\mid48`$ have been calculated above.

The rationality supposition in this proof supplies the integer orbit. The rate implies $`a_{n+1}/a_n^2\to1`$ and excludes the eventual Sylvester recurrence, so the conclusion is irrationality on a restricted class of the sequences in Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>.

At the cubic rate $`P_n/a_n`$ grows like $`n^3`$ and its increment like $`n^2`$. Thus neither the bounded-increment criterion nor Koizumi’s nonpositive upper-limit criterion applies. The rate also fails his $`1+o(1/n)`$ condition, and Duverney’s signed defect series diverges. We do not decide whether the LCM-weighted criteria apply; that requires information about the repeated factors in the prefix product. Conversely, Theorem <a href="#long243:res:cubicexclusion" data-reference-type="ref" data-reference="long243:res:cubicexclusion">4</a> assumes only positive integer $`a_n,C_n,D_n`$ and the recurrences <a href="#long243:eq:cubicorbit" data-reference-type="eqref" data-reference="long243:eq:cubicorbit">[long243:eq:cubicorbit]</a>, not the near-quadratic growth limit. The two arguments therefore retain distinct hypotheses.

In familiar approximation notation, $`C_n=q\bigl(\prod_{k<n}a_k\cdot\sum_m1/a_m-\sum_{k<n}\prod_{j<n,\,j\ne k}a_j\bigr)`$ is a linear form in the reciprocal sum with integer coefficients. These integer remainders grow like $`n^3`$. We use the precision $`o(n^{-3})`$ to determine their polynomial form by finite differences, then exclude that form by the recurrence. The integer example $`n(n+1)(n+2)+(-1)^n`$ above explains why an $`O(n^{-3})`$ error alone does not justify that polynomial conclusion.

<a id="long243:sec:priorwork"></a>

# Prior work and formalisation

<a id="classical-criteria-and-pseudo-greedy-expansions."></a>

#### Classical criteria and pseudo-greedy expansions.

The rational-tail method predates these coordinates. Erdős and Straus \[erdosstraus1974, Theorem 2.1, pp. 85–86\] use eventual integer remainders under a small-numerator hypothesis. In polynomial Cantor series, Hančl and Tijdeman split the numerator into finitely many shifted products. Rationality is then characterised by the vanishing of the resulting polynomial sum \[hancltijdeman2008, Theorem 2.2 and its proof, pp. 39–40\]. Their theorem provides methodological context, not a result for arbitrary arrays of signed integer coefficients: the rearrangement of the infinite sum needs boundary control, supplied there by the polynomial hypothesis. Neither result supplies the first-crossing argument for a lower error bound proved below.

Several classical results give sufficient conditions directly on the sequence $`(a_n)`$. Their hypotheses use different quantities, so the comparisons must be made separately. Koizumi’s product criterion is implied by eventual nonnegativity of the integer error $`E_n`$, under the identification of coordinates given below. It therefore already covers the descent argument in Section <a href="#long243:sec:descent" data-reference-type="ref" data-reference="long243:sec:descent">8</a> (see \[koizumi2025, Cor. 4(1) and Prop. 1(1), pp. 14–15\]). The original Erdős–Straus criterion instead uses a least common multiple. Erdős and Straus proved that if $`\lim a_n/a_{n-1}^{2}=1`$, the reciprocal sum is rational, and $`(a_n)`$ has no Sylvester tail, then
``` math
\limsup_{n\to\infty}\ \frac{[a_1,\ldots,a_n]}{a_{n+1}}
 \left(\frac{a_{n+1}^{2}}{a_{n+2}}-1\right)>0,
```
where $`[a_1,\ldots,a_n]`$ is the least common multiple \[erdosstraus1964, Theorem 3, p. 132\]. This is the indexing in the original theorem. With $`A_r=\operatorname{lcm}(a_1,\ldots,a_{r-1})`$ and $`r=n+1`$, its expression is exactly $`(A_r/a_r)(a_r^2/a_{r+1}-1)`$, the LCM quantity in the short note. The index change is not an additional difference between those two criteria. Erdős’s 1988 survey, followed by the catalogue summary, instead prints $`a_n^2/a_{n+1}-1`$ in the second factor while retaining the same prefix-LCM quotient; that displayed summary is off by one and is not followed here \[erdos1988, p. 105\]\[erdosproblems\]. Koizumi records the convenient sufficient rate $`a_n^2/a_{n+1}=1+o(1/n)`$ under which the Erdős–Straus criterion settles the problem \[koizumi2025, Remark 3, p. 16\]. Tijdeman and Yuan give a criterion of the same kind for Ahmes series with positive integer numerators, weighted by the least common multiple of the earlier denominators \[tijdemanyuan2002\].

Duverney’s signed criterion gives a further comparison. For positive integers $`a_n\to\infty`$ and signs $`\epsilon_n\in\{-1,1\}`$, its printed hypothesis (3.6) is the one-sided condition
``` math
\sum_{n\ge0}\left(\frac{a_{n+1}}{a_n^2}-1\right)<\infty,
```
without absolute values. The stated conclusion is that $`\sum_{n\ge0}\epsilon_n/a_n`$ is rational if and only if
``` math
a_{n+1}=a_n^2-(\epsilon_{n+1}/\epsilon_n)a_n
             +\epsilon_{n+2}/\epsilon_{n+1}
```
for all large $`n`$ \[duverney2001, Corollary 3.2, p. 287\]. For the comparison here we impose the stronger sufficient hypothesis $`\sum_{n\ge0}|a_{n+1}/a_n^2-1|<\infty`$ and take all signs positive. The distinction concerns one step of the printed proof. On pp. 299–300, the reduced auxiliary fractions $`p'_n/q'_n`$ satisfy $`p'_{n+1}\mid q'_n`$ and
``` math
p'_n\le p'_N\prod_{k=N}^{n-1}\frac{q'_k}{p'_k}.
```
The required boundedness follows if $`\prod_{k\ge N}(p'_k/q'_k)`$ has a positive limit. Absolute convergence of the growth-defect series ensures this, using the summable error in Duverney’s estimate (3.3). Signed convergence alone does not justify that product step, even for positive rational factors. For each integer $`m\ge2`$, take the pair $`1+1/m`$, $`1-1/m`$ successively $`m`$ times. The deviations cancel after every pair, and the intervening partial sums are $`1/m\to0`$, so their series converges. But the product through the block $`m=N`$ is
``` math
\prod_{m=2}^{N}\left(1-\frac1{m^2}\right)^m
 =\frac{(N+1)^N}{2N^{N+1}}\sim\frac e{2N}\longrightarrow0;
```
the equality follows by cancelling powers of consecutive integers. This example does not impose $`p'_{n+1}\mid q'_n`$. It refutes only the general product inference, not Duverney’s arithmetic criterion. We therefore use only the absolute-convergence form; the interpretation with merely signed convergence is not needed in any proof here.

In the all-positive case $`\epsilon_n=1`$, absolute convergence also gives a direct comparison with the classical product criterion. With the one-based notation $`P_n=\prod_{1\le j<n}a_j`$ used above,
``` math
\frac{P_{n+1}/a_{n+1}}{P_n/a_n}=\frac{a_n^2}{a_{n+1}}.
```
The ratios on the right have an absolutely convergent sum of deviations from $`1`$, because the same is true of their reciprocals and those reciprocals tend to $`1`$. Thus $`P_n/a_n`$ has a positive finite limit, and its increments tend to zero. This case already satisfies the classical nonpositive-upper-limit condition; the bounded-increment result allows a larger class of sequences.

A different quantitative question is treated by Duverney, Kurosawa and Shiokawa \[duverneykurosawashiokawa2020, Theorem 1, author-version p. 2; proof in Section 3\]. For rational $`x_n>1`$, their result assumes eventual $`x_{n+1}\ge x_n^2`$ and control of the accumulated denominators of $`x_{n+1}/x_n^2`$; it computes the irrationality exponent of a signed reciprocal series. We use it only as a restricted comparison. In particular, the eventual Sylvester recurrence and the cubic rate considered here approach quadratic growth from the other side.

Badea’s positive-term criterion is adjacent but different. For a convergent series $`\sum_n b_n/a_n`$ with $`a_n,b_n`$ positive integers, eventual strict inequality
``` math
a_{n+1}>\frac{b_{n+1}}{b_n}a_n^2-\frac{b_{n+1}}{b_n}a_n+1
```
forces irrationality, while rationality under the corresponding non-strict inequality forces eventual equality \[badea1993, Theorem A, p. 313; Cor. 2.2, p. 316\]. For $`b_n=1`$, its hypothesis is $`a_{n+1}\ge a_n^2-a_n+1`$, an inequality between consecutive denominators, not the one-step sign condition $`E_n\ge0`$ used in integer descent. Under the standing rational-tail and growth hypotheses, however, either inequality imposed eventually forces the Sylvester recurrence and hence the other. Their eventual forms are equivalent in this setting; that fact does not supply either condition for a general signed error.

Koizumi’s pseudo-greedy expansion \[koizumi2025\] chooses $`a_n`$ by rounding $`x_n^{-1}+1`$ to the nearest integer, with a half-integer rounded upwards. Here $`x_n`$ is the remaining sum before subtracting $`1/a_n`$. Thus $`a_n=\lfloor x_n^{-1}+3/2\rfloor`$, and the gap $`\varepsilon_n=x_n^{-1}+1-a_n`$ is the signed rounding error. Write the rational initial sum as $`r=p/q`$ with positive integers $`p,q`$. His Lemma 4  \[koizumi2025, pp. 11–12\] produces integers $`c_n>0`$, $`d_n`$ and $`e_n`$ with $`x_n=c_n/d_n`$ and $`\varepsilon_n=e_n/c_n`$, satisfying
``` math
a_n=\frac{d_n-e_n}{c_n}+1,\qquad
 c_{n+1}=c_n-e_n,\qquad
 d_{n+1}=a_nd_n ,
```
and the proof of that lemma also gives $`c_{n+1}=a_nc_n-d_n`$. These are the recurrences of Section <a href="#long243:sec:state" data-reference-type="ref" data-reference="long243:sec:state">4</a>, after matching the starting index and the initial normalization. For a sequence satisfying the hypotheses of Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>, the rounding rule is guaranteed only after a finite restart \[koizumi2025, Corollary 3, p. 9\]. Restarting there with the tail in lowest terms gives $`(c_n,d_n,e_n)`$; the original $`(C_n,D_n,E_n)`$ on that tail is a fixed positive integer multiple of this triple, with the indices matched. Thus $`E_n/C_n=\varepsilon_n`$ is unchanged by the restart. The integer $`E_n`$ is not necessarily a numerator in lowest terms, and the rounding range is not asserted before the restart. The first identity above gives $`E_n=D_n-(a_n-1)C_n`$; the remaining identities are exactly the numerator and denominator recurrences, including Proposition <a href="#long243:res:update" data-reference-type="ref" data-reference="long243:res:update">14</a>. On an all-negative tail we later write $`e_n=-E_n>0`$ for the magnitude. That local use of lower-case $`e_n`$ has the opposite sign to Koizumi’s signed integer $`e_n`$.

His Theorem 3 \[koizumi2025, pp. 12–13\] proves the equivalence of two assertions. Conjecture 1 \[koizumi2025, p. 4\] asks whether, for a positive rational $`r`$, the condition $`\varepsilon_n\to0`$ forces $`\varepsilon_n=0`$ eventually. Question 1 \[koizumi2025, p. 3\] is the question of Erdős and Graham stated as Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a> above. Two implications used below already appear in these coordinates: his Lemma 3, that $`\varepsilon_n=0`$ forces $`\varepsilon_{n+1}=0`$, is the absorption of Theorem <a href="#long243:res:absorb" data-reference-type="ref" data-reference="long243:res:absorb">24</a>, and his Proposition 1(2), that $`\varepsilon_n\ge0`$ for all large $`n`$ forces $`\varepsilon_n=0`$ for all large $`n`$, is the descent of Theorem <a href="#long243:res:descent" data-reference-type="ref" data-reference="long243:res:descent">42</a>. Both statements are given in \[koizumi2025, Lemma 3, p. 10; Prop. 1(2), p. 14\]. Koizumi attributes Proposition 1(2) to Badea. Its contrapositive says that a counterexample must have negative errors infinitely often; it assumes the sign is eventually nonnegative, while Theorem <a href="#long243:res:bounded" data-reference-type="ref" data-reference="long243:res:bounded">53</a> below assumes only that the negative part is eventually bounded. It permits negative errors between $`-B`$ and $`0`$ and imposes no independent upper bound on positive errors; the relative-error limit is still required.

The growth hypothesis in Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a> is calibrated by two facts about Sylvester’s sequence. With $`a_1=2`$, it satisfies $`a_n\sim c_0^{2^{n}}`$ with $`c_0=1.2640847\ldots`$. Deleting initial terms and reindexing produces sequences with $`a_n\sim C^{2^{n}}`$ for arbitrarily large $`C`$ whose reciprocals still sum to a rational number \[kovactao2024, arXiv v4, p. 2\]. The classical sufficient condition for irrationality, $`\lim_n a_n^{1/2^{n}}=\infty`$, is therefore sharp. Kovač and Tao identify that condition as folklore  \[kovactao2024, arXiv v4, p. 2\]; they attribute the sharpness observation to Erdős (1975). A sequence with $`a_n/a_{n-1}^{2}\to1`$ has $`a_n^{1/2^{n}}`$ convergent, so that criterion says nothing about the sequences of Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>, and rationality is genuinely possible there. Sylvester’s sequence is `A000058` in the OEIS; `A129871` is the variant $`1,2,3,7,43,\ldots`$ with an initial $`1`$ prepended. For the recent literature on irrationality of Ahmes series we refer to Kovač and Tao \[kovactao2024\], who resolve several problems of Erdős and Graham drawn from the same two sources cited above, and whose introduction gives a sample of the intermediate work, including Sándor (1984) and Badea (1987). They do not treat Problem #243; the rigidity conclusion asked for there is not among their results.

Crmarić and Kovač \[crmarickovac2025, Theorems 1–2\] address the neighbouring Problem #270, not Problem #243. Allowing integer $`f(n)\to\infty`$ in $`\sum_n(\prod_{j=1}^{f(n)}(n+j))^{-1}`$ gives every positive real value; imposing nondecreasing $`f`$ gives a measure-zero value set. The latter assertion does not rule out individual rational values. Their extension of Kakeya’s subsum argument explains why decay alone need not force irrationality when the summands remain freely selectable. The present exact denominator recurrence imposes additional compatibility, so neither direction is an implication between their theorem and ours.

The *Formal Conjectures* collection contains a mathematically equivalent unproved declaration, up to its zero-based indexing  \[formalconjectures243\]. Its summand is $`\mathbb{Q}`$-valued, so Lean’s `Summable` hypothesis asserts the existence of a sum in $`\mathbb{Q}`$; the finite indexing shift changes that sum only by a rational prefix. The declaration therefore does encode the rationality premise, but its proof is `sorry`. It states the problem without proving it, and the development in this note is independent of it. Earlier formal work on the remainder method should also be distinguished from a solution of this problem: Koutsoukou-Argyraki and Li’s Archive of Formal Proofs entry \[kouli2020\] records an Isabelle/HOL formalisation of Erdős–Straus (1974), Theorem 2.1, Corollary 2.10 and Theorem 3.1. That is formal prior art for those classical criteria, not an existing formal proof of Erdős #243.

Each criterion still requires an additional bound or convergence estimate under the unrestricted hypotheses. In the stable-gcd case, for example, the record-increment theorem gives a positive lower bound for the log-log coefficient, rather than proving it infinite. All conclusions about a persistently nonzero error assume failure of eventual Sylvester behaviour. We collect them in Section <a href="#long243:sec:open" data-reference-type="ref" data-reference="long243:sec:open">14</a>, where mixed-sign tails remain unclassified. The two recurrence proofs below are independent of the cubic argument: one uses a stable gcd and CRT, the other an infinite product and integer descent.

<div id="243-long-integer-tails">

</div>

<a id="long243:sec:state"></a>

# Integer numerators, denominators and errors

We retain an unreduced fraction $`C_n/D_n`$ for each rational tail. This keeps the denominator update multiplicative: removing $`1/a_n`$ from the tail gives
``` math
\begin{equation}
\label{long243:eq:recurrences}
 D_{n+1}=a_nD_n,\qquad C_{n+1}=a_nC_n-D_n.
\end{equation}
```
We measure the difference from the Sylvester recurrence by $`E_n=D_n-(a_n-1)C_n`$. These are Koizumi’s recurrences \[koizumi2025, Lemma 4, pp. 11–12\]; their formal definitions are the [denominator update](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L41), the [numerator update](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L45), and the [error](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L49).

We also consider integer solutions of <a href="#long243:eq:recurrences" data-reference-type="eqref" data-reference="long243:eq:recurrences">[long243:eq:recurrences]</a> without initially assuming that $`C_n/D_n`$ is a reciprocal tail. Here and in the following recurrence sections the indices may start at $`0`$, and $`E_n`$ always denotes the error just defined. We state positivity and growth assumptions as they are needed. The terms $`a_n`$ are the multipliers, while $`C_n,D_n`$ are the numerator and denominator. The pseudo-greedy rounding rule is an additional condition giving $`-C_n/2\le E_n<C_n/2`$, whereas the absorption argument below needs only $`|E_n|<C_n`$. At a negative error we write $`e_n=-E_n>0`$. For an isolated step we use $`a,D,C\in\mathbb{Z}`$ without subscripts.

<div id="long243:res:update" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L57">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-update-comparator">Comparator</a></p>

**Proposition 14** (update law). *For all $`a,D,C\in\mathbb{Z}`$,
``` math
aC-D=C-\bigl(D-(a-1)C\bigr).
```
Consequently, every solution of <a href="#long243:eq:recurrences" data-reference-type="eqref" data-reference="long243:eq:recurrences">[long243:eq:recurrences]</a> satisfies $`C_{n+1}=C_n-E_n`$.*

</div>

<div class="proof">

*Proof.* $`C-\bigl(D-(a-1)C\bigr)=aC-D`$. ◻

</div>

$`C_n`$ decreases when $`E_n>0`$, increases when $`E_n<0`$, and stays unchanged when $`E_n=0`$. This is why bounds on the negative error become bounds on upward increments.

<div id="long243:ex:sylvester" class="example">

**Example 15** (the Sylvester sequence). Take $`a_n=2,3,7,43,1807,\ldots`$ with $`a_{n+1}=a_n^{2}-a_n+1`$, and start the state at $`D_0=C_0=1`$. The two updates give

<div class="center">

| $`n`$ |  $`a_n`$ |  $`D_n`$ | $`C_n`$ | $`E_n`$ |
|------:|---------:|---------:|--------:|--------:|
| $`0`$ |    $`2`$ |    $`1`$ |   $`1`$ |   $`0`$ |
| $`1`$ |    $`3`$ |    $`2`$ |   $`1`$ |   $`0`$ |
| $`2`$ |    $`7`$ |    $`6`$ |   $`1`$ |   $`0`$ |
| $`3`$ |   $`43`$ |   $`42`$ |   $`1`$ |   $`0`$ |
| $`4`$ | $`1807`$ | $`1806`$ |   $`1`$ |   $`0`$ |

</div>

and $`D_n=a_n-1`$ with $`C_n=1`$ at every index: if $`D_n=a_n-1`$ and $`C_n=1`$ then $`C_{n+1}=a_n-(a_n-1)=1`$ and $`D_{n+1}=a_n(a_n-1)=a_{n+1}-1`$. Hence $`E_n=D_n-(a_n-1)C_n=0`$ throughout and the numerator never moves, which is Proposition <a href="#long243:res:update" data-reference-type="ref" data-reference="long243:res:update">14</a> in the stationary case.

</div>

<a id="construction-from-the-reciprocal-sum."></a>

#### Construction from the reciprocal sum.

Let $`T_n=\sum_{k\ge n}1/a_k`$ and suppose $`T_0\in\mathbb{Q}`$. Put $`D_0`$ equal to a common denominator and $`D_n=D_0a_0\cdots a_{n-1}`$, and set $`C_n=D_nT_n`$. Then $`C_n\in\mathbb{Z}`$ for every $`n`$, and from $`T_n=1/a_n+T_{n+1}`$ one gets $`C_{n+1}=a_nC_n-D_n`$, which is the tail update. On Sylvester’s sequence $`T_n=1/(a_n-1)`$ exactly, so $`D_n=(a_n-1)C_n`$ and $`E_n=0`$: the error measures deviation from the telescoping tail identity, and it vanishes identically on the Sylvester orbit.

In Lean, the elementary identities are stated for an abstract integer system, and their application to a rational reciprocal sum has separate statements, including [the product condition for a rational reciprocal sum](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos243/PaperCompleteR7/ProductDefect.lean#L211). This passage uses the [tail realisation](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1869), the [denominator realisation](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1881) and the [signed update](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1978).

Conversely, the recurrences identify a reciprocal sum when the ratio $`C_n/D_n`$ tends to zero. Regard that ratio as a real number, the [tail ratio](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1901). Assume $`a_n>0`$, $`D_n>0`$, $`C_{n+1}+D_n=a_nC_n`$ and $`D_{n+1}=a_nD_n`$. Dividing the numerator update by $`a_nD_n`$ gives $`C_n/D_n=1/a_n+C_{n+1}/D_{n+1}`$, the [one-step reciprocal identity](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1905). Iterating gives
``` math
\frac{C_0}{D_0}=\sum_{n<N}\frac1{a_n}+\frac{C_N}{D_N},
```
as in the [finite telescoping identity](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1929). If $`C_N/D_N\to0`$, taking the limit identifies $`\sum_n1/a_n=C_0/D_0`$, the [series realisation](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1955). No growth, error bound or separate rationality hypothesis is used in these three identities. Positivity and the stated limit of $`C_n/D_n`$ are still required. They prove the direction from recurrences to a series; the construction from a rational reciprocal sum was given above and is also formalised in separate declarations.

Under the relative-error hypothesis used below, the required limit is automatic. Suppose $`a_n>1`$, $`C_n>0`$, $`D_n\ge0`$ and $`E_n/C_n\to0`$ on an exact integer orbit. If $`D_0=0`$, then $`D_n=0`$ and $`E_n/C_n=1-a_n\le-1`$ at every index, a contradiction. Thus $`D_0\ge1`$ and $`D_n\ge D_0 2^n`$. For each $`\varepsilon>0`$, the update gives $`C_{n+1}\le(1+\varepsilon)C_n`$ eventually. Taking $`0<\varepsilon<1`$ shows that $`C_n/D_n\to0`$, so the telescoping identity realises the reciprocal sum as $`C_0/D_0`$.

The same assumptions also imply the quadratic growth limit. Put $`\theta_n=E_n/C_n`$. Then $`a_n=D_n/C_n+1-\theta_n\to\infty`$, and the exact recurrences give
``` math
\frac{a_{n+1}}{a_n^2}
 =\frac1{1-\theta_n}-\frac1{a_n}
   +\frac{1-\theta_{n+1}}{a_n^2}\longrightarrow1.
```
In particular, the multipliers are strictly increasing eventually. Thus a global orbit with these positivity and relative-error assumptions already gives a sequence of the type in Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a> after deletion of a finite prefix. No separate tail-limit estimate is needed for such an orbit; without the relative-error assumption, that estimate remains a condition of the general telescoping argument.

<div id="long243:res:scale" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Arithmetic.lean#L31">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-scale-comparator">Comparator</a></p>

**Proposition 16** (scaling the numerator and denominator). *For every $`s,a,D,C\in\mathbb{Z}`$,
``` math
a(sD)=s\,(aD),\qquad
 a(sC)-sD=s\,(aC-D),
```
``` math
sD-(a-1)sC=s\,[D-(a-1)C].
```*

</div>

Multiplying the numerator and denominator by the same factor therefore preserves the recurrence and scales the error by that factor. When the factor divides all entries, we can divide it out instead. This is used in the finite calculation of Appendix <a href="#long243:app:residue" data-reference-type="ref" data-reference="long243:app:residue">16</a> and in the induction in Theorem <a href="#long243:res:periodic" data-reference-type="ref" data-reference="long243:res:periodic">45</a>.

<a id="long243:sec:defect"></a>

# Zero errors and the Sylvester recurrence

To recover the Sylvester recurrence from a zero error, we eliminate $`D_n`$ between two successive updates. Write
``` math
\Delta_n=a_{n+1}-(a_n^2-a_n+1),
```
the [Sylvester defect](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L53). The identity below expresses $`\Delta_nC_{n+1}`$ through two consecutive errors. If both errors vanish, positivity lets us cancel $`C_{n+1}`$ and recover the recurrence. Under the bound $`|E_n|<C_n`$, it will also make a single zero propagate to the next index.

<div id="long243:res:defect" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1775">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-defect-comparator">Comparator</a></p>

**Theorem 17** (defect identity). *For all $`a,a',D,C\in\mathbb{Z}`$,
``` math
\begin{aligned}
 \relax[a'-(a^2-a+1)]\,(aC-D)
 &=a^2[D-(a-1)C]\\
 &\quad-\bigl[aD-(a'-1)(aC-D)\bigr],
 \end{aligned}
```
that is, $`\Delta_n\,C_{n+1}=a_n^{2}E_n-E_{n+1}`$.*

</div>

<div class="proof">

*Proof.* A direct expansion: both sides equal $`a'aC-a'D-a^{3}C+a^{2}D+a^{2}C-aD-aC+D`$. ◻

</div>

No sign or growth hypothesis is needed for the identity itself. Such hypotheses enter only in its consequences below.

<div id="long243:ex:defect" class="example">

**Example 18** (one defect and the error it creates). Continue Example <a href="#long243:ex:sylvester" data-reference-type="ref" data-reference="long243:ex:sylvester">15</a> but replace $`a_3=43`$ by $`a_3=44`$. The states $`D_3=42`$ and $`C_3=1`$ are unchanged, since they depend only on $`a_0,a_1,a_2`$, and $`E_2=0`$ still. The defect is $`\Delta_2=a_3-(a_2^2-a_2+1)=44-43=1`$, and $`E_3=D_3-(a_3-1)C_3=42-43=-1`$, so the identity reads
``` math
\Delta_2C_3=1\cdot1=1=49\cdot0-(-1)=a_2^{2}E_2-E_3 .
```
By Proposition <a href="#long243:res:update" data-reference-type="ref" data-reference="long243:res:update">14</a> the numerator then rises, $`C_4=C_3-E_3=2`$. A single unit of defect at one index has produced a negative error of magnitude $`1`$ at the next, increasing the numerator from $`1`$ to $`2`$.

</div>

<div id="long243:res:step" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1787">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-step-comparator">Comparator</a></p>

**Theorem 19** (two vanishing errors force the step). *Let $`a,a',D,C\in\mathbb{Z}`$ with $`aC-D\ne0`$. If
``` math
D-(a-1)C=0,\qquad aD-(a'-1)(aC-D)=0,
```
then $`a'=a^2-a+1`$.*

</div>

<div class="proof">

*Proof.* Theorem <a href="#long243:res:defect" data-reference-type="ref" data-reference="long243:res:defect">17</a> gives $`[a'-(a^2-a+1)]\,(aC-D)=0`$. The second factor is nonzero, so the first factor must vanish. ◻

</div>

The hypothesis $`C_{n+1}\ne0`$ is not removable: at $`C_{n+1}=0`$ the identity gives no information about $`a'`$.

<a id="relations-among-three-consecutive-numerators"></a>

## Relations among three consecutive numerators

Eliminating the denominator from two successive steps gives a relation among three reduced numerators. Write $`u,u_1,u_2`$ for the reduced numerator coordinates, $`v,v_1`$ for the corresponding denominator coordinates, and $`h,h_1`$ for the two common factors removed in reduction. If the two steps have multipliers $`a,a_1`$, then the exact hypotheses are
``` math
hu_1+v=au,\qquad hv_1=av,\qquad
 h_1u_2+v_1=a_1u_1.
```

<div id="long243:res:secondorder" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Arithmetic.lean#L42">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-secondorder-comparator">Comparator</a></p>

**Theorem 20** (eliminating the denominator from two steps). *Let $`a,a_1,u,u_1,u_2,v,v_1,h,h_1`$ be integers satisfying
``` math
hu_1+v=au,\qquad hv_1=av,\qquad h_1u_2+v_1=a_1u_1.
```
Then $`a^2u+hh_1u_2=h(a+a_1)u_1`$.*

</div>

<div class="proof">

*Proof.* Multiply the first equation by $`a`$, replace $`av`$ using the second equation, and then replace $`h_1u_2+v_1`$ using the third. The remaining terms factor as the displayed right-hand side. ◻

</div>

This is the [recurrence obtained by eliminating the denominator](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/DynamicCancellation.lean#L270). Both cancellation factors remain in the formula. The identity adds no assumption to the two exact steps, but it still contains both multipliers and cannot by itself force $`a_1=a^2-a+1`$; Lemma <a href="#long243:res:oldmodulussaturation" data-reference-type="ref" data-reference="long243:res:oldmodulussaturation">22</a> specifies what it forgets modulo a fixed old denominator.

When neither step cancels a common factor, the same recurrence gives a square identity. Write $`p,p_1,p_2`$ for three consecutive numerators, $`q=ap-p_1`$ for the denominator before the first step, and $`a,a_1`$ for the two multipliers. Then
``` math
p_2+a^2p=(a+a_1)p_1.
```
The resulting square identity is as follows.

<div id="long243:res:curvature" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/DynamicCancellation.lean#L309">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-curvature-comparator">Comparator</a></p>

**Theorem 21** (a square identity without cancellation). *Let $`a,a_1,p,p_1,p_2,q`$ be integers with $`q=ap-p_1`$ and $`p_2+a^2p=(a+a_1)p_1`$. Then
``` math
q^2+\bigl(pp_2-p_1^2\bigr)=(a_1-a)pp_1.
```*

</div>

<div class="proof">

*Proof.* Substitute $`q=ap-p_1`$ and $`p_2=(a+a_1)p_1-a^2p`$:
``` math
\begin{aligned}
 q^2+pp_2-p_1^2
 &=(ap-p_1)^2+p\bigl((a+a_1)p_1-a^2p\bigr)-p_1^2\\
 &=(a_1-a)pp_1.
 \end{aligned}
```
 ◻

</div>

The term $`q^2`$ is nonnegative, while $`pp_2-p_1^2`$ measures the difference between the product of the outer numerators and the square of the middle one. The right side records the change in multiplier, so the identity gives a necessary algebraic constraint without asserting a sign or a global monotonicity. It is checked as [the square identity when no factor is cancelled](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/DynamicCancellation.lean#L309); no global exclusion of approximate solutions is claimed.

The reduced error update must also be compatible with the denominator recurrence. The following calculation gives the exact compatibility condition. Here $`e,e_1`$ are signed errors in reduced coordinates, not the positive magnitudes denoted by $`e_n`$ in the all-negative case. Let $`\Delta`$ be a proposed value of the Sylvester defect. If
``` math
hu_1=u-e,
 \qquad he_1=a^2e-\Delta(u-e),
```
then the denominator equality
``` math
h\bigl((a_1-1)u_1+e_1\bigr)
   =a\bigl((a-1)u+e\bigr)
```
holds precisely when the following difference vanishes:
``` math
\begin{aligned}
 &h\bigl((a_1-1)u_1+e_1\bigr)-a\bigl((a-1)u+e\bigr)\\
 &\qquad=\bigl[a_1-(a^2-a+1)-\Delta\bigr]\,(u-e).
 \end{aligned}
```
Consequently, when $`u-e\ne0`$,
``` math
h\bigl((a_1-1)u_1+e_1\bigr)
   =a\bigl((a-1)u+e\bigr)
 \quad\Longleftrightarrow\quad
 a_1=a^2-a+1+\Delta.
```
The [equivalence with the denominator recurrence](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/FeedbackRealizability.lean#L64) is formalised using the [factored difference between the two recurrences](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/FeedbackRealizability.lean#L15). The hypothesis $`u-e\ne0`$ is essential: if $`u-e=0`$, the factorised mismatch cannot identify $`a_1`$.

The identities hold under the local hypotheses displayed in their statements. It is their proposed global applications, not the identities, that would need additional information, such as control of cancellation or a sign estimate for $`pp_2-p_1^2`$. No such information is deduced here for an arbitrary rational near-quadratic tail.

<div id="long243:res:oldmodulussaturation" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/ReducedStepLocalArithmetic.lean#L39">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-oldmodulussaturation-comparator">Comparator</a></p>

**Lemma 22** (saturation modulo an old denominator). *Let $`M\ge2`$. Any finite word $`r_0,\ldots,r_k`$ of units modulo $`M`$ is compatible with the cancellation-free recurrences modulo $`M`$, with all reduced denominator residues equal to zero. Consequently the eliminated two-step identity alone imposes no further restriction on such unit words when the multiplier residues are free.*

</div>

<div class="proof">

*Proof.* Set $`v_i\equiv0\pmod M`$ and choose $`a_i\equiv r_{i+1}r_i^{-1}\pmod M`$. Then $`r_{i+1}+v_i\equiv a_ir_i`$ and $`v_{i+1}\equiv a_iv_i`$. Eliminating $`v_i`$ gives the two-step identity automatically. ◻

</div>

This is finite residue compatibility, not existence of a positive integer orbit, much less a rational tail with near-quadratic growth. For $`M\mid v_T`$ on a tail with no further common-factor cancellation, the actual $`u_n`$ are indeed units modulo $`M`$. Useful further restrictions must therefore retain information discarded here: for example multiplier size, changing moduli, or primes outside the old denominator. The square restriction used in the cubic proof concerns precisely a prime at which a middle numerator vanishes.

<div id="long243:res:eventual" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1805">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-eventual-comparator">Comparator</a></p>

**Theorem 23** (sequence form). *Let $`a,D,C:\mathbb{N}\to\mathbb{Z}`$ satisfy $`D_{n+1}=a_nD_n`$ and $`C_{n+1}=a_nC_n-D_n`$. If $`E_n=0`$ for all sufficiently large $`n`$ and $`C_{n+1}\ne0`$ for all sufficiently large $`n`$, then $`a_{n+1}=a_n^{2}-a_n+1`$ for all sufficiently large $`n`$.*

</div>

Take the larger of the two thresholds and apply Theorem <a href="#long243:res:step" data-reference-type="ref" data-reference="long243:res:step">19</a> at each later index. This is the final step of the criteria below that force $`E_n`$ to vanish eventually.

The same identity shows that a zero error persists whenever $`|E_n|<C_n`$ at the subsequent indices.

<div id="long243:res:absorb" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2227">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-absorb-comparator">Comparator</a></p>

**Theorem 24** (zero is absorbing). *Let $`a,C,D:\mathbb{N}\to\mathbb{N}`$ satisfy $`C_{n+1}+D_n=a_nC_n`$ and $`D_{n+1}=a_nD_n`$, and put $`E_n=D_n-(a_n-1)C_n`$. Suppose that $`|E_n|<C_n`$ for every $`n`$. If $`E_n=0`$ then $`E_{n+1}=0`$.*

</div>

<div class="proof">

*Proof.* Putting $`E_n=0`$ in Theorem <a href="#long243:res:defect" data-reference-type="ref" data-reference="long243:res:defect">17</a> gives $`\Delta_n C_{n+1}=-E_{n+1}`$, so $`C_{n+1}`$ divides $`E_{n+1}`$. A multiple of $`C_{n+1}`$ of absolute value smaller than $`C_{n+1}`$ is zero, and $`|E_{n+1}|<C_{n+1}`$ by hypothesis. ◻

</div>

Beyond an index from which $`|E_n|<C_n`$ always holds, either $`E_n`$ reaches zero and remains zero, or it is never zero. A zero at an earlier index need not persist: in Example <a href="#long243:ex:defect" data-reference-type="ref" data-reference="long243:ex:defect">18</a>, the altered multiplier gives $`E_3=-1`$ and $`C_3=1`$, so the required strict inequality fails. Sections <a href="#long243:sec:constant" data-reference-type="ref" data-reference="long243:sec:constant">9</a> and <a href="#long243:sec:periodic" data-reference-type="ref" data-reference="long243:sec:periodic">10</a> address the special all-negative case. The mixed-sign analysis in Sections <a href="#long243:sec:bounded" data-reference-type="ref" data-reference="long243:sec:bounded">12</a> and <a href="#long243:sec:mass" data-reference-type="ref" data-reference="long243:sec:mass">13</a> separates arbitrarily late negative errors from an eventually nonnegative tail.

<div id="243-long-weighted-records">

</div>

<a id="long243:sec:lcmrecords"></a>

# LCM numerators and weighted records

Clearing a rational tail by an LCM removes repeated denominator factors, but need not make its numerator coprime to that LCM. The argument here therefore forbids short crossings, not numerator values. It characterises boundedness by a weighted sum over new maxima, even after subtracting a fixed amount at each record. The error may have either sign, extending the setting of Koizumi’s eventual-nonnegative case in Proposition 1(2).

Applied to rational tails, this gives a Sylvester recurrence criterion. Its convergence hypothesis remains unproved for the unrestricted problem. The whole-modulus avoidance model in Proposition <a href="#long243:res:coprimalitycap" data-reference-type="ref" data-reference="long243:res:coprimalitycap">41</a> omits the denominator recurrence and prime-factor coprimality; its examples therefore do not contradict the criterion.

In this section the indices start at $`0`$. Write the full reciprocal sum as $`p/q`$, with positive integers $`p,q`$, put $`x_n=\sum_{k\ge n}1/a_k`$, and take $`D_0=q`$. Set
``` math
L_n=\operatorname{lcm}(q,a_0,\ldots,a_{n-1}),\quad
 M_n=D_n/L_n,\quad U_n=L_nx_n=C_n/M_n,\quad V_n=E_n/M_n.
```
The rational tail has denominator dividing $`L_n`$, so $`U_n`$ is an integer. Also $`V_n=L_n-(a_n-1)U_n\in\mathbb{Z}`$. This clears the denominator but need not reduce the fraction: $`U_n`$ and $`L_n`$ may still have common factors. With $`\rho_n=\gcd(L_n,a_n)`$, the exact updates are
``` math
M_{n+1}=M_n\rho_n,\qquad
 \rho_nU_{n+1}=U_n-V_n,\qquad V_n=L_n-(a_n-1)U_n.
```
These are Bado’s LCM coordinates, with the indexing translated explicitly. Take his denominator parameter to be $`q`$ and identify his $`a_{n+1}`$ with our $`a_n`$. Then his $`M_n`$, $`\Delta_n`$, $`K_n`$, $`u_{n+1}`$ and $`g_{n+1}`$ are respectively our $`L_n`$, $`M_n`$, $`U_n`$, $`V_n`$ and $`\rho_n`$. His (19) becomes the middle update above \[bado2026, Prop. 7.1 and (16)–(20), pp. 6–7\].

Write $`R_n=\max_{j\le n}U_j`$ and $`\mathcal R=\{n:U_{n+1}>R_n\}`$. The inequality $`|V_n|<U_n`$ gives $`U_{n+1}<U_n`$ when $`\rho_n\ge2`$, so every sufficiently late strict rise has $`\rho_n=1`$. The stronger eventual bound $`-U_n\le2V_n`$, supplied by $`V_n/U_n=E_n/C_n\to0`$, gives the quantitative estimate $`U_{n+1}\le3U_n/4`$ when $`\rho_n\ge2`$. Repeated factors thus cause contraction; late records use multipliers coprime to the current LCM. At those records the actual jump is $`d_n=U_{n+1}-U_n=-V_n>0`$. This identity need not hold when $`\rho_n\ge2`$.

For $`B=0`$, divergence under unbounded growth can already be seen by comparing a record step with the interval of new heights it covers:
``` math
\int_{R_n}^{R_{n+1}}f(t)\,dt
 \le (R_{n+1}-R_n)f(U_n)
 \le (U_{n+1}-U_n)f(U_n).
```
The last expression is $`(-V_n)f(U_n)`$ at a record. The theorem retains this divergence after subtracting a fixed $`B`$ at every record. That is where the congruences enter: they select a progression of heights whose first crossings necessarily have an excess jump. For the divergence direction, unboundedness of $`U_n`$ suffices; no limit $`U_n\to\infty`$ is assumed.

<div id="long243:res:arithmeticrecord" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR11/ArithmeticWeightedRecord.lean#L264">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-arithmeticrecord-comparator">Comparator</a></p>

**Theorem 25** (boundedness and a weighted sum over new maxima). *Let $`a_n,L_n,U_n`$ be positive integers and $`V_n`$ integers satisfying
``` math
\begin{gathered}
 L_{n+1}=\operatorname{lcm}(L_n,a_n),\qquad \rho_n=\gcd(L_n,a_n),\\
 \rho_nU_{n+1}=U_n-V_n,\qquad
 V_n=L_n-(a_n-1)U_n,\qquad -U_n\le2V_n.
 \end{gathered}
```
Let $`f:[1,\infty)\to[0,\infty)`$ be finite and nonincreasing, with $`\int_1^\infty f(t)\,dt=\infty`$. For each fixed integer $`B\ge0`$,
``` math
\sup_n U_n<\infty
 \quad\Longleftrightarrow\quad
 \sum_{n\in\mathcal R}(-V_n-B)_+f(U_n)<\infty.
```*

</div>

<div class="proof">

*Proof.* A bounded integer running maximum increases only finitely many times, so bounded $`U_n`$ gives a finite sum. Suppose instead that $`U_n`$ is unbounded. There are infinitely many record rises, each with $`\rho_n=1`$. Its multiplier is greater than one because $`d_n=(a_n-1)U_n-L_n>0`$. If $`r<s`$ are record indices, then $`a_r\mid L_s`$ and $`\gcd(a_s,L_s)=1`$, hence $`\gcd(a_r,a_s)=1`$. The record multipliers are therefore distinct and pairwise coprime. For any fixed $`B\ge1`$, choose $`B`$ of them greater than $`B`$, and take $`T`$ after their indices. These earlier multipliers $`m_0,\ldots,m_{B-1}`$ all divide $`L_T`$.

Put $`P=\prod_i m_i`$ and choose $`x`$ with $`m_i\mid x+i`$ by the Chinese remainder theorem. Select the heights $`\tau=x+B+kP>R_T`$, $`k\in\mathbb{Z}`$. At the first crossing of any selected height we have $`U_n\le R_n<\tau\le U_n+d_n`$, so the crossing is a record step. Here $`d_n=U_{n+1}-U_n`$ is the full jump from the current numerator. If $`d_n\le B`$, then $`U_n\in[\tau-B,\tau)`$, so
``` math
U_n=\tau-B+i=x+kP+i\qquad\text{for some }0\le i<B.
```
The choice of $`x`$ gives $`m_i\mid U_n`$, which is compatible with these unreduced LCM coordinates. Since $`m_i\mid L_n`$ too, it also gives $`m_i\mid d_n=(a_n-1)U_n-L_n`$. The contradiction is $`0<d_n\le B<m_i`$: the jump is too short to be a positive multiple of the modulus.

Every crossing has $`d_n>B`$. We must still avoid counting one excess several times when a jump crosses more than one selected height: their combined weight must fit within that same $`d_n-B`$. If it first crosses $`h\ge1`$ selected heights, their spacing gives $`(h-1)P<d_n`$. Writing $`r=d_n-B\ge1`$ and using $`P\ge B+1`$, we obtain $`d_n=B+r\le Pr`$, hence $`h\le r`$. Since each crossed height is above $`U_n`$, monotonicity of $`f`$ gives
``` math
\sum_{\substack{\tau\text{ first crossed}\\\text{at step }n}}f(\tau)
 \le(d_n-B)f(U_n).
```
Each selected height has one first crossing. The first is at most $`R_T+P`$, and successive selected heights are $`P`$ apart. For $`R_N\ge R_T+P`$, the intervals $`[\tau,\min\{\tau+P,R_N\}]`$, over selected heights $`\tau\le R_N`$, cover $`[R_T+P,R_N]`$. Since $`f`$ is nonincreasing, its integral over each interval is at most $`P f(\tau)`$. Summing the crossing bounds gives
``` math
\begin{equation}
\label{long243:eq:weightedcrossing}
 \sum_{\substack{T\le n<N\\n\in\mathcal R}}(-V_n-B)_+f(U_n)
 \ge\frac1P\int_{R_T+P}^{R_N} f(t)\,dt.
\end{equation}
```
Since $`R_n\to\infty`$, the right side diverges for every $`B\ge1`$. The case $`B=0`$ follows by domination. ◻

</div>

The abstract theorem used only unboundedness, not $`U_n\to\infty`$: record multipliers supplied the CRT moduli, and the stated error bound excluded records with $`\rho_n\ge2`$. For reciprocal tails, vanishing relative error and absorption supply the missing alternative: failure of Sylvester behaviour forces $`U_n\to\infty`$.

<div id="long243:res:weightedrecord" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR11/CanonicalRecords.lean#L202">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-weightedrecord-comparator">Comparator</a></p>

**Theorem 26** (a convergent weighted sum over new maxima). *Assume the growth and rationality hypotheses of Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>, and let $`f`$ be as in Theorem <a href="#long243:res:arithmeticrecord" data-reference-type="ref" data-reference="long243:res:arithmeticrecord">25</a>. The sequence is eventually Sylvester if and only if, for some integer $`B\ge0`$,
``` math
\sum_{n\in\mathcal R}(-V_n-B)_+f(U_n)<\infty.
```*

</div>

<div class="proof">

*Proof.* If the sequence is not eventually Sylvester, zero error is never reached on a sufficiently late tail. Integrality gives $`1/U_n\le|V_n|/U_n=|E_n|/C_n\to0`$, so $`U_n`$ is unbounded. The same relative-error limit gives $`2|V_n|<U_n`$ at every sufficiently large index, and hence the bound $`-U_n\le2V_n`$ required by Theorem <a href="#long243:res:arithmeticrecord" data-reference-type="ref" data-reference="long243:res:arithmeticrecord">25</a>. Applying that theorem to this tail forces divergence for every $`B`$. Once the running maximum of the retained tail exceeds the omitted prefix maximum, deleting that prefix no longer changes which steps set new records. Unboundedness ensures that this crossing occurs. Conversely, a sequence satisfying the eventual Sylvester recurrence telescopes to $`x_n=1/(a_n-1)`$, so $`V_n=0`$ eventually. ◻

</div>

The nonincreasing weights $`1/t`$ and $`1/[t\log(et)]`$ have divergent integrals and are admissible. The weight $`1/t^2`$ is excluded: its integral is finite, so the crossing lower bound would not contradict unbounded numerators. For example, $`f(t)=1/[t\log(et)]`$ gives the sufficient condition
``` math
\sum_{n\in\mathcal R}\frac{(-V_n-B)_+}{U_n\log(eU_n)}<\infty.
```
Its finite lower bound in <a href="#long243:eq:weightedcrossing" data-reference-type="eqref" data-reference="long243:eq:weightedcrossing">[long243:eq:weightedcrossing]</a> is $`P^{-1}\log\bigl(\log(eR_N)/\log(e(R_T+P))\bigr)`$. Further fixed iterated logarithmic factors are allowed whenever the integral still diverges. These are specialisations of one crossing theorem.

Transferring the criterion to the growth defect requires a summable change in the summands, not merely a pointwise asymptotic. Put $`\gamma_n=a_n^2/a_{n+1}-1`$ and $`\theta_n=E_n/C_n`$. The defect identity gives
``` math
\gamma_n+\theta_n=
 \frac{(1-\theta_n)(a_n-1+\theta_{n+1})}{a_{n+1}},
 \qquad 0<\gamma_n+\theta_n<3/a_n
```
eventually. Taking positive parts cannot increase the absolute difference. Since $`V_n=U_n\theta_n`$, the two nonnegative summands $`U_nf(U_n)(\gamma_n-B/U_n)_+`$ and $`(-V_n-B)_+f(U_n)`$ differ by at most $`3U_nf(U_n)/a_n`$. To see summability directly, put $`P_n=\prod_{j<n}a_j`$. The tail estimate $`x_n\sim1/a_n`$ gives $`C_n/a_n\sim qP_n/a_n^2`$, and
``` math
\frac{P_{n+1}/a_{n+1}^{2}}{P_n/a_n^{2}}
 =\frac{a_n^3}{a_{n+1}^{2}}\longrightarrow0.
```
Thus $`\sum_n C_n/a_n<\infty`$ by the ratio test. Since $`U_n\le C_n`$ and $`f(U_n)\le f(1)`$, the comparison error is summable. Consequently Theorem <a href="#long243:res:weightedrecord" data-reference-type="ref" data-reference="long243:res:weightedrecord">26</a> is equivalent to finiteness of
``` math
\begin{equation}
\label{long243:eq:weightedgrowth}
 \sum_{n\in\mathcal R}U_nf(U_n)
 \left(\frac{a_n^2}{a_{n+1}}-1-\frac B{U_n}\right)_+
\end{equation}
```
for some $`B`$. The original hypotheses do not currently supply this finiteness. In particular, termwise convergence to zero is insufficient. A Lean formulation of this comparison, with the sufficient constant $`16`$ in place of $`3`$ and the summand of <a href="#long243:eq:weightedgrowth" data-reference-type="eqref" data-reference="long243:eq:weightedgrowth">[long243:eq:weightedgrowth]</a> at record indices and zero elsewhere, is in the companion Lean repository [`plectis-erdos-lean`](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos243/PaperCompleteR8/GrowthDebtSummability.lean#L234); it is not covered by the evidence record.

The crossed heights lie above $`R_n`$, but the divisibility argument uses the starting numerator $`U_n`$ and the full jump $`U_{n+1}-U_n`$. Replacing this by $`R_{n+1}-R_n`$ would discard the recovery from an earlier decrease.

<a id="integer-coefficients."></a>

#### Integer coefficients.

The first-crossing proof extends to summands with arbitrary integer numerators $`b_n`$. We record this extension separately from the unit-fraction criteria used above. In that case
``` math
V_n=b_nL_n-(a_n-1)U_n,\qquad
 \rho_nU_{n+1}=U_n-V_n.
```
Assume that $`a_n\ge2`$, that $`L_n,U_n`$ are positive integers, and that $`L_{n+1}=\operatorname{lcm}(L_n,a_n)`$, with $`\rho_n=\gcd(L_n,a_n)`$. Suppose $`V_n\ge-B`$ eventually, with an integer $`B\ge0`$. Then $`U_{n+1}\le U_n+B`$; if $`B=0`$, boundedness follows at once. For $`B\ge1`$, a record step with $`R_n>B`$ must have $`\rho_n=1`$, since $`\rho_n\ge2`$ would give
``` math
U_{n+1}\le\frac{U_n+B}{2}\le\frac{R_n+B}{2}<R_n.
```
Thus an unbounded sequence would supply infinitely many pairwise coprime record multipliers. Choose $`B`$ of them larger than $`B`$, and then a CRT block of $`B`$ consecutive integers above the previous maximum, each divisible by one of the chosen multipliers. The first step past the upper end of the block is a high record step, so $`\rho_n=1`$. Its positive jump is at most $`B`$, hence the preceding numerator $`U_n`$ lies in the block. The corresponding multiplier divides both $`U_n`$ and $`L_n`$, hence divides the jump $`(a_n-1)U_n-b_nL_n`$. A positive jump at most $`B`$ cannot have a divisor larger than $`B`$. No growth or relative-error hypothesis was used.

With the additional limit $`V_n/U_n\to0`$, choose an integer $`K`$ bounding $`U_n`$. Eventually $`|V_n|<U_n/K\le1`$, so the integer $`V_n`$ is zero. The recurrence becomes $`\rho_nU_{n+1}=U_n`$; the positive integer sequence $`U_n`$ is then nonincreasing and hence eventually constant. For positive $`b_n`$, the classical comparisons are Badea’s Corollary 2.2 \[badea1993, p. 316\] and the criterion of Tijdeman and Yuan \[tijdemanyuan2002\]. Further finite examples separating boundedness from stationarity are in the [coefficient proof supplement](https://github.com/wcook04/plectis-erdos/blob/eccd8afc6db3c02a2265d0601b727d6c5e4467d5/lean/ErdosProblems/Erdos243/CoefficientUniformBoundedHeight.md).

<a id="long243:sec:records"></a>

# New maxima of reduced numerators

We now reduce each tail to lowest terms, writing $`u_n/v_n`$. Coprimality is restored, but persistence is lost: a prime power can disappear from $`v_n`$ while remaining in every later LCM $`L_j`$. Before applying coprimality at new maxima, we must therefore bound what cancellation removes. Lower-case $`u_n`$ is the reduced numerator; upper-case $`U_n`$ remains the LCM numerator of the preceding section.

<a id="fractions-in-lowest-terms."></a>

#### Fractions in lowest terms.

Put
``` math
G_n=\gcd(C_n,D_n),\qquad u_n=C_n/G_n,\qquad v_n=D_n/G_n,
 \qquad \tilde e_n=E_n/G_n.
```
Thus $`\gcd(u_n,v_n)=1`$ and $`\tilde e_n`$ is a signed integer. The factor $`h_n=G_{n+1}/G_n`$ records the common factor removed at the next step. The relation to the preceding section is exact:
``` math
\frac{G_n}{M_n}=\gcd(U_n,L_n),\qquad
 u_n=\frac{U_n}{\gcd(U_n,L_n)},\qquad
 v_n=\frac{L_n}{\gcd(U_n,L_n)}.
```
Indeed, $`C_n=M_nU_n`$ and $`D_n=M_nL_n`$. Clearing with an LCM and reducing to lowest terms are different operations. For example, the exact step $`(C,D,a)=(3,6,3)`$ has $`E=0`$ and gives $`(C',D')=(3,18)`$. With $`L=6`$, its LCM numerator falls from $`3`$ to $`1`$, while the reduced numerator stays $`1`$: the LCM factor is $`\rho=3`$, but the reduction factor is $`h=1`$. From this step onwards, the Sylvester recurrence holds.

In general, before reduction the next numerator is $`w_n=a_nu_n-v_n=u_n-\tilde e_n`$, so
``` math
h_nu_{n+1}=w_n,\qquad h_nv_{n+1}=a_nv_n,\qquad
 \gcd(u_n,u_{n+1})=1.
```
The negative magnitude $`e_n=-E_n`$ used earlier is not $`\tilde e_n`$; neither is Koizumi’s real gap $`\varepsilon_n`$.

For the maxima and their increments write
``` math
R_n=\max_{k\le n}u_k,\qquad H_n=\max_{j\le n}C_j,
 \qquad s_n=R_{n+1}-R_n.
```
At a strict rise let $`d_n=u_{n+1}-u_n`$. Then $`s_n=(d_n-(R_n-u_n))_+`$. Thus the actual jump includes recovery of the earlier decrease $`R_n-u_n`$, whereas the record increment does not. For example, if $`R_n=10`$, $`u_n=5`$ and $`u_{n+1}=12`$, then $`s_n=2`$ but $`d_n=7`$. This illustrates the definitions, not a claimed reciprocal-tail orbit. We will use
``` math
m_n=(-\tilde e_n)_+,\qquad \mathcal A_n=\frac{R_n}{u_n}m_n,
 \qquad \delta_n=\left(\frac{a_n^2}{a_{n+1}}-1\right)_+,
 \qquad \ell(x)=\log_2\log_2\max(4,x).
```
The factor $`R_n/u_n`$ in $`\mathcal A_n`$ measures how far the current numerator has fallen below its previous maximum. It equals one at a maximum and can be large after a decrease. The symbol $`\mathcal A_n`$ is distinct from the prefix product $`A_n`$ used later.

Unless a statement in this section specifies an abstract recurrence, we assume the hypotheses of Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a> and use its integer tails, for which $`|E_n|/C_n\to0`$ after a finite shift. We will write out the conclusion $`a_{n+1}=a_n^2-a_n+1`$ eventually rather than give it a separate symbol.

<a id="comparison-with-duverneys-reduced-parameters."></a>

#### Comparison with Duverney’s reduced parameters.

For the positive reciprocal series, the eventually reduced parameters in Duverney’s Theorem 3.1 and Section 5.2 \[duverney2001, pp. 285–286, 299–300\] can be taken as follows. The symbols $`p_n,q_n`$ in this comparison are Duverney’s auxiliary integers, not the fixed numerator and denominator of the full reciprocal sum:
``` math
p_n=u_n,\qquad q_n=w_n=a_nu_n-v_n=h_nu_{n+1},\qquad
 E_n=G_n(p_n-q_n).
```
Indeed, $`\gcd(u_n,w_n)=\gcd(u_n,v_n)=1`$. Since $`a_nv_n=a_n^2u_n-a_nw_n`$, reduction of the next tail gives
``` math
h_n=\gcd(w_n,a_nv_n)=\gcd(w_n,a_n^2),\qquad
 p_{n+1}\mid q_n.
```
For the gcd equality, subtract the multiple $`a_nw_n`$ and use the coprimality of $`u_n,w_n`$; the divisibility follows from $`q_n=h_np_{n+1}`$. Eliminating $`v_{n+1}`$ then gives Duverney’s recurrence:
``` math
a_{n+1}=\frac{p_n}{q_n}a_n^2-a_n+\frac{q_{n+1}}{p_{n+1}}.
```
Thus $`q_n/p_{n+1}=h_n`$ is precisely the cancellation factor, and $`q_n/p_n\to1`$. This identifies the reduced parameters, not every possible unreduced choice in the original theorem. An upper bound on $`q_n-p_n`$ controls the increase before cancellation in the reduced coordinates. To transfer that bound directly to $`(-E_n)_+=G_n(q_n-p_n)_+`$ would also require control of $`G_n`$.

An old prime power can be lost only when the multiplier supplies exactly its exponent and subtraction cancels more. The formula below separates this case from unequal exponents.

<div id="long243:res:valuationtransition" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-valuationtransition">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-valuationtransition-comparator">Comparator</a></p>

**Lemma 27** (the denominator valuation transition). *Let $`u,v,a`$ be positive integers, $`\gcd(u,v)=1`$, and $`w=au-v>0`$. Put $`h=\gcd(w,av)`$ and $`v'=av/h`$. For a prime $`p`$, write $`r=\nu_p(a)`$, $`s=\nu_p(v)`$ and $`t=\nu_p(w)`$. Then
``` math
\nu_p(v')=
 \begin{cases}
 \max(r,s),&r\ne s,\\
 \max(0,2s-t),&r=s.
 \end{cases}
```
In particular $`\nu_p(v')\le\max(r,s)`$. A strict loss relative to $`s`$ requires $`r=s\ge1`$ and $`t>s`$.*

</div>

<div class="proof">

*Proof.* Always $`\nu_p(v')=r+s-\min(t,r+s)`$. If $`r\ne s`$, primitivity implies $`t=\min(r,s)`$: when $`s>0`$, $`u`$ is a $`p`$-adic unit, and when $`s=0<r`$, $`v`$ is a unit. If $`r=s>0`$, both terms in $`au-v`$ are divisible by $`p^s`$, so $`t\ge s`$; substituting gives the second case. If $`r=s=0`$, the same formula gives zero without needing $`u`$ to be a unit. ◻

</div>

Cancellation is measured against the enlarged denominator $`av`$, not against $`v`$. Thus $`h>1`$ need not mean that an old prime power is lost. For example, $`(u,v,a)=(2,15,9)`$ gives $`w=3`$, $`h=3`$ and $`(u',v')=(1,45)`$. The numerator before cancellation exceeds $`u`$ by only $`w-u=1`$, yet the $`3`$-adic valuation of the reduced denominator rises from $`1`$ to $`2`$. This is a finite exact step, not an infinite counterexample.

<div id="long243:res:powerpersistence" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR20/PowerPersistence.lean#L27">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-powerpersistence-comparator">Comparator</a></p>

**Corollary 28** (persistence of a prime power). *Suppose $`p^k\mid v_s`$. If $`w_n<p^{k+1}`$ at every step from $`s`$ through $`t-1`$, then $`p^k\mid v_t`$.*

</div>

<div class="proof">

*Proof.* At a first loss of divisibility by $`p^k`$, the current exponent is some $`j\ge k`$ and the valuation lemma forces $`\nu_p(w_n)>j`$. This would give $`w_n\ge p^{j+1}\ge p^{k+1}`$, contrary to the hypothesis. ◻

</div>

The bound on $`w_n`$ protects the old prime power despite varying cancellation factors. It is needed only until the crossing under study.

<a id="growth-of-the-running-maximum"></a>

## Growth of the running maximum

<div id="long243:res:recorddichotomy" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-recorddichotomy">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-recorddichotomy-comparator">Comparator</a></p>

**Theorem 29** (increments of the running maximum). *Let $`\Theta=\limsup_n(H_{n+1}-H_n)/\ell(H_n)`$ on a rational-tail orbit under the standing hypotheses, and suppose $`E_n`$ is not eventually zero. Then either $`G_n`$ is unbounded and $`\Theta`$ is infinite, or $`G_n`$ stabilises at a value $`g`$ and $`\Theta\ge g\,v_T/\varphi(v_T)`$ for every late $`T`$, so that $`\Theta>g\ge1`$. For any orbit under the standing hypotheses, therefore, $`\Theta=0`$ or $`\Theta>1`$, and $`\Theta\le1`$ forces the eventual Sylvester recurrence.*

</div>

The constant in the next condition is measured against a double logarithm, not against $`C_n`$. This grows much more slowly than any positive power of $`C_n`$. Every fixed bound on $`(-E_n)_+`$ satisfies it on a nonzero tail because $`C_n\to\infty`$; it also permits unbounded negative parts on the double-logarithmic scale, with the coefficient specified below. In contrast, an error of size $`\sqrt{C_n}`$ has relative size tending to zero but violates the condition. These are comparisons of bounds, not constructions of reciprocal tails.

<div id="long243:res:loglogboundary" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-loglogboundary">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-loglogboundary-comparator">Comparator</a></p>

**Corollary 30** (the double-logarithmic bound). *If
``` math
\limsup_n\frac{(-E_n)_+}{\ell(C_n)}\le1,
```
then the sequence is eventually Sylvester. Every counterexample therefore satisfies
``` math
\limsup_n\frac{(-E_n)_+}{\ell(C_n)}>1.
```*

</div>

<div class="proof">

*Proof of Theorem <a href="#long243:res:recorddichotomy" data-reference-type="ref" data-reference="long243:res:recorddichotomy">29</a> and Corollary <a href="#long243:res:loglogboundary" data-reference-type="ref" data-reference="long243:res:loglogboundary">30</a>.* We first prove the auxiliary lower bound $`\Theta\ge1`$. This part needs only an exact positive integer orbit with $`a_n>1`$, $`D_0\ge1`$, $`|E_n|/C_n\to0`$ and error not eventually zero. In particular, it will also apply to the abstract orbit in Theorem <a href="#long243:res:slownegative" data-reference-type="ref" data-reference="long243:res:slownegative">37</a>. The key input is that, outside a set of indices of density zero, $`a_n`$ is coprime to the entire preceding denominator $`D_n`$. This supplies almost one new coprime modulus per step. The denominator growth then places the resulting CRT block at the required double-logarithmic height.

*How often a multiplier is coprime to the preceding denominator.* We use the LCM factorisation from Section <a href="#long243:sec:lcmrecords" data-reference-type="ref" data-reference="long243:sec:lcmrecords">6</a>. In the present zero-based indexing, put
``` math
L_n=\operatorname{lcm}(D_0,a_0,\ldots,a_{n-1}),\qquad
 M_n=D_n/L_n,\qquad \rho_n=\gcd(L_n,a_n).
```
The finite telescoping identity gives
``` math
\frac{C_n}{M_n}
 =L_n\left(\frac{C_0}{D_0}-\sum_{j<n}\frac1{a_j}\right)
 \in\mathbb{Z}_{>0}.
```
Thus $`M_n\mid C_n`$, while $`M_0=1`$ and $`M_{n+1}=\rho_nM_n`$. Since $`L_n`$ and $`D_n`$ have the same prime divisors,
``` math
\#\{n<N:\gcd(a_n,D_n)>1\}
 =\#\{n<N:\rho_n>1\}
 \le\log_2M_N\le\log_2C_N=o(N).
```
Here the last estimate follows by summing $`\log(C_{n+1}/C_n)=\log(1-E_n/C_n)=o(1)`$. This is the density-one coprimality argument of Bado \[bado2026, Theorem 9.1, p. 7\], written with the exact-orbit hypotheses used here. Only the finite telescoping identity is needed; no estimate on record increments has entered this count.

*Choosing the moduli and controlling their product.* Absorption and vanishing relative error give $`C_n\to\infty`$, hence $`H_n\to\infty`$. The maximum is still subexponential: for every $`\varepsilon>0`$, choose $`K_\varepsilon`$ with $`C_j\le K_\varepsilon e^{\varepsilon j}`$ for every $`j`$. Then $`H_n\le K_\varepsilon e^{\varepsilon n}`$, so $`\log H_n=o(n)`$. Since $`D_n\ge2^n`$ and $`a_n=D_n/C_n+1-E_n/C_n`$, eventually
``` math
a_n\ge2^{n/2},\qquad a_n<2D_n,\qquad \ell(D_n)\le n+O(1).
```
For the last inequality, $`D_{n+1}<2D_n^2`$ gives $`1+\log_2D_{n+1}<2(1+\log_2D_n)`$. Iteration from a fixed late index, followed by another logarithm, gives $`\ell(D_n)\le n+O(1)`$.

Suppose $`H_{n+1}-H_n\le c\ell(H_n)`$ eventually for some $`0<c<1`$. For a large integer $`B`$, take the first $`B`$ indices at or after $`\lceil3\log_2B\rceil`$ for which $`\gcd(a_n,D_n)=1`$. Write the corresponding multipliers as $`m_0,\ldots,m_{B-1}`$ and let $`s`$ be the index immediately after the last choice. The density estimate just proved gives $`s=B+o(B)`$: deleting $`O(\log B)`$ initial indices and $`o(s)`$ exceptional indices leaves $`B`$ choices. Each $`m_i>2B`$ for large $`B`$, and the chosen multipliers are pairwise coprime, because each earlier one divides the denominator preceding a later one. All divide $`D_s`$. For $`P=\prod_i m_i`$ we therefore have
``` math
(2B)^B<P\le D_s,\qquad H_s<P,\qquad B<P,
 \qquad \ell(3P)\le B+o(B).
```
The bound on $`H_s`$ uses $`\log H_s=o(s)`$ and $`s=B+o(B)`$. Thus the product is large enough to place the block beyond the previous maximum, but small enough that the allowed jump at its height is less than the block length: $`c\ell(3P)<B`$ for all sufficiently large $`B`$. Both comparisons are needed; existence of a distant CRT block alone would not control a height-dependent jump bound.

*Crossing the block.* An unreduced numerator may land on a multiple. The modulus then becomes a persistent common divisor, forbidding the *next* small record. Choose $`x\in[P,2P)`$ by the Chinese remainder theorem so that $`m_i\mid x+i`$ for $`0\le i<B`$. At the first record $`C_t\ge x`$ after $`s`$, the preceding maximum is below $`x`$ and its increase is at most $`c\ell(2P)<B`$. Thus $`x\le C_t<x+B<3P`$, so some $`m_i`$ divides both $`C_t`$ and $`D_t`$. The exact updates preserve this common divisor. At the next record $`C_r`$ we would therefore have
``` math
m_i\mid C_r-C_t,\qquad
 0<C_r-C_t\le c\ell(C_t)\le c\ell(3P)<B<m_i,
```
which is impossible. This proves the auxiliary bound $`\Theta\ge1`$.

The integer normalisation matters here. Scaling $`(C,D,E)`$ by a positive integer $`k`$ scales the running maximum by $`k`$ and its limit-superior coefficient by $`k`$, since $`\ell(kx)/\ell(x)\to1`$. Thus the bound with coefficient $`1`$ is not invariant under arbitrary clearing of denominators. The next step keeps track of the common factor rather than discarding it.

*The common gcd and the sharper coefficient.* For any fixed $`N`$, divide the tail from $`N`$ onwards by $`G_N`$. The resulting integer orbit satisfies the same hypotheses. Its running maximum is eventually $`H_n/G_N`$, and $`\ell(H_n/G_N)/\ell(H_n)\to1`$. The auxiliary bound therefore gives $`\Theta\ge G_N`$. If $`G_N`$ is unbounded, then $`\Theta=+\infty`$.

Otherwise $`G_n=g`$ eventually. Fix a later index $`T`$ with $`v_T>1`$. The reduced fractions have pairwise coprime multipliers, each coprime to $`v_T`$. Its prime factors already exclude the nonunit offsets; new multipliers need cover only the rest. For a large integer $`L`$, exactly
``` math
k_L=\frac{\varphi(v_T)}{v_T}L+O(v_T)
```
of the offsets $`0,\ldots,L-1`$ are coprime to $`v_T`$. Assign to those offsets the next $`k_L`$ multipliers, beginning at $`T`$. Put $`s=T+k_L`$ and $`Q=v_s=v_T\prod_{T\le j<s}a_j`$. Solve $`x\equiv0\pmod{v_T}`$ and $`x\equiv-j`$ modulo the multiplier assigned to offset $`j`$, and take the solution in $`[Q,2Q)`$. Every integer in $`[x,x+L)`$ then fails to be coprime to $`v_s`$. No later reduced numerator can lie there.

The running maximum $`R_s`$ of the reduced numerator is below $`Q`$ for large $`L`$, by the growth estimates above. The first crossing of $`x`$ after $`s`$ must therefore have a record increment at least $`L`$. Its preceding maximum is below $`2Q`$, and $`\ell(2Q)\le s+O(1)=T+k_L+O(1)`$. The corresponding record indices tend to infinity with $`L`$, so
``` math
\limsup_n\frac{R_{n+1}-R_n}{\ell(R_n)}
 \ge\lim_{L\to\infty}\frac{L}{T+k_L+O(1)}
 =\frac{v_T}{\varphi(v_T)}.
```
Since $`H_n=gR_n`$ eventually, this gives $`\Theta\ge g v_T/\varphi(v_T)>g`$. Under the eventual Sylvester recurrence, $`C_n`$ is eventually constant and $`\Theta=0`$. Finally,
``` math
H_{n+1}-H_n=\bigl(-E_n-(H_n-C_n)\bigr)_+\le(-E_n)_+.
```
Together with $`\ell(C_n)\le\ell(H_n)`$, this proves the corollary. ◻

</div>

<a id="integer-solutions-of-the-recurrences."></a>

#### Integer solutions of the recurrences.

The strict bound $`\Theta>1`$ is also a Lean theorem for solutions of <a href="#long243:eq:recurrences" data-reference-type="eqref" data-reference="long243:eq:recurrences">[long243:eq:recurrences]</a> with $`a_n>1`$, $`C_n>0`$, $`D_0\ge1`$ and vanishing relative error whose error is not eventually zero ([strict record bound](https://github.com/wcook04/plectis-erdos/blob/168bf6727758f918a430ef056a1c93d3160b53a6/lean/ErdosProblems/Erdos243/PaperCompleteR21/ExactOrbitRecordDichotomy.lean#L363)). The implication of Corollary <a href="#long243:res:loglogboundary" data-reference-type="ref" data-reference="long243:res:loglogboundary">30</a>, that $`\limsup_n(-E_n)_+/\ell(C_n)\le1`$ forces $`E_n=0`$ eventually, is a Lean theorem for solutions of <a href="#long243:eq:recurrences" data-reference-type="eqref" data-reference="long243:eq:recurrences">[long243:eq:recurrences]</a> with $`a_n>1`$, $`C_n>0`$ and vanishing relative error ([double-logarithmic bound for an exact orbit](https://github.com/wcook04/plectis-erdos/blob/168bf6727758f918a430ef056a1c93d3160b53a6/lean/ErdosProblems/Erdos243/PaperCompleteR21/DoubleLogOrbitBound.lean#L45)); there $`D_0\ge1`$ follows from the vanishing relative error. The Lean sources also contain pointwise-rise versions of the arithmetic steps: [persistence of a common divisor](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SlowRiseBarrier.lean#L111), a [CRT block starting in $`[P,2P)`$](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SlowRiseBarrier.lean#L51), the [landing of a slowly rising numerator in that block](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SlowRiseBarrier.lean#L194) and the [resulting exclusion](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SlowRiseBarrier.lean#L280). Their landing bound controls increments of $`C_n`$; the argument above controls increments of $`H_n`$.

No upper bound on $`\Theta`$ is proved. If $`G_n`$ is unbounded, the theorem forces $`\Theta=+\infty`$. If $`G_n=g`$ eventually, it proves only $`\Theta\ge g\,v_T/\varphi(v_T)`$ for every late $`T`$. Since $`v_T\mid v_{T+1}`$, the ratios $`\varphi(v_T)/v_T`$ are nonincreasing and have a limit $`\sigma\ge0`$. If $`\sigma=0`$, the lower bound again forces $`\Theta=+\infty`$; if $`\sigma>0`$, it gives $`\Theta\ge g/\sigma`$ but does not determine whether $`\Theta`$ is finite. Replacing $`H_n`$ by the running maximum of $`u_n`$ divides the coefficient by $`g`$, since $`\ell(gx)/\ell(x)\to1`$.

<a id="bounds-that-allow-for-cancellation-and-earlier-decreases"></a>

## Bounds that allow for cancellation and earlier decreases

<div id="long243:res:recordamplified" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-recordamplified">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-recordamplified-comparator">Comparator</a></p>

**Theorem 31** (bounds allowing for previous decreases). *Under the standing hypotheses, the following are equivalent: eventual Sylvester behaviour; $`\limsup_n\mathcal A_n<\infty`$; $`\limsup_nR_n\delta_n<\infty`$. Each of those two limits superior is $`0`$ or $`+\infty`$.*

</div>

<div id="long243:res:criticalrate" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-criticalrate">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-criticalrate-comparator">Comparator</a></p>

**Corollary 32** (the critical rate). *Under the standing hypotheses and $`\delta_n=O(1/n)`$, with no convergence of $`n\delta_n`$ assumed, eventual Sylvester behaviour is equivalent to $`u_n=O(n)`$ and to $`(-\tilde e_n)_+=O(1)`$. A counterexample at the critical rate therefore has $`\limsup_nu_n/n=\infty`$ and $`\limsup_n(-\tilde e_n)_+=\infty`$.*

</div>

<div class="proof">

*Proof of Theorem <a href="#long243:res:recordamplified" data-reference-type="ref" data-reference="long243:res:recordamplified">31</a>.* Suppose the orbit is not eventually Sylvester and $`\mathcal A_n\le K`$ eventually, for an integer $`K\ge1`$. Absorption and $`|\tilde e_n|/u_n\to0`$ give $`u_n\to\infty`$. Negative reduced errors must occur arbitrarily late, since otherwise $`h_nu_{n+1}=u_n-\tilde e_n`$ would make $`u_n`$ eventually nonincreasing.

Cancellation may lower $`u_{s+1}`$ without a record. The first later negative error detects the loss: its magnitude is at least one, while $`R_t`$ remembers $`u_s`$. Fix a late $`s`$ and let $`t>s`$ be that first negative-error index. At the intervening steps the reduced numerator is nonincreasing, so $`u_t\le u_{s+1}`$. Since $`R_t\ge u_s`$ and $`m_t=|\tilde e_t|\ge1`$,
``` math
\mathcal A_t=\frac{R_tm_t}{u_t}\ge\frac{u_s}{u_{s+1}}
 =\frac{h_s}{1-\tilde e_s/u_s}.
```
Thus $`h_s\le3K/2<2K`$ after the relative-error threshold. Also $`m_n\le\mathcal A_n\le K`$, since $`R_n\ge u_n`$, and hence $`u_{n+1}\le u_n+K`$.

We can now choose primes too large to be removed by cancellation. The density-one argument in the proof of Theorem <a href="#long243:res:recorddichotomy" data-reference-type="ref" data-reference="long243:res:recorddichotomy">29</a> supplies infinitely many late multipliers $`a_n`$ coprime to $`D_n`$. These multipliers are pairwise coprime. At each such step, $`a_n`$ is coprime to $`v_n`$ and $`\gcd(u_n,v_n)=1`$, so $`a_nu_n-v_n`$ is coprime to both $`a_n`$ and $`v_n`$. Hence $`h_n=1`$ and $`a_n\mid v_{n+1}`$. Only finitely many of the chosen multipliers can have all their prime divisors at most $`2K`$, since each uses a different prime from that finite set. Choose $`K`$ distinct primes $`p_0,\ldots,p_{K-1}>2K`$ at these steps. Once a chosen prime divides a reduced denominator, it divides every later one: $`h_nv_{n+1}=a_nv_n`$ and $`h_n<2K<p_i`$ prevent its removal. All the primes therefore divide $`v_T`$ at a common later index $`T`$.

Consequently every $`u_n`$ with $`n\ge T`$ is coprime to all the $`p_i`$. Choose a CRT block of $`K`$ consecutive integers, one divisible by each $`p_i`$, above $`R_T`$. Divergence forces a first crossing, while $`u_{n+1}\le u_n+K`$ forces it to land inside the block, a contradiction. This proves that finite $`\limsup\mathcal A_n`$ forces the eventual Sylvester recurrence.

The comparison $`|\delta_n-m_n/u_n|\le3/a_n`$ gives $`|R_n\delta_n-\mathcal A_n|\le3R_n/a_n\to0`$. Here $`R_n\le H_n`$, $`\log H_n=o(n)`$ and $`a_n`$ grows doubly exponentially. Thus the two boundedness conditions are equivalent. Under the eventual Sylvester recurrence, $`u_n=1`$ and $`m_n=0`$ eventually, so $`\mathcal A_n\to0`$ and $`R_n\delta_n\to0`$. Since both quantities are nonnegative, their limits superior can only be $`0`$ or $`+\infty`$. ◻

</div>

The estimate at the first later negative error is the lemma in the release, [negative error scaled by the previous maximum after cancellation](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos243/SaturatedSquareTransport.lean#L378): at the first later negative error, $`u_t\le u_{s+1}`$ and $`u_su_t\le R_t|\tilde e_t|u_{s+1}`$. The exact example $`15/134=1/10+1/85+1/5695`$, with steps in reduced fractions $`(15,134)\to(4,335)\to(1,5695)`$ and $`\mathcal A_1=15/4`$, attains equality in the displayed bound.

For Corollary <a href="#long243:res:criticalrate" data-reference-type="ref" data-reference="long243:res:criticalrate">32</a>, the comparison $`|\delta_n-m_n/u_n|\le3/a_n`$ and the rate $`\delta_n=O(1/n)`$ give $`m_n/u_n=O(1/n)`$. If $`u_n=O(n)`$, then $`m_n=O(1)`$. Conversely, $`m_n=O(1)`$ gives $`u_{n+1}\le u_n+m_n`$, hence $`u_n=O(n)`$ and $`R_n=O(n)`$. In either case $`\mathcal A_n=R_nm_n/u_n=O(1)`$, so Theorem <a href="#long243:res:recordamplified" data-reference-type="ref" data-reference="long243:res:recordamplified">31</a> gives eventual Sylvester behaviour. The eventual Sylvester recurrence gives $`u_n=1`$ and $`m_n=0`$ eventually, which proves the converse implications.

The critical-rate assumption is doing real work: a bound on $`(-\tilde e_n)_+`$ alone does not directly control $`R_n/u_n`$ after a decrease. The preceding corollary supplies the missing control from $`\delta_n=O(1/n)`$. No such bound is derived here from the unrestricted quadratic limit.

<div id="long243:res:oddpowersupply" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-oddpowersupply">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-oddpowersupply-comparator">Comparator</a></p>

**Lemma 33** (large odd prime powers in the reduced denominator). *Under the standing hypotheses, for every fixed $`A>0`$ and every sufficiently large $`n`$, the reduced denominator $`v_n`$ has an odd prime-power divisor $`Q=p^k`$ with
``` math
Q>(H_n+2)^A,\qquad H_n=\max_{j\le n}C_j.
```
The prime $`p`$ may depend on $`n`$; no stable-gcd or prime-arrival assumption is imposed.*

</div>

<div class="proof">

*Proof.* The denominator grows too fast for all its odd prime-power factors to remain small compared with $`H_n`$. Indeed, the estimate for the rational tail gives $`C_{n+1}/C_n\to1`$, hence $`\log H_n=o(n)`$. Since $`x_n=u_n/v_n\le2/a_n`$ and $`u_n\ge1`$, $`v_n\ge a_n/2`$. Also $`v_n\mid L_n=\operatorname{lcm}(q,a_0,\ldots,a_{n-1})`$, so the $`2`$-primary part of $`v_n`$ is at most $`\max(q,a_{n-1})=a_{n-1}`$ for all large $`n`$. Its odd part $`W_n`$ therefore satisfies
``` math
W_n\ge\frac{a_n}{2a_{n-1}}\ge\frac{a_{n-1}}4,
 \qquad \log W_n\ge c2^{n-1}-O(1)
```
for some $`c>0`$. Put $`B_n=(H_n+2)^A=\exp(o(n))`$. If every exact odd prime-power factor of $`W_n`$ were at most $`B_n`$, then $`W_n\mid\operatorname{lcm}(1,\ldots,\lfloor B_n\rfloor)`$, giving
``` math
\log W_n\le B_n\log B_n=\exp(o(n)).
```
This contradicts the preceding exponential lower bound for all sufficiently large $`n`$. An offending exact prime-power factor is the required $`Q`$. ◻

</div>

This uses only an elementary factorial bound, not prime distribution. The prime may change with $`n`$: choose one large prime power at a late start and protect it until the first forbidden crossing.

<div id="long243:res:unitrecord" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-unitrecord">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-unitrecord-comparator">Comparator</a></p>

**Theorem 34** (unit record increments). *Under the standing hypotheses, if $`R_{n+1}-R_n\le1`$ for all large $`n`$, then $`a_{n+1}=a_n^2-a_n+1`$ for all large $`n`$. Hence the sequence is eventually Sylvester if and only if $`\#\{n:R_{n+1}-R_n\ge2\}`$ is finite. No hypothesis is placed on decreases in $`u_n`$, on record-setting jumps, or on the cancellation factors $`h_n`$.*

</div>

<div class="proof">

*Proof.* Suppose the orbit is not eventually Sylvester. Absorption gives $`\tilde e_n\ne0`$ on a late tail, so vanishing relative error and integrality give $`u_n\to\infty`$. Choose $`s`$ so large that the unit-increment bound and $`|\tilde e_n|<u_n/2`$ hold for every $`n\ge s`$, and that Lemma <a href="#long243:res:oddpowersupply" data-reference-type="ref" data-reference="long243:res:oddpowersupply">33</a> applies with $`A=3`$. Since $`H_s\ge R_s\ge1`$, it supplies an odd $`Q=p^k\mid v_s`$ with $`Q>(H_s+2)^3>4(R_s+2)`$ and $`Q\ge16`$. Let $`Y`$ be the least multiple of $`p`$ above $`R_s`$. Then $`Y\le R_s+p< Q/4+p\le5Q/4`$. At the first $`t>s`$ with $`u_t\ge Y`$, the integer maximum rises from at most $`Y-1`$ by at most one, forcing $`u_t=Y`$ regardless of $`u_{t-1}`$. Before $`t`$, one has $`w_n<3u_n/2<15Q/8<pQ=p^{k+1}`$. Corollary <a href="#long243:res:powerpersistence" data-reference-type="ref" data-reference="long243:res:powerpersistence">28</a> therefore gives $`p^k\mid v_t`$. But $`p\mid u_t=Y`$, contradicting $`\gcd(u_t,v_t)=1`$. The converse follows because the eventual Sylvester recurrence gives $`u_n=1`$ eventually. ◻

</div>

The `plectis-erdos-lean` repository contains the [unit-increment landing lemma](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos243/RecordIncrementBarrier.lean#L329) and the [one-unit record-increment implication](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos243/RecordIncrementBarrier.lean#L425); they assume the existence of the prime power that Lemma <a href="#long243:res:oddpowersupply" data-reference-type="ref" data-reference="long243:res:oddpowersupply">33</a> supplies.

The two-unit criterion discussed below bounds the actual jump at each record step, rather than the increase in the running maximum. As numerical bounds on individual steps, neither condition implies the other: the first allows $`s_n=2`$, while $`s_n\le1`$ permits large jumps after an earlier decrease. This is a comparison of the bounds, not a claim that they remain logically independent under all the standing tail hypotheses; there both criteria force eventual Sylvester behaviour. The finite example $`(8,177)\to(7,4071)\to(10,2373393)`$ with multipliers $`23`$ and $`583`$ has records $`8`$ and $`10`$, increment $`2`$, jump $`3`$ and $`\gcd(8,10)=2`$, which is why the parity argument for crossing an odd level does not transfer from actual jumps to increments of the running maximum.

<a id="counting-jumps-before-a-prime-power-can-be-lost"></a>

## Counting jumps before a prime power can be lost

Large jumps may skip forbidden values. Under the relative-error bound, $`L=pQ/2`$ keeps the numerator before cancellation below $`pQ`$ until the crossing, protecting the prime power. Odd multiples of $`p`$ exclude two-unit crossings as well: skipping an odd level in two units would leave both adjacent numerators even. We count both crossing jumps and their excess over two.

<div id="long243:res:epochenergy" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-epochenergy">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-epochenergy-comparator">Comparator</a></p>

**Theorem 35** (counting crossings before a prime power is lost). *Let the orbit satisfy the reduced recurrences of this section, with $`2|\tilde e_n|<u_n`$ from an index $`s`$. Let $`p\ge3`$ be prime, $`Q=p^{\ell}`$ divide $`v_s`$ with $`Q\ge16`$, put $`L=pQ/2`$, and assume $`R_s<L/2`$. Assume that $`u_t\ge L`$ for some $`t>s`$, and let $`\tau`$ be the first such index, let $`J`$ be the set of steps in $`[s,\tau)`$ that first cross at least one odd multiple of $`p`$ in $`(L/2,L]`$, and put $`X=\sum_{n\in J}(d_n-2)`$. Then every $`n\in J`$ is a record step with $`h_n=1`$ and $`d_n\ge3`$, and $`pQ\le(8p+8)\lvert J\rvert+4X+8p`$.*

</div>

<div class="proof">

*Proof of Theorem <a href="#long243:res:epochenergy" data-reference-type="ref" data-reference="long243:res:epochenergy">35</a>.* For $`s\le n<\tau`$, one has $`u_n<L`$ and $`w_n<3u_n/2<3pQ/4<p^{\ell+1}`$, since $`Q=p^{\ell}`$. Corollary <a href="#long243:res:powerpersistence" data-reference-type="ref" data-reference="long243:res:powerpersistence">28</a> gives $`Q\mid v_t`$ throughout $`[s,\tau]`$, so $`p\nmid u_t`$ there. A first crossing of a level above $`R_s`$ is a record step. If $`h_n\ge2`$ then $`u_{n+1}=w_n/h_n<3u_n/4`$, so every such record step has $`h_n=1`$. An odd multiple of $`p`$ cannot be landed on. A jump of size $`1`$ crossing it would land on it; a jump of size $`2`$ avoiding the landing would have two even endpoints, contrary to $`\gcd(u_n,u_{n+1})=1`$. Thus every $`n\in J`$ has $`d_n\ge3`$. It remains to count these levels. The interval $`(L/2,L]`$ has length $`pQ/4`$, and odd multiples of $`p`$ are spaced by $`2p`$, so it contains at least $`Q/8-1`$ of them. The levels first crossed by a step of size $`d_n`$ have the same spacing, so there are at most $`1+d_n/(2p)`$ of them. Summing over $`J`$ gives
``` math
Q/8-1\le |J|+\frac{2|J|+X}{2p},
```
which rearranges to the asserted inequality. ◻

</div>

Crossing requires many jumps or a few large ones. The first series therefore counts jumps of size at least three and measures their excess over two, with weights that detect either contribution. A non-Sylvester tail pays a fixed positive amount on arbitrarily late protected intervals; a Sylvester tail has no late records. The relative-error limit alone gives no convergence.

<div id="long243:res:energycriterion" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-energycriterion">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-energycriterion-comparator">Comparator</a></p>

**Theorem 36** (two convergence criteria for large record jumps). *Under the standing hypotheses, the sum $`\mathcal E=\sum_{n\ \mathrm{record}}\bigl(\mathbf 1_{d_n\ge3}u_n^{-1/2}
+(d_n-2)_+u_n^{-1}\bigr)`$ is finite if and only if the sequence is eventually Sylvester; and $`\sum_{n\ \mathrm{record}}(d_n-2)_+u_n^{-1/2}`$ is finite if and only if the sequence is eventually Sylvester.*

</div>

<div class="proof">

*Proof.* Assume first that the recurrence is not eventually Sylvester. Then $`u_n\to\infty`$. For every sufficiently late $`s`$, Lemma <a href="#long243:res:oddpowersupply" data-reference-type="ref" data-reference="long243:res:oddpowersupply">33</a> with $`A=3`$ gives an odd $`Q=p^k\mid v_s`$ with $`Q>(H_s+2)^3`$, hence $`Q\ge16`$ and $`pQ>4R_s`$. Set $`L=pQ/2`$ and take its first crossing. The preceding theorem applies. Because $`Q\ge p`$ and $`p\ge3`$,
``` math
\frac{8p}{L}=\frac{16}{Q}\le1,
 \qquad \frac{8p+8}{\sqrt L}
 \le8\sqrt2(1+1/p)<16.
```
Dividing the preceding counting inequality by $`L`$ therefore gives
``` math
1\le16\frac{|J|}{\sqrt L}+4\frac{X}{L}
 \le16\sum_{n\in J}\left(\frac1{\sqrt{u_n}}+
                  \frac{d_n-2}{u_n}\right),
```
since $`u_n<L`$ for $`n<\tau`$ and $`d_n\ge3`$ on $`J`$. Thus an arbitrarily late finite window contributes at least $`1/16`$ to $`\mathcal E`$, contradicting convergence. No disjointness of the windows is needed: every window lies in a tail of the nonnegative series. Under the eventual Sylvester recurrence, $`u_n=1`$ eventually, so there are no late records and $`\mathcal E`$ is finite. Finally, term by term at a record,
``` math
\mathbf1_{d_n\ge3}u_n^{-1/2}+(d_n-2)_+u_n^{-1}
 \le2(d_n-2)_+u_n^{-1/2}.
```
Hence finiteness of the second series implies finiteness of the first, and convergence in the converse direction again follows from eventual Sylvester behaviour. ◻

</div>

<a id="formalisation."></a>

#### Formalisation.

The `plectis-erdos-lean` repository contains [the integer inequality counting crossings before a prime power is lost](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos243/ProtectedEpochEnergy.lean#L185) and its counting lemmas. In Lean, [the two-unit record-rise implication](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PrimitiveRecordBarrier.lean#L435) assumes that arbitrarily late $`s`$ admit an odd $`p^k\mid v_s`$ with $`3R_s<p^k`$; Lemma <a href="#long243:res:oddpowersupply" data-reference-type="ref" data-reference="long243:res:oddpowersupply">33</a> supplies such prime powers.

<a id="bounds-on-the-error-and-on-the-original-sequence"></a>

## Bounds on the error and on the original sequence

<div id="long243:res:slownegative" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-slownegative">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-slownegative-comparator">Comparator</a></p>

**Theorem 37** (slow negative part). *Let $`a,C,D:\mathbb{N}\to\mathbb{N}`$ satisfy <a href="#long243:eq:recurrences" data-reference-type="eqref" data-reference="long243:eq:recurrences">[long243:eq:recurrences]</a> with $`a_n>1`$, $`C_n>0`$, $`D_0\ge1`$, under vanishing relative error. Suppose that for some $`\delta\in(0,1)`$ and all large $`n`$ with $`E_n<0`$ one has $`-E_n\le(1-\delta)\ell(C_n)`$. Then $`E_n=0`$ for all large $`n`$, and $`a_{n+1}=a_n^2-a_n+1`$ for all large $`n`$.*

</div>

Theorem <a href="#long243:res:bounded" data-reference-type="ref" data-reference="long243:res:bounded">53</a> is the case of a constant bound, since a constant is eventually below $`(1-\delta)\ell(C_n)`$ on a nonzero tail, where $`C_n\to\infty`$.

<div class="proof">

*Proof.* Suppose the error is not eventually zero. The auxiliary lower bound in the proof of Theorem <a href="#long243:res:recorddichotomy" data-reference-type="ref" data-reference="long243:res:recorddichotomy">29</a> applies to this exact integer orbit: it used only $`a_n>1`$, $`C_n>0`$, $`D_0\ge1`$ and vanishing relative error. It gives $`\limsup_n(H_{n+1}-H_n)/\ell(H_n)\ge1`$. On the other hand, the hypothesis and $`C_n\le H_n`$ give
``` math
H_{n+1}-H_n\le(-E_n)_+
 \le(1-\delta)\ell(C_n)\le(1-\delta)\ell(H_n)
```
for all large $`n`$, a contradiction. Thus $`E_n=0`$ eventually, and Theorem <a href="#long243:res:eventual" data-reference-type="ref" data-reference="long243:res:eventual">23</a> gives the Sylvester recurrence. ◻

</div>

The corresponding pointwise-rise argument also has formalised arithmetic lemmas: [persistence of a common divisor](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SlowRiseBarrier.lean#L111), [divisibility of every later error by $`\gcd(a_n,D_n)`$](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SlowRiseBarrier.lean#L162), the [landing lemma](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SlowRiseBarrier.lean#L194) and the [resulting exclusion](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SlowRiseBarrier.lean#L280). The count of indices and the simultaneous choice of constants are written out in the earlier proof. Corollary <a href="#long243:res:loglogboundary" data-reference-type="ref" data-reference="long243:res:loglogboundary">30</a> includes the boundary coefficient $`1`$, while the preceding theorem on the running maximum also discounts rises that recover an earlier decrease. The present statement is retained for its direct bound on $`E_n`$.

To compare the bounded hypothesis with the classical criteria, number the original sequence from $`1`$ in this subsection and put $`P_n=\prod_{1\le j<n}a_j`$. Then
``` math
\frac{P_n}{a_n}\left(\frac{a_n^2}{a_{n+1}}-1\right)
 =\frac{P_{n+1}}{a_{n+1}}-\frac{P_n}{a_n}.
```
Thus the bound concerns upward increments, not boundedness of $`P_n/a_n`$. The quadratic growth limit controls only the ratio of consecutive terms. Sequences satisfying the eventual Sylvester recurrence satisfy the bound, as do exact-square sequences $`a_n=b^{2^{n-1}}`$ with $`b\ge2`$, for which the difference is zero. The latter never satisfies the Sylvester recurrence, so the bounded criterion below recovers irrationality of its reciprocal sum. The rounded examples after Corollary <a href="#long243:res:onethreshold" data-reference-type="ref" data-reference="long243:res:onethreshold">39</a> show more generally how a term $`c/n`$ in the ratio produces increments of order $`n^{c-1}`$. The theorem allows a finite positive upper limit where the classical product criterion requires a nonpositive one; neither bound is derived from the original problem alone.

<div id="long243:res:strausbounded" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-strausbounded">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-strausbounded-comparator">Comparator</a></p>

**Theorem 38** (bounded or slowly growing increments of the product ratio). *Let $`a_1<a_2<\cdots`$ be positive integers with $`a_{n+1}/a_n^2\to1`$ and $`\sum_{n\ge1}1/a_n=p/q`$, where $`p,q`$ are positive integers. Put
``` math
Q_n=\frac{a_1a_2\cdots a_{n-1}}{a_n}
     \left(\frac{a_n^2}{a_{n+1}}-1\right).
```
If $`\limsup_nQ_n<\infty`$, the sequence is eventually Sylvester. The same conclusion holds if, for some $`\delta>0`$ and all large $`n`$,
``` math
Q_n\le\frac{1-\delta}{q}\,
 \ell(a_1\cdots a_{n-1}/a_n).
```*

</div>

For the bounded clause, use the stated denominator $`q`$, put $`P_n=\prod_{j<n}a_j`$, $`x_n=\sum_{k\ge n}1/a_k`$, and form the integer tail $`D_n=qP_n`$, $`C_n=D_nx_n`$, $`E_n=D_n-(a_n-1)C_n`$. Exact cancellation gives
``` math
E_n+qQ_n=qP_n\left(\frac1{a_{n+1}}
 -(a_n-1)\sum_{k\ge n+2}\frac1{a_k}\right).
```
The expression in parentheses is positive eventually, since $`\sum_{k\ge n+2}1/a_k\le4/a_{n+1}^2`$ and $`a_{n+1}>4(a_n-1)`$ eventually. Thus $`E_n\ge-qQ_n`$, and $`\limsup Q_n<\infty`$ supplies the eventual lower bound required by Theorem <a href="#long243:res:bounded" data-reference-type="ref" data-reference="long243:res:bounded">53</a>. This proves the bounded clause without first estimating the absolute size of the comparison error.

For the slow-growth clause and the later summability comparisons, the same exact formula gives
``` math
0<E_n+qQ_n\le qP_n/a_{n+1}=O(P_n/a_n^2)
```
eventually. The ratio test in Section <a href="#long243:sec:lcmrecords" data-reference-type="ref" data-reference="long243:sec:lcmrecords">6</a> shows that these errors have a convergent sum, hence tend to zero. The factor $`1/q`$ in the slow-growth clause cancels the factor $`q`$ in $`E_n+qQ_n=o(1)`$. Suppose the sequence is not eventually Sylvester. Absorption and vanishing relative error give $`C_n\to\infty`$, and the tail estimate $`C_n\sim qP_n/a_n`$ implies
``` math
\frac{\ell(C_n)}{\ell(P_n/a_n)}\longrightarrow1.
```
For $`0<\delta<1`$, the assumed bound and $`E_n+qQ_n=o(1)`$ consequently give $`(-E_n)_+\le(1-\delta/2)\ell(C_n)`$ eventually. This contradicts Theorem <a href="#long243:res:slownegative" data-reference-type="ref" data-reference="long243:res:slownegative">37</a>. If $`\delta\ge1`$, the hypothesis gives $`Q_n\le0`$ eventually and the bounded clause already applies.

The same comparison permits any positive real clearing factor $`F_n\le qP_n`$: multiplying $`E_n+qQ_n=o(1)`$ by $`F_n/(qP_n)`$ gives
``` math
F_n-(a_n-1)F_nx_n+
 \frac{F_n}{a_n}\left(\frac{a_n^2}{a_{n+1}}-1\right)=o(1).
```
Neither $`F_nx_n`$ nor $`F_n-(a_n-1)F_nx_n`$ need be integral. The LCM choice $`F_n=L_n`$ makes both integers, but its update includes the factor $`\rho_n`$ of Section <a href="#long243:sec:lcmrecords" data-reference-type="ref" data-reference="long243:sec:lcmrecords">6</a>. The short note uses only this LCM specialisation; no general clearing factor is needed in its bounded-increment proof.

<a id="attribution."></a>

#### Attribution.

Erdős and Straus require $`\limsup\le0`$ in the corresponding criterion, with the least common multiple in place of the product and the growth factor one index later, so their quantity is $`[a_1,\ldots,a_n]a_{n+1}^{-1}(a_{n+1}^{2}/a_{n+2}-1)`$ \[erdosstraus1964, Theorem 3, p. 132\]; Koizumi’s Corollary 4(1) uses the product form \[koizumi2025, Cor. 4(1), pp. 14–15\]. The bounded clause follows from Theorem <a href="#long243:res:bounded" data-reference-type="ref" data-reference="long243:res:bounded">53</a>. For Koizumi’s product expression it replaces a nonpositive upper limit by an arbitrary finite upper limit. The material distinction here is product versus least common multiple. Reindexing $`r=n+1`$ makes the classical LCM expression $`[a_1,\ldots,a_{r-1}]a_r^{-1}(a_r^2/a_{r+1}-1)`$, exactly the expression in the short note’s LCM corollary.

The comparison $`E_n+qQ_n=o(1)`$ has its classical predecessor in Koizumi’s proof of Corollary 4(1) \[koizumi2025, (11)–(12), p. 15\].

<div id="long243:res:onethreshold" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-onethreshold">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-onethreshold-comparator">Comparator</a></p>

**Corollary 39** (the $`1/n`$ threshold). *Let $`a_1<a_2<\cdots`$ be positive integers with $`a_{n+1}/a_n^2\to1`$ and $`\sum_n1/a_n\in\mathbb{Q}`$. If
``` math
\limsup_{n\to\infty} n\,(a_n^2/a_{n+1}-1)_+<1,
```
then $`a_{n+1}=a_n^2-a_n+1`$ for all large $`n`$. The same conclusion holds if, for some $`K\ge0`$ and $`\varepsilon>0`$,
``` math
\frac{a_n^2}{a_{n+1}}-1\le\frac1n+\frac{K}{n^{1+\varepsilon}}
 \quad\hbox{eventually}.
```
In particular the one-sided bound by $`1/n`$ is included.*

</div>

<div class="proof">

*Proof.* Put $`\gamma_n=a_n^2/a_{n+1}-1`$ and $`t_n=\bigl(\prod_{j<n}a_j\bigr)/a_n`$, so that $`t_{n+1}/t_n=1+\gamma_n`$. Choose $`r\in(0,1)`$ and $`N`$ with $`\gamma_n^{+}\le r/n`$ for all $`n\ge N`$. Then
``` math
t_n\le t_N\prod_{k=N}^{n-1}\Bigl(1+\frac rk\Bigr)=O(n^{r}),
```
so $`(t_n\gamma_n)_+=t_n\gamma_n^{+}=O(n^{r-1})`$ tends to zero and $`\limsup_nt_n\gamma_n\le0`$. Koizumi’s Corollary 4(1) \[koizumi2025, pp. 14–15\] gives the first conclusion. For the second, divide $`t_n`$ by $`n`$ to obtain
``` math
\frac{t_{n+1}/(n+1)}{t_n/n}
 =\frac{1+\gamma_n}{1+1/n}
 \le 1+\frac{K}{n^\varepsilon(n+1)}.
```
The product of the upper bounds converges, so $`t_n/n`$ is bounded above. Consequently $`t_n(\gamma_n)_+=O(1)`$, and Theorem <a href="#long243:res:strausbounded" data-reference-type="ref" data-reference="long243:res:strausbounded">38</a> applies. ◻

</div>

The inclusive clause requires more than $`\limsup n(\gamma_n)_+\le1`$. That weaker condition does not give the product estimate: for example, the scalar sequence $`\gamma_n=(1+1/\log n)/n`$ has $`t_n\asymp n\log n`$ and $`t_n\gamma_n\asymp\log n`$. This is a limitation of the estimate, not a counterexample to the original problem.

More generally, if $`c>0`$, $`\varepsilon>0`$ and
``` math
\frac{a_n^2}{a_{n+1}}=1+\frac cn+O(n^{-1-\varepsilon}),
```
then the consecutive-ratio identity gives $`t_n\sim Kn^c`$ for some $`K>0`$ and $`t_{n+1}-t_n\sim Kc n^{c-1}`$. To see the constant, take logarithms and subtract $`c\log(1+1/n)`$; the remainder is absolutely summable. Hence the increments are bounded for $`c\le1`$ and unbounded for $`c>1`$. These rates are realised by increasing integer sequences: set $`a_{n+1}=\lceil n a_n^2/(n+c)\rceil`$ and choose the seed large enough that $`a_{n+1}\ge a_n^2/(1+c)\ge2a_n`$ throughout. The rounding remainder in $`[0,1)`$ gives an error in the ratio bounded by $`(1+c)^2/a_n^2`$, smaller than every fixed inverse power of $`n`$. This calculation supplies the family comparison behind the two rounded examples retained in the short note. It concerns their growth and does not assume rationality.

The second clause has a concrete application outside Koizumi’s nonpositive-upper-limit product condition. The sequence $`a_1=4`$, $`a_{n+1}=\lceil n a_n^2/(n+1)\rceil`$ begins $`4,8,43,1387,\ldots`$ and satisfies
``` math
a_n\ge2\cdot2^{2^{n-1}},\qquad
 0\le1+\frac1n-\frac{a_n^2}{a_{n+1}}<\frac4{a_n^2}.
```
The lower bound follows from $`a_{n+1}\ge a_n^2/2`$; the upper error bound follows by writing the rounding remainder in $`[0,1)`$. Consequently $`t_n\sim Kn`$ and $`t_n\gamma_n\to K>0`$ by the product comparison above. The corollary proves that the reciprocal sum is irrational, since the eventual Sylvester recurrence would give $`\gamma_n=O(1/a_n)`$ rather than $`\gamma_n\sim1/n`$.

The strict clause includes Koizumi’s sufficient rate $`1+o(1/n)`$ \[koizumi2025, Remark 3, p. 16\]; the inclusive clause allows a bounded positive increment rather than requiring a nonpositive upper limit.

<a id="signs-of-the-error-and-of-the-growth-ratio"></a>

## Signs of the error and of the growth ratio

We keep the preceding one-based indexing. The growth defect need not have the opposite sign to $`E_n`$: the next identity displays the correction, including its sign under the eventual Sylvester recurrence.

<div id="long243:res:classicalhalfspace" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-classicalhalfspace">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-classicalhalfspace-comparator">Comparator</a></p>

**Proposition 40** (comparison of the two signs). *The factor $`M_n=D_n/L_n`$ divides $`G_n=\gcd(C_n,D_n)`$. Thus $`G_n/M_n`$ is a positive integer and $`E_n/M_n=(G_n/M_n)\tilde e_n`$ is an integer with the same sign as $`E_n`$. The sign of the growth ratio minus one also depends on a correction term. The exact recurrences give, whenever $`a_{n+1}C_nC_{n+1}\ne0`$,
``` math
\begin{equation}
\label{long243:eq:shiftedsign}
 \frac{a_n^2}{a_{n+1}}-1=-\frac{E_n}{C_n}+\Lambda_n,
 \qquad
 \Lambda_n=\frac{\bigl(1-E_n/C_n\bigr)\bigl(a_n-1+E_{n+1}/C_{n+1}\bigr)}{a_{n+1}},
\end{equation}
```
and, under the standing positive rational-tail hypotheses, $`0<\Lambda_n<3/a_n`$ for all sufficiently large $`n`$. The Erdős–Straus quantity of Theorem 3 is
``` math
Z_n^{\mathrm{ES}}=
 \frac{[a_1,\ldots,a_n]}{a_{n+1}}
 \left(\frac{a_{n+1}^2}{a_{n+2}}-1\right).
```
Its least common multiple includes $`a_n`$ but not the clearing denominator $`q`$. It is not $`Q_n=(P_n/a_n)\gamma_n`$ from the preceding subsection, nor $`L_n\gamma_{n+1}/a_{n+1}`$ under our convention $`L_n=\operatorname{lcm}(q,a_1,\ldots,a_{n-1})`$. Being a positive multiple of the next growth defect, $`Z_n^{\mathrm{ES}}`$ has the sign of $`\Lambda_{n+1}-E_{n+1}/C_{n+1}`$. For all sufficiently large $`n`$, it is positive when $`E_{n+1}\le0`$; for $`E_{n+1}>0`$, it is negative precisely when $`E_{n+1}/C_{n+1}>\Lambda_{n+1}`$. Under the eventual Sylvester recurrence, $`E_n=0`$ and $`\Lambda_n=(a_n-1)/a_{n+1}>0`$.*

</div>

<div class="proof">

*Proof.* Since both $`C_n=D_nx_n`$ and $`L_nx_n`$ are integers, $`M_n=D_n/L_n`$ divides $`C_n`$ as well as $`D_n`$. It therefore divides $`G_n`$. For <a href="#long243:eq:shiftedsign" data-reference-type="eqref" data-reference="long243:eq:shiftedsign">[long243:eq:shiftedsign]</a>, write $`\theta_n=E_n/C_n`$; Proposition <a href="#long243:res:update" data-reference-type="ref" data-reference="long243:res:update">14</a> gives $`C_{n+1}=C_n(1-\theta_n)`$ and $`D_n/C_n=a_n-1+\theta_n`$, so $`a_{n+1}-1+\theta_{n+1}=a_nD_n/C_{n+1}=a_n(a_n-1+\theta_n)/(1-\theta_n)`$. Multiplying the asserted identity by $`a_{n+1}`$ and substituting reduces it to $`a_{n+1}+a_n-1+\theta_{n+1}=a_n^2/(1-\theta_n)`$, which is the displayed relation with $`a_n`$ added to both sides. The bound follows from $`\theta_n\to0`$ and $`a_{n+1}\ge a_n^2/2`$. On Sylvester’s sequence $`\theta_n=0`$ and $`a_{n+1}=a_n^2-a_n+1`$, so $`a_n^2/a_{n+1}-1=(a_n-1)/a_{n+1}=\Lambda_n>0`$. ◻

</div>

A nonpositive upper limit admits positive values tending to zero; it is not an eventual pointwise sign condition. For the *product* quantity $`Q_n=(P_n/a_n)\gamma_n`$, the identity $`E_n+qQ_n=o(1)`$ shows that eventual $`E_n\ge0`$ implies $`\limsup Q_n\le0`$, as in Koizumi’s Corollary 4(1) \[koizumi2025, pp. 14–15\]. For the classical LCM expression $`Z_n^{\mathrm{ES}}`$, the corresponding integer error is also taken one index later. Its published hypotheses are those of Erdős–Straus Theorem 3 \[erdosstraus1964, p. 132\]. Reindexing relates it to an LCM-cleared error, not to $`E_n`$ with the unchanged product factor $`qQ_n`$.

<a id="a-comparison-with-mathcal-b-free-integers."></a>

#### A comparison with $`\mathcal B`$-free integers.

For a fixed family $`\mathcal B=\{m_i\}`$, the integers divisible by none of the $`m_i`$ are called $`\mathcal B`$-free integers. With pairwise coprime moduli and $`\sum_i1/m_i<\infty`$, this is the standard setting of \[elabdalaoui2015, §1.2\]. The next proposition is an elementary interval count in that setting. It tests what can follow from avoiding whole multiples alone. Unlike the reciprocal-tail argument, it imposes all the moduli from the outset and has no denominator recurrence or cancellation factors.

<div id="long243:res:coprimalitycap" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-coprimalitycap">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-coprimalitycap-comparator">Comparator</a></p>

**Proposition 41** (an elementary interval bound). *Let $`m_0<m_1<\cdots`$ be pairwise coprime integers at least $`2`$ with $`\theta=\sum_i1/m_i<1`$. For all integers $`x\ge1`$ and $`L\ge1`$ satisfying $`L>k/(1-\theta)`$, where $`k=\#\{i:m_i\le x+L\}`$, the interval $`[x,x+L)`$ contains an integer divisible by no $`m_i`$. If also $`\ell(m_i)=i+O(1)`$, then for every $`\epsilon>0`$ there are an index $`T`$ and a strictly increasing sequence of positive integers $`(u_n)`$ such that
``` math
m_i\nmid u_n\quad\text{for every }i\ge T\text{ and every }n,
 \qquad
 u_{n+1}-u_n\le(1+\epsilon)\ell(u_n)\quad\text{eventually}.
```*

</div>

<div class="proof">

*Proof.* The interval $`[x,x+L)`$ contains exactly $`L`$ integers. Each lies in $`[1,\infty)`$ and is smaller than $`x+L`$, so a modulus exceeding $`x+L`$ divides none of them. Each of the $`k`$ remaining moduli divides at most $`L/m_i+1`$ of them, so the covered count is at most $`L\theta+k<L`$. This interval count itself does not use pairwise coprimality; that condition is needed for the exact CRT proportions in the later gap theorem.

For the second assertion, choose a tail of the family and reindex it so that $`\theta<\epsilon/(1+\epsilon)`$. If $`k(z)=\#\{i:m_i\le z\}`$, the hypothesis $`\ell(m_i)=i+O(1)`$ gives $`k(z)\le\ell(z)+C`$ for all large $`z`$ and some constant $`C`$. Choose
``` math
(1-\theta)^{-1}<\rho<1+\epsilon,
 \qquad L(y)=\left\lceil\rho\ell(y)\right\rceil .
```
Then $`L(y)=O(\ell(y))=o(y)`$, and the definition of $`\ell`$ gives $`\ell(y+1+L(y))=\ell(y)+o(1)`$. Consequently, for all large integers $`y`$,
``` math
\frac{k(y+1+L(y))}{1-\theta}
 \le \frac{\ell(y)+C+o(1)}{1-\theta}
 < \rho\ell(y)\le L(y),
```
while $`L(y)\le(1+\epsilon)\ell(y)`$. The first part also supplies an admissible $`u_0`$ beyond this threshold. Apply it successively with $`x=u_n+1`$ and length $`L(u_n)`$, and choose $`u_{n+1}`$ in the resulting window. The sequence is strictly increasing, avoids every retained modulus, and has the required rise bound. ◻

</div>

The small-increment sequence avoids only the retained moduli $`m_i`$, $`i\ge T`$. Discarding the prefix makes their reciprocal sum small. For the full family, Theorem <a href="#long243:res:gapconstant" data-reference-type="ref" data-reference="long243:res:gapconstant">63</a> instead gives the coefficient $`\prod_i(1-1/m_i)^{-1}>1`$ for the increasing enumeration of integers avoiding all the moduli.

Proposition <a href="#long243:res:coprimalitycap" data-reference-type="ref" data-reference="long243:res:coprimalitycap">41</a> concerns avoidance of whole multiples, not coprimality to a composite modulus. The distinction matters: no integer in $`[2,5)`$ is coprime to $`30`$, although none is divisible by $`30`$. Thus this proposition alone does not disprove a coprime-walk extension of Theorem <a href="#long243:res:barrier" data-reference-type="ref" data-reference="long243:res:barrier">48</a>. Proposition <a href="#long243:res:variablerise" data-reference-type="ref" data-reference="long243:res:variablerise">62</a> below gives a separate counterexample using sparse *prime* moduli. Under the additional scale $`\ell(m_j)=j+O(1)`$, Theorem <a href="#long243:res:gapconstant" data-reference-type="ref" data-reference="long243:res:gapconstant">63</a> determines the exact maximal-gap coefficient for these $`\mathcal B`$-free integers. Its proof uses a finite sieve estimate and the Chinese remainder theorem, not an orbit construction. Neither static construction supplies an exact reciprocal-tail orbit.

<a id="conditions-on-a-possible-counterexample."></a>

#### Conditions on a possible counterexample.

Together, these criteria give necessary conditions on a counterexample. For every fixed $`\delta\in(0,1)`$, it must have
``` math
(1-\delta)\ell(C_n)\ \le\ -E_n\ =\ o(C_n)
 \qquad\text{at infinitely many }n.
```
It must also have a divergent sum of relative increases, unbounded negative error scaled by the previous maximum, and infinitely many record jumps of the reduced numerator of size at least three, with $`h_n=1`$. These are necessary conditions, not a construction of a counterexample. The residue-saturation lemma shows precisely one limitation of the fixed-old-modulus method; it is not an impossibility theorem about every future approach. A useful next target is interaction between new prime support, three consecutive numerators and the global bound on numerator growth.

<a id="long243:sec:descent"></a>

# Nonnegative errors

The scalar update already settles nonnegative errors. With indices starting at zero, $`C_{n+1}=C_n-E_n`$ makes $`C_n`$ nonincreasing, and a decreasing sequence of natural numbers must stabilise.

<div id="long243:res:descent" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1843">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-descent-comparator">Comparator</a></p>

**Theorem 42** (descent). *Let $`C,E:\mathbb{N}\to\mathbb{N}`$ satisfy $`C_{n+1}+E_n=C_n`$ for every $`n`$. Then $`E_n=0`$ for all sufficiently large $`n`$.*

</div>

<div class="proof">

*Proof.* The recurrence gives $`C_{n+1}\le C_n`$. Choose an index at which the natural-number sequence reaches its minimum. Every later value equals that minimum, and $`C_{n+1}+E_n=C_n`$ then gives $`E_n=0`$. ◻

</div>

The hypothesis is exactly one-sidedness: $`C`$ and $`E`$ take values in $`\mathbb{N}`$. If $`E_n<0`$ infinitely often, the numerator rises at those indices and this descent argument no longer applies. The next two sections first treat constant and periodic negative errors.

<a id="long243:sec:constant"></a>

# Constant negative errors

A constant negative error makes the numerator grow linearly. Such behaviour can persist for arbitrarily long finite intervals, even on genuine rational orbits, by the flat-transient theorem in the working report on Problem #243 \[erdosproblemaday243, Flat-transient theorem\]. We exclude infinite constant and periodic negative tails below. These exclusions supply no bound for the finite transient lengths.

Suppose the error is negative with a constant magnitude, $`E_n=-m`$ for a fixed $`m>0`$ and every $`n`$. By Proposition <a href="#long243:res:update" data-reference-type="ref" data-reference="long243:res:update">14</a> the numerator increases by $`m`$ at each step, so $`C_n=c+nm`$ with $`c=C_0`$, and the definition of the error becomes the identity
``` math
D_n+m=(a_n-1)\,(c+nm) .
\tag{5.1}\label{long243:eq:shape}
```
Together with $`D_{n+1}=a_nD_n`$ this is a closed system in $`(a,D)`$. We shall prove that it has no infinite natural-number solution with $`a_n\ge2`$, after examining a finite example.

<div id="long243:ex:shape" class="example">

**Example 43** (a nonintegral second step). Take $`m=c=1`$, so that $`C_n=1+n`$ and <a href="#long243:eq:shape" data-reference-type="eqref" data-reference="long243:eq:shape">[long243:eq:shape]</a> reads $`D_n+1=(a_n-1)(1+n)`$, and take $`D_0=1`$. Each step is now determined: at $`n=0`$ the equation reads $`2=(a_0-1)\cdot1`$, so $`a_0=3`$, and $`D_1=a_0D_0=3`$; at $`n=1`$ it reads $`4=(a_1-1)\cdot2`$, so $`a_1=3`$, and $`D_2=a_1D_1=9`$; at $`n=2`$ it reads $`10=(a_2-1)\cdot3`$, which has no integer solution, and the orbit stops. Longer prefixes occur for other starting values. For $`2\le a_0<5000`$, the exact residue search in Appendix <a href="#long243:app:residue" data-reference-type="ref" data-reference="long243:app:residue">16</a> gives a maximum of $`17`$ successful updates, hence $`18`$ multiplier values including $`a_0`$.

</div>

<div id="long243:res:constant" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-constant">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-constant-comparator">Comparator</a></p>

**Theorem 44** (no constant negative magnitude). *For any $`m,c\in\mathbb{N}`$ with $`m>0`$, there is no pair of sequences $`a,D:\mathbb{N}\to\mathbb{N}`$ with $`a_n\ge2`$ for all $`n`$ satisfying $`D_{n+1}=a_nD_n`$ and <a href="#long243:eq:shape" data-reference-type="eqref" data-reference="long243:eq:shape">[long243:eq:shape]</a>. The same holds if the identity is assumed only from some index onwards.*

</div>

<div class="proof">

*Proof when $`c`$ and $`m`$ are coprime.* Assume first $`\gcd(c,m)=1`$. Every multiplier must share a prime with $`m`$, but each such prime can occur in at most one multiplier.

*Every $`a_j`$ shares a prime with $`m`$.* Suppose $`\gcd(a_j,m)=1`$. Then $`m`$ is invertible modulo $`a_j`$, so some $`n`$ has $`c+nm\equiv0`$, that is $`a_j\mid C_n`$; and $`a_j\mid D_n`$ for every $`n>j`$, since $`D`$ is multiplicative with $`a_j`$ among its factors. Choosing such an $`n`$ beyond $`j`$ and reading <a href="#long243:eq:shape" data-reference-type="eqref" data-reference="long243:eq:shape">[long243:eq:shape]</a> modulo $`a_j`$ gives $`a_j\mid m`$, contradicting $`\gcd(a_j,m)=1`$ and $`a_j\ge2`$.

*A prime divisor of $`m`$ occurs in at most one $`a_j`$.* Suppose $`p\mid m`$ and $`p\mid a_j`$. For $`n>j`$ we have $`p\mid D_n`$, so <a href="#long243:eq:shape" data-reference-type="eqref" data-reference="long243:eq:shape">[long243:eq:shape]</a> gives $`(a_n-1)C_n\equiv0 \pmod p`$. Now $`C_n=c+nm\equiv c`$, and $`p\nmid c`$ because $`p\mid m`$ and $`\gcd(c,m)=1`$; hence $`p\mid a_n-1`$, so $`p\nmid a_n`$. Thus $`p`$ cannot divide any later multiplier.

This injects infinitely many multipliers into the finite set of prime divisors of $`m`$, a contradiction. ◻

</div>

The case $`\gcd(c,m)=1`$ is the [exclusion when $`c`$ and $`m`$ are coprime](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L147). The special case $`m=c=1`$, worked through in Example <a href="#long243:ex:shape" data-reference-type="ref" data-reference="long243:ex:shape">43</a>, where $`m`$ has no prime divisors at all and the first fact is immediately contradictory, is recorded separately as the [case $`c=m=1`$](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L100).

<div class="proof">

*Removing the scale.* For general $`c`$, set $`g=\gcd(c,m)`$. Equation <a href="#long243:eq:shape" data-reference-type="eqref" data-reference="long243:eq:shape">[long243:eq:shape]</a> gives $`g\mid D_n`$. Both identities are homogeneous in $`D,c,m`$: dividing them by $`g`$ leaves the multipliers unchanged and gives coprime data, excluded by the previous case. ◻

</div>

The formal statements are the [exclusion at every scale](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L286) and the [eventual exclusion](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L350). The latter follows by shifting the orbit to the first index of constant error.

Theorem <a href="#long243:res:constant" data-reference-type="ref" data-reference="long243:res:constant">44</a> excludes an error that is eventually constant and negative, at every magnitude and every scale. Constancy fixes both the possible prime divisors and the congruence used at later indices. For varying magnitudes, even when their prime divisors belong to a fixed finite set, this argument does not supply the same later congruence. It therefore does not settle that case.

<a id="long243:sec:periodic"></a>

# Periodic negative errors

Let the negative error have periodic magnitude $`e_n=-E_n>0`$, so $`e_{n+h}=e_n`$ and $`C_{n+1}=C_n+e_n`$. Summing over a period gives $`C_{n+h}=C_n+M`$, where the positive integer $`M=\sum_{j=0}^{h-1}e_j`$ is the *drift*. Periodicity makes this sum independent of the starting index.

At $`h=1`$ this says that the magnitude is constant and that $`M`$ is its value, which is the situation of Section <a href="#long243:sec:constant" data-reference-type="ref" data-reference="long243:sec:constant">9</a>; Theorem <a href="#long243:res:constant" data-reference-type="ref" data-reference="long243:res:constant">44</a> already excludes it without using the pointwise bound $`e_n<a_n`$ in the proof below. The new case is $`h\ge2`$.

For a constant error, the proof used the finitely many prime divisors of its magnitude. For a periodic error we use the prime divisors of the increase $`M`$ over one period. The required divisibility facts are as follows. Every multiplier $`a_j`$ divides each later denominator, by [persistence of a multiplier](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L382). If a prime divides both $`D_n`$ and $`a_n`$, the numerator update makes it divide $`C_{n+1}`$, the [one-step divisibility implication](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L402). Once it divides both numerator and denominator, it divides every later numerator, denominator and error, by [persistence of a common divisor](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L429).

Periodicity carries this divisibility back to every phase. Suppose $`d\mid M`$ and $`d\mid a_i,a_j`$ with $`i<j`$. Then $`d\mid D_j`$, and $`C_{j+1}=a_jC_j-D_j`$ gives $`d\mid C_{j+1}`$. The common divisor persists in both sequences and in every later error. For any phase $`r`$, choose $`k`$ with $`r+kh\ge j+1`$; periodicity gives $`d\mid e_{r+kh}=e_r`$. Taking $`kh\ge j+1`$ also gives $`d\mid C_{kh}=C_0+kM`$, hence $`d\mid C_0`$. This is [the repeated-divisor implication](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L494); it uses the [period relation](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L461) and the [increase over successive periods](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L476), each iterated through whole periods. A repeated prime can therefore be divided out of the entire system. This explains the induction on $`M`$ in the proof.

<div id="long243:res:periodic" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/NegativeMagnitudeExclusions.lean#L68">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-periodic-comparator">Comparator</a></p>

**Theorem 45** (no periodic negative magnitude). *Let $`a,D,C,e:\mathbb{N}\to\mathbb{N}`$ with $`a_n\ge2`$, $`e_n>0`$ and $`e_n<a_n`$ for every $`n`$, satisfying
``` math
D_{n+1}=a_nD_n,\qquad C_{n+1}=C_n+e_n,\qquad D_n+e_n=(a_n-1)C_n ,
```
and suppose $`e_{n+h}=e_n`$ and $`C_{n+h}=C_n+M`$ for some $`h>0`$ and $`M>0`$. This is impossible.*

</div>

<div class="proof">

*Proof.* We use strong induction on the drift $`M`$. A prime divisor of $`M`$ that recurs among the multipliers need not give an immediate contradiction. It instead divides the whole orbit, allowing us to reduce $`M`$ by that prime and apply the induction hypothesis.

Suppose first that no prime divisor of $`M`$ is a common divisor of $`C_0`$ and of every magnitude. The repeated-divisor implication applies in the contrapositive: a prime divisor of $`M`$ occurring in two of the multipliers would be exactly such a common divisor, so each prime divisor of $`M`$ occurs in at most one multiplier. On the other hand, every multiplier shares a prime with $`M`$. Indeed, if $`\gcd(a_j,M)=1`$, choose $`k\ge1`$ so that $`a_j\mid C_j+kM=C_{j+kh}`$. The same multiplier divides $`D_{j+kh}`$, and periodicity gives $`e_{j+kh}=e_j`$. The identity at $`j+kh`$ therefore implies $`a_j\mid e_j`$, contrary to $`0<e_j<a_j`$. Thus infinitely many multipliers would require distinct prime divisors of the fixed integer $`M`$, a contradiction.

Otherwise some prime $`p`$ divides $`M`$, divides $`C_0`$, and divides every magnitude. Then $`p\mid C_n`$ for every $`n`$, since $`C_{n+1}=C_n+e_n`$ and both summands on the right are divisible by $`p`$, and the same identity $`D_n+e_n=(a_n-1)C_n`$ then gives $`p\mid D_n`$ for every $`n`$. Divide $`D`$, $`C`$ and $`e`$ by $`p`$. The multipliers are untouched, so $`a_n\ge2`$ and $`e_n<a_n`$ persist and the magnitudes stay positive; the three recurrences are homogeneous in $`(D,C,e)`$ and so survive; the period is still $`h`$; and the drift becomes $`M/p<M`$. The inductive hypothesis applies. ◻

</div>

The first of the two cases above is the [exclusion when no prime of $`M`$ divides all phases](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L548), the induction is the [exclusion at every scale](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L690), and the eventual form is the [eventual exclusion](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L802).

The bound $`e_n<a_n`$ rules out $`a_j\mid e_j`$. It follows eventually, without rescaling: on an infinite orbit with periodic positive magnitudes, bounded errors and exponential denominator growth suffice. The identity gives $`C_n>0`$, and periodicity gives
``` math
C_n=\frac{M}{h}n+O(1),\qquad \sup_ne_n<\infty,
```
and $`D_0`$ cannot be zero: otherwise all $`D_n`$ vanish and the defining identity gives $`e_n=(a_n-1)C_n\ge C_n`$, contradicting these bounds. Thus $`D_n\ge2^nD_0`$, and
``` math
a_n-1=\frac{D_n+e_n}{C_n}\longrightarrow\infty.
```
Consequently $`e_n<a_n`$ eventually. Applying the eventual exclusion therefore rules out periodic positive magnitudes without an independent smallness assumption. The numbered theorem retains the pointwise bound used by its checked phase-by-phase proof. The later bounded-negative theorem also excludes this case.

<div id="long243:rem:eventual-error-bound" class="remark">

*Remark 1*. For the tail numerators of \[koizumi2025\], the absolute error satisfies $`|E_n|<a_n`$ eventually. Indeed, under the dictionary in Section <a href="#long243:sec:priorwork" data-reference-type="ref" data-reference="long243:sec:priorwork">3</a>, Lemma 4(2) gives $`-C_n/2\le E_n<C_n/2`$, hence $`|E_n|\le C_n/2`$. The proof of Lemma 4(3) gives $`C_{n+1}\le\tfrac32C_n`$ \[koizumi2025, pp. 11–12\], hence $`C_n\le C_N(3/2)^{n-N}`$ beyond a pseudo-greedy starting index $`N`$. On the other hand, convergence of $`\sum1/a_n`$ gives $`a_n\to\infty`$, and $`a_{n+1}/a_n^2\to1`$ then gives $`a_{n+1}\ge2a_n`$ eventually. Thus $`|E_n|/a_n\to0`$. On a negative-error tail this gives $`e_n<a_n`$.

For integer solutions of <a href="#long243:eq:recurrences" data-reference-type="eqref" data-reference="long243:eq:recurrences">[long243:eq:recurrences]</a>, the same conclusion follows when $`a_n>1`$, $`C_n>0`$ and $`E_n/C_n\to0`$ hold: the calculation in Section <a href="#long243:sec:state" data-reference-type="ref" data-reference="long243:sec:state">4</a> already derives the reciprocal series and its growth from these hypotheses. Summability is not an independent assumption in that setting. The bound $`e_n<a_n`$ is still only eventual, whereas Theorem <a href="#long243:res:periodic" data-reference-type="ref" data-reference="long243:res:periodic">45</a> states it at every index; its eventual form, cited above, is therefore the applicable one. For a periodic magnitude, boundedness of $`e_n`$ and divergence of $`a_n`$ already suffice.

</div>

<a id="long243:sec:barrier"></a>

# Bounded increases and coprimality

For nonperiodic errors, the Chinese remainder theorem replaces the fixed period. It produces a block of consecutive forbidden values. An unbounded numerator with bounded upward steps must enter that block when it first crosses its lower end.

<div id="long243:res:crt" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/ForbiddenBlockCrossing.lean#L26">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-crt-comparator">Comparator</a></p>

**Lemma 46** (shifted blocks of consecutive multiples). *Let $`m_0,\ldots,m_{B-1}`$ be pairwise coprime and at least $`2`$. For every bound there is a $`t`$ beyond it with $`m_i\mid t+i`$ for each $`i<B`$.*

</div>

<div class="proof">

*Proof.* Solve $`t\equiv-i\pmod{m_i}`$ simultaneously by the Chinese remainder theorem. Adding a sufficiently large multiple of $`\prod_i m_i`$ puts the solution beyond the prescribed bound. ◻

</div>

Lemma <a href="#long243:res:crt" data-reference-type="ref" data-reference="long243:res:crt">46</a> matches each modulus $`m_i`$ to its own multiple $`t+i`$ inside a window of $`B`$ consecutive integers. Matchings of a set of integers to distinct multiples in an interval are the subject of Erdős Problem #650, solved by van Doorn, Li and Tang: for every set $`S`$ of $`k`$ positive integers, every open interval of length $`2\max S`$ contains distinct multiples of at least $`\min(k,\lceil 2\sqrt{k}\,\rceil)`$ elements of $`S`$, and this count is optimal \[vandoornlitang2026, Theorem 2.1\]. Their extremal construction uses the same Chinese remaindering for moduli that need not be pairwise coprime, with their Claim 3.2 supplying the divisibility of residue differences by greatest common divisors that the generalised theorem requires \[vandoornlitang2026, pp. 4–5\]. The first-crossing argument below needs only the pairwise coprime case.

<div id="long243:ex:crt" class="example">

**Example 47** (a block of three consecutive multiples). Take $`B=3`$ and $`(m_0,m_1,m_2)=(3,4,5)`$. The congruences $`t\equiv0\pmod3`$, $`t\equiv3\pmod4`$ and $`t\equiv3\pmod5`$ hold exactly when $`t\equiv3\pmod{60}`$. At $`t=3`$ the block is $`3,4,5`$ with $`3\mid3`$, $`4\mid4`$ and $`5\mid5`$; at $`t=63`$ it is $`63,64,65`$ with $`3\mid63`$, $`4\mid64`$ and $`5\mid65`$. A sequence of natural numbers that starts at $`0`$, tends to infinity and rises by at most $`3`$ at each step cannot step over the block $`\{3,4,5\}`$: it has a first value at least $`3`$, that value is at most $`5`$, and every member of $`\{3,4,5\}`$ is divisible by one of the three moduli.

</div>

<div id="long243:res:barrier" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/ForbiddenBlockCrossing.lean#L44">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-barrier-comparator">Comparator</a></p>

**Theorem 48** (bounded increases and coprimality to earlier moduli). *Let $`u:\mathbb{N}\to\mathbb{N}`$ tend to infinity with $`u_{n+1}\le u_n+B`$ for a fixed integer $`B\ge1`$. Then $`u`$ cannot remain coprime to infinitely many fresh pairwise coprime moduli: there is no family of pairwise coprime $`m_i\ge2`$, one for each index, such that $`\gcd(m_i,u_t)=1`$ whenever $`i<t`$.*

</div>

The CRT block must lie above the initial segment where some moduli are not yet available. No monotonicity of $`u`$ is assumed.

<div class="proof">

*Proof.* Choose $`m_0,\ldots,m_{B-1}`$ and use Lemma <a href="#long243:res:crt" data-reference-type="ref" data-reference="long243:res:crt">46</a> to find $`t>\max(u_0,\ldots,u_B)`$ with $`m_i\mid t+i`$ for $`0\le i<B`$. Since $`u_n\to\infty`$, there is a first $`n>B`$ with $`u_n\ge t`$. Minimality and the rise bound give
``` math
t\le u_n\le u_{n-1}+B<t+B.
```
Hence $`u_n=t+i`$ for some $`0\le i<B<n`$, so $`m_i\mid u_n`$. The inequality $`i<n`$ now permits the avoidance hypothesis, which says $`\gcd(m_i,u_n)=1`$; this contradicts $`m_i\ge2`$. The argument uses the first crossing of the CRT block, not monotonicity of $`u`$. ◻

</div>

Only unboundedness above is used to obtain this first crossing. Divergence is stated because it holds for the reduced rational tail in the application. This distinction also explains why the weighted proof in Section <a href="#long243:sec:lcmrecords" data-reference-type="ref" data-reference="long243:sec:lcmrecords">6</a> works with an unbounded running maximum, without assuming that its numerator tends to infinity.

Divergence forces $`u`$ to reach the forbidden block, and the uniform rise bound prevents it from jumping over the block. A bound only along a subsequence would leave the intervening steps unrestricted. Without a scale restriction on the moduli, Proposition <a href="#long243:res:variablerise" data-reference-type="ref" data-reference="long243:res:variablerise">62</a> gives an unbounded coprime walk with rises $`o(\log\log u_n)`$. The same forbidden-block crossing, under a two-sided bound on the error, appears in the proof of Bado’s Theorem 5.1 \[bado2026, pp. 4–5\], posted in September 2026.

In the application, $`m_i`$ is the $`i`$th multiplier. Its coprimality is known only for later numerators, which explains the condition $`i<t`$.

To apply the preceding theorem, we reduce $`C_n/D_n`$ to lowest terms and require that no further common factor be cancelled. In that case the reduced numerators and denominators still satisfy the original recurrences. The relevant coprimality is as follows.

<div id="long243:res:reduced" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Reduction.lean#L16">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-reduced-comparator">Comparator</a></p>

**Proposition 49** (persistent coprimality). *Suppose that $`\gcd(u_n,v_n)=1`$ at every index and
``` math
u_{n+1}+v_n=a_nu_n,\qquad v_{n+1}=a_nv_n.
```
Then $`\gcd(a_n,v_n)=1`$, the $`a_n`$ are pairwise coprime, and $`\gcd(a_i,u_t)=1`$ whenever $`i<t`$.*

</div>

<div class="proof">

*Proof.* A common prime divisor of $`a_n`$ and $`v_n`$ would divide both $`u_{n+1}=a_nu_n-v_n`$ and $`v_{n+1}=a_nv_n`$, contradicting their coprimality. Hence $`\gcd(a_n,v_n)=1`$. For $`i<t`$, the denominator recurrence gives $`a_i\mid v_t`$. Combining this with $`\gcd(a_t,v_t)=1`$ proves that $`a_i`$ and $`a_t`$ are coprime; combining it with $`\gcd(u_t,v_t)=1`$ proves that $`a_i`$ and $`u_t`$ are coprime. ◻

</div>

These are the [step coprimality](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L989), the [pairwise coprimality](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1016), and the [coprimality to each earlier multiplier](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1030). Applying Theorem <a href="#long243:res:barrier" data-reference-type="ref" data-reference="long243:res:barrier">48</a> shows that a numerator satisfying these conditions cannot tend to infinity with uniformly bounded upward increments. This is the [reduced exclusion under bounded upward increments](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1041), together with its eventual form, the [version with an eventual increment bound](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1066).

<div id="long243:ex:reduced" class="example">

**Example 50** (coprimality in Sylvester’s sequence). Put $`u_n=1`$ and $`v_n=D_n=1,2,6,42,1806,\ldots`$ as in Example <a href="#long243:ex:sylvester" data-reference-type="ref" data-reference="long243:ex:sylvester">15</a>, with multipliers $`a_n=v_n+1=2,3,7,43,1807,\ldots`$. Then $`\gcd(u_n,v_n)=1`$, $`u_{n+1}+v_n=1+v_n=a_nu_n`$ and $`v_{n+1}=a_nv_n`$, so Proposition <a href="#long243:res:reduced" data-reference-type="ref" data-reference="long243:res:reduced">49</a> applies and gives the classical fact that Sylvester’s numbers are pairwise coprime. Its numerator is constant, so it satisfies every hypothesis of the exclusion just stated except divergence; since the tail exists, that hypothesis cannot be dropped.

</div>

The fraction $`C_n/D_n`$ in Section <a href="#long243:sec:state" data-reference-type="ref" data-reference="long243:sec:state">4</a> need not be in lowest terms. To use the preceding argument, we must show that the common factor stops changing. One uniform bound on the negative magnitudes at arbitrarily late indices suffices: each gcd divides every later gcd, and at a negative index it also divides the nonzero magnitude. Thus a bound at arbitrarily late negative indices bounds the entire gcd sequence. The next proposition justifies dividing by its eventual value.

<div id="long243:res:gcdstab" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Reduction.lean#L103">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-gcdstab-comparator">Comparator</a></p>

**Proposition 51** (the tail gcd stabilises). *Let $`a,D,C:\mathbb{N}\to\mathbb{N}`$ satisfy $`C_{n+1}+D_n=a_nC_n`$ and $`D_{n+1}=a_nD_n`$, and put $`E_n=D_n-(a_n-1)C_n`$. Suppose some fixed integer $`B\ge1`$ satisfies $`-B\le E_n<0`$ at infinitely many indices. Then $`\gcd(C_n,D_n)`$ is eventually constant. Dividing $`C_n,D_n`$ by its eventual value gives coprime sequences satisfying the same recurrences.*

</div>

<div class="proof">

*Proof.* First, $`C_n>0`$ at every index. If $`C_n=0`$, the nonnegative recurrence forces $`C_{n+1}=D_n=0`$, and both sequences then vanish at all later indices. This contradicts the existence of arbitrarily late negative errors.

The two recurrences give $`G_n\mid G_{n+1}`$ for $`G_n=\gcd(C_n,D_n)`$, as in [the gcd divisibility relation](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1430). Also $`G_n=\gcd(C_n,|E_n|)`$, since $`D_n=E_n+(a_n-1)C_n`$; at a negative index this is [the gcd identity with the negative magnitude](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1587). For any $`n`$, choose $`t\ge n`$ with $`-B\le E_t<0`$. Then
``` math
G_n\le G_t\le |E_t|\le B.
```
The entire positive divisibility chain is therefore bounded and eventually constant, by [stabilisation of a bounded divisibility chain](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1605). In Lean this is the [gcd stabilisation result](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1636). Dividing both sequences by the eventual value preserves the recurrences and gives coprime numerator and denominator at every later index. ◻

</div>

Other negative errors may exceed $`B`$ in magnitude. Gcd stabilisation uses the bounded witnesses, whereas the CRT application needs a bound on *every* upward increment.

Vanishing relative error also gives sparsity of the strict gcd increases. The next proposition asserts long finite intervals of constancy, not constancy on an infinite tail. For $`a,C,D:\mathbb{N}\to\mathbb{N}`$ satisfying <a href="#long243:eq:recurrences" data-reference-type="eqref" data-reference="long243:eq:recurrences">[long243:eq:recurrences]</a> with $`C_n>0`$, put
``` math
G_n=\gcd(C_n,D_n),\qquad
 \Gamma(N)=\#\{0\le j<N:G_j<G_{j+1}\}.
```

<div id="long243:res:gcdsparse" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Limits.lean#L97">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-gcdsparse-comparator">Comparator</a></p>

**Proposition 52** (vanishing relative error makes strict gcd changes sparse). *Let $`a,C,D:\mathbb{N}\to\mathbb{N}`$ satisfy $`C_{n+1}+D_n=a_nC_n`$ and $`D_{n+1}=a_nD_n`$ with $`C_n>0`$, and put $`E_n=D_n-(a_n-1)C_n`$, $`G_n=\gcd(C_n,D_n)`$ and $`\Gamma(N)=\#\{0\le j<N:G_j<G_{j+1}\}`$. If $`|E_n|/C_n\to0`$, then $`\Gamma(N)=o(N)`$. Moreover, for every starting bound $`B`$ and block length $`L`$, some $`n\ge B`$ satisfies
``` math
G_n=G_{n+1}=\cdots=G_{n+L}.
```*

</div>

The first assertion is the [sublinear strict-growth theorem](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2186); the second is the [arbitrarily late constant-block theorem](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2202). The proof first converts vanishing relative error into subexponential growth of $`C_n`$. Each strict divisibility increase of $`G_n`$ contributes a factor of at least $`2`$, so $`2^{\Gamma(N)}G_0\le G_N\le C_N`$. Taking logarithms gives $`\Gamma(N)=o(N)`$. For $`L=0`$ the second assertion is immediate. For $`L\ge1`$, if every block of $`L`$ successive transitions beyond $`B`$ contained a strict increase, disjoint such blocks would give $`\Gamma(N)\ge(N-B)/L-O(1)`$, a contradiction.

The starting index may depend on the block length; arbitrarily long constant blocks do not give an infinite constant tail. Proposition <a href="#long243:res:gcdstab" data-reference-type="ref" data-reference="long243:res:gcdstab">51</a> needs additional bounded negative witnesses, which Proposition <a href="#long243:res:gcdsparse" data-reference-type="ref" data-reference="long243:res:gcdsparse">52</a> does not supply.

<div id="243-long-bounded-increases">

</div>

<a id="long243:sec:bounded"></a>

# Bounded negative part

The lower bound $`E_n\ge-B`$ has two uses. At negative indices it bounds the gcd, making it stable. At every index it bounds the upward step $`C_{n+1}-C_n=-E_n`$. We can therefore combine the preceding coprimality and first-crossing arguments.

Without the denominator recurrence, $`C_n=c+bn`$, $`E_n=-b`$ would be a counterexample for any positive integers $`b,c`$. Theorem <a href="#long243:res:constant" data-reference-type="ref" data-reference="long243:res:constant">44</a> excludes this exact-orbit behaviour. The separate summability criterion in the next section needs only the scalar update. For positive integer solutions of <a href="#long243:eq:recurrences" data-reference-type="eqref" data-reference="long243:eq:recurrences">[long243:eq:recurrences]</a> with vanishing relative error, both criteria are equivalent to eventual zero error. Neither extra estimate has been derived from the unrestricted hypotheses.

<div id="long243:res:bounded" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2360">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-bounded-comparator">Comparator</a></p>

**Theorem 53** (bounded negative part). *Let $`a,C,D:\mathbb{N}\to\mathbb{N}`$ satisfy $`a_n>1`$, $`C_n>0`$, and
``` math
C_{n+1}+D_n=a_nC_n,\qquad D_{n+1}=a_nD_n
 \quad(n\ge0).
```
Put $`E_n=D_n-(a_n-1)C_n`$. If
``` math
\frac{E_n}{C_n}\longrightarrow0
 \quad\text{and}\quad E_n\ge-B\quad\text{for all sufficiently large }n
```
for some integer $`B\ge0`$, then $`E_n=0`$ for all sufficiently large $`n`$.*

</div>

The limit is equivalent, for positive $`C_n`$, to the integer condition $`K|E_n|<C_n`$ eventually for each $`K\in\mathbb{N}`$. This is the form used by the linked declaration. Its $`K=1`$ case gives $`|E_n|<C_n`$ eventually.

<div class="proof">

*Proof.* Suppose that the error fails to vanish eventually. After the point from which $`|E_n|<C_n`$ always holds, Theorem <a href="#long243:res:absorb" data-reference-type="ref" data-reference="long243:res:absorb">24</a> excludes every zero. Hence $`|E_n|\ge1`$, and the relative limit forces $`C_n\to\infty`$.

There are infinitely many negative indices, since otherwise Theorem <a href="#long243:res:descent" data-reference-type="ref" data-reference="long243:res:descent">42</a> would give eventual zero. At each sufficiently late negative index, $`1\le-E_n\le B`$, so $`B\ge1`$. Proposition <a href="#long243:res:gcdstab" data-reference-type="ref" data-reference="long243:res:gcdstab">51</a> makes $`G_n=\gcd(C_n,D_n)`$ stabilise to an integer $`g>0`$. The divided sequences $`u_n=C_n/g`$, $`v_n=D_n/g`$ satisfy the coprime recurrences, with $`u_n\to\infty`$ and $`u_{n+1}-u_n=-E_n/g\le B`$. Their coprimality properties from Proposition <a href="#long243:res:reduced" data-reference-type="ref" data-reference="long243:res:reduced">49</a> now contradict Theorem <a href="#long243:res:barrier" data-reference-type="ref" data-reference="long243:res:barrier">48</a>. ◻

</div>

<div id="long243:res:cor" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2412">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-cor-comparator">Comparator</a></p>

**Corollary 54**. *Under the hypotheses of Theorem <a href="#long243:res:bounded" data-reference-type="ref" data-reference="long243:res:bounded">53</a>, the multipliers satisfy $`a_{n+1}=a_n^{2}-a_n+1`$ for all sufficiently large $`n`$.*

</div>

<div class="proof">

*Proof.* Theorem <a href="#long243:res:bounded" data-reference-type="ref" data-reference="long243:res:bounded">53</a> gives eventual zero error. Since $`C_{n+1}>0`$, Theorem <a href="#long243:res:eventual" data-reference-type="ref" data-reference="long243:res:eventual">23</a> gives the recurrence. ◻

</div>

To apply it to Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>, delete a finite prefix and use Koizumi’s Corollary 3 \[koizumi2025, p. 9\]. The remaining sequence is the pseudo-greedy expansion of its own reciprocal sum. His Lemma 4 gives positive integer numerators $`c_n`$, denominators $`d_n`$ and errors $`e_n`$ with
``` math
c_{n+1}=a_nc_n-d_n,\qquad d_{n+1}=a_nd_n,\qquad
 e_n=d_n-(a_n-1)c_n.
```
The terms $`a_n`$ eventually exceed one, and $`e_n/c_n\to0`$ by that corollary. The same construction gives $`-c_n/2\le e_n<c_n/2`$. The additional condition still required is an eventual lower bound $`e_n\ge-B`$. Neither Koizumi’s construction nor the constant and periodic exclusions above establish this bound for every rational sum in the problem. The result therefore remains conditional.

<div id="243-long-relative-increase">

</div>

<a id="long243:sec:mass"></a>

# Finite total relative increase

We can bound a positive integer sequence by multiplying the relative increases of its terms. If their sum converges, that product is finite. Only finitely many upward integer steps can then occur, and descent finishes the argument. No denominator recurrence is needed. For comparison, $`C_n=n+1`$ and $`C_n=(n+1)^2`$ have relative increases tending to zero but divergent sums. The eventual Sylvester recurrence gives an eventually constant numerator, so it satisfies the summability condition.

<div class="samepage">

<div id="long243:res:mass" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Frontier.lean#L84">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-mass-comparator">Comparator</a></p>

**Theorem 55** (finite sum of relative increases). *Let $`C_n\in\mathbb{N}_{>0}`$ and $`E_n\in\mathbb{Z}`$ satisfy $`C_{n+1}=C_n-E_n`$. If
``` math
\sum_{n=0}^{\infty}\frac{(-E_n)_+}{C_n}<\infty,
```
then $`E_n=0`$ eventually. For an exact reciprocal-tail orbit this implies $`a_{n+1}=a_n^2-a_n+1`$ eventually. No hypothesis $`|E_n|/C_n\to0`$ is required.*

</div>

</div>

<div class="proof">

*Proof.* Put $`\delta_n=(-E_n)_+/C_n`$. The update gives $`C_{n+1}\le C_n(1+\delta_n)`$, so
``` math
C_N\le C_0\prod_{n<N}(1+\delta_n)
 \le C_0\exp\!\left(\sum_n\delta_n\right).
```
Choose an integer upper bound $`K`$ for $`C_n`$. Each strict rise of the integer sequence contributes at least $`1/K`$ to $`\sum_n\delta_n`$, so there are only finitely many rises. The remaining positive integer sequence is nonincreasing and therefore stabilises, forcing $`E_n=0`$. The recurrence follows from Theorem <a href="#long243:res:eventual" data-reference-type="ref" data-reference="long243:res:eventual">23</a>, since $`C_n>0`$. ◻

</div>

Integer increments suffice even for positive real $`C_0`$: the bounded values lie in the finite set $`(C_0+\mathbb{Z})\cap(0,K]`$, so the same proof works. The Lean statement retains integer-valued $`C_n`$.

The two indispensable features of this argument are positivity and discrete increments. With $`C_n=1+1/(n+1)`$ and $`E_n=1/((n+1)(n+2))`$, the numerator decreases forever with zero relative-increase sum, but the errors are not integers. With $`C_n=-n-1`$ and $`E_n=1`$, the increments are integers but positivity fails.

The pseudo-greedy gap version, with the same product bound and integer descent, appears in the 12 August 2026 working report \[erdosproblemaday243, A global termination criterion\]. Bado additionally accounts for factors removed in LCM clearing \[bado2026, Thm. 11.1 and Remark 11.3, p. 9\]. In the notation of Section <a href="#long243:sec:lcmrecords" data-reference-type="ref" data-reference="long243:sec:lcmrecords">6</a>, the update gives
``` math
\log U_N\le\log U_0+
 \sum_{n<N}\frac{(-E_n)_+}{C_n}-\sum_{n<N}\log\rho_n.
```
His sufficient condition is an upper bound on the difference of these two sums. The subtractive term records the decrease caused by a repeated factor in the denominator. It may offset some relative increases; the hypothesis does not require either sum to converge separately. Unlike the scalar criterion above, this argument also uses the pseudo-greedy limit: bounded $`U_n`$ and $`V_n/U_n=E_n/C_n\to0`$ make the integer $`V_n`$ eventually zero, after which $`\rho_nU_{n+1}=U_n`$ gives eventual constancy.

Corollary 3 \[koizumi2025, p. 9\] and Lemma 4  \[koizumi2025, pp. 11–12\] supply the same positive integer update after a finite restart. Theorem <a href="#long243:res:mass" data-reference-type="ref" data-reference="long243:res:mass">55</a> therefore applies if the relative-increase sum converges. This is the sole additional hypothesis, asked for in Problem <a href="#long243:res:masshyp" data-reference-type="ref" data-reference="long243:res:masshyp">61</a>; the cited construction does not establish it.

<div id="long243:ex:mass" class="example">

**Example 56** (the product bound at a geometric rate). Suppose $`C_0=100`$ and $`(-E_n)_+/C_n\le2^{-n-1}`$ for every $`n`$, so that the sum of relative increases is at most $`1`$; the constraint at $`n=0`$ still permits $`E_0`$ as negative as $`-50`$. Since $`1+x\le e^{x}`$,
``` math
C_N\le100\prod_{n<N}\bigl(1+2^{-n-1}\bigr)\le100e<272
```
for every $`N`$. For all sufficiently large $`n`$, we have $`2^{-n-1}<1/272`$. A strict rise would then force $`(-E_n)_+/C_n\ge1/C_n>1/272`$, a contradiction. Thus $`C_n`$ is eventually nonincreasing; as a positive integer sequence it stabilises, and $`E_n=0`$ thereafter. The constant $`272`$ comes from the total mass and not from any single magnitude, which is why the hypothesis of Theorem <a href="#long243:res:mass" data-reference-type="ref" data-reference="long243:res:mass">55</a> is summability of $`(-E_n)_+/C_n`$ and not a bound on it.

</div>

<div id="243-long-open-questions">

</div>

<a id="long243:sec:open"></a>

# Further questions

We collect the restrictions on a possible counterexample and the estimates which would exclude it. The constant and periodic arguments concern all-negative tails. They leave open a periodic pattern seen only along the negative indices of a mixed-sign sequence. The unrestricted problem remains unresolved here.

<div id="long243:res:frontier" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Frontier.lean#L151">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-frontier-comparator">Comparator</a></p>

**Proposition 57** (necessary conditions on a counterexample). *For the integer tail attached to any counterexample to Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>,
``` math
E_n\ne0\quad\hbox{eventually},\qquad
 \frac{|E_n|}{C_n}\longrightarrow0,
```
and
``` math
\limsup_{\substack{n\to\infty\\E_n<0}}(-E_n)=\infty,
 \qquad
 \sum_{n=0}^{\infty}\frac{(-E_n)_+}{C_n}=\infty .
```
In particular, negative indices occur infinitely often. Thus the remaining regime consists of unbounded negative errors along exact reciprocal tails for which the sum of relative increases diverges.*

</div>

<div class="proof">

*Proof.* Koizumi’s construction gives vanishing relative error after a finite shift, hence $`|E_n|<C_n`$ eventually. Absorption then makes $`E_n\ne0`$ eventually, since eventual zero would give the Sylvester recurrence. Descent excludes an eventually nonnegative error. Theorem <a href="#long243:res:bounded" data-reference-type="ref" data-reference="long243:res:bounded">53</a> excludes a bounded negative part, and Theorem <a href="#long243:res:mass" data-reference-type="ref" data-reference="long243:res:mass">55</a> excludes convergence of the sum of relative increases. These statements are unchanged by deleting a finite prefix. ◻

</div>

Proposition <a href="#long243:res:frontier" data-reference-type="ref" data-reference="long243:res:frontier">57</a> does not assert infinitely many prime divisors of the error magnitudes. Nor are its numerical conditions alone a reformulation of the problem: the numerator and denominator must satisfy the exact recurrences. With those recurrences, positivity and vanishing relative error, Section <a href="#long243:sec:state" data-reference-type="ref" data-reference="long243:sec:state">4</a> supplies the reciprocal-series realisation. The following exact-orbit question is therefore equivalent to the original problem.

<div id="long243:res:excursions" class="problem">

**Problem 58** (unbounded negative errors with divergent relative sum). Exclude, or construct, natural-number sequences $`(a,D,C)`$ satisfying <a href="#long243:eq:recurrences" data-reference-type="eqref" data-reference="long243:eq:recurrences">[long243:eq:recurrences]</a>, with $`a_n>1`$ and $`C_n>0`$, whose multipliers satisfy $`\lim_n a_{n+1}/a_n^{2}=1`$ and whose error satisfies vanishing relative error, and which is negative infinitely often with magnitudes unbounded along that infinite set and
``` math
\sum_n\frac{(-E_n)_+}{C_n}=\infty .
```
Such an orbit fails the bounded-negative-part and summable-relative-increase hypotheses. By Proposition <a href="#long243:res:frontier" data-reference-type="ref" data-reference="long243:res:frontier">57</a> the integer tail of a counterexample is such an orbit after deletion of a finite prefix, so an exclusion would settle Problem #243. Conversely, a global orbit with the displayed properties has $`C_n/D_n\to0`$ by Section <a href="#long243:sec:state" data-reference-type="ref" data-reference="long243:sec:state">4</a>. The [reciprocal-series realisation](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1955) then identifies its reciprocal sum as $`C_0/D_0`$. After deletion of a finite prefix the multipliers are strictly increasing, and the infinitely many negative errors rule out a Sylvester tail. It is therefore a counterexample to Problem #243. Finite admissible prefixes alone do not provide such a construction.

</div>

<div id="long243:rem:recurrence-without-relative-bound" class="remark">

*Remark 2*. The recurrences alone admit unbounded negative errors for which $`\sum_n(-E_n)_+/C_n`$ diverges. The following example fails both the relative-error and growth assumptions of Problem <a href="#long243:res:excursions" data-reference-type="ref" data-reference="long243:res:excursions">58</a>. Put
``` math
C_n=2^{n},\qquad b_0=2,\qquad b_{n+1}=\tfrac12 b_n(b_n+2),\qquad
 a_n=b_n+2,\qquad D_n=b_nC_n ,
```
so that $`(b_n)=2,4,12,84,3612,\ldots`$ and $`(a_n)=4,6,14,86,3614,\ldots`$. Every $`b_n`$ is a positive even integer, since $`b_n=2k`$ gives $`b_{n+1}=2k(k+1)`$, so all four sequences are $`\mathbb{N}`$-valued. They satisfy both recurrences: $`C_{n+1}+D_n=2^{n}(2+b_n)=a_nC_n`$ and $`D_{n+1}=b_{n+1}2^{n+1}=b_n(b_n+2)2^{n}=a_nD_n`$. Its error is
``` math
E_n=D_n-(a_n-1)C_n=b_n2^{n}-(b_n+1)2^{n}=-C_n ,
```
so the negative magnitudes $`2^{n}`$ are unbounded and $`\sum_n(-E_n)_+/C_n`$ diverges. Here $`|E_n|=C_n`$ at every index, so both the strict inequality $`|E_n|<C_n`$ and the vanishing relative error fail. The multipliers satisfy $`a_{n+1}=\tfrac12(a_n^{2}-2a_n+4)`$, so $`a_{n+1}/a_n^{2}\to\tfrac12`$ and the growth hypothesis fails as well. The example therefore says nothing about Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>, and it does not isolate the error bounds: $`E_n=-C_n`$ at every index forces that multiplier recurrence, so growth fails with them. It is recorded only to show that the two recurrences alone do not force the required conclusion.

</div>

<a id="a-scalar-profile-need-not-satisfy-the-recurrences."></a>

#### A scalar profile need not satisfy the recurrences.

The example $`C_n=n^2+1`$, $`E_n=-(2n+1)`$ satisfies the numerator update, $`|E_n|/C_n\to0`$, $`\log C_n=o(n)`$ and $`\sum_n(E_n/C_n)^2<\infty`$. It is not an exact reciprocal-tail orbit. Indeed, $`C_2=5`$, $`C_3=10`$ and $`C_4=17`$. The first numerator update forces $`5\mid D_2`$; the multiplicative denominator update gives $`5\mid D_3`$; the next numerator update then forces $`5\mid C_4`$, a contradiction. This is the failed-route example referred to at the end of the short note: subexponential size and a small relative error do not supply arithmetic compatibility.

<a id="growth-of-the-factors-repeated-in-the-denominator"></a>

## Growth of the factors repeated in the denominator

To compare repeated prime factors in the denominator with its total size, define
``` math
L_0=D_0,\qquad L_{n+1}=\operatorname{lcm}(L_n,a_n),\qquad M_n=\frac{D_n}{L_n}.
```
The integer $`M_n`$ records prime factors counted repeatedly in $`D_n=D_0\prod_{j<n}a_j`$ but only to their largest exponent in $`L_n`$; thus $`M_nL_n=D_n`$. Problem <a href="#long243:res:lcmheight" data-reference-type="ref" data-reference="long243:res:lcmheight">59</a> asks whether failure of the Sylvester recurrence forces exponential growth of $`M_n`$, contradicting its subexponential upper bound. The following recovery estimate is local and does not supply that lower bound.

<a id="cancellation-during-recovery-intervals"></a>

## Cancellation during recovery intervals

The LCM quotient $`M_n`$ need not equal the common divisor $`G_n`$ removed by reduction to lowest terms. Since $`M_n`$ divides both $`C_n`$ and $`D_n`$, we have $`M_n\mid G_n`$, but equality is not assumed. The following estimate concerns the successive reduction factors, over an interval where the reduced numerator regains its starting value. In the calculation below, $`h_n`$ is the factor removed at step $`n`$, $`c_n`$ is a positive integer with $`c_n^2\mid h_n`$, and $`\tilde e_n`$ denotes the signed reduced error, as in Section <a href="#long243:sec:records" data-reference-type="ref" data-reference="long243:sec:records">7</a>. For the estimate itself, let $`u,h,c:\mathbb{N}\to\mathbb{N}`$ and $`\tilde e:\mathbb{N}\to\mathbb{Z}`$ satisfy
``` math
h_nu_{n+1}=u_n-\tilde e_n,
 \qquad u_n>0,
 \qquad h_n>0.
```
Fix $`K,r,L\in\mathbb{N}`$ with $`K,L>0`$, assume
``` math
K|\tilde e_{r+i}|<u_{r+i}\quad(0\le i<L),
 \qquad u_r\le u_{r+L},
```
and let $`R`$ be a finite family of moduli. Suppose every $`m_q`$, $`q\in R`$, divides $`\prod_{r\le n<r+L}c_n`$, and that $`c_n^2\mid h_n`$ throughout the interval. Then
``` math
\begin{equation}
\label{long243:eq:repair-entropy}
 K^L\operatorname{lcm}(m_q:q\in R)^2<(K+1)^L.
\end{equation}
```
To see this, divide the recurrence by $`u_n`$ and multiply over the interval:
``` math
\left(\prod_{r\le n<r+L}h_n\right)\frac{u_{r+L}}{u_r}
 =\prod_{r\le n<r+L}\left(1-\frac{\tilde e_n}{u_n}\right)
 <(1+1/K)^L.
```
Recovery makes the endpoint ratio at least $`1`$, giving $`\prod_{r\le n<r+L}h_n<(1+1/K)^L`$. Without $`u_r\le u_{r+L}`$, a small endpoint ratio could conceal a large cancellation product. The least common multiple of the $`m_q`$ divides the product of the $`c_n`$, and $`c_n^2\mid h_n`$ at every step. Its square therefore divides, and is at most, the positive integer $`\prod_{r\le n<r+L}h_n`$. Multiplying by $`K^L`$ proves the claimed bound. This is the [bound on cancellation over a recovery interval](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/RepairEntropy.lean#L48).

The square in <a href="#long243:eq:repair-entropy" data-reference-type="eqref" data-reference="long243:eq:repair-entropy">[long243:eq:repair-entropy]</a> comes from the assumption $`c_n^2\mid h_n`$. If the least common multiple of the chosen moduli is at least $`2^{|R|}`$, then
``` math
K^L4^{|R|}<(K+1)^L.
```
The formal consequence is [the bound on the number of independent moduli](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/RepairEntropy.lean#L78). Taking logarithms gives the explicit bound
``` math
\frac{|R|}{L}<\frac{\log(1+1/K)}{\log4}
 \le\frac1{K\log4}.
```
Thus the number of these moduli is small relative to the recovery length when the relative-error bound is small. This statement requires the lower bound $`2^{|R|}`$ on their least common multiple; it does not apply to an arbitrary family with repeated prime factors.

For a fixed number of steps, the same estimate has a simpler consequence: a sufficiently late recovery cannot include any cancellation. If $`K|\tilde e_n|<u_n`$ eventually for every $`K`$, then for each fixed $`L>0`$ there is an $`N`$ such that every recovery $`u_r\le u_{r+L}`$ with $`r\ge N`$ satisfies
``` math
\prod_{0\le i<L}h_{r+i}=1.
```
Indeed, choose $`K`$ so large that $`(1+1/K)^L<2`$ and apply the same product estimate beyond its error threshold. The positive integer product is then smaller than $`2`$, so it equals $`1`$. The same $`K`$ works for every length $`1\le j\le L`$, since $`(1+1/K)^j\le(1+1/K)^L<2`$. Thus, after a sufficiently late step with $`h_n>1`$, the numerator cannot regain its starting value at any of the next $`L`$ indices. This includes a recovery followed by another fall before the last endpoint. The fixed-length conclusion is formalised as [absence of late cancellation during recovery intervals of fixed length](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/RepairEntropy.lean#L107). The threshold $`N`$ depends on $`L`$: late cancellations require longer recoveries, but have not been excluded. A global contradiction needs control of those varying lengths and a lower bound on the moduli’s least common multiple; the interval estimate supplies neither.

<div id="long243:res:lcmheight" class="problem">

**Problem 59** (growth of repeated denominator factors). For every rational-tail orbit satisfying the hypotheses but not the conclusion of Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>, must
``` math
\limsup_{n\to\infty}\frac{\log M_n}{n}>0?
```
Equivalently, must there be a $`K\ge1`$ for which
``` math
2^n\le M_n^K
```
at infinitely many indices?

</div>

The two displayed formulations are equivalent up to changing the positive constant; the second is not a weaker target. Section <a href="#long243:sec:lcmrecords" data-reference-type="ref" data-reference="long243:sec:lcmrecords">6</a> already gives $`1\le M_n\le C_n`$, hence $`\log M_n/n\to0`$ on every orbit under consideration. A positive answer would therefore be a contradiction, not a further compatible necessary condition. It would prove Problem #243. The missing step is to force exponential growth of $`M_n`$ from failure of the Sylvester recurrence.

There is also a more local-looking question whose content is nevertheless the entire prefix. Put $`A_n=\prod_{j<n}a_j`$, so $`D_n=D_0A_n`$. From
``` math
D_0A_n=(a_n-1)C_n+E_n
```
one immediately obtains
``` math
\gcd(A_n,a_n-1)\mid E_n.
```
The checked [tail-height estimate](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2170) and vanishing relative error make $`|E_n|`$ subexponential in $`n`$.

<div id="long243:res:prefixgcd" class="problem">

**Problem 60** (common factors of the prefix and $`a_n-1`$). In every rational-tail orbit satisfying the hypotheses but not the conclusion of Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>, is
``` math
\limsup_{n\to\infty}
 \frac{\log\gcd(A_n,a_n-1)}{n}>0?
```
Equivalently, do there exist $`\eta>0`$ and infinitely many $`n`$ such that $`\gcd(A_n,a_n-1)\ge e^{\eta n}`$?

</div>

By Proposition <a href="#long243:res:frontier" data-reference-type="ref" data-reference="long243:res:frontier">57</a>, the error is nonzero eventually. The displayed divisibility therefore bounds $`\gcd(A_n,a_n-1)`$ by $`|E_n|`$ at every sufficiently late index. A positive answer contradicts the subexponential bound on that error. Arbitrarily long locally admissible blocks do not answer this question: the gcd uses the complete prefix.

<a id="the-direct-analytic-question"></a>

## The direct analytic question

<div id="long243:res:masshyp" class="problem">

**Problem 61** (summability from rationality). Let $`(a_n)`$ satisfy the hypotheses of Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>, and let $`(D_n,C_n,E_n)`$ be its integer tail. Must
``` math
\sum_{n=0}^{\infty}\frac{(-E_n)_+}{C_n}<\infty ?
```

</div>

An affirmative answer closes Problem #243 by Theorem <a href="#long243:res:mass" data-reference-type="ref" data-reference="long243:res:mass">55</a>. Since the summands tend to zero and $`\log(1+t)\sim t`$, convergence is equivalent to bounded partial products $`\prod_{n<N}(1+(-E_n)_+/C_n)`$. A negative answer requires the full growth and rationality hypotheses, not merely a locally admissible orbit. By Theorem <a href="#long243:res:weightedrecord" data-reference-type="ref" data-reference="long243:res:weightedrecord">26</a>, finiteness of <a href="#long243:eq:weightedgrowth" data-reference-type="eqref" data-reference="long243:eq:weightedgrowth">[long243:eq:weightedgrowth]</a> for one nonincreasing weight with divergent integral and one fixed $`B\ge0`$ also suffices. The equivalent record-only sum in Theorem <a href="#long243:res:weightedrecord" data-reference-type="ref" data-reference="long243:res:weightedrecord">26</a> weights the positive excess of each actual upward jump over $`B`$ by $`f(U_n)`$.

<div id="long243:rem:relative-error-boundary" class="remark">

*Remark 3*. One further question is not left open here, since it is answered in \[koizumi2025\]: whether vanishing relative error follows from $`a_{n+1}/a_n^{2}\to1`$ and rationality. It does. After deleting a finite prefix, Koizumi’s Corollary 3  \[koizumi2025, p. 9\] makes the sequence the pseudo-greedy expansion of its own reciprocal sum and gives $`\varepsilon_n\to0`$ under exactly the hypotheses of Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>; rationality is not needed for that step, only summability of $`\sum1/a_n`$. The matched-index dictionary in Section <a href="#long243:sec:priorwork" data-reference-type="ref" data-reference="long243:sec:priorwork">3</a> gives $`\varepsilon_n=E_n/C_n`$ on the restarted tail. For a rational sum, Lemma 4(2)  \[koizumi2025, pp. 11–12\] also gives $`-c_n/2\le e_n<c_n/2`$ at every index of that expansion. Thus $`|E_n|<C_n`$ holds beyond the restart, as required by Theorem <a href="#long243:res:bounded" data-reference-type="ref" data-reference="long243:res:bounded">53</a>; it need not hold at every original index. The eventual inequality $`|E_n|<C_n`$ also follows directly from vanishing relative error with $`K=1`$. What remains unsupplied is the eventual lower bound on $`E_n`$ in Theorem <a href="#long243:res:bounded" data-reference-type="ref" data-reference="long243:res:bounded">53</a>. That additional hypothesis is why the theorem is still conditional.

</div>

<a id="unbounded-upward-increments"></a>

## Unbounded upward increments

<div id="long243:res:variablerise" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/WindowAvoidance.lean#L862">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-variablerise-comparator">Comparator</a></p>

**Proposition 62** (small increases when the prime moduli are sparse). *There exist strictly increasing primes $`p_i`$ and a strictly increasing positive integer sequence $`u_n\to\infty`$ such that $`\gcd(u_n,p_i)=1`$ for all $`i,n`$ and
``` math
u_{n+1}-u_n=O\bigl(\sqrt{\log\log(u_n+e^e)}\bigr)
             =o\bigl(\log\log(u_n+3)\bigr).
```
Thus the bounded-increment hypothesis of Theorem <a href="#long243:res:barrier" data-reference-type="ref" data-reference="long243:res:barrier">48</a> cannot be replaced by an $`o(\log\log u_n)`$ bound without a quantitative restriction on the moduli.*

</div>

<div class="proof">

*Proof.* Choose increasing primes $`p_i>\max\{\exp(\exp((i+2)^2)),2^{i+3}\}`$, for $`i\ge0`$. Primes of arbitrarily large size suffice; no distribution theorem is used. Then $`\theta=\sum_i1/p_i<1/4`$ and $`k(z)=\#\{i:p_i\le z\}\le\sqrt{\log\log z}`$ whenever $`z`$ is large. For integer $`x`$ put $`L(x)=\lceil4\sqrt{\log\log(x+e^e)}+8\rceil`$. Since $`L(x)=o(x)`$, eventually $`L(x)>k(x+L(x))/(1-\theta)`$. The elementary window bound of Proposition <a href="#long243:res:coprimalitycap" data-reference-type="ref" data-reference="long243:res:coprimalitycap">41</a> leaves an integer in $`[x,x+L(x))`$ divisible by no $`p_i`$. The set of such integers is therefore unbounded. Enumerate it increasingly as $`(u_n)`$ and apply the same bound with $`x=u_n+1`$ to obtain $`u_{n+1}-u_n\le L(u_n+1)`$. For prime moduli nondivisibility is exactly coprimality, proving every claim. Sparse moduli defeat the abstract coprimality argument, not the exact tail recurrences. The next theorem instead fixes the moduli’s double-exponential scale. ◻

</div>

We now keep the full family of moduli, rather than discarding a prefix as in Proposition <a href="#long243:res:coprimalitycap" data-reference-type="ref" data-reference="long243:res:coprimalitycap">41</a>. The resulting coefficient depends on $`\sigma=\prod_j(1-1/m_j)`$. For a finite prefix, the corresponding product is exactly the proportion of admissible residue classes by the Chinese remainder theorem. This explains the constant in the statement before the limiting argument is made.

<div id="long243:res:gapconstant" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/MaximalGapConstant.lean#L1041">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-gapconstant-comparator">Comparator</a></p>

**Theorem 63** (largest gaps between integers avoiding given multiples). *Let $`m_0<m_1<\cdots`$ be pairwise coprime integers at least $`2`$ with $`\ell(m_j)=j+O(1)`$, where $`\ell(x)=\log_2\log_2\max(4,x)`$. Let $`\sigma=\prod_j(1-1/m_j)>0`$ and enumerate the positive integers divisible by no $`m_j`$ in increasing order as $`(u_n)`$. Then
``` math
\limsup_{n\to\infty}\frac{u_{n+1}-u_n}{\ell(u_n)}=\sigma^{-1}.
```
This is a statement about avoidance of multiples of whole moduli. It is not a statement about coprimality to composite $`m_j`$, or about integer tail orbits.*

</div>

<div class="proof">

*Proof.* Write $`k(z)=\#\{j:m_j\le z\}=\ell(z)+O(1)`$. For a fixed prefix length $`T`$, set
``` math
M_T=\prod_{j<T}m_j,\qquad
 \sigma_T=\prod_{j<T}(1-1/m_j),\qquad
 \theta_T=\sum_{j\ge T}1/m_j.
```
Here $`\theta_T\to0`$. By the Chinese remainder theorem, avoiding the first $`T`$ whole moduli selects precisely the fraction $`\sigma_T`$ of the residues modulo $`M_T`$.

For the upper bound, fix $`T`$ before sending the interval to infinity, so the prefix error $`M_T`$ stays constant. An integer interval $`[x,x+L)`$ contains at least $`\sigma_TL-M_T`$ integers avoiding that prefix. The remaining moduli cover at most $`L\theta_T+k(x+L)`$ integers. Choose $`T`$ large enough that $`\sigma_T>\theta_T`$, and then any $`c>(\sigma_T-\theta_T)^{-1}`$. For $`L=\lceil c\ell(x)\rceil`$, the number left is positive for all sufficiently large $`x`$, since $`k(x+L)=\ell(x)+O(1)`$. Thus the set being enumerated is unbounded, and every sufficiently late such interval meets it. Applying this at $`x=u_n+1`$ gives
``` math
\limsup_n\frac{u_{n+1}-u_n}{\ell(u_n)}
 \le(\sigma_T-\theta_T)^{-1}.
```
Letting $`T\to\infty`$ gives the upper bound $`\sigma^{-1}`$.

For the lower bound, fix $`T`$ and let the integer length $`L`$ tend to infinity. Among the offsets $`0\le j<L`$, precisely $`K_L=\sigma_TL+O(M_T)`$ avoid the first $`T`$ moduli. Assign to these offsets distinct moduli $`m_T,\ldots,m_{T+K_L-1}`$. Solve simultaneously $`x\equiv0\pmod{M_T}`$ and $`x\equiv-j`$ modulo the modulus assigned to $`j`$. Put $`Q_L=\prod_{i<T+K_L}m_i`$ and choose this solution in $`[Q_L,2Q_L)`$. Every integer of $`[x,x+L)`$ is then divisible by a modulus: either an old one or its assigned new one. Let $`u`$ be the greatest admissible integer below $`x`$; its successor is at least $`x+L`$, so the gap is at least $`L`$. The scale assumption gives
``` math
\ell(2Q_L)\le T+K_L+O(1),
```
because $`\log_2m_i=2^{i+O(1)}`$ and these upper bounds sum geometrically. Since $`u<2Q_L`$, the ratio for this gap is at least $`L/(T+K_L+O(1))`$, tending to $`\sigma_T^{-1}`$. These $`u`$ tend to infinity: $`x\ge Q_L\to\infty`$ and admissible integers are unbounded. Hence the limsup is at least $`\sigma_T^{-1}`$ for every $`T`$. Let $`T\to\infty`$ to finish. ◻

</div>

For the Fermat moduli $`m_j=2^{2^j}+1`$, pairwise coprimality and the finite-product identity
``` math
\prod_{j=0}^{N}\left(1-\frac1{2^{2^j}+1}\right)
 =\frac{2^{2^{N+1}-1}}{2^{2^{N+1}}-1}
```
give $`\sigma=1/2`$, so the coefficient is exactly $`2`$. These results describe gaps between integers avoiding fixed moduli. They do not construct multipliers or numerator and denominator sequences satisfying the exact recurrences. In particular, the static proportion $`\sigma`$ must not be substituted for $`\varphi(v_T)/v_T`$: the first excludes multiples of the whole moduli, while the second excludes every prime factor of the reduced denominator.

<a id="formalisation-targets"></a>

## Formalisation targets

<a id="erdősstraus."></a>

#### Erdős–Straus.

Formalise Theorem 3 of \[erdosstraus1964\], with its prefix-LCM quotient and correctly indexed growth factor, under the published analytic hypotheses.

<a id="duverney."></a>

#### Duverney.

Formalise the absolute-convergence form of Corollary 3.2 of \[duverney2001\], including its signed numerators, and recover the all-positive specialisation used for comparison here. For the printed condition interpreted as mere signed convergence, first justify the nonvanishing-product step discussed in Section <a href="#long243:sec:priorwork" data-reference-type="ref" data-reference="long243:sec:priorwork">3</a>. That interpretation is not treated as an already verified formalisation target.

<a id="statements-and-declarations"></a>

## Statements and declarations

<a id="artefact-and-data-availability."></a>

#### Artefact and data availability.

The fixed toolchain, Lean sources and evidence record are described in Appendix <a href="#long243:app:index" data-reference-type="ref" data-reference="long243:app:index">15</a>.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

I thank Wouter van Doorn for advice on exposition, including the explanation of restrictive hypotheses and the removal of unnecessary terminology. The problem numbering follows Bloom’s Erdős Problems catalogue \[erdosproblems\].

<a id="long243:app:index"></a>

# Verification and reproducibility

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

The fixed toolchain, library manifest and Lean sources are in the [public repository](https://github.com/wcook04/plectis-erdos/tree/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd). The evidence record identifies the exact declarations, source versions and Comparator status, including source-pin and index gaps. The external formal-conjecture entry states the problem without proving it. The printed square-specialisation proof uses Chebotarev, while the formal proof uses a Dedekind-zeta pole comparison; the shared conclusion does not check every step of the printed argument. No new Lean build, Comparator replay or independent review was performed for this revision.

The recurrence identities and arithmetic exclusions are in `ReciprocalTailRigidity.lean`, the scalar convergence theorem is in `SparseResetRecovery.lean`, and the bounds on cancelled factors are in `RepairEntropy.lean`. The Lean statement excluding a periodic error assumes $`e_n<a_n`$; Section <a href="#long243:sec:periodic" data-reference-type="ref" data-reference="long243:sec:periodic">10</a> derives this bound eventually for a periodic positive error magnitude. The printed bounded-negative theorem uses $`E_n/C_n\to0`$. The formal statement uses its division-free form, $`K|E_n|<C_n`$ eventually for each natural $`K`$; the bound $`|E_n|<C_n`$ is its $`K=1`$ case. Sections <a href="#long243:sec:priorwork" data-reference-type="ref" data-reference="long243:sec:priorwork">3</a> and <a href="#long243:sec:bounded" data-reference-type="ref" data-reference="long243:sec:bounded">12</a> give the construction from a rational reciprocal sum.

<div id="243-long-indexing">

</div>

<a id="indexing-of-the-regular-rate-theorems"></a>

## Indexing of the regular-rate theorems

*Index translation for the Lean statements.* Both Lean declarations use $`b:\mathbb{N}\to\mathbb{N}`$, including a positive $`b_0`$, whereas the theorems above start at $`a_1`$. A simple shift changes $`\lambda/n`$ by order $`n^{-2}`$ and may lose the stated $`o(n^{-\lambda})`$ precision. Instead choose a large $`N`$ with $`a_N>N`$. Such an $`N`$ exists: strict increase gives $`a_n\ge n`$ and the rate gives $`a_n^2/a_{n+1}<2`$ eventually, hence $`a_{n+1}>a_n^2/2\ge n^2/2>n+1`$ for large $`n`$. Define
``` math
b_n=\begin{cases}n+1,&0\le n<N,\\a_n,&n\ge N.\end{cases}
```
Then $`b`$ is positive and strictly increasing, with the same indexed rate for every $`n\ge N`$. Moreover
``` math
\sum_{n\ge0}\frac1{b_n}-\sum_{n\ge1}\frac1{a_n}
 =\sum_{n=0}^{N-1}\frac1{n+1}-\sum_{n=1}^{N-1}\frac1{a_n}\in\mathbb{Q}.
```
The series converge by the stated rapid-growth rate. If the original sum were rational, so would be the sum for $`b`$, contradicting the corresponding zero-indexed Lean theorem. This finite-prefix implication is proved here in ordinary mathematics; the Lean declarations check the zero-indexed theorems themselves.

<a id="the-square-specialisation-proofs"></a>

## The square-specialisation proofs

Lemma <a href="#long243:res:squarespec" data-reference-type="ref" data-reference="long243:res:squarespec">8</a> and its consequences, Proposition <a href="#long243:res:transportsquare" data-reference-type="ref" data-reference="long243:res:transportsquare">9</a>, Theorem <a href="#long243:res:cubicexclusion" data-reference-type="ref" data-reference="long243:res:cubicexclusion">4</a> and Theorem <a href="#long243:res:cubicrate" data-reference-type="ref" data-reference="long243:res:cubicrate">2</a>, are formalised without Chebotarev. The printed proof of Lemma <a href="#long243:res:squarespec" data-reference-type="ref" data-reference="long243:res:squarespec">8</a> uses that theorem; its Lean proof instead uses the simple pole of the Dedekind zeta function. The zero-indexed Lean statement of Theorem <a href="#long243:res:cubicrate" data-reference-type="ref" data-reference="long243:res:cubicrate">2</a> requires the finite-prefix bridge above.

The nonintegral-rate formal proof uses the real-parameter extraction theorem and a quantitative canonical-tail estimate. Convergence of the reciprocal series is derived from the rate.

<a id="recurrence-declarations"></a>

## Recurrence declarations

*Proposition <a href="#long243:res:update" data-reference-type="ref" data-reference="long243:res:update">14</a>.* [update law](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L57).

*Proposition <a href="#long243:res:scale" data-reference-type="ref" data-reference="long243:res:scale">16</a>.* [denominator](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L65), [numerator](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L70) and [error](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L75).

*Theorem <a href="#long243:res:defect" data-reference-type="ref" data-reference="long243:res:defect">17</a>.* [defect identity](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1775).

*Theorem <a href="#long243:res:step" data-reference-type="ref" data-reference="long243:res:step">19</a>.* [local rigidity step](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1787).

*Theorem <a href="#long243:res:eventual" data-reference-type="ref" data-reference="long243:res:eventual">23</a>.* [eventual Sylvester recurrence](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1805).

*Theorem <a href="#long243:res:absorb" data-reference-type="ref" data-reference="long243:res:absorb">24</a>.* [absorption of a vanishing error](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2227), with the companion [contrapositive along a tail](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2254).

*Theorem <a href="#long243:res:descent" data-reference-type="ref" data-reference="long243:res:descent">42</a>.* [stabilisation of the nonnegative error](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1843), using the [eventual constancy of a nonincreasing sequence](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1825).

*Lemma <a href="#long243:res:crt" data-reference-type="ref" data-reference="long243:res:crt">46</a>.* [shifted consecutive multiples](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L839).

*Theorem <a href="#long243:res:barrier" data-reference-type="ref" data-reference="long243:res:barrier">48</a>.* [the Chinese-remainder first-crossing consequence](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L903).

*Theorem <a href="#long243:res:bounded" data-reference-type="ref" data-reference="long243:res:bounded">53</a>.* The theorem is [stated with an eventual lower bound and division-free vanishing relative error](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2360). The Lean proof shifts past both thresholds and applies the [version with $`|E_n|<C_n`$ and the lower bound at every index](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2271). It uses [divergence from vanishing relative error](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1739) and the [exclusion for bounded upward increments and arbitrarily late bounded negative magnitudes](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1754), via [its formulation with divergence as a hypothesis](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1661). Both exclusion statements require a uniform bound on all upward increments. Bounded negative magnitudes at arbitrarily late indices suffice for gcd stabilisation, but not for the jump bound in the CRT argument.

*Theorem <a href="#long243:res:mass" data-reference-type="ref" data-reference="long243:res:mass">55</a>.* The scalar conclusion is [the eventual vanishing for a positive integer sequence](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SparseResetRecovery.lean#L612); its exact-orbit consequence is [the scalar recurrence from a convergent sum](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SparseResetRecovery.lean#L690). A separate exact-orbit formulation retains the denominator and tail update equations, positivity, the centered-step identity and division-free normalized vanishing. Under $`\sum_n(-E_n)_+/C_n<\infty`$, the checked results give [a bound on numerator growth](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SparseResetRecovery.lean#L378), [eventual zero error](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SparseResetRecovery.lean#L488), and [the Sylvester recurrence](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/SparseResetRecovery.lean#L510). These are conditional hypotheses, not properties proved here for the original orbit. The `plectis-erdos-lean` repository contains a [formulation for the rational-tail numerators using a convergent sum](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/ErdosProblems/Erdos243/PaperCompleteR8/CanonicalNegativeMass.lean#L19), not covered by the evidence record. Summability remains an assumption; the elementary scalar implication needs neither growth nor vanishing relative error.

*Proposition <a href="#long243:res:frontier" data-reference-type="ref" data-reference="long243:res:frontier">57</a>.* In the Lean statement of Proposition <a href="#long243:res:frontier" data-reference-type="ref" data-reference="long243:res:frontier">57</a>, the divergent sum of relative increases is recorded as divergence of the partial sums.

<a id="long243:app:residue"></a>

# A factorial modulus for integral recursion

In the case $`m=c=1`$ of Section <a href="#long243:sec:constant" data-reference-type="ref" data-reference="long243:sec:constant">9</a>, the identity <a href="#long243:eq:shape" data-reference-type="eqref" data-reference="long243:eq:shape">[long243:eq:shape]</a> becomes $`D_n+1=(a_n-1)(n+1)`$. It determines the recursion $`a_{n+1}=\operatorname{num}(n,a_n)/(n+2)`$, where
``` math
\operatorname{num}(n,a)=(n+1)a^{2}-(n+2)a+(n+3),
```
the [forced numerator](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L22). We stop at the first nonintegral quotient. The [formal survival predicate](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L75) requires exact division at each step. For $`a_0=3`$, as in Example <a href="#long243:ex:shape" data-reference-type="ref" data-reference="long243:ex:shape">43</a>, the first quotient is $`\operatorname{num}(0,3)/2=3`$, but the next quotient is $`\operatorname{num}(1,3)/3=13/3`$, so the recursion stops. Direct iteration can produce very large intermediate integers. To decide whether the first $`h`$ divisions are exact, however, it suffices to know the initial value modulo $`(h+1)!`$. Computing a pseudo-greedy orbit through residues modulo a shrinking product modulus is Koizumi’s method \[koizumi2025, Remark 2 and Algorithm 1, pp. 13–14\]; for the forced numerator that product is a factorial.

<div id="long243:res:residue" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-residue">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/b4d9b60327e3c4d4cc50acb37e62268788cd77e0/evidence/erdos243-reciprocal-tail-reasoning-surface.md#long243-res-residue-comparator">Comparator</a></p>

**Theorem 64** (factorial residue reduction). *Let $`h`$ be a nonnegative integer and let $`a,b`$ be integers with $`a\equiv b\pmod{(h+1)!}`$. The first $`h`$ steps of the recursion $`a_{n+1}=\operatorname{num}(n,a_n)/(n+2)`$, starting at index zero, are integral for $`a_0=a`$ if and only if they are integral for $`a_0=b`$.*

</div>

<div class="proof">

*Proof.* Each exact division consumes a congruence factor. Retain the remaining factors by setting $`M(0,i)=1`$ and $`M(h+1,i)=(i+2)M(h,i+1)`$. Thus $`M(h,0)=(h+1)!`$. We prove the stronger statement that, at index $`i`$, congruent inputs modulo $`M(h,i)`$ give the same answer to whether the next $`h`$ quotients are all integral. There is nothing to prove for $`h=0`$.

For the inductive step, suppose $`a\equiv b\pmod{(i+2)M(h,i+1)}`$. Since $`\operatorname{num}(i,\cdot)`$ is an integer polynomial, its values at $`a`$ and $`b`$ are congruent modulo that product. In particular, one is divisible by $`i+2`$ if and only if the other is. If neither is divisible, both recursions stop. Otherwise their quotients are congruent modulo $`M(h,i+1)`$, so the induction hypothesis applies to the remaining $`h`$ updates at index $`i+1`$. Taking $`i=0`$ proves the claim. ◻

</div>

The formal [factorial residue reduction](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L134) uses the [shrinking-modulus induction](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L97), [polynomial congruence](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L26), and [cancellation after exact division](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L41). Its modulus is identified by the [ascending-factorial formula](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L59) and its [factorial value at the initial index](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L69).

For $`h=1`$, the modulus is $`2!=2`$. The first quotient is integral if and only if $`2\mid a^2-2a+3`$, or equivalently if $`a`$ is odd. For instance, $`\operatorname{num}(0,3)=6`$ and $`\operatorname{num}(0,4)=11`$. Thus the parity of $`a`$ decides the first step, as Theorem <a href="#long243:res:residue" data-reference-type="ref" data-reference="long243:res:residue">64</a> asserts in this case.

Exact enumeration for $`2\le a_0<5000`$ gives a maximum of $`17`$ successful updates, or $`18`$ multiplier values including $`a_0`$. Nine seeds attain it, the least being $`1501`$. The seed $`a_0=1`$ is excluded: it gives $`a_n=1`$ at every step and violates the hypothesis $`a_n\ge2`$. The test certifies exact division, not a positive orbit. Even a surviving seed for every finite horizon would not supply one integer seed surviving forever. Theorem <a href="#long243:res:constant" data-reference-type="ref" data-reference="long243:res:constant">44</a> proves the infinite exclusion; the residue reduction also applies to other polynomial-division recurrences.

<a id="sec:erdos-243-complete-family-map"></a>

# Result map and proof dependencies

Beyond the short paper, this companion supplies signed-series comparisons (Section <a href="#long243:sec:priorwork" data-reference-type="ref" data-reference="long243:sec:priorwork">3</a>), integer coefficients (Section <a href="#long243:sec:lcmrecords" data-reference-type="ref" data-reference="long243:sec:lcmrecords">6</a>), general $`1+c/n`$ rates (Section <a href="#long243:sec:records" data-reference-type="ref" data-reference="long243:sec:records">7</a>), and regular-rate extraction with positive-density cubic exclusion (Section <a href="#long243:sec:cubicrate" data-reference-type="ref" data-reference="long243:sec:cubicrate">2</a>). Theorem <a href="#long243:res:recorddichotomy" data-reference-type="ref" data-reference="long243:res:recorddichotomy">29</a> gives the double-logarithmic bound; Section <a href="#long243:sec:open" data-reference-type="ref" data-reference="long243:sec:open">14</a> includes the scalar failed-divisibility example. The principal dependencies are:

<a id="bounded-upward-increments."></a>

#### Bounded upward increments.

Vanishing relative error gives eventual absorption. Bounded negative values at arbitrarily late indices give a stable gcd; CRT then excludes the unbounded reduced tail with bounded upward increments. The increment bound is an extra hypothesis.

<a id="a-convergent-sum-of-relative-increases."></a>

#### A convergent sum of relative increases.

The inequality $`C_{n+1}\le C_n(1+(-E_n)_+/C_n)`$ turns summability into a uniform bound on $`C_n`$. Integrality then permits only finitely many rises, after which the numerator stabilises. No vanishing relative error is needed.

<a id="new-maxima-and-prime-power-persistence."></a>

#### New maxima and prime-power persistence.

The amplified error bounds cancellation, protecting large primes for Theorem <a href="#long243:res:recordamplified" data-reference-type="ref" data-reference="long243:res:recordamplified">31</a>. Density-one coprimality and CRT height control give the double-logarithmic bound. LCM tails give weighted crossings without primitive numerators. For reduced tails, Corollary <a href="#long243:res:powerpersistence" data-reference-type="ref" data-reference="long243:res:powerpersistence">28</a> protects a prime power below its numerator threshold, allowing crossings to be counted before that protection fails.

<a id="cubic-rate."></a>

#### Cubic rate.

The tail estimate and finite differences of the Gamma ratio force an eventual cubic polynomial for the integer numerator. The recurrence forces a modular square condition, which the square-specialisation lemma lifts to the cubic field. The ordinary proof uses Chebotarev; the Lean proof obtains the same implication from a Dedekind-zeta pole comparison. The trace calculation leaves $`m=12`$, and both possible signs are excluded modulo seven.

<a id="avoidance-of-fixed-moduli."></a>

#### Avoidance of fixed moduli.

For sufficiently sparse prime moduli, a coprime integer sequence can have unbounded but very small increments. At the specified double-exponential scale, counting residue classes and applying CRT give the largest gaps between integers divisible by none of the whole moduli. These auxiliary results do not construct reciprocal-tail examples.

<a id="what-remains."></a>

#### What remains.

For the unrestricted problem, one still needs the stated summability or record bound, or a contradiction to the necessary conditions on a counterexample. The static examples and local identities supply neither.

<div class="thebibliography">

99

P. Erdős and E. G. Straus, [*On the irrationality of certain Ahmes series*](https://users.renyi.hu/~p_erdos/1964-19.pdf), J. Indian Math. Soc. (N.S.) **27** (1964), 129–133. MR 175848. D. Duverney, [*Irrationality of fast converging series of rational numbers*](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf), J. Math. Sci. Univ. Tokyo **8** (2001), 275–316. MR 1837165. C. Badea, [*A theorem on irrationality of infinite series and applications*](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf), Acta Arith. **63** (1993), no. 4, 313–323, doi:[10.4064/aa-63-4-313-323](https://doi.org/10.4064/aa-63-4-313-323). R. Tijdeman and P. Yuan, *On the rationality of Cantor and Ahmes series*, Indag. Math. (N.S.) **13** (2002), no. 3, 407–418, doi:[10.1016/S0019-3577(02)80018-0](https://doi.org/10.1016/S0019-3577(02)80018-0). P. Erdős and R. L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf), Monogr. Enseign. Math. 28, Geneva, 1980, p. 64. P. Erdős, [*On the irrationality of certain series: problems and results*](https://users.renyi.hu/~p_erdos/1988-22.pdf), in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). V. Kovač and T. Tao, [*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593v4), Acta Math. Hungar. **175** (2025), no. 2, 572–608, doi:[10.1007/s10474-025-01528-0](https://doi.org/10.1007/s10474-025-01528-0); arXiv:[2406.17593v4](https://arxiv.org/abs/2406.17593v4). Page references are to arXiv:2406.17593v4. I. O. Bado, *Prime-Support Rigidity and Primitive Pseudo-Greedy Dynamics: Partial Progress on Erdős Problem #243*, preprint posted September 2026, doi:[10.13140/RG.2.2.36612.08325](https://doi.org/10.13140/RG.2.2.36612.08325). P. White with Claude (Anthropic), [*Erdős \#243: working report*](https://erdosproblemaday.com/report/243), Erdős Problem a Day, page dated 12 August 2026. AI-assisted, unrefereed working report. P. Stevenhagen and H. W. Lenstra, Jr., [*Chebotarëv and his density theorem*](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1994c/art.pdf), Math. Intelligencer **18** (1996), no. 2, 26–37, doi:[10.1007/BF03027290](https://doi.org/10.1007/BF03027290). Page references are to the linked author version dated 23 March 1995. W. van Doorn, Y. Li and Q. Tang, [*Optimal bounds for an Erdős problem on matching integers to distinct multiples*](https://arxiv.org/abs/2603.28636), preprint arXiv:2603.28636v1, 2026. J. Koizumi, [*Irrationality of the reciprocal sum of doubly exponential sequences*](https://math.colgate.edu/~integers/aa28/aa28.pdf), Integers **26** (2026), Paper No. A28, 17 pp., doi:[10.5281/zenodo.18714404](https://doi.org/10.5281/zenodo.18714404). Locators refer to this published version. T. F. Bloom, [*Erdős Problem \#243*](https://www.erdosproblems.com/243), accessed 28 July 2026. The Formal Conjectures Authors, [*FormalConjectures.ErdosProblems.`243`*](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/243.lean), Lean source at commit `f776d2f`, 2025. Formal problem statement, not a proof. P. Erdős and E. G. Straus, [*On the irrationality of certain series*](https://msp.org/pjm/1974/55-1/pjm-v55-n1-p08-s.pdf), Pacific J. Math. **55** (1974), no. 1, 85–92. J. Hančl and R. Tijdeman, [*On the irrationality of polynomial Cantor series*](https://www.impan.pl/shop/en/publication/transaction/download/product/82186), Acta Arith. **133** (2008), no. 1, 37–52, doi:[10.4064/aa133-1-3](https://doi.org/10.4064/aa133-1-3). Locators refer to the published version. D. Duverney, T. Kurosawa and I. Shiokawa, [*Irrationality exponents of certain fast converging series of rational numbers*](https://danielduverney.fr/documents/theorie-des-nombres/Tsukuba.pdf), Tsukuba J. Math. **44** (2020), no. 2, 235–250, doi:[10.21099/tkbjm/20204402235](https://doi.org/10.21099/tkbjm/20204402235). Theorem locators follow the linked 14-page author version. T. Crmarić and V. Kovač, [*On the irrationality of certain super-polynomially decaying series*](https://arxiv.org/abs/2504.18712v1), Colloq. Math. **179** (2025), 55–68, doi:[10.4064/cm9628-5-2025](https://doi.org/10.4064/cm9628-5-2025). Theorem locators follow arXiv:2504.18712v1. A. Koutsoukou-Argyraki and W. Li, [*Irrationality Criteria for Series by Erdős and Straus*](https://isa-afp.org/entries/Irrational_Series_Erdos_Straus.html), Archive of Formal Proofs, 12 May 2020. An Isabelle/HOL formalisation; the archive entry identifies the results formalised. National Institute of Standards and Technology, [*Digital Library of Mathematical Functions*, §5.11(iii), formula 5.11.12](https://dlmf.nist.gov/5.11.E12), accessed 16 September 2026. E. H. el Abdalaoui, M. Lemańczyk and T. de la Rue, *A dynamical point of view on the set of $`\mathcal B`$-free integers*, Int. Math. Res. Not. IMRN (2015), no. 16, 7258–7286, doi:[10.1093/imrn/rnu164](https://doi.org/10.1093/imrn/rnu164). The cited definition is also in §1.2 of arXiv:[1311.3752v3](https://arxiv.org/abs/1311.3752v3).

</div>
