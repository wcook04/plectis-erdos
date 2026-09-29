<a id="erdos-243-reciprocal-tail-rigidity"></a>

# Cubic-Rate Irrationality and Reciprocal-Tail Rigidity

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We prove that a strictly increasing sequence of positive integers with $`a_n^2/a_{n+1}=1+3/n+o(n^{-3})`$ has irrational reciprocal sum. Rationality would make an integer tail numerator an eventual cubic polynomial, which we exclude by a square condition in a cubic field and congruences modulo seven. We also give criteria for an eventual Sylvester recurrence using bounded increases and weighted sums over new maxima. The unrestricted question of Erdős and Graham remains unresolved here.

<a id="sec:problem"></a>

# Introduction

The identity
``` math
\frac1{a-1}=\frac1a+\frac1{a^2-a}
```
explains why the Sylvester recurrence $`a_{n+1}=a_n^2-a_n+1`$ produces a rational reciprocal tail. We call a sequence satisfying this recurrence eventually a *Sylvester tail*; at every sufficiently late index its tail sum is $`1/(a_n-1)`$. The question is whether quadratic growth allows any other rational reciprocal sum.

<div id="res:problem" class="problem">

**Problem 1** (Erdős Problem 243). Let $`1\le a_1<a_2<\cdots`$ be a sequence of integers with
``` math
\lim_{n\to\infty}\frac{a_n}{a_{n-1}^{2}}=1
 \qquad\text{and}\qquad
 \sum\frac{1}{a_n}\in\mathbb{Q}.
```
Then $`a_n=a_{n-1}^{2}-a_{n-1}+1`$ for all sufficiently large $`n`$.

</div>

Erdős and Graham \[erdosgraham1980, p. 64\] asked this question; see also Erdős \[erdos1988, p. 105\] and Bloom’s catalogue \[erdosproblems\]. We prove the following irrationality result for a restricted class of quadratically growing sequences.

<div id="res:cubicrate" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L70">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-cubicrate-comparator">Comparator</a></p>

**Theorem 2** (cubic-rate irrationality). *A strictly increasing sequence of positive integers with
``` math
a_n^2/a_{n+1}=1+\frac3n+o(n^{-3})
```
has irrational reciprocal sum.*

</div>

A Sylvester tail has $`a_n^2/a_{n+1}-1=O(1/a_n)`$, so it cannot satisfy the rate in Theorem <a href="#res:cubicrate" data-reference-type="ref" data-reference="res:cubicrate">2</a>. Thus the theorem excludes rational sums in this class. The recurrence question for all sequences with $`a_{n+1}\sim a_n^2`$ remains open here.

For example, set $`a_1=8`$ and
``` math
a_{n+1}=\left\lceil\frac{n a_n^2}{n+3}\right\rceil.
```
The first terms are $`8,16,103,5305`$. Induction gives $`a_n\ge4\cdot2^{2^{n-1}}`$, since $`a_{n+1}\ge a_n^2/4`$. The rounding error is less than one, so
``` math
0\le 1+\frac3n-\frac{a_n^2}{a_{n+1}}<\frac{16}{a_n^2}=o(n^{-3}).
```
Thus its reciprocal sum is irrational by Theorem <a href="#res:cubicrate" data-reference-type="ref" data-reference="res:cubicrate">2</a>. If $`P_n=\prod_{j<n}a_j`$ and $`t_n=P_n/a_n`$, then $`t_{n+1}/t_n=a_n^2/a_{n+1}`$. Comparison with $`n(n+1)(n+2)`$, using the summable rounding errors, gives $`t_n\sim K n^3`$ for some $`K>0`$ and $`t_{n+1}-t_n\sim3K n^2`$. This example lies outside the bounded-increment criterion proved in Section <a href="#sec:bounded" data-reference-type="ref" data-reference="sec:bounded">4</a>.

To prove the theorem, we clear the rational tails to obtain positive integers $`C_n`$ with $`C_{n+1}/C_n=1+3/n+o(n^{-3})`$. After division by $`n(n+1)(n+2)`$, the recurrence gives $`\Delta^4C_n\to0`$. These integer differences eventually vanish, leaving $`C_n=A n(n+1)(n+2)+B`$. We then divide out a stable gcd. The resulting coprime recurrence forces a square at every root of this cubic modulo almost every prime. Chebotarev gives the corresponding square in its cubic field, and a trace calculation leaves two polynomials, both excluded modulo seven. Section <a href="#sec:secondaryrate" data-reference-type="ref" data-reference="sec:secondaryrate">3</a> gives the proof.

The remaining sections concern sufficient conditions for a rational reciprocal sum to have a Sylvester tail. Clearing denominators gives the integer remainders used by Koizumi \[koizumi2025, Lemma 4\]. Section <a href="#sec:bounded" data-reference-type="ref" data-reference="sec:bounded">4</a> combines their gcd stabilisation with a Chinese-remainder argument to allow any finite upper bound on the increments of $`P_n/a_n`$. Section <a href="#sec:mass" data-reference-type="ref" data-reference="sec:mass">5</a> records an elementary summability criterion, and Section <a href="#sec:lcmrecords" data-reference-type="ref" data-reference="sec:lcmrecords">6</a> treats an LCM numerator at steps reaching new maxima. Its weighted criterion leads to the unresolved estimate in Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">7</a>. The [companion paper](../../../paper/243/erdos243-reciprocal-tail-reasoning-surface.pdf) contains the nonintegral-rate theorem, the stronger cubic disagreement result and further recurrence criteria. Appendix <a href="#app:index" data-reference-type="ref" data-reference="app:index">9</a> describes the formal sources and their relation to these proofs.

<a id="sec:transfer"></a>

# Integer tails

<span id="sec:state" label="sec:state"></span> Assume for this section that $`a_n`$ are strictly increasing positive integers, $`a_{n+1}/a_n^2\to1`$, and $`\sum_{n\ge1}1/a_n=p/q`$ with positive integers $`p,q`$. Write
``` math
x_n=\sum_{k\ge n}\frac1{a_k},\qquad P_n=\prod_{j<n}a_j,
 \qquad D_n=qP_n,\qquad C_n=D_nx_n.
```
Then
``` math
C_n=pP_n-q\sum_{k<n}\frac{P_n}{a_k}\in\mathbb{N}_{>0},
 \qquad C_{n+1}=a_nC_n-D_n,\qquad D_{n+1}=a_nD_n.
```
We keep this fraction unreduced. Up to a common rescaling and the indexing above, these are Koizumi’s integer-tail coordinates \[koizumi2025, Lemma 4, pp. 11–12\].

For large $`n`$, $`a_{n+1}\ge a_n^2/2\ge2a_n`$. The terms after $`1/a_{n+1}`$ sum to at most $`2/a_{n+2}\le4/a_{n+1}^2`$, so
``` math
\begin{equation}
\label{eq:tail-estimate}
 x_n=\frac1{a_n}+\frac1{a_{n+1}}+O(a_{n+1}^{-2}),
 \qquad
 \frac{C_{n+1}}{C_n}=\frac{a_n^2}{a_{n+1}}+O(1/a_n).
\end{equation}
```
The growth is at least double exponential after a fixed initial index. In particular, $`1/a_n=o(n^{-k})`$ for every fixed $`k`$. We retain the original index in the cubic rate throughout: shifting $`n`$ changes its lower-order terms. An eventual recurrence is unaffected by removing a finite prefix.

<a id="sec:reduction"></a>

## Coprimality after reduction

The gcds $`G_n=\gcd(C_n,D_n)`$ form a divisibility chain, since both updates preserve common divisors. If $`G_n`$ is constant, say $`g`$, on a tail, division by $`g`$ gives
``` math
u_{n+1}=a_nu_n-v_n,\qquad v_{n+1}=a_nv_n,
 \qquad \gcd(u_n,v_n)=1.
```
Here $`u_n>0`$ and $`v_n\ge0`$; we call this a *reduced exact tail*.

<div id="res:reduced" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Reduction.lean#L16">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-reduced-comparator">Comparator</a></p>

**Proposition 3** (persistent coprimality). *In a reduced exact tail, $`\gcd(a_n,v_n)=1`$. Distinct multipliers are pairwise coprime, and every earlier multiplier is coprime to every later numerator.*

</div>

<div class="proof">

*Proof.* A prime dividing both $`a_n`$ and $`v_n`$ would divide $`u_{n+1}`$ and $`v_{n+1}`$, contrary to reducedness. For $`i<t`$, the factor $`a_i`$ divides $`v_t`$. Reducedness gives $`\gcd(a_i,u_t)=1`$, and $`\gcd(a_t,v_t)=1`$ gives $`\gcd(a_i,a_t)=1`$. ◻

</div>

In the cubic proof, a finite difference bounds $`G_n`$. For bounded increases we will instead bound it by the error at negative indices.

<a id="sec:secondaryrate"></a>

# Proof of cubic-rate irrationality

Suppose, towards a contradiction, that the reciprocal sum in Theorem <a href="#res:cubicrate" data-reference-type="ref" data-reference="res:cubicrate">2</a> is rational. Construct $`C_n,D_n`$ as in Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">2</a>. Equation <a href="#eq:tail-estimate" data-reference-type="eqref" data-reference="eq:tail-estimate">[eq:tail-estimate]</a> transfers the rate without changing its precision:
``` math
\begin{equation}
\label{eq:cubic-ratio}
 \frac{C_{n+1}}{C_n}=1+\frac3n+o(n^{-3}).
\end{equation}
```
We show first that $`C_n`$ is eventually a polynomial. The denominator recurrence will then restrict its coefficients and exclude the two remaining possibilities.

<a id="sec:cubic-extraction"></a>

## Polynomial extraction

Put $`F_n=n(n+1)(n+2)`$, so $`F_{n+1}/F_n=1+3/n`$, and write the error in <a href="#eq:cubic-ratio" data-reference-type="eqref" data-reference="eq:cubic-ratio">[eq:cubic-ratio]</a> as $`\varepsilon_n=o(n^{-3})`$. For $`z_n=C_n/F_n`$,
``` math
\frac{z_{n+1}}{z_n}=1+\frac{\varepsilon_n}{1+3/n}.
```
The logarithms of these positive ratios are absolutely summable. Their product therefore converges to a positive limit $`A`$. Since the tails of the logarithmic series are $`o(n^{-2})`$, we have $`z_n-A=o(n^{-2})`$. Hence $`\delta_n=C_n-AF_n=o(n)`$. To control differences of this error, we use the recurrence itself:
``` math
\Delta\delta_n=\frac3n\delta_n+\varepsilon_n C_n=o(1),
 \qquad \Delta h_n=h_{n+1}-h_n.
```
It follows that $`\Delta^4C_n=\Delta^3(\Delta\delta_n)\to0`$. These fourth differences are integers and therefore vanish eventually. The sequence $`C_n`$ agrees on a tail with a polynomial in $`\mathbb{Q}[n]`$ of degree at most three. Since $`C_n-AF_n=o(n)`$, comparison of polynomial coefficients gives
``` math
\begin{equation}
\label{eq:cubic-shape}
 C_n=A n(n+1)(n+2)+B,\qquad A\in\mathbb{Q}_{>0},\quad B\in\mathbb{Q}.
\end{equation}
```
The extraction requires the little-oh error. Indeed, $`F_n+(-1)^n`$ is a positive integer sequence with ratio $`1+3/n+O(n^{-3})`$ and no eventual polynomial form. This example concerns the extraction step alone and is not asserted to satisfy the reciprocal-tail recurrences.

<a id="sec:cubic-normalisation"></a>

## Normalisation and irreducibility

For a sufficiently late $`n`$, the integer $`G_n=\gcd(C_n,D_n)`$ divides $`C_n,C_{n+1},C_{n+2},C_{n+3}`$ and therefore divides $`\Delta^3C_n=6A`$. The positive divisibility chain $`G_n`$ is bounded and stabilises at $`g`$. Proposition <a href="#res:reduced" data-reference-type="ref" data-reference="res:reduced">3</a> applies to $`u_n=C_n/g`$, $`v_n=D_n/g`$. In addition, adjacent numerators are coprime: $`\gcd(u_n,u_{n+1})=\gcd(u_n,v_n)=1`$.

Write the polynomial for $`u_n`$ as
``` math
\begin{equation}
\label{eq:normal-cubic}
 Q(n)=\frac m6 n(n+1)(n+2)+c.
\end{equation}
```
Since $`m=6A/g`$ is the third difference of the integer sequence $`u_n`$, it is a positive integer. To see that $`Q`$ is integer-valued at every integer, choose a common denominator of its coefficients and translate any integer by a sufficiently large multiple of that denominator. The eventual integer values of $`Q`$ then give $`c=Q(0)\in\mathbb{Z}`$. If a prime $`\ell`$ divides $`c`$, choose an arbitrarily late $`n\equiv-1\pmod{6\ell}`$. Both $`Q(n)`$ and $`Q(n+1)`$ would be divisible by $`\ell`$, contradicting adjacent coprimality. This also excludes $`c=0`$. Thus
``` math
m\in\mathbb{N}_{>0},\qquad c\in\{1,-1\}.
```

The multipliers $`a_n>1`$ on the reduced tail are pairwise coprime, so infinitely many distinct primes occur among them. Once a prime divides one such $`a_n`$, it divides every later $`v_t`$ and no later $`u_t`$. If the cubic $`Q`$ had a rational root, that root would reduce to a root modulo all but finitely many primes. Choose one of the persistent primes outside those exceptions; a sufficiently late index in the root’s residue class would have $`\ell\mid Q(t)=u_t`$, a contradiction. A cubic is reducible over $`\mathbb{Q}`$ only if it has a rational root. Hence $`Q`$ is irreducible.

Set $`\kappa=m/6`$, $`\eta=6c/m`$, and
``` math
f(T)=T^3-T+\eta,\qquad Q(n)=\kappa f(n+1).
```
Let $`\alpha`$ be a root of $`f`$ and $`K=\mathbb{Q}(\alpha)`$, a cubic number field.

<a id="sec:cubic-field"></a>

## Square specialisation

Eliminating $`v_n`$ from the reduced recurrence gives
``` math
\begin{equation}
\label{eq:three-tail}
 u_{n+2}=(a_n+a_{n+1})u_{n+1}-a_n^2u_n.
\end{equation}
```
Let $`\ell\nmid6m`$ be prime and let $`r`$ be a root of $`f`$ in $`\mathbb F_\ell`$. Since $`\eta\ne0`$ modulo $`\ell`$, we have $`r\notin\{0,1,-1\}`$. Choose a sufficiently late index $`k`$ with $`k+1\equiv r\pmod\ell`$, so that $`u_k\equiv0`$. Using $`f(r)=0`$, we obtain
``` math
f(r-1)=-3r(r-1),\qquad f(r+1)=3r(r+1).
```
Multiplying <a href="#eq:three-tail" data-reference-type="eqref" data-reference="eq:three-tail">[eq:three-tail]</a> at index $`k-1`$ by $`u_{k-1}`$ yields
``` math
-u_{k-1}u_{k+1}=(a_{k-1}u_{k-1})^2
 =9\kappa^2r^2(r^2-1)\quad\text{in }\mathbb F_\ell.
```
As $`9\kappa^2r^2`$ is a nonzero square, it follows that $`r^2-1`$ is a nonzero square for every root of $`f`$ modulo each such prime.

We claim that $`\alpha^2-1`$ is a square in $`K`$. Suppose otherwise, and let $`\beta^2=\alpha^2-1`$. The nontrivial automorphism of the quadratic extension $`K(\beta)/K`$ fixes $`\alpha`$ and exchanges $`\beta`$ and $`-\beta`$. Extend it to an automorphism $`\sigma`$ of a Galois closure over $`\mathbb{Q}`$. By the Chebotarev density theorem \[stevenhagenlenstra1996, §3, author-version p. 15\], infinitely many unramified rational primes have Frobenius in the conjugacy class of $`\sigma`$. Choose a prime above each of them whose Frobenius is $`\sigma`$, and discard the finitely many primes of bad reduction, residue characteristic two, or vanishing denominators.

In the residue field, Frobenius fixes $`\bar\alpha`$ but sends $`\bar\beta`$ to $`-\bar\beta\ne\bar\beta`$. Thus $`\bar\alpha\in\mathbb F_\ell`$ is a root of $`f`$, while $`\bar\alpha^2-1`$ is not a square in $`\mathbb F_\ell`$: its only two square roots in the residue field are $`\pm\bar\beta`$, neither fixed by Frobenius. This contradicts the modular condition. Consequently there is a $`\beta\in K`$ with $`\beta^2=\alpha^2-1`$. We can now use this square to determine the coefficients of $`Q`$.

<a id="sec:cubic-trace"></a>

## Traces in the cubic field

Set $`z=\alpha+\beta`$. The relation $`(\alpha+\beta)(\alpha-\beta)=1`$ gives $`z^{-1}=\alpha-\beta`$ and $`\alpha=(z+z^{-1})/2`$, whence $`\mathbb{Q}(z)=K`$. We may therefore write the minimal polynomial of $`z`$ as $`z^3+bz^2+dz+w`$, with rational $`b,d,w`$ and $`w\ne0`$. The polynomial for $`\alpha`$ gives
``` math
\operatorname{Tr}(\alpha)=0,\qquad
 \operatorname{Tr}(\alpha^2)=2,\qquad
 \operatorname{Tr}(\alpha^3)=-3\eta.
```
Newton’s identities for $`z`$ and $`z^{-1}`$ turn these three equations into
``` math
\begin{equation}
\label{eq:cubic-traces}
 d=-bw,\qquad b^2+b(w-w^{-1})=1,\qquad
 \eta=\frac{(b^2+1)(w+w^{-1})}{8}.
\end{equation}
```
For the first equation, use $`\operatorname{Tr}(z)=-b`$, $`\operatorname{Tr}(z^{-1})=-d/w`$. After substituting $`d=-bw`$, the second follows from $`4\operatorname{Tr}(\alpha^2)
=\operatorname{Tr}(z^2)+6+\operatorname{Tr}(z^{-2})`$; the third follows from $`8\operatorname{Tr}(\alpha^3)
=\operatorname{Tr}(z^3)+\operatorname{Tr}(z^{-3})`$, since $`\operatorname{Tr}(z+z^{-1})=0`$.

The middle equation factors as $`(bw-1)(b+w)=0`$. Write $`w=r/s`$ in lowest terms, with $`r\ne0`$, $`s>0`$. Substituting $`b=-w`$ or $`b=1/w`$ into the last equation and using $`\eta=6c/m`$ gives respectively
``` math
m=\frac{48c\,r s^3}{(r^2+s^2)^2}
 \qquad\text{or}\qquad
 m=\frac{48c\,r^3s}{(r^2+s^2)^2}.
```
Because $`\gcd(r^2+s^2,rs)=1`$ and $`m`$ is an integer, $`(r^2+s^2)^2\mid48`$. Since $`r,s`$ are nonzero, this forces $`r^2+s^2=2`$ and $`|r|=s=1`$. The positive value of $`m`$ is consequently $`12`$. The only remaining numerators are
``` math
Q(n)=2n(n+1)(n+2)+1
 \quad\text{and}\quad
 Q(n)=2n(n+1)(n+2)-1.
```

<a id="sec:cubic-mod-seven"></a>

## The contradiction modulo seven

In the plus case, choose a late block starting at $`n\equiv0\pmod7`$; in the minus case, start at $`n\equiv1\pmod7`$. The four successive numerators have residues
``` math
(u_n,u_{n+1},u_{n+2},u_{n+3})\equiv
 \begin{cases}(1,6,0,2)&(c=1),\\(4,5,0,1)&(c=-1).
 \end{cases}
```
Call the first two denominator residues $`d_0,d_1`$ and the displayed numerator residues $`c_0,c_1,0,c_3`$. From $`0=a_{n+1}c_1-d_1`$ and $`c_3=-a_{n+1}d_1`$ we get $`d_1^2=-c_1c_3=2`$. Thus $`d_1\in\{3,4\}`$. The first update, however, gives
``` math
d_1=a_nd_0=\frac{d_0(d_0+c_1)}{c_0}.
```
As $`d_0`$ runs through $`\mathbb F_7`$, the plus case is $`d_0(d_0+6)`$ and the minus case is $`2d_0(d_0+5)`$. Both have image $`\{0,2,5,6\}`$, disjoint from $`\{3,4\}`$. This contradiction excludes both profiles and proves Theorem <a href="#res:cubicrate" data-reference-type="ref" data-reference="res:cubicrate">2</a>.

The companion strengthens eventual disagreement to positive lower density of disagreement with every rational cubic of this form. Its lower bound may depend on the orbit and the cubic. The present theorem uses only exclusion of eventual equality.

<a id="sec:bounded"></a>

# Bounded increases

We next give a sufficient condition for an exact integer recurrence to become Sylvester. The condition bounds upward increments of its numerator and permits arbitrarily large decreases. For reciprocal tails, the relative-error hypothesis below follows from quadratic growth.

<div id="res:bounded" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2360">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-bounded-comparator">Comparator</a></p>

**Theorem 4** (bounded negative part). *Let $`a,C,D:\mathbb{N}\to\mathbb{N}`$ satisfy $`a_n>1`$, $`C_n>0`$, and
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

Ordinary proof of an equivalent restatement. The margin link identifies the earlier formulation; the revised statement has not been reconciled with its formal evidence.

The relative-error limit implies $`|E_n|<C_n`$ eventually. We shall use this inequality to propagate zero errors, then use the lower bound to stabilise the gcd and prohibit unbounded growth by a first crossing. For a rational tail, the lower bound is the additional assumption still needed beyond Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">2</a>.

<a id="sec:defect"></a>

## Zero errors and descent

<span id="sec:descent" label="sec:descent"></span> We call the sequences and error in Theorem <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">4</a> an *exact state*. In a reciprocal tail, $`E_n=0`$ means $`x_n=1/(a_n-1)`$ at a positive tail. We use $`z_+=\max(z,0)`$, and *strict centring* means $`|E_n|<C_n`$.

<div id="res:update" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Arithmetic.lean#L21">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-update-comparator">Comparator</a></p>

**Proposition 5** (error identities). *<span id="res:defect" label="res:defect"></span> For an exact integer state,
``` math
C_{n+1}=C_n-E_n,\qquad
 \bigl(a_{n+1}-a_n^2+a_n-1\bigr)C_{n+1}=a_n^2E_n-E_{n+1}.
```*

</div>

<div class="proof">

*Proof.* The first identity follows by substituting $`D_n=E_n+(a_n-1)C_n`$ into the numerator recurrence. Substituting this expression at the next index and using $`D_{n+1}=a_nD_n`$ gives the second. ◻

</div>

Equation <a href="#eq:tail-estimate" data-reference-type="eqref" data-reference="eq:tail-estimate">[eq:tail-estimate]</a> now gives $`E_n/C_n=1-C_{n+1}/C_n\to0`$, hence strict centring eventually. Koizumi proves this relative-gap limit for an eventual pseudo-greedy tail \[koizumi2025, Corollary 3, p. 9\]. His rounding convention also gives half-width centring, a stronger bound than is used here.

<div id="res:absorb" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Arithmetic.lean#L120">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-absorb-comparator">Comparator</a></p>

**Theorem 6** (absorption and descent). *<span id="res:descent" label="res:descent"></span> For a positive exact state with strict centring, $`E_n=0`$ implies $`E_{n+1}=0`$. For any positive integer state with $`C_{n+1}=C_n-E_n`$, eventual nonnegativity of $`E_n`$ implies its eventual vanishing.*

</div>

<div class="proof">

*Proof.* When $`E_n=0`$, the second identity in Proposition <a href="#res:update" data-reference-type="ref" data-reference="res:update">5</a> shows that $`C_{n+1}`$ divides $`E_{n+1}`$. The inequality $`|E_{n+1}|<C_{n+1}`$ then forces $`E_{n+1}=0`$. For the second assertion, $`C_{n+1}=C_n-E_n`$ makes the positive integer sequence $`C_n`$ eventually nonincreasing, hence constant. ◻

</div>

<div id="res:step" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-step">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-step-comparator">Comparator</a></p>

**Corollary 7** (two zero errors). *<span id="res:eventual" label="res:eventual"></span> If $`E_n=E_{n+1}=0`$ and $`C_{n+1}\ne0`$, then $`a_{n+1}=a_n^2-a_n+1`$. Thus eventual zero error in a positive exact state implies the eventual Sylvester recurrence.*

</div>

<div class="proof">

*Proof.* Cancel the nonzero factor $`C_{n+1}`$ in the second error identity. ◻

</div>

Consequently, beyond a centring threshold either all later errors vanish, or none does. In the latter case $`|E_n|\ge1`$, so the relative-error limit forces $`C_n\to\infty`$. The denominator recurrence remains necessary: $`C_n=n+1`$, $`E_n=-1`$ satisfy the scalar update and relative limit without ever reaching zero.

<a id="sec:barrier"></a>

## A stable gcd and a forbidden block

<div id="res:gcdstab" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Reduction.lean#L103">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-gcdstab-comparator">Comparator</a></p>

**Proposition 8** (gcd stabilisation). *For a positive exact state, suppose that some fixed integer $`B\ge1`$ satisfies $`-B\le E_n<0`$ at infinitely many indices. Then $`G_n=\gcd(C_n,D_n)`$ is eventually constant. Division by its stable value gives a reduced exact tail.*

</div>

<div class="proof">

*Proof.* We have $`G_n\mid G_{n+1}`$ and $`G_n\mid E_n`$. Given $`n`$, choose $`t\ge n`$ with $`-B\le E_t<0`$. Then $`G_n\le G_t\le -E_t\le B`$. Hence the positive divisibility chain stabilises. Division by its stable value preserves the recurrences and gives coprime states. ◻

</div>

This argument uses bounded negative errors only at arbitrarily late indices. The subsequent first-crossing argument also requires a bound on every sufficiently late upward step.

<div id="res:crt" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L839">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-crt-comparator">Comparator</a></p>

**Lemma 9** (consecutive multiples). *For pairwise coprime integers $`m_0,\ldots,m_{B-1}\ge2`$ and every lower bound, there is a larger $`t`$ such that $`m_i\mid t+i`$ for each $`i<B`$.*

</div>

<div class="proof">

*Proof.* Solve $`t\equiv-i\pmod{m_i}`$ by the Chinese remainder theorem and add multiples of $`\prod_i m_i`$ to exceed the prescribed bound. ◻

</div>

For instance, a sequence avoiding multiples of $`2`$ and $`3`$ cannot cross the pair $`6k+2,6k+3`$ from below with upward steps at most two. Decreases do not affect this first-crossing argument.

<div id="res:barrier" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L903">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-barrier-comparator">Comparator</a></p>

**Theorem 10** (Chinese remainder theorem and first crossing). *Let $`u:\mathbb{N}\to\mathbb{N}`$ tend to infinity and let $`B\ge1`$ be an integer with $`u_{n+1}\le u_n+B`$ for every $`n`$. There is no sequence of pairwise coprime integers $`m_i\ge2`$ for which $`\gcd(m_i,u_t)=1`$ whenever $`i<t`$.*

</div>

<div class="proof">

*Proof.* Apply Lemma <a href="#res:crt" data-reference-type="ref" data-reference="res:crt">9</a> to $`m_0,\ldots,m_{B-1}`$, choosing $`t>\max(u_0,\ldots,u_B)`$. There is a first $`n>B`$ with $`u_n\ge t`$. Then
``` math
t\le u_n\le u_{n-1}+B<t+B.
```
Thus $`u_n=t+i`$ for some $`i<B<n`$, and $`m_i\mid u_n`$, contrary to $`\gcd(m_i,u_n)=1`$. ◻

</div>

Bado proves a two-sided bounded-error criterion by this forbidden-block argument \[bado2026, Theorem 5.1, pp. 4–5\]. The gcd stabilisation above allows us to use only the lower error bound.

<div class="proof">

*Proof of Theorem <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">4</a>.* Suppose $`E_n`$ does not vanish eventually. Absorption excludes all sufficiently late zeros, so $`|E_n|\ge1`$. The relative-error limit gives $`C_n\to\infty`$. There must be infinitely many negative errors, since otherwise integer descent would give eventual zero. Their magnitudes are bounded by $`B`$ at late indices, so $`B\ge1`$ and Proposition <a href="#res:gcdstab" data-reference-type="ref" data-reference="res:gcdstab">8</a> gives a stable gcd $`g`$. On the reduced tail, $`u_n=C_n/g\to\infty`$ and
``` math
u_{n+1}-u_n=-E_n/g\le B.
```
By Proposition <a href="#res:reduced" data-reference-type="ref" data-reference="res:reduced">3</a>, the multipliers $`a_i\ge2`$ are pairwise coprime and each is coprime to every later numerator. They supply the moduli prohibited by Theorem <a href="#res:barrier" data-reference-type="ref" data-reference="res:barrier">10</a>, a contradiction. ◻

</div>

<div id="res:cor" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Arithmetic.lean#L179">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-cor-comparator">Comparator</a></p>

**Corollary 11**. *Under Theorem <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">4</a>, the multipliers satisfy $`a_{n+1}=a_n^2-a_n+1`$ eventually.*

</div>

<div class="proof">

*Proof.* Theorem <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">4</a> gives eventual zero error; positivity of $`C_n`$ and Corollary <a href="#res:step" data-reference-type="ref" data-reference="res:step">7</a> give the recurrence. ◻

</div>

<a id="sec:product-bound"></a>

## The condition in the original sequence

Let $`\gamma_n=a_n^2/a_{n+1}-1`$. For $`t_n=P_n/a_n`$,
``` math
t_{n+1}-t_n=t_n\gamma_n.
```
The following corollary therefore assumes only an eventual upper bound on the increments of $`t_n`$; $`t_n`$ itself may be unbounded or decrease.

<div id="res:originalbounded" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/ProductDefect.lean#L211">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-originalbounded-comparator">Comparator</a></p>

**Corollary 12** (bounded increments of $`P_n/a_n`$). *Let $`a_1<a_2<\cdots`$ be positive integers, $`a_{n+1}/a_n^2\to1`$, and $`\sum_{n\ge1}1/a_n\in\mathbb{Q}`$. Put $`P_n=\prod_{j<n}a_j`$. If
``` math
\limsup_{n\to\infty}\frac{P_n}{a_n}
 \left(\frac{a_n^2}{a_{n+1}}-1\right)<+\infty,
```
then $`a_{n+1}=a_n^2-a_n+1`$ for all sufficiently large $`n`$.*

</div>

<div class="proof">

*Proof.* For the canonical integer tail, direct substitution gives
``` math
\begin{equation}
\label{eq:canonical-dictionary}
 E_n+q\frac{P_n}{a_n}\gamma_n
 =qP_n\left(\frac1{a_{n+1}}
 -(a_n-1)\sum_{k\ge n+2}\frac1{a_k}\right).
\end{equation}
```
By the tail estimate, the subtracted term is at most $`4(a_n-1)/a_{n+1}^2<1/a_{n+1}`$ eventually. The right side is positive, so an upper bound on $`(P_n/a_n)\gamma_n`$ gives a lower bound on $`E_n`$. All the remaining hypotheses were established in Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">2</a>. Apply Theorem <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">4</a> and Corollary <a href="#res:cor" data-reference-type="ref" data-reference="res:cor">11</a>. ◻

</div>

Koizumi’s proof of Corollary 4(1) uses this product-weighted comparison \[koizumi2025, (11)–(12), p. 15\]; that corollary assumes a nonpositive upper limit, whereas the argument here allows any finite upper limit. A corresponding LCM comparison appears below. For $`a_n=b^{2^{n-1}}`$, $`b\ge2`$, the increments of $`P_n/a_n`$ are zero. Since this is not a Sylvester tail, the corollary gives irrationality. For a Sylvester sequence starting at $`a_1>1`$, $`a_n-1=(a_1-1)P_n`$ and the increments tend to zero.

The inclusive rate $`1/n`$ gives another useful sufficient condition.

<div id="res:inclusiveone" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-inclusiveone">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-inclusiveone-comparator">Comparator</a></p>

**Corollary 13** (an inclusive one-sided $`1/n`$ bound). *Let $`a_1<a_2<\cdots`$ be positive integers with $`a_{n+1}/a_n^2\to1`$ and $`\sum_n1/a_n\in\mathbb{Q}`$. Suppose that for some $`K\ge0`$ and $`\varepsilon>0`$,
``` math
\gamma_n:=a_n^2/a_{n+1}-1\le \frac1n+\frac{K}{n^{1+\varepsilon}}
 \quad\hbox{for all large }n.
```
Then the sequence is eventually Sylvester. In particular, the conclusion holds under the pointwise eventual bound $`\gamma_n\le1/n`$.*

</div>

<div class="proof">

*Proof.* The hypothesis bounds the positive part of $`\gamma_n`$ eventually by $`1/n+K/n^{1+\varepsilon}`$. Since $`t_{n+1}/t_n=1+\gamma_n`$, comparison with $`n`$ and the convergent product of $`1+K/n^{1+\varepsilon}`$ gives $`t_n=O(n)`$. Hence $`t_n\gamma_n\le t_n(\gamma_n)_+=O(1)`$, and Corollary <a href="#res:originalbounded" data-reference-type="ref" data-reference="res:originalbounded">12</a> applies. ◻

</div>

The weaker condition $`\limsup n(\gamma_n)_+\le1`$ does not suffice for the estimate $`t_n=O(n)`$. For example, the scalar ratios $`1+\gamma_n=1+(1+1/\log n)/n`$ give a product of order $`n\log n`$. This example does not supply a reciprocal-tail counterexample.

For positive limiting increments, take $`a_1=4`$ and $`a_{n+1}=\lceil n a_n^2/(n+1)\rceil`$, beginning $`4,8,43,1387`$. Here $`a_n\ge2\cdot2^{2^{n-1}}`$ and
``` math
0\le1+\frac1n-\frac{a_n^2}{a_{n+1}}<\frac4{a_n^2}.
```
Consequently $`t_n\sim K n`$ and $`t_{n+1}-t_n\to K>0`$. The corollary proves irrationality because $`\gamma_n\sim1/n`$ is incompatible with a Sylvester tail. The cubic example in the introduction has unbounded increments and requires the different proof in Section <a href="#sec:secondaryrate" data-reference-type="ref" data-reference="sec:secondaryrate">3</a>.

<a id="sec:mass"></a>

# Finite total relative increase

A different sufficient condition is summability of the relative upward increments. We record the elementary argument because it applies to an arbitrary positive integer sequence. In comparison, $`C_n=n+1`$ and $`C_n=(n+1)^2`$ have relative increments tending to zero but divergent sums of relative increases.

<div id="res:massscalar" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Frontier.lean#L84">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-massscalar-comparator">Comparator</a></p>

**Theorem 14** (a convergent sum of relative increases). *<span id="res:mass" label="res:mass"></span> Let $`C_n`$ be positive integers and $`E_n`$ integers satisfying $`C_{n+1}=C_n-E_n`$. If
``` math
\sum_n\frac{(-E_n)_+}{C_n}<\infty,
```
then $`E_n=0`$ eventually. Neither denominator dynamics nor vanishing relative error is required.*

</div>

<div class="proof">

*Proof.* Set $`\delta_n=(-E_n)_+/C_n`$. Then
``` math
C_N\le C_0\prod_{n<N}(1+\delta_n)
 \le C_0\exp\!\left(\sum_n\delta_n\right).
```
Choose an integer upper bound $`K`$ for $`C_n`$. Each strict rise contributes at least $`1/K`$ to $`\sum\delta_n`$, so there are only finitely many rises. The remaining positive integer sequence is nonincreasing and stabilises, and the update then gives $`E_n=0`$. ◻

</div>

The proof also allows positive real $`C_n`$ with integer $`E_n`$: the values lie in $`C_0+\mathbb{Z}`$, whose bounded positive part is finite. Discrete increments are essential to this argument. With real errors, $`C_n=1+1/(n+1)`$ decreases forever with zero relative-increase sum; without positivity, $`C_n=-n-1`$, $`E_n=1`$ does so too. The companion’s Section 13 gives the details.

On an exact reciprocal-tail orbit the conclusion gives the Sylvester recurrence. For the gap sequence of the pseudo-greedy expansion, the same criterion, with the same product bound and integer descent, appears in the Erdős Problem a Day working report on Problem #243, dated 12 August 2026 \[erdosproblemaday243, A global termination criterion\]; the statement above is for any positive integer sequence with $`C_{n+1}=C_n-E_n`$. This summability condition and the bound in Theorem <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">4</a> are different estimates. For exact reciprocal tails with $`|E_n|/C_n\to0`$, each is equivalent to eventual vanishing of $`E_n`$; neither estimate has been derived here from the unrestricted problem.

<a id="sec:lcmrecords"></a>

# New maxima of an LCM numerator

Instead of multiplying all earlier denominators, one can clear the rational tail with their least common multiple. We will sum only at steps where the resulting numerator exceeds all its earlier values. This allows some increases to be omitted from the sum and others to receive smaller weights. Set
``` math
L_n=\operatorname{lcm}(q,a_1,\ldots,a_{n-1}),\quad
 M_n=D_n/L_n,\quad U_n=C_n/M_n,\quad V_n=E_n/M_n.
```
The rational tail has denominator dividing $`L_n`$, so $`U_n`$ and $`V_n`$ are integers. This need not be a reduced fraction: $`U_n`$ and $`L_n`$ may share a factor. With $`\rho_n=\gcd(L_n,a_n)`$, the exact updates are
``` math
M_{n+1}=M_n\rho_n,\qquad
 \rho_nU_{n+1}=U_n-V_n,\qquad V_n=L_n-(a_n-1)U_n.
```
These coordinates and updates also appear in Bado’s September 2026 preprint. With his denominator parameter equal to $`q`$, his $`M_{n-1}`$, $`\Delta_{n-1}`$, $`K_{n-1}`$, $`u_n`$ and $`g_n`$ are respectively our $`L_n`$, $`M_n`$, $`U_n`$, $`V_n`$ and $`\rho_n`$; his (19) is the middle update above \[bado2026, Proposition 7.1 and (16)–(20), pp. 6–7\].

Since $`L_n\mid qP_n`$ and $`V_n=(L_n/(qP_n))E_n`$, multiplying <a href="#eq:canonical-dictionary" data-reference-type="eqref" data-reference="eq:canonical-dictionary">[eq:canonical-dictionary]</a> by $`L_n/(qP_n)`$ gives, eventually,
``` math
\begin{equation}
\label{eq:general-clearance-dictionary}
 0<V_n+\frac{L_n}{a_n}\left(\frac{a_n^2}{a_{n+1}}-1\right)
 \le\frac{L_n}{a_{n+1}}.
\end{equation}
```
Its lower bound gives the LCM corollary below. Summability of the comparison error is proved when needed for the weighted criterion; the different denominator update is accounted for by $`\rho_n`$.

Write $`R_n=\max_{j\le n}U_j`$ and $`\mathcal R=\{n:U_{n+1}>R_n\}`$. Strict centring already gives $`U_{n+1}<U_n`$ when $`\rho_n\ge2`$, so every sufficiently late strict rise has $`\rho_n=1`$. The stronger eventual bound $`-U_n\le2V_n`$, supplied by $`V_n/U_n=E_n/C_n\to0`$, gives the quantitative estimate $`U_{n+1}\le3U_n/4`$ when $`\rho_n\ge2`$. At a sufficiently late record step, where $`\rho_n=1`$, the actual jump is $`d_n=U_{n+1}-U_n=-V_n>0`$. This identity is not asserted at a contracting step with $`\rho_n\ge2`$.

<div id="res:weightedrecord" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR11/CanonicalRecords.lean#L202">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-weightedrecord-comparator">Comparator</a></p>

**Theorem 15** (a convergent weighted sum over new maxima). *Assume the growth and rationality hypotheses of Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a>. Let $`f:[1,\infty)\to[0,\infty)`$ be finite and nonincreasing, with $`\int_1^\infty f(t)\,dt=\infty`$. Then the sequence is eventually Sylvester if and only if, for some integer $`B\ge0`$,
``` math
\sum_{n\in\mathcal R}(-V_n-B)_+f(U_n)<\infty.
```*

</div>

At a late record step, $`-V_n=U_{n+1}-U_n`$, so the summand charges the part of the increase beyond $`B`$. The theorem permits $`f(t)=1/t`$ and $`f(t)=1/[t\log(et)]`$. It excludes $`f(t)=1/t^2`$, whose integral is finite. We will prove divergence for every admissible $`f`$ and fixed $`B`$ on a non-Sylvester tail. The relative limit $`V_n/U_n\to0`$ alone gives no bound for this series.

<div class="proof">

*Proof.* Suppose the sequence is not eventually Sylvester. Absorption and integrality give
``` math
\frac1{U_n}\le\frac{|V_n|}{U_n}=\frac{|E_n|}{C_n}\longrightarrow0.
```
Thus $`U_n\to\infty`$, so there are infinitely many record steps. At every sufficiently late one, $`\rho_n=1`$, so $`a_n`$ is coprime to $`L_n`$. The corresponding terms $`a_n`$ are pairwise coprime: an earlier term divides the later $`L_n`$, while the term at that record is coprime to $`L_n`$. For any fixed $`B\ge1`$, choose $`B`$ such multipliers $`m_0,\ldots,m_{B-1}>B`$ and take $`T`$ after their indices and after the threshold beyond which records have $`\rho_n=1`$. Their size follows from $`a_n\to\infty`$.

Put $`P=\prod_i m_i`$ and choose $`x`$ by the Chinese remainder theorem with $`m_i\mid x+i`$. Consider all translates $`\tau=x+B+kP>R_T`$, $`k\in\mathbb{Z}`$; the first is at most $`R_T+P`$. Consider a first crossing $`U_n\le R_n<\tau\le U_n+d_n`$. This is a record step, and $`d_n=U_{n+1}-U_n`$ includes any recovery from an earlier decrease. If $`d_n\le B`$, then $`U_n\in[\tau-B,\tau)`$, so some $`m_i`$ divides $`U_n`$. It also divides $`L_n`$, hence divides $`d_n=(a_n-1)U_n-L_n`$, contradicting $`0<d_n\le B<m_i`$.

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
eventually. Thus the two nonnegative summands $`U_nf(U_n)(\gamma_n-B/U_n)_+`$ and $`(-V_n-B)_+f(U_n)`$ differ by at most $`3U_nf(U_n)/a_n`$. We verify that this comparison error is summable. Since $`a_nx_n\to1`$, we have $`C_n/a_n\sim qP_n/a_n^2`$, and
``` math
\frac{P_{n+1}/a_{n+1}^{2}}{P_n/a_n^{2}}
 =\frac{a_n^3}{a_{n+1}^{2}}\longrightarrow0.
```
The ratio test gives $`\sum_nC_n/a_n<\infty`$; now $`U_n\le C_n`$ and $`f(U_n)\le f(1)`$ make the comparison error summable. The errors in <a href="#eq:canonical-dictionary" data-reference-type="eqref" data-reference="eq:canonical-dictionary">[eq:canonical-dictionary]</a> and <a href="#eq:general-clearance-dictionary" data-reference-type="eqref" data-reference="eq:general-clearance-dictionary">[eq:general-clearance-dictionary]</a> are also absolutely summable, since each is eventually between zero and $`qP_n/a_{n+1}=O(P_n/a_n^2)`$. Consequently Theorem <a href="#res:weightedrecord" data-reference-type="ref" data-reference="res:weightedrecord">15</a> is equivalent to finiteness of
``` math
\begin{equation}
\label{eq:weightedgrowth}
 \sum_{n\in\mathcal R}U_nf(U_n)
 \left(\frac{a_n^2}{a_{n+1}}-1-\frac B{U_n}\right)_+
\end{equation}
```
for some $`B`$. Finiteness under the unrestricted hypotheses remains to be proved. In both forms of the criterion, the jump is $`U_{n+1}-U_n`$, including recovery from an earlier decrease. Replacing it by the increase $`R_{n+1}-R_n`$ would invalidate the crossing estimate. Termwise convergence of the summands to zero would also be insufficient.

<div id="res:lcmbounded" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/LcmDefect.lean#L49">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-lcmbounded-comparator">Comparator</a></p>

**Corollary 16** (a bound using the least common multiple). *Assume the hypotheses of Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a>. Write $`A_n=\operatorname{lcm}(a_1,\ldots,a_{n-1})`$ with $`A_1=1`$. If
``` math
\limsup_{n\to\infty}\frac{A_n}{a_n}
 \left(\frac{a_n^2}{a_{n+1}}-1\right)<\infty,
```
then the sequence is eventually Sylvester.*

</div>

<div class="proof">

*Proof.* Since $`L_n/A_n=q/\gcd(q,A_n)`$ lies in $`[1,q]`$, an upper bound on the expression in the corollary gives an upper bound on $`(L_n/a_n)(a_n^2/a_{n+1}-1)`$; negative terms remain negative. Equation <a href="#eq:general-clearance-dictionary" data-reference-type="eqref" data-reference="eq:general-clearance-dictionary">[eq:general-clearance-dictionary]</a> therefore bounds the negative part of $`V_n`$. Choose an integer $`B`$ above that eventual bound. The record series then vanishes after a finite prefix, so Theorem <a href="#res:weightedrecord" data-reference-type="ref" data-reference="res:weightedrecord">15</a> applies. ◻

</div>

Erdős and Straus assume a nonpositive upper limit in this LCM expression \[erdosstraus1964, Theorem 3, p. 132\]: their $`N_k`$ is $`A_{k+1}`$ and their growth ratio has index $`k+1`$. Tijdeman and Yuan extend this type of criterion to positive numerators \[tijdemanyuan2002\]. Here any finite upper bound suffices under the quadratic-limit assumption. Since $`A_n\mid P_n`$, the LCM hypothesis is no stronger than the product hypothesis in Corollary <a href="#res:originalbounded" data-reference-type="ref" data-reference="res:originalbounded">12</a>: if the product expression is at most $`B`$, the LCM expression is at most $`\max(B,0)`$. When the earlier terms are pairwise coprime the two weights agree; repeated prime factors can make the LCM much smaller. This comparison does not assert the existence of a non-Sylvester rational example satisfying one bound but not the other.

The finite upper limit means an eventual upper bound; it does not require $`q`$ to divide the LCM of the preceding denominators. For positive integer summand numerators $`b_n`$, the modified error is $`V_n=b_nL_n-(a_n-1)U_n`$. The companion, Section 6 under “Integer coefficients”, separately proves boundedness from a lower bound on $`V_n`$ and eventual constancy when $`V_n/U_n\to0`$ is also assumed. The latter conclusion must not be read into the first hypothesis alone. The same section links finite examples separating them; compare Badea \[badea1993, p. 316\] and Tijdeman–Yuan \[tijdemanyuan2002\]. The companion’s Section 3 retains the signed-series comparison with Duverney \[duverney2001, Corollary 3.2, p. 287\] and the different growth hypotheses for irrationality exponents in \[duverneykurosawashiokawa2020, Theorem 1, author-version p. 2\]. The crossing theorem uses neither of these further sets of hypotheses.

<a id="sec:open"></a>

# Further questions

<div id="res:frontier" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Frontier.lean#L151">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-frontier-comparator">Comparator</a></p>

**Proposition 17** (necessary profile). *The integer tail of a sequence satisfying Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a>’s hypotheses but not its conclusion has $`E_n\ne0`$ eventually, $`|E_n|/C_n\to0`$, unbounded negative magnitudes along negative indices, and
``` math
\sum_n\frac{(-E_n)_+}{C_n}=\infty.
```*

</div>

<div class="proof">

*Proof.* Absorption excludes late zeros, descent excludes an eventually nonnegative error, and Theorems <a href="#res:bounded" data-reference-type="ref" data-reference="res:bounded">4</a> and <a href="#res:massscalar" data-reference-type="ref" data-reference="res:massscalar">14</a> exclude the two finiteness conditions. ◻

</div>

For $`B\ge0`$ put
``` math
F_B(X)=\sum_{\substack{n\in\mathcal R\\U_n\le X}}(-V_n-B)_+.
```
For a rational tail satisfying the growth hypothesis, the weighted criterion reduces the original problem to proving that, for some fixed integer $`B\ge0`$,
``` math
\begin{equation}
\label{eq:remaining-record-budget}
 \liminf_{X\to\infty}\frac{F_B(X)}X=0.
\end{equation}
```
If the recurrence is not eventually Sylvester, first crossings instead give $`F_B(X)\ge X/P_B-O_B(1)`$, with an orbit-dependent CRT modulus $`P_B`$. The sum groups each record step by its starting numerator $`U_n`$, not by the running maximum $`R_n`$ or the time index. On a non-Sylvester tail, $`U_n\to\infty`$, so only finitely many of these steps begin below any fixed $`X`$. The following lemma proves equivalence with the existence of an admissible weight. Enumerate the record indices $`n\in\mathcal R`$ by $`j`$, and apply it with $`u_j=U_n`$ and $`w_j=(-V_n-B)_+`$. It remains to deduce <a href="#eq:remaining-record-budget" data-reference-type="eqref" data-reference="eq:remaining-record-budget">[eq:remaining-record-budget]</a> from growth and rationality. Such a deduction would contradict the first-crossing lower bound for every non-Sylvester tail.

<div id="res:weights" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR20/RealCutoffCriterion.lean#L87">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-weights-comparator">Comparator</a></p>

**Lemma 18** (weights and linear density). *Let $`u_j`$ be positive integers, let $`w_j\ge0`$, and put $`F(X)=\sum_{u_j\le X}w_j`$, with the sum allowed a priori to be $`+\infty`$. Then $`\liminf_{X\to\infty}F(X)/X=0`$ if and only if there is a finite nonincreasing $`f:[1,\infty)\to[0,\infty)`$ with $`\int_1^\infty f(t)\,dt=\infty`$ and $`\sum_jw_jf(u_j)<\infty`$.*

</div>

<div class="proof">

*Proof.* Suppose the lower limit vanishes. Choose cutoffs at which the ratio $`F(X)/X`$ is small. Since $`F`$ is constant on each $`[m,m+1)`$, there are integers $`X_1<X_2<\cdots`$ with $`X_k\ge2^k`$ and $`F(X_k)\le2^{-k}X_k`$. Set
``` math
f(t)=\sum_{k\ge1}\frac{\mathbf 1_{[1,X_k]}(t)}{X_k}.
```
This function is nonincreasing and bounded by $`\sum_k2^{-k}`$. Each cutoff contributes $`1-1/X_k`$ to its integral, but at most $`2^{-k}`$ to the weighted sum. Interchanging nonnegative sums therefore gives
``` math
\int_1^\infty f(t)\,dt=\sum_k(1-1/X_k)=\infty,
 \qquad
 \sum_jw_jf(u_j)=\sum_k\frac{F(X_k)}{X_k}\le1.
```

Conversely, let $`f`$ be such a weight and suppose $`F(m)\ge cm`$ for some $`c>0`$ and all integers $`m\ge M`$. A nonincreasing nonnegative function with divergent integral is positive everywhere, so $`F(X)\le f(X)^{-1}\sum_jw_jf(u_j)`$ is finite. Partial summation gives, for $`N>M`$,
``` math
\sum_{u_j\le N}w_jf(u_j)
 =F(N)f(N)+\sum_{m=1}^{N-1}F(m)\bigl(f(m)-f(m+1)\bigr)
 \ge c\Bigl(Mf(M)+\sum_{m=M+1}^{N}f(m)\Bigr),
```
every term being nonnegative. The right side diverges as $`N\to\infty`$, because $`\sum_{m\ge1}f(m)\ge\int_1^\infty f(t)\,dt=\infty`$. ◻

</div>

<a id="sec:scalar-limit"></a>

## Why the scalar profile is not enough

The remaining estimate must use arithmetic compatibility, not just the size of the error. For example, $`C_n=n^2+1`$, $`E_n=-(2n+1)`$ has vanishing relative error and the necessary scalar pattern. But at $`n=2,3,4`$ its numerators are $`5,10,17`$. The update $`10=5a_2-D_2`$ forces $`5\mid D_2`$, hence $`5\mid D_3=a_2D_2`$; the next update would force $`5\mid17`$. It is not an exact tail. The companion’s Section 14 also constructs sequences avoiding sparse fixed moduli and distinguishes that avoidance from compatibility with all later denominators. Neither property alone supplies <a href="#eq:remaining-record-budget" data-reference-type="eqref" data-reference="eq:remaining-record-budget">[eq:remaining-record-budget]</a>.

The profile is a necessary condition, not a construction. For a zero-indexed exact orbit with $`a_n>1`$, $`C_n>0`$, $`D_n\ge0`$ and $`E_n/C_n\to0`$, the companion’s Section 4 proves that $`D_n>0`$, $`C_n/D_n\to0`$ and $`\sum_n1/a_n=C_0/D_0`$; it also derives quadratic growth. Thus these global orbit assumptions already make the orbit the integer tail of a reciprocal series. A scalar numerical profile or a finite admissible prefix does not.

<div id="res:lcmheight" class="problem">

**Problem 19** (growth of repeated denominator factors). For every rational-tail orbit satisfying the hypotheses but not the conclusion of Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a>, must
``` math
\limsup_{n\to\infty}\frac{\log M_n}{n}>0?
```
Equivalently, must there be a $`K\ge1`$ for which
``` math
2^n\le M_n^K
```
at infinitely many indices?

</div>

Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">2</a> gives $`C_{n+1}/C_n\to1`$; averaging logarithms therefore gives $`\log C_n=o(n)`$. Since $`1\le M_n\le C_n`$, every such orbit already satisfies $`\log M_n/n\to0`$. A positive answer therefore holds exactly when no such orbit exists: proving it from failure of Sylvester behaviour would exclude every counterexample.

<a id="acknowledgements."></a>

#### Acknowledgements.

I thank Wouter van Doorn for advice on the exposition, in particular for asking what the additional bound excludes and for pointing out unnecessary terminology and notation.

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
the [forced numerator](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L22), and the divisor is $`n+2`$. The orbit continues for another step exactly when this division is exact. Here survival counts exact divisions; it does not impose the positivity conditions of an infinite reciprocal-tail orbit. The [formal survival predicate](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L75) requires exact division at each step.

<div id="ex:shape" class="example">

**Example 20** (the shape equation running until it fails). The forced orbit from $`a=3`$ reads this way: $`\operatorname{num}(0,3)=6`$ is divisible by $`2`$ and gives $`a_1=3`$, while $`\operatorname{num}(1,3)=13`$ is not divisible by $`3`$, so the orbit stops there.

</div>

Direct iteration can produce very large intermediate integers. To decide whether the first $`h`$ divisions are exact, however, it suffices to know the initial value modulo $`(h+1)!`$. Computing a pseudo-greedy orbit through residues modulo a shrinking product modulus is Koizumi’s method \[koizumi2025, Remark 2 and Algorithm 1, pp. 13–14\]; for the forced numerator that product is a factorial.

<div id="res:residue" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L134">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-243-reciprocal-tail-rigidity.md#res-residue-comparator">Comparator</a></p>

**Theorem 21** (factorial residue reduction). *For all $`h`$ and all integers $`a\equiv b \pmod{(h+1)!}`$, the orbit from $`a`$ survives $`h`$ forced updates exactly when the orbit from $`b`$ does.*

</div>

<div class="proof">

*Proof.* Define $`M(0,i)=1`$ and $`M(h+1,i)=(i+2)M(h,i+1)`$. Thus $`M(h,0)=(h+1)!`$. We prove the stronger statement that, at index $`i`$, congruent inputs modulo $`M(h,i)`$ survive the same $`h`$ updates. There is nothing to prove for $`h=0`$.

For the inductive step, suppose $`a\equiv b\pmod{(i+2)M(h,i+1)}`$. Since $`\operatorname{num}(i,\cdot)`$ is an integer polynomial, its values at $`a`$ and $`b`$ are congruent modulo that product. In particular, one is divisible by $`i+2`$ if and only if the other is. If neither is divisible, both orbits stop. Otherwise their quotients are congruent modulo $`M(h,i+1)`$, so the induction hypothesis applies to the remaining $`h`$ updates at index $`i+1`$. Taking $`i=0`$ proves the claim. ◻

</div>

At $`h=1`$, survival means $`2\mid a^2-2a+3`$, or equivalently that $`a`$ is odd. This illustrates Theorem <a href="#res:residue" data-reference-type="ref" data-reference="res:residue">21</a> with modulus $`2!=2`$.

The enumeration in Example 9.1 of the companion, over $`2\le a_0<5000`$, gives at most $`17`$ successful updates ($`18`$ values including $`a_0`$). The seed $`a_0=1`$ is excluded because it is fixed and violates $`a_n\ge2`$. This finite calculation establishes only the stated range. The infinite [constant-negative exclusion](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L286) requires the separate argument under the hypotheses given there.

<a id="app:index"></a>

# Sources and related work

The companion *Reciprocal-Tail Rigidity: Theorems, Proofs and Questions* keeps the complete arguments and fixed-revision declaration routes. Its Section 2 contains the general regular-rate extraction, cubic square specialisation, trace calculation and the stronger positive-density disagreement result. Sections 4–5 develop exact tails; Sections 11–12 give the gcd and bounded-increment arguments; Section 6 contains the LCM and integer-coefficient results; Section 13 treats the scalar summability criterion; and Section 14 keeps the unresolved arithmetic estimates and failed constructions. Its final result map records the proof dependencies. The auxiliary numerical constructions there satisfy only the hypotheses stated for them; they need not be rational reciprocal series.

The older integer-remainder method is represented by Erdős–Straus \[erdosstraus1974, Theorem 2.1, pp. 85–86\]. The polynomial Cantor-series hypotheses in Hančl–Tijdeman \[hancltijdeman2008, Theorem 2.2, pp. 39–40\] and the freely selectable series of Problem #270 \[crmarickovac2025, Theorems 1–2\] concern different settings; the companion’s Section 3 explains the distinction. The Isabelle/HOL work \[kouli2020\] formalises older Erdős–Straus criteria, not Problem #243. The general regular-rate extraction in the companion also uses the standard Gamma-ratio asymptotics recorded in \[dlmf_gamma\]; the cubic specialisation here uses only its explicit polynomial $`F_n`$.

The margin links identify the recorded formal propositions at fixed revisions. No Lean or Comparator checks have been rerun for this revision, and no independent review is claimed. The printed number-field proof uses Chebotarev; the formal square-specialisation proof uses a Dedekind-zeta pole comparison. The bounded-negative theorem is restated here with the equivalent hypothesis $`E_n/C_n\to0`$, which also implies eventual strict centring. The supplied evidence records have source-pin and index gaps, so their presence alone does not certify this revision. Neither cubic proof supplies the unrestricted estimate in Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">7</a>.

The formal [factorial residue reduction](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L134) uses the [shrinking-modulus induction](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L97), [polynomial congruence](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L26), and [cancellation after exact division](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L41). Its modulus is identified by the [ascending-factorial formula](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L59) and its [factorial value at the initial index](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L69).

<div class="thebibliography">

99

P. Erdős and E. G. Straus, [*On the irrationality of certain Ahmes series*](https://users.renyi.hu/~p_erdos/1964-19.pdf), J. Indian Math. Soc. (N.S.) **27** (1964), 129–133. MR 175848. D. Duverney, [*Irrationality of fast converging series of rational numbers*](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf), J. Math. Sci. Univ. Tokyo **8** (2001), 275–316. MR 1837165. C. Badea, [*A theorem on irrationality of infinite series and applications*](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf), Acta Arith. **63** (1993), no. 4, 313–323, doi:[10.4064/aa-63-4-313-323](https://doi.org/10.4064/aa-63-4-313-323). R. Tijdeman and P. Yuan, *On the rationality of Cantor and Ahmes series*, Indag. Math. (N.S.) **13** (2002), no. 3, 407–418, doi:[10.1016/S0019-3577(02)80018-0](https://doi.org/10.1016/S0019-3577(02)80018-0). P. Erdős and R. L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf), Monogr. Enseign. Math. 28, Geneva, 1980, p. 64. P. Erdős, [*On the irrationality of certain series: problems and results*](https://users.renyi.hu/~p_erdos/1988-22.pdf), in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). I. O. Bado, *Prime-Support Rigidity and Primitive Pseudo-Greedy Dynamics: Partial Progress on Erdős Problem #243*, preprint posted September 2026, doi:[10.13140/RG.2.2.36612.08325](https://doi.org/10.13140/RG.2.2.36612.08325). P. White with Claude (Anthropic), [*Erdős \#243: working report*](https://erdosproblemaday.com/report/243), Erdős Problem a Day, page dated 12 August 2026. AI-assisted, unrefereed working report. P. Stevenhagen and H. W. Lenstra, Jr., [*Chebotarëv and his density theorem*](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1994c/art.pdf), Math. Intelligencer **18** (1996), no. 2, 26–37, doi:[10.1007/BF03027290](https://doi.org/10.1007/BF03027290). Page references are to the linked author version dated 23 March 1995. J. Koizumi, [*Irrationality of the reciprocal sum of doubly exponential sequences*](https://math.colgate.edu/~integers/aa28/aa28.pdf), Integers **26** (2026), Paper No. A28, 17 pp., doi:[10.5281/zenodo.18714404](https://doi.org/10.5281/zenodo.18714404). Locators refer to this published version. T. F. Bloom, [*Erdős Problem \#243*](https://www.erdosproblems.com/243), accessed 28 July 2026. P. Erdős and E. G. Straus, [*On the irrationality of certain series*](https://msp.org/pjm/1974/55-1/pjm-v55-n1-p08-s.pdf), Pacific J. Math. **55** (1974), no. 1, 85–92. J. Hančl and R. Tijdeman, [*On the irrationality of polynomial Cantor series*](https://www.impan.pl/shop/en/publication/transaction/download/product/82186), Acta Arith. **133** (2008), no. 1, 37–52, doi:[10.4064/aa133-1-3](https://doi.org/10.4064/aa133-1-3). Locators refer to the published version. D. Duverney, T. Kurosawa and I. Shiokawa, [*Irrationality exponents of certain fast converging series of rational numbers*](https://danielduverney.fr/documents/theorie-des-nombres/Tsukuba.pdf), Tsukuba J. Math. **44** (2020), no. 2, 235–250, doi:[10.21099/tkbjm/20204402235](https://doi.org/10.21099/tkbjm/20204402235). Theorem locators follow the linked 14-page author version. T. Crmarić and V. Kovač, [*On the irrationality of certain super-polynomially decaying series*](https://arxiv.org/abs/2504.18712v1), Colloq. Math. **179** (2025), 55–68, doi:[10.4064/cm9628-5-2025](https://doi.org/10.4064/cm9628-5-2025). Theorem locators follow arXiv:2504.18712v1. A. Koutsoukou-Argyraki and W. Li, [*Irrationality Criteria for Series by Erdős and Straus*](https://isa-afp.org/entries/Irrational_Series_Erdos_Straus.html), Archive of Formal Proofs, 12 May 2020. An Isabelle/HOL formalisation; the archive entry identifies the results formalised. National Institute of Standards and Technology, [*Digital Library of Mathematical Functions*, §5.11(iii), formula 5.11.12](https://dlmf.nist.gov/5.11.E12), accessed 16 September 2026.

</div>
