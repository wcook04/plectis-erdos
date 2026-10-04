<a id="erdos-243-reciprocal-tail-rigidity"></a>

# Cubic-Rate Irrationality of Reciprocal Sums

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We prove irrationality of the reciprocal sum when strictly increasing positive integers satisfy $`a_n^2/a_{n+1}=1+3/n+o(n^{-3})`$. The proof extracts a cubic polynomial from an integer tail numerator, then uses a square in a cubic field to restrict its coefficients. Congruences modulo seven exclude the remaining possibilities. The unrestricted Erdős–Graham question remains open.

<a id="sec:problem"></a>

# Introduction

The Sylvester recurrence $`a_{n+1}=a_n^2-a_n+1`$ gives a rational reciprocal sum by telescoping:
``` math
\frac1{a_n-1}=\frac1{a_n}+\frac1{a_{n+1}-1}.
```
For an increasing sequence of positive integers that eventually satisfies this recurrence, the tail sum at every sufficiently large index is $`1/(a_n-1)`$. Erdős and Graham asked whether every rational reciprocal sum with $`a_{n+1}\sim a_n^2`$ arises in this way.

<div id="res:problem" class="problem">

**Problem 1** (Erdős Problem 243). Let $`1\le a_1<a_2<\cdots`$ be a sequence of integers with
``` math
\lim_{n\to\infty}\frac{a_n}{a_{n-1}^{2}}=1
 \qquad\text{and}\qquad
 \sum\frac{1}{a_n}\in\mathbb{Q}.
```
Then $`a_n=a_{n-1}^{2}-a_{n-1}+1`$ for all sufficiently large $`n`$.

</div>

Erdős and Graham \[erdosgraham1980, p. 64\] asked this question; see also Erdős \[erdos1988, p. 105\] and Bloom’s catalogue \[erdosproblems\]. We prove the following irrationality result for a restricted class of sequences with $`a_{n+1}\sim a_n^2`$.

<div id="res:cubicrate" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L70">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-243-reciprocal-tail-rigidity.md#res-cubicrate-comparator">Comparator</a></p>

**Theorem 2** (cubic-rate irrationality). *A strictly increasing sequence of positive integers with
``` math
a_n^2/a_{n+1}=1+\frac3n+o(n^{-3})
```
has irrational reciprocal sum.*

</div>

Under the eventual Sylvester recurrence, $`a_n^2/a_{n+1}-1=O(1/a_n)`$, which is much smaller than $`3/n`$. Theorem <a href="#res:cubicrate" data-reference-type="ref" data-reference="res:cubicrate">2</a> therefore treats a restricted case of the problem by excluding rationality altogether. The general quadratic limit $`a_{n+1}\sim a_n^2`$ remains insufficient for any argument given here.

For example, set $`a_1=8`$ and
``` math
a_{n+1}=\left\lceil\frac{n a_n^2}{n+3}\right\rceil.
```
This gives $`8,16,103,5305,\ldots`$. From $`a_{n+1}\ge a_n^2/4`$ we obtain $`a_n\ge4\cdot2^{2^{n-1}}`$ by induction. The error introduced by the ceiling is less than one, and hence
``` math
0\le 1+\frac3n-\frac{a_n^2}{a_{n+1}}<\frac{16}{a_n^2}=o(n^{-3}).
```
The theorem applies to this explicitly defined sequence.

If the sum is rational, clearing denominators gives positive integer tail numerators $`C_n`$. Their growth is cubic, so we compare them with $`F_n=n(n+1)(n+2)`$, for which $`F_{n+1}/F_n=1+3/n`$. The ratio estimate gives $`C_n=AF_n+o(n)`$. Subtracting the recurrences for $`C_n`$ and $`AF_n`$ then shows that the first difference of the error tends to zero. It follows that $`\Delta^4C_n\to0`$. Since these fourth differences are integers, they eventually vanish, and $`C_n=AF_n+B`$.

We next use the denominator recurrence to constrain this polynomial. It gives a square condition at every root of a cubic modulo almost every prime. Chebotarev’s theorem implies that the corresponding element of the cubic number field is a square. Trace identities leave two possible polynomials; four consecutive terms modulo seven exclude both. The proof in Section <a href="#sec:secondaryrate" data-reference-type="ref" data-reference="sec:secondaryrate">3</a> follows this order.

The proof uses the integer tail numerators of Koizumi \[koizumi2025, Lemma 4\]. Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">2</a> introduces these numerators, and Section <a href="#sec:secondaryrate" data-reference-type="ref" data-reference="sec:secondaryrate">3</a> proves the theorem. The [long record](../../../paper/243/erdos243-reciprocal-tail-reasoning-surface.pdf#nameddest=long243-bounded) treats bounded increases, summable relative increases and weighted crossings of new maxima as separate criteria for the Sylvester recurrence. Those criteria do not resolve the general question.

<a id="sec:transfer"></a>

# Tail numerators

<span id="sec:state" label="sec:state"></span> For the Sylvester sequence $`2,3,7,43,\ldots`$, whose reciprocal sum is $`1`$, the successive tails are $`1,1/2,1/6,1/42,\ldots`$. Multiplication by the products $`1,2,6,42,\ldots`$ leaves the constant integer numerator $`1`$. For an arbitrary rational reciprocal sum, we also multiply by a denominator of the whole sum. The resulting integer numerators need not be constant.

Assume now that $`a_n`$ are strictly increasing positive integers, $`a_{n+1}/a_n^2\to1`$, and $`\sum_{n\ge1}1/a_n=p/q`$ with positive integers $`p,q`$. All indices in this construction start at $`1`$. Put
``` math
x_n=\sum_{k\ge n}\frac1{a_k},\qquad
 P_n=\prod_{1\le j<n}a_j,\qquad D_n=qP_n,\qquad C_n=D_nx_n.
```
Here $`P_1=1`$, $`D_1=q`$ and $`C_1=p`$. Since every $`a_k`$ with $`k<n`$ divides $`P_n`$, subtracting the finite prefix from $`p/q`$ gives
``` math
C_n=pP_n-q\sum_{1\le k<n}\frac{P_n}{a_k}\in\mathbb{N}_{>0}.
```
The integer is positive because it equals the positive tail multiplied by $`D_n`$. Removing the term $`1/a_n`$ from the tail gives
``` math
\begin{equation}
\label{eq:recurrences}
 C_{n+1}=a_nC_n-D_n,\qquad D_{n+1}=a_nD_n.
\end{equation}
```
Koizumi constructs these coordinates in Lemma 4 \[koizumi2025, pp. 11–12\]. On a pseudo-greedy tail his $`c_n,d_n,e_n`$ correspond to $`C_n,D_n,D_n-(a_n-1)C_n`$. If the tail is restarted with its value in lowest terms, both coordinates are divided by the same fixed integer. We retain the unreduced fraction $`C_n/D_n`$ to keep the denominator update multiplicative. In the cubic proof we first extract a polynomial for this $`C_n`$, then divide out the eventual fixed gcd in Section <a href="#sec:cubic-normalisation" data-reference-type="ref" data-reference="sec:cubic-normalisation">3.2</a>.

For large $`n`$, $`a_{n+1}\ge a_n^2/2\ge2a_n`$. The terms after $`1/a_{n+1}`$ sum to at most $`2/a_{n+2}\le4/a_{n+1}^2`$, so
``` math
\begin{equation}
\label{eq:tail-estimate}
 x_n=\frac1{a_n}+\frac1{a_{n+1}}+O(a_{n+1}^{-2}),
 \qquad
 \frac{C_{n+1}}{C_n}=\frac{a_n^2}{a_{n+1}}+O(1/a_n).
\end{equation}
```
For the second estimate, the first gives $`a_nx_n=1+O(1/a_n)`$. Use this in
``` math
\frac{C_{n+1}}{C_n}
 =\frac{a_n^2}{a_{n+1}}\,
  \frac{a_{n+1}x_{n+1}}{a_nx_n}.
```
The last factor is $`1+O(1/a_n)`$, and $`a_n^2/a_{n+1}\to1`$, giving the stated additive error. Quadratic growth makes $`1/a_n=o(n^{-k})`$ for every fixed $`k`$, so this error preserves the precision required in the cubic theorem. We keep the original index $`n`$ throughout that proof. Although an eventual recurrence survives removal of a finite prefix, the expression $`1+3/n+o(n^{-3})`$ changes its lower-order terms under an index shift.

<a id="sec:secondaryrate"></a>

# Proof of cubic-rate irrationality

Suppose, towards a contradiction, that the reciprocal sum in Theorem <a href="#res:cubicrate" data-reference-type="ref" data-reference="res:cubicrate">2</a> is rational. Construct $`C_n,D_n`$ as in Section <a href="#sec:transfer" data-reference-type="ref" data-reference="sec:transfer">2</a>. Equation <a href="#eq:tail-estimate" data-reference-type="eqref" data-reference="eq:tail-estimate">[eq:tail-estimate]</a> transfers the rate without changing its precision:
``` math
\begin{equation}
\label{eq:cubic-ratio}
 \frac{C_{n+1}}{C_n}=1+\frac3n+o(n^{-3}).
\end{equation}
```
We first show that $`C_n`$ is eventually a polynomial, using <a href="#eq:cubic-ratio" data-reference-type="eqref" data-reference="eq:cubic-ratio">[eq:cubic-ratio]</a> and integrality. We then apply <a href="#eq:recurrences" data-reference-type="eqref" data-reference="eq:recurrences">[eq:recurrences]</a> to restrict its coefficients.

<a id="sec:cubic-extraction"></a>

## An eventual cubic polynomial

The factor $`1+3/n`$ suggests the cubic $`F_n=n(n+1)(n+2)`$, since $`F_{n+1}/F_n=1+3/n`$. Write <a href="#eq:cubic-ratio" data-reference-type="eqref" data-reference="eq:cubic-ratio">[eq:cubic-ratio]</a> as $`C_{n+1}=(1+3/n+\varepsilon_n)C_n`$, where $`\varepsilon_n=o(n^{-3})`$. Dividing out the exact model gives
``` math
z_n=\frac{C_n}{F_n},\qquad
 \frac{z_{n+1}}{z_n}=1+\frac{\varepsilon_n}{1+3/n}.
```
The logarithmic increments are absolutely summable, with tails $`o(n^{-2})`$. Hence $`z_n`$ tends to some $`A>0`$ and $`z_n-A=o(n^{-2})`$. Multiplying back by $`F_n`$ yields
``` math
C_n=AF_n+\delta_n,\qquad \delta_n=o(n).
```

The estimate $`\delta_n=o(n)`$ alone does not control its differences. Instead, subtracting the recurrences for $`C_n`$ and $`AF_n`$ gives
``` math
\Delta\delta_n=\frac3n\delta_n+\varepsilon_n C_n=o(1),
 \qquad \Delta h_n=h_{n+1}-h_n.
```
Here $`C_n=O(n^3)`$ makes the second term $`o(1)`$. Three more differences still tend to zero and kill the cubic model:
``` math
\Delta^4 C_n=\Delta^3(\Delta\delta_n)\longrightarrow0.
```
The left side is an integer, so it vanishes for all sufficiently large $`n`$. Newton interpolation therefore expresses $`C_n`$ on that tail as a rational polynomial of degree at most three. Its difference from $`AF_n`$ is $`o(n)`$, which permits only a constant term:
``` math
\begin{equation}
\label{eq:cubic-shape}
 C_n=A n(n+1)(n+2)+B,\qquad A\in\mathbb{Q}_{>0},\quad B\in\mathbb{Q}.
\end{equation}
```

The precision matters at the subtraction step. The integer sequence $`F_n+(-1)^n`$ has ratio $`1+3/n+O(n^{-3})`$ and never agrees eventually with a polynomial; its error has an oscillating first difference. This example concerns polynomial extraction alone. It is not asserted to satisfy the denominator recurrence.

<a id="sec:cubic-normalisation"></a>

## Reduction and the constant term

<span id="sec:reduction" label="sec:reduction"></span> We now use the denominator recurrence. Both updates preserve common divisors, so $`G_n=\gcd(C_n,D_n)`$ forms a divisibility chain: $`G_n\mid G_{n+1}`$. For every sufficiently late $`n`$, it divides four consecutive values of $`C_n`$, and hence their third difference $`6A`$. Unlike the vanishing fourth difference used above, this positive third difference bounds the gcd. Thus $`G_n`$ stabilises at a positive integer $`g`$.

We can therefore reduce all sufficiently late fractions by the same factor: put $`u_n=C_n/g`$ and $`v_n=D_n/g`$. The recurrences persist after this division. The following observation describes the resulting coprimality conditions.

<div id="res:reduced" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos243/PaperCompleteR7/Reduction.lean#L16">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-243-reciprocal-tail-rigidity.md#res-reduced-comparator">Comparator</a></p>

**Proposition 3** (persistent coprimality). *Let $`a_n,u_n,v_n`$ be integer sequences with $`u_n>0`$, $`v_n\ge0`$ and $`\gcd(u_n,v_n)=1`$ satisfying
``` math
u_{n+1}=a_nu_n-v_n,\qquad v_{n+1}=a_nv_n.
```
Then $`\gcd(a_n,v_n)=1`$. The $`a_n`$ are pairwise coprime, and $`\gcd(a_i,u_t)=1`$ whenever $`i<t`$.*

</div>

<div class="proof">

*Proof.* A prime dividing both $`a_n`$ and $`v_n`$ would divide $`u_{n+1}`$ and $`v_{n+1}`$, contrary to reducedness. For $`i<t`$, the factor $`a_i`$ divides $`v_t`$. Reducedness gives $`\gcd(a_i,u_t)=1`$, and $`\gcd(a_t,v_t)=1`$ gives $`\gcd(a_i,a_t)=1`$. ◻

</div>

In the cubic case, adjacent numerators are also coprime, since $`\gcd(u_n,u_{n+1})=\gcd(u_n,v_n)=1`$. Write the polynomial for $`u_n`$ as
``` math
\begin{equation}
\label{eq:normal-cubic}
 Q(n)=\frac m6 n(n+1)(n+2)+c.
\end{equation}
```
The third difference $`m=6A/g`$ is a positive integer. Since $`n(n+1)(n+2)/6=\binom{n+2}{3}`$ is an integer, any sufficiently late value $`u_n=Q(n)`$ gives
``` math
c=u_n-m\binom{n+2}{3}\in\mathbb{Z}.
```
Thus $`Q`$ is integer-valued, although its coefficients need not all be integers. If a prime $`\ell`$ divides $`c`$, choose an arbitrarily late $`n\equiv-1\pmod{6\ell}`$. Both $`Q(n)`$ and $`Q(n+1)`$ would be divisible by $`\ell`$, contradicting adjacent coprimality. This also excludes $`c=0`$. Thus
``` math
m\in\mathbb{N}_{>0},\qquad c\in\{1,-1\}.
```

We also need irreducibility. The multipliers $`a_n>1`$ on the reduced tail are pairwise coprime, so infinitely many distinct primes occur among them. Once a prime divides one such $`a_n`$, it divides every later $`v_t`$ and no later $`u_t`$. If the cubic $`Q`$ had a rational root, that root would reduce to a root modulo all but finitely many primes. Choose one of the persistent primes outside those exceptions; a sufficiently late index in the root’s residue class would have $`\ell\mid Q(t)=u_t`$, a contradiction. A cubic is reducible over $`\mathbb{Q}`$ only if it has a rational root. Hence $`Q`$ is irreducible.

Set $`\kappa=m/6`$, $`\eta=6c/m`$, and
``` math
f(T)=T^3-T+\eta,\qquad Q(n)=\kappa f(n+1).
```

<a id="sec:cubic-field"></a>

## A square forced by a zero numerator

A zero numerator modulo a prime eliminates one term of the recurrence. To use this, first eliminate $`v_n`$ from the two exact updates:
``` math
\begin{equation}
\label{eq:three-tail}
 u_{n+2}=(a_n+a_{n+1})u_{n+1}-a_n^2u_n.
\end{equation}
```
Whenever $`u_k\equiv0\pmod\ell`$, it follows that
``` math
-u_{k-1}u_{k+1}\equiv(a_{k-1}u_{k-1})^2\pmod\ell.
```
Thus the negative product of the neighbouring numerators must be a square. Since our numerator is a polynomial, its roots modulo $`\ell`$ tell us exactly where to apply this observation.

Let $`\ell\nmid6m`$ be prime and let $`r\in\mathbb F_\ell`$ satisfy $`f(r)=0`$. The constant $`\eta=6c/m`$ is nonzero modulo $`\ell`$, so $`r\notin\{0,1,-1\}`$. Choose a sufficiently late $`k`$ with $`k+1\equiv r\pmod\ell`$. Then $`u_k=\kappa f(k+1)\equiv0`$, whereas
``` math
f(r-1)=-3r(r-1),\qquad f(r+1)=3r(r+1).
```
Consequently, in $`\mathbb F_\ell`$,
``` math
(a_{k-1}u_{k-1})^2=-u_{k-1}u_{k+1}
   =9\kappa^2r^2(r^2-1).
```
Dividing by the nonzero square $`9\kappa^2r^2`$ gives
``` math
\begin{equation}
\label{eq:all-root-square}
 \ell\nmid6m,\quad r\in\mathbb F_\ell,\quad f(r)=0
 \quad\Longrightarrow\quad r^2-1\in(\mathbb F_\ell^\times)^2
 \qquad(\ell\text{ prime}).
\end{equation}
```
Every root is covered. A prime at which $`f`$ has no root imposes no condition.

Let $`\alpha`$ be a root of $`f`$ and put $`K=\mathbb{Q}(\alpha)`$, a cubic field. We claim that $`\alpha^2-1`$ is a square in $`K`$. A nonsquare would give a quadratic extension in which an automorphism fixes $`\alpha`$ but changes the sign of its square root. Chebotarev realises this behaviour modulo a prime: the reduced $`\alpha`$ lies in the prime field, while the square root does not. That would contradict <a href="#eq:all-root-square" data-reference-type="eqref" data-reference="eq:all-root-square">[eq:all-root-square]</a>.

Here are the details of this passage. Suppose $`\alpha^2-1`$ is not a square in $`K`$, and choose $`\beta`$ with $`\beta^2=\alpha^2-1`$. The nontrivial automorphism of $`K(\beta)/K`$ fixes $`\alpha`$ and sends $`\beta`$ to $`-\beta`$. Extend it to an element $`\sigma\in\operatorname{Gal}(M/\mathbb{Q})`$, where $`M`$ is a Galois closure of $`K(\beta)/\mathbb{Q}`$.

Chebotarev’s density theorem \[stevenhagenlenstra1996, §3, author-version p. 15\] supplies infinitely many unramified rational primes whose Frobenius is conjugate to $`\sigma`$. Choosing a prime of $`M`$ above each of them makes the Frobenius equal to $`\sigma`$ itself. Omit residue characteristic two, primes dividing $`6m`$, and the finitely many primes where $`\alpha`$ or $`\beta`$ is nonintegral or $`\beta`$ reduces to zero. At a remaining prime, Frobenius acts by the $`\ell`$-th power on the residue field, so
``` math
\bar\alpha^\ell=\bar\alpha,\qquad
 \bar\beta^\ell=-\bar\beta\ne\bar\beta.
```
The first equality puts $`r=\bar\alpha`$ in $`\mathbb F_\ell`$ and gives $`f(r)=0`$. The second keeps both roots $`\pm\bar\beta`$ of $`X^2-(r^2-1)`$ outside $`\mathbb F_\ell`$. This contradicts <a href="#eq:all-root-square" data-reference-type="eqref" data-reference="eq:all-root-square">[eq:all-root-square]</a>, which applies to the particular root selected by Frobenius. Removing finitely many primes has left infinitely many choices. Hence there is a $`\beta\in K`$ with $`\beta^2=\alpha^2-1`$.

<a id="sec:cubic-trace"></a>

## Traces in the cubic field

To constrain $`\eta`$, we use the square relation to express $`\alpha`$ through a pair of reciprocal elements in the same cubic field:
``` math
(\alpha+\beta)(\alpha-\beta)=1.
```
Put $`z=\alpha+\beta`$. Then $`z^{-1}=\alpha-\beta`$ and $`2\alpha=z+z^{-1}`$. Since $`z\in K`$ and $`\alpha\in\mathbb{Q}(z)`$, we have $`\mathbb{Q}(z)=K`$. Write the minimal polynomial of $`z`$ as
``` math
p(T)=T^3+bT^2+dT+w,\qquad b,d,w\in\mathbb{Q},\quad w\ne0.
```
The minimal polynomial of $`z^{-1}`$ is the monic reciprocal polynomial
``` math
\frac{T^3p(T^{-1})}{w}
   =T^3+\frac dwT^2+\frac bwT+\frac1w.
```
These two polynomials give the traces of $`z`$ and $`z^{-1}`$ by the same Newton identities. All traces below are from $`K`$ to $`\mathbb{Q}`$.

The cubic for $`\alpha`$ determines its first three traces:
``` math
\operatorname{Tr}(\alpha)=0,\qquad
 \operatorname{Tr}(\alpha^2)=2,\qquad
 \operatorname{Tr}(\alpha^3)=-3\eta.
```
Expressing these same traces through $`z`$ and its reciprocal gives
``` math
\begin{equation}
\label{eq:cubic-traces}
 d=-bw,\qquad b^2+b(w-w^{-1})=1,\qquad
 \eta=\frac{(b^2+1)(w+w^{-1})}{8}.
\end{equation}
```
For completeness, the first equality follows from $`0=2\operatorname{Tr}(\alpha)=-b-d/w`$. After substituting $`d=-bw`$, Newton’s identities give
``` math
\begin{aligned}
 \operatorname{Tr}(z^2)+\operatorname{Tr}(z^{-2})
   &=2b^2+2b(w-w^{-1}),\\
 \operatorname{Tr}(z^3)+\operatorname{Tr}(z^{-3})
   &=-3(b^2+1)(w+w^{-1}).
 \end{aligned}
```
The first line is $`4\operatorname{Tr}(\alpha^2)-6=2`$. The second is $`8\operatorname{Tr}(\alpha^3)=-24\eta`$, because the mixed terms in $`(z+z^{-1})^3`$ have trace $`3\operatorname{Tr}(z+z^{-1})=0`$. These give the other two equalities in <a href="#eq:cubic-traces" data-reference-type="eqref" data-reference="eq:cubic-traces">[eq:cubic-traces]</a>.

Multiplying the middle equation by $`w`$ and bringing all terms to one side gives $`(bw-1)(b+w)=0`$. Write $`w=r/s`$ in lowest terms, with $`r\ne0`$, $`s>0`$. Substituting $`b=-w`$ or $`b=1/w`$ into the last equation and using $`\eta=6c/m`$ gives respectively
``` math
m=\frac{48c\,r s^3}{(r^2+s^2)^2}
 \qquad\text{or}\qquad
 m=\frac{48c\,r^3s}{(r^2+s^2)^2}.
```
Since $`\gcd(r^2+s^2,rs)=1`$ and $`m\in\mathbb{Z}`$, the square $`(r^2+s^2)^2`$ divides $`48`$. Hence $`r^2+s^2`$ is $`1`$, $`2`$ or $`4`$. Both $`r`$ and $`s`$ are nonzero, which leaves only $`2`$: a sum of two nonzero integer squares cannot equal $`1`$ or $`4`$. Thus $`|r|=s=1`$, and positivity of $`m`$ gives $`m=12`$. The only remaining numerators are
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
Completing the square in these two cases gives, in $`\mathbb F_7`$,
``` math
d_1+2=
 \begin{cases}
 (d_0+3)^2 &(c=1),\\
 2(d_0-1)^2 &(c=-1).
 \end{cases}
```
Since $`2=3^2`$ in this field, $`d_1+2`$ must be a square in either case. But $`d_1\in\{3,4\}`$ would give $`d_1+2\in\{5,6\}`$, both nonsquares. The middle zero and its two neighbours supplied $`d_1^2=2`$; the preceding update supplied the incompatible second square. All four numerators are used. Both cubics are excluded, proving Theorem <a href="#res:cubicrate" data-reference-type="ref" data-reference="res:cubicrate">2</a>.

Section 2 of the companion proves positive lower density of disagreement with each rational cubic of this form. That lower bound depends on the orbit and the cubic. For Theorem <a href="#res:cubicrate" data-reference-type="ref" data-reference="res:cubicrate">2</a>, exclusion of eventual equality suffices.

<a id="scope-and-verification"></a>

# Scope and verification

The cubic-rate hypothesis permits the extraction of a cubic polynomial from the integer tail numerator. The assumption $`a_{n+1}/a_n^2\to1`$ in Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a> alone does not supply that rate, so the general eventual-recurrence question remains open. The [long record’s recurrence criteria and further questions](../../../paper/243/erdos243-reciprocal-tail-reasoning-surface.pdf#nameddest=scope-relocated-criteria) retain the other arguments and their precise hypotheses.

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-243-reciprocal-tail-rigidity.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

The [verification section of the long record](../../../paper/243/erdos243-reciprocal-tail-reasoning-surface.pdf#nameddest=scope-verification) gives the formal correspondence, source revisions and reproduction commands.

<div class="thebibliography">

99

P. Erdős and R. L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf), Monogr. Enseign. Math. 28, Geneva, 1980, p. 64. P. Erdős, [*On the irrationality of certain series: problems and results*](https://users.renyi.hu/~p_erdos/1988-22.pdf), in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). P. Stevenhagen and H. W. Lenstra, Jr., [*Chebotarëv and his density theorem*](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1994c/art.pdf), Math. Intelligencer **18** (1996), no. 2, 26–37, doi:[10.1007/BF03027290](https://doi.org/10.1007/BF03027290). Page references are to the linked author version dated 23 March 1995. J. Koizumi, [*Irrationality of the reciprocal sum of doubly exponential sequences*](https://math.colgate.edu/~integers/aa28/aa28.pdf), Integers **26** (2026), Paper No. A28, 17 pp., doi:[10.5281/zenodo.18714404](https://doi.org/10.5281/zenodo.18714404). Locators refer to this published version. T. F. Bloom, [*Erdős Problem \#243*](https://www.erdosproblems.com/243), accessed 28 July 2026.

</div>
