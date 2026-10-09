<a id="erdos-68-factorial-denominator-irrationality"></a>

# Integer Linear Forms for a Factorial Reciprocal Series

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

For $`S=\sum_{n\ge2}(n!-1)^{-1}`$, we classify the multipliers in cancellation forms $`MS+k`$ constructed from finite integer vectors supported on $`n\ge2`$. An integral basis solves cancellation through depth $`D\ge2`$; excluding index one leaves one Diophantine equation. Its coefficient gcd is determined below $`2D^2`$, giving the least positive multiplier and an attaining vector. At $`D=4`$, the minimum is $`1380`$; an attaining form is nonintegral. Irrationality still requires, for each $`q>0`$, a nonintegral form with $`q\mid M`$.

<a id="sec:problem"></a>

# Introduction

Erdős asked whether replacing $`n!`$ by $`n!-1`$ preserves the irrationality of the reciprocal sum \[erdos1988, p. 102\]. The question appears as Problem 68 in Bloom’s catalogue \[bloom\].

<div id="res:problem" class="problem">

**Problem 1** (Erdős Problem #68). Is
``` math
S=\sum_{n\ge2}\frac1{n!-1}
```
irrational?

</div>

The elementary proof that $`e`$ is irrational clears the partial sum by a factorial and bounds the remaining positive tail. Here the first step fails: for $`H_m=\sum_{n=2}^m(n!-1)^{-1}`$, already $`3!H_3=36/5`$. We instead construct forms $`MS+k`$, with $`M,k\in\mathbb Z`$, by cancelling initial weighted sums. If $`S=a/q`$ and $`q\mid M`$, then $`MS+k`$ is integral; proving it nonintegral excludes that denominator.

At depth four, the weight congruences force $`115\mid M`$. Restricting the coefficient support to $`n\ge2`$ strengthens this to $`1380\mid M`$, and every multiple of $`1380`$ occurs. We determine the exact factor at every depth $`D\ge2`$ and construct a vector attaining the least positive multiplier.

First allow a coefficient at index one. Theorem <a href="#res:divisor-channel-coordinates" data-reference-type="ref" data-reference="res:divisor-channel-coordinates">2</a> constructs an integral basis by correcting adjacent factorial differences at proper divisors to isolate each weighted sum. At fixed $`M`$, cancellation determines the lower basis coefficients; removing index one leaves a single equation in the higher coefficients. Theorem <a href="#res:finite-channel-moment-certificate" data-reference-type="ref" data-reference="res:finite-channel-moment-certificate">3</a> reduces its infinite gcd to a calculation below $`2D^2`$. Bézout coefficients then construct an attaining vector. No assumption on the rationality of $`S`$ enters this classification.

Hančl and Tijdeman’s tail-integrality lemma treats factorial series with integer coefficients \[hancl-tijdeman, Lemma 2.1 and the following remark, p. 385\]. Their factorial-scaled partial sums are integers. Here the scaled partial sum need not be integral. Instead, the weight congruences give $`\mathcal R-MS\in\mathbb Z`$ <a href="#eq:integer-linear-form" data-reference-type="eqref" data-reference="eq:integer-linear-form">[eq:integer-linear-form]</a>; the assumption $`S=a/q`$ and $`q\mid M`$ then makes $`\mathcal R`$ integral. Koepf and Schmersau’s factorial-digit criterion \[koepf-schmersau, Example 3.2, p. 121\] is used in the [companion’s digit argument](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r5-digits) to give an equivalent eventual-pattern condition for $`S-e+2`$. Failure of that pattern at arbitrarily large indices also remains unproved.

Section <a href="#sec:depth-four" data-reference-type="ref" data-reference="sec:depth-four">4</a> tests an attaining form; Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">5</a> gives the general nonintegrality test.

<a id="sec:channels"></a>

# An integral basis

We need integer weights congruent to $`n!`$ modulo $`d!-1`$, with $`nW_{d,n-1}=W_{d,n}`$ when $`n\ge2`$ and $`d\nmid n`$. Removing powers of $`d!`$ preserves the residue; the floor exponent gives the required jumps. Put
``` math
W_{d,n}=\frac{n!}{(d!)^{\lfloor n/d\rfloor}}
 \qquad(d\ge2,\ n\ge1).
```
Writing $`n=kd+r`$, $`0\le r<d`$, shows that $`W_{d,n}`$ is $`r!`$ times the multinomial coefficient $`n!/((d!)^k r!)`$. Thus it is an integer, and $`n!=(d!)^kW_{d,n}`$ gives $`W_{d,n}\equiv n!\pmod{d!-1}`$. For example, $`W_{3,4}=4`$ and $`(4!-W_{3,4})/(3!-1)=4`$.

For a finitely supported integer vector $`\lambda=(\lambda_n)_{n\ge1}`$, define the integer linear forms
``` math
M(\lambda)=\sum_n\lambda_n n!,\qquad
 V_d(\lambda)=\sum_n\lambda_nW_{d,n},
```
and let
``` math
\mathcal R(\lambda)=\sum_{d\ge2}\frac{V_d(\lambda)}{d!-1}.
```
Here $`n`$ indexes coefficients and $`d`$ indexes remainder summands. If the support lies in $`n\le N`$, $`N\ge2`$, then $`V_d=M`$ for $`d>N`$. Thus the remainder converges absolutely, and subtracting $`MS`$ leaves only finitely many terms. The weight congruence makes each an integer:
``` math
\begin{equation}
 \mathcal R(\lambda)-M(\lambda)S
 =\sum_{d=2}^N\frac{V_d(\lambda)-M(\lambda)}{d!-1}\in\mathbb Z.
 \label{eq:integer-linear-form}
\end{equation}
```
We solve $`V_2=\cdots=V_D=0`$, allowing either sign of $`M`$. Write $`e_n`$ for the unit vector at index $`n`$. Index one is auxiliary: it makes the basis triangular but introduces no term $`1/(1!-1)`$, since the remainder still starts at $`d=2`$. We impose $`\lambda_1=0`$ in Section <a href="#sec:moments" data-reference-type="ref" data-reference="sec:moments">3</a>.

The identity $`n(n-1)!-n!=0`$ suggests starting with $`T_n=ne_{n-1}-e_n`$. At $`n=2`$, the vector $`U_2=2e_1-e_2`$ has $`V_2=1`$ and every other weighted sum zero. At $`n=4`$, the difference $`T_4=4e_3-e_4`$ has two nonzero weighted sums. One correction suffices:

<div class="center">

| Vector       | $`M`$ | $`V_2`$ | $`V_3`$ | $`V_4`$ |
|:-------------|------:|--------:|--------:|--------:|
| $`T_4`$      | $`0`$ |   $`6`$ |   $`0`$ |  $`23`$ |
| $`6U_2`$     | $`0`$ |   $`6`$ |   $`0`$ |   $`0`$ |
| $`T_4-6U_2`$ | $`0`$ |   $`0`$ |   $`0`$ |  $`23`$ |

</div>

For $`d>4`$ these weighted sums equal $`M=0`$. Thus $`U_4=T_4-6U_2`$ isolates $`V_4=4!-1`$. In general, the unwanted sums occur at proper divisors of $`n`$, whose correcting vectors are already available in an inductive construction.

<div id="res:divisor-channel-coordinates" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos68/PaperCompleteDivisorCoordinates.lean#L260">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-68-factorial-denominator-irrationality.md#res-divisor-channel-coordinates-comparator">Comparator</a></p>

**Theorem 2** (an integer basis with prescribed weighted sums). *Set
``` math
T_n=ne_{n-1}-e_n,\qquad
U_n=T_n-\sum_{\substack{d\mid n\\2\le d<n}}W_{d,n}U_d
\quad(n\ge2).
```
Then
``` math
M(U_n)=0,\qquad V_d(U_n)=(d!-1)\mathbf1_{d=n}.
```
The vectors $`e_1,U_2,U_3,\ldots`$ form an integral basis. Every finite vector has the unique finite expansion
``` math
\begin{equation}
\lambda=M(\lambda)e_1+
\sum_{d\ge2}\frac{V_d(\lambda)-M(\lambda)}{d!-1}U_d.
\label{eq:channel-basis-expansion}
\end{equation}
```*

</div>

<div class="proof">

*Proof.* We have $`M(T_n)=0`$. If $`d\nmid n`$, the floor exponents at $`n-1`$ and $`n`$ agree, so $`nW_{d,n-1}=W_{d,n}`$. If $`d\mid n`$, the exponent increases by one, so $`nW_{d,n-1}=d!W_{d,n}`$. Hence
``` math
V_d(T_n)=(d!-1)W_{d,n}\mathbf1_{d\mid n}.
```
Suppose the asserted identities hold below $`n`$. For each proper divisor $`d`$, subtracting $`W_{d,n}U_d`$ cancels the sum at $`d`$ and changes none of the others. The sum at $`n`$ remains $`n!-1`$, since $`W_{n,n}=1`$. This proves the identities by induction.

For completeness, restrict to indices $`1,\ldots,N`$. The columns $`e_1,T_2,\ldots,T_N`$ form a triangular integer matrix with diagonal $`1,-1,\ldots,-1`$. Replacing each $`T_n`$ by $`U_n`$ subtracts an integer combination of earlier columns, so the second change of basis is triangular with diagonal one. Both matrices have integer inverses: back-substitution divides only by $`1`$ or $`-1`$. Hence $`e_1,U_2,\ldots,U_N`$ is a basis over $`\mathbb Z`$.

In the resulting expansion, applying $`M`$ gives the coefficient of $`e_1`$. If the coefficient of $`U_d`$ is $`c_d`$, applying $`V_d`$ gives $`V_d=M+(d!-1)c_d`$, which proves <a href="#eq:channel-basis-expansion" data-reference-type="eqref" data-reference="eq:channel-basis-expansion">[eq:channel-basis-expansion]</a>. For $`d>N`$ that coefficient is zero because $`V_d=M`$. ◻

</div>

The $`U_d`$-coordinates in <a href="#eq:channel-basis-expansion" data-reference-type="eqref" data-reference="eq:channel-basis-expansion">[eq:channel-basis-expansion]</a> are exactly the integer summands in <a href="#eq:integer-linear-form" data-reference-type="eqref" data-reference="eq:integer-linear-form">[eq:integer-linear-form]</a>. Their sum is therefore $`k`$ in $`\mathcal R=MS+k`$.

For a prime $`p\ge3`$ the divisor sum is empty, and $`U_p=pe_{p-1}-e_p`$. At a composite index the correction terms remove the extra weighted sums. For example,
``` math
\begin{equation}
 U_9=9e_8-e_9-5040e_2+1680e_3.
 \label{res:translator}
\end{equation}
```
Adding $`U_n`$ changes only $`V_n`$ among the weighted sums, preserves $`M`$, and adds one to $`\mathcal R`$. Integer multiples therefore preserve the fractional part.

<a id="sec:moments"></a>

# Possible values of $`M`$

Fix $`D\ge2`$ and solve $`V_2=\cdots=V_D=0`$, allowing index one temporarily. The coordinates in <a href="#eq:channel-basis-expansion" data-reference-type="eqref" data-reference="eq:channel-basis-expansion">[eq:channel-basis-expansion]</a> give
``` math
\begin{equation}
 V_d(\lambda)\equiv M(\lambda)\pmod{d!-1}.
 \label{res:congruence}
\end{equation}
```
It follows that $`M`$ must be divisible by
``` math
L_D=\operatorname{lcm}_{2\le d\le D}(d!-1).
```
This necessary condition is sufficient while index one is allowed: $`L_De_1`$ has every weighted sum equal to $`L_D`$, and subtracting $`L_D/(d!-1)`$ copies of $`U_d`$ sets the $`d`$th sum to zero without changing the others. Thus put
``` math
K_D=L_De_1-\sum_{d=2}^D\frac{L_D}{d!-1}U_d.
```
Uniqueness of the coordinates now gives the complete solution
``` math
\begin{equation}
 V_2=\cdots=V_D=0
 \quad\Longleftrightarrow\quad
 \lambda=tK_D+\sum_{n>D}z_nU_n,\qquad M=tL_D,
 \label{eq:low-channel-classification}
\end{equation}
```
with $`t\in\mathbb Z`$ and finitely many nonzero integers $`z_n`$. The coefficient of $`e_1`$ in <a href="#eq:channel-basis-expansion" data-reference-type="eqref" data-reference="eq:channel-basis-expansion">[eq:channel-basis-expansion]</a> is $`M`$; the original coordinate $`\lambda_1`$ also receives contributions from the $`U_n`$. Write $`a_D=(K_D)_1`$ and $`u_n=(U_n)_1`$. The support restriction is exactly
``` math
\begin{equation}
 ta_D+\sum_{n>D}z_nu_n=0.
 \label{eq:support-equation}
\end{equation}
```
The higher corrections leave cancellation untouched and change the first coordinate by exactly $`g_D\mathbb Z`$, where $`g_D=\gcd\{u_n:n>D\}`$. They can therefore remove $`ta_D`$ precisely when $`g_D\mid ta_D`$. For example, at depth four we shall find $`a_4=-55`$ and $`g_4=60`$. Removing index one then requires $`60\mid55t`$, or $`12\mid t`$; hence $`M=115t`$ must be a multiple of $`1380`$.

In general, the possible values of $`M`$ form the ideal
``` math
\begin{equation}
 \mu_D\mathbb Z,\qquad
 \mu_D=L_D\frac{g_D}{\gcd(g_D,a_D)}.
 \label{eq:attainable-moment-ideal}
\end{equation}
```
Indeed, division by $`\gcd(g_D,a_D)`$ leaves two coprime integers, so $`g_D\mid ta_D`$ holds exactly when $`g_D/\gcd(g_D,a_D)\mid t`$. Bézout’s identity supplies the required finite combination; the next theorem bounds the indices needed. Every vector attaining $`\mu_D`$ has coefficient gcd one, since division by a common factor would give a smaller positive multiplier.

<a id="sec:finite-gcd"></a>

## A finite gcd calculation

The recursion for the first coordinate is
``` math
u_2=2,\qquad
 u_n=-\sum_{\substack{d\mid n\\2\le d<n}}W_{d,n}u_d\quad(n>2).
```
Induction gives $`u_n=0`$ at odd indices and $`u_{2p}=-(2p)!/2^{p-1}\ne0`$ at twice a prime, including $`p=2`$. Choose a prime $`\ell`$ with $`D/2<\ell\le D`$, using Bertrand’s postulate for $`D\ge3`$ and $`\ell=2`$ for $`D=2`$. A finite gcd containing $`u_{2\ell}`$ is positive and divides $`(2\ell)!`$.

The remaining issue is whether later coefficients reduce this gcd. In each recurrence term $`W_{d,n}u_d`$, induction controls $`u_d`$ for $`d>D`$. For $`d\le D`$, unordered block counting gives $`(n/d)!\mid W_{d,n}`$. The cutoff ensures $`n/d\ge2\ell`$, so the weight supplies the factor $`(2\ell)!`$ instead.

<div id="res:finite-channel-moment-certificate" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-68-factorial-denominator-irrationality.md#res-finite-channel-moment-certificate">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-68-factorial-denominator-irrationality.md#res-finite-channel-moment-certificate-comparator">Comparator</a></p>

**Theorem 3** (a finite formula for the gcd). *Choose a prime $`\ell`$ with $`D/2<\ell\le D`$ and put $`H=D(2\ell-1)`$. Then
``` math
g_D=\gcd(u_{D+1},\ldots,u_H),\qquad H<2D^2.
```*

</div>

<div class="proof">

*Proof.* Let $`g=\gcd(u_{D+1},\ldots,u_H)`$. The index $`2\ell`$ belongs to this interval, and $`u_{2\ell}=-(2\ell)!/2^{\ell-1}\ne0`$. Consequently $`g>0`$ and $`g\mid(2\ell)!`$.

We prove $`g\mid u_n`$ for every $`n>D`$ by strong induction. This is true up to $`H`$ by definition. For $`n>H`$, consider a proper divisor $`d\ge2`$ in the recurrence for $`u_n`$. If $`d>D`$, the induction hypothesis gives $`g\mid u_d`$. If $`d\le D`$, put $`k=n/d`$. The choice $`H=D(2\ell-1)`$ ensures $`k\ge2\ell`$. Moreover,
``` math
\frac{W_{d,n}}{k!}=\frac{n!}{(d!)^k k!}\in\mathbb Z:
```
this quotient counts partitions of $`n`$ labelled objects into $`k`$ unordered blocks of size $`d`$. Hence $`(2\ell)!\mid k!\mid W_{d,n}`$, so $`g\mid W_{d,n}`$ in the small-divisor case as well. Every product $`W_{d,n}u_d`$ in the recurrence is therefore divisible by $`g`$.

Thus $`g`$ divides the whole tail. Conversely, every common divisor of the tail divides its finite subfamily $`u_{D+1},\ldots,u_H`$. The two gcds are equal, and $`H\le D(2D-1)<2D^2`$. ◻

</div>

The coefficient at $`2\ell\le2D`$ supplies positivity; the larger cutoff controls the small-divisor weights. The argument does not justify truncation at $`2D`$.

To attain the least positive multiplier, compute integers $`b_n`$ with $`\sum_{n=D+1}^H b_nu_n=g_D`$ by the extended Euclidean algorithm, and put $`h=\gcd(g_D,a_D)`$. Taking
``` math
t=g_D/h,\qquad z_n=-(a_D/h)b_n\quad(D<n\le H)
```
makes $`ta_D+\sum z_nu_n=0`$. Substitution in <a href="#eq:low-channel-classification" data-reference-type="eqref" data-reference="eq:low-channel-classification">[eq:low-channel-classification]</a> therefore gives $`M=\mu_D`$ with support in $`2,\ldots,H`$.

<a id="sec:coordinate-remainder"></a>

## The associated remainder

Fix $`M\in\mu_D\mathbb Z`$ and put $`t=M/L_D`$. For choices of $`z_n`$ satisfying <a href="#eq:support-equation" data-reference-type="eqref" data-reference="eq:support-equation">[eq:support-equation]</a>, the identities $`\mathcal R(e_1)=S`$ and $`\mathcal R(U_n)=1`$ give
``` math
\begin{equation}
 \mathcal R\left(tK_D+\sum_{n>D}z_nU_n\right)
 =tL_D(S-H_D)+\sum_{n>D}z_n,
 \qquad H_D=\sum_{d=2}^D\frac1{d!-1}.
 \label{eq:residual-transparency}
\end{equation}
```
Since $`MH_D\in\mathbb Z`$, the offset from $`MS`$ is $`k=-MH_D+\sum_{n>D}z_n`$; $`\sum z_n`$ alone is the offset from $`M(S-H_D)`$. All choices at fixed $`M`$ therefore have the same fractional part.

<a id="sec:depth-four"></a>

# The least multiplier at depth four

At depth four the recursion gives
``` math
L_4=115,\qquad
 K_4=-55e_1+16e_2+3e_3+5e_4,\qquad a_4=-55.
```
Take $`\ell=3`$ in Theorem <a href="#res:finite-channel-moment-certificate" data-reference-type="ref" data-reference="res:finite-channel-moment-certificate">3</a>, so that $`H=20`$. Since $`u_6=-180`$, $`u_8=-4200`$ and $`23u_6-u_8=60`$, we have $`g_4\mid60`$. For the converse,
``` math
\begin{equation}
 \operatorname{lcm}(1,\ldots,n)\mid u_n
 \label{eq:channel-lcm-envelope}
\end{equation}
```
gives $`60\mid u_n`$ for every $`n>4`$, hence $`60\mid g_4`$. To prove <a href="#eq:channel-lcm-envelope" data-reference-type="eqref" data-reference="eq:channel-lcm-envelope">[eq:channel-lcm-envelope]</a>, put $`\Lambda_n=\operatorname{lcm}(1,\ldots,n)`$. For a prime $`r`$, write $`v_r`$ for its valuation. If $`d\mid n`$, Legendre’s formula gives
``` math
v_r(W_{d,n})=\sum_{j\ge1}\left(
 \left\lfloor\frac n{r^j}\right\rfloor
 -\frac nd\left\lfloor\frac d{r^j}\right\rfloor\right)
 \ge v_r(\Lambda_n)-v_r(\Lambda_d).
```
Each summand is nonnegative, and each power $`d<r^j\le n`$ contributes at least one. Hence $`\Lambda_n\mid W_{d,n}\Lambda_d`$, and induction in the recurrence, starting from $`u_2=2`$, proves the assertion. Thus $`g_4=60`$, and <a href="#eq:attainable-moment-ideal" data-reference-type="eqref" data-reference="eq:attainable-moment-ideal">[eq:attainable-moment-ideal]</a> gives
``` math
\mu_4=115\frac{60}{\gcd(60,55)}=1380.
```

To attain $`M=1380`$, take $`t=12`$ in <a href="#eq:support-equation" data-reference-type="eqref" data-reference="eq:support-equation">[eq:support-equation]</a>. The choice $`z_6=-27`$, $`z_8=1`$ works because
``` math
12(-55)-27(-180)-4200=0.
```
The vector $`12K_4-27U_6+U_8`$ therefore has no index-one coefficient and cancels $`V_2,V_3,V_4`$. To remove its coefficients at indices four and seven, add $`-26U_5+8U_7`$. These corrections still cancel through four and do not restore index one, since $`u_5=u_7=0`$. Thus
``` math
\lambda=12K_4-26U_5-27U_6+8U_7+U_8,
```
which expands to
``` math
\begin{equation}
 \lambda=1482e_2-784e_3-136e_5+83e_6-e_8,
 \qquad (M,V_2,V_3,V_4)=(1380,0,0,0).
 \label{eq:depth-four-short-vector}
\end{equation}
```
Table <a href="#tab:depth-four" data-reference-type="ref" data-reference="tab:depth-four">1</a> verifies all four sums directly.

<div id="tab:depth-four">

<table>
<caption>The depth-four checks: multiply each of the last four columns by <span class="math inline"><em>λ</em><sub><em>n</em></sub></span> and sum to obtain the last row.</caption>
<thead>
<tr>
<th style="text-align: right;"><span class="math inline"><em>n</em></span></th>
<th style="text-align: right;"><span class="math inline"><em>λ</em><sub><em>n</em></sub></span></th>
<th style="text-align: right;"><span class="math inline"><em>n</em>!</span></th>
<th style="text-align: right;"><span class="math inline"><em>W</em><sub>2, <em>n</em></sub></span></th>
<th style="text-align: right;"><span class="math inline"><em>W</em><sub>3, <em>n</em></sub></span></th>
<th style="text-align: right;"><span class="math inline"><em>W</em><sub>4, <em>n</em></sub></span></th>
</tr>
</thead>
<tbody>
<tr>
<td style="text-align: right;">2</td>
<td style="text-align: right;">1482</td>
<td style="text-align: right;">2</td>
<td style="text-align: right;">1</td>
<td style="text-align: right;">2</td>
<td style="text-align: right;">2</td>
</tr>
<tr>
<td style="text-align: right;">3</td>
<td style="text-align: right;">-784</td>
<td style="text-align: right;">6</td>
<td style="text-align: right;">3</td>
<td style="text-align: right;">1</td>
<td style="text-align: right;">6</td>
</tr>
<tr>
<td style="text-align: right;">5</td>
<td style="text-align: right;">-136</td>
<td style="text-align: right;">120</td>
<td style="text-align: right;">30</td>
<td style="text-align: right;">20</td>
<td style="text-align: right;">5</td>
</tr>
<tr>
<td style="text-align: right;">6</td>
<td style="text-align: right;">83</td>
<td style="text-align: right;">720</td>
<td style="text-align: right;">90</td>
<td style="text-align: right;">20</td>
<td style="text-align: right;">30</td>
</tr>
<tr>
<td style="text-align: right;">8</td>
<td style="text-align: right;">-1</td>
<td style="text-align: right;">40320</td>
<td style="text-align: right;">2520</td>
<td style="text-align: right;">1120</td>
<td style="text-align: right;">70</td>
</tr>
<tr>
<td colspan="2" style="text-align: left;">Weighted totals</td>
<td style="text-align: right;"><span class="math inline">1380</span></td>
<td style="text-align: right;"><span class="math inline">0</span></td>
<td style="text-align: right;"><span class="math inline">0</span></td>
<td style="text-align: right;"><span class="math inline">0</span></td>
</tr>
</tbody>
</table>

</div>

The basis coordinates give the offset $`-26-27+8+1=-44`$ in <a href="#eq:residual-transparency" data-reference-type="eqref" data-reference="eq:residual-transparency">[eq:residual-transparency]</a>. Since $`H_4=143/115`$, the original linear form is
``` math
\mathcal R(\lambda)=1380(S-H_4)-44=1380S-1760.
```
For the remainder estimate, the inequality $`(n+1)!-1>(n+1)(n!-1)`$ gives the geometric bound
``` math
\begin{equation}
 0<S-H_N<\frac{N+2}{(N+1)((N+1)!-1)}
          <\frac{2}{(N+1)!-1}\qquad(N\ge2).
 \label{eq:series-tail-bound}
\end{equation}
```
The majorant starts with $`1/((N+1)!-1)`$ and has ratio $`1/(N+2)`$.

Exact rational arithmetic gives
``` math
-31+\frac45
 <1380\sum_{d=5}^{8}\frac1{d!-1}-44
 <-31+\frac56,
 \qquad \frac{2\cdot1380}{9!-1}<\frac1{100}.
```
The omitted contribution to $`\mathcal R`$ is positive and less than $`1/100`$, so $`-31<\mathcal R(\lambda)<-30`$. If $`S=a/q`$ with $`q\mid1380`$, <a href="#eq:integer-linear-form" data-reference-type="eqref" data-reference="eq:integer-linear-form">[eq:integer-linear-form]</a> would make this remainder an integer. Every divisor of $`1380`$ is therefore excluded.

The [depth-six calculation](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r15-depth-six) gives $`\mu_6=24L_6`$: the extra factor need not equal $`12`$. The companion also gives a [dual congruence, support bounds and coefficient-norm refinements](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r5-depth-refinements). Least multiplier, least support size and least coefficient norm are distinct problems; <a href="#eq:attainable-moment-ideal" data-reference-type="eqref" data-reference="eq:attainable-moment-ideal">[eq:attainable-moment-ideal]</a> settles only the first.

<a id="sec:open"></a>

# Nonintegrality of the remainder

<span id="sec:plateau" label="sec:plateau"></span> <span id="r12-short-gap"></span>

Fix a vector with $`V_2=\cdots=V_D=0`$ and $`M>0`$, and choose any cutoff $`N\ge D`$ at or beyond its support. Separate the signed finite sum from the positive tail:
``` math
A_N=\sum_{d=D+1}^N\frac{V_d(\lambda)}{d!-1},\qquad
 \mathcal R(\lambda)=A_N+M(S-H_N).
```
The remainder exceeds $`A_N`$. By <a href="#eq:series-tail-bound" data-reference-type="eqref" data-reference="eq:series-tail-bound">[eq:series-tail-bound]</a>, it lies below the least integer strictly above $`A_N`$ whenever
``` math
\begin{equation}
 \frac{2M}{(N+1)!-1}<\lfloor A_N\rfloor+1-A_N.
 \label{eq:signed-block-gap}
\end{equation}
```
Then $`\lfloor A_N\rfloor<\mathcal R(\lambda)<\lfloor A_N\rfloor+1`$, excluding every denominator dividing $`M`$. The strict successor matters: at an integral $`A_N`$ the gap is one, whereas just below an integer it can be arbitrarily small. Failure of the comparison is inconclusive.

At depth two, fix $`\lambda=-6e_2+e_4`$, with $`M=12`$, and vary only the cutoff. At $`N=4`$, its finite part $`A_4=-239/115`$ lies just below $`-2`$, and its gap $`9/115`$ is smaller than the bound $`24/119`$. At $`N=5`$, the finite part $`A_5=-27061/13685`$ has crossed $`-2`$: the next integer is now $`-1`$, and the gap $`13376/13685`$ exceeds $`24/719`$. For any fixed vector with $`M>0`$, $`A_N`$ increases to $`\mathcal R`$. If $`\mathcal R`$ is nonintegral, the gap tends to a positive number and the test eventually succeeds. If $`\mathcal R`$ is integral, the eventual gap equals the omitted tail, so the strict upper-bound test fails. Changing the cutoff detects nonintegrality; it neither creates it nor changes $`M`$. Coefficient changes at fixed $`M`$ preserve nonintegrality by <a href="#eq:residual-transparency" data-reference-type="eqref" data-reference="eq:residual-transparency">[eq:residual-transparency]</a>.

To exclude every denominator, $`M`$ must vary. The [companion’s progression construction](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r5-progression) adds size control: polynomial root conditions give primitive vectors (coefficient gcd one) with $`0<M<N!`$, where $`N`$ is their largest supported index. Every fixed $`q`$ divides their multipliers for all sufficiently large $`N`$. The tail at that endpoint is below $`2/N`$, but the next-integer gap may shrink too. For each $`q>0`$, one still needs a vector with $`q\mid M`$ and a cutoff satisfying <a href="#eq:signed-block-gap" data-reference-type="eqref" data-reference="eq:signed-block-gap">[eq:signed-block-gap]</a>; the cutoff may exceed its support endpoint. No minimal-support assertion is made.

The companion treats the [equivalent carry condition](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r5-carry) and the [complementary-denominator tail inequality](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r5-complement). It also records two larger finite computations: a non-unit carry at $`m=300000`$ excludes every $`q\mid299999!`$, and a continued-fraction enclosure excludes every $`q<2^{39990}`$. Both computations were performed outside Lean; their [algorithms, exact outputs and scope](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r12-finite) are given there. The factorial-divisibility exclusion does not exclude all denominators with only small prime factors, whose exponents may be larger. Neither finite restriction establishes the required condition at arbitrarily large indices.

<a id="app:sources"></a>

# Verification

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-68-factorial-denominator-irrationality.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

The integral-basis theorem and finite gcd formula have recorded exact Lean bindings. The [companion source concordance](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r12-short-sources) identifies their declarations and the theorem on the possible values of $`M`$. Its large finite computations are separate from these kernel proofs.

<a id="acknowledgements"></a>

# Acknowledgements

An AI research pass supplied by Will Cook derived the depth-four dual congruence and shorter vectors from the weighted linear forms and the classification of their possible coefficients $`M`$ developed earlier here. OpenAI Codex checked and integrated them; a separate AI pass reviewed the proof.

<div class="thebibliography">

99

Paul Erdős. [On the irrationality of certain series: problems and results](https://doi.org/10.1017/CBO9780511897184.009). In Alan Baker (ed.), *New Advances in Transcendence Theory*, Cambridge University Press (1988), pp. 102–109.

Thomas F. Bloom. [Erdős Problem \#68](https://www.erdosproblems.com/68). Online resource (2026). Historical access: 28 July 2026; present-page status not reverified.

Wolfram Koepf and Dieter Schmersau. [Irrationality of certain infinite series II](https://doi.org/10.1524/anly.2011.1094). *Analysis* **31** (2011), 117–124.

Jaroslav Hančl and Robert Tijdeman. [On the irrationality of factorial series](https://doi.org/10.4064/aa118-4-5). *Acta Arithmetica* **118** (4) (2005), 383–401.

</div>
