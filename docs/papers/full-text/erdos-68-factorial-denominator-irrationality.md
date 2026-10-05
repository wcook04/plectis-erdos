<a id="erdos-68-factorial-denominator-irrationality"></a>

# Integer Linear Forms for a Factorial Reciprocal Series

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

For $`S=\sum_{n\ge2}(n!-1)^{-1}`$, we determine the integers $`M`$ that occur in finitely supported cancellation forms $`MS+k`$. An integral basis reduces cancellation through $`D`$ and exclusion of index one to a single Diophantine equation. Its coefficient gcd is computable below $`2D^2`$, giving the least positive $`M`$ and a vector attaining it. At $`D=4`$ this minimum is $`1380`$, and the resulting form is nonintegral. Irrationality still requires, for each $`q>0`$, a nonintegral form with $`q\mid M`$.

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

Even these cancellation equations impose more than the expected common-denominator condition. Cancelling the weighted sums indexed by $`2,3,4`$ forces $`115\mid M`$, but a vector supported on indices $`n\ge2`$ requires $`1380\mid M`$. We determine the exact additional factor at every depth $`D`$, and construct a vector attaining the least positive value of $`M`$.

The proof has two steps. Adjacent factorial differences, corrected at proper divisors, give an integral basis that isolates each weighted sum (Theorem <a href="#res:divisor-channel-coordinates" data-reference-type="ref" data-reference="res:divisor-channel-coordinates">2</a>). Temporarily allowing index one makes this basis triangular; removing that coordinate leaves one Diophantine equation. Its gcd initially involves infinitely many coefficients. Theorem <a href="#res:finite-channel-moment-certificate" data-reference-type="ref" data-reference="res:finite-channel-moment-certificate">3</a> reduces it to a specified finite interval, not an observed stabilization.

The classification is independent of rationality. The attaining example $`M=1380`$ also passes a separate nonintegrality test. For an irrationality proof, however, the divisibility $`q\mid M`$ and nonintegrality must hold for the same vector, for every $`q>0`$. The companion’s [progression construction](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r5-progression) provides the divisibility; its nonintegrality remains unproved.

Hančl and Tijdeman’s tail-integrality lemma treats factorial series with integer coefficients \[hancl-tijdeman, Lemma 2.1 and the following remark, p. 385\]. Their factorial-scaled partial sums are integers. Here the scaled partial sum need not be integral. Instead, the weight congruences give $`\mathcal R-MS\in\mathbb Z`$ <a href="#eq:integer-linear-form" data-reference-type="eqref" data-reference="eq:integer-linear-form">[eq:integer-linear-form]</a>; the assumption $`S=a/q`$ and $`q\mid M`$ then makes $`\mathcal R`$ integral. Koepf and Schmersau’s factorial-digit criterion \[koepf-schmersau, Example 3.2, p. 121\] is used in the [companion’s digit argument](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r5-digits) to give an equivalent eventual-pattern condition for $`S-e+2`$. Failure of that pattern at arbitrarily large indices also remains unproved.

Sections <a href="#sec:channels" data-reference-type="ref" data-reference="sec:channels">2</a>–<a href="#sec:moments" data-reference-type="ref" data-reference="sec:moments">3</a> prove the classification; Section <a href="#sec:depth-four" data-reference-type="ref" data-reference="sec:depth-four">4</a> constructs and tests the least-$`M`$ example. Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">5</a> separates the remaining nonintegrality question from the freedoms in that construction.

<a id="sec:channels"></a>

# An integral basis

At the denominator $`d!-1`$, we replace $`n!`$ by an integer with the same residue. Dividing by $`d!`$ preserves that residue; the exponent below is chosen to make adjacent differences vanish except at multiples of $`d`$. Put
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
Here $`n`$ indexes coefficients and $`d`$ indexes remainder summands. If the support lies in $`n\le N`$, $`N\ge2`$, then $`V_d=M`$ for $`d>N`$. Thus the infinite tail agrees with that of $`MS`$. The remainder converges absolutely, and each of the finitely many termwise differences is an integer:
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
Since $`M(U_n)=0`$ and $`\mathcal R(U_n)=1`$, adding an integer multiple of $`U_n`$ changes only $`V_n`$ among the weighted sums and changes the remainder by an integer. It therefore preserves both $`M`$ and the fractional part of the remainder.

<a id="sec:moments"></a>

# Possible values of $`M`$

Fix $`D\ge2`$. We first solve $`V_2=\cdots=V_D=0`$ with index one allowed, and then impose the support restriction $`\lambda_1=0`$. The weight congruence, or the coordinates in <a href="#eq:channel-basis-expansion" data-reference-type="eqref" data-reference="eq:channel-basis-expansion">[eq:channel-basis-expansion]</a>, gives
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
This necessary condition is sufficient while index one is allowed: $`L_De_1`$ has every weighted sum equal to $`L_D`$, and subtracting $`L_D/(d!-1)`$ copies of $`U_d`$ sets the $`d`$th sum to zero. Thus put
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
with $`t\in\mathbb Z`$ and finitely many nonzero integers $`z_n`$. Here $`t`$ fixes $`M`$ and the coefficients of $`U_2,\ldots,U_D`$. The remaining basis coefficients $`z_n`$ are free until we impose $`\lambda_1=0`$.

It remains to remove index one. Write $`a_D`$ for its coefficient in $`K_D`$, and $`u_n`$ for its coefficient in $`U_n`$. All other coordinates already lie in the permitted range $`n\ge2`$, so the only remaining equation is
``` math
\begin{equation}
 ta_D+\sum_{n>D}z_nu_n=0.
 \label{eq:support-equation}
\end{equation}
```
The higher corrections can change this coefficient by exactly the integer multiples of $`g_D=\gcd\{u_n:n>D\}`$. Thus the equation is soluble precisely when $`g_D\mid ta_D`$. For example, at depth four we shall find $`a_4=-55`$ and $`g_4=60`$. Removing index one then requires $`60\mid55t`$, or $`12\mid t`$; hence $`M=115t`$ must be a multiple of $`1380`$.

In general, the possible values of $`M`$ form the ideal
``` math
\begin{equation}
 \mu_D\mathbb Z,\qquad
 \mu_D=L_D\frac{g_D}{\gcd(g_D,a_D)}.
 \label{eq:attainable-moment-ideal}
\end{equation}
```
Indeed, division by $`\gcd(g_D,a_D)`$ leaves two coprime integers, so $`g_D\mid ta_D`$ holds exactly when $`g_D/\gcd(g_D,a_D)\mid t`$. Bézout’s identity supplies the required finite combination of the $`u_n`$. The next theorem proves $`g_D>0`$ and bounds the indices needed for this combination. A vector attaining the least positive value $`\mu_D`$ is primitive, since dividing its coefficients by a common factor would give a smaller positive value of $`M`$.

<a id="sec:finite-gcd"></a>

## A finite gcd calculation

The recursion for the first coordinate is
``` math
u_2=2,\qquad
 u_n=-\sum_{\substack{d\mid n\\2\le d<n}}W_{d,n}u_d\quad(n>2).
```
Induction gives $`u_n=0`$ at odd indices and $`u_{2p}=-(2p)!/2^{p-1}\ne0`$ at twice a prime, including $`p=2`$. Choose a prime $`\ell`$ with $`D/2<\ell\le D`$. A finite gcd that includes $`u_{2\ell}`$ is positive and divides $`(2\ell)!`$.

The issue is to prove that this gcd divides every later coefficient. In the recurrence, a proper divisor $`d>D`$ passes divisibility through $`u_d`$ by induction. For $`d\le D`$, divisibility must instead come from the weight: once $`n/d\ge2\ell`$, the block-counting formula below makes $`(2\ell)!\mid W_{d,n}`$. The cutoff ensures this for every small divisor.

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

Bertrand’s postulate supplies the prime $`\ell`$ when $`D\ge3`$; for $`D=2`$ take $`\ell=2`$. Merely including the nonzero coefficient at $`2\ell`$ is not enough: the cutoff must also control every later small-divisor weight. A truncation at $`2D`$ is not justified by this argument.

To attain the least positive multiplier, compute integers $`b_n`$ with $`\sum_{n=D+1}^H b_nu_n=g_D`$ by the extended Euclidean algorithm, and put $`h=\gcd(g_D,a_D)`$. Taking
``` math
t=g_D/h,\qquad z_n=-(a_D/h)b_n\quad(D<n\le H)
```
makes $`ta_D+\sum z_nu_n=0`$. Substitution in <a href="#eq:low-channel-classification" data-reference-type="eqref" data-reference="eq:low-channel-classification">[eq:low-channel-classification]</a> therefore produces a vector with $`M=\mu_D`$. Minimising its support or its coefficient norm is a separate problem.

<a id="sec:coordinate-remainder"></a>

## The associated remainder

Fix $`M\in\mu_D\mathbb Z`$ and put $`t=M/L_D`$. The choices of $`z_n`$ satisfying <a href="#eq:support-equation" data-reference-type="eqref" data-reference="eq:support-equation">[eq:support-equation]</a> change the remainder only by an integer: $`\mathcal R(e_1)=S`$ and $`\mathcal R(U_n)=1`$ give
``` math
\begin{equation}
 \mathcal R\left(tK_D+\sum_{n>D}z_nU_n\right)
 =tL_D(S-H_D)+\sum_{n>D}z_n,
 \qquad H_D=\sum_{d=2}^D\frac1{d!-1}.
 \label{eq:residual-transparency}
\end{equation}
```
Since $`M=tL_D`$ clears the denominators of $`H_D`$, the integer in $`\mathcal R=MS+k`$ is $`k=-MH_D+\sum_{n>D}z_n`$. Thus the sum of the higher basis coefficients is the offset from $`M(S-H_D)`$, not from $`MS`$.

<a id="sec:depth-four"></a>

# An example attaining the minimum

At depth four the recursion gives
``` math
L_4=115,\qquad
 K_4=-55e_1+16e_2+3e_3+5e_4,\qquad a_4=-55.
```
Take $`\ell=3`$ in Theorem <a href="#res:finite-channel-moment-certificate" data-reference-type="ref" data-reference="res:finite-channel-moment-certificate">3</a>, so that $`H=20`$. The coefficients in this finite interval have gcd $`60`$. There is a useful short proof: $`u_6=-180`$, $`u_8=-4200`$ and $`23u_6-u_8=60`$, while
``` math
\begin{equation}
 \operatorname{lcm}(1,\ldots,n)\mid u_n
 \label{eq:channel-lcm-envelope}
\end{equation}
```
gives the reverse divisibility for every $`n>4`$. To prove <a href="#eq:channel-lcm-envelope" data-reference-type="eqref" data-reference="eq:channel-lcm-envelope">[eq:channel-lcm-envelope]</a>, put $`\Lambda_n=\operatorname{lcm}(1,\ldots,n)`$. For a prime $`r`$, write $`v_r`$ for its valuation. If $`d\mid n`$, Legendre’s formula gives
``` math
v_r(W_{d,n})=\sum_{j\ge1}\left(
 \left\lfloor\frac n{r^j}\right\rfloor
 -\frac nd\left\lfloor\frac d{r^j}\right\rfloor\right)
 \ge v_r(\Lambda_n)-v_r(\Lambda_d).
```
Each summand is nonnegative, and each power $`d<r^j\le n`$ contributes at least one. Hence $`\Lambda_n\mid W_{d,n}\Lambda_d`$, and induction in the recurrence, starting from $`u_2=2`$, proves the assertion. Formula <a href="#eq:attainable-moment-ideal" data-reference-type="eqref" data-reference="eq:attainable-moment-ideal">[eq:attainable-moment-ideal]</a> now gives
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
<caption>The depth-four vector and its checks. To obtain the last row, multiply each of the final four columns by <span class="math inline"><em>λ</em><sub><em>n</em></sub></span> before summing.</caption>
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

The companion gives an [alternative dual congruence and support and coefficient-norm refinements](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r5-depth-refinements). Minimising $`M`$, the number of supported indices, and the coefficient norm are distinct problems; only the first is settled by <a href="#eq:attainable-moment-ideal" data-reference-type="eqref" data-reference="eq:attainable-moment-ideal">[eq:attainable-moment-ideal]</a>.

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
Then $`\lfloor A_N\rfloor<\mathcal R(\lambda)<\lfloor A_N\rfloor+1`$, excluding every denominator dividing $`M`$. The strict successor is essential: the gap is one at an integer, but can be arbitrarily small just below one. Failure of the comparison is inconclusive.

First keep the vector fixed and increase only the cutoff. The vector $`-6e_2+e_4`$ has $`M=12`$. At $`N=4`$, its finite part $`A_4=-239/115`$ lies just below $`-2`$, and its gap $`9/115`$ is smaller than the bound $`24/119`$. At $`N=5`$, the finite part $`A_5=-27061/13685`$ has crossed $`-2`$: the next integer is now $`-1`$, and the gap $`13376/13685`$ exceeds $`24/719`$. For any fixed vector with $`M>0`$, $`A_N`$ increases to $`\mathcal R`$. If $`\mathcal R`$ is nonintegral, the gap tends to a positive number and the test eventually succeeds. If $`\mathcal R`$ is integral, the eventual gap equals the omitted tail, so the strict upper-bound test fails. Thus moving the cutoff detects nonintegrality; it does not create it or change the divisors of $`M`$ that are excluded.

Nor can a change of coefficients at fixed $`M`$ create nonintegrality: by <a href="#eq:integer-linear-form" data-reference-type="eqref" data-reference="eq:integer-linear-form">[eq:integer-linear-form]</a>, it changes the remainder only by an integer. The $`U_n`$ corrections simplify support and weighted sums, not the fractional part.

To exclude every denominator, $`M`$ must vary. The [companion’s progression construction](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r5-progression) turns cancellation into polynomial root conditions. It gives primitive vectors (their coefficients have gcd one) with $`0<M<N!`$ and multipliers eventually divisible by every fixed $`q`$. At the support endpoint the tail is less than $`2/N`$, but the next-integer gap may shrink too. The missing step is therefore one comparison for the same vector: for each $`q>0`$, find $`q\mid M`$ and a cutoff satisfying <a href="#eq:signed-block-gap" data-reference-type="eqref" data-reference="eq:signed-block-gap">[eq:signed-block-gap]</a>. Neither divisibility nor a vanishing tail bound supplies that comparison. No minimal-support assertion is made for this family.

The companion treats the [equivalent carry condition](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r5-carry) and the [complementary-denominator tail inequality](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r5-complement). It also records two larger finite computations: a non-unit carry at $`m=300000`$ excludes every $`q\mid299999!`$, and a continued-fraction enclosure excludes every $`q<2^{39990}`$. Both computations were performed outside Lean; their [algorithms, exact outputs and scope](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r12-finite) are given there. The factorial-divisibility exclusion does not exclude all denominators with only small prime factors, whose exponents may be larger. Neither finite restriction establishes the required condition at arbitrarily large indices.

<a id="app:sources"></a>

# Verification

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-68-factorial-denominator-irrationality.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

The integral-basis theorem and finite gcd formula have recorded exact Lean bindings. The [companion source concordance](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r12-short-sources) identifies their declarations and the theorem on the possible values of $`M`$. Its large finite computations are separate from these kernel proofs.

<a id="acknowledgements"></a>

# Acknowledgements

The author thanks Wouter van Doorn for advice on exposition: explaining notation when it first appears, avoiding private terminology, and saying how restrictive a conditional hypothesis is. His advice concerned the writing of another note; he has not reviewed the mathematics of this paper. An AI research pass supplied by Will Cook derived the depth-four dual congruence and shorter vectors from the weighted linear forms and the classification of their possible coefficients $`M`$ developed earlier here. OpenAI Codex checked and integrated them; a separate AI pass reviewed the proof.

<div class="thebibliography">

99

Paul Erdős. [On the irrationality of certain series: problems and results](https://doi.org/10.1017/CBO9780511897184.009). In Alan Baker (ed.), *New Advances in Transcendence Theory*, Cambridge University Press (1988), pp. 102–109.

Thomas F. Bloom. [Erdős Problem \#68](https://www.erdosproblems.com/68). Online resource (2026). Historical access: 28 July 2026; present-page status not reverified.

Wolfram Koepf and Dieter Schmersau. [Irrationality of certain infinite series II](https://doi.org/10.1524/anly.2011.1094). *Analysis* **31** (2011), 117–124.

Jaroslav Hančl and Robert Tijdeman. [On the irrationality of factorial series](https://doi.org/10.4064/aa118-4-5). *Acta Arithmetica* **118** (4) (2005), 383–401.

</div>
