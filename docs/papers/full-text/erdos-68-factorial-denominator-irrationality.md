<a id="erdos-68-factorial-denominator-irrationality"></a>

# Integer Linear Forms for a Factorial Reciprocal Series

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We construct an integral basis that diagonalises factorial-weighted cancellation equations. Restricting the support to indices at least two leaves one Diophantine equation, whose finite gcd determines all attainable factorial moments. At depth four the least positive moment is $`1380`$. We also construct primitive vectors on arithmetic progressions with moments eventually divisible by every fixed positive integer. Their remainders are integer linear forms in $`S=\sum_{n\ge2}(n!-1)^{-1}`$; the nonintegrality needed to deduce the irrationality of $`S`$ remains open.

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

The usual proof for $`e`$ compares a factorial multiple of the tail with an integer. Here the last denominator of a partial sum is already coprime to the corresponding factorial, so that multiplier leaves a fractional part in the prefix. We instead form integer combinations of factorial weights chosen to preserve the fractional parts over $`d!-1`$. Cancelling the weights for $`2\le d\le D`$ then gives a linear form in $`1`$ and $`S`$ whose first $`D-1`$ weighted summands vanish.

Our main result is an integral basis for these coefficient vectors (Theorem <a href="#res:divisor-channel-coordinates" data-reference-type="ref" data-reference="res:divisor-channel-coordinates">2</a>). An adjacent factorial difference affects only the divisors of its index. By eliminating its proper-divisor contributions in increasing order, we obtain a vector that adjusts just one weighted sum. The resulting triangular change of basis is invertible over $`\mathbb Z`$, and hence describes every finite integer solution. We initially allow a coefficient at index one. Setting it to zero imposes a single Diophantine equation, for which Theorem <a href="#res:finite-channel-moment-certificate" data-reference-type="ref" data-reference="res:finite-channel-moment-certificate">3</a> supplies a finite gcd. The construction and classification require no assumption on $`S`$.

At depth four the least positive factorial moment is $`1380`$, and a vector attaining it has a remainder strictly between $`-31`$ and $`-30`$. This excludes the divisors of $`1380`$ as possible denominators of $`S`$. To obtain an irrationality proof, we would need such exclusions for every positive denominator. A separate construction on arithmetic progressions gives primitive vectors whose moments have the required divisibility, but the nonintegrality of their corresponding remainders is still to be proved.

For the comparison with an integer, we use the classical factorial-series viewpoint. Hančl and Tijdeman’s tail integrality lemma \[hancl-tijdeman, Lemma 2.1 and the following remark, p. 385\] underlies the comparison with an integer. Cantor’s expansion criterion, as presented by Galambos \[galambos1976, Ch. II, §2.1\] and illustrated by Koepf and Schmersau \[koepf-schmersau, Example 3.2\], explains the carry and digit criteria below. For this series, the required departures from an eventual digit pattern remain unproved.

Sections <a href="#sec:channels" data-reference-type="ref" data-reference="sec:channels">2</a>–<a href="#sec:compressed-kernel" data-reference-type="ref" data-reference="sec:compressed-kernel">5</a> develop the coefficient construction. Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">6</a> states the required real comparison, and Section <a href="#sec:finite" data-reference-type="ref" data-reference="sec:finite">7</a> gives the carry criterion and two recorded finite exclusions. The appendices treat reduced denominators and the factorial digits of $`S-e+2`$.

<a id="sec:channels"></a>

# An integral basis

We seek integral weights congruent to $`n!`$ modulo $`d!-1`$. For integers $`d\ge2`$ and $`n\ge1`$, take
``` math
W_{d,n}=\frac{n!}{(d!)^{\lfloor n/d\rfloor}}.
```
Write $`n=kd+r`$, where $`0\le r<d`$. The quotient is $`r!`$ times the multinomial coefficient $`n!/((d!)^k r!)`$, and is therefore an integer. Since $`n!=(d!)^kW_{d,n}`$ and $`d!\equiv1\pmod{d!-1}`$, it also satisfies $`W_{d,n}\equiv n!\pmod{d!-1}`$. Thus replacing $`n!`$ by $`W_{d,n}`$ in a numerator changes the fraction with denominator $`d!-1`$ by an integer. For instance, $`W_{3,4}=4`$, and the change is $`(24-4)/5=4`$.

For a finitely supported integer vector $`\lambda=(\lambda_n)_{n\ge1}`$, we define its factorial moment and weighted sums by
``` math
M(\lambda)=\sum_n\lambda_n n!,\qquad
 V_d(\lambda)=\sum_n\lambda_nW_{d,n},
```
and let
``` math
\mathcal R(\lambda)=\sum_{d\ge2}\frac{V_d(\lambda)}{d!-1}.
```
Choose $`N\ge2`$ beyond the support of $`\lambda`$. For $`d>N`$ the floor exponents are zero, so $`V_d=M`$ and the series converges absolutely. Only the first $`N-1`$ terms can differ from those of $`MS`$, and the weight congruence gives
``` math
\begin{equation}
 \mathcal R(\lambda)-M(\lambda)S
 =\sum_{d=2}^N\frac{V_d(\lambda)-M(\lambda)}{d!-1}\in\mathbb Z.
 \label{eq:integer-linear-form}
\end{equation}
```
We now solve $`V_2=\cdots=V_D=0`$ in integer vectors, allowing either sign of $`M`$. Write $`e_n`$ for the unit vector at index $`n`$. The auxiliary coordinate at index one will make the basis triangular. It occurs only in the coefficient vector: the series still starts at $`d=2`$, so no term $`1/(1!-1)`$ is introduced. We impose $`\lambda_1=0`$ in Section <a href="#sec:moments" data-reference-type="ref" data-reference="sec:moments">3</a>.

To see the elimination in a small case, take $`4e_3-e_4`$. Its factorial moment vanishes, and the only nonzero weighted sums are $`V_2=6`$ and $`V_4=23`$: the floor exponent changes only when $`d`$ divides $`4`$. Subtracting $`6(2e_1-e_2)`$ removes $`V_2`$ without changing $`V_4`$. We apply the same procedure successively to all proper divisors.

<div id="res:divisor-channel-coordinates" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos68/PaperCompleteDivisorCoordinates.lean#L260">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/ce368994f355cdf8b00595bfd72e71796e941f20/evidence/erdos-68-factorial-denominator-irrationality.md#res-divisor-channel-coordinates-comparator">Comparator</a></p>

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

*Proof.* First, $`M(T_n)=n(n-1)!-n!=0`$. For a fixed $`d`$, the floor exponents at $`n-1`$ and $`n`$ differ by one precisely when $`d\mid n`$. We therefore have
``` math
V_d(T_n)=(d!-1)W_{d,n}\mathbf1_{d\mid n}.
```
Suppose the identities hold below $`n`$. For each proper divisor $`d`$, subtracting $`W_{d,n}U_d`$ cancels the weighted sum at $`d`$ and changes none of the others. The weighted sum at $`n`$ remains $`n!-1`$, since $`W_{n,n}=1`$. This proves the two identities by induction.

It remains to show that these vectors give all integer solutions. Restrict to indices $`1,\ldots,N`$. The columns $`e_1,T_2,\ldots,T_N`$ form a triangular integer matrix with diagonal $`1,-1,\ldots,-1`$. Passing from the $`T_n`$ to the $`U_n`$ is another triangular integer change, now with diagonal one. Both matrices have determinant a unit, so their inverses have integer entries. We may therefore expand any integer vector uniquely in $`e_1,U_2,\ldots,U_N`$. Applying $`M`$ and $`V_d`$ determines its coefficients as in <a href="#eq:channel-basis-expansion" data-reference-type="eqref" data-reference="eq:channel-basis-expansion">[eq:channel-basis-expansion]</a>. The coefficients with $`d>N`$ are zero because $`V_d=M`$. ◻

</div>

For a prime $`p\ge3`$ the divisor sum is empty, and $`U_p=pe_{p-1}-e_p`$. At a composite index the correction terms remove the extra weighted sums. For example,
``` math
\begin{equation}
 U_9=9e_8-e_9-5040e_2+1680e_3.
 \label{res:translator}
\end{equation}
```
Each $`U_n`$ has moment zero and remainder one. We can thus alter an individual weighted sum by adding a multiple of $`U_n`$, while the fractional part of the remainder stays fixed. This will separate the cancellation equations from the eventual nonintegrality question.

<a id="sec:moments"></a>

# Attainable moments

We first allow the auxiliary coordinate $`\lambda_1`$ and classify all vectors cancelling through a fixed depth $`D\ge2`$. Put
``` math
L_D=\operatorname{lcm}_{2\le d\le D}(d!-1),\qquad
 K_D=L_De_1-\sum_{d=2}^D\frac{L_D}{d!-1}U_d.
```
The integral coordinates in <a href="#eq:channel-basis-expansion" data-reference-type="eqref" data-reference="eq:channel-basis-expansion">[eq:channel-basis-expansion]</a> imply
``` math
\begin{equation}
 V_d(\lambda)\equiv M(\lambda)\pmod{d!-1}.
 \label{res:congruence}
\end{equation}
```
When $`V_2=\cdots=V_D=0`$, these congruences force $`L_D\mid M`$. Substituting $`M=tL_D`$ into the basis expansion gives
``` math
\begin{equation}
 V_2=\cdots=V_D=0
 \quad\Longleftrightarrow\quad
 \lambda=tK_D+\sum_{n>D}z_nU_n,\qquad M=tL_D,
 \label{eq:low-channel-classification}
\end{equation}
```
where the integers $`z_n`$ have finite support. Since $`\mathcal R(e_1)=S`$ and $`\mathcal R(U_n)=1`$, their remainders are
``` math
\begin{equation}
 \mathcal R\left(tK_D+\sum_{n>D}z_nU_n\right)
 =tL_D(S-H_D)+\sum_{n>D}z_n,
 \qquad H_D=\sum_{d=2}^D\frac1{d!-1}.
 \label{eq:residual-transparency}
\end{equation}
```

We now require support on $`n\ge2`$. Write $`a_D=[e_1]K_D`$ and $`u_n=[e_1]U_n`$ for the first coordinates. Setting $`\lambda_1=0`$ gives
``` math
\begin{equation}
 ta_D+\sum_{n>D}z_nu_n=0.\label{eq:support-equation}
\end{equation}
```
Let $`g_D=\gcd\{u_n:n>D\}`$. Since the $`z_n`$ may be arbitrary integers of finite support, their sums $`\sum z_nu_n`$ form the ideal $`g_D\mathbb Z`$. The moments of the admissible vectors are consequently
``` math
\begin{equation}
 \mu_D\mathbb Z,\qquad
 \mu_D=L_D\frac{g_D}{\gcd(g_D,a_D)}.
 \label{eq:attainable-moment-ideal}
\end{equation}
```
Indeed, <a href="#eq:support-equation" data-reference-type="eqref" data-reference="eq:support-equation">[eq:support-equation]</a> has a solution exactly when $`g_D\mid ta_D`$, or equivalently when $`g_D/\gcd(g_D,a_D)`$ divides $`t`$. Bézout’s identity uses finitely many $`u_n`$, so the generator is attained by a finite vector. We show next that $`g_D>0`$. Any vector attaining $`\mu_D`$ is primitive: dividing its coefficients by a common factor greater than one would preserve the cancellations and give a smaller positive moment.

<a id="sec:finite-gcd"></a>

## A finite gcd calculation

The recursion for the first coordinate is
``` math
u_2=2,\qquad
 u_n=-\sum_{\substack{d\mid n\\2\le d<n}}W_{d,n}u_d\quad(n>2).
```
Induction gives $`u_n=0`$ at odd indices. At twice a prime it gives $`u_{2p}=-(2p)!/2^{p-1}\ne0`$, including $`p=2`$, so the tail contains a nonzero coefficient and $`g_D>0`$. To compute this infinite gcd, we show that a specified finite interval already forces divisibility of every later coefficient.

<div id="res:finite-channel-moment-certificate" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/ce368994f355cdf8b00595bfd72e71796e941f20/evidence/erdos-68-factorial-denominator-irrationality.md#res-finite-channel-moment-certificate">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/ce368994f355cdf8b00595bfd72e71796e941f20/evidence/erdos-68-factorial-denominator-irrationality.md#res-finite-channel-moment-certificate-comparator">Comparator</a></p>

**Theorem 3** (a finite formula for the gcd). *Choose a prime $`\ell`$ with $`D/2<\ell\le D`$ and put $`H=D(2\ell-1)`$. Then
``` math
g_D=\gcd(u_{D+1},\ldots,u_H),\qquad H<2D^2.
```*

</div>

<div class="proof">

*Proof.* Let $`g=\gcd(u_{D+1},\ldots,u_H)`$. The interval contains $`2\ell`$, so $`u_{2\ell}=-(2\ell)!/2^{\ell-1}`$ shows that $`g>0`$ and $`g\mid(2\ell)!`$. We prove by strong induction that $`g\mid u_n`$ for all $`n>D`$.

The assertion holds through $`H`$ by definition. For $`n>H`$ split the proper divisors in the recurrence at $`D`$. If $`d\le D`$ and $`d\mid n`$, then $`n/d\ge2\ell`$. We also have
``` math
(n/d)!\mid W_{d,n}\qquad(d\mid n),
```
because the quotient counts partitions into $`n/d`$ unordered blocks of size $`d`$. Hence $`(2\ell)!\mid W_{d,n}`$, and therefore $`g\mid W_{d,n}`$, for each small divisor. If $`D<d<n`$, the induction hypothesis instead gives $`g\mid u_d`$. Every summand of the recurrence is divisible by $`g`$, completing the induction. The finite gcd thus divides the whole tail, while the reverse divisibility follows from inclusion of the finite interval. Finally, $`H\le D(2D-1)<2D^2`$. ◻

</div>

Bertrand’s postulate supplies the prime $`\ell`$ when $`D\ge3`$; for $`D=2`$ take $`\ell=2`$. The proof requires $`n/d\ge2\ell`$ for every small divisor, which is why it uses the horizon $`H=D(2\ell-1)`$. A truncation at $`2D`$ is not justified by this argument.

<a id="sec:depth-four"></a>

## Depth four

At depth four the calculation gives $`L_4=115`$, $`a_4=-55`$ and $`g_4=60`$, so <a href="#eq:attainable-moment-ideal" data-reference-type="eqref" data-reference="eq:attainable-moment-ideal">[eq:attainable-moment-ideal]</a> yields $`\mu_4=1380`$. For the gcd, $`23u_6-u_8=60`$ gives one divisibility, and the reverse follows from
``` math
\begin{equation}
 \operatorname{lcm}(1,\ldots,n)\mid u_n.
 \label{eq:channel-lcm-envelope}
\end{equation}
```
The companion record gives the [Legendre-formula proof and the full moment calculation](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r12-moment). We can also prove the lower bound for this depth without computing the basis coefficients. The required congruence is
``` math
\begin{equation}
 1380\mid 11n!-46W_{2,n}+12W_{4,n}\qquad(n\ge2).
 \label{eq:depth-four-dual}
\end{equation}
```
The expression vanishes at $`n=2,3,4`$. For $`n\ge4`$, each of its three summands is divisible by $`12`$; for the term involving $`W_{2,n}`$, use $`W_{2,2r}=r!\prod_{j=1}^r(2j-1)`$ and $`W_{2,2r+1}=(2r+1)W_{2,2r}`$. For $`n\ge5`$, removing powers of $`2`$ or $`24`$ from $`n!`$ preserves divisibility by $`5`$. Finally $`n!\equiv W_{4,n}\pmod{23}`$ and $`46W_{2,n}\equiv0\pmod{23}`$. Combining the three coprime moduli $`12,5,23`$ proves <a href="#eq:depth-four-dual" data-reference-type="eqref" data-reference="eq:depth-four-dual">[eq:depth-four-dual]</a>.

Now sum <a href="#eq:depth-four-dual" data-reference-type="eqref" data-reference="eq:depth-four-dual">[eq:depth-four-dual]</a> against $`\lambda_n`$. If $`V_2=V_4=0`$, we obtain $`1380\mid11M`$ and hence $`1380\mid M`$. The following vector attains $`M=1380`$ and cancels $`V_3`$ as well:
``` math
\begin{equation}
 \lambda=1482e_2-784e_3-136e_5+83e_6-e_8,
 \qquad (M,V_2,V_3,V_4)=(1380,0,0,0).
 \label{eq:depth-four-short-vector}
\end{equation}
```
Table <a href="#tab:depth-four" data-reference-type="ref" data-reference="tab:depth-four">1</a> verifies all four sums directly.

<div id="tab:depth-four">

| $`n`$ | $`\lambda_n`$ | $`n!`$ | $`W_{2,n}`$ | $`W_{3,n}`$ | $`W_{4,n}`$ |
|------:|--------------:|-------:|------------:|------------:|------------:|
|     2 |          1482 |      2 |           1 |           2 |           2 |
|     3 |          -784 |      6 |           3 |           1 |           6 |
|     5 |          -136 |    120 |          30 |          20 |           5 |
|     6 |            83 |    720 |          90 |          20 |          30 |
|     8 |            -1 |  40320 |        2520 |        1120 |          70 |

The depth-four vector. Multiplying the last four columns by $`\lambda_n`$ and summing gives $`1380,0,0,0`$.

</div>

The extra equation $`V_3=0`$ restricts the vectors without changing the attainable moments. For example, $`3e_2-e_3`$ has $`M=V_2=V_4=0`$ but $`V_3=5`$. To attain $`1380`$ we also need an index at least eight. Indeed, the expression in <a href="#eq:depth-four-dual" data-reference-type="eqref" data-reference="eq:depth-four-dual">[eq:depth-four-dual]</a> vanishes through $`n=5`$ and equals $`4140,7\cdot4140`$ at $`n=6,7`$. Repeating the congruence argument shows that support at most seven and $`V_2=V_4=0`$ force $`4140\mid M`$.

We finish the example by excluding denominators of $`S`$. For the vector in <a href="#eq:depth-four-short-vector" data-reference-type="eqref" data-reference="eq:depth-four-short-vector">[eq:depth-four-short-vector]</a>, <a href="#eq:residual-transparency" data-reference-type="eqref" data-reference="eq:residual-transparency">[eq:residual-transparency]</a> gives $`\mathcal R(\lambda)=1380(S-H_4)-44`$. Exact rational arithmetic gives
``` math
-31+\frac45
 <1380\sum_{d=5}^{8}\frac1{d!-1}-44
 <-31+\frac56,
 \qquad \frac{2\cdot1380}{9!-1}<\frac1{100}.
```
Since the remaining tail is positive and less than $`2/(9!-1)`$, we obtain $`-31<\mathcal R(\lambda)<-30`$. If $`S=a/q`$ with $`q\mid1380`$, then <a href="#eq:integer-linear-form" data-reference-type="eqref" data-reference="eq:integer-linear-form">[eq:integer-linear-form]</a> would make this remainder an integer. Thus every divisor of $`1380`$ is excluded. The larger computations in Section <a href="#sec:finite" data-reference-type="ref" data-reference="sec:finite">7</a> give stronger finite exclusions.

<a id="sec:translator"></a>

# The cost of cancellation

Cancellation imposes divisibility beyond $`L_D\mid M`$. On support $`n\ge2`$, we have $`12\mid M-2V_2`$: for $`n=2,3`$ the identity $`n!=2W_{2,n}`$ holds, and for $`n\ge4`$ both terms are divisible by $`12`$. Since every $`d!-1`$ is coprime to $`6`$, it follows that
``` math
\begin{equation}
 12L_D\mid M.\label{eq:twelve-lcm}
\end{equation}
```
The least positive moment can be larger; at $`D=6`$ it is $`24L_6`$. Also, $`9\nmid12L_D`$ for every $`D`$, so these compulsory factors alone do not provide divisibility by every possible denominator.

To understand the support restriction, consider an interval on which the floor exponent in a fixed weight is constant.

<div id="res:bandbreakpoint" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/ce368994f355cdf8b00595bfd72e71796e941f20/evidence/erdos-68-factorial-denominator-irrationality.md#res-bandbreakpoint">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/ce368994f355cdf8b00595bfd72e71796e941f20/evidence/erdos-68-factorial-denominator-irrationality.md#res-bandbreakpoint-comparator">Comparator</a></p>

**Theorem 4** (constant values of the floor in the weights). *Let $`\lambda`$ be a finitely supported integer vector, let $`d\ge2`$ and $`k\ge0`$ be integers, and suppose each index $`n`$ in its support satisfies $`kd\le n<(k+1)d`$. Then
``` math
M(\lambda)=(d!)^k V_d(\lambda).
```
In particular, support in $`[d,2d)`$ and $`V_d(\lambda)=0`$ force $`M(\lambda)=0`$. If all supported indices are at least $`d`$, $`V_d(\lambda)=0`$ and $`M(\lambda)\ne0`$, some supported index is at least $`2d`$.*

</div>

<div class="proof">

*Proof.* Multiply $`n!=(d!)^kW_{d,n}`$ by $`\lambda_n`$ and sum over the support. This proves the identity. In the interval $`[d,2d)`$ we have $`k=1`$, so $`V_d=0`$ would imply $`M=0`$, proving the final assertion. ◻

</div>

The size of $`L_N`$ gives a second restriction. We have
``` math
\begin{equation}
 \liminf_{N\to\infty}\frac{\log L_N}{N^{3/2}\log N}
 \ge\frac{2\sqrt2}{3}.
 \label{res:lcm-growth}
\end{equation}
```
We compare the product of a short terminal block of denominators with their pairwise gcds. Subtraction gives $`\gcd(i!-1,j!-1)\mid j!/i!-1`$ for $`i<j`$. This is the constant-shift case of the argument of Luca and Shparlinski \[luca-shparlinski, proof of Lemma 5, p. 811\], also used by Lai \[lai, proof of Lemma 2.4, (2.5)\]; shared prime powers were used in spacing arguments by Erdős and Stewart \[erdos-stewart1976, §3\].

For positive integers $`x_i`$, compare valuations prime by prime to obtain $`\prod_i x_i\mid\operatorname{lcm}(x_i)\prod_{i<j}\gcd(x_i,x_j)`$. Apply this inequality to $`x_i=i!-1`$ over the last $`k`$ indices through $`N`$. The subtraction bound then gives
``` math
\log L_N\ge\sum_{n=N-k+1}^N\log(n!-1)
              -\binom{k+1}{3}\log N.
```
Taking $`k=\lfloor\alpha\sqrt N\rfloor`$, we obtain the limiting normalised lower bound $`\alpha-\alpha^3/6`$ by Stirling’s formula. Its maximum over $`\alpha>0`$ occurs at $`\alpha=\sqrt2`$, giving <a href="#res:lcm-growth" data-reference-type="eqref" data-reference="res:lcm-growth">[res:lcm-growth]</a>. The companion record [gives the error estimates and the extension to a fixed nonzero polynomial shift](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r12-lcm), using the eventual nonvanishing lemma attributed by Lai \[lai, Lemma 2.1\] to Luca and Shparlinski. The shift $`n!+2^n-1`$ requires a different elimination \[luca-shparlinski-exp, Lemmas 2.1–2.3\].

Here $`L_N`$ is the common denominator before reduction. Multiplying the tail by it actually gives a quantity tending to infinity. To see this, note that $`(N-1)!-1`$ and $`N!-1`$ are coprime: subtraction makes a common divisor divide $`N-1`$, to which $`(N-1)!-1`$ is coprime. Thus
``` math
L_N(S-H_N)>
 \frac{((N-1)!-1)(N!-1)}{(N+1)!-1}\longrightarrow\infty.
```
Consequently the usual small-tail proof cannot use this clearing factor. Appendix <a href="#sec:prime-pole" data-reference-type="ref" data-reference="sec:prime-pole">8</a> treats the cancellations that can occur when the partial sum is reduced.

<a id="sec:compressed-kernel"></a>

# Solutions on an arithmetic progression

We next construct vectors whose moments are eventually divisible by every fixed denominator. Equal spacing turns the cancellation equations into prescribed roots of a polynomial. Let $`D,r\ge2`$, let $`\ell`$ be a positive multiple of $`2,\ldots,D`$, and put
``` math
i_j=r+j\ell\ (0\le j<D),\quad N=r+(D-1)\ell,\quad
 \alpha_d=(d!)^{\ell/d},\quad A=\prod_{d=2}^D\alpha_d,
```
and define $`h_j`$ and the supported coefficients by
``` math
\prod_{d=2}^D(\alpha_dX-1)=\sum_{j=0}^{D-1}h_jX^j,
 \qquad c_{i_j}=\frac{N!h_j}{A i_j!}.
```
Set all other coefficients to zero. We first check integrality. Each term of $`h_j/A`$, up to sign, is the reciprocal of a product of $`D-1-j`$ distinct $`\alpha_d`$. A factor $`\alpha_d=(d!)^{\ell/d}`$ represents $`\ell/d`$ blocks of size $`d`$, with total size $`\ell`$. Together with a block of size $`i_j`$, the selected factors therefore account for $`i_j+(D-1-j)\ell=N`$ objects. The corresponding multinomial coefficient is an integer, proving $`c_{i_j}\in\mathbb Z`$. The leading coefficient gives $`c_N=1`$, so the vector is primitive.

We now use the roots of the polynomial. Since $`d\mid\ell`$, each step along the progression increases the floor exponent by $`\ell/d`$, and
``` math
V_d(c)=\frac{N!}{A(d!)^{\lfloor r/d\rfloor}}
          \sum_{j=0}^{D-1}h_j\alpha_d^{-j}=0
 \qquad(2\le d\le D).
```
Summing $`c_{i_j}i_j!`$ amounts to evaluating the polynomial at one, giving
``` math
\begin{equation}
 M=N!\prod_{d=2}^D(1-1/\alpha_d),\qquad 0<M<N!.
 \label{eq:progression-moment}
\end{equation}
```
For $`D=r=\ell=2`$ the vector is $`-6e_2+e_4`$, with moment $`12`$. We make no minimal-support assertion for this family.

For divisibility of the moments we use the same block count, now leaving blocks of each equal size unordered. It gives
``` math
\frac{N!}{r!A\prod_{d=2}^D(\ell/d)!}\in\mathbb Z.
```
Since $`M=(N!/A)\prod_{d=2}^D(\alpha_d-1)`$, we deduce that $`r!\prod_{d=2}^D(\ell/d)!`$ divides $`M`$. Put $`v=\max(r,\ell/2)`$. One of the factors $`r!`$ and $`(\ell/2)!`$ is $`v!`$, while $`D\le\ell\le2v`$ gives $`N\le4v^2-v<4v^2`$. Hence
``` math
\begin{equation}
 (\lfloor\sqrt N/2\rfloor+1)!\mid M,
 \qquad N\ge4(q-1)^2\ \Longrightarrow\ q\mid M.
 \label{eq:progression-divisibility}
\end{equation}
```
Thus, for each fixed $`q`$, all sufficiently large endpoints in this family give $`q\mid M`$. Excluding $`q`$ still requires a nonintegral remainder for one of those vectors.

<a id="sec:open"></a>

# Nonintegrality of the remainder

<span id="sec:plateau" label="sec:plateau"></span> <span id="r12-short-gap"></span>

Fix a vector with $`V_2=\cdots=V_D=0`$ and $`M>0`$. We may choose the cutoff $`N\ge D`$ anywhere at or beyond its support. Separate the finite signed sum from the positive tail:
``` math
A_N=\sum_{d=D+1}^N\frac{V_d(\lambda)}{d!-1},\qquad
 \mathcal R(\lambda)=A_N+M(S-H_N).
```
The tail satisfies $`0<S-H_N<2/((N+1)!-1)`$. We can therefore prove nonintegrality by comparing its upper bound with the distance from $`A_N`$ to the next integer:
``` math
\begin{equation}
 \frac{2M}{(N+1)!-1}<\lfloor A_N\rfloor+1-A_N
 \label{eq:signed-block-gap}
\end{equation}
```
Under this inequality, $`\mathcal R(\lambda)`$ lies strictly between consecutive integers, excluding every denominator dividing $`M`$. The argument allows either sign of $`A_N`$. Its strict gap is one when $`A_N`$ is integral and can be arbitrarily small when $`A_N`$ approaches an integer from below.

At the support endpoint of a progression vector, <a href="#eq:progression-moment" data-reference-type="eqref" data-reference="eq:progression-moment">[eq:progression-moment]</a> gives $`0<M(S-H_N)<2/N`$. The right side of <a href="#eq:signed-block-gap" data-reference-type="eqref" data-reference="eq:signed-block-gap">[eq:signed-block-gap]</a> can shrink too, so this bound alone does not prove nonintegrality. To prove irrationality by these vectors, we need the comparison to succeed for a moment divisible by each prescribed $`q>0`$. Merely making the moments unbounded would not suffice.

Increasing the cutoff is a different operation from choosing a new vector. For $`-6e_2+e_4`$ the support ends at four, where the test fails because $`9/115<24/119`$. At $`N=5`$ it succeeds because $`13376/13685>24/719`$. More generally, for a fixed vector with $`M>0`$, the quantities $`A_N`$ increase to $`\mathcal R`$. If this limit is nonintegral, their gaps to the next integer tend to a positive number, so the test eventually succeeds. If the limit is integral, the eventual gap equals the omitted tail and the test fails. Thus extending the cutoff eventually detects a nonintegral remainder, but leaves both the remainder and the moment unchanged.

<a id="sec:nogo"></a>

#### Short cutoffs.

<span id="sec:adjacent-unit-no-go" label="sec:adjacent-unit-no-go"></span> If $`N=D+O(1)`$ as $`D\to\infty`$, then $`L_D\mid M`$ and <a href="#res:lcm-growth" data-reference-type="eqref" data-reference="res:lcm-growth">[res:lcm-growth]</a> force the left side of the test to infinity, while the right side is at most one. Hence such cutoffs cannot succeed. This is a support restriction only when the cutoff must equal the support endpoint. A large prime-power denominator also gives no uniform lower bound on the gap: the reduced fraction $`1-1/q^e`$ has gap $`1/q^e`$.

<a id="sec:finite"></a>

# Carries and finite denominator exclusions

We can also exclude denominators directly from scaled partial sums. For $`m\ge2`$ put
``` math
H_m=\sum_{n=2}^m\frac1{n!-1},\qquad
 Z_m=\lfloor m!H_m\rfloor+1,
```
and for $`m\ge3`$ put $`b_m=mZ_{m-1}+1-Z_m`$. The definition always takes the next integer, even if $`m!H_m`$ is already integral. For $`n\ge3`$, the bound $`1/(n!-1)<(n-1)/n!`$ telescopes to $`0<m!(S-H_m)<1`$. A rational value of $`S`$ would therefore satisfy
``` math
\begin{equation}
 S=a/q,\quad q\mid(m-1)!,\quad m\ge3
 \quad\Longrightarrow\quad Z_m=m!S=mZ_{m-1},\quad b_m=1.
 \label{eq:finite-denominator-consumer}
\end{equation}
```
It is $`m!S`$ that is integral in this argument; no integrality of $`m!H_m`$ is assumed. Thus a non-unit carry excludes every divisor of $`(m-1)!`$, in particular every positive denominator below $`m`$.

<div id="res:carry-characterization" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L45">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/ce368994f355cdf8b00595bfd72e71796e941f20/evidence/erdos-68-factorial-denominator-irrationality.md#res-carry-characterization-comparator">Comparator</a></p>

**Theorem 5** (exact carry characterisation). *<span id="res:strict-successor-complete-characterization" label="res:strict-successor-complete-characterization"></span> The following conditions are equivalent:
``` math
S\notin\mathbb Q,\qquad
(\forall B)(\exists m>B)\ b_m\ne1,\qquad
(\forall B)(\exists m>B)\ m\nmid Z_m.
```
In particular, [cofinal non-unit carries imply irrationality](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos68/FactorialZeroPlateau.lean#L953); equivalently, the original problem is the [criterion using the next integer](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos68/FactorialZeroPlateau.lean#L1090).*

</div>

<div class="proof">

*Proof.* If $`S`$ is rational, <a href="#eq:finite-denominator-consumer" data-reference-type="eqref" data-reference="eq:finite-denominator-consumer">[eq:finite-denominator-consumer]</a> gives $`b_m=1`$ for all sufficiently large $`m`$. Conversely, if $`b_m=1`$ eventually, then $`Z_m=mZ_{m-1}`$, so $`Z_m/m!`$ is eventually a fixed rational number. Since $`H_m<Z_m/m!\le H_m+1/m!`$, that number is $`S`$. To relate the carries to divisibility, write $`x=(m-1)!H_{m-1}`$. Then
``` math
b_m=m-1-\lfloor m\{x\}+1/(m!-1)\rfloor,\qquad -1\le b_m\le m-1.
```
Using $`Z_m=mZ_{m-1}+1-b_m`$, we see that $`m\mid Z_m`$ is equivalent to $`m\mid1-b_m`$. In the displayed range the only possible multiple of $`m`$ is zero, so $`m\mid Z_m`$ holds exactly when $`b_m=1`$. ◻

</div>

For the given series, it remains to prove
``` math
\begin{equation}
 (\forall B)(\exists m>B)\ m\nmid Z_m.
 \label{eq:canonical-open-target}
\end{equation}
```
The recorded exact GMP calculation through $`m=300000`$ has unit carries
``` math
52,\ 591,\ 1030,\ 1407,\ 1438,\ 2164,\ 4258,\ 10991,\ 21236.
```
The non-unit endpoint excludes the divisors of $`299999!`$. Denominators with only primes at most $`299999`$ are not all excluded, because their prime exponents may exceed those in the factorial. Equivalently, a rational denominator $`q`$ would have least $`r>0`$ with $`q\mid r!`$ at least $`300000`$, the factorial index used by Sondow for $`e`$ \[sondow2006, §3, Theorem 1\]; his approximation bound is not being applied to $`S`$.

<a id="sec:continued-fractions"></a>

## A continued-fraction exclusion

A rational enclosure gives a size bound on any denominator. Put $`B=2^{80000}`$, let $`N`$ be the first integer with $`N!-1>B`$, and define
``` math
\ell=\sum_{n=2}^{N-1}\left\lfloor\frac B{n!-1}\right\rfloor,
 \qquad u=\ell+(N-2)+\left\lfloor\frac{2B}{N!-1}\right\rfloor+1.
```
Rounding the $`N-2`$ prefix terms loses less than $`N-2`$, and the tail is less than $`2/(N!-1)`$, proving the strict enclosure $`\ell/B<S<u/B`$. The recorded integer calculation gives $`N=7054`$, $`u-\ell=7053`$ and $`23449`$ common partial quotients $`a_0,\ldots,a_{23448}`$. The convergent denominators satisfy
``` math
Q_{-2}=1,\quad Q_{-1}=0,\quad Q_j=a_jQ_{j-1}+Q_{j-2},
 \qquad Q_{23448}\ge2^{39990}>10^{12038}.
```
To obtain the common prefix, retain each common integer part while both remainders are nonzero, then invert and reverse the endpoints. Every rational strictly between the original endpoints has that prefix. If its continued fraction continues after $`P_j/Q_j`$ with $`x/y>1`$, its denominator is $`Q_jx+Q_{j-1}y\ge Q_j`$; termination gives $`Q_j`$. The fractions are reduced by the determinant identity $`P_jQ_{j-1}-P_{j-1}Q_j=\pm1`$ \[nist-dlmf, §1.12(ii)\]. Hence every representation $`S=a/q`$, reduced or otherwise, has $`q\ge2^{39990}`$.

Neither restriction contains the other. The prime $`300007`$ satisfies $`q\nmid299999!`$ but fails the size bound, and $`299999!`$ does the reverse. Both large calculations were performed outside Lean. The companion record [identifies their programs and recorded outputs](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r12-finite), the separate carry calculation through $`4000`$, and the kernel-checked non-unit carry at $`67`$. None establishes <a href="#eq:canonical-open-target" data-reference-type="eqref" data-reference="eq:canonical-open-target">[eq:canonical-open-target]</a>.

<a id="sec:prime-pole"></a>

# Reduced denominators

To determine the reduced denominator, we must account for cancellation between summands. It can remove a prime, as in $`1/3+1/15=2/5`$, or lower its exponent, as in $`1/9+1/45=2/15`$. The reciprocal-sum test below is the elementary-symmetric-sum valuation formula of Louwsma and Martino \[louwsma-martino, Lemma 4.1, p. 10\] after division by the product of the arguments.

Write $`v_q`$ for the exponent of a prime $`q`$ and $`\operatorname{den}`$ for the positive reduced denominator. Let $`A_M=\sum_{n=2}^M L_M/(n!-1)`$, and suppose $`e=\max_{2\le n\le M}v_q(n!-1)>0`$. If $`I_{q,e}(M)`$ is the set where this maximum is attained, put
``` math
R_{q,e}(M)=\sum_{n\in I_{q,e}(M)}
 \left((n!-1)/q^e\right)^{-1}\pmod q.
```
Reduce $`A_M`$ modulo $`q`$. Terms whose denominator has valuation below $`e`$ vanish, leaving $`A_M\equiv(L_M/q^e)R_{q,e}(M)\pmod q`$. Since $`L_M/q^e`$ is a unit modulo $`q`$, we obtain
``` math
\begin{equation}
 v_q(\operatorname{den}H_M)=e
 \quad\Longleftrightarrow\quad R_{q,e}(M)\ne0\pmod q.
 \label{eq:prime-pole-survival}
\end{equation}
```
The surviving exponent in general is $`\max(0,e-v_q(A_M))`$. Thus a zero residue lowers the exponent, and removes the prime completely only when $`v_q(A_M)\ge e`$.

For an example of complete cancellation, take $`q=139`$. The maximal exponent is one at indices $`69,122,137`$, with cofactor residues $`6,49,73`$ and reciprocal sum zero. For $`q=2593`$ the indices are $`349,2243,2591`$, with cofactor residues $`1508,1566,1678`$ and reciprocal sum zero. Each prime disappears completely and remains absent from all later reduced partial sums. Indeed, Wilson’s theorem excludes a denominator divisible by $`q`$ at index $`q-1`$, and $`n!\equiv0\pmod q`$ excludes one at $`n\ge q`$. This persistence statement concerns finite partial sums. Spacing bounds \[stewart2004, Lemma 2\] and factorial value multiplicities \[garaev-luca-shparlinski, arXiv v1, Theorem 12\] do not supply the real-tail comparison for $`S`$.

<a id="sec:projection"></a>

## A sufficient inequality

We now remove the prime-power levels shared by two denominators. The remaining maximal levels occur in unique summands and cannot cancel. For a natural parameter $`p\ge3`$, not necessarily prime, put $`d_n=n!-1`$ and
``` math
F_p=(p-1)!,\quad D_p=\operatorname{lcm}_{2\le i<j\le2p-1}\gcd(d_i,d_j),
 \quad C_p=\operatorname{lcm}(F_p,D_p),
```
``` math
L_p^{\rm blk}=\operatorname{lcm}(F_p,d_2,\ldots,d_{2p-1}),\quad
 R_p=L_p^{\rm blk}/C_p,\quad
 T_p=\sum_{n=2}^{2p-1}L_p^{\rm blk}/d_n,\quad
 \rho_p=(-T_p)\bmod R_p.
```
For a prime dividing $`R_p`$, exactly one summand of $`T_p`$ is a unit modulo that prime. Hence $`\gcd(T_p,R_p)=1`$, so $`R_p=\operatorname{den}(C_pH_{2p-1})`$. The factors $`C_p`$ and $`R_p`$ need not be coprime. When $`R_p>1`$, the strict gap to the next integer is $`\rho_p/R_p>0`$; when $`R_p=1`$, that gap is one, even though $`\rho_p=0`$.

<div id="res:global-complementary-criterion" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L154">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/ce368994f355cdf8b00595bfd72e71796e941f20/evidence/erdos-68-factorial-denominator-irrationality.md#res-global-complementary-criterion-comparator">Comparator</a></p>

**Proposition 6** (a sufficient tail inequality). *If arbitrarily large natural parameters $`p\ge3`$ satisfy
``` math
\begin{equation}
R_p>1,\qquad
(2p+1)L_p^{\rm blk}<2p^2(2p-1)!\rho_p,
\label{eq:global-complementary-target}
\end{equation}
```
then $`S`$ is irrational.*

</div>

<div class="proof">

*Proof.* Suppose $`S=a/q`$. Choose an admissible $`p>q`$, so $`q\mid F_p\mid C_p`$ and $`C_pS`$ is an integer. It lies above $`C_pH_{2p-1}`$ by at least $`\rho_p/R_p`$. On the other hand, the tail estimate gives
``` math
C_p(S-H_{2p-1})<\frac{(2p+1)C_p}{2p^2(2p-1)!}<\frac{\rho_p}{R_p},
```
a contradiction. For the first inequality, use $`1/(n!-1)<2/n!`$ for $`n\ge2p`$ and sum a geometric majorant with ratio $`1/(2p+1)`$. The second inequality is <a href="#eq:global-complementary-target" data-reference-type="eqref" data-reference="eq:global-complementary-target">[eq:global-complementary-target]</a>. ◻

</div>

At $`p=3`$ the test succeeds: $`C_3=2`$, $`C_3H_5=34264/13685`$, and the gap $`6791/13685`$ exceeds the tail bound $`7/1080`$. Whether the hypothesis holds for arbitrarily large $`p`$ remains open. Its logarithmic form is
``` math
\begin{equation}
 \log\frac{C_p}{(p-1)!}-\log\frac{\rho_p}{R_p}
 <\log\frac{2p^2(2p-1)!}{(2p+1)(p-1)!}
 =p\log p+(2\log2-1)p+O(\log p).
 \label{eq:joint-loss-budget}
\end{equation}
```
The strict comparison uses the exact logarithm, whose asymptotic expansion is shown on the right. Nonvanishing of $`\rho_p`$ alone gives no uniform lower bound for $`\rho_p/R_p`$, so the clearing factor and gap must be estimated at the same indices. Requiring in addition a prime $`q\mid R_p`$ with $`(2p+1)C_pq<2p^2(2p-1)!`$ would impose a stronger condition.

<a id="sec:companion-orbit"></a>

# The factorial digits of $`S-e+2`$

Subtract the exponential series term by term, using $`1/(n!-1)=1/n!+1/(n!(n!-1))`$, to obtain
``` math
\begin{equation}
 C+(e-2)=S,\qquad C=\sum_{n\ge2}\frac1{n!(n!-1)}.
 \label{eq:companion-decomposition}
\end{equation}
```
The series are absolutely convergent. We use the canonical factorial digits of $`C`$, defined by
``` math
d_m(C)=\lfloor m!C\rfloor-m\lfloor(m-1)!C\rfloor,\qquad 0\le d_m(C)<m.
```
This floor convention selects $`1/2!`$ rather than the eventually maximal expansion $`1/2=\sum_{m\ge3}(m-1)/m!`$. Cantor’s criterion \[cantor1869\] says that a rational number has eventually zero canonical digits. In the present decomposition, rationality of $`S`$ corresponds to the eventual digit $`m-2`$ for $`C`$.

<div id="res:companion-orbit-rationality-boundary" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L27">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/ce368994f355cdf8b00595bfd72e71796e941f20/evidence/erdos-68-factorial-denominator-irrationality.md#res-companion-orbit-rationality-boundary-comparator">Comparator</a></p>

**Theorem 7** (rationality and factorial residues). *The following statements are equivalent:*

1.  *$`S\in\mathbb Q`$;*

2.  *$`(\lfloor m!C\rfloor+2)\bmod m=0`$ for every sufficiently large $`m`$.*

*Consequently,
``` math
\begin{equation}
 S\notin\mathbb Q
 \quad\Longleftrightarrow\quad
 (\forall B)(\exists m>B)\;
   (\lfloor m!C\rfloor+2)\bmod m\ne0 .
 \label{eq:companion-cofinal}
\end{equation}
```*

</div>

<div class="proof">

*Proof.* Suppose $`S=a/q`$ and take $`m`$ with $`q\mid(m-1)!`$. The integer $`E_m=m!\sum_{n=2}^m1/n!`$ is congruent to one modulo $`m`$, and $`0<m!\sum_{n>m}1/n!<1`$. Equation <a href="#eq:companion-decomposition" data-reference-type="eqref" data-reference="eq:companion-decomposition">[eq:companion-decomposition]</a> therefore gives $`\lfloor m!C\rfloor=m!S-E_m-1\equiv-2\pmod m`$.

Conversely, the residue condition and $`0\le d_m(C)<m`$ force $`d_m(C)=m-2`$ for all sufficiently large $`m\ge3`$. Choose $`N`$ beyond the exceptions. We add the canonical expansion of $`C`$ to that of $`e-2`$; the tail then telescopes by $`\sum_{m>N}(m-1)/m!=1/N!`$. Thus
``` math
S=\lfloor C\rfloor+\sum_{m=2}^N\frac{d_m(C)+1}{m!}+\frac1{N!}\in\mathbb Q.
```
Negating the eventual assertion gives the cofinal equivalence. ◻

</div>

<div id="bdry:companion-orbit-nonconcentration" class="remark">

*Remark 1*. It remains to prove that the displayed congruence fails at arbitrarily large indices for this particular $`C`$. Any one finite list of failures, however long, is not enough. The theorem is an equivalence, not an estimate for the distribution of these residues.

</div>

<a id="sec:digits"></a>

## The floor correction

To compare these digits with the carries, we must account for the tail removed before taking a floor. Set
``` math
\delta_m=m!\sum_{n>m}\frac1{n!(n!-1)},\qquad
 \sigma_m=\mathbf1_{\{\{m!C\}<\delta_m\}}.
```
Here $`\{x\}=x-\lfloor x\rfloor`$. The factorial-tail bound gives $`0<\delta_m<1/((m+1)!-1)<1`$. Subtracting $`\delta_m`$ from $`m!C`$ lowers its floor by one exactly when $`\{m!C\}<\delta_m`$. Therefore
``` math
Z_m=m!\sum_{n=2}^m\frac1{n!}+\lfloor m!C\rfloor+1-\sigma_m.
```
Insert this expression for $`Z_m`$ into the carry recurrence to obtain
``` math
\begin{equation}
 b_m=m-1-d_m(C)+\sigma_m-m\sigma_{m-1}\qquad(m\ge3).
 \label{eq:companion-wrap}
\end{equation}
```
When $`\{m!C\}=\delta_m`$, the prefix is integral and $`\sigma_m=0`$. For a smaller fractional part, subtracting even this small tail crosses an integer. Tail size alone therefore permits neither correction term to be omitted.

<a id="app:sources"></a>

# Verification and related estimates

*Formal proofs.* A result with a kernel-checked Lean proof carries a mark in the margin. *Lean* opens the proof: the declaration itself when one declaration states the whole result, otherwise the list of declarations that together state it. *Comparator* opens the record of an independent check, in which the same statement, written again from Mathlib alone in a separate repository, was compared with our proof by Lean’s Comparator tool, allowing only the three standard axioms. A dagger on the Lean mark means that the Lean proof assumes an input named just below the result. A result without a mark has no Lean proof of its whole statement; what is checked is said below it. The [evidence record](https://github.com/wcook04/plectis-erdos/blob/ce368994f355cdf8b00595bfd72e71796e941f20/evidence/erdos-68-factorial-denominator-irrationality.md) gives every declaration, version and check. These checks show that the stated propositions are proved; whether they are the right propositions is a question the reader can settle by comparing them with the text.

The margin marks identify the recorded statements and comparisons. The value $`1380`$ and the full-tail divisibility <a href="#eq:channel-lcm-envelope" data-reference-type="eqref" data-reference="eq:channel-lcm-envelope">[eq:channel-lcm-envelope]</a> have ordinary proofs with exact arithmetic checks; the generic formal gcd lemmas take that divisibility as an input. The individual declarations and their original revisions are listed in the [companion source concordance](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r12-short-sources). Section <a href="#sec:finite" data-reference-type="ref" data-reference="sec:finite">7</a> distinguishes the two recorded large computations from kernel checks.

Denominator savings also occur in the $`p`$-adic linear forms of Lai, Lupu and Sprang \[lai-lupu-sprang, §5, Lemma 7.3 and (8.1)\]. Their irrationality criterion \[lai-lupu-sprang, Lemma 2.1\], quoted from Lai \[lai-2adic, Lemma 2.1\], requires nonzero integer-coefficient forms whose $`p`$-adic absolute values times the largest ordinary coefficient size tend to zero on the same unbounded subsequence. For the prefixes considered here, the corresponding saving is $`L_M/\operatorname{den}(H_M)`$. Its required asymptotic size remains unproved, and no $`p`$-adic zeta theorem is being applied to $`S`$.

The companion shows that the cofactor construction, with positive starting parameter, recovers the progression vector up to sign. Requiring a nonintegral remainder with least support index tending to infinity is equivalent to irrationality. It also treats adjacent unit carries, lower-endpoint intervals and $`p^2\mid Z_{2p}`$, whose proposed applications still require a same-index comparison. Non-unit carries at arbitrarily large $`2p`$ with $`p`$ an odd prime would suffice. Fixed denominator factors eventually divide the removed factorial, so they cannot by themselves supply these conditions.

<a id="acknowledgements"></a>

# Acknowledgements

The author thanks Wouter van Doorn for advice on exposition: explaining notation when it first appears, avoiding private terminology, and saying how restrictive a conditional hypothesis is. His advice concerned the writing of another note; he has not reviewed the mathematics of this paper. An AI research pass supplied by Will Cook derived the depth-four dual congruence and shorter vectors from the factorial-channel definitions and general moment-ideal theory developed earlier here. OpenAI Codex checked and integrated them; a separate AI pass reviewed the proof.

<div class="thebibliography">

99

Paul Erdős. [On the irrationality of certain series: problems and results](https://doi.org/10.1017/CBO9780511897184.009). In Alan Baker (ed.), *New Advances in Transcendence Theory*, Cambridge University Press (1988), pp. 102–109.

Thomas F. Bloom. [Erdős Problem \#68](https://www.erdosproblems.com/68). Online resource (2026). Historical access: 28 July 2026; present-page status not reverified.

Georg Cantor. Über die einfachen Zahlensysteme. *Zeitschrift für Mathematik und Physik* **14** (1869), 121–128.

János Galambos. [Representations of Real Numbers by Infinite Series](https://doi.org/10.1007/BFb0081642). Lecture Notes in Mathematics 502, Springer (1976).

Wolfram Koepf and Dieter Schmersau. [Irrationality of certain infinite series II](https://doi.org/10.1524/anly.2011.1094). *Analysis* **31** (2011), 117–124.

Jaroslav Hančl and Robert Tijdeman. [On the irrationality of factorial series](https://doi.org/10.4064/aa118-4-5). *Acta Arithmetica* **118** (4) (2005), 383–401.

Joel Louwsma and Joseph Martino. [Rational numbers with odd greedy expansion of fixed length](https://arxiv.org/abs/2309.07280v1). Preprint (2023). arXiv:2309.07280.

Li Lai. [On the largest prime divisor of $`n!+1`$](https://doi.org/10.1017/S0004972725100543). *Bulletin of the Australian Mathematical Society* **113** (3) (2026), 390–403. arXiv:2103.14894.

Florian Luca and Igor E. Shparlinski. [Prime divisors of shifted factorials](https://doi.org/10.1112/S0024609305004923). *Bulletin of the London Mathematical Society* **37** (6) (2005), 809–817.

Li Lai, Cezar Lupu and Johannes Sprang. [On the irrationality of certain $`p`$-adic zeta values](https://doi.org/10.1007/s40687-025-00559-x). *Research in the Mathematical Sciences* **12** (4) (2025), article 77. arXiv:2505.23088.

Li Lai. [On the irrationality of certain $`2`$-adic zeta values](https://doi.org/10.1142/S1793042125500113). *International Journal of Number Theory* **21** (1) (2025), 207–235. arXiv:2304.00816.

NIST Digital Library of Mathematical Functions. [Continued fractions: convergents](https://dlmf.nist.gov/1.12). Online resource (2026).

Paul Erdős and Cameron L. Stewart. [On the greatest and least prime factors of $`n!+1`$](https://doi.org/10.1112/jlms/s2-13.3.513). *Journal of the London Mathematical Society* **13** (3) (1976), 513–519.

Florian Luca and Igor E. Shparlinski. [On the largest prime factor of $`n!+2^n-1`$](https://doi.org/10.5802/jtnb.524). *Journal de Théorie des Nombres de Bordeaux* **17** (3) (2005), 859–870.

Jonathan Sondow. [A geometric proof that $`e`$ is irrational and a new measure of its irrationality](https://arxiv.org/abs/0704.1282v2). *American Mathematical Monthly* **113** (7) (2006), 637–641. arXiv:0704.1282. Addendum: *Amer. Math. Monthly* **114** (2007), 659; reading copy v2.

Cameron L. Stewart. [On the greatest and least prime factors of $`n!+1`$, II](https://doi.org/10.5486/PMD.2004.3190). *Publicationes Mathematicae Debrecen* **65** (3–4) (2004), 461–480.

Moubariz Z. Garaev, Florian Luca and Igor E. Shparlinski. [Character sums and congruences with $`n!`$](https://doi.org/10.1090/S0002-9947-04-03612-8). *Transactions of the American Mathematical Society* **356** (12) (2004), 5089–5102. arXiv:math/0403422.

</div>
