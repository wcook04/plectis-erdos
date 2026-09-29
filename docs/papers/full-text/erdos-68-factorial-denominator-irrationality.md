<a id="erdos-68-factorial-denominator-irrationality"></a>

# Integer Linear Forms for a Factorial Reciprocal Series

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We construct an integral basis for finitely supported integer sequences under factorial-weighted linear forms. It classifies cancellation of a prescribed initial segment and reduces the attainable factorial moments, with support on indices at least two, to a finite gcd. We obtain the least positive moment $`1380`$ at depth four and construct primitive solutions on arithmetic progressions. Their remainders are integer linear forms in $`S=\sum_{n\ge2}(n!-1)^{-1}`$. Applying them to irrationality requires nonintegral remainders whose moments cover every positive denominator by divisibility. That step remains open.

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

In the usual proof of the irrationality of $`e`$, multiplying a tail by a factorial gives a positive integer smaller than one under the assumption of rationality. The same multiplier does not clear the partial sums here, since even their last denominator is coprime to it. We consider integer linear forms in $`1`$ and $`S`$, choosing their coefficients to cancel a prescribed initial set of weighted summands. Theorem <a href="#res:divisor-channel-coordinates" data-reference-type="ref" data-reference="res:divisor-channel-coordinates">2</a> gives an integral basis in which these cancellation equations are diagonal. Requiring the coefficient at index one to vanish leaves a single equation in integers, and Theorem <a href="#res:finite-channel-moment-certificate" data-reference-type="ref" data-reference="res:finite-channel-moment-certificate">3</a> reduces its gcd to a finite calculation.

We obtain the basis from adjacent factorial identities by eliminating the proper divisors of each index in turn. Since the construction works for every finite integer coefficient vector, it classifies the solutions without any assumption on $`S`$. At depth four we can compute the least positive moment and then bound a corresponding remainder between consecutive integers, obtaining a denominator exclusion. We also give a family on arithmetic progressions whose moments eventually contain every fixed denominator as a divisor. To apply that family to irrationality, we still need to control the fractional parts of its real linear forms.

The classical factorial-series criteria are relevant to a different part of the argument. Hančl and Tijdeman’s tail integrality lemma \[hancl-tijdeman, Lemma 2.1 and the following remark, p. 385\] underlies the comparison with an integer. Cantor’s expansion criterion, as presented by Galambos \[galambos1976, Ch. II, §2.1\] and illustrated by Koepf and Schmersau \[koepf-schmersau, Example 3.2\], explains the carry and digit criteria below. These criteria leave an eventual or unbounded assertion about this particular series to be proved.

Sections <a href="#sec:channels" data-reference-type="ref" data-reference="sec:channels">2</a>–<a href="#sec:compressed-kernel" data-reference-type="ref" data-reference="sec:compressed-kernel">5</a> develop the coefficient construction. Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">6</a> states the required real comparison, and Section <a href="#sec:finite" data-reference-type="ref" data-reference="sec:finite">7</a> gives the carry criterion and two recorded finite exclusions. The appendices treat reduced denominators and the factorial digits of $`S-e+2`$.

<a id="sec:channels"></a>

# An integral basis

For integers $`d\ge2`$ and $`n\ge1`$, put
``` math
W_{d,n}=\frac{n!}{(d!)^{\lfloor n/d\rfloor}}.
```
Writing $`n=kd+r`$, with $`0\le r<d`$, we see that $`W_{d,n}`$ is integral: it is $`r!`$ times the multinomial coefficient $`n!/((d!)^k r!)`$. Moreover, $`n!=(d!)^kW_{d,n}`$ and $`d!\equiv1\pmod{d!-1}`$ give $`W_{d,n}\equiv n!\pmod{d!-1}`$, so replacing $`n!`$ by this weight preserves the fractional part over $`d!-1`$. For example, $`W_{3,4}=4`$, and $`(24-4)/5=4`$.

For a finitely supported integer vector $`\lambda=(\lambda_n)_{n\ge1}`$, we define its factorial moment and weighted sums by
``` math
M(\lambda)=\sum_n\lambda_n n!,\qquad
 V_d(\lambda)=\sum_n\lambda_nW_{d,n},
```
and let
``` math
\mathcal R(\lambda)=\sum_{d\ge2}\frac{V_d(\lambda)}{d!-1}.
```
If $`N\ge2`$ contains the support, then $`V_d=M`$ for $`d>N`$, proving absolute convergence of this series. Using the congruence for the weights in its finitely many remaining terms, we obtain
``` math
\begin{equation}
 \mathcal R(\lambda)-M(\lambda)S
 =\sum_{d=2}^N\frac{V_d(\lambda)-M(\lambda)}{d!-1}\in\mathbb Z.
 \label{eq:integer-linear-form}
\end{equation}
```
We shall solve $`V_2=\cdots=V_D=0`$ over the integers. We allow either sign for the moment and write $`e_n`$ for the unit vector at index $`n`$. The auxiliary index one simplifies the basis calculation, but introduces no term $`1/(1!-1)`$ into the series: to recover vectors supported on indices at least two, we shall set its coefficient to zero.

Because $`\lfloor n/d\rfloor`$ changes only at multiples of $`d`$, the vector $`4e_3-e_4`$ has only two nonzero weighted sums: $`V_2=6`$ and $`V_4=23`$. We can remove the former by subtracting $`6(2e_1-e_2)`$. The following recursion carries out this elimination at every index.

<div id="res:divisor-channel-coordinates" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos68/PaperCompleteDivisorCoordinates.lean#L260">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-68-factorial-denominator-irrationality.md#res-divisor-channel-coordinates-comparator">Comparator</a></p>

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

*Proof.* The moment of $`T_n`$ is zero. To compute its weighted sums, we compare the consecutive floor exponents, which differ by one when $`d\mid n`$ and otherwise agree. This gives
``` math
V_d(T_n)=(d!-1)W_{d,n}\mathbf1_{d\mid n}.
```
Assuming the assertion for smaller indices, subtracting $`W_{d,n}U_d`$ removes the contribution at a proper divisor $`d`$ and leaves all other weighted sums unchanged. We obtain the required identities by induction, with $`V_n(U_n)=n!-1`$ because $`W_{n,n}=1`$.

For the basis assertion, we check that both changes of coordinates are integral and invertible over $`\mathbb Z`$. On indices $`1,\ldots,N`$, the columns $`e_1,T_2,\ldots,T_N`$ give a triangular matrix with diagonal $`1,-1,\ldots,-1`$, while the change from $`T_n`$ to $`U_n`$ is triangular with diagonal one. Both determinants are units. Applying $`M`$ and each $`V_d`$ to the resulting unique integral expansion determines the coefficients in <a href="#eq:channel-basis-expansion" data-reference-type="eqref" data-reference="eq:channel-basis-expansion">[eq:channel-basis-expansion]</a>; those with $`d>N`$ vanish because $`V_d=M`$. ◻

</div>

At a prime $`p\ge3`$, there are no proper divisors in the recursion, so $`U_p=pe_{p-1}-e_p`$. Composite indices allow the same separate adjustment of one weighted sum; for instance,
``` math
\begin{equation}
 U_9=9e_8-e_9-5040e_2+1680e_3.
 \label{res:translator}
\end{equation}
```
Since each $`U_n`$ has moment zero and remainder one, adding these vectors translates the remainder by an integer. Thus they preserve the fractional part in <a href="#eq:integer-linear-form" data-reference-type="eqref" data-reference="eq:integer-linear-form">[eq:integer-linear-form]</a>.

<a id="sec:moments"></a>

# Attainable moments

Fix an integer $`D\ge2`$ and write
``` math
L_D=\operatorname{lcm}_{2\le d\le D}(d!-1),\qquad
 K_D=L_De_1-\sum_{d=2}^D\frac{L_D}{d!-1}U_d.
```
Reading the integral coefficients in the basis expansion, we obtain
``` math
\begin{equation}
 V_d(\lambda)\equiv M(\lambda)\pmod{d!-1}.
 \label{res:congruence}
\end{equation}
```
Cancellation therefore forces $`L_D\mid M`$, and substituting $`M=tL_D`$ into the expansion gives all solutions:
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

To restrict the support to $`n\ge2`$, let $`a_D=[e_1]K_D`$ and $`u_n=[e_1]U_n`$. The additional condition is the single integer equation
``` math
\begin{equation}
 ta_D+\sum_{n>D}z_nu_n=0.\label{eq:support-equation}
\end{equation}
```
Let $`g_D=\gcd\{u_n:n>D\}`$. The finite integer combinations of these coefficients form $`g_D\mathbb Z`$, so we obtain the attainable moments
``` math
\begin{equation}
 \mu_D\mathbb Z,\qquad
 \mu_D=L_D\frac{g_D}{\gcd(g_D,a_D)}.
 \label{eq:attainable-moment-ideal}
\end{equation}
```
Indeed, <a href="#eq:support-equation" data-reference-type="eqref" data-reference="eq:support-equation">[eq:support-equation]</a> is soluble if and only if $`g_D\mid ta_D`$, and the gcd is itself a finite integer combination of the $`u_n`$. This proves attainment of the positive generator, once we have checked below that $`g_D>0`$. An attaining vector must be primitive, for otherwise division by a common coefficient factor would give a smaller positive moment with the same cancellations.

<a id="sec:finite-gcd"></a>

## A finite gcd calculation

The recursion for the first coordinate is
``` math
u_2=2,\qquad
 u_n=-\sum_{\substack{d\mid n\\2\le d<n}}W_{d,n}u_d\quad(n>2).
```
It gives $`u_n=0`$ at odd indices and $`u_{2p}=-(2p)!/2^{p-1}\ne0`$ for every prime $`p`$, including $`p=2`$. Hence $`g_D>0`$. The following result replaces the infinite tail by a finite interval.

<div id="res:finite-channel-moment-certificate" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-68-factorial-denominator-irrationality.md#res-finite-channel-moment-certificate">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-68-factorial-denominator-irrationality.md#res-finite-channel-moment-certificate-comparator">Comparator</a></p>

**Theorem 3** (a finite formula for the gcd). *Choose a prime $`\ell`$ with $`D/2<\ell\le D`$ and put $`H=D(2\ell-1)`$. Then
``` math
g_D=\gcd(u_{D+1},\ldots,u_H),\qquad H<2D^2.
```*

</div>

<div class="proof">

*Proof.* Let $`g`$ be the gcd on the stated finite interval. That interval contains $`u_{2\ell}=-(2\ell)!/2^{\ell-1}`$, so $`g>0`$ and $`g\mid(2\ell)!`$. For $`n>H`$, a divisor $`d\le D`$ has $`n/d\ge2\ell`$. Moreover,
``` math
(n/d)!\mid W_{d,n}\qquad(d\mid n),
```
because the quotient counts partitions into $`n/d`$ unordered blocks of size $`d`$. Thus $`g\mid W_{d,n}`$ for every such small divisor. In the remaining terms of the recurrence, $`D<d<n`$, strong induction gives $`g\mid u_d`$. It follows that $`g`$ divides every coefficient beyond $`H`$, proving the equality of gcds. Finally $`H\le D(2D-1)<2D^2`$. ◻

</div>

Bertrand’s postulate supplies $`\ell`$ for $`D\ge3`$, and $`\ell=2`$ works for $`D=2`$. The argument gives the stated horizon $`H`$; it does not justify replacing it by $`2D`$.

<a id="sec:depth-four"></a>

## Depth four

For $`D=4`$, one has $`L_4=115`$, $`a_4=-55`$ and $`g_4=60`$, hence $`\mu_4=1380`$. The gcd calculation uses $`23u_6-u_8=60`$ and
``` math
\begin{equation}
 \operatorname{lcm}(1,\ldots,n)\mid u_n.
 \label{eq:channel-lcm-envelope}
\end{equation}
```
The companion record gives the [Legendre-formula proof and the full moment calculation](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r12-moment). For this particular depth, the following elementary congruence provides a shorter proof of minimality:
``` math
\begin{equation}
 1380\mid 11n!-46W_{2,n}+12W_{4,n}\qquad(n\ge2).
 \label{eq:depth-four-dual}
\end{equation}
```
The expression is zero for $`n=2,3,4`$. For $`n\ge4`$, each summand is divisible by $`12`$, using $`W_{2,2r}=r!\prod_{j=1}^r(2j-1)`$ and $`W_{2,2r+1}=(2r+1)W_{2,2r}`$. For $`n\ge5`$, removing powers of $`2`$ or $`24`$ from $`n!`$ preserves divisibility by $`5`$. Finally $`n!\equiv W_{4,n}\pmod{23}`$ and $`46W_{2,n}\equiv0\pmod{23}`$. The pairwise coprime factors $`12,5,23`$ prove the congruence.

Summing <a href="#eq:depth-four-dual" data-reference-type="eqref" data-reference="eq:depth-four-dual">[eq:depth-four-dual]</a> against $`\lambda_n`$ shows that $`V_2=V_4=0`$ forces $`1380\mid M`$, since $`\gcd(11,1380)=1`$. Equality is attained with $`V_3=0`$ as well:
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

The additional condition $`V_3=0`$ therefore preserves the attainable moments, though it restricts the vectors: $`3e_2-e_3`$ has $`M=V_2=V_4=0`$ and $`V_3=5`$. Index eight is also necessary to attain $`1380`$. For $`n\le7`$, the expression in <a href="#eq:depth-four-dual" data-reference-type="eqref" data-reference="eq:depth-four-dual">[eq:depth-four-dual]</a> is zero through $`n=5`$ and equals $`4140,7\cdot4140`$ at $`n=6,7`$. Thus support at most seven and $`V_2=V_4=0`$ force $`4140\mid M`$.

This vector already gives a nonintegral remainder. Equation <a href="#eq:residual-transparency" data-reference-type="eqref" data-reference="eq:residual-transparency">[eq:residual-transparency]</a> yields $`\mathcal R(\lambda)=1380(S-H_4)-44`$, and rational arithmetic gives
``` math
-31+\frac45
 <1380\sum_{d=5}^{8}\frac1{d!-1}-44
 <-31+\frac56,
 \qquad \frac{2\cdot1380}{9!-1}<\frac1{100}.
```
The tail from $`d=9`$ is less than $`2/(9!-1)`$, so $`-31<\mathcal R(\lambda)<-30`$. By <a href="#eq:integer-linear-form" data-reference-type="eqref" data-reference="eq:integer-linear-form">[eq:integer-linear-form]</a>, every divisor of $`1380`$ is excluded as a denominator of $`S`$. This small example illustrates the construction; the finite calculations in Section <a href="#sec:finite" data-reference-type="ref" data-reference="sec:finite">7</a> give stronger exclusions.

<a id="sec:translator"></a>

# The cost of cancellation

On support $`n\ge2`$, the weights satisfy $`12\mid M-2V_2`$. For $`n=2,3`$ we have $`n!=2W_{2,n}`$, and for $`n\ge4`$ both terms are divisible by $`12`$. Since every $`d!-1`$ is coprime to $`6`$, cancellation gives
``` math
\begin{equation}
 12L_D\mid M.\label{eq:twelve-lcm}
\end{equation}
```
This need not be the least positive moment: at $`D=6`$ it is $`24L_6`$. Nor do these compulsory factors alone cover all denominators, since $`9\nmid12L_D`$ for every $`D`$.

A restriction on the support follows directly from the floor in the weights.

<div id="res:bandbreakpoint" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-68-factorial-denominator-irrationality.md#res-bandbreakpoint">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-68-factorial-denominator-irrationality.md#res-bandbreakpoint-comparator">Comparator</a></p>

**Theorem 4** (constant values of the floor in the weights). *Let $`\lambda`$ be a finitely supported integer vector, let $`d\ge2`$ and $`k\ge0`$ be integers, and suppose each index $`n`$ in its support satisfies $`kd\le n<(k+1)d`$. Then
``` math
M(\lambda)=(d!)^k V_d(\lambda).
```
In particular, support in $`[d,2d)`$ and $`V_d(\lambda)=0`$ force $`M(\lambda)=0`$. If all supported indices are at least $`d`$, $`V_d(\lambda)=0`$ and $`M(\lambda)\ne0`$, some supported index is at least $`2d`$.*

</div>

<div class="proof">

*Proof.* On the indicated interval, $`n!=(d!)^kW_{d,n}`$. Summing against $`\lambda_n`$ proves the identity. If all support lies at or above $`d`$ but below $`2d`$, its case $`k=1`$ proves the final assertion by contraposition. ◻

</div>

The compulsory common denominator also has the lower bound
``` math
\begin{equation}
 \liminf_{N\to\infty}\frac{\log L_N}{N^{3/2}\log N}
 \ge\frac{2\sqrt2}{3}.
 \label{res:lcm-growth}
\end{equation}
```
To prove it, subtract suitable multiples of two shifted factorials: $`\gcd(i!-1,j!-1)\mid j!/i!-1`$ for $`i<j`$. This is the constant-shift case of the argument of Luca and Shparlinski \[luca-shparlinski, proof of Lemma 5, p. 811\], also used by Lai \[lai, proof of Lemma 2.4, (2.5)\]; shared prime powers were used in spacing arguments by Erdős and Stewart \[erdos-stewart1976, §3\].

For positive integers $`x_i`$, comparison of prime valuations gives $`\prod_i x_i\mid\operatorname{lcm}(x_i)\prod_{i<j}\gcd(x_i,x_j)`$. Applying this to the last $`k`$ denominators before $`N`$ yields
``` math
\log L_N\ge\sum_{n=N-k+1}^N\log(n!-1)
              -\binom{k+1}{3}\log N.
```
For $`k=\lfloor\alpha\sqrt N\rfloor`$, Stirling’s formula makes the normalised lower bound tend to $`\alpha-\alpha^3/6`$. Taking $`\alpha=\sqrt2`$ gives <a href="#res:lcm-growth" data-reference-type="eqref" data-reference="res:lcm-growth">[res:lcm-growth]</a>. The companion record [gives the error estimates and the extension to a fixed nonzero polynomial shift](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r12-lcm), using the eventual nonvanishing lemma attributed by Lai \[lai, Lemma 2.1\] to Luca and Shparlinski. The shift $`n!+2^n-1`$ requires a different elimination \[luca-shparlinski-exp, Lemmas 2.1–2.3\].

These estimates concern a common denominator before reduction. They do not imply smallness of a scaled tail. In fact $`(N-1)!-1`$ and $`N!-1`$ are coprime: a common divisor divides $`N-1`$ by subtraction and is coprime to $`N-1`$. Hence
``` math
L_N(S-H_N)>
 \frac{((N-1)!-1)(N!-1)}{(N+1)!-1}\longrightarrow\infty.
```
Clearing the full common denominator therefore fails even at this simpler level. Reduced denominators require the separate cancellation test in Appendix <a href="#sec:prime-pole" data-reference-type="ref" data-reference="sec:prime-pole">8</a>.

<a id="sec:compressed-kernel"></a>

# Solutions on an arithmetic progression

Let $`D,r\ge2`$, and let $`\ell`$ be a positive multiple of $`2,\ldots,D`$. We can solve the cancellation equations on $`D`$ equally spaced indices. Put
``` math
i_j=r+j\ell\ (0\le j<D),\quad N=r+(D-1)\ell,\quad
 \alpha_d=(d!)^{\ell/d},\quad A=\prod_{d=2}^D\alpha_d,
```
and define $`h_j`$ and the supported coefficients by
``` math
\prod_{d=2}^D(\alpha_dX-1)=\sum_{j=0}^{D-1}h_jX^j,
 \qquad c_{i_j}=\frac{N!h_j}{A i_j!}.
```
All other coefficients are zero. A term of $`h_j/A`$ is, up to sign, the reciprocal of a product of $`D-1-j`$ distinct $`\alpha_d`$. Interpret each factor as $`\ell/d`$ blocks of size $`d`$. Together with one block of size $`i_j`$, their total size is $`N`$, so the multinomial coefficient proves that each contribution to $`c_{i_j}`$ is integral. Also $`c_N=1`$, proving primitivity.

Equal spacing turns cancellation into a polynomial root condition:
``` math
V_d(c)=\frac{N!}{A(d!)^{\lfloor r/d\rfloor}}
          \sum_{j=0}^{D-1}h_j\alpha_d^{-j}=0
 \qquad(2\le d\le D).
```
Evaluation at one gives
``` math
\begin{equation}
 M=N!\prod_{d=2}^D(1-1/\alpha_d),\qquad 0<M<N!.
 \label{eq:progression-moment}
\end{equation}
```
Taking $`D=r=\ell=2`$, we recover $`-6e_2+e_4`$, with moment $`12`$. The construction gives solutions without asserting that their support is minimal.

Counting the equal blocks without ordering blocks of the same size gives
``` math
\frac{N!}{r!A\prod_{d=2}^D(\ell/d)!}\in\mathbb Z.
```
Thus $`r!\prod_{d=2}^D(\ell/d)!`$ divides $`M`$. For $`v=\max(r,\ell/2)`$ we obtain $`v!\mid M`$, while $`D\le\ell\le2v`$ gives $`N\le4v^2-v<4v^2`$. In particular,
``` math
\begin{equation}
 (\lfloor\sqrt N/2\rfloor+1)!\mid M,
 \qquad N\ge4(q-1)^2\ \Longrightarrow\ q\mid M.
 \label{eq:progression-divisibility}
\end{equation}
```
We have therefore supplied the divisibility required for each fixed denominator. To exclude it, we must also prove nonintegrality of a remainder from this same family.

<a id="sec:open"></a>

# Nonintegrality of the remainder

<span id="sec:plateau" label="sec:plateau"></span> <span id="r12-short-gap"></span>

Suppose $`V_2=\cdots=V_D=0`$ and $`M>0`$, and choose $`N\ge D`$ containing the support. The finite signed part is
``` math
A_N=\sum_{d=D+1}^N\frac{V_d(\lambda)}{d!-1},\qquad
 \mathcal R(\lambda)=A_N+M(S-H_N).
```
Since $`0<S-H_N<2/((N+1)!-1)`$, the comparison
``` math
\begin{equation}
 \frac{2M}{(N+1)!-1}<\lfloor A_N\rfloor+1-A_N
 \label{eq:signed-block-gap}
\end{equation}
```
places $`\mathcal R(\lambda)`$ strictly between consecutive integers and excludes every denominator dividing $`M`$. We place no sign condition on $`A_N`$: at an integer its strict gap is one, whereas just below an integer that gap can be arbitrarily small.

At the endpoint of a progression vector, <a href="#eq:progression-moment" data-reference-type="eqref" data-reference="eq:progression-moment">[eq:progression-moment]</a> already gives $`0<M(S-H_N)<2/N`$. The gap on the right of <a href="#eq:signed-block-gap" data-reference-type="eqref" data-reference="eq:signed-block-gap">[eq:signed-block-gap]</a> may tend to zero as well. An irrationality proof by these vectors needs, for each $`q>0`$, a vector with $`q\mid M`$ for which the comparison succeeds. Unbounded moments without this divisibility coverage are insufficient.

We may take the cutoff beyond the support endpoint without changing the vector. For instance, with $`-6e_2+e_4`$ the comparison fails at $`N=4`$ because $`9/115<24/119`$, but succeeds at $`N=5`$ because $`13376/13685>24/719`$. For any fixed vector with $`M>0`$, it succeeds at all sufficiently large cutoffs exactly when the remainder is nonintegral. Indeed, $`A_N`$ increases to $`\mathcal R`$; if the limit is nonintegral its gap to the next integer is positive, whereas at an integral limit the eventual gap is the omitted tail itself. Increasing the cutoff cannot change the moment or supply a new denominator divisibility.

<a id="sec:nogo"></a>

#### Short cutoffs.

<span id="sec:adjacent-unit-no-go" label="sec:adjacent-unit-no-go"></span> As $`D\to\infty`$, the test cannot succeed with $`N=D+O(1)`$: the left side tends to infinity by $`L_D\mid M`$ and <a href="#res:lcm-growth" data-reference-type="eqref" data-reference="res:lcm-growth">[res:lcm-growth]</a>, while the right side is at most one. This restricts support only when the cutoff is required to equal its endpoint. Nor does a large prime-power denominator guarantee a useful gap: the reduced fraction $`1-1/q^e`$ has gap $`1/q^e`$ to the next integer.

<a id="sec:finite"></a>

# Carries and finite denominator exclusions

A second approach uses the strict successor of a scaled partial sum. For $`m\ge2`$ put
``` math
H_m=\sum_{n=2}^m\frac1{n!-1},\qquad
 Z_m=\lfloor m!H_m\rfloor+1,
```
and for $`m\ge3`$ put $`b_m=mZ_{m-1}+1-Z_m`$. The strict successor convention includes the case of an integral prefix. For $`n\ge3`$, the inequality $`1/(n!-1)<(n-1)/n!`$ telescopes to $`0<m!(S-H_m)<1`$. Therefore
``` math
\begin{equation}
 S=a/q,\quad q\mid(m-1)!,\quad m\ge3
 \quad\Longrightarrow\quad Z_m=m!S=mZ_{m-1},\quad b_m=1.
 \label{eq:finite-denominator-consumer}
\end{equation}
```
Here the scaled *limit* is integral, although the scaled partial sum need not be. A non-unit carry excludes divisors of $`(m-1)!`$ and forces every rational denominator to be at least $`m`$.

<div id="res:carry-characterization" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L45">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-68-factorial-denominator-irrationality.md#res-carry-characterization-comparator">Comparator</a></p>

**Theorem 5** (exact carry characterisation). *<span id="res:strict-successor-complete-characterization" label="res:strict-successor-complete-characterization"></span> The following conditions are equivalent:
``` math
S\notin\mathbb Q,\qquad
(\forall B)(\exists m>B)\ b_m\ne1,\qquad
(\forall B)(\exists m>B)\ m\nmid Z_m.
```
In particular, [cofinal non-unit carries imply irrationality](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos68/FactorialZeroPlateau.lean#L953); equivalently, the original problem is the [criterion using the next integer](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos68/FactorialZeroPlateau.lean#L1090).*

</div>

<div class="proof">

*Proof.* A rational $`S`$ has eventual unit carries by <a href="#eq:finite-denominator-consumer" data-reference-type="eqref" data-reference="eq:finite-denominator-consumer">[eq:finite-denominator-consumer]</a>. Conversely, eventual unit carries make $`Z_m/m!`$ eventually constant. The inequalities $`H_m<Z_m/m!\le H_m+1/m!`$ identify this rational constant with $`S`$. Finally, writing $`x=(m-1)!H_{m-1}`$ gives
``` math
b_m=m-1-\lfloor m\{x\}+1/(m!-1)\rfloor,\qquad -1\le b_m\le m-1.
```
Together with $`Z_m=mZ_{m-1}+1-b_m`$, this range shows that $`m\mid Z_m`$ if and only if $`b_m=1`$ for $`m\ge3`$. ◻

</div>

The unresolved assertion can thus be written
``` math
\begin{equation}
 (\forall B)(\exists m>B)\ m\nmid Z_m.
 \label{eq:canonical-open-target}
\end{equation}
```
A single computed non-unit carry gives only a finite denominator exclusion. The recorded exact GMP calculation through $`m=300000`$ has unit carries
``` math
52,\ 591,\ 1030,\ 1407,\ 1438,\ 2164,\ 4258,\ 10991,\ 21236.
```
Its non-unit endpoint gives $`q\nmid299999!`$. This does not exclude all $`299999`$-smooth denominators: a sufficiently high power of a small prime need not divide that factorial. Equivalently, the least $`r>0`$ with $`q\mid r!`$ is at least $`300000`$, the factorial index used by Sondow for $`e`$ \[sondow2006, §3, Theorem 1\]; his approximation bound is not being applied to $`S`$.

<a id="sec:continued-fractions"></a>

## A continued-fraction exclusion

Put $`B=2^{80000}`$, let $`N`$ be the first integer with $`N!-1>B`$, and define
``` math
\ell=\sum_{n=2}^{N-1}\left\lfloor\frac B{n!-1}\right\rfloor,
 \qquad u=\ell+(N-2)+\left\lfloor\frac{2B}{N!-1}\right\rfloor+1.
```
Rounding the prefix loses less than $`N-2`$, and the omitted tail is less than $`2/(N!-1)`$. Thus $`\ell/B<S<u/B`$ strictly. The recorded integer calculation gives $`N=7054`$, $`u-\ell=7053`$ and $`23449`$ common partial quotients $`a_0,\ldots,a_{23448}`$ for the two endpoints. Their denominators satisfy
``` math
Q_{-2}=1,\quad Q_{-1}=0,\quad Q_j=a_jQ_{j-1}+Q_{j-2},
 \qquad Q_{23448}\ge2^{39990}>10^{12038}.
```
At each step, the algorithm retains a common integer part only while both remainders are nonzero, then inverts and reverses the endpoints. Every rational in the open interval has the common initial segment. A continuation $`x/y>1`$ after $`P_j/Q_j`$ has reduced denominator $`Q_jx+Q_{j-1}y\ge Q_j`$; termination at the convergent gives $`Q_j`$. Reducedness follows from $`P_jQ_{j-1}-P_{j-1}Q_j=\pm1`$ \[nist-dlmf, §1.12(ii)\]. Hence every representation $`S=a/q`$, reduced or otherwise, has $`q\ge2^{39990}`$.

The two restrictions are incomparable: the prime $`300007`$ satisfies $`q\nmid299999!`$ but fails the size bound, whereas $`299999!`$ does the reverse. Both large calculations are outside Lean. The companion record [identifies their programs and recorded outputs](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r12-finite), the separate carry calculation through $`4000`$, and the kernel-checked non-unit carry at $`67`$. None establishes <a href="#eq:canonical-open-target" data-reference-type="eqref" data-reference="eq:canonical-open-target">[eq:canonical-open-target]</a>.

<a id="sec:prime-pole"></a>

# Reduced denominators

Addition may remove a prime from a common denominator, as in $`1/3+1/15=2/5`$, or merely lower its exponent, as in $`1/9+1/45=2/15`$. The following reciprocal-sum test is the elementary-symmetric-sum valuation formula of Louwsma and Martino \[louwsma-martino, Lemma 4.1, p. 10\] after division by the product of the arguments.

Write $`v_q`$ for the exponent of a prime $`q`$ and $`\operatorname{den}`$ for the positive reduced denominator. Let $`A_M=\sum_{n=2}^M L_M/(n!-1)`$, and suppose $`e=\max_{2\le n\le M}v_q(n!-1)>0`$. If $`I_{q,e}(M)`$ is the set where this maximum is attained, put
``` math
R_{q,e}(M)=\sum_{n\in I_{q,e}(M)}
 \left((n!-1)/q^e\right)^{-1}\pmod q.
```
All lower-valuation terms vanish when $`A_M`$ is reduced modulo $`q`$, so $`A_M\equiv(L_M/q^e)R_{q,e}(M)\pmod q`$. The factor $`L_M/q^e`$ is a unit, and therefore
``` math
\begin{equation}
 v_q(\operatorname{den}H_M)=e
 \quad\Longleftrightarrow\quad R_{q,e}(M)\ne0\pmod q.
 \label{eq:prime-pole-survival}
\end{equation}
```
In general the surviving exponent is $`\max(0,e-v_q(A_M))`$. A zero residue lowers it; complete cancellation requires $`v_q(A_M)\ge e`$.

Actual cancellation occurs. For $`q=139`$ the maximal exponent is one at indices $`69,122,137`$, with cofactor residues $`6,49,73`$ and reciprocal sum zero. For $`q=2593`$ the indices are $`349,2243,2591`$, with cofactor residues $`1508,1566,1678`$ and reciprocal sum zero. Each prime disappears completely. These cancellations persist, since no term after index $`q-2`$ has a denominator divisible by $`q`$: Wilson’s theorem handles $`q-1`$, and $`n!\equiv0\pmod q`$ handles $`n\ge q`$. The conclusion concerns finite partial sums. Spacing bounds \[stewart2004, Lemma 2\] and factorial value multiplicities \[garaev-luca-shparlinski, arXiv v1, Theorem 12\] do not supply the real-tail comparison for $`S`$.

<a id="sec:projection"></a>

## A sufficient inequality

We can clear all prime-power levels shared by two summand denominators and retain the remaining unique maxima. For an integer $`p\ge3`$, which need not be prime, put $`d_n=n!-1`$ and
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
For each prime dividing $`R_p`$, exactly one summand in $`T_p`$ is a unit modulo that prime. Thus $`\gcd(T_p,R_p)=1`$ and $`R_p=\operatorname{den}(C_pH_{2p-1})`$, without any coprimality assumption on $`C_p,R_p`$. If $`R_p>1`$, the strict gap to the next integer is $`\rho_p/R_p>0`$. If $`R_p=1`$, the gap is one although $`\rho_p=0`$.

<div id="res:global-complementary-criterion" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L154">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-68-factorial-denominator-irrationality.md#res-global-complementary-criterion-comparator">Comparator</a></p>

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

*Proof.* Suppose $`S=a/q`$ and choose an admissible $`p>q`$. Since $`q\mid F_p\mid C_p`$, the integer $`C_pS`$ lies strictly above $`C_pH_{2p-1}`$, so its distance is at least $`\rho_p/R_p`$. But a geometric majorant gives
``` math
C_p(S-H_{2p-1})<\frac{(2p+1)C_p}{2p^2(2p-1)!}<\frac{\rho_p}{R_p},
```
a contradiction. The first inequality uses $`1/(n!-1)<2/n!`$ for $`n\ge2p`$ and ratio $`1/(2p+1)`$; the second is the hypothesis. ◻

</div>

For $`p=3`$, we have $`C_3=2`$, $`C_3H_5=34264/13685`$ and gap $`6791/13685`$, exceeding the tail bound $`7/1080`$. No unbounded family satisfying the hypothesis is established. Equivalently, one needs
``` math
\begin{equation}
 \log\frac{C_p}{(p-1)!}-\log\frac{\rho_p}{R_p}
 <\log\frac{2p^2(2p-1)!}{(2p+1)(p-1)!}
 =p\log p+(2\log2-1)p+O(\log p).
 \label{eq:joint-loss-budget}
\end{equation}
```
The equality on the right is an asymptotic evaluation; the strict comparison is with the exact logarithm. Nonzero residues give no uniform lower bound for the gap. Estimates for the clearing factor and for the gap must hold at the same indices. Requiring an additional prime $`q\mid R_p`$ and $`(2p+1)C_pq<2p^2(2p-1)!`$ imposes a further restriction.

<a id="sec:companion-orbit"></a>

# The factorial digits of $`S-e+2`$

The termwise identity $`1/(n!-1)=1/n!+1/(n!(n!-1))`$ gives
``` math
\begin{equation}
 C+(e-2)=S,\qquad C=\sum_{n\ge2}\frac1{n!(n!-1)}.
 \label{eq:companion-decomposition}
\end{equation}
```
All series converge absolutely. Define the canonical digits by
``` math
d_m(C)=\lfloor m!C\rfloor-m\lfloor(m-1)!C\rfloor,\qquad 0\le d_m(C)<m.
```
The convention excludes eventually maximal alternatives, such as $`1/2=\sum_{m\ge3}(m-1)/m!`$ instead of $`1/2!`$. Cantor’s criterion \[cantor1869\] says that a rational number has eventually zero canonical digits. In the present decomposition, rationality of $`S`$ corresponds to the eventual digit $`m-2`$ for $`C`$.

<div id="res:companion-orbit-rationality-boundary" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L27">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-68-factorial-denominator-irrationality.md#res-companion-orbit-rationality-boundary-comparator">Comparator</a></p>

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

Conversely, the congruence forces $`d_m(C)=m-2`$ for all sufficiently large $`m\ge3`$. Choose $`N`$ beyond the exceptions. Adding the factorial expansion of $`e-2`$ to the canonical expansion of $`C`$, and using $`\sum_{m>N}(m-1)/m!=1/N!`$, gives
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

The digit uses the full $`C`$, whereas the carry uses a partial sum. Set
``` math
\delta_m=m!\sum_{n>m}\frac1{n!(n!-1)},\qquad
 \sigma_m=\mathbf1_{\{\{m!C\}<\delta_m\}}.
```
Here $`\{x\}=x-\lfloor x\rfloor`$. Comparison with the factorial tail gives $`0<\delta_m<1/((m+1)!-1)<1`$. Subtracting it lowers the floor by $`\sigma_m`$, whence
``` math
Z_m=m!\sum_{n=2}^m\frac1{n!}+\lfloor m!C\rfloor+1-\sigma_m.
```
Substitution into the carry recurrence yields
``` math
\begin{equation}
 b_m=m-1-d_m(C)+\sigma_m-m\sigma_{m-1}\qquad(m\ge3).
 \label{eq:companion-wrap}
\end{equation}
```
At equality $`\{m!C\}=\delta_m`$, the prefix is integral and the correction is zero. A smaller fractional part crosses an integer, however small the tail. Neither indicator can be discarded on grounds of tail size.

<a id="app:sources"></a>

# Verification and related estimates

*Formal proofs.* A result with a kernel-checked Lean proof carries a mark in the margin. *Lean* opens the proof: the declaration itself when one declaration states the whole result, otherwise the list of declarations that together state it. *Comparator* opens the record of an independent check, in which the same statement, written again from Mathlib alone in a separate repository, was compared with our proof by Lean’s Comparator tool, allowing only the three standard axioms. A dagger on the Lean mark means that the Lean proof assumes an input named just below the result. A result without a mark has no Lean proof of its whole statement; what is checked is said below it. The [evidence record](https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-68-factorial-denominator-irrationality.md) gives every declaration, version and check. These checks show that the stated propositions are proved; whether they are the right propositions is a question the reader can settle by comparing them with the text.

The marks concern the recorded statements and comparisons. The moment $`1380`$ and full-tail divisibility <a href="#eq:channel-lcm-envelope" data-reference-type="eqref" data-reference="eq:channel-lcm-envelope">[eq:channel-lcm-envelope]</a> have ordinary proofs with exact arithmetic checks; generic formal gcd lemmas assume that divisibility. Individual declarations and their original revisions are listed in the [companion source concordance](../../../paper/68/erdos68-factorial-reasoning-surface.pdf#nameddest=r12-short-sources). Section <a href="#sec:finite" data-reference-type="ref" data-reference="sec:finite">7</a> distinguishes the two recorded large computations from kernel checks.

Denominator savings also occur in the $`p`$-adic linear forms of Lai, Lupu and Sprang \[lai-lupu-sprang, §5, Lemma 7.3 and (8.1)\]. Their irrationality criterion \[lai-lupu-sprang, Lemma 2.1\], quoted from Lai \[lai-2adic, Lemma 2.1\], requires nonzero integer-coefficient forms whose $`p`$-adic absolute values times the largest ordinary coefficient size tend to zero on the same unbounded subsequence. For a prefix here, the saving is $`L_M/\operatorname{den}(H_M)`$; its required asymptotic size has not been established. This comparison applies no $`p`$-adic zeta theorem to $`S`$.

In the companion, the cofactor construction with positive starting parameter recovers the progression vector up to sign. Nonintegrality with least support index tending to infinity is equivalent to irrationality. Tests using adjacent unit carries, lower-endpoint intervals or $`p^2\mid Z_{2p}`$ still require a same-index comparison; non-unit carries at arbitrarily large $`2p`$, for odd primes $`p`$, suffice. Fixed denominator factors eventually divide the removed factorial. These restrictions concern the stated applications of the identities.

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
