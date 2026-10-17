<a id="erdos257-expository-sums-never-fractions"></a>

# Why certain sums of 1/(2^n-1) are irrational

*Authorship and AI use.* Will Cook built and directed the research infrastructure and reviewed the claims when he could. AI agents did most of the research and drafting. Cook did not independently verify every claim. Appendix [9.6](#app%3Alean) identifies the linked formal proof and the limits of its coverage of this exposition.

<a id="sec:intro"></a>

# The question: which infinite sums are irrational?

Every finite sum of fractions is a fraction. An infinite sum can be one too:
``` math
\frac12+\frac14+\frac18+\dots=1.
```
Now consider
``` math
S=\frac13+\frac1{15}+\frac1{255}+\frac1{65535}+\dots,
```
where the denominators are $`2^2-1,2^4-1,2^8-1,2^{16}-1,\dots`$. The exponents double at each step. We will prove that this sum cannot equal any fraction.

Multiply by $`255`$, the third denominator:
``` math
\begin{aligned}
 255S&=85+17+1+\frac{255}{65535}+\dots\\
     &=103+\frac1{257}+\dots.
\end{aligned}
```
The first three terms have become the integer $`103`$, leaving a positive remainder. If $`S=p/q`$, with integers $`p,q`$ and $`q>0`$, multiplying by an integer and subtracting an integer leaves an integer multiple of $`1/q`$. A positive remainder must therefore be at least $`1/q`$. We will repeat the construction to make the *whole* remainder smaller than this fixed gap, whatever denominator $`q`$ is proposed.

This example belongs to a larger family. Its fractions are obtained by taking a power of $`2`$, subtracting $`1`$, and taking the reciprocal:

<div class="center">

|  |  |  |  |  |  |  |  |
|:---|---:|---:|---:|---:|---:|---:|:--:|
| exponent $`n`$ | $`1`$ | $`2`$ | $`3`$ | $`4`$ | $`5`$ | $`6`$ | $`\dots`$ |
| $`2^n`$ | $`2`$ | $`4`$ | $`8`$ | $`16`$ | $`32`$ | $`64`$ | $`\dots`$ |
| denominator $`2^n-1`$ | $`1`$ | $`3`$ | $`7`$ | $`15`$ | $`31`$ | $`63`$ | $`\dots`$ |
| term $`1/(2^n-1)`$ | $`1`$ | $`\tfrac13`$ | $`\tfrac17`$ | $`\tfrac1{15}`$ | $`\tfrac1{31}`$ | $`\tfrac1{63}`$ | $`\dots`$ |

</div>

Choose infinitely many of these terms, each at most once, and add them. Choosing the terms is equivalent to choosing a set $`A`$ of positive integer exponents. The opening example uses $`A=\{2,4,8,16,\dots\}`$; choosing all even exponents instead gives
``` math
A=\{2,4,6,8,\dots\}:\qquad
 \frac13+\frac1{15}+\frac1{63}+\frac1{255}+\dots.
```
The exponent $`0`$ is excluded, since $`2^0-1=0`$. We write
``` math
S_A=\sum_{n\in A}\frac1{2^n-1}.
```
The symbol $`\sum_{n\in A}`$ means that we add the terms whose exponents belong to $`A`$, taking those exponents in increasing order. A *partial sum* stops after finitely many selected terms. Here *irrational* means that $`S_A`$ cannot equal $`p/q`$ for integers $`p,q`$ with $`q>0`$.

For the geometric series at the start, the partial sums are

<div class="center">

|  |  |  |  |  |
|:---|:--:|:--:|:--:|:--:|
| number of terms $`N`$ | $`1`$ | $`2`$ | $`3`$ | $`4`$ |
| $`\tfrac12+\dots+\tfrac1{2^N}`$ | $`\tfrac12`$ | $`\tfrac34`$ | $`\tfrac78`$ | $`\tfrac{15}{16}`$ |
| gap to $`1`$ | $`\tfrac12`$ | $`\tfrac14`$ | $`\tfrac18`$ | $`\tfrac1{16}`$ |

</div>

In general the partial sum is $`1-2^{-N}`$. Its gap to $`1`$ tends to zero, which is precisely the assertion $`\tfrac12+\tfrac14+\tfrac18+\dots=1`$.

Every series $`S_A`$ converges: for $`n\ge1`$,
``` math
0<\frac1{2^n-1}\le\frac1{2^{n-1}},\qquad
 \sum_{n=1}^{\infty}\frac1{2^{n-1}}=2.
```
The inequality follows from $`2^n-1\ge2^{n-1}`$. Consequently the partial sums of $`S_A`$ increase and are bounded by $`2`$. A basic property of real numbers says that an increasing, bounded sequence has a finite limit (Appendix [9.1](#app%3Asums)). The issue is whether this limit is rational.

<a id="sec:problem"></a>

# Erdős’s question and the theorem

In a 1988 account, Erdős wrote \[erdos1988, p. 105\] (excerpt):

> “let $`n_1<n_2<\dots`$. Is it then true that $`\sum \frac{1}{2^{n_k}-1}`$ is irrational, …”

The indices $`k=1,2,\dots`$ count the chosen exponents $`n_k`$. In these terms, we prove:

<div id="thm:main" class="theorem">

**Theorem 1**. *Let $`n_1<n_2<\dots`$ be an infinite sequence of positive integers. If $`\sum_{k=1}^{\infty}1/n_k<\infty`$, then*
``` math
\sum_{k=1}^{\infty}\frac1{2^{n_k}-1}
```
*is irrational.*

</div>

Taking $`A=\{n_1,n_2,\dots\}`$, this series is exactly $`S_A`$, and the additional hypothesis is exactly $`\sum_{n\in A}1/n<\infty`$. The question for arbitrary infinite $`A`$ remains open \[erdosproblems257\].

The condition concerns the reciprocals of the *exponents*. The conclusion concerns the fractions with denominators $`2^n-1`$. For the doubling exponents, the distinction is visible in one table:

<div class="center">

|  |  |  |  |  |  |
|:---|:--:|:--:|:--:|:--:|:--:|
| chosen exponent $`n`$ | $`2`$ | $`4`$ | $`8`$ | $`16`$ | $`\dots`$ |
| term in the hypothesis, $`1/n`$ | $`\tfrac12`$ | $`\tfrac14`$ | $`\tfrac18`$ | $`\tfrac1{16}`$ | $`\dots`$ |
| term in $`S_A`$, $`1/(2^n-1)`$ | $`\tfrac13`$ | $`\tfrac1{15}`$ | $`\tfrac1{255}`$ | $`\tfrac1{65535}`$ | $`\dots`$ |

</div>

The second row sums to $`1`$. The theorem therefore says that the third row sums to an irrational number. The hypothesis is an additional restriction on $`A`$; it is not needed merely to make $`S_A`$ converge.

We will use the hypothesis in this form: beyond a sufficiently large exponent, the remaining reciprocals $`1/n`$ together add up to less than any positive target we specify. This remaining sum is called a *tail*.

The square exponents $`A=\{1,4,9,16,\dots\}`$ also satisfy the condition. Indeed, for $`m\ge2`$,
``` math
\frac1{m^2}<\frac1{m(m-1)}=\frac1{m-1}-\frac1m,
```
so the comparison sum cancels:
``` math
(1-\tfrac12)+(\tfrac12-\tfrac13)+(\tfrac13-\tfrac14)
 +\dots+(\tfrac1{N-1}-\tfrac1N)=1-\tfrac1N<1.
```
Thus $`\sum_{m=2}^{N}1/m^2<1`$. Hence $`\sum_{m=1}^{\infty}1/m^2`$ converges, and the theorem proves that $`1+\tfrac1{15}+\tfrac1{511}+\tfrac1{65535}+\dots`$ is irrational.

By contrast, choosing every positive integer gives the divergent harmonic series in the hypothesis. Group its terms as $`1`$; $`1/2`$; $`1/3+1/4`$; $`1/5+1/6+1/7+1/8`$; and so on. For example,
``` math
\frac15+\frac16+\frac17+\frac18\ge4\cdot\frac18=\frac12.
```
Every subsequent block doubles the number of terms and halves their smallest value, so again contributes at least $`1/2`$. These repeated contributions make the partial sums unbounded. Even exponents also fail the condition, since their reciprocal sum is half the harmonic series. The theorem makes no assertion for these choices. Infinitude is essential too: $`A=\{2,4\}`$ has a finite reciprocal sum, but $`S_A=\tfrac13+\tfrac1{15}=\tfrac25`$. (Question [1](#chk%3Ahypotheses).)

Erdős proved the theorem in 1968 under the extra assumption that no two chosen exponents share a divisor greater than $`1`$, and stated that this assumption could be removed without supplying the details \[erdos1968, p. 222\]. We explain a proof without that assumption.

The proof has three stages. First, rationality forces a fixed lower bound on certain positive remainders. Next, the denominators $`2^n-1`$ let us calculate those remainders explicitly. Finally, a small average guarantees at least one choice whose *total* remainder is below that lower bound. The doubling exponents show the construction at work before the averaging is needed. The main proof ends in Section [7.2](#sec%3Aallchoices). Appendices [9.1](#app%3Asums)–[9.4](#app%3Aproof) justify the supporting infinite-sum and divisibility facts; they can be read as needed or after the main proof. The other-base extension and formal-proof correspondence are further reading.

<a id="sec:test"></a>

# A rational number has a fixed positive gap

Start with $`2/5`$. Multiplying it by an integer and subtracting an integer always gives an integer multiple of $`1/5`$:
``` math
3\cdot\frac25-1=\frac15,\quad
 4\cdot\frac25-1=\frac35,\quad
 5\cdot\frac25-2=0,\quad
 1\cdot\frac25-1=-\frac35.
```
There is no such value strictly between $`0`$ and $`1/5`$. The denominator fixes a smallest possible positive result.

The same reasoning applies to any fraction. From now on write $`S=S_A`$ for the series belonging to our chosen set $`A`$, and suppose $`S=p/q`$, where $`p\in\mathbb Z`$ and $`q`$ is a positive integer. For integers $`u,j`$,
``` math
uS-j=\frac{up-jq}{q}.
```
Its numerator is an integer. If $`uS-j>0`$, then $`up-jq\ge1`$, and therefore
``` math
uS-j\ge\frac1q.
```
Positivity is necessary: zero and negative values do not contradict rationality.

To prove our sum irrational, we will therefore suppose that $`S=p/q`$ and construct integers $`u,j`$, which may depend on $`q`$, satisfying

<a id="eq:goal"></a>

``` math
\begin{equation}
\label{eq:goal}
 0<uS-j<\frac1q.
\end{equation}
```

<a id="sec:split"></a>

# Multiplying the series and retaining fractional parts

We want a multiplier that makes some terms integers. Choose a positive integer $`k`$ and consider $`2^k-1`$. Here $`k`$ is the multiplier exponent; it no longer indexes the list $`n_1,n_2,\dots`$. For example, $`15=2^4-1`$ is divisible by $`3=2^2-1`$. Let us first see exactly what multiplying by $`15`$ does:

<div class="center">

|                |               |                 |              |                 |
|:--------------:|:-------------:|:---------------:|:------------:|:---------------:|
| exponent $`n`$ | original term | multiplied term | integer part | fractional part |
|     $`2`$      |    $`1/3`$    |   $`15/3=5`$    |    $`5`$     |      $`0`$      |
|     $`3`$      |    $`1/7`$    | $`15/7=2+1/7`$  |    $`2`$     |     $`1/7`$     |
|     $`4`$      |   $`1/15`$    |   $`15/15=1`$   |    $`1`$     |      $`0`$      |
|     $`5`$      |   $`1/31`$    |    $`15/31`$    |    $`0`$     |    $`15/31`$    |

</div>

These rows illustrate the operation; in the chosen series we retain only rows with $`n\in A`$. For $`x\ge0`$, its integer part $`\lfloor x\rfloor`$ is the greatest integer at most $`x`$. Subtracting it leaves the fractional part $`\{x\}=x-\lfloor x\rfloor\in[0,1)`$. For example, $`2\le15/7<3`$, so we subtract $`2`$ and retain $`1/7`$. This choice keeps every contribution nonnegative.

<a id="the-remainder-can-be-read-from-the-exponents."></a>

#### The remainder can be read from the exponents.

Keep the denominator $`2^n-1`$ fixed and add $`n`$ to $`k`$. The identity
``` math
2^{k+n}-1=2^k(2^n-1)+(2^k-1)
```
gives
``` math
\frac{2^{k+n}-1}{2^n-1}=2^k+\frac{2^k-1}{2^n-1}.
```
The added term $`2^k`$ is an integer, so the fractional part is unchanged. Write $`k=an+r`$ with $`0\le r<n`$. Repeatedly subtracting $`n`$ from the exponent reduces the calculation to $`r`$. Since $`0\le2^r-1<2^n-1`$,

<a id="eq:fracpart-main"></a>

``` math
\begin{equation}
\label{eq:fracpart-main}
 \ell_n(k):=\left\{\frac{2^k-1}{2^n-1}\right\}
 =\frac{2^{k\bmod n}-1}{2^n-1}.
\end{equation}
```
Here $`k\bmod n`$ denotes the integer remainder $`r`$ in division by $`n`$. It lies between $`0`$ and $`n-1`$; $`\ell_n(k)`$ is the fractional part calculated from it. We will sum these fractional parts to obtain $`R(k)`$. For example, $`8=2\cdot3+2`$, so $`\{255/7\}=(2^2-1)/7=3/7`$. The fractional part is zero exactly when $`n`$ divides $`k`$. Thus the multiplier $`2^k-1`$ turns a selected term into an integer exactly when its exponent divides $`k`$. This is why we chose this multiplier: we can make selected contributions vanish by choosing $`k`$ divisible by their exponents.

<a id="what-happens-to-the-entire-sum."></a>

#### What happens to the entire sum.

Apply the same multiplier to every selected term, subtract each integer part, and sum the fractional parts:
``` math
R(k)=\sum_{n\in A}\ell_n(k),\qquad
 J(k)=\sum_{\substack{n\in A\\ n\le k}}
       \left\lfloor\frac{2^k-1}{2^n-1}\right\rfloor.
```
Only exponents $`n\le k`$ contribute to $`J(k)`$: when $`n>k`$, the multiplied term is already less than $`1`$. Thus $`J(k)`$ is a finite sum of integers. Splitting the terms gives

<a id="eq:split-main"></a>

``` math
\begin{equation}
\label{eq:split-main}
 (2^k-1)S=J(k)+R(k).
\end{equation}
```
The series defining $`R(k)`$ converges by comparison with $`(2^k-1)S`$; Appendix [9.2](#app%3Asplit) justifies the identity using partial sums.

The sum $`R(k)`$ need not itself be a fractional part. For the three exponents $`2,3,6`$ and $`k=5`$, the separate fractional parts sum to
``` math
\left\{\frac{31}3\right\}+\left\{\frac{31}7\right\}
 +\left\{\frac{31}{63}\right\}
 =\frac13+\frac37+\frac{31}{63}=\frac{79}{63}>1.
```
The fractional part of the whole product is instead $`16/63`$. We retain the separate contributions because each has the explicit formula [\[eq:fracpart-main\]](#eq%3Afracpart-main); their sum still has the required form $`uS-j`$.

Finally, if $`A`$ is infinite, there is always a selected exponent $`n>k`$. Its multiplied term is positive and less than $`1`$, so it contributes positively to $`R(k)`$; all other contributions are nonnegative. Therefore
``` math
S=p/q\quad\Longrightarrow\quad
 R(k)=(2^k-1)S-J(k)\ge\frac1q\quad\hbox{for every }k\ge1.
```
Our task is now to find *one* $`k`$ with $`R(k)<1/q`$. (Question [2](#chk%3Apositive).)

<a id="sec:doubling"></a>

# A complete example: the doubling exponents

Return to the opening example, $`A=\{2,4,8,16,\dots\}`$. We now know why $`255`$ cleared its first three terms: it is $`2^8-1`$, and the exponents $`2,4,8`$ all divide $`8`$. In our new notation that calculation is
``` math
255S=103+R(8),\qquad R(8)=\frac1{257}+\frac1{16843009}+\dots>0.
```
One small remainder rules out only some denominators. To rule out every $`q`$, we need remainders as small as we please. For any doubling exponent $`k`$, all selected $`n\le k`$ divide $`k`$ and contribute zero. Every later selected exponent is at least $`2k`$, and
``` math
0<\ell_n(k)=\frac{2^k-1}{2^n-1}
 <\frac{2^k}{2^{n-1}}=\frac2{2^{n-k}}.
```
For $`k=8`$, the gaps $`n-k`$ are $`8,24,56,\dots`$. In general they are distinct integers at least $`k`$. Insert the missing positive terms so that the gaps run through *all* integers $`k,k+1,k+2,\dots`$; this can only increase the upper bound:
``` math
0<R(k)<\sum_{e=k}^{\infty}\frac2{2^e}=\frac4{2^k}.
```
The last equality is the geometric-series formula: the first term is $`2/2^k`$ and each successive term is half its predecessor.

For $`k=8`$ this gives $`R(8)<1/64`$, ruling out every denominator $`q\le64`$: such a denominator would force $`R(8)\ge1/q\ge1/64`$. For $`k=16`$ the bound is $`R(16)<1/16384`$. Given any proposed denominator $`q`$, choose a doubling exponent $`k`$ with $`2^k>4q`$. Then $`0<R(k)<1/q`$, contradicting rationality. This completes the proof for the doubling exponents.

The special feature was that $`k`$ both eliminated all earlier terms and left the next exponent at least $`2k`$. A general set $`A`$ need not have that spacing. The next section explains how averaging replaces it.

<a id="sec:general"></a>

# Why averaging works

<a id="larger-multipliers-need-not-help."></a>

#### Larger multipliers need not help.

For the square exponents $`A=\{1,4,9,16,\dots\}`$, both $`k=4`$ and $`k=8`$ are divisible by the first two selected exponents $`1,4`$. All later selected exponents exceed $`8`$, so their integer parts vanish for both multipliers. Consequently
``` math
R(4)=15\left(\frac1{511}+\frac1{65535}+\dots\right),\qquad
 R(8)=255\left(\frac1{511}+\frac1{65535}+\dots\right)=17R(4).
```
In fact $`R(4)\approx0.0296`$ and $`R(8)\approx0.503`$. Increasing $`k`$ while preserving the same zero contributions has enlarged the remaining terms. Even eliminating longer initial groups need not suffice: in Exercise [5](#ex%3A6), the next selected exponent is $`k+1`$, leaving $`(2^k-1)/(2^{k+1}-1)`$, which approaches $`1/2`$. The choices of $`k`$ matter, not just how many initial rows they make zero.

<a id="one-table-many-attempts"></a>

## One table, many attempts

Keep $`A`$, and hence the original number $`S`$, fixed. For each new choice of $`k`$, repeat the whole calculation: multiply every selected term by $`2^k-1`$, subtract its integer part, and add what remains to obtain $`R(k)`$. *Each column below is one entire attempt to obtain the contradiction.* Each row follows the contribution from one original term across the attempts. We need one column whose total is less than $`1/q`$.

Choose candidate exponents spaced $`Q`$ apart: $`k=Q,2Q,\dots,MQ`$. Here $`Q`$ is the spacing, $`M`$ is the number of attempts, and $`m`$ labels the attempt $`k=mQ`$; the actual multiplier is $`2^{mQ}-1`$. Neither $`Q`$ nor $`k`$ has to belong to $`A`$. We choose $`Q`$ divisible by an initial group of selected exponents so those rows stay zero in every column. For the square exponents, $`Q=4`$ gives:

<div class="center">

|  |  |  |  |  |
|:--:|:--:|:--:|:--:|:--:|
| selected exponent $`n`$ | $`k=4`$ | $`k=8`$ | $`k=12`$ | $`k=16`$ |
| $`1`$ | $`0`$ | $`0`$ | $`0`$ | $`0`$ |
| $`4`$ | $`0`$ | $`0`$ | $`0`$ | $`0`$ |
| $`9`$ | $`15/511`$ | $`255/511`$ | $`7/511`$ | $`127/511`$ |
| $`16`$ | $`15/65535`$ | $`255/65535`$ | $`4095/65535`$ | $`0`$ |
| $`\vdots`$ | $`\vdots`$ | $`\vdots`$ | $`\vdots`$ | $`\vdots`$ |
| column total | $`R(4)`$ | $`R(8)`$ | $`R(12)`$ | $`R(16)`$ |

</div>

Every entry is a fractional part $`\ell_n(k)`$. For example, the cell $`n=9,k=12`$ uses $`12=1\cdot9+3`$, so $`\ell_9(12)=(2^3-1)/(2^9-1)=7/511`$. Each column uses the same multiplier throughout, including in the rows not displayed. (Question [3](#chk%3Acolumns).)

<a id="average-complete-attempts."></a>

#### Average complete attempts.

Different rows may be small in different columns; choosing a separate column for each row would not give one multiplier for the original series. Instead average *every row across the same columns*, then add those row averages. This gives the average of the complete column totals: both calculations add the same entries and divide by the same number $`M`$. In symbols,

<a id="eq:average-main"></a>

``` math
\begin{equation}
\label{eq:average-main}
 \frac1M\sum_{m=1}^{M}R(mQ)
 =\sum_{n\in A}\frac1M\sum_{m=1}^{M}\ell_n(mQ).
\end{equation}
```

For infinitely many rows we first use finite portions and then let them grow; convergence preserves the equality (Appendix [9.4](#app%3Aproof)). If this average is below $`1/q`$, at least one whole column has total below $`1/q`$. Otherwise every column total would be at least $`1/q`$, making their average at least $`1/q`$ too.

<a id="what-the-two-estimates-will-do."></a>

#### What the two estimates will do.

We will divide the rows into three groups. An initial finite group stays zero. A further finite group can complete its cycles if we choose $`M`$ appropriately; we will bound each such row’s average by $`1/n`$. For the infinitely many remaining rows, we need a bound valid for every $`M`$: we will prove $`2Q/n`$. Once $`Q`$ is fixed, we can make the sum of these bounds as small as needed by moving far enough down the rows: the remaining reciprocals $`1/n`$ have arbitrarily small total. Section [7](#sec%3Aproof) will choose the two row cutoffs and then $`M`$ so that both nonzero groups have small total averages.

<a id="sec:cycles"></a>

## Complete cycles give small averages

To derive a rule for any row, use $`n=3`$ and $`n=6`$, which are not exponents of the square series. Start with $`n=3`$ and consecutive $`k`$:

<div class="center">

|               |         |         |       |         |         |       |
|:--------------|:-------:|:-------:|:-----:|:-------:|:-------:|:-----:|
| $`k`$         |  $`1`$  |  $`2`$  | $`3`$ |  $`4`$  |  $`5`$  | $`6`$ |
| $`k\bmod3`$   |  $`1`$  |  $`2`$  | $`0`$ |  $`1`$  |  $`2`$  | $`0`$ |
| $`\ell_3(k)`$ | $`1/7`$ | $`3/7`$ | $`0`$ | $`1/7`$ | $`3/7`$ | $`0`$ |

</div>

One repeating block, or *cycle*, has sum $`4/7<1`$ and average $`4/21<1/3`$. This bounds the average, not every entry: $`3/7>1/3`$. For general $`n`$, a consecutive cycle has remainders $`0,1,\dots,n-1`$. The powers $`2^0,2^1,\dots,2^{n-1}`$ add up to $`2^n-1`$, exactly the denominator. Each actual numerator is one less than the corresponding power, so the cycle’s total is
``` math
\frac{(2^0-1)+(2^1-1)+\dots+(2^{n-1}-1)}{2^n-1}
 <\frac{2^0+2^1+\dots+2^{n-1}}{2^n-1}=1.
```
Dividing by its $`n`$ entries gives a cycle average below $`1/n`$. These reciprocals bound the row averages, which is why the hypothesis controls their sum.

<a id="keep-the-required-spacing."></a>

#### Keep the required spacing.

Our candidates use steps of $`Q`$, not necessarily $`1`$, because $`Q`$ preserves the initial zero rows. With $`n=6`$ and $`Q=4`$:

<div class="center">

|                     |           |          |        |
|:--------------------|:---------:|:--------:|:------:|
| sample number $`m`$ |   $`1`$   |  $`2`$   | $`3`$  |
| $`k=4m`$            |   $`4`$   |  $`8`$   | $`12`$ |
| $`k\bmod6`$         |   $`4`$   |  $`2`$   | $`0`$  |
| $`\ell_6(k)`$       | $`15/63`$ | $`3/63`$ | $`0`$  |

</div>

The last two rows repeat every three samples. Only the even remainders occur, and the average is $`(15+3+0)/(3\cdot63)=2/21<1/6`$.

Let $`g=\gcd(n,Q)`$ be the *greatest common divisor*, the largest positive integer dividing both $`n`$ and $`Q`$, and put $`c=n/g`$. In the example $`n=6,Q=4`$, these are $`g=2,c=3`$. We will show that one cycle has exactly $`c`$ samples, visiting $`0,g,2g,\dots,n-g`$ once each, in some order. Knowing which remainders occur will let us compare the sampled mean with the mean over all remainders. Here are the four steps.

*Possible remainders.* Each remainder is a multiple of $`g`$: it is $`mQ`$ minus a multiple of $`n`$, and both are divisible by $`g`$. Between $`0`$ and $`n-1`$ there are exactly $`c`$ possibilities, $`0,g,2g,\dots,n-g`$.

*A return after $`c`$ steps.* Since
``` math
cQ=\frac ng Q=n\frac Qg,
```
taking another $`c`$ steps adds a multiple of $`n`$ and leaves the remainder unchanged. So $`c`$ is a period; we still have to exclude earlier repetition.

*No earlier repetition.* Two integers have the same remainder on division by $`n`$ exactly when their difference is a multiple of $`n`$. For samples $`m_1<m_2`$, that difference is $`m_2Q-m_1Q=(m_2-m_1)Q`$. Dividing out $`g`$, equal remainders therefore mean that $`n/g`$ divides $`(m_2-m_1)(Q/g)`$. The integers $`n/g`$ and $`Q/g`$ have no common divisor greater than $`1`$; they are called *coprime*. This lets us cancel $`Q/g`$: $`c=n/g`$ must divide $`m_2-m_1`$. In the example $`n=6,Q=4`$, write $`d=m_2-m_1`$: if $`3`$ divides $`2d`$, it also divides $`d=2(2d)-3d`$, since both terms on the right are multiples of $`3`$. Appendix [9.3](#app%3Acycle) proves the general cancellation fact. Thus samples fewer than $`c`$ steps apart cannot have the same remainder.

*All possibilities are visited.* The first $`c`$ remainders are distinct and there are only $`c`$ possible values. Hence every possible remainder occurs exactly once per cycle.

<a id="compare-means-without-calculating-a-new-formula."></a>

#### Compare means without calculating a new formula.

Sort the sampled remainders $`4,2,0`$ as $`0,2,4`$, preserving the sampled mean. These start the pairs $`(0,1)`$, $`(2,3)`$, $`(4,5)`$. Since $`(2^r-1)/(2^n-1)`$ increases with $`r`$, each pair’s first remainder gives its smaller fractional part. Copy each sampled value twice to compare with all six consecutive-cycle values.

<div class="center">

<span id="fig:cycle-mean" label="fig:cycle-mean"></span>

</div>

In general, each group has $`g`$ consecutive remainders, and the sample selects its first: $`0,g,\dots,n-g`$. Repeating each selected value $`g`$ times gives a sum no larger than the sum over all $`n`$ remainders. Divide by $`n`$: the copied list retains the mean of the $`c`$ samples, while the consecutive-cycle mean is below $`1/n`$. Thus, whenever $`M`$ is a positive multiple of $`c`$,

<a id="eq:cycle-main"></a>

``` math
\begin{equation}
\label{eq:cycle-main}
 \frac1M\sum_{m=1}^{M}\ell_n(mQ)<\frac1n.
\end{equation}
```
The bound $`1/n`$ does not grow with $`Q`$: making the initial rows zero can require a large spacing without worsening this bound, provided $`M`$ completes the cycles. If $`n`$ divides $`Q`$, the cycle has one entry, zero, which also satisfies the bound.

<a id="sec:unfinished"></a>

## A bound that also covers unfinished cycles

An unfinished cycle can miss its final zero. For $`n=5`$ and consecutive candidates ($`Q=1`$), one cycle is
``` math
\frac1{31},\quad\frac3{31},\quad\frac7{31},\quad\frac{15}{31},\quad0.
```
The first four entries average $`26/(4\cdot31)=13/62>1/5`$; all five average $`26/(5\cdot31)=26/155<1/5`$. The increasing positive list and the full cycle therefore have different average bounds. (Question [4](#chk%3Apartial) gives a spaced example.)

Nor can finitely many columns complete infinitely many rows: if $`n>MQ`$, the last sample has not even reached the first positive multiple of $`n`$.

We need another estimate, valid for *every* positive $`M`$:

<a id="eq:uniform-main"></a>

``` math
\begin{equation}
\label{eq:uniform-main}
 \frac1M\sum_{m=1}^{M}\ell_n(mQ)\le\frac{2Q}{n}.
\end{equation}
```
For fixed $`Q`$, this bound holds for every $`M`$, so choosing the number of columns later cannot invalidate it. We prove it using the same cycles.

<a id="first-bound-all-the-consecutive-entries."></a>

#### First bound all the consecutive entries.

The $`M`$ sampled exponents $`Q,2Q,\dots,MQ`$ lie among the first $`MQ`$ positive integers. We first bound the sum over all $`MQ`$ entries. For $`n\ge2`$, consecutive entries beginning at $`k=1`$ repeat the block
``` math
\underbrace{\frac1{2^n-1},\frac3{2^n-1},\dots,
 \frac{2^{n-1}-1}{2^n-1}}_{n-1\text{ positive entries, increasing}},\quad 0.
```

For $`n=2`$, the positive list consists only of $`1/3`$. The positive entries sum to less than $`1`$, as the complete-cycle calculation showed. Their average is therefore less than $`1/(n-1)`$. Any beginning portion of this *positive* list has no larger average: each omitted entry is at least every included entry, so appending the omitted entries cannot lower the average. Thus a nonempty beginning portion has average at most $`2/n`$, since $`1/(n-1)\le2/n`$ for $`n\ge2`$. We excluded the final zero for this comparison; the whole block including zero already has the stronger bound $`1/n`$.

The first $`MQ`$ entries consist of complete blocks followed, possibly, by a beginning portion of the positive list. For example, the first seven entries when $`n=5`$ have numerators $`(1,3,7,15,0)`$ followed by $`(1,3)`$, all over $`31`$. Each piece has sum at most its number of entries times $`2/n`$. The pieces contain $`MQ`$ entries altogether, so their total is at most $`2MQ/n`$. For $`n=1`$, all entries are zero and the bound still holds.

<a id="keep-only-the-sampled-entries."></a>

#### Keep only the sampled entries.

Removing nonnegative entries cannot increase the sum. Hence
``` math
\sum_{m=1}^{M}\ell_n(mQ)
 \le\sum_{k=1}^{MQ}\ell_n(k)\le\frac{2MQ}{n}.
```
Divide by the number $`M`$ of actual candidates to obtain [\[eq:uniform-main\]](#eq%3Auniform-main). This explains the factor $`Q`$: we bounded $`M`$ sampled entries by including all $`MQ`$ consecutive entries. We have not changed our candidates or assumed that their sampled values are increasing.

<a id="sec:proof"></a>

# Combining the estimates

Suppose $`S=p/q`$. Every column total $`R(k)`$ is then at least $`1/q`$. We will contradict this by making a finite average of column totals less than $`1/q`$.

<a id="app:numbers"></a>

## The construction with actual numbers

Use the doubling exponents again, this time to see the general method at work. We already have a shorter proof for them. Assume the proposed denominator is $`q=5`$. It is enough to make the average of the column totals less than $`1/5`$; allow less than $`1/10`$ from each of the two nonzero groups.

Beyond a doubling exponent $`2^h`$, the reciprocal tail is $`1/2^{h+1}+1/2^{h+2}+\dots=1/2^h`$.

1.  *Decide which early rows to make zero.* Set the first cutoff at exponent $`t=16`$. The reciprocal sum of all later rows is $`1/16<1/10`$, so any middle group will have enough room in its bound. The earlier cutoff $`8`$ would give $`1/8>1/10`$.

2.  *Preserve those zeros in every attempt.* Choose $`Q=16`$, divisible by $`2,4,8,16`$. Every candidate $`k=16m`$ therefore gives zero in these four rows.

3.  *Make the infinite far group small despite the factor $`2Q`$.* Applying $`2Q/n`$ to every row beyond $`t=16`$ would bound the sum of their averages by $`32/16=2`$. Increasing a doubling cutoff $`t`$ together with $`Q=t`$ still gives $`2Q/t=2`$. This shows a limitation of the estimate, not a lower bound on $`R(k)`$. Instead keep $`Q=16`$ and put the second cutoff at $`T=512`$. The remaining rows have exponents $`1024,2048,\dots`$. Adding the bounds $`32/n`$ on their averages gives
    ``` math
    32\left(\frac1{1024}+\frac1{2048}+\dots\right)
      =\frac{32}{512}<\frac1{10}.
    ```
    A cutoff of $`256`$ would leave $`32/256=1/8`$, above the reserved $`1/10`$.

4.  *Complete all cycles between the cutoffs.* The middle exponents $`32,64,128,256,512`$ have cycle lengths $`2,4,8,16,32`$. Choose $`M=64`$, a common multiple of these lengths. Every middle row completes its cycles, and the far bound is still valid because it holds for every $`M`$.

Here $`t`$ and $`T`$ are cutoffs on *exponent values*, not counts of terms. The last candidate is $`MQ=1024`$, whereas the second cutoff is $`T=512`$: the number of columns and the division into groups of rows have different jobs. $`M=32`$ would also work; choosing $`64`$ shows that we may use more columns without changing either cutoff.

The initial rows contribute zero. The middle row averages together are less than
``` math
\frac1{32}+\frac1{64}+\frac1{128}+\frac1{256}+\frac1{512}
 =\frac{31}{512}.
```
The far row averages add up to at most $`2Q/T=32/512`$. Hence
``` math
\frac1{64}\sum_{m=1}^{64}R(16m)
 <\frac{31}{512}+\frac{32}{512}=\frac{63}{512}<\frac15.
```
At least one of the 64 complete attempts has $`0<R(k)<1/5`$, contradicting $`S=p/5`$. We have proved that a candidate works without identifying which one. That existence is enough for the contradiction.

The first cutoff determines which rows $`Q`$ must keep zero; the second is chosen after $`Q`$ is fixed, to compensate for the factor $`2Q`$. Only then do we choose how many columns to use. (For a change of $`Q`$, see Question [5](#chk%3Aorder).)

<a id="sec:allchoices"></a>

## The same choices for any admissible set

Let $`A`$ satisfy the theorem’s hypotheses, and suppose $`S_A=p/q`$, where $`q`$ is a positive integer. Since only finitely many positive integers lie below any fixed bound, the infinite set $`A`$ has arbitrarily large elements. Moving a cutoff farther out can only decrease a reciprocal tail. We may therefore choose cutoffs $`t,T\in A`$, with $`T>t`$: the initial group then contains $`t`$, and the middle group contains $`T`$. Make the choices in this order:
``` math
t\ \longrightarrow\ Q\ \longrightarrow\ T\ \longrightarrow\ M.
```

1.  Choose $`t\in A`$ so that $`\sum_{n\in A,\,n>t}1/n<1/(2q)`$. This is possible because the reciprocal tails tend to zero.

2.  Choose a positive common multiple $`Q`$ of the selected exponents $`n\le t`$. Their product works. These exponents divide every candidate $`mQ`$, so their rows are zero.

3.  With $`Q`$ fixed, choose $`T\in A`$, with $`T>t`$, so that $`2Q\sum_{n\in A,\,n>T}1/n<1/(2q)`$. The tails again tend to zero, now with a fixed coefficient $`2Q`$.

4.  For the finitely many selected $`t<n\le T`$, choose $`M`$ to be a positive common multiple of their cycle lengths $`n/\gcd(n,Q)`$. Their product works. The far-tail bound remains valid for this final choice of $`M`$.

Add the row averages over these same $`M`$ columns:

<div class="center">

|  |  |  |
|:---|:---|:---|
| selected exponents | reason for the bound | total contribution |
| $`n\le t`$ | each $`n`$ divides $`Q`$ | $`0`$ |
| $`t<n\le T`$ | complete cycles; row average below $`1/n`$ | below $`\sum_{n\in A,\,n>t}1/n<1/(2q)`$ |
| $`n>T`$ | bound $`2Q/n`$ for every $`M`$ | at most $`2Q\sum_{n\in A,\,n>T}1/n<1/(2q)`$ |

</div>

By [\[eq:average-main\]](#eq%3Aaverage-main), the average of the column totals is therefore
``` math
\frac1M\sum_{m=1}^{M}R(mQ)<0+\frac1{2q}+\frac1{2q}=\frac1q.
```
At least one total is below $`1/q`$, contradicting the rationality lower bound for every column. This proves Theorem [1](#thm%3Amain).

Infinitude supplied positivity; rationality supplied the fixed gap; reciprocal convergence supplied both small tails. The order of choices ensured that all bounds apply to the same finite collection of complete attempts.

<a id="sec:limits"></a>

# Consequences and limits

For every integer $`b\ge2`$, the same method proves
``` math
A\text{ infinite},\quad\sum_{n\in A}\frac1n<\infty
 \quad\Longrightarrow\quad
 \sum_{n\in A}\frac1{b^n-1}\text{ is irrational}.
```
Replace the multiplier by $`b^k-1`$. The fractional parts are $`(b^{k\bmod n}-1)/(b^n-1)`$, and their cycle averages are still below $`1/n`$. Appendix [9.5](#app%3Abases) checks both estimates.

The theorem covers arbitrary selections from the square-exponent series $`1+\tfrac1{15}+\tfrac1{511}+\dots`$. If infinitely many remain, their sum is irrational: deleting terms cannot increase the reciprocal-exponent sum $`\sum_{m\ge1}1/m^2<\infty`$, so Theorem [1](#thm%3Amain) still applies. If only finitely many remain, their sum is rational. Thus a selection from this series has rational sum exactly when it is finite; no pattern in the retained exponents is required. Replacing $`2`$ by any integer $`b\ge2`$ gives the same conclusion for the same retained exponents.

The reciprocal-sum condition is sufficient, not necessary. These particular remainders $`R(k)`$ need not become arbitrarily small for every infinite $`A`$. When every positive exponent is selected, the terms with $`n>k`$ alone give
``` math
R(k)\ge\sum_{n>k}\frac{2^k-1}{2^n-1}
 >\sum_{n>k}\frac{2^k-1}{2^n}
 =1-2^{-k}\ge\frac12.
```
Thus these remainders can never be arbitrarily small. Nevertheless, Erdős proved that the full sum is irrational in 1948 \[erdos1948\]. Failure of our method does not imply rationality. Tao and Teräväinen proved irrationality for the prime exponents \[taoteravainen2025, Theorem 1.3\], another case with divergent reciprocal sum. The short paper \[shortpaper\] gives further sufficient conditions; the long record \[longrecord\] develops the proofs and the obstructions to extending them. The question for every infinite set $`A`$ remains open.

Appendix [9.6](#app%3Alean) identifies the Lean-checked theorem and explains how its proof differs from the finite-average proof given here.

<a id="app:full"></a>

# Supporting details and formal-proof correspondence

This appendix supplies convergence and limit details, the divisibility argument for sampled cycles, the other-base estimates, and an optional account of formal verification.

<a id="app:sums"></a>

## Convergence and tails

For nonnegative terms $`a_n`$, the partial sums $`\sum_{n=1}^{N}a_n`$ increase. If they are bounded above, let $`L`$ be their least upper bound: the smallest real number at least every partial sum. For every $`\varepsilon>0`$, some partial sum exceeds $`L-\varepsilon`$; otherwise $`L-\varepsilon`$ would be a smaller upper bound. Every later partial sum then lies in $`(L-\varepsilon,L]`$, so the series converges to $`L`$. Its tail after $`N`$ equals $`L-\sum_{n=1}^{N}a_n`$ and tends to zero. This is the property used twice when choosing the cutoffs in Section [7](#sec%3Aproof).

Comparison follows by comparing partial sums. In particular, $`0\le a_n\le b_n`$ and $`\sum b_n<\infty`$ imply $`\sum a_n\le\sum b_n<\infty`$. If one term is strictly smaller, the sums differ by at least that positive difference. Restricting a nonnegative series to a subset of its indices can only decrease its sum.

For $`0<x<1`$, multiplication and subtraction of the finite geometric sum give
``` math
(1-x)(1+x+\dots+x^{N-1})=1-x^N.
```
Letting $`N\to\infty`$ yields $`\sum_{j=0}^{\infty}x^j=1/(1-x)`$. At $`x=1/2`$, this gives $`\sum_{j=1}^{\infty}2^{-j}=1`$ and, by scaling, $`\sum_{j=h}^{\infty}2^{-j}=2^{1-h}`$. Consequently $`1/(2^n-1)\le2^{1-n}`$ proves convergence of $`S_A`$ for every set $`A`$, irrespective of whether $`\sum_{n\in A}1/n`$ converges.

<a id="app:split"></a>

## Passing to the full transformed sum

Fix $`k`$. Each $`\ell_n(k)`$ is nonnegative and at most $`(2^k-1)/(2^n-1)`$, so $`R(k)`$ converges by comparison with $`(2^k-1)S`$. Only selected exponents $`n\le k`$ have nonzero integer parts. For any integer $`L\ge k`$, splitting the finitely many terms up to $`L`$ gives
``` math
(2^k-1)\sum_{\substack{n\in A\\n\le L}}\frac1{2^n-1}
 =J(k)+\sum_{\substack{n\in A\\n\le L}}\ell_n(k).
```
As $`L`$ grows, $`J(k)`$ stays fixed and the two convergent partial sums tend to $`S`$ and $`R(k)`$. This proves [\[eq:split-main\]](#eq%3Asplit-main).

<a id="app:cycle"></a>

## Why the sampled remainders form a cycle

The elementary cancellation fact is: if positive integers $`c,u`$ are coprime and $`c`$ divides $`du`$, then $`c`$ divides $`d`$. The example in Section [6.2](#sec%3Acycles) used $`c=3,u=2`$. For general coprime $`c,u`$, the same argument uses integers $`a,b`$ with $`au+bc=1`$. Here is why they exist. Among the positive values $`au+bc`$, allowing $`a,b`$ to be any integers, choose the smallest, $`v`$; there is at least one since $`u=1\cdot u+0\cdot c`$ is such a combination. Write $`v=au+bc`$ for coefficients attaining this minimum. Division gives $`u=sv+r`$ with $`0\le r<v`$, so
``` math
r=u-sv=(1-sa)u-sbc.
```
Thus $`r`$ is another integer combination of $`u,c`$. If it were positive, it would contradict the choice of $`v`$ as the smallest positive combination. Hence $`r=0`$, so $`v`$ divides $`u`$. The same reasoning with $`c`$ shows that $`v`$ divides $`c`$ too. Since $`u,c`$ are coprime, $`v=1`$. Now $`d=a(du)+b(dc)`$ proves cancellation.

Return to $`g=\gcd(n,Q)`$, $`c=n/g`$ and $`u=Q/g`$. The integers $`c,u`$ are coprime: a larger common divisor would give a common divisor of $`n,Q`$ larger than $`g`$. Write $`x\mid y`$ to mean that $`x`$ divides $`y`$. Two sampled exponents $`m_1Q`$ and $`m_2Q`$ have equal remainders exactly when their difference is divisible by $`n`$, that is,
``` math
n\mid(m_2-m_1)Q
 \quad\Longleftrightarrow\quad
 c\mid(m_2-m_1)u
 \quad\Longleftrightarrow\quad
 c\mid m_2-m_1.
```
Thus the first $`c`$ sampled remainders are distinct and repeat after $`c`$ steps. Every remainder is divisible by $`g`$, since both $`mQ`$ and $`n`$ are. There are exactly $`c`$ possibilities $`0,g,\dots,n-g`$, so each occurs once. This supplies the remainder rule used in Section [6.2](#sec%3Acycles).

<a id="app:proof"></a>

## Adding the row averages

For finitely many rows $`n\le H`$, adding the row averages equals averaging the column totals: both operations add the same entries and divide by $`M`$. Keep $`Q`$ and $`M`$ fixed. Given any positive target $`\varepsilon`$, each of the $`M`$ convergent column sums $`R(mQ)`$ has tail less than $`\varepsilon`$ beyond some row cutoff. Take the largest of these finitely many cutoffs. All column tails, and therefore their average, are less than $`\varepsilon`$ beyond it. Consequently the finite sums of row averages tend to the average of the full column totals. This proves [\[eq:average-main\]](#eq%3Aaverage-main); no interchange of two infinite sums is needed.

<a id="app:bases"></a>

## Other bases

Let $`b\ge2`$ be an integer. For $`b=3`$, exponents $`2,4,8,\dots`$ give $`1/8+1/80+1/6560+\dots`$. Convergence and the fractional-part formula carry over because $`b^n-1\ge2^{n-1}`$ and $`b^{k+n}-1=b^k(b^n-1)+(b^k-1)`$.

For a consecutive cycle, the sum of the fractional parts is
``` math
\frac{(b^0-1)+\dots+(b^{n-1}-1)}{b^n-1}
 <\frac{b^0+b^1+\dots+b^{n-1}}{b^n-1}
 =\frac1{b-1}\le1.
```
Here we used $`1+b+\dots+b^{n-1}=(b^n-1)/(b-1)`$ and $`b\ge2`$. The fractional parts still increase with the remainder, so the equal-group comparison bounds a complete sampled-cycle average by the consecutive-cycle average, which is below $`1/n`$.

For $`n\ge2`$ the $`n-1`$ positive entries are still increasing and have total less than $`1`$. The beginning-portion argument in Section [6.3](#sec%3Aunfinished) therefore gives the same $`2/n`$ bound for consecutive entries starting at $`k=1`$. Keeping only the sampled entries then gives the bound $`2Q/n`$ for any sampled length $`M`$. For $`n=1`$ the fractional parts are all zero: $`(b^k-1)/(b-1)`$ is an integer. Both estimates required for the three groups remain valid. With the same choices of $`t,Q,T,M`$, the proof establishes irrationality of $`\sum_{n\in A}1/(b^n-1)`$ whenever $`A`$ is infinite and $`\sum_{n\in A}1/n<\infty`$ \[shortpaper, Theorem A.1\].

<a id="app:lean"></a>

## Formal verification and its scope

<div class="center">

<div class="minipage">

theorem irrational_erdosSupportSeries_of_summable_reciprocal\
(b : $`\mathbb{N}`$) (A : Set $`\mathbb{N}`$) (hb : 2 $`\le`$ b) (hA : A.Infinite)\
(hsum : Summable (reciprocalSupportTerm A)) :\
Irrational (erdosSupportSeries b A)

</div>

</div>

Line by line: $`b`$ is a nonnegative integer and `hb` assumes $`b\ge2`$; $`A`$ is a set of nonnegative integers and `hA` assumes it is infinite; `reciprocalSupportTerm A` is a sequence indexed by $`n=0,1,\dots`$, with entry $`1/n`$ when $`n`$ is in $`A`$ and $`0`$ otherwise, and `hsum` assumes its sum is finite; the conclusion says that `erdosSupportSeries b A`, the sum of $`1/(b^n-1)`$ over $`A`$, is irrational. Lean’s nonnegative integers start at $`0`$, and in Lean dividing by $`0`$ gives $`0`$, so the exponent $`0`$ counts as $`0`$ in both sums; removing it changes neither sum and leaves an infinite set infinite. So for $`b=2`$ the statement says the same as Theorem [1](#thm%3Amain). It is the formal version of \[shortpaper, Theorem A.1\].

The [Lean source at a fixed commit](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean#L395) contains this statement and its proof. The Lean kernel, a small program, has checked every step of that proof. Comparator checked that the proof establishes a separately written formal statement. Its [verification receipt](https://github.com/wcook04/plectis-erdos/blob/0064fc9b2a2693de97aebc8abec26090c3cd1095/evidence/comparator/replay-35935225572/receipt-E257_47.json) records acceptance by Lean’s kernel and by a second, independent kernel checker. At base $`2`$ the Lean proof follows \[shortpaper, Appendix A\], which takes limits of averages; it reaches the other bases by comparing each base-$`b`$ fractional part with twice the base-$`2`$ one, a different route from Appendix [9.5](#app%3Abases).

With exponent $`0`$ omitted as above, the shifted quantity used in Lean is
``` math
\sum_{n\in A}\frac{2^{k\bmod n}}{2^n-1}=S_A+R(k).
```
Its value at $`k=0`$ is $`S_A`$. A value strictly between $`S_A`$ and $`S_A+\varepsilon`$ therefore means exactly $`0<R(k)<\varepsilon`$, the target of our proof. Subtracting $`S_A`$, we can describe the two limits in terms of our fractional parts.

First fix $`Q`$ and let the averaging length tend to infinity. Each row’s average tends to its cycle mean: complete cycles have that mean, and the unfinished last cycle has bounded length, so its weight in the average tends to zero. Throughout this limit the row averages are bounded by $`2(Q+1)/n`$.

To pass from the row limits to the whole sum, choose a row cutoff so far out that the sum of these bounds beyond it is small. This is possible because $`Q`$ is fixed and $`\sum_{n\in A}1/n`$ converges. The same bound holds for each row’s limit, so it controls both the tails before taking the limit and the tail of the limiting row averages. Only finitely many earlier rows remain, and their limits can be taken one at a time. Combining that finite part with the two small tails justifies passing the limit through the sum.

Next consider $`Q=\operatorname{lcm}(1,\dots,t)`$. For every $`n\le t`$, the limiting row average is zero, because $`n`$ divides $`Q`$. All remaining limiting row averages are bounded by $`1/n`$, independently of $`t`$. Their total is therefore at most $`\sum_{n\in A,\,n>t}1/n`$, which tends to zero. This is the second use of small reciprocal tails. The averaging length tends to infinity with $`Q`$ fixed before $`t`$ varies. To obtain one witness, the proof chooses a suitable $`Q`$ first and a sufficiently long average second.

Our cutoffs $`t,T`$ and number $`M`$ of candidate columns make those choices explicit, using the separately proved estimate $`2Q/n`$. Under the rationality assumption, both arguments make the integer $`qR(k)`$ strictly between $`0`$ and $`1`$. The finite reconstruction and its estimates are ordinary proofs provided here; the historical Lean and Comparator receipts establish the linked formal theorem and its own proof.

<a id="sec:exercises"></a>

# Questions and exercises

<div id="chk:hypotheses" class="readercheck">

**Question 1**. Which of $`\{2,4\}`$, $`\{2,4,8,16,\dots\}`$ and $`\{2,4,6,8,\dots\}`$ does Theorem [1](#thm%3Amain) apply to?

</div>

<div id="chk:positive" class="readercheck">

**Question 2**. Suppose $`S=p/q`$. Why would $`0<R(k)<1/q`$ be impossible, even if $`k`$ was chosen using $`q`$? Why do we need $`R(k)>0`$, and where does infinitude of $`A`$ supply it?

</div>

<div id="chk:columns" class="readercheck">

**Question 3**. In the square-exponent table, what stays fixed and what changes when we move from $`k=4`$ to $`k=8`$? Why can we not choose the smallest entry in each row and regard their sum as one successful attempt?

</div>

<div id="chk:partial" class="readercheck">

**Question 4**. Why is the mean over a complete consecutive cycle below $`1/n`$? Why does the same bound hold for a complete sampled cycle, which may have fewer than $`n`$ entries? For $`n=6`$ and $`Q=4`$, the full cycle averages $`\tfrac2{21}<\tfrac16`$. Is the first value alone also below $`\tfrac16`$?

</div>

<div id="chk:order" class="readercheck">

**Question 5**. In Section [7.1](#app%3Anumbers), replace $`Q=16`$ by $`Q'=64`$ and keep $`T=512`$. Does the far bound still give less than $`\tfrac1{10}`$? What must be chosen again?

</div>

<div id="ex:2" class="exercise">

**Exercise 1**. For $`n=5`$ and $`Q=1`$, calculate the mean of the first seven entries. Separate them into a complete cycle and a beginning portion of the next. Why is the mean of all seven not simply half the sum of the two piece-means?

</div>

<div id="ex:3" class="exercise">

**Exercise 2**. Use the fractional-part formula [\[eq:fracpart-main\]](#eq%3Afracpart-main) to show that $`2^{12}-1`$ is divisible by $`7`$ and by $`63`$, and find its remainder on division by $`2^5-1=31`$.

</div>

<div id="ex:4" class="exercise">

**Exercise 3**. Adapt the proof in Section [5](#sec%3Adoubling) to the exponents $`3,9,27,81,\dots`$, using $`k=3^j`$.

</div>

<div id="ex:5" class="exercise">

**Exercise 4**. Show that $`5\sqrt2-7=(\sqrt2-1)^3`$, and that multiplying a number $`a\sqrt2-c`$, where $`a,c`$ are nonnegative integers, by $`3-2\sqrt2`$ gives another number $`a'\sqrt2-c'`$, where $`a',c'`$ are nonnegative integers. Use the test of Section [3](#sec%3Atest) to show that $`\sqrt2`$ is irrational.

</div>

<div id="ex:6" class="exercise">

**Exercise 5**. Let $`a_1=2`$ and let each later exponent be one more than the product of the earlier ones, giving $`2,3,7,43,1807,\dots`$. Set $`A=\{a_1,a_2,\dots\}`$ and write $`P_j=a_1a_2\cdots a_j`$. (a) Show that $`\tfrac1{a_1}+\dots+\tfrac1{a_j}=1-\tfrac1{P_j}`$. (b) Show that with $`k=P_j`$ the first $`j`$ exponents leave $`0`$ but the exponent $`P_j+1`$ leaves at least $`\tfrac37`$, so $`R(P_j)\ge\tfrac37`$ for every $`j`$.

</div>

<a id="app:answers"></a>

# Answers

*Question [1](#chk%3Ahypotheses).* Only $`\{2,4,8,16,\dots\}`$: $`\{2,4\}`$ is finite (its sum $`\tfrac25`$ is rational), and for $`\{2,4,6,\dots\}`$ the sum $`\tfrac12+\tfrac14+\tfrac16+\dots`$ is half of $`1+\tfrac12+\tfrac13+\dots`$, which diverges.

*Question [2](#chk%3Apositive).* The identity $`R(k)=((2^k-1)p-qJ(k))/q`$ has an integer numerator. If positive, that numerator is at least $`1`$, so $`R(k)\ge1/q`$. Choosing $`k`$ using $`q`$ does not change this argument: $`2^k-1`$ and $`J(k)`$ remain integers. Zero would give no contradiction. Infinitude supplies a selected $`n>k`$, whose multiplied term is positive and less than $`1`$; all of it contributes to $`R(k)`$, and the other contributions are nonnegative.

*Question [3](#chk%3Acolumns).* The exponents $`A`$ and the original sum $`S`$ stay fixed. The multiplier changes from $`15`$ to $`255`$, and every selected term is transformed using that same multiplier within its column. Separate row minima may come from different columns and need not describe any one multiplier applied to $`S`$.

*Question [4](#chk%3Apartial).* A consecutive cycle has total below $`1`$ and $`n`$ entries, hence mean below $`1/n`$. A sampled cycle selects the smallest remainder from each equal-sized group. Since the fractional parts increase with the remainder, its mean is no larger, even when it has fewer entries. The first value alone, however, is $`\tfrac{15}{63}=\tfrac5{21}=\tfrac{10}{42}`$, more than $`\tfrac16=\tfrac7{42}`$. The complete-cycle bound need not hold for a beginning portion; the separate bound [\[eq:uniform-main\]](#eq%3Auniform-main) covers these too.

*Question [5](#chk%3Aorder).* No: $`2Q'/T=128/512=1/4>1/10`$. Choose $`T`$ again: $`T'=1024`$ still fails, but $`T'=2048`$ works, since $`128/2048=1/16<1/10`$. The middle exponents $`32,64,\dots,2048`$ now have cycle lengths $`1,1,2,4,8,16,32`$, so $`M=64`$ still works. Its validity had to be rechecked, even though its value did not change. This is why $`Q`$ is fixed before $`T`$.

*Exercise [1](#ex%3A2).* The first five entries sum to $`26/31`$; the next two sum to $`4/31`$. All seven therefore average $`30/217`$. The two piece-means, $`26/155`$ and $`2/31`$, must be weighted by their lengths: $`\bigl(5\cdot\tfrac{26}{155}+2\cdot\tfrac2{31}\bigr)/7=30/217`$. Giving the two pieces equal weight would give each entry in the shorter piece more weight than each entry in the longer one.

*Exercise [2](#ex%3A3).* $`3`$ and $`6`$ divide $`12`$, so $`7`$ and $`63`$ divide $`2^{12}-1=4095`$. The remainder of $`12`$ divided by $`5`$ is $`2`$, so the remainder on division by $`31`$ is $`2^2-1=3`$: indeed $`4095=31\times132+3`$.

*Exercise [3](#ex%3A4).* For $`k=3^j`$, exponents $`3^i`$ with $`i\le j`$ divide $`k`$ and leave nothing. Later exponents $`n=3^i`$ leave less than $`\tfrac2{2^{n-k}}`$, and the gaps $`3^i-3^j`$ are different and at least $`2\times3^j`$, so $`R(3^j)<\sum_{e\ge2\times3^j}\tfrac2{2^e}=\tfrac4{2^{2\times3^j}}`$, which is below $`\tfrac1q`$ for large $`j`$.

*Exercise [4](#ex%3A5).* $`(\sqrt2-1)^2=3-2\sqrt2`$ and $`(\sqrt2-1)(3-2\sqrt2)=5\sqrt2-7`$. Also $`(a\sqrt2-c)(3-2\sqrt2)=(3a+2c)\sqrt2-(4a+3c)`$. Start with $`\sqrt2-1=1\sqrt2-1`$. The displayed recurrence preserves nonnegative integer values of $`a`$ and $`c`$, so every odd power $`(\sqrt2-1)^{2i+1}`$ is $`m\sqrt2-j`$ for nonnegative integers $`m`$ and $`j`$, and it is positive. Since $`1^2<2<(3/2)^2`$, we have $`0<\sqrt2-1<\tfrac12`$. Hence $`0<(\sqrt2-1)^{2i+1}<\tfrac1{2\cdot4^i}`$, which is below $`\tfrac1q`$ once $`2\cdot4^i>q`$. By the test, $`\sqrt2`$ is irrational.

*Exercise [5](#ex%3A6).* (a) With $`P_0=1`$, $`a_j=P_{j-1}+1`$ and $`P_j=P_{j-1}a_j`$, so $`\tfrac1{P_{j-1}}-\tfrac1{P_j}=\tfrac{a_j-1}{P_j}=\tfrac1{a_j}`$, and adding these for $`1,\dots,j`$ leaves $`1-\tfrac1{P_j}`$. Since $`P_j\ge2^j`$, these partial sums tend to $`1`$. The set $`A`$ is infinite and satisfies the theorem’s reciprocal-sum hypothesis. (b) The first $`j`$ exponents divide $`P_j`$. The exponent $`P_j+1`$ is bigger than $`k=P_j`$, so it leaves $`\tfrac{2^{P_j}-1}{2^{P_j+1}-1}`$, which is at least $`\tfrac37`$ because $`7(2^{P_j}-1)-3(2^{P_j+1}-1)=2^{P_j}-4\ge0`$. Thus the particular choices $`k=P_j`$ fail to make the remainders small. Other multiples of $`P_j`$ preserve the same initial zeros; averaging lets us search among those choices.

<div class="thebibliography">

9 P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. 12 (1948), 63–66. P. Erdős, [*On the irrationality of certain series*](https://users.renyi.hu/~p_erdos/1969-09.pdf), Math. Student 36 (1968), 222–226 (issued 1969). P. Erdős, [*On the irrationality of certain series: problems and results*](https://users.renyi.hu/~p_erdos/1988-22.pdf), in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge University Press, 1988, 102–109. T. F. Bloom, *Erdős Problem \#257*, <https://www.erdosproblems.com/257>; the statement is quoted in the Formal Conjectures file `FormalConjectures/ErdosProblems/257.lean`. T. Tao and J. Teräväinen, [*Quantitative correlations and some problems on prime factors of consecutive integers*](https://arxiv.org/abs/2512.01739v2), arXiv:2512.01739v2 (submitted December 2025, revised April 2026). W. Cook, [*Irrationality criteria for Lambert subseries*](https://github.com/wcook04/plectis-erdos/blob/0064fc9b2a2693de97aebc8abec26090c3cd1095/paper/257/erdos-257-mersenne-support-subseries.pdf), 30 September 2026. W. Cook, [*Reciprocal Mersenne subseries: support criteria, finite arithmetic and conditional orbit problems*](https://github.com/wcook04/plectis-erdos/blob/0064fc9b2a2693de97aebc8abec26090c3cd1095/paper/257/erdos257-mersenne-reasoning-surface.pdf), 30 September 2026.

</div>
