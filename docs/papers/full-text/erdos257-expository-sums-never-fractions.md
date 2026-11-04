<a id="erdos257-expository-sums-never-fractions"></a>

# Why certain sums of 1/(2^n-1) are irrational

*Authorship and AI use.* Will Cook built and directed the research infrastructure and reviewed the claims when he could. AI agents did most of the research and drafting. Cook did not independently verify every claim. Appendix [9.6](#app%3Alean) identifies the linked formal proof and the limits of its coverage of this exposition.

<a id="sec:intro"></a>

# The question: which infinite sums are irrational?

Every finite sum of fractions is a fraction, and an infinite sum can be one too:
``` math
\frac12+\frac14+\frac18+\dots=1.
```
Now consider
``` math
S=\frac13+\frac1{15}+\frac1{255}+\frac1{65535}+\dots,
```
where the denominators are $`2^2-1,2^4-1,2^8-1,2^{16}-1,\dots`$ and the exponents double at each step. We will prove that this sum is equal to no fraction at all.

To see where such a proof might come from, multiply by $`255`$, the third denominator:
``` math
\begin{aligned}
 255S&=85+17+1+\frac{255}{65535}+\dots\\
     &=103+\frac1{257}+\dots.
\end{aligned}
```
The first three terms have become the integer $`103`$, and a positive remainder is left over. If $`S=p/q`$ with integers $`p,q`$ and $`q>0`$, then multiplying by an integer and subtracting an integer leaves an integer multiple of $`1/q`$, so a positive remainder must be at least $`1/q`$. Our plan is to repeat this construction until the *whole* remainder is smaller than that fixed gap, whatever denominator $`q`$ is proposed.

The example belongs to a larger family, whose fractions are obtained by taking a power of $`2`$, subtracting $`1`$, and taking the reciprocal:

<div class="center">

|  |  |  |  |  |  |  |  |
|:---|---:|---:|---:|---:|---:|---:|:--:|
| exponent $`n`$ | $`1`$ | $`2`$ | $`3`$ | $`4`$ | $`5`$ | $`6`$ | $`\dots`$ |
| $`2^n`$ | $`2`$ | $`4`$ | $`8`$ | $`16`$ | $`32`$ | $`64`$ | $`\dots`$ |
| denominator $`2^n-1`$ | $`1`$ | $`3`$ | $`7`$ | $`15`$ | $`31`$ | $`63`$ | $`\dots`$ |
| term $`1/(2^n-1)`$ | $`1`$ | $`\tfrac13`$ | $`\tfrac17`$ | $`\tfrac1{15}`$ | $`\tfrac1{31}`$ | $`\tfrac1{63}`$ | $`\dots`$ |

</div>

Choose infinitely many of these terms, each at most once, and add them. Choosing the terms amounts to choosing a set $`A`$ of positive integer exponents. The opening example uses $`A=\{2,4,8,16,\dots\}`$, and choosing all even exponents instead gives
``` math
A=\{2,4,6,8,\dots\}:\qquad
 \frac13+\frac1{15}+\frac1{63}+\frac1{255}+\dots.
```
The exponent $`0`$ is excluded, since $`2^0-1=0`$, and we write
``` math
S_A=\sum_{n\in A}\frac1{2^n-1}
```
for the sum of the terms whose exponents belong to $`A`$, taken in increasing order of the exponents. A *partial sum* stops after finitely many selected terms, and to say that $`S_A`$ is *irrational* is to say that $`S_A\ne p/q`$ for all integers $`p,q`$ with $`q>0`$.

For the geometric series at the start, the partial sums are

<div class="center">

|  |  |  |  |  |
|:---|:--:|:--:|:--:|:--:|
| number of terms $`N`$ | $`1`$ | $`2`$ | $`3`$ | $`4`$ |
| $`\tfrac12+\dots+\tfrac1{2^N}`$ | $`\tfrac12`$ | $`\tfrac34`$ | $`\tfrac78`$ | $`\tfrac{15}{16}`$ |
| gap to $`1`$ | $`\tfrac12`$ | $`\tfrac14`$ | $`\tfrac18`$ | $`\tfrac1{16}`$ |

</div>

In general the partial sum is $`1-2^{-N}`$, and its gap to $`1`$ tends to zero; this is what the equation $`\tfrac12+\tfrac14+\tfrac18+\dots=1`$ means.

Every series $`S_A`$ converges: for $`n\ge1`$,
``` math
0<\frac1{2^n-1}\le\frac1{2^{n-1}},\qquad
 \sum_{n=1}^{\infty}\frac1{2^{n-1}}=2.
```
The inequality follows from $`2^n-1\ge2^{n-1}`$, so the partial sums of $`S_A`$ increase and are bounded by $`2`$. A basic property of the real numbers says that an increasing bounded sequence has a finite limit (Appendix [9.1](#app%3Asums)), and the question is whether this limit is rational.

<a id="sec:problem"></a>

# Erdős’s question and the theorem

In a 1988 account, Erdős wrote \[erdos1988, p. 105\] (excerpt):

> “let $`n_1<n_2<\dots`$. Is it then true that $`\sum \frac{1}{2^{n_k}-1}`$ is irrational, …”

Here the indices $`k=1,2,\dots`$ count the chosen exponents $`n_k`$. In these terms, we shall prove the following theorem.

<div id="thm:main" class="theorem">

**Theorem 1**. *Let $`n_1<n_2<\dots`$ be an infinite sequence of positive integers. If $`\sum_{k=1}^{\infty}1/n_k<\infty`$, then*
``` math
\sum_{k=1}^{\infty}\frac1{2^{n_k}-1}
```
*is irrational.*

</div>

With $`A=\{n_1,n_2,\dots\}`$ this series is $`S_A`$, and the hypothesis says that $`\sum_{n\in A}1/n<\infty`$. Erdős’s question for arbitrary infinite $`A`$ remains open \[erdosproblems257\].

The hypothesis concerns the reciprocals of the *exponents*, while the conclusion concerns the fractions with denominators $`2^n-1`$. For the doubling exponents one table shows the difference:

<div class="center">

|  |  |  |  |  |  |
|:---|:--:|:--:|:--:|:--:|:--:|
| chosen exponent $`n`$ | $`2`$ | $`4`$ | $`8`$ | $`16`$ | $`\dots`$ |
| term in the hypothesis, $`1/n`$ | $`\tfrac12`$ | $`\tfrac14`$ | $`\tfrac18`$ | $`\tfrac1{16}`$ | $`\dots`$ |
| term in $`S_A`$, $`1/(2^n-1)`$ | $`\tfrac13`$ | $`\tfrac1{15}`$ | $`\tfrac1{255}`$ | $`\tfrac1{65535}`$ | $`\dots`$ |

</div>

The second row sums to $`1`$, so the theorem says that the third row sums to an irrational number. Every $`S_A`$ converges, so the hypothesis restricts $`A`$ further, for the sake of the irrationality proof.

We shall use the hypothesis in the following form: beyond a sufficiently large exponent, the remaining reciprocals $`1/n`$ add up to less than any positive target we specify. Such a remaining sum is called a *tail*.

The square exponents $`A=\{1,4,9,16,\dots\}`$ also satisfy the hypothesis. Indeed, for $`m\ge2`$,
``` math
\frac1{m^2}<\frac1{m(m-1)}=\frac1{m-1}-\frac1m,
```
so the comparison sum cancels:
``` math
(1-\tfrac12)+(\tfrac12-\tfrac13)+(\tfrac13-\tfrac14)
 +\dots+(\tfrac1{N-1}-\tfrac1N)=1-\tfrac1N<1.
```
Thus $`\sum_{m=2}^{N}1/m^2<1`$, so $`\sum_{m=1}^{\infty}1/m^2`$ converges, and the theorem proves that $`1+\tfrac1{15}+\tfrac1{511}+\tfrac1{65535}+\dots`$ is irrational.

Choosing every positive integer, on the other hand, puts the divergent harmonic series into the hypothesis. To see the divergence, group its terms as $`1`$; $`1/2`$; $`1/3+1/4`$; $`1/5+1/6+1/7+1/8`$; and so on. For example,
``` math
\frac15+\frac16+\frac17+\frac18\ge4\cdot\frac18=\frac12.
```
Each later block doubles the number of terms and halves their smallest value, so it too contributes at least $`1/2`$, and these repeated contributions make the partial sums unbounded. The even exponents fail the hypothesis as well, since their reciprocal sum is half the harmonic series, and the theorem makes no assertion about either choice. Infinitude matters too: $`A=\{2,4\}`$ has a finite reciprocal sum, but $`S_A=\tfrac13+\tfrac1{15}=\tfrac25`$ (Question [1](#chk%3Ahypotheses)).

Erdős proved the theorem in 1968 under the extra assumption that no two chosen exponents share a divisor greater than $`1`$, and remarked that this assumption could be removed, without giving the details \[erdos1968, p. 222\]. We explain a proof that does without it.

The proof has three stages. First, rationality forces a fixed lower bound on certain positive remainders. Next, the special form of the denominators $`2^n-1`$ lets us calculate those remainders. Finally, an average guarantees at least one choice whose *total* remainder lies below that lower bound. The doubling exponents show the construction at work before any averaging is needed, and the main proof ends in Section [7.2](#sec%3Aallchoices). Appendices [9.1](#app%3Asums)–[9.4](#app%3Aproof) justify the supporting facts about infinite sums and divisibility, and can be read as needed or after the main proof; the extension to other bases and the comparison with the formal proof are further reading.

<a id="sec:test"></a>

# A rational number has a fixed positive gap

Start with $`2/5`$. Multiplying it by an integer and subtracting an integer always gives an integer multiple of $`1/5`$:
``` math
3\cdot\frac25-1=\frac15,\quad
 4\cdot\frac25-1=\frac35,\quad
 5\cdot\frac25-2=0,\quad
 1\cdot\frac25-1=-\frac35.
```
No such value lies strictly between $`0`$ and $`1/5`$, because the denominator fixes a smallest possible positive result.

The same reasoning applies to any fraction. From now on we write $`S=S_A`$ for the series belonging to our chosen set $`A`$ and suppose that $`S=p/q`$, where $`p\in\mathbb Z`$ and $`q`$ is a positive integer. For integers $`u,j`$,
``` math
uS-j=\frac{up-jq}{q}.
```
The numerator is an integer, so if $`uS-j>0`$, then $`up-jq\ge1`$ and
``` math
uS-j\ge\frac1q.
```
Positivity matters here, since zero and negative values are perfectly compatible with rationality.

To prove our sum irrational, we shall therefore suppose that $`S=p/q`$ and construct integers $`u,j`$, which may depend on $`q`$, such that

<a id="eq:goal"></a>

``` math
\begin{equation}
\label{eq:goal}
 0<uS-j<\frac1q.
\end{equation}
```

<a id="sec:split"></a>

# Multiplying the series and retaining fractional parts

We want a multiplier that turns some terms into integers. Choose a positive integer $`k`$ and consider $`2^k-1`$; from now on $`k`$ is the exponent of the multiplier and no longer indexes the list $`n_1,n_2,\dots`$. For example, $`15=2^4-1`$ is divisible by $`3=2^2-1`$. Here is what multiplying by $`15`$ does to the first few terms:

<div class="center">

|                |               |                 |              |                 |
|:--------------:|:-------------:|:---------------:|:------------:|:---------------:|
| exponent $`n`$ | original term | multiplied term | integer part | fractional part |
|     $`2`$      |    $`1/3`$    |   $`15/3=5`$    |    $`5`$     |      $`0`$      |
|     $`3`$      |    $`1/7`$    | $`15/7=2+1/7`$  |    $`2`$     |     $`1/7`$     |
|     $`4`$      |   $`1/15`$    |   $`15/15=1`$   |    $`1`$     |      $`0`$      |
|     $`5`$      |   $`1/31`$    |    $`15/31`$    |    $`0`$     |    $`15/31`$    |

</div>

The rows illustrate the operation, and in the chosen series we keep only the rows with $`n\in A`$. For $`x\ge0`$ the integer part $`\lfloor x\rfloor`$ is the greatest integer at most $`x`$, and subtracting it leaves the fractional part $`\{x\}=x-\lfloor x\rfloor\in[0,1)`$. For example, $`2\le15/7<3`$, so we subtract $`2`$ and keep $`1/7`$. Subtracting integer parts in this way keeps every contribution nonnegative.

<a id="the-remainder-can-be-read-from-the-exponents."></a>

#### The remainder can be read from the exponents.

Keep the denominator $`2^n-1`$ fixed and add $`n`$ to $`k`$. Then the identity
``` math
2^{k+n}-1=2^k(2^n-1)+(2^k-1)
```
gives
``` math
\frac{2^{k+n}-1}{2^n-1}=2^k+\frac{2^k-1}{2^n-1}.
```
The added term $`2^k`$ is an integer, so the fractional part is unchanged. Writing $`k=an+r`$ with $`0\le r<n`$ and subtracting $`n`$ from the exponent repeatedly, we reduce the calculation to $`r`$, and since $`0\le2^r-1<2^n-1`$,

<a id="eq:fracpart-main"></a>

``` math
\begin{equation}
\label{eq:fracpart-main}
 \ell_n(k):=\left\{\frac{2^k-1}{2^n-1}\right\}
 =\frac{2^{k\bmod n}-1}{2^n-1}.
\end{equation}
```
Here $`k\bmod n`$ denotes the remainder $`r`$ on division by $`n`$, which lies between $`0`$ and $`n-1`$, and $`\ell_n(k)`$ is the fractional part calculated from it; summing these fractional parts will give $`R(k)`$. For example, $`8=2\cdot3+2`$, so $`\{255/7\}=(2^2-1)/7=3/7`$. The fractional part vanishes when $`n`$ divides $`k`$ and only then, so the multiplier $`2^k-1`$ turns a selected term into an integer if and only if its exponent divides $`k`$. This is why we chose this multiplier: by taking $`k`$ divisible by some selected exponents, we make their contributions vanish.

<a id="what-happens-to-the-entire-sum."></a>

#### What happens to the entire sum.

We apply the same multiplier to every selected term, subtract each integer part, and sum the fractional parts:
``` math
R(k)=\sum_{n\in A}\ell_n(k),\qquad
 J(k)=\sum_{\substack{n\in A\\ n\le k}}
       \left\lfloor\frac{2^k-1}{2^n-1}\right\rfloor.
```
Only exponents $`n\le k`$ contribute to $`J(k)`$, since for $`n>k`$ the multiplied term is already less than $`1`$; thus $`J(k)`$ is a finite sum of integers. Splitting the terms gives

<a id="eq:split-main"></a>

``` math
\begin{equation}
\label{eq:split-main}
 (2^k-1)S=J(k)+R(k).
\end{equation}
```
The series defining $`R(k)`$ converges by comparison with $`(2^k-1)S`$, and Appendix [9.2](#app%3Asplit) justifies the identity using partial sums.

The sum $`R(k)`$ may exceed $`1`$, so it need not be a fractional part itself. For the three exponents $`2,3,6`$ and $`k=5`$, the separate fractional parts sum to
``` math
\left\{\frac{31}3\right\}+\left\{\frac{31}7\right\}
 +\left\{\frac{31}{63}\right\}
 =\frac13+\frac37+\frac{31}{63}=\frac{79}{63}>1.
```
The fractional part of the whole product, by contrast, is $`16/63`$. We keep the separate contributions because each has the formula [\[eq:fracpart-main\]](#eq%3Afracpart-main), and their sum still has the required form $`uS-j`$.

Finally, if $`A`$ is infinite, there is always a selected exponent $`n>k`$. Its multiplied term is positive and less than $`1`$, so it makes a positive contribution to $`R(k)`$, and all other contributions are nonnegative. Therefore
``` math
S=p/q\quad\Longrightarrow\quad
 R(k)=(2^k-1)S-J(k)\ge\frac1q\quad\hbox{for every }k\ge1.
```
Our task is now to find *one* $`k`$ with $`R(k)<1/q`$ (Question [2](#chk%3Apositive)).

<a id="sec:doubling"></a>

# A complete example: the doubling exponents

We return to the opening example, $`A=\{2,4,8,16,\dots\}`$, and can now see why $`255`$ cleared the first three terms: it is $`2^8-1`$, and the exponents $`2,4,8`$ all divide $`8`$. In the new notation the calculation reads
``` math
255S=103+R(8),\qquad R(8)=\frac1{257}+\frac1{16843009}+\dots>0.
```
One small remainder rules out only some denominators, and to rule out every $`q`$ we need remainders as small as we please. For any doubling exponent $`k`$, all selected $`n\le k`$ divide $`k`$ and contribute zero, while every later selected exponent $`n`$ is at least $`2k`$ and gives
``` math
0<\ell_n(k)=\frac{2^k-1}{2^n-1}
 <\frac{2^k}{2^{n-1}}=\frac2{2^{n-k}}.
```
For $`k=8`$ the gaps $`n-k`$ are $`8,24,56,\dots`$, and in general they are distinct integers at least $`k`$. Inserting the missing positive terms, so that the gaps run through *all* integers $`k,k+1,k+2,\dots`$, can only increase the upper bound, and so
``` math
0<R(k)<\sum_{e=k}^{\infty}\frac2{2^e}=\frac4{2^k}.
```
The last equality is the formula for a geometric series whose first term is $`2/2^k`$ and whose ratio is $`1/2`$.

For $`k=8`$ this gives $`R(8)<1/64`$, which rules out every denominator $`q\le64`$, since such a denominator would force $`R(8)\ge1/q\ge1/64`$; for $`k=16`$ the bound is $`R(16)<1/16384`$. Given any proposed denominator $`q`$, we choose a doubling exponent $`k`$ with $`2^k>4q`$, and then $`0<R(k)<1/q`$ contradicts rationality. This completes the proof for the doubling exponents.

What made this work is that each $`k`$ both eliminated all earlier terms and left the next exponent at least $`2k`$. A general set $`A`$ need not have that spacing, and the next section explains how averaging takes its place.

<a id="sec:general"></a>

# Why averaging works

<a id="larger-multipliers-need-not-help."></a>

#### Larger multipliers need not help.

For the square exponents $`A=\{1,4,9,16,\dots\}`$, both $`k=4`$ and $`k=8`$ are divisible by the first two selected exponents $`1`$ and $`4`$, and all later selected exponents exceed $`8`$, so their integer parts vanish for both multipliers. Consequently
``` math
R(4)=15\left(\frac1{511}+\frac1{65535}+\dots\right),\qquad
 R(8)=255\left(\frac1{511}+\frac1{65535}+\dots\right)=17R(4).
```
In fact $`R(4)\approx0.0296`$ and $`R(8)\approx0.503`$: increasing $`k`$ while keeping the same zero contributions has enlarged the remaining terms. Eliminating longer initial groups need not help either. In Exercise [5](#ex%3A6) the next selected exponent is $`k+1`$, which leaves $`(2^k-1)/(2^{k+1}-1)`$, close to $`1/2`$. What matters is which values of $`k`$ we use, and the number of initial rows they make zero is only part of the story.

<a id="one-table-many-attempts"></a>

## One table, many attempts

Keep $`A`$, and hence the original number $`S`$, fixed. For each new choice of $`k`$ we repeat the whole calculation: multiply every selected term by $`2^k-1`$, subtract its integer part, and add what remains to obtain $`R(k)`$. *Each column below is one complete attempt at the contradiction*, and each row follows the contribution of one original term across the attempts. We need one column whose total is less than $`1/q`$.

We choose candidate exponents spaced $`Q`$ apart, $`k=Q,2Q,\dots,MQ`$, so that $`Q`$ is the spacing, $`M`$ is the number of attempts, $`m`$ labels the attempt $`k=mQ`$, and the multiplier itself is $`2^{mQ}-1`$. Neither $`Q`$ nor $`k`$ has to belong to $`A`$. We take $`Q`$ divisible by an initial group of selected exponents, so that those rows stay zero in every column. For the square exponents, $`Q=4`$ gives the following table.

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

Every entry is a fractional part $`\ell_n(k)`$; for example, the cell $`n=9,k=12`$ uses $`12=1\cdot9+3`$, so $`\ell_9(12)=(2^3-1)/(2^9-1)=7/511`$. Each column uses the same multiplier throughout, including in the rows not displayed (Question [3](#chk%3Acolumns)).

<a id="average-complete-attempts."></a>

#### Average complete attempts.

Different rows may be small in different columns, and choosing a separate column for each row would give no single multiplier for the original series. Instead we average *every row across the same columns* and then add the row averages. The result is the average of the complete column totals, since both calculations add the same entries and divide by the same number $`M`$. In symbols,

<a id="eq:average-main"></a>

``` math
\begin{equation}
\label{eq:average-main}
 \frac1M\sum_{m=1}^{M}R(mQ)
 =\sum_{n\in A}\frac1M\sum_{m=1}^{M}\ell_n(mQ).
\end{equation}
```

With infinitely many rows we first use finite portions and then let them grow, and convergence preserves the equality (Appendix [9.4](#app%3Aproof)). If this average is below $`1/q`$, then at least one whole column has total below $`1/q`$, for otherwise every column total would be at least $`1/q`$ and so would their average.

<a id="what-the-two-estimates-will-do."></a>

#### What the two estimates will do.

We shall divide the rows into three groups. An initial finite group stays zero. A further finite group can complete its cycles if $`M`$ is chosen suitably, and we shall bound the average of each such row by $`1/n`$. For the infinitely many remaining rows we need a bound valid for every $`M`$, and we shall prove the bound $`2Q/n`$. Once $`Q`$ is fixed, the sum of these bounds becomes as small as we like if we move far enough down the rows, because the remaining reciprocals $`1/n`$ have arbitrarily small total. Section [7](#sec%3Aproof) chooses the two row cutoffs, and then $`M`$, so that both nonzero groups have small total averages.

<a id="sec:cycles"></a>

## Complete cycles give small averages

To find a rule for every row we look at $`n=3`$ and $`n=6`$, even though they are not exponents of the square series. Start with $`n=3`$ and consecutive $`k`$:

<div class="center">

|               |         |         |       |         |         |       |
|:--------------|:-------:|:-------:|:-----:|:-------:|:-------:|:-----:|
| $`k`$         |  $`1`$  |  $`2`$  | $`3`$ |  $`4`$  |  $`5`$  | $`6`$ |
| $`k\bmod3`$   |  $`1`$  |  $`2`$  | $`0`$ |  $`1`$  |  $`2`$  | $`0`$ |
| $`\ell_3(k)`$ | $`1/7`$ | $`3/7`$ | $`0`$ | $`1/7`$ | $`3/7`$ | $`0`$ |

</div>

One repeating block, or *cycle*, has sum $`4/7<1`$ and average $`4/21<1/3`$. The bound concerns the average only, since one entry, $`3/7`$, exceeds $`1/3`$. For general $`n`$, a consecutive cycle has the remainders $`0,1,\dots,n-1`$. The powers $`2^0,2^1,\dots,2^{n-1}`$ add up to $`2^n-1`$, which is the denominator, and each numerator is one less than the corresponding power, so the total over the cycle is
``` math
\frac{(2^0-1)+(2^1-1)+\dots+(2^{n-1}-1)}{2^n-1}
 <\frac{2^0+2^1+\dots+2^{n-1}}{2^n-1}=1.
```
Dividing by its $`n`$ entries gives a cycle average below $`1/n`$. These reciprocals bound the row averages, and that is why the hypothesis $`\sum_{n\in A}1/n<\infty`$ controls their sum.

<a id="keep-the-required-spacing."></a>

#### Keep the required spacing.

Our candidates move in steps of $`Q`$, because the spacing $`Q`$ is what preserves the initial zero rows. With $`n=6`$ and $`Q=4`$ we find

<div class="center">

|                     |           |          |        |
|:--------------------|:---------:|:--------:|:------:|
| sample number $`m`$ |   $`1`$   |  $`2`$   | $`3`$  |
| $`k=4m`$            |   $`4`$   |  $`8`$   | $`12`$ |
| $`k\bmod6`$         |   $`4`$   |  $`2`$   | $`0`$  |
| $`\ell_6(k)`$       | $`15/63`$ | $`3/63`$ | $`0`$  |

</div>

The last two rows repeat every three samples, only the even remainders occur, and the average is $`(15+3+0)/(3\cdot63)=2/21<1/6`$.

Let $`g=\gcd(n,Q)`$ be the *greatest common divisor*, the largest positive integer dividing both $`n`$ and $`Q`$, and put $`c=n/g`$. In the example $`n=6,Q=4`$ these are $`g=2`$ and $`c=3`$. We shall show that one cycle has $`c`$ samples, which visit $`0,g,2g,\dots,n-g`$ once each in some order; knowing which remainders occur will let us compare the sampled mean with the mean over all remainders. The argument has four steps.

*Possible remainders.* Each remainder is $`mQ`$ minus a multiple of $`n`$, and both are divisible by $`g`$, so each remainder is a multiple of $`g`$. Between $`0`$ and $`n-1`$ there are $`c`$ such multiples, $`0,g,2g,\dots,n-g`$.

*A return after $`c`$ steps.* Since
``` math
cQ=\frac ng Q=n\frac Qg,
```
taking another $`c`$ steps adds a multiple of $`n`$ and leaves the remainder unchanged. So $`c`$ is a period, and it remains to exclude an earlier repetition.

*No earlier repetition.* Two integers have the same remainder on division by $`n`$ if and only if their difference is a multiple of $`n`$. For samples $`m_1<m_2`$ that difference is $`m_2Q-m_1Q=(m_2-m_1)Q`$, so, after dividing out $`g`$, equal remainders mean that $`n/g`$ divides $`(m_2-m_1)(Q/g)`$. The integers $`n/g`$ and $`Q/g`$ have no common divisor greater than $`1`$, that is, they are *coprime*, and this lets us cancel $`Q/g`$: the number $`c=n/g`$ must divide $`m_2-m_1`$. In the example $`n=6,Q=4`$, write $`d=m_2-m_1`$; if $`3`$ divides $`2d`$, it also divides $`d=2(2d)-3d`$, since both terms on the right are multiples of $`3`$. Appendix [9.3](#app%3Acycle) proves the general cancellation fact. Hence samples fewer than $`c`$ steps apart have different remainders.

*All possibilities are visited.* The first $`c`$ remainders are distinct and there are only $`c`$ possible values, so every possible remainder occurs once in each cycle.

<a id="compare-means-without-calculating-a-new-formula."></a>

#### Compare means without calculating a new formula.

Sorting the sampled remainders $`4,2,0`$ as $`0,2,4`$ leaves the sampled mean unchanged, and these remainders begin the pairs $`(0,1)`$, $`(2,3)`$, $`(4,5)`$. Since $`(2^r-1)/(2^n-1)`$ increases with $`r`$, the first remainder of each pair gives its smaller fractional part. We copy each sampled value twice and compare the copies with all six values of the consecutive cycle (Figure [1](#fig%3Acycle-mean)).

<a id="fig:cycle-mean"></a>

<figure data-latex-placement="htbp">

<figcaption>For <span class="math inline"><em>n</em> = 6, <em>Q</em> = 4</span>, two copies of each sample double both sum and count, preserving the mean. Each filled value is at most its outlined counterpart, so the sampled mean is at most the consecutive-cycle mean, which is below <span class="math inline">1/6</span>.</figcaption>
</figure>

In general each group consists of $`g`$ consecutive remainders, and the sample selects the first of them, giving $`0,g,\dots,n-g`$. Repeating each selected value $`g`$ times gives a sum no larger than the sum over all $`n`$ remainders. After division by $`n`$, the copied list has the mean of the $`c`$ samples, while the mean over the consecutive cycle is below $`1/n`$. Thus, whenever $`M`$ is a positive multiple of $`c`$,

<a id="eq:cycle-main"></a>

``` math
\begin{equation}
\label{eq:cycle-main}
 \frac1M\sum_{m=1}^{M}\ell_n(mQ)<\frac1n.
\end{equation}
```
The bound $`1/n`$ is independent of $`Q`$, so making the initial rows zero may require a large spacing without worsening it, provided $`M`$ completes the cycles. If $`n`$ divides $`Q`$, the cycle has the single entry $`0`$, which also satisfies the bound.

<a id="sec:unfinished"></a>

## A bound that also covers unfinished cycles

An unfinished cycle can miss its final zero. For $`n=5`$ and consecutive candidates ($`Q=1`$), one cycle is
``` math
\frac1{31},\quad\frac3{31},\quad\frac7{31},\quad\frac{15}{31},\quad0.
```
The first four entries average $`26/(4\cdot31)=13/62>1/5`$, whereas all five average $`26/(5\cdot31)=26/155<1/5`$, so the increasing positive list and the full cycle obey different bounds (Question [4](#chk%3Apartial) gives a spaced example).

Moreover, finitely many columns cannot complete infinitely many rows: if $`n>MQ`$, the last sample has not even reached the first positive multiple of $`n`$. We therefore need a second estimate, valid for *every* positive $`M`$:

<a id="eq:uniform-main"></a>

``` math
\begin{equation}
\label{eq:uniform-main}
 \frac1M\sum_{m=1}^{M}\ell_n(mQ)\le\frac{2Q}{n}.
\end{equation}
```
For fixed $`Q`$ this bound holds for every $`M`$, so choosing the number of columns later cannot invalidate it. We prove it with the same cycles.

<a id="first-bound-all-the-consecutive-entries."></a>

#### First bound all the consecutive entries.

The $`M`$ sampled exponents $`Q,2Q,\dots,MQ`$ lie among the first $`MQ`$ positive integers, and we first bound the sum over all $`MQ`$ entries. For $`n\ge2`$, consecutive entries beginning at $`k=1`$ repeat the block
``` math
\underbrace{\frac1{2^n-1},\frac3{2^n-1},\dots,
 \frac{2^{n-1}-1}{2^n-1}}_{n-1\text{ positive entries, increasing}},\quad 0.
```

For $`n=2`$ the positive list consists of $`1/3`$ alone. As the calculation for a complete cycle showed, the positive entries sum to less than $`1`$, so their average is less than $`1/(n-1)`$. No beginning portion of this *positive* list has a larger average, because each omitted entry is at least as large as every included entry, and appending the omitted entries therefore cannot lower the average. Thus a nonempty beginning portion has average at most $`2/n`$, since $`1/(n-1)\le2/n`$ for $`n\ge2`$. We left out the final zero for this comparison; the whole block, zero included, already has the stronger bound $`1/n`$.

The first $`MQ`$ entries consist of complete blocks followed, possibly, by a beginning portion of the positive list; for $`n=5`$, for example, the first seven entries have numerators $`(1,3,7,15,0)`$ followed by $`(1,3)`$, all over $`31`$. Each piece has sum at most $`2/n`$ times its number of entries, and the pieces contain $`MQ`$ entries altogether, so their total is at most $`2MQ/n`$. For $`n=1`$ all entries are zero and the bound still holds.

<a id="keep-only-the-sampled-entries."></a>

#### Keep only the sampled entries.

Removing nonnegative entries cannot increase the sum, and hence
``` math
\sum_{m=1}^{M}\ell_n(mQ)
 \le\sum_{k=1}^{MQ}\ell_n(k)\le\frac{2MQ}{n}.
```
Dividing by the number $`M`$ of candidates, we obtain [\[eq:uniform-main\]](#eq%3Auniform-main). This also explains the factor $`Q`$: we bounded $`M`$ sampled entries by all $`MQ`$ consecutive entries. The candidates themselves are unchanged, and at no point did we assume that their sampled values increase.

<a id="sec:proof"></a>

# Combining the estimates

Suppose that $`S=p/q`$. Then every column total $`R(k)`$ is at least $`1/q`$, and we shall contradict this by making a finite average of column totals less than $`1/q`$.

<a id="app:numbers"></a>

## The construction with actual numbers

We use the doubling exponents once more, although we already have a shorter proof for them, because they let us watch the general method at work with actual numbers. Suppose the proposed denominator is $`q=5`$. It is enough to make the average of the column totals less than $`1/5`$, and we allow each of the two nonzero groups less than $`1/10`$. Beyond a doubling exponent $`2^h`$, the reciprocal tail is $`1/2^{h+1}+1/2^{h+2}+\dots=1/2^h`$.

1.  *Decide which early rows to make zero.* Put the first cutoff at the exponent $`t=16`$. The reciprocal sum of all later rows is $`1/16<1/10`$, so any middle group fits within its allowance, whereas the earlier cutoff $`8`$ would give $`1/8>1/10`$.

2.  *Preserve those zeros in every attempt.* Choose $`Q=16`$, which is divisible by $`2,4,8,16`$, so that every candidate $`k=16m`$ gives zero in these four rows.

3.  *Make the infinite far group small despite the factor $`2Q`$.* Applying $`2Q/n`$ to every row beyond $`t=16`$ would bound the sum of their averages only by $`32/16=2`$, and raising a doubling cutoff $`t`$ together with $`Q=t`$ still gives $`2Q/t=2`$. This reflects a limitation of the estimate and says nothing about the size of $`R(k)`$. Instead we keep $`Q=16`$ and put the second cutoff at $`T=512`$, so that the remaining rows have exponents $`1024,2048,\dots`$, and adding the bounds $`32/n`$ on their averages gives
    ``` math
    32\left(\frac1{1024}+\frac1{2048}+\dots\right)
      =\frac{32}{512}<\frac1{10}.
    ```
    A cutoff of $`256`$ would leave $`32/256=1/8`$, more than the allowance $`1/10`$.

4.  *Complete all cycles between the cutoffs.* The middle exponents $`32,64,128,256,512`$ have cycle lengths $`2,4,8,16,32`$, and we choose $`M=64`$, a common multiple of these lengths. Every middle row then completes its cycles, and the far bound remains valid because it holds for every $`M`$.

The cutoffs $`t`$ and $`T`$ are *values of exponents*, and they should be distinguished from counts of terms. The last candidate is $`MQ=1024`$ while the second cutoff is $`T=512`$, because the number of columns and the division of the rows into groups do different jobs. The choice $`M=32`$ would also work; taking $`64`$ shows that we may use more columns without changing either cutoff.

The initial rows contribute zero, and the middle row averages together are less than
``` math
\frac1{32}+\frac1{64}+\frac1{128}+\frac1{256}+\frac1{512}
 =\frac{31}{512}.
```
The far row averages add up to at most $`2Q/T=32/512`$, and hence
``` math
\frac1{64}\sum_{m=1}^{64}R(16m)
 <\frac{31}{512}+\frac{32}{512}=\frac{63}{512}<\frac15.
```
At least one of the 64 complete attempts has $`0<R(k)<1/5`$, which contradicts $`S=p/5`$. The argument proves that some candidate works without identifying which, and that existence is all the contradiction needs.

The first cutoff determines which rows $`Q`$ must keep zero, the second is chosen after $`Q`$ is fixed to compensate for the factor $`2Q`$, and only then do we choose how many columns to use (Question [5](#chk%3Aorder) asks what happens when $`Q`$ changes).

<a id="sec:allchoices"></a>

## The same choices for any admissible set

Let $`A`$ satisfy the hypotheses of the theorem, and suppose that $`S_A=p/q`$, where $`q`$ is a positive integer. Only finitely many positive integers lie below any fixed bound, so the infinite set $`A`$ has arbitrarily large elements, and moving a cutoff farther out can only decrease a reciprocal tail. We may therefore take the cutoffs to be elements $`t<T`$ of $`A`$, so that the initial group contains $`t`$ and the middle group contains $`T`$. The choices are made in the following order:
``` math
t\ \longrightarrow\ Q\ \longrightarrow\ T\ \longrightarrow\ M.
```

1.  Choose $`t\in A`$ such that $`\sum_{n\in A,\,n>t}1/n<1/(2q)`$, which is possible because the reciprocal tails tend to zero.

2.  Choose a positive common multiple $`Q`$ of the selected exponents $`n\le t`$, for instance their product. These exponents divide every candidate $`mQ`$, so their rows are zero.

3.  With $`Q`$ fixed, choose $`T\in A`$ with $`T>t`$ such that $`2Q\sum_{n\in A,\,n>T}1/n<1/(2q)`$; the tails tend to zero, and the coefficient $`2Q`$ is now fixed.

4.  For the finitely many selected $`t<n\le T`$, choose $`M`$ to be a positive common multiple of their cycle lengths $`n/\gcd(n,Q)`$, for instance their product. The far-tail bound remains valid for this final choice of $`M`$.

We add the row averages over these $`M`$ columns:

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
At least one total is therefore below $`1/q`$, which contradicts the lower bound that rationality gives for every column. This proves Theorem [1](#thm%3Amain).

Looking back, infinitude supplied the positivity of the remainders, rationality supplied the fixed gap, and the convergence of $`\sum_{n\in A}1/n`$ supplied both small tails. The order of the choices ensured that all the bounds apply to the same finite collection of complete attempts.

<a id="sec:limits"></a>

# Consequences and limits

For every integer $`b\ge2`$, the same method proves
``` math
A\text{ infinite},\quad\sum_{n\in A}\frac1n<\infty
 \quad\Longrightarrow\quad
 \sum_{n\in A}\frac1{b^n-1}\text{ is irrational}.
```
We replace the multiplier by $`b^k-1`$; the fractional parts become $`(b^{k\bmod n}-1)/(b^n-1)`$, their cycle averages are still below $`1/n`$, and Appendix [9.5](#app%3Abases) checks both estimates.

The theorem covers every selection from the square-exponent series $`1+\tfrac1{15}+\tfrac1{511}+\dots`$. If infinitely many terms remain, their sum is irrational, because deleting terms cannot increase the reciprocal sum $`\sum_{m\ge1}1/m^2<\infty`$ of the exponents, so Theorem [1](#thm%3Amain) still applies; if only finitely many remain, their sum is rational. Thus a selection from this series has a rational sum if and only if it is finite, whatever pattern the retained exponents follow, and the same holds with $`2`$ replaced by any integer $`b\ge2`$.

The reciprocal-sum condition is sufficient for irrationality, and the method stops short of necessity: the remainders $`R(k)`$ need not become arbitrarily small for every infinite $`A`$. When every positive exponent is selected, the terms with $`n>k`$ alone give
``` math
R(k)\ge\sum_{n>k}\frac{2^k-1}{2^n-1}
 >\sum_{n>k}\frac{2^k-1}{2^n}
 =1-2^{-k}\ge\frac12.
```
These remainders therefore never fall below $`1/2`$. Nevertheless, Erdős proved in 1948 that the full sum is irrational \[erdos1948\], and the failure of our method says nothing about rationality. Tao and Teräväinen proved irrationality for the prime exponents \[taoteravainen2025, Theorem 1.3\], another case with divergent reciprocal sum. The short paper \[shortpaper\] gives further sufficient conditions, and the long record \[longrecord\] develops their proofs and the obstructions to extending them. Erdős’s question for every infinite set $`A`$ remains open.

Appendix [9.6](#app%3Alean) describes the formal proof of the theorem and how it differs from the finite-average proof given here.

<a id="app:full"></a>

# Supporting details and formal-proof correspondence

This appendix supplies the details on convergence and limits, the divisibility argument for sampled cycles, the estimates at other bases, and an optional comparison with the formal proof.

<a id="app:sums"></a>

## Convergence and tails

For nonnegative terms $`a_n`$, the partial sums $`\sum_{n=1}^{N}a_n`$ increase. If they are bounded above, let $`L`$ be their least upper bound, the smallest real number that is at least every partial sum. For every $`\varepsilon>0`$ some partial sum exceeds $`L-\varepsilon`$, for otherwise $`L-\varepsilon`$ would be a smaller upper bound, and every later partial sum then lies in $`(L-\varepsilon,L]`$, so the series converges to $`L`$. Its tail after $`N`$ equals $`L-\sum_{n=1}^{N}a_n`$ and tends to zero, which is the property used twice when choosing the cutoffs in Section [7](#sec%3Aproof).

Comparison of series follows by comparing partial sums: if $`0\le a_n\le b_n`$ and $`\sum b_n<\infty`$, then $`\sum a_n\le\sum b_n<\infty`$, and if one term is strictly smaller, the sums differ by at least that positive difference. In particular, restricting a nonnegative series to a subset of its indices can only decrease its sum.

For $`0<x<1`$, multiplying out the finite geometric sum gives
``` math
(1-x)(1+x+\dots+x^{N-1})=1-x^N.
```
Letting $`N\to\infty`$ yields $`\sum_{j=0}^{\infty}x^j=1/(1-x)`$. At $`x=1/2`$ this gives $`\sum_{j=1}^{\infty}2^{-j}=1`$ and, by scaling, $`\sum_{j=h}^{\infty}2^{-j}=2^{1-h}`$. Consequently the bound $`1/(2^n-1)\le2^{1-n}`$ proves that $`S_A`$ converges for every set $`A`$, whether or not $`\sum_{n\in A}1/n`$ converges.

<a id="app:split"></a>

## Passing to the full transformed sum

Fix $`k`$. Each $`\ell_n(k)`$ is nonnegative and at most $`(2^k-1)/(2^n-1)`$, so $`R(k)`$ converges by comparison with $`(2^k-1)S`$, and only selected exponents $`n\le k`$ have nonzero integer parts. For any integer $`L\ge k`$, splitting the finitely many terms up to $`L`$ gives
``` math
(2^k-1)\sum_{\substack{n\in A\\n\le L}}\frac1{2^n-1}
 =J(k)+\sum_{\substack{n\in A\\n\le L}}\ell_n(k).
```
As $`L`$ grows, $`J(k)`$ stays fixed and the two partial sums tend to $`S`$ and $`R(k)`$, which proves [\[eq:split-main\]](#eq%3Asplit-main).

<a id="app:cycle"></a>

## Why the sampled remainders form a cycle

The elementary cancellation fact states that if positive integers $`c,u`$ are coprime and $`c`$ divides $`du`$, then $`c`$ divides $`d`$. The example in Section [6.2](#sec%3Acycles) used $`c=3`$ and $`u=2`$, and for general coprime $`c,u`$ the same argument uses integers $`a,b`$ with $`au+bc=1`$. To see that they exist, let $`v`$ be the smallest positive value of $`au+bc`$ as $`a,b`$ range over the integers; there is at least one positive value, since $`u=1\cdot u+0\cdot c`$. Write $`v=au+bc`$ with coefficients attaining this minimum. Division gives $`u=sv+r`$ with $`0\le r<v`$, so
``` math
r=u-sv=(1-sa)u-sbc.
```
Thus $`r`$ is another integer combination of $`u`$ and $`c`$. If it were positive, it would contradict the minimality of $`v`$, so $`r=0`$ and $`v`$ divides $`u`$. The same reasoning shows that $`v`$ divides $`c`$, and since $`u,c`$ are coprime, $`v=1`$. Now $`d=a(du)+b(dc)`$ proves the cancellation.

Return to $`g=\gcd(n,Q)`$, $`c=n/g`$ and $`u=Q/g`$. The integers $`c,u`$ are coprime, since a larger common divisor would give a common divisor of $`n`$ and $`Q`$ larger than $`g`$. Writing $`x\mid y`$ to mean that $`x`$ divides $`y`$, we see that two sampled exponents $`m_1Q`$ and $`m_2Q`$ have equal remainders if and only if
``` math
n\mid(m_2-m_1)Q
 \quad\Longleftrightarrow\quad
 c\mid(m_2-m_1)u
 \quad\Longleftrightarrow\quad
 c\mid m_2-m_1.
```
Thus the first $`c`$ sampled remainders are distinct and repeat after $`c`$ steps. Every remainder is divisible by $`g`$, since both $`mQ`$ and $`n`$ are, and there are only the $`c`$ possibilities $`0,g,\dots,n-g`$, so each occurs once. This is the remainder rule used in Section [6.2](#sec%3Acycles).

<a id="app:proof"></a>

## Adding the row averages

For finitely many rows $`n\le H`$, adding the row averages is the same as averaging the column totals, since both operations add the same entries and divide by $`M`$. Keep $`Q`$ and $`M`$ fixed. Given any positive target $`\varepsilon`$, each of the $`M`$ convergent column sums $`R(mQ)`$ has tail less than $`\varepsilon`$ beyond some row cutoff, and beyond the largest of these finitely many cutoffs all column tails, and therefore their average, are less than $`\varepsilon`$. Consequently the finite sums of row averages tend to the average of the full column totals. This proves [\[eq:average-main\]](#eq%3Aaverage-main) with only finite rearrangements.

<a id="app:bases"></a>

## Other bases

Let $`b\ge2`$ be an integer; for $`b=3`$, the exponents $`2,4,8,\dots`$ give $`1/8+1/80+1/6560+\dots`$. Convergence and the fractional-part formula carry over, because $`b^n-1\ge2^{n-1}`$ and $`b^{k+n}-1=b^k(b^n-1)+(b^k-1)`$.

For a consecutive cycle, the sum of the fractional parts is
``` math
\frac{(b^0-1)+\dots+(b^{n-1}-1)}{b^n-1}
 <\frac{b^0+b^1+\dots+b^{n-1}}{b^n-1}
 =\frac1{b-1}\le1.
```
Here we used $`1+b+\dots+b^{n-1}=(b^n-1)/(b-1)`$ and $`b\ge2`$. The fractional parts still increase with the remainder, so the comparison by equal groups bounds the average over a complete sampled cycle by the average over a consecutive cycle, which is below $`1/n`$.

For $`n\ge2`$ the $`n-1`$ positive entries still increase and have total less than $`1`$, so the argument for beginning portions in Section [6.3](#sec%3Aunfinished) gives the same bound $`2/n`$ for consecutive entries starting at $`k=1`$, and keeping only the sampled entries gives the bound $`2Q/n`$ for every sampled length $`M`$. For $`n=1`$ the fractional parts are all zero, because $`(b^k-1)/(b-1)`$ is an integer. Both estimates needed for the three groups therefore remain valid, and with the same choices of $`t,Q,T,M`$ the proof shows that $`\sum_{n\in A}1/(b^n-1)`$ is irrational whenever $`A`$ is infinite and $`\sum_{n\in A}1/n<\infty`$ \[shortpaper, Theorem A.1\].

<a id="app:lean"></a>

## The formal proof and how it differs

The theorem is proved in Lean as [`irrational_erdosSupportSeries_of_summable_reciprocal`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean#L395). For every natural number $`b\ge2`$ and every infinite set $`A`$ of natural numbers whose sequence of terms $`1/n`$ for $`n\in A`$ (and $`0`$ otherwise) is summable, it states that the sum of $`1/(b^n-1)`$ over $`A`$ is irrational. Lean’s natural numbers start at $`0`$, and in Lean division by $`0`$ gives $`0`$, so the exponent $`0`$ contributes $`0`$ to both sums; removing it changes neither sum and leaves an infinite set infinite. At $`b=2`$ the statement is therefore Theorem [1](#thm%3Amain), and in general it is the formal version of \[shortpaper, Theorem A.1\]. The Lean kernel accepts the proof, and a [Comparator check](https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-257-mersenne-support-subseries.md#res-reciprocal-support-comparator) confirms, with a second independent kernel checker, that the proof establishes a separately written formal statement. The finite reconstruction in Sections [3](#sec%3Atest)–[7](#sec%3Aproof) and its estimates are ordinary proofs written for this exposition; the formal proof follows its own route and does not check them line by line.

At base $`2`$ the Lean proof follows \[shortpaper, Appendix A\] and takes limits of averages; it reaches the other bases by comparing each base-$`b`$ fractional part with twice the base-$`2`$ one, a different route from Appendix [9.5](#app%3Abases). With the exponent $`0`$ omitted, the shifted quantity used in Lean is
``` math
\sum_{n\in A}\frac{2^{k\bmod n}}{2^n-1}=S_A+R(k),
```
whose value at $`k=0`$ is $`S_A`$, so a value strictly between $`S_A`$ and $`S_A+\varepsilon`$ means $`0<R(k)<\varepsilon`$, the target of our proof. In terms of our fractional parts, the formal proof first fixes $`Q`$ and lets the averaging length tend to infinity. Each row average then tends to its cycle mean, since the unfinished last cycle has bounded length, and throughout this limit the row averages are bounded by $`2(Q+1)/n`$. Because $`Q`$ is fixed and $`\sum_{n\in A}1/n`$ converges, these bounds have small tails, which justifies passing the limit through the sum. The proof then takes $`Q=\operatorname{lcm}(1,\dots,t)`$: every limiting row average with $`n\le t`$ is zero, every other one is at most $`1/n`$, independently of $`t`$, and their total is at most $`\sum_{n\in A,\,n>t}1/n`$, which tends to zero. To obtain one witness it chooses a suitable $`Q`$ first and a sufficiently long average second. Our cutoffs $`t,T`$ and number $`M`$ of columns make those choices explicit, using the separately proved estimate $`2Q/n`$, and under the rationality assumption both arguments make the integer $`qR(k)`$ lie strictly between $`0`$ and $`1`$.

<a id="sec:exercises"></a>

# Questions and exercises

<div id="chk:hypotheses" class="readercheck">

**Question 1**. Which of $`\{2,4\}`$, $`\{2,4,8,16,\dots\}`$ and $`\{2,4,6,8,\dots\}`$ does Theorem [1](#thm%3Amain) apply to?

</div>

<div id="chk:positive" class="readercheck">

**Question 2**. Suppose that $`S=p/q`$. Why is $`0<R(k)<1/q`$ impossible, even when $`k`$ is chosen using $`q`$? Why do we need $`R(k)>0`$, and where does the infinitude of $`A`$ supply it?

</div>

<div id="chk:columns" class="readercheck">

**Question 3**. In the square-exponent table, what stays fixed and what changes when we move from $`k=4`$ to $`k=8`$? Why may we not choose the smallest entry in each row and treat their sum as one successful attempt?

</div>

<div id="chk:partial" class="readercheck">

**Question 4**. Why is the mean over a complete consecutive cycle below $`1/n`$? Why does the same bound hold for a complete sampled cycle, which may have fewer than $`n`$ entries? For $`n=6`$ and $`Q=4`$, the full cycle averages $`\tfrac2{21}<\tfrac16`$. Is the first value alone also below $`\tfrac16`$?

</div>

<div id="chk:order" class="readercheck">

**Question 5**. In Section [7.1](#app%3Anumbers), replace $`Q=16`$ by $`Q'=64`$ and keep $`T=512`$. Does the far bound still give less than $`\tfrac1{10}`$? What must be chosen again?

</div>

<div id="ex:2" class="exercise">

**Exercise 1**. For $`n=5`$ and $`Q=1`$, calculate the mean of the first seven entries by separating them into a complete cycle and a beginning portion of the next. Why is the mean of all seven different from half the sum of the two piece-means?

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

*Question [2](#chk%3Apositive).* In the identity $`R(k)=((2^k-1)p-qJ(k))/q`$ the numerator is an integer, so if it is positive it is at least $`1`$, and $`R(k)\ge1/q`$. Choosing $`k`$ using $`q`$ leaves this argument intact, because $`2^k-1`$ and $`J(k)`$ are still integers. The value zero would give no contradiction. Infinitude supplies a selected $`n>k`$, whose multiplied term is positive and less than $`1`$ and so contributes all of itself to $`R(k)`$, while the other contributions are nonnegative.

*Question [3](#chk%3Acolumns).* The exponents $`A`$ and the original sum $`S`$ stay fixed, while the multiplier changes from $`15`$ to $`255`$, and within a column every selected term is transformed by the same multiplier. The row minima may come from different columns, and then no single multiplier applied to $`S`$ produces them.

*Question [4](#chk%3Apartial).* A consecutive cycle has total below $`1`$ and $`n`$ entries, hence mean below $`1/n`$. A sampled cycle selects the smallest remainder from each group of equal size, and since the fractional parts increase with the remainder, its mean is no larger, even when it has fewer entries. The first value alone, however, is $`\tfrac{15}{63}=\tfrac5{21}=\tfrac{10}{42}`$, which exceeds $`\tfrac16=\tfrac7{42}`$. The bound for complete cycles may fail for a beginning portion, and the separate bound [\[eq:uniform-main\]](#eq%3Auniform-main) is there to cover such portions.

*Question [5](#chk%3Aorder).* No, since $`2Q'/T=128/512=1/4>1/10`$. We must choose $`T`$ again: $`T'=1024`$ still fails, but $`T'=2048`$ works, since $`128/2048=1/16<1/10`$. The middle exponents $`32,64,\dots,2048`$ now have cycle lengths $`1,1,2,4,8,16,32`$, so $`M=64`$ still works, although its validity had to be rechecked even though its value did not change. This is why $`Q`$ is fixed before $`T`$.

*Exercise [1](#ex%3A2).* The first five entries sum to $`26/31`$ and the next two to $`4/31`$, so all seven average $`30/217`$. The two piece-means, $`26/155`$ and $`2/31`$, must be weighted by their lengths, $`\bigl(5\cdot\tfrac{26}{155}+2\cdot\tfrac2{31}\bigr)/7=30/217`$, since equal weights for the two pieces would give each entry of the shorter piece more weight than each entry of the longer one.

*Exercise [2](#ex%3A3).* Both $`3`$ and $`6`$ divide $`12`$, so $`7`$ and $`63`$ divide $`2^{12}-1=4095`$. The remainder of $`12`$ on division by $`5`$ is $`2`$, so the remainder on division by $`31`$ is $`2^2-1=3`$; indeed $`4095=31\times132+3`$.

*Exercise [3](#ex%3A4).* For $`k=3^j`$, the exponents $`3^i`$ with $`i\le j`$ divide $`k`$ and leave nothing. Each later exponent $`n=3^i`$ leaves less than $`\tfrac2{2^{n-k}}`$, and the gaps $`3^i-3^j`$ are distinct and at least $`2\times3^j`$, so $`R(3^j)<\sum_{e\ge2\times3^j}\tfrac2{2^e}=\tfrac4{2^{2\times3^j}}`$, which is below $`\tfrac1q`$ for large $`j`$.

*Exercise [4](#ex%3A5).* We have $`(\sqrt2-1)^2=3-2\sqrt2`$, $`(\sqrt2-1)(3-2\sqrt2)=5\sqrt2-7`$ and $`(a\sqrt2-c)(3-2\sqrt2)=(3a+2c)\sqrt2-(4a+3c)`$. Starting from $`\sqrt2-1=1\sqrt2-1`$, the last recurrence preserves nonnegative integer values of $`a`$ and $`c`$, so every odd power $`(\sqrt2-1)^{2i+1}`$ is $`m\sqrt2-j`$ for nonnegative integers $`m`$ and $`j`$, and it is positive. Since $`1^2<2<(3/2)^2`$, we have $`0<\sqrt2-1<\tfrac12`$, and hence $`0<(\sqrt2-1)^{2i+1}<\tfrac1{2\cdot4^i}`$, which is below $`\tfrac1q`$ once $`2\cdot4^i>q`$. By the test, $`\sqrt2`$ is irrational.

*Exercise [5](#ex%3A6).* (a) With $`P_0=1`$, $`a_j=P_{j-1}+1`$ and $`P_j=P_{j-1}a_j`$, so $`\tfrac1{P_{j-1}}-\tfrac1{P_j}=\tfrac{a_j-1}{P_j}=\tfrac1{a_j}`$, and adding these for $`1,\dots,j`$ leaves $`1-\tfrac1{P_j}`$. Since $`P_j\ge2^j`$, these partial sums tend to $`1`$, so the infinite set $`A`$ satisfies the reciprocal-sum hypothesis of the theorem. (b) The first $`j`$ exponents divide $`P_j`$, and the exponent $`P_j+1`$ exceeds $`k=P_j`$, so it leaves $`\tfrac{2^{P_j}-1}{2^{P_j+1}-1}`$, which is at least $`\tfrac37`$ because $`7(2^{P_j}-1)-3(2^{P_j+1}-1)=2^{P_j}-4\ge0`$. Thus the particular choices $`k=P_j`$ fail to make the remainders small. Other multiples of $`P_j`$ preserve the same initial zeros, and averaging lets us search among them.

<div class="thebibliography">

9 P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. 12 (1948), 63–66. P. Erdős, [*On the irrationality of certain series*](https://users.renyi.hu/~p_erdos/1969-09.pdf), Math. Student 36 (1968), 222–226 (issued 1969). P. Erdős, [*On the irrationality of certain series: problems and results*](https://users.renyi.hu/~p_erdos/1988-22.pdf), in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge University Press, 1988, 102–109. T. F. Bloom, *Erdős Problem \#257*, <https://www.erdosproblems.com/257>; the statement is quoted in the Formal Conjectures file `FormalConjectures/ErdosProblems/257.lean`. T. Tao and J. Teräväinen, [*Quantitative correlations and some problems on prime factors of consecutive integers*](https://arxiv.org/abs/2512.01739v2), arXiv:2512.01739v2 (submitted December 2025, revised April 2026). W. Cook, [*Irrationality criteria for Lambert subseries*](https://github.com/wcook04/plectis-erdos/blob/0064fc9b2a2693de97aebc8abec26090c3cd1095/paper/257/erdos-257-mersenne-support-subseries.pdf), 30 September 2026. W. Cook, [*Reciprocal Mersenne subseries: support criteria, finite arithmetic and conditional orbit problems*](https://github.com/wcook04/plectis-erdos/blob/0064fc9b2a2693de97aebc8abec26090c3cd1095/paper/257/erdos257-mersenne-reasoning-surface.pdf), 30 September 2026.

</div>
