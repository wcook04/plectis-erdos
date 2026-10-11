<a id="erdos257-expository-sums-never-fractions"></a>

# Sums of 1/(2^n-1) that are never fractions

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Take the powers of $`2`$, subtract $`1`$ from each, and put each result under a $`1`$: this gives $`1,\tfrac13,\tfrac17,\tfrac1{15},\tfrac1{31},\dots`$. Erdős asked whether adding up an infinite subset of this list, that is, infinitely many of these fractions with each used at most once, can ever give a fraction. Each fraction comes from an exponent $`n`$: the exponent $`3`$ gives $`\tfrac1{2^3-1}=\tfrac17`$. We prove that the chosen fractions add up to an irrational number whenever $`1/n`$, added up over the chosen exponents $`n`$, is finite. For example, for the exponents $`2,4,8,16,\dots`$ the sum of $`1/n`$ is $`\tfrac12+\tfrac14+\tfrac18+\dots`$, which adds up to $`1`$ (Section 1 shows why), so the chosen fractions $`\tfrac13+\tfrac1{15}+\tfrac1{255}+\tfrac1{65535}+\dots`$ add up to an irrational number. Sections 1 to 8 explain the proof with examples, and Appendix A gives every step in full. A computer has checked a proof of this theorem in the Lean proof assistant; the version written here is checked by hand. For an arbitrary infinite choice the question is still open.

<a id="sec:intro"></a>

# What Erdős asked

Start with the powers of $`2`$, subtract $`1`$ from each, and put each result under a $`1`$:

<div class="center">

|  |  |  |  |  |  |  |  |
|:---|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| exponent $`n`$ | $`1`$ | $`2`$ | $`3`$ | $`4`$ | $`5`$ | $`6`$ | $`\dots`$ |
| $`2^n`$ | $`2`$ | $`4`$ | $`8`$ | $`16`$ | $`32`$ | $`64`$ | $`\dots`$ |
| $`2^n-1`$ | $`1`$ | $`3`$ | $`7`$ | $`15`$ | $`31`$ | $`63`$ | $`\dots`$ |
| fraction $`\dfrac1{2^n-1}`$ | $`1`$ | $`\tfrac13`$ | $`\tfrac17`$ | $`\tfrac1{15}`$ | $`\tfrac1{31}`$ | $`\tfrac1{63}`$ | $`\dots`$ |

</div>

The top row is the *exponent* $`n`$, and the exponent $`n`$ gives the fraction $`1/(2^n-1)`$: the exponent $`3`$ gives $`\tfrac17`$, because $`2^3-1=8-1=7`$. The exponents are $`1,2,3,\dots`$; the exponent $`0`$ is left out, since $`2^0-1=0`$.

Now choose an infinite subset of the list: infinitely many of its fractions, each used at most once. Choosing the subset is the same as choosing its exponents. Add up the fractions in it, for example:

<div class="center">

|  |  |
|:---|:---|
| every exponent $`1,2,3,4,\dots`$: | $`1+\tfrac13+\tfrac17+\tfrac1{15}+\dots`$ |
| the even exponents $`2,4,6,8,\dots`$: | [detail note 1](#paper-table-note-a1a433b510e61a50) |
| the doubling exponents $`2,4,8,16,\dots`$: | [detail note 2](#paper-table-note-f7343e2d61b7acf3) |

<a id="paper-table-note-a1a433b510e61a50"></a> **Detail note 1.** $`\tfrac13+\tfrac1{15}+\tfrac1{63}+\tfrac1{255}+\dots`$

<a id="paper-table-note-f7343e2d61b7acf3"></a> **Detail note 2.** $`\tfrac13+\tfrac1{15}+\tfrac1{255}+\tfrac1{65535}+\dots`$


</div>

Erdős asked whether any choice like this can add up to a fraction: exactly $`\tfrac25`$, say, or $`\tfrac{17}{41}`$, or any other. A number that cannot be written as a fraction is called *irrational*. Its decimal never ends and never settles into a repeating block, like $`\sqrt2=1.41421356\dots`$ (Exercise [5](#ex%3A5) proves that $`\sqrt2`$ is irrational), while a fraction’s decimal either ends, like $`\tfrac34=0.75`$, or repeats for ever, like $`\tfrac17=0.142857\,142857\dots`$.

We can never finish adding infinitely many numbers, so we add them one at a time and watch the *running total*. Take
``` math
\frac12+\frac14+\frac18+\frac1{16}+\dots .
```
The running totals are $`\tfrac12,\tfrac34,\tfrac78,\tfrac{15}{16},\dots`$, and the gaps to $`1`$ are $`\tfrac12,\tfrac14,\tfrac18,\tfrac1{16},\dots`$. Each new number is exactly half of the gap left before it: $`\tfrac14`$ is half of the gap $`\tfrac12`$, and $`\tfrac18`$ is half of the gap $`\tfrac14`$. So the gap halves every time (Figure [1](#fig%3Ahalving)). The running totals therefore never reach $`1`$, and they get as close to $`1`$ as we like: after $`10`$ numbers the gap is $`\tfrac1{1024}`$, and after $`20`$ it is $`\tfrac1{1048576}`$, less than a millionth. That is what
``` math
\frac12+\frac14+\frac18+\frac1{16}+\dots=1
```
means. So infinitely many fractions *can* add up to a fraction, and a proof that our sums are irrational has to use something special about the bottoms $`1,3,7,15,\dots`$.

<a id="fig:halving"></a>

<figure data-latex-placement="htb">

<figcaption>The running totals of <span class="math inline">$\tfrac12+\tfrac14+\tfrac18+\dots$</span>, each on a line from <span class="math inline">0</span> to <span class="math inline">1</span>; the dashed part is the gap to <span class="math inline">1</span>, and each new number fills half of it. The rows go on for ever.</figcaption>
</figure>

Erdős proved in 1948 that choosing every exponent gives an irrational sum \[erdos1948\]. Whether every infinite choice does is Erdős Problem \#257 \[erdosproblems257\], and it is still open.

<a id="sec:problem"></a>

# What this paper proves

We write $`A`$ for the set of chosen exponents, which is an infinite subset of $`1,2,3,\dots`$, and $`\sum_{n\in A}`$ for “add up over the exponents $`n`$ in $`A`$”.

<div id="thm:main" class="theorem">

**Theorem 1**. *Let $`A`$ be an infinite set of positive integers such that the sum $`\sum_{n\in A}1/n`$ is finite. Then*
``` math
\sum_{n\in A}\frac1{2^n-1}
```
*is irrational.*

</div>

For $`A=\{2,4,8,16,\dots\}`$ the theorem reads: $`A`$ is infinite; $`\sum_{n\in A}1/n=\tfrac12+\tfrac14+\tfrac18+\dots=1`$ is finite; so $`\sum_{n\in A}1/(2^n-1)=\tfrac13+\tfrac1{15}+\tfrac1{255}+\dots`$ is irrational. A sum of infinitely many positive numbers is *finite* when its running totals get as close as we like to one number without passing it, as the running totals of $`\tfrac12+\tfrac14+\dots`$ do with $`1`$; Appendix [9.1](#app%3Asums) says exactly what that means and shows that every choice of exponents gives a definite sum. Two more examples:

- *The squares* $`1,4,9,16,\dots`$. Each $`\tfrac1{m^2}`$ after the first is less than $`\tfrac1{(m-1)m}`$, which equals $`\tfrac1{m-1}-\tfrac1m`$: for instance $`\tfrac14<\tfrac12=1-\tfrac12`$ and $`\tfrac19<\tfrac16=\tfrac12-\tfrac13`$. These differences cancel in a chain,
  ``` math
  \Bigl(1-\frac12\Bigr)+\Bigl(\frac12-\frac13\Bigr)+\dots+\Bigl(\frac1{m-1}-\frac1m\Bigr)=1-\frac1m ,
  ```
  so $`\tfrac14+\tfrac19+\dots+\tfrac1{m^2}`$ stays below $`1`$ however far we go, and $`1+\tfrac14+\tfrac19+\dots`$ is finite: its running totals only go up and stay below $`2`$ (Appendix [9.1](#app%3Asums)). The theorem says that $`1+\tfrac1{15}+\tfrac1{511}+\tfrac1{65535}+\dots`$ is irrational.

- *Every exponent* $`1,2,3,4,\dots`$. Now $`1+\tfrac12+\tfrac13+\tfrac14+\dots`$ is infinite: $`\tfrac13+\tfrac14`$ is at least $`\tfrac14+\tfrac14=\tfrac12`$; the next four numbers, $`\tfrac15`$ to $`\tfrac18`$, are each at least $`\tfrac18`$, so they add up to at least $`\tfrac12`$; the next eight add up to at least $`\tfrac12`$ again; and so on, so the running totals pass every number. The theorem says nothing about this choice. (Erdős’s 1948 proof covers it by another method.)

The theorem also needs $`A`$ to be infinite: for $`A=\{2,4\}`$, $`\tfrac12+\tfrac14=\tfrac34`$ is finite, but $`\tfrac13+\tfrac1{15}=\tfrac25`$ is a fraction.

In 1968 Erdős proved Theorem [1](#thm%3Amain) when no two chosen exponents have a common factor bigger than $`1`$, and wrote that this condition could be removed, without giving the details \[erdos1968, p. 222\]. Tao and Teräväinen settled the prime exponents $`2,3,5,7,11,\dots`$ \[taoteravainen2025, Theorem 1.3\]; for the primes $`\sum_{n\in A}1/n`$ is infinite (a theorem of Euler from 1737), so Theorem [1](#thm%3Amain) does not cover them. Theorem [1](#thm%3Amain) with any whole number $`b\ge2`$ in place of $`2`$ is Theorem A.1 of the short paper \[shortpaper\], and a computer has checked a proof of it in the Lean proof assistant (Section [8](#sec%3Alimits)). This paper explains the case $`b=2`$ for a reader new to the problem. It follows \[shortpaper, Appendix A\] and \[longrecord, Section 1.1\] with one change in the last step, explained in Appendix [9.10](#app%3Alean). That version is checked by hand, not by Lean.

<a id="sec:test"></a>

# The test: a fraction cannot leave a tiny positive remainder

Suppose the sum $`S`$ of the chosen fractions were a fraction $`p/q`$, with $`p`$ and $`q`$ whole numbers. Multiply it by a whole number $`m`$ and take away a whole number $`j`$:
``` math
mS-j=\frac{mp}q-\frac{jq}q=\frac{mp-jq}q .
```
The top, $`mp-jq`$, is one whole number minus another. So if $`mS-j`$ is positive, its top is a positive whole number, which is at least $`1`$, and $`mS-j`$ is at least $`\tfrac1q`$.

For example, if $`S`$ were $`\tfrac25`$:
``` math
3\times\frac25-1=\frac15,\qquad 4\times\frac25-1=\frac35,\qquad
 5\times\frac25-2=0,\qquad 1\times\frac25-1=-\frac35 .
```
Every answer lands on one of the marks $`\dots,-\tfrac25,-\tfrac15,0,\tfrac15,\tfrac25,\dots`$ (Figure [2](#fig%3Afifths)), and there is no mark between $`0`$ and $`\tfrac15`$. So a positive answer is at least $`\tfrac15`$, and no choice of $`m`$ and $`j`$ gives $`0.00001`$. The word *positive* matters, since an answer can also be $`0`$ or negative.

<a id="fig:fifths"></a>

<figure data-latex-placement="htb">

<figcaption>Part of the line of fifths, which continues in both directions. Every value of <span class="math inline">$m\times\tfrac25-j$</span> lies on a mark, and the shaded gap between <span class="math inline">0</span> and <span class="math inline">$\tfrac15$</span> contains no mark.</figcaption>
</figure>

This gives the strategy of the whole proof. Whatever bottom $`q`$ someone claims for $`S`$, find whole numbers $`m`$ and $`j`$ with
``` math
0<mS-j<\frac1q .
```
Then $`S`$ is not $`p/q`$, and doing this for every $`q`$ shows that $`S`$ is not a fraction at all. The numbers $`m`$ and $`j`$ are allowed to depend on $`q`$.

<a id="sec:doubling"></a>

# The doubling exponents: multiply by $`2^k-1`$

Take $`S=\tfrac13+\tfrac1{15}+\tfrac1{255}+\tfrac1{65535}+\dots`$ and multiply it by $`255=2^8-1`$. The first three fractions give whole numbers, and the rest give very small ones:
``` math
\frac{255}3=85,\quad \frac{255}{15}=17,\quad \frac{255}{255}=1,\quad
 \frac{255}{65535}=\frac1{257},\quad \frac{255}{2^{32}-1}=\frac1{16843009},\quad\dots .
```
So, with $`103=85+17+1`$,
``` math
255S=103+\Bigl(\frac1{257}+\frac1{16843009}+\dots\Bigr).
```
Take away $`103`$. What is left,
``` math
R(8)=255S-103=\frac1{257}+\frac1{16843009}+\dots\approx0.0039 ,
```
is positive and small. This is the test with $`m=255`$ and $`j=103`$. If $`S`$ were $`p/q`$, then $`R(8)`$ would be at least $`\tfrac1q`$; since $`R(8)`$ is less than $`\tfrac1{64}`$ (shown below), no bottom $`q`$ from $`1`$ to $`64`$ is possible.

The multiplier $`255`$ works because $`3`$, $`15`$ and $`255`$ all divide it. Section [5](#sec%3Asplit) shows that this happens because the exponents $`2`$, $`4`$ and $`8`$ all divide $`8`$. Multiplying by $`2^{16}-1=65535`$ instead makes the first four fractions whole numbers; the exponent $`32`$ leaves $`\tfrac{65535}{2^{32}-1}=\tfrac1{65537}`$, and what is left in total is about $`0.000015`$.

<a id="why-this-works-for-every-bottom."></a>

#### Why this works for every bottom.

Let $`k`$ be any of the doubling exponents, multiply $`S`$ by $`2^k-1`$, and look at each chosen fraction.

- Every chosen exponent up to $`k`$ divides $`k`$, so those fractions give whole numbers.

- Every later chosen exponent $`n`$ is at least $`2k`$, and its fraction gives $`\frac{2^k-1}{2^n-1}`$. This is less than $`\frac{2^k}{2^{n-1}}=\frac2{2^{n-k}}`$, because $`2^n-1`$ is at least half of $`2^n`$.

Take away the whole numbers, and call what is left $`R(k)`$; it is positive, because there is always a chosen exponent beyond $`k`$. The gaps $`n-k`$ between $`k`$ and the later exponents are different whole numbers, all at least $`k`$ (for $`k=8`$ they are $`8,24,56,\dots`$). Allowing every gap from $`k`$ upwards only adds more positive numbers, so
``` math
0<R(k)<\frac2{2^k}+\frac2{2^{k+1}}+\frac2{2^{k+2}}+\dots=\frac4{2^k}.
```
The last step uses the same pattern as $`\tfrac12+\tfrac14+\dots=1`$: when each number is half the one before, the sum is twice the first number. For $`k=8`$ the bound is $`\tfrac1{64}`$, and for $`k=16`$ it is $`\tfrac1{16384}`$.

Now take any bottom $`q`$, and choose a doubling exponent $`k`$ with $`2^k>4q`$. Then $`R(k)<\tfrac4{2^k}<\tfrac1q`$. But $`R(k)`$ is $`S`$ times the whole number $`2^k-1`$, minus a whole number, and it is positive, so if $`S`$ were $`p/q`$ it would be at least $`\tfrac1q`$. It cannot be both. So $`\tfrac13+\tfrac1{15}+\tfrac1{255}+\dots`$ is irrational. That is the whole proof for the doubling exponents (Appendix [9.4](#app%3Adoubling) writes it out as Theorem [6](#thm%3Adoubling)).

<a id="sec:split"></a>

# Why $`2^n-1`$ divides $`2^k-1`$, and what is left when it does not

A whole number divided by another splits into a *whole part* and a *fractional part* that is at least $`0`$ and less than $`1`$: for example $`\tfrac{255}7=36+\tfrac37`$, with whole part $`36`$ and fractional part $`\tfrac37`$. For our numbers the fractional part follows one rule.

Going from $`k`$ to $`k+n`$ multiplies $`2^k`$ by $`2^n`$, and $`2^n`$ is one more than $`2^n-1`$. So $`2^{k+n}-1=2^k(2^n-1)+(2^k-1)`$, and dividing by $`2^n-1`$,
``` math
\frac{2^{k+n}-1}{2^n-1}=2^k+\frac{2^k-1}{2^n-1}.
```
With $`n=3`$, for example, $`\tfrac{63}7=8+\tfrac77`$ (Figure [3](#fig%3Adots)) and $`\tfrac{255}7=32+\tfrac{31}7`$. So adding $`n`$ to $`k`$ adds the whole number $`2^k`$, and adding a whole number does not change the fractional part. For the exponent $`n`$ the fractional part therefore repeats every $`n`$ steps of $`k`$, and depends only on the remainder $`r`$ when $`k`$ is divided by $`n`$. At $`k=r`$ the fraction $`\tfrac{2^r-1}{2^n-1}`$ is less than $`1`$, because $`r`$ is less than $`n`$, so it is its own fractional part. Hence
``` math
\text{the fractional part of }\frac{2^k-1}{2^n-1}\text{ is }\frac{2^r-1}{2^n-1},
 \qquad\text{where $r$ is the remainder when $k$ is divided by $n$.}
```
For $`k=8`$ and $`n=3`$: $`8=2\times3+2`$, so $`r=2`$, and the fractional part is $`\tfrac{2^2-1}7=\tfrac37`$, as above.

The fractional part is $`0`$ exactly when $`r=0`$, that is, when $`n`$ divides $`k`$; we then say that $`k`$ *cancels* the exponent $`n`$. So $`2^n-1`$ divides $`2^k-1`$ exactly when $`n`$ divides $`k`$: $`15=2^4-1`$ divides $`255=2^8-1`$ because $`4`$ divides $`8`$, while $`7=2^3-1`$ does not, because $`3`$ does not divide $`8`$. Here is the exponent $`3`$, with the fraction $`\tfrac17`$, as $`k`$ goes up:

<div class="center">

|  |  |  |  |  |  |  |  |  |  |  |
|:---|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| $`k`$ | $`1`$ | $`2`$ | $`3`$ | $`4`$ | $`5`$ | $`6`$ | $`7`$ | $`8`$ | $`9`$ | $`\dots`$ |
| remainder of $`k`$ divided by $`3`$ | $`1`$ | $`2`$ | $`0`$ | $`1`$ | $`2`$ | $`0`$ | $`1`$ | $`2`$ | $`0`$ | $`\dots`$ |
| fractional part of $`\tfrac{2^k-1}7`$ | $`\tfrac17`$ | $`\tfrac37`$ | $`0`$ | $`\tfrac17`$ | $`\tfrac37`$ | $`0`$ | $`\tfrac17`$ | $`\tfrac37`$ | $`0`$ | $`\dots`$ |

</div>

<a id="fig:dots"></a>

<figure data-latex-placement="htb">

<figcaption>The step from <span class="math inline"><em>k</em> = 3</span> to <span class="math inline"><em>k</em> = 6</span> for the exponent <span class="math inline">3</span>: <span class="math inline">2<sup>6</sup> − 1 = 2<sup>3</sup> × 7 + 7</span>, so <span class="math inline">$\tfrac{63}7=8+\tfrac77=9$</span>. The open circle is the dot removed.</figcaption>
</figure>

<a id="the-sum-of-the-fractional-parts."></a>

#### The sum of the fractional parts.

Now take any infinite set of exponents $`A`$, with sum $`S`$, and any whole number $`k\ge1`$. Multiply every chosen fraction by $`2^k-1`$, take away the whole part of each, and add up the fractional parts. Call the result $`R(k)`$. Two facts make it useful.

- Only exponents up to $`k`$ can have a whole part other than $`0`$, because a later fraction times $`2^k-1`$ is less than $`1`$. So the whole parts add up to a whole number $`J(k)`$, and $`R(k)=(2^k-1)S-J(k)`$: this is the test of Section [3](#sec%3Atest) with $`m=2^k-1`$ and $`j=J(k)`$.

- $`R(k)`$ is positive, because $`A`$ is infinite, so it has a chosen exponent beyond $`k`$, and that fraction times $`2^k-1`$ is all fractional part.

So if $`S`$ were $`p/q`$, then *every* $`R(k)`$ would be at least $`\tfrac1q`$ (Lemma [3](#lem%3Asplit) and Corollary [4](#cor%3Aatleast)). The rest of the proof finds one $`k`$ with $`R(k)<\tfrac1q`$. ($`R(k)`$ adds the separate fractional parts, so it can be bigger than $`1`$; Appendix [9.3](#app%3Asplit) has an example.)

<a id="sec:general"></a>

# Other choices: averaging

<a id="why-cancelling-the-early-exponents-is-not-enough."></a>

#### Why cancelling the early exponents is not enough.

For the squares $`1,4,9,16,\dots`$, both $`k=4`$ and $`k=8`$ cancel exponents $`1`$ and $`4`$, which divide both. Every other square is at least $`9`$, bigger than $`8`$, so each of those fractions is all fractional part, and $`R(k)`$ is the multiplier times the same sum $`\tfrac1{511}+\tfrac1{65535}+\tfrac1{2^{25}-1}+\dots`$ in both cases. The multipliers are $`15`$ and $`255=17\times15`$, so
``` math
R(8)=17\times R(4)\approx0.503,\qquad R(4)\approx0.0296 .
```
The bigger $`k`$ kept the same exponents cancelled and made everything else seventeen times bigger; the exponent $`9`$ alone leaves $`\tfrac{255}{511}\approx0.499`$. Cancelling longer batches does not fix this by itself: Exercise [6](#ex%3A6) gives a choice of exponents and, for every $`j`$, a $`k`$ that cancels the first $`j`$ of them while the very next chosen exponent, $`k+1`$, leaves at least $`\tfrac37`$.

So we use many values of $`k`$ at once. Fix a whole number $`Q`$, the *step*, that every exponent in an early batch of chosen exponents divides, and take
``` math
k=Q,\ 2Q,\ 3Q,\ \dots,\ MQ .
```
Every one of these cancels the batch. If the values $`R(Q),R(2Q),\dots,R(MQ)`$ have an average below $`\tfrac1q`$, then at least one of them is below $`\tfrac1q`$, because if every one were at least $`\tfrac1q`$, so would be their average. (For example, $`3`$, $`5`$ and $`10`$ have average $`6`$, and $`3`$ is below $`6`$.)

<a id="one-exponent-over-a-full-cycle."></a>

#### One exponent over a full cycle.

The exponent $`3`$ leaves $`\tfrac17`$, $`\tfrac37`$, $`0`$ and then repeats. Over one full cycle these average
``` math
\frac13\Bigl(\frac17+\frac37+0\Bigr)=\frac4{21}\approx0.19,
```
less than $`\tfrac13`$. Here is why. Add $`\tfrac17`$ to each fractional part to get $`\tfrac27,\tfrac47,\tfrac17`$. These add up to exactly $`1`$, since $`2+4+1=7`$, so they average exactly $`\tfrac13`$, and the fractional parts themselves average $`\tfrac17`$ less (Figure [4](#fig%3Abars)). One of them, $`\tfrac37`$, is bigger than $`\tfrac13`$; it is the average that is below $`\tfrac13`$. The same works for every exponent $`n`$, because $`1+2+4+\dots+2^{n-1}=2^n-1`$: over a full cycle the fractional parts for the exponent $`n`$ average $`\tfrac1n-\tfrac1{2^n-1}`$, less than $`\tfrac1n`$.

<a id="fig:bars"></a>

<figure data-latex-placement="htb">

<figcaption>The exponent <span class="math inline">3</span> leaves <span class="math inline">$\tfrac17,\tfrac37,0$</span> and repeats (dark bars). With <span class="math inline">$\tfrac17$</span> added (light caps) they are <span class="math inline">$\tfrac27,\tfrac47,\tfrac17$</span>, which average exactly <span class="math inline">$\tfrac13$</span> (solid line), so the fractional parts average <span class="math inline">$\tfrac13-\tfrac17=\tfrac4{21}$</span> (dashed line). Only the averages are compared: the bar <span class="math inline">$\tfrac37$</span> is above <span class="math inline">$\tfrac13$</span>.</figcaption>
</figure>

<a id="steps-of-q."></a>

#### Steps of $`Q`$.

With $`k`$ going up in steps of $`Q`$, an exponent can skip some remainders. Take the exponent $`6`$ with $`Q=4`$: the values $`k=4,8,12`$ leave remainders $`4,2,0`$ when divided by $`6`$, then repeat, so the fractional parts are $`\tfrac{15}{63},\tfrac3{63},0`$, averaging $`\tfrac2{21}`$, which is less than $`\tfrac16`$. The skipped remainders do not spoil the bound, for a reason: the remainders visited are exactly $`0,2,4`$, the multiples of $`2`$, the highest common factor of $`6`$ and $`4`$, each once per cycle. With $`\tfrac1{63}`$ added, the fractional parts are $`\tfrac{16}{63},\tfrac4{63},\tfrac1{63}`$, which add up to $`\tfrac{21}{63}=\tfrac13`$; so they average $`\tfrac19`$, and the fractional parts average $`\tfrac19-\tfrac1{63}=\tfrac2{21}`$. In general, over a full cycle of $`k=Q,2Q,3Q,\dots`$, exponent $`n`$ averages less than $`\tfrac1n`$ (Lemma [7](#lem%3Acycle)).

<a id="unfinished-cycles."></a>

#### Unfinished cycles.

Over part of a cycle the average can be bigger than $`\tfrac1n`$. The exponent $`9`$ with $`Q=4`$ leaves $`\tfrac{15}{511},\tfrac{255}{511},\tfrac7{511},\tfrac{127}{511}`$ at the first four values of $`k`$, which average $`\tfrac{101}{511}`$, more than $`\tfrac19`$; the full cycle of nine values averages $`\tfrac19-\tfrac1{511}`$, below $`\tfrac19`$. With infinitely many exponents, a fixed number $`M`$ of values of $`k`$ always leaves some exponents unfinished: a chosen exponent $`n`$ bigger than $`MQ`$ never even reaches remainder $`0`$. For those exponents we use a weaker bound that holds however few values of $`k`$ we take:
``` math
\text{the average fractional part for the exponent $n$ over }k=Q,2Q,\dots,MQ
 \text{ is at most }\frac{Q+2}n .
```
The idea: a fractional part for the exponent $`n`$ is large only when $`k`$ is just below a multiple of $`n`$. If $`s`$ is the distance from $`k`$ up to the next multiple of $`n`$, the fractional part is less than $`\tfrac1{2^s}+\tfrac1{2^{s+n}}+\tfrac1{2^{s+2n}}+\dots`$. As $`k`$ runs through $`Q,2Q,\dots,MQ`$, each distance $`s`$ comes up at most $`\tfrac{MQ+s}n`$ times, and adding up gives at most $`\tfrac{MQ+2}n`$ in total (Lemma [8](#lem%3Acrude)). The bound grows with $`Q`$ but not with $`M`$, so taking more values of $`k`$ never spoils it.

<a id="sec:proof"></a>

# The proof of Theorem [1](#thm%3Amain)

Suppose the sum $`S`$ were $`p/q`$. We find values of $`k`$ whose values $`R(k)`$ average less than $`\tfrac1q`$. Picture a table with a row for each chosen exponent and a column for each $`k=Q,2Q,\dots,MQ`$; each entry is the fractional part for that exponent at that $`k`$, and each column adds up to $`R(k)`$. We call this table the *grid*, and $`R(k)`$ its bottom row. The average of the column totals equals the sum of the row averages, since both add up the same entries (Appendix [9.7](#app%3Aproof) checks this for infinitely many rows). Split the rows at two cutoffs $`t\le T`$, chosen below, into three groups:

<div class="center">

|  |  |  |
|:---|:---|:---|
| exponents | what we do | contribution to the average |
| early, $`n\le t`$ | choose $`Q`$ so that every one of them divides $`Q`$ | $`0`$ |
| middle, $`t<n\le T`$ | choose $`M`$ so that every one of them finishes whole cycles | less than $`\sum_{n\in A,\,n>t}\tfrac1n`$ |
| far, $`n>T`$ | use the bound $`\tfrac{Q+2}n`$ | at most $`(Q+2)\sum_{n\in A,\,n>T}\tfrac1n`$ |

</div>

The four numbers are chosen in this order, each with a job.

1.  Since $`\sum_{n\in A}1/n`$ is finite, the part of it beyond a cutoff gets as small as we like as the cutoff grows. Choose $`t`$ so that the part beyond $`t`$ is less than $`\tfrac1{2q}`$.

2.  Multiply together the chosen exponents up to $`t`$ (or take $`Q=1`$ if there are none). Every one of them divides $`Q`$, so they leave $`0`$ at every $`k=Q,2Q,\dots`$.

3.  Now that $`Q`$ is fixed, choose $`T`$, at least $`t`$, so that $`Q+2`$ times the part beyond $`T`$ is less than $`\tfrac1{2q}`$. This is why $`T`$ comes after $`Q`$: the far bound contains $`Q+2`$.

4.  There are only finitely many middle exponents. Take $`M`$ to be the product of their cycle lengths (or $`1`$ if there are none), so that every middle row finishes whole cycles.

Then the early rows contribute $`0`$, the middle rows less than $`\tfrac1{2q}`$, and the far rows less than $`\tfrac1{2q}`$. So
``` math
\frac{R(Q)+R(2Q)+\dots+R(MQ)}M<\frac1{2q}+\frac1{2q}=\frac1q ,
```
and at least one of these values $`R(k)`$ is less than $`\tfrac1q`$. But every $`R(k)`$ is positive, so if $`S`$ were $`p/q`$, every one would be at least $`\tfrac1q`$ (Section [5](#sec%3Asplit)). Both cannot hold. The same argument works whatever bottom $`q`$ we start from, so $`S`$ is not a fraction. That proves Theorem [1](#thm%3Amain).

Each assumption did one job. $`A`$ being infinite made every $`R(k)`$ positive. Supposing $`S=p/q`$ made every $`R(k)`$ at least $`\tfrac1q`$. And $`\sum_{n\in A}1/n`$ being finite made the parts beyond $`t`$ and beyond $`T`$ small. Appendix [9.8](#app%3Anumbers) runs the four choices with actual numbers: for the doubling exponents and $`q=5`$ they are $`t=16`$, $`Q=1024`$, $`T=16384`$ and $`M=1024`$.

<a id="sec:limits"></a>

# What the proof shows, and what it does not

<a id="every-exponent."></a>

#### Every exponent.

If every exponent is chosen, then for any $`k`$ the exponents beyond $`k`$ are all fractional part, and
``` math
R(k)>\frac{2^k-1}{2^{k+1}}+\frac{2^k-1}{2^{k+2}}+\dots=\frac{2^k-1}{2^k}\ge\frac12 ,
```
since replacing each bottom $`2^n-1`$ by the bigger $`2^n`$ makes each fraction smaller, and the halving list on the right adds up to twice its first number. So $`R(k)`$ never gets below $`\tfrac12`$ (for instance $`R(7)\approx2.05`$), and this proof cannot reach this choice. Its sum is still irrational, by Erdős’s 1948 argument \[erdos1948\]. A proof for every infinite set of exponents will need more than small values of $`R(k)`$.

<a id="other-bases."></a>

#### Other bases.

The same proof works with any whole number $`b\ge2`$ in place of $`2`$, giving the sums of $`1/(b^n-1)`$, for example $`\tfrac18+\tfrac1{80}+\tfrac1{6560}+\dots`$ for $`b=3`$ and exponents $`2,4,8,\dots`$ (Appendix [9.9](#app%3Abases)).

<a id="what-is-open."></a>

#### What is open.

Theorem [1](#thm%3Amain) answers Erdős’s question for every choice with $`\sum_{n\in A}1/n`$ finite. The short paper \[shortpaper\] proves irrationality under weaker conditions, which include some choices where $`\sum_{n\in A}1/n`$ is infinite, and the long record \[longrecord\] keeps every route tried on the full problem, including those that failed and why. For an arbitrary infinite choice the question is open.

<a id="the-computer-checked-proof."></a>

#### The computer-checked proof.

Lean is a programming language in which a computer checks every step of a proof. The theorem for every base $`b\ge2`$ is the Lean theorem `irrational_erdosSupportSeries_of_summable_reciprocal` ([source at a fixed commit](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean#L395)). Its proof takes about two thousand lines in its own file and the file it builds on, and reading it takes fluency in Lean. A separate tool, Comparator, checked that the proof proves exactly a separately written copy of the statement, using only Lean’s three standard axioms (replay run 35935225572). Neither check says that the Lean statement means the sentence of Theorem [1](#thm%3Amain); Appendix [9.10](#app%3Alean) reads it line by line so the reader can compare. The argument of Sections [3](#sec%3Atest) to [7](#sec%3Aproof) is this paper’s rewriting, checked by hand.

<a id="app:full"></a>

# The proof in full

This appendix proves every step of Sections [3](#sec%3Atest) to [7](#sec%3Aproof), the facts about infinite sums used in Sections [1](#sec%3Aintro) and [2](#sec%3Aproblem), and the other bases of Section [8](#sec%3Alimits). Whole numbers are $`0,1,2,3,\dots`$, and positive integers are $`1,2,3,\dots`$.

<a id="app:sums"></a>

## Adding infinitely many numbers

<a id="adding-up-to-a-number."></a>

#### Adding up to a number.

Infinitely many positive numbers *add up to* a number $`L`$ when their running totals never pass $`L`$ and get as close to $`L`$ as we like: however small a positive number we name, from some point on every running total is within that distance of $`L`$. For $`\tfrac12+\tfrac14+\tfrac18+\dots`$ the running total after $`N`$ numbers is $`1-\tfrac1{2^N}`$ (Section [1](#sec%3Aintro)), and $`\tfrac1{2^N}`$ gets below any positive number we name, since $`2^N`$ doubles at each step and so passes every number. The sum is *finite* when it adds up to some number, and *infinite* when its running totals pass every number.

<a id="halving-lists."></a>

#### Halving lists.

Putting $`1`$ in front of $`\tfrac12+\tfrac14+\dots=1`$ gives $`1+\tfrac12+\tfrac14+\dots=2`$, and multiplying every number by the same amount multiplies every running total, and so the sum, by that amount. So a list in which each number is half the one before adds up to twice its first number: for example $`\tfrac14+\tfrac18+\tfrac1{16}+\dots=\tfrac12`$.

<a id="running-totals-that-only-go-up-and-stay-below-a-fixed-number-add-up-to-a-number."></a>

#### Running totals that only go up and stay below a fixed number add up to a number.

Suppose the running totals only go up and never pass some fixed number. Then they add up to a number, and the decimals show why. Here are the running totals for every exponent:

<div class="center">

|                 |                 |                 |                 |
|:---------------:|:---------------:|:---------------:|:---------------:|
| fractions added |  running total  | fractions added |  running total  |
|      $`1`$      | $`1.0000\dots`$ |      $`6`$      | $`1.5909\dots`$ |
|      $`2`$      | $`1.3333\dots`$ |      $`7`$      | $`1.5988\dots`$ |
|      $`3`$      | $`1.4761\dots`$ |      $`8`$      | $`1.6027\dots`$ |
|      $`4`$      | $`1.5428\dots`$ |      $`9`$      | $`1.6047\dots`$ |
|      $`5`$      | $`1.5751\dots`$ |     $`10`$      | $`1.6057\dots`$ |

</div>

The whole-number part can only go up, and it stays below the fixed number, so it changes only finitely often and then stays fixed; here it is $`1`$ from the start. After that, the first digit after the point can only go up, and it cannot pass $`9`$, so it also changes at most nine times and then stays fixed; here it reads $`0,3,4,5,5,5,5,6,6,6`$. The same holds for the second digit, the third, and every later one. The digits they settle on make one number, here $`1.6066951\dots`$; the running totals never pass it, and once the first $`d`$ digits have settled they are within $`\tfrac1{10^d}`$ of it. So they add up to that number.

<a id="comparison."></a>

#### Comparison.

If each number in one list is at most the matching number in a second list, then each running total of the first is at most the matching running total of the second. So if the second sum is finite, the first is finite and no bigger; if moreover one number of the first list is strictly smaller than its partner, the first sum is strictly smaller, by at least the difference of those two numbers. Leaving numbers out of a list of positive numbers only lowers its running totals.

<a id="the-part-after-a-cutoff."></a>

#### The part after a cutoff.

For a finite sum, the numbers after a cutoff add up to the whole sum minus the running total at the cutoff: for $`\tfrac12+\tfrac14+\dots=1`$ cut after $`\tfrac1{16}`$, the rest is $`\tfrac1{32}+\tfrac1{64}+\dots=\tfrac1{16}=1-\tfrac{15}{16}`$. Since the running totals get as close to the sum as we like, the part after the cutoff gets as small as we like. For a set of exponents $`A`$ and a cutoff $`t`$, the *part of $`\sum_{n\in A}1/n`$ beyond $`t`$* means $`\sum_{n\in A,\,n>t}1/n`$, the sum of $`1/n`$ over the chosen exponents bigger than $`t`$; for the doubling exponents and $`t=4`$ it is $`\tfrac18+\tfrac1{16}+\dots=\tfrac14`$.

<a id="every-choice-of-exponents-gives-a-definite-number."></a>

#### Every choice of exponents gives a definite number.

Compare our fractions with the halving list $`1,\tfrac12,\tfrac14,\tfrac18,\dots`$: exponent by exponent, $`1\le1`$, $`\tfrac13\le\tfrac12`$, $`\tfrac17\le\tfrac14`$, $`\tfrac1{15}\le\tfrac18`$, and in general $`\tfrac1{2^n-1}\le\tfrac1{2^{n-1}}`$, because $`2^n-1=2^{n-1}+(2^{n-1}-1)`$ is at least $`2^{n-1}`$. The halving list adds up to $`2`$, so for every set of exponents $`A`$ the running totals of $`\sum_{n\in A}1/(2^n-1)`$ only go up and never pass $`2`$. So this sum is a definite number $`S_A`$, at most $`2`$.

<a id="app:test"></a>

## The fraction test

<div id="lem:grid" class="lemma">

**Lemma 2** (the fraction test). *Let $`x=p/q`$, where $`p`$ and $`q`$ are whole numbers and $`q\ge1`$. If $`m`$ and $`j`$ are whole numbers and $`mx-j`$ is positive, then $`mx-j\ge\tfrac1q`$.*

</div>

<div class="proof">

*Proof.* $`mx-j=\tfrac{mp-jq}q`$. The top is a whole number minus a whole number, and it is positive because $`mx-j`$ is. So it is a positive whole number, at least $`1`$, and $`mx-j\ge\tfrac1q`$. ◻

</div>

So to prove that a number $`x`$ is irrational it is enough to find, for every positive integer $`q`$, whole numbers $`m`$ and $`j`$ (which may depend on $`q`$) with $`0<mx-j<\tfrac1q`$: if $`x`$ were $`p/q`$, the lemma would give $`mx-j\ge\tfrac1q`$ for that $`q`$. The value $`0`$ must be excluded: $`5\times\tfrac25-2=0`$ is below every $`\tfrac1q`$.

<a id="app:split"></a>

## Whole parts, fractional parts and $`R(k)`$

Dividing a whole number $`a`$ by a positive integer $`b`$ gives $`a=sb+r`$ with whole numbers $`s`$ and $`r`$ and $`0\le r<b`$, so $`\tfrac ab=s+\tfrac rb`$. The *whole part* of $`\tfrac ab`$ is $`s`$ and its *fractional part* is $`\tfrac rb`$, which is at least $`0`$ and less than $`1`$. Only one such pair exists: if $`sb+r=s'b+r'`$ with $`r`$ and $`r'`$ both between $`0`$ and $`b-1`$, then $`r-r'=(s'-s)b`$ is a multiple of $`b`$ strictly between $`-b`$ and $`b`$, so it is $`0`$. We write $`k\mskip 5mu\mathrm{mod}\mskip 5mun`$ for the remainder when $`k`$ is divided by $`n`$, so $`8\mskip 5mu\mathrm{mod}\mskip 5mu3=2`$. Adding a whole number $`w`$ to $`\tfrac ab`$ adds $`w`$ to the whole part and leaves the fractional part unchanged.

Fix a set of exponents $`A`$ with sum $`S=S_A`$. For each chosen exponent $`n`$ and each positive integer $`k`$, write $`\ell_n(k)`$ for the fractional part of $`\tfrac{2^k-1}{2^n-1}`$, and define
``` math
R(k)=\sum_{n\in A}\ell_n(k).
```
It adds the separate fractional parts, so it can be bigger than $`1`$. For the three exponents $`2,3,6`$ and $`k=5`$, the multiplier is $`31`$, and $`\tfrac{31}3=10+\tfrac13`$, $`\tfrac{31}7=4+\tfrac37`$, $`\tfrac{31}{63}=0+\tfrac{31}{63}`$, so the fractional parts add up to
``` math
\frac13+\frac37+\frac{31}{63}=\frac{21+27+31}{63}=\frac{79}{63}=1+\frac{16}{63},
```
while the whole product $`31\times\bigl(\tfrac13+\tfrac17+\tfrac1{63}\bigr)=31\times\tfrac{31}{63}=\tfrac{961}{63}=15+\tfrac{16}{63}`$ has fractional part $`\tfrac{16}{63}`$. The proof always uses the sum of the separate fractional parts.

<div id="lem:split" class="lemma">

**Lemma 3**. *For every positive integer $`k`$, the number $`(2^k-1)S-R(k)`$ is a whole number $`J(k)`$. If $`A`$ is infinite, then $`R(k)>0`$.*

</div>

<div class="proof">

*Proof.* An exponent $`n>k`$ has $`2^n-1>2^k-1`$, so its multiplied fraction is less than $`1`$ and has whole part $`0`$. So only the finitely many chosen exponents up to $`k`$ can have whole parts other than $`0`$, and the whole parts add up to a whole number $`J(k)`$. Each fractional part is at least $`0`$ and at most the multiplied fraction it comes from, and the multiplied fractions add up to $`(2^k-1)S`$, so by comparison $`R(k)`$ is a definite number. For the chosen exponents up to some $`L\ge k`$, splitting each of these finitely many multiplied fractions gives
``` math
(2^k-1)\sum_{\substack{n\in A\\n\le L}}\frac1{2^n-1}
 =J(k)+\sum_{\substack{n\in A\\n\le L}}\ell_n(k).
```
As $`L`$ grows, $`J(k)`$ does not change, and the two sums get as close as we like to $`S`$ and to $`R(k)`$. Hence $`(2^k-1)S=J(k)+R(k)`$. If $`A`$ is infinite, it has a chosen exponent $`n>k`$, because only $`k`$ positive integers are at most $`k`$; that fraction’s fractional part is all of $`\tfrac{2^k-1}{2^n-1}`$, which is positive, and no fractional part is negative. So $`R(k)>0`$. ◻

</div>

<div id="cor:atleast" class="corollary">

**Corollary 4**. *Let $`A`$ be infinite. If $`S=p/q`$ with whole numbers $`p`$ and $`q\ge1`$, then $`R(k)\ge\tfrac1q`$ for every positive integer $`k`$.*

</div>

<div class="proof">

*Proof.* $`R(k)=(2^k-1)S-J(k)`$ is positive, so the fraction test with $`m=2^k-1`$ and $`j=J(k)`$ gives $`R(k)\ge\tfrac1q`$. ◻

</div>

Being infinite gives $`R(k)>0`$ for each $`k`$ separately, through a chosen exponent beyond $`k`$; it gives no single positive number that all the $`R(k)`$ stay above (for the doubling exponents they get as small as we like). The bound $`\tfrac1q`$ comes only from supposing $`S=p/q`$.

<div id="lem:fracpart" class="lemma">

**Lemma 5**. *Let $`k`$ and $`n`$ be positive integers and $`r=k\mskip 5mu\mathrm{mod}\mskip 5mun`$. The fractional part of $`\tfrac{2^k-1}{2^n-1}`$ is*
``` math
\ell_n(k)=\frac{2^r-1}{2^n-1}.
```
*It is $`0`$ exactly when $`n`$ divides $`k`$, and it repeats every $`n`$ steps of $`k`$.*

</div>

<div class="proof">

*Proof.* For every whole number $`j`$, $`2^{j+n}-1=2^j(2^n-1)+(2^j-1)`$, so $`\tfrac{2^{j+n}-1}{2^n-1}=2^j+\tfrac{2^j-1}{2^n-1}`$: adding $`n`$ to the exponent adds the whole number $`2^j`$ and leaves the fractional part unchanged. Write $`k=sn+r`$. Applying this $`s`$ times, the fractional part at $`k`$ equals the fractional part at $`r`$. Since $`0\le r<n`$, the fraction $`\tfrac{2^r-1}{2^n-1}`$ is at least $`0`$ and less than $`1`$, so it is its own fractional part. It is $`0`$ exactly when $`2^r=1`$, that is, when $`r=0`$, which says that $`n`$ divides $`k`$. ◻

</div>

<a id="app:doubling"></a>

## The doubling exponents

<div id="thm:doubling" class="theorem">

**Theorem 6**. *The sum $`\tfrac13+\tfrac1{15}+\tfrac1{255}+\tfrac1{65535}+\dots`$ of the fractions in exponents $`2,4,8,16,\dots`$ is irrational.*

</div>

<div class="proof">

*Proof.* Let $`k`$ be one of the exponents $`2,4,8,\dots`$. Every chosen exponent up to $`k`$ divides $`k`$, so its fractional part is $`0`$ (Lemma [5](#lem%3Afracpart)). Every later chosen exponent $`n`$ is bigger than $`k`$, so its fractional part is the whole multiplied fraction, and since $`2^n-1\ge2^{n-1}`$,
``` math
0<\frac{2^k-1}{2^n-1}<\frac{2^k}{2^{n-1}}=\frac2{2^{n-k}} .
```
The gaps $`n-k`$ are different whole numbers, the smallest being $`2k-k=k`$. Allowing every gap $`e\ge k`$ only adds positive numbers, so by comparison
``` math
0<R(k)<\sum_{e=k}^{\infty}\frac2{2^e}=\frac4{2^k}.
```
If the sum were $`p/q`$, Corollary [4](#cor%3Aatleast) would give $`R(k)\ge\tfrac1q`$ for every $`k`$. But the chosen exponents $`k`$ grow without end, so some $`k`$ has $`2^k>4q`$, and then $`R(k)<\tfrac1q`$. This is a contradiction. ◻

</div>

For example $`R(8)=\tfrac1{257}+\tfrac1{16843009}+\dots\approx0.0039`$, below the bound $`\tfrac1{64}`$, and $`R(16)\approx0.000015`$, below $`\tfrac1{16384}`$.

<a id="app:cycle"></a>

## Averages over a full cycle

<div id="lem:cycle" class="lemma">

**Lemma 7** (average over a cycle). *Let $`n`$ and $`Q`$ be positive integers, let $`g`$ be their highest common factor (the biggest whole number dividing both), and let $`c=n/g`$. As $`m`$ runs through $`1,2,\dots,c`$, the remainders $`mQ\mskip 5mu\mathrm{mod}\mskip 5mun`$ are the numbers $`0,g,2g,\dots,n-g`$, each exactly once, in some order, and after that they repeat with period $`c`$. So for every positive multiple $`M`$ of $`c`$,*
``` math
\frac1M\sum_{m=1}^{M}\ell_n(mQ)=\frac{g}{n(2^g-1)}-\frac1{2^n-1}<\frac1n .
```

</div>

<div class="proof">

*Proof.* *Period $`c`$.* Two values $`m_1<m_2`$ give the same remainder exactly when $`n`$ divides $`(m_2-m_1)Q`$. Since $`cQ=n\times\tfrac Qg`$ and $`\tfrac Qg`$ is a whole number, $`n`$ divides $`cQ`$, so moving $`c`$ steps on never changes the remainder.

*No shorter period.* Let $`d`$ be the smallest positive integer for which $`n`$ divides $`dQ`$; so $`d\le c`$. Divide $`c`$ by $`d`$: $`c=sd+r`$ with $`0\le r<d`$. Both $`cQ`$ and $`sdQ`$ are multiples of $`n`$, so $`rQ`$ is too, and since $`r<d`$, the choice of $`d`$ gives $`r=0`$. So $`d`$ divides $`c`$, and hence $`d`$ divides $`n=cg`$. Now $`dQ=nf`$ for a whole number $`f`$, so $`Q=\tfrac nd\,f`$: the whole number $`\tfrac nd`$ divides both $`n`$ and $`Q`$, and therefore $`\tfrac nd\le g`$, that is, $`d\ge c`$. So $`d=c`$.

*Which remainders occur.* If two of $`m=1,\dots,c`$ gave the same remainder, $`n`$ would divide $`(m_2-m_1)Q`$ with $`0<m_2-m_1<c=d`$, which is impossible. So the first $`c`$ values give $`c`$ different remainders, each a multiple of $`g`$ (because $`g`$ divides $`mQ`$ and $`n`$). There are exactly $`c`$ multiples of $`g`$ from $`0`$ to $`n-g`$, so each occurs once.

*The average.* By Lemma [5](#lem%3Afracpart) the fractional parts over one cycle are $`\tfrac{2^{ig}-1}{2^n-1}`$ for $`i=0,1,\dots,c-1`$. Add $`\tfrac1{2^n-1}`$ to each. With $`G=1+2^g+2^{2g}+\dots+2^{(c-1)g}`$, we have $`2^gG-G=2^{cg}-1=2^n-1`$, so these add up to
``` math
\frac G{2^n-1}=\frac1{2^g-1}.
```
Divide by the $`c=\tfrac ng`$ values and take away the amount added to each: the average is $`\tfrac g{n(2^g-1)}-\tfrac1{2^n-1}`$. A whole number of cycles has the same average. Finally $`2^g-1=1+2+\dots+2^{g-1}\ge g`$, so $`\tfrac g{n(2^g-1)}\le\tfrac1n`$, and taking away the positive amount $`\tfrac1{2^n-1}`$ leaves less than $`\tfrac1n`$. ◻

</div>

For $`n=6`$ and $`Q=4`$: $`g=2`$, $`c=3`$, and the average is $`\tfrac2{6\times3}-\tfrac1{63}=\tfrac19-\tfrac1{63}=\tfrac2{21}`$, as in Section [6](#sec%3Ageneral). For $`n=3`$ and $`Q=1`$ it is $`\tfrac13-\tfrac17=\tfrac4{21}`$.

<a id="app:crude"></a>

## The bound for unfinished cycles

<div id="lem:crude" class="lemma">

**Lemma 8**. *For all positive integers $`n`$, $`Q`$ and $`M`$,*
``` math
\frac1M\sum_{m=1}^{M}\ell_n(mQ)\le\frac{Q+2}{n} .
```

</div>

<div class="proof">

*Proof.* *One fractional part.* Fix $`N\ge1`$ and let $`r=N\mskip 5mu\mathrm{mod}\mskip 5mun`$. The distances $`s\ge1`$ from $`N`$ up to the later multiples of $`n`$ are $`n-r,\,2n-r,\,3n-r,\dots`$. Call $`X=\tfrac1{2^{n-r}}+\tfrac1{2^{2n-r}}+\tfrac1{2^{3n-r}}+\dots`$, which is finite by comparison with a halving list. Multiplying $`X`$ by $`2^n`$ gives $`2^r+X`$, so $`(2^n-1)X=2^r`$ and $`X=\tfrac{2^r}{2^n-1}`$. Hence
``` math
\ell_n(N)=\frac{2^r-1}{2^n-1}<\frac{2^r}{2^n-1}
 =\frac1{2^{n-r}}+\frac1{2^{2n-r}}+\frac1{2^{3n-r}}+\dots
 =\sum_{\substack{s\ge1\\n\text{ divides }N+s}}\frac1{2^s} .
```
For example $`\ell_6(4)=\tfrac{15}{63}<\tfrac{16}{63}=\tfrac1{2^2}+\tfrac1{2^8}+\tfrac1{2^{14}}+\dots`$, the distances from $`4`$ to $`6,12,18,\dots`$ being $`2,8,14,\dots`$.

*Cut off at $`H`$.* Fix a positive integer $`H`$. The terms with $`s>H`$ add up to at most $`\sum_{s>H}2^{-s}=2^{-H}`$, so for each $`m=1,\dots,M`$,
``` math
\ell_n(mQ)<\sum_{\substack{1\le s\le H\\n\text{ divides }mQ+s}}\frac1{2^s}+\frac1{2^H}.
```

*Count by distance.* Add these $`M`$ inequalities. The right side now has finitely many terms, so we may collect them by distance. For each $`s`$, let $`C_s`$ be the number of $`m`$ for which $`n`$ divides $`mQ+s`$. The numbers $`Q+s,2Q+s,\dots,MQ+s`$ are different and none is bigger than $`MQ+s`$, and there are at most $`\tfrac{MQ+s}n`$ multiples of $`n`$ from $`1`$ to $`MQ+s`$; so $`C_s\le\tfrac{MQ+s}n`$. Hence
``` math
\sum_{m=1}^{M}\ell_n(mQ)<\frac{MQ}n\sum_{s=1}^{H}\frac1{2^s}+\frac1n\sum_{s=1}^{H}\frac s{2^s}+\frac M{2^H}.
```
The first sum is $`1-\tfrac1{2^H}<1`$. For the second, $`U_H=\sum_{s=1}^{H}\tfrac s{2^s}`$, take away half of it from itself: the terms pair off as $`\tfrac s{2^s}-\tfrac{s-1}{2^s}=\tfrac1{2^s}`$, so $`U_H-\tfrac{U_H}2=1-\tfrac1{2^H}-\tfrac H{2^{H+1}}`$ and $`U_H=2-\tfrac{H+2}{2^H}<2`$. So $`\sum_{m=1}^{M}\ell_n(mQ)<\tfrac{MQ+2}n+\tfrac M{2^H}`$.

*Let $`H`$ grow.* The left side does not depend on $`H`$, and $`\tfrac M{2^H}`$ gets below any positive number we name, so the left side is at most $`\tfrac{MQ+2}n`$. Dividing by $`M\ge1`$ gives at most $`\tfrac{Q+2/M}n\le\tfrac{Q+2}n`$. ◻

</div>

For $`n=6`$, $`Q=4`$ and $`M=2`$, the actual average is $`\tfrac{15+3}{2\times63}=\tfrac17`$ and the bound is $`\tfrac{4+2}6=1`$: weak, but once $`Q`$ is fixed it is the same multiple of $`\tfrac1n`$ for every $`M`$.

<a id="app:proof"></a>

## The proof of Theorem [1](#thm%3Amain)

Let $`A`$ be infinite with $`\sum_{n\in A}1/n`$ finite, and suppose $`S=p/q`$ with whole numbers $`p`$ and $`q\ge1`$. By Corollary [4](#cor%3Aatleast),

<a id="eq:atleast"></a>

``` math
\begin{equation}
\label{eq:atleast}
 R(k)\ge\frac1q\qquad\text{for every positive integer }k .
\end{equation}
```

*The four choices.* By the part after a cutoff (Appendix [9.1](#app%3Asums)), choose $`t`$ with $`\sum_{n\in A,\,n>t}\tfrac1n<\tfrac1{2q}`$. Let $`Q`$ be the product of the chosen exponents up to $`t`$, or $`1`$ if there are none; each of them divides every $`mQ`$, so leaves $`0`$ there (Lemma [5](#lem%3Afracpart)). With $`Q`$ fixed, choose $`T\ge t`$ with $`(Q+2)\sum_{n\in A,\,n>T}\tfrac1n<\tfrac1{2q}`$. Let $`M`$ be the product of the cycle lengths $`\tfrac n{g}`$ (with $`g`$ the highest common factor of $`n`$ and $`Q`$) of the finitely many chosen exponents with $`t<n\le T`$, or $`1`$ if there are none.

*Adding by rows.* We need
``` math
\frac1M\sum_{m=1}^{M}R(mQ)=\sum_{n\in A}\frac1M\sum_{m=1}^{M}\ell_n(mQ).
```
Keep only the rows $`n\le H`$; then both sides add the same finitely many entries and agree. Every entry in a row $`n`$ is at most $`\tfrac{2^{MQ}-1}{2^n-1}\le(2^{MQ}-1)\tfrac2{2^n}`$, so the rows $`n>H`$ add at most $`E_H=(2^{MQ}-1)\tfrac2{2^H}`$ to each side. With $`Q`$ and $`M`$ fixed, $`E_H`$ gets below any positive number we name as $`H`$ grows, so the two sides are equal.

*The three groups.* Rows $`n\le t`$ contribute $`0`$. Each middle row $`t<n\le T`$ finishes whole cycles, so by Lemma [7](#lem%3Acycle) its average is less than $`\tfrac1n`$, and together they contribute at most $`\sum_{n\in A,\,t<n\le T}\tfrac1n\le\sum_{n\in A,\,n>t}\tfrac1n<\tfrac1{2q}`$ (“at most” because the middle group may be empty). By Lemma [8](#lem%3Acrude), the far rows contribute at most $`(Q+2)\sum_{n\in A,\,n>T}\tfrac1n<\tfrac1{2q}`$. So the average of $`R(Q),\dots,R(MQ)`$ is less than $`\tfrac1q`$, and at least one of them is less than $`\tfrac1q`$, contradicting [\[eq:atleast\]](#eq%3Aatleast). Since $`q`$ was arbitrary, $`S`$ is irrational.0◻

<a id="app:numbers"></a>

## The four choices with actual numbers

Take the doubling exponents and $`q=5`$, so the middle and far groups each get $`\tfrac1{2q}=\tfrac1{10}`$. Beyond a doubling exponent $`2^h`$, the part of $`\sum_{n\in A}1/n`$ is $`\tfrac1{2^{h+1}}+\tfrac1{2^{h+2}}+\dots=\tfrac1{2^h}`$.

- $`t=16`$: the part beyond it is $`\tfrac1{16}<\tfrac1{10}`$ ($`t=8`$ fails, since $`\tfrac18>\tfrac1{10}`$).

- $`Q=2\times4\times8\times16=1024`$.

- $`T=16384`$: $`\tfrac{Q+2}{16384}=\tfrac{1026}{16384}<\tfrac1{10}`$, since $`10260<16384`$ ($`T=8192`$ fails, since $`10260>8192`$).

- The middle exponents are $`32,64,\dots,16384`$, with cycle lengths $`1,1,1,1,1,1,2,4,8,16`$ (each is $`n`$ divided by the smaller of $`n`$ and $`1024`$), so $`M=2\times4\times8\times16=1024`$.

The middle rows contribute less than $`\tfrac1{32}+\tfrac1{64}+\dots+\tfrac1{16384}=\tfrac{1023}{16384}`$ and the far rows at most $`\tfrac{1026}{16384}`$, so the average of $`R(1024m)`$ over $`m=1,\dots,1024`$ is less than $`\tfrac{2049}{16384}`$, which is less than $`\tfrac15`$ because $`5\times2049=10245<16384`$. So some $`R(k)`$ is below $`\tfrac15`$, which rules out $`S=p/5`$ (in fact every bottom up to $`7`$, since $`7\times2049=14343<16384`$). The largest $`k`$ used is $`1024\times1024=1048576`$; the multiplier $`2^{1048576}-1`$ is never written out, because every step uses only the bounds.

<a id="app:bases"></a>

## Other bases

Replace $`2`$ by a whole number $`b\ge2`$. For $`b=3`$ the list is $`\tfrac12,\tfrac18,\tfrac1{26},\tfrac1{80},\dots`$, and exponents $`2,4,8,\dots`$ give $`\tfrac18+\tfrac1{80}+\tfrac1{6560}+\dots`$. Each step above carries over: $`b^n-1\ge2^{n-1}`$, so the comparisons hold; the same calculation as in Lemma [5](#lem%3Afracpart) gives the fractional part $`\tfrac{b^r-1}{b^n-1}`$ with $`r=k\mskip 5mu\mathrm{mod}\mskip 5mun`$; Lemma [7](#lem%3Acycle) gives the average $`\tfrac g{n(b^g-1)}-\tfrac1{b^n-1}<\tfrac1n`$, since $`b^g-1\ge g`$; and in Lemma [8](#lem%3Acrude), with $`\tfrac1b`$ in place of $`\tfrac12`$, the first sum is at most $`\tfrac1{b-1}\le1`$ and the second at most $`\tfrac b{(b-1)^2}=\tfrac1{b-1}+\tfrac1{(b-1)^2}\le2`$, so the bound $`\tfrac{Q+2}n`$ still holds. So for every $`b\ge2`$, $`\sum_{n\in A}1/(b^n-1)`$ is irrational whenever $`A`$ is infinite and $`\sum_{n\in A}1/n`$ is finite \[shortpaper, Theorem A.1\].

<a id="app:lean"></a>

## The Lean statement

<div class="center">

<div class="minipage">

theorem irrational_erdosSupportSeries_of_summable_reciprocal\
(b : $`\mathbb{N}`$) (A : Set $`\mathbb{N}`$) (hb : 2 $`\le`$ b) (hA : A.Infinite)\
(hsum : Summable (reciprocalSupportTerm A)) :\
Irrational (erdosSupportSeries b A)

</div>

</div>

Line by line: $`b`$ is a whole number and `hb` assumes $`b\ge2`$; $`A`$ is a set of whole numbers and `hA` assumes it is infinite; `reciprocalSupportTerm A` is the list whose entry at $`n`$ is $`1/n`$ when $`n`$ is in $`A`$ and $`0`$ otherwise, and `hsum` assumes its sum is finite; the conclusion says that `erdosSupportSeries b A`, the sum of $`1/(b^n-1)`$ over $`A`$, is irrational. Lean’s whole numbers start at $`0`$, and in Lean dividing by $`0`$ gives $`0`$, so the exponent $`0`$ counts as $`0`$ in both sums; removing it changes neither sum and leaves an infinite set infinite. So for $`b=2`$ the statement says the same as Theorem [1](#thm%3Amain). It is the formal version of \[shortpaper, Theorem A.1\].

The Lean kernel, a small program, has checked every step of the proof. Comparator checked that the proof proves exactly a separately written formal statement, one of eight theorems restated in the challenge `E257_47`, using only the axioms `propext`, `Quot.sound` and `Classical.choice`. The replay run 35935225572 passed, and its [Comparator receipt](https://github.com/wcook04/plectis-erdos/blob/0064fc9b2a2693de97aebc8abec26090c3cd1095/evidence/comparator/replay-35935225572/receipt-E257_47.json) records acceptance by Lean’s kernel and by a second, independent kernel checker. At base $`2`$ the Lean proof follows \[shortpaper, Appendix A\], which takes limits of averages; it reaches the other bases by comparing each base-$`b`$ fractional part with twice the base-$`2`$ one, a different route from Appendix [9.9](#app%3Abases). The finite average of Appendix [9.7](#app%3Aproof) is this paper’s rewriting, checked by hand.

<a id="sec:exercises"></a>

# Questions and exercises

<div id="chk:hypotheses" class="readercheck">

**Question 1**. Which of $`\{2,4\}`$, $`\{2,4,8,16,\dots\}`$ and $`\{2,4,6,8,\dots\}`$ does Theorem [1](#thm%3Amain) apply to?

</div>

<div id="chk:positive" class="readercheck">

**Question 2**. If $`A`$ is infinite and $`k`$ cancels every chosen exponent up to $`k`$, why is $`R(k)`$ still not $`0`$?

</div>

<div id="chk:partial" class="readercheck">

**Question 3**. For the exponent $`6`$ and $`Q=4`$ the full cycle averages $`\tfrac2{21}<\tfrac16`$. Is the first value alone also below $`\tfrac16`$?

</div>

<div id="chk:order" class="readercheck">

**Question 4**. In Appendix [9.8](#app%3Anumbers), replace $`Q=1024`$ by $`Q'=4096`$ and keep $`T=16384`$. Does the far bound still give less than $`\tfrac1{10}`$? What must be chosen again?

</div>

<div id="ex:1" class="exercise">

**Exercise 1**. Write $`\tfrac13+\tfrac17+\tfrac1{63}`$ as a single fraction in lowest terms.

</div>

<div id="ex:2" class="exercise">

**Exercise 2**. List the fractional parts of $`\tfrac{2^k-1}{15}`$ for $`k=1,\dots,8`$, and check that their average over one cycle is $`\tfrac14-\tfrac1{15}`$.

</div>

<div id="ex:3" class="exercise">

**Exercise 3**. Use Lemma [5](#lem%3Afracpart) to show that $`2^{12}-1`$ is divisible by $`7`$ and by $`63`$, and find its remainder on division by $`2^5-1=31`$.

</div>

<div id="ex:4" class="exercise">

**Exercise 4**. Adapt the proof of Theorem [6](#thm%3Adoubling) to the exponents $`3,9,27,81,\dots`$, using $`k=3^j`$.

</div>

<div id="ex:5" class="exercise">

**Exercise 5**. Show that $`5\sqrt2-7=(\sqrt2-1)^3`$, and that multiplying a number $`a\sqrt2-c`$ by $`3-2\sqrt2`$ gives another number of that form. Use the test of Section [3](#sec%3Atest) to show that $`\sqrt2`$ is irrational.

</div>

<div id="ex:6" class="exercise">

**Exercise 6**. Let $`a_1=2`$ and let each later exponent be one more than the product of the earlier ones, giving $`2,3,7,43,1807,\dots`$, and write $`P_j=a_1a_2\cdots a_j`$. (a) Show that $`\tfrac1{a_1}+\dots+\tfrac1{a_j}=1-\tfrac1{P_j}`$. (b) Show that with $`k=P_j`$ the first $`j`$ exponents leave $`0`$ but the exponent $`P_j+1`$ leaves at least $`\tfrac37`$, so $`R(P_j)\ge\tfrac37`$ for every $`j`$.

</div>

<a id="app:answers"></a>

# Answers

*Question [1](#chk%3Ahypotheses).* Only $`\{2,4,8,16,\dots\}`$: $`\{2,4\}`$ is finite (its sum $`\tfrac25`$ is a fraction), and for $`\{2,4,6,\dots\}`$ the sum $`\tfrac12+\tfrac14+\tfrac16+\dots`$ is half of $`1+\tfrac12+\tfrac13+\dots`$, which is infinite.

*Question [2](#chk%3Apositive).* $`A`$ is infinite, so some chosen exponent $`n`$ is bigger than $`k`$; that fraction times $`2^k-1`$ is positive and less than $`1`$, so all of it is fractional part.

*Question [3](#chk%3Apartial).* No: the first value leaves $`\tfrac{15}{63}=\tfrac5{21}=\tfrac{10}{42}`$, more than $`\tfrac16=\tfrac7{42}`$. The full-cycle bound says nothing about part of a cycle, which is why Lemma [8](#lem%3Acrude) is needed.

*Question [4](#chk%3Aorder).* No: $`\tfrac{4098}{16384}=\tfrac{2049}{8192}`$ is more than $`\tfrac1{10}`$, since $`20490>8192`$. $`T`$ must be chosen again, for instance $`T'=65536`$, where $`\tfrac{4098}{65536}=\tfrac{2049}{32768}<\tfrac1{10}`$, and then $`M`$ again. This is why $`Q`$ is fixed before $`T`$.

*Exercise [1](#ex%3A1).* $`\tfrac{21}{63}+\tfrac9{63}+\tfrac1{63}=\tfrac{31}{63}`$, already in lowest terms, since $`31`$ is prime and does not divide $`63`$.

*Exercise [2](#ex%3A2).* The remainders of $`k=1,\dots,8`$ divided by $`4`$ are $`1,2,3,0,1,2,3,0`$, so the fractional parts are $`\tfrac1{15},\tfrac3{15},\tfrac7{15},0,\tfrac1{15},\tfrac3{15},\tfrac7{15},0`$. One cycle adds up to $`\tfrac{11}{15}`$, so the average is $`\tfrac{11}{60}=\tfrac14-\tfrac1{15}`$.

*Exercise [3](#ex%3A3).* $`3`$ and $`6`$ divide $`12`$, so $`7`$ and $`63`$ divide $`2^{12}-1=4095`$. The remainder of $`12`$ divided by $`5`$ is $`2`$, so the remainder on division by $`31`$ is $`2^2-1=3`$: indeed $`4095=31\times132+3`$.

*Exercise [4](#ex%3A4).* For $`k=3^j`$, exponents $`3^i`$ with $`i\le j`$ divide $`k`$ and leave nothing. Later exponents $`n=3^i`$ leave less than $`\tfrac2{2^{n-k}}`$, and the gaps $`3^i-3^j`$ are different and at least $`2\times3^j`$, so $`R(3^j)<\sum_{e\ge2\times3^j}\tfrac2{2^e}=\tfrac4{2^{2\times3^j}}`$, which is below $`\tfrac1q`$ for large $`j`$.

*Exercise [5](#ex%3A5).* $`(\sqrt2-1)^2=3-2\sqrt2`$ and $`(\sqrt2-1)(3-2\sqrt2)=5\sqrt2-7`$. Also $`(a\sqrt2-c)(3-2\sqrt2)=(3a+2c)\sqrt2-(4a+3c)`$. So every odd power $`(\sqrt2-1)^{2i+1}`$ is $`m\sqrt2-j`$ for whole numbers $`m`$ and $`j`$, and it is positive. Since $`2.8^2=7.84<8`$, we have $`3-2\sqrt2<\tfrac15`$, and $`\sqrt2-1<\tfrac12`$, so $`(\sqrt2-1)^{2i+1}<\tfrac12\times\tfrac1{5^i}`$, which is below $`\tfrac1q`$ once $`5^i>q`$. By the test, $`\sqrt2`$ is irrational.

*Exercise [6](#ex%3A6).* (a) With $`P_0=1`$, $`a_j=P_{j-1}+1`$ and $`P_j=P_{j-1}a_j`$, so $`\tfrac1{P_{j-1}}-\tfrac1{P_j}=\tfrac{a_j-1}{P_j}=\tfrac1{a_j}`$, and adding these for $`1,\dots,j`$ leaves $`1-\tfrac1{P_j}`$. (b) The first $`j`$ exponents divide $`P_j`$. The exponent $`P_j+1`$ is bigger than $`k=P_j`$, so it leaves $`\tfrac{2^{P_j}-1}{2^{P_j+1}-1}`$, which is at least $`\tfrac37`$ because $`7(2^{P_j}-1)-3(2^{P_j+1}-1)=2^{P_j}-4\ge0`$. So cancelling longer and longer early batches still leaves $`R(P_j)\ge\tfrac37`$, which is why the proof averages.

<div class="thebibliography">

9 P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. 12 (1948), 63–66. P. Erdős, [*On the irrationality of certain series*](https://users.renyi.hu/~p_erdos/1969-09.pdf), Math. Student 36 (1968), 222–226 (issued 1969). T. F. Bloom, *Erdős Problem \#257*, <https://www.erdosproblems.com/257>; the statement is quoted in the Formal Conjectures file `FormalConjectures/ErdosProblems/257.lean`. T. Tao and J. Teräväinen, [*Quantitative correlations and some problems on prime factors of consecutive integers*](https://arxiv.org/abs/2512.01739v2), arXiv:2512.01739v2 (submitted December 2025, revised April 2026). W. Cook, [*Irrationality criteria for Lambert subseries*](https://github.com/wcook04/plectis-erdos/blob/0064fc9b2a2693de97aebc8abec26090c3cd1095/paper/257/erdos-257-mersenne-support-subseries.pdf), 30 September 2026. W. Cook, [*Reciprocal Mersenne subseries: support criteria, finite arithmetic and conditional orbit problems*](https://github.com/wcook04/plectis-erdos/blob/0064fc9b2a2693de97aebc8abec26090c3cd1095/paper/257/erdos257-mersenne-reasoning-surface.pdf), 30 September 2026.

</div>
