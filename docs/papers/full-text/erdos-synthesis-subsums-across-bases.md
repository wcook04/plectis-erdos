<a id="erdos-synthesis-subsums-across-bases"></a>

# Rational and Irrational Subsums of a Lambert Series Across Bases

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Let $`a>b\ge1`$ be coprime integers with $`a^2>b^3`$. We prove that $`\sum_{n\in S}((a/b)^n-1)^{-1}`$ is irrational for every infinite set $`S`$ of positive integers that is totally ordered by divisibility, and transcendental at every rational base when $`S`$ eventually doubles. For every rational base strictly between $`1`$ and $`2`$ the same sums take rational values on infinite sets $`S`$; at base $`3/2`$ the value $`1/2`$ occurs. Both facts come from one comparison, the number of admissible choices at each level against the contraction between levels. Subsum sets are null when the choices fall short by an unbounded factor and contain intervals when every step is at most the reach of the later steps, and base $`2`$ lies exactly on the boundary. On the interval side no property shared by all the competing series can decide irrationality; the rational series constructed in the companion notes on Erdős Problems \#249 and \#251 are instances. At base $`2`$ the subsums form a Cantor set of measure one. We prove that the proportion of rationals of bounded height that survive a fixed number of greedy steps is forced by the equidistribution of Farey fractions, so it carries no information about membership, and we state the membership question that remains.

<a id="sec:results"></a>

# Results

Seven of the eight problems treated in the companion notes ask whether a series is irrational: $`\sum(n!-1)^{-1}`$ in \#68, reciprocal sums of near-Sylvester sequences in \#243, $`\sum\varphi(n)2^{-n}`$ in \#249, $`\sum p_n2^{-n}`$ in \#251, the subseries $`\sum_{n\in S}(2^n-1)^{-1}`$ in \#257, a running least common multiple in \#269, and $`\sum(t^n-1)^{-1}`$ at rational $`t`$ in \#1049 \[erdosgraham1980; erdos1988\]. The eighth, \#1041, is geometric and plays no part here. This note reads the seven together. Its theorems concern the two that share a series. For real $`t>1`$ and a set $`S`$ of positive integers put
``` math
X_S(t)=\sum_{n\in S}\frac{1}{t^n-1},\qquad
 w_n=\frac{1}{t^n-1},\qquad R_N=\sum_{n>N}w_n .
```
Problem \#257 asks whether $`X_S(t)`$ is irrational for every infinite $`S`$ at every integer $`t\ge2`$ \[erdosgraham1980, p. 62\]; Problem \#1049 asks about $`X_{\mathbb{N}_{>0}}(t)`$ at rational $`t`$.

The comparison behind everything is stated for weights with multiplicities. Let $`u_n>0`$ and integers $`D_n\ge1`$ satisfy $`\sum_nD_nu_n<\infty`$, and put
``` math
V=\Bigl\{\sum_{n\ge1}\varepsilon_nu_n:\ \varepsilon_n\in\{0,1,\dots,D_n\}\Bigr\},
 \qquad C_N=\sum_{n>N}D_nu_n .
```

<div id="thm:dichotomy" class="theorem">

**Theorem 1** (choices against contraction). *<span class="upright">(i)</span> For every $`N`$, the Lebesgue measure of $`V`$ is at most $`C_N\prod_{n\le N}(D_n+1)`$. If $`\liminf_NC_N\prod_{n\le N}(D_n+1)=0`$ then $`V`$ is null.*

*<span class="upright">(ii)</span> If $`u_n\le C_n`$ for every $`n>N_0`$, then for each choice of $`\varepsilon_1,\dots,\varepsilon_{N_0}`$ the set $`V`$ contains the interval $`[\mu,\mu+C_{N_0}]`$, where $`\mu=\sum_{n\le N_0}\varepsilon_nu_n`$.*

*<span class="upright">(iii)</span> For $`u_n=\beta^{-n}`$ with real $`\beta>1`$ and $`D_n=D`$, the bound in <span class="upright">(i)</span> tends to $`0`$ exactly when $`D+1<\beta`$, and the hypothesis of <span class="upright">(ii)</span> holds exactly when $`D+1\ge\beta`$.*

</div>

Part (ii) is Kakeya’s covering argument and part (i) is the standard covering bound; both are classical \[hornich1941; nitecki2013; fridy1966\], and Kovač and Tao use the higher-dimensional form of (ii) to construct rational Ahmes series \[kovactao2024, Lemma 5.1\]. We claim no novelty for Theorem <a href="#thm:dichotomy" data-reference-type="ref" data-reference="thm:dichotomy">1</a>. Its use here is to say which side each problem lies on.

<div id="thm:bases" class="theorem">

**Theorem 2** (the subseries across bases). *Let $`t>1`$ be real.*

*<span class="upright">(a)</span> If $`t<2`$, let $`N_0\ge0`$ be least with $`t^{-n}\le2-t`$ for all $`n>N_0`$. Then the set of values $`X_S(t)`$ is the union of the intervals $`[X_F(t),X_F(t)+R_{N_0}]`$ over $`F\subseteq\{1,\dots,N_0\}`$, where $`X_F(t)=\sum_{n\in F}w_n`$; in particular it contains $`[0,R_{N_0}]`$. If moreover $`t=a/b`$ in lowest terms, then every rational in $`[0,R_{N_0}]`$ whose reduced denominator shares a prime factor with $`ab`$ equals $`X_S(t)`$ for some $`S`$, and every such $`S`$ is infinite. There is an infinite $`S\subseteq\{2,3,\dots\}`$ with $`X_S(3/2)=1/2`$.*

*<span class="upright">(b)</span> If $`t=2`$, every value has exactly one $`S`$, and the set of values is a Cantor set of Lebesgue measure $`1`$ inside $`[0,E]`$, where $`E=\sum_{n\ge1}(2^n-1)^{-1}=1.6066951524\ldots`$.*

*<span class="upright">(c)</span> If $`t>2`$, the set of values is null.*

</div>

Part (b) is proved in the companion note on \#257, Section 7, from Hornich’s theorem as proved by Nitecki \[plectis257; hornich1941; nitecki2013\]; Kovač and Tao record the strict inequality $`w_N>R_N`$ and the Cantor-set conclusion for every fixed base $`t\ge2`$ \[kovactao2024, Remark 4.1\]. Parts (a) and (c) follow from Theorem <a href="#thm:dichotomy" data-reference-type="ref" data-reference="thm:dichotomy">1</a> in a few lines. We have not found part (a) stated for non-integer bases and it may be known. It shows that the statement asked in \#257 is false at every rational base below $`2`$, so any proof at base $`2`$ must use more than the shape of the series.

<div id="thm:chains" class="theorem">

**Theorem 3** (divisibility chains). *Let $`t=a/b>1`$ in lowest terms and let $`S=\{n_1<n_2<\cdots\}`$ be infinite with $`n_j\mid n_{j+1}`$ for every $`j`$.*

*<span class="upright">(a)</span> If $`a^2>b^3`$, then $`X_S(t)`$ is irrational.*

*<span class="upright">(b)</span> If $`n_{j+1}=2n_j`$ for all large $`j`$, then $`X_S(t)`$ is transcendental, with no condition on $`a`$ and $`b`$.*

</div>

The hypothesis $`a^2>b^3`$ says $`\log b/\log a<2/3`$. It holds for every integer base, for $`3/2`$, $`5/2`$ and $`7/3`$, and fails for $`4/3`$ and $`5/4`$. At integer bases part (a) is contained in the theorem of Erdős on supports with $`\sum_{n\in S}1/n<\infty`$ \[erdos1968\], proved in full in \[plectis257, Theorem 2\]. At base $`3/2`$ it sits inside the regime of Theorem <a href="#thm:bases" data-reference-type="ref" data-reference="thm:bases">2</a>(a): rational values occur there, and exact divisibility still forces irrationality. For comparison, the companion note on \#1049 proves the irrationality of the full sum $`X_{\mathbb{N}_{>0}}(a/b)`$ when $`\log b/\log a<0.4056\ldots`$, using Zudilin’s linear forms \[plectis1049, Theorem 1\], \[zudilin2004\], and proves that no family of forms of that shape reaches $`1/2`$ \[plectis1049, Theorem 5\]. Thin supports reach further than the full sum because the denominators divide one another.

At base $`2`$ the greedy rule decides membership: starting from $`r_0=x`$, take index $`n`$ when $`r_{n-1}\ge w_n`$ and subtract. Since $`w_n>R_n`$, a real $`x\in[0,E]`$ is a subsum if and only if no remainder falls strictly between $`R_n`$ and $`w_n`$; we say $`x`$ is *rejected at step $`n`$* when that happens first at index $`n`$.

<div id="thm:forced" class="theorem">

**Theorem 4** (a forced statistic). *Fix $`N\ge1`$. Among the reduced fractions $`p/q\in(0,E]`$ with $`q\le Q`$, the proportion not rejected in the first $`N`$ steps tends to $`2^NR_N/E`$ as $`Q\to\infty`$, with error $`O(2^N\log Q/Q)`$. Consequently the upper limit of the proportion that are subsums is at most $`1/E=0.62239\ldots`$.*

</div>

The limit $`2^NR_N/E`$ does not depend on whether \#257 is true. A count of fractions that survive a fixed depth therefore says nothing about membership. An exact computation in \[plectisinvestigation\] first read a surviving share near $`62\%`$ as evidence that most such fractions are subsums; Theorem <a href="#thm:forced" data-reference-type="ref" data-reference="thm:forced">4</a> is the correction. Section <a href="#sec:base2" data-reference-type="ref" data-reference="sec:base2">4</a> states what remains.

<a id="evidence."></a>

#### Evidence.

Every proof in this note is an ordinary proof. Nothing here is checked in Lean, and nothing has been reviewed by a specialist. Statements quoted from the companion notes carry the status given there, which we repeat at each use. Theorem <a href="#thm:chains" data-reference-type="ref" data-reference="thm:chains">3</a> uses Mahler’s theorem as an external premise in the eventually doubling case, hence in both parts.

<a id="sec:dichotomy"></a>

# Choices against contraction

<div class="proof">

*Proof of Theorem <a href="#thm:dichotomy" data-reference-type="ref" data-reference="thm:dichotomy">1</a>.* (i) A choice of $`\varepsilon_1,\dots,\varepsilon_N`$ fixes $`\sum_{n\le N}\varepsilon_nu_n`$, and the rest of the sum lies in $`[0,C_N]`$. So $`V`$ is covered by at most $`\prod_{n\le N}(D_n+1)`$ intervals of length $`C_N`$.

\(ii\) Subtracting $`\mu`$, it suffices to reach every $`y\in[0,C_{N_0}]`$ with the levels $`n>N_0`$. Put $`y_{N_0}=y`$ and, for $`n>N_0`$, let $`\varepsilon_n=\min(D_n,\lfloor y_{n-1}/u_n\rfloor)`$ and $`y_n=y_{n-1}-\varepsilon_nu_n`$. If $`0\le y_{n-1}\le C_{n-1}=D_nu_n+C_n`$ then $`0\le y_n\le C_n`$: when $`\varepsilon_n=D_n`$ this is a subtraction, and when $`\varepsilon_n<D_n`$ it holds because $`y_n<u_n\le C_n`$. Since $`C_n\to0`$, the sum of the $`\varepsilon_nu_n`$ is $`y`$.

\(iii\) Here $`C_n=D\beta^{-n}/(\beta-1)`$. The product in (i) is a constant multiple of $`((D+1)/\beta)^N`$, and $`u_n\le C_n`$ says $`\beta-1\le D`$. ◻

</div>

The reading that matters for irrationality is immediate. Suppose a family of series has values $`x_0+\sum\varepsilon_nu_n`$ with the $`\varepsilon_n`$ free as in (ii). The values then fill an interval, which contains rationals and irrationals, so a property that all members of the family share implies neither. A proof of irrationality for one member has to use something that distinguishes it inside the family. Two constructions in the companion notes are families of this kind.

*Problem \#251.* Proposition 1 of \[plectis251\] (ordinary proof), applied in its Corollary 2 to the prime gaps, changes the gaps on a set of upper Banach density zero, by nonnegative integers below any prescribed function tending to infinity, keeping every congruence modulo every fixed $`q`$ from some point on, and reaches every real in an interval. The resulting positions $`P_n`$ satisfy $`P_n\sim n\log n`$ and are not asserted to be prime. In the notation above the $`j`$-th block has $`u_j=M_j2^{-n_j-2}`$ and $`D_j=2^{s_j}-1`$, and the inequality verified there is $`u_j\le C_j`$. The lemma is credited there to \[fridy1966\], \[crmarickovac2025, Lemma 4\] and \[kovactao2024, Lemma 5.1\]. The note also proves that a bounded allowance is impossible, so an unbounded one is exactly what is needed. Hence growth, densities of patterns and residues of $`p_n`$ cannot prove $`\sum p_n2^{-n}`$ irrational.

*Problem \#249.* Section 5 of \[plectis249\] gives an integer sequence $`c`$ with $`c(n)=\varphi(n)`$ for odd $`n`$, $`|c(n)-\varphi(n)|\le2`$ for even $`n`$, $`0\le c(n)\le n`$ and $`\sum c(n)2^{-n}=5/4`$ (Lean-checked there). Changing even indices by at most $`2`$ is the case $`u_n=2^{-n}`$ for even $`n`$, $`D_n=4`$, where $`C_n\ge\tfrac43 2^{-n}>u_n`$.

The same comparison appears in Kovač and Tao’s theorem that for integers $`2\le t_1<\dots<t_m`$ with $`\sum1/(t_k-1)>1`$ there are sets $`S_k`$, one of them infinite, with $`\sum_kX_{S_k}(t_k)`$ rational \[kovactao2024, Theorem 2.3\]: merging the weights of the $`m`$ bases, the sum of all weights below a given weight $`u`$ is at least $`(1-O(u))\,u\sum1/(t_k-1)`$, which exceeds $`u`$ once $`u`$ is small.

<a id="sec:bases"></a>

# The subseries across bases

<div class="proof">

*Proof of Theorem <a href="#thm:bases" data-reference-type="ref" data-reference="thm:bases">2</a>.* (a) Since $`R_n\ge\sum_{k>n}t^{-k}=t^{-n}/(t-1)`$ and $`w_n=t^{-n}/(1-t^{-n})`$, the inequality $`w_n\le R_n`$ holds as soon as $`t^{-n}\le2-t`$. Theorem <a href="#thm:dichotomy" data-reference-type="ref" data-reference="thm:dichotomy">1</a>(ii) with $`D_n=1`$ gives, for each $`F\subseteq\{1,\dots,N_0\}`$, the interval $`[X_F(t),X_F(t)+R_{N_0}]`$, and every value $`X_S(t)`$ lies in the one with $`F=S\cap[1,N_0]`$. For $`t=a/b`$ a finite subsum is $`\sum_{n\in F}b^n/(a^n-b^n)`$, whose denominator divides $`\prod(a^n-b^n)`$ and is coprime to $`ab`$. A rational whose denominator is not coprime to $`ab`$ is therefore never a finite subsum, and inside the interval it is a subsum. At $`t=3/2`$ the inequality $`t^{-n}\le1/2`$ holds for $`n\ge2`$ and $`R_1>1/2`$.

\(c\) For $`t>2`$, $`2^NR_N\le2^Nt^{-N}/((t-1)(1-t^{-1}))\to0`$, and Theorem <a href="#thm:dichotomy" data-reference-type="ref" data-reference="thm:dichotomy">1</a>(i) applies. ◻

</div>

<div class="proof">

*Proof of Theorem <a href="#thm:chains" data-reference-type="ref" data-reference="thm:chains">3</a>.* Write $`\rho=b/a`$, $`D_j=a^{n_j}-b^{n_j}`$ and $`S_j=\sum_{i\le j}b^{n_i}/(a^{n_i}-b^{n_i})`$. Because $`n_i\mid n_j`$ for $`i\le j`$, each $`a^{n_i}-b^{n_i}`$ divides $`D_j`$, so $`D_jS_j`$ is an integer. The tail satisfies
``` math
0<X_S(t)-S_j\le\sum_{n\ge n_{j+1}}\frac{\rho^n}{1-\rho^n}
 \le\frac{\rho^{\,n_{j+1}}}{(1-\rho)^2}.
```
Each ratio $`n_{j+1}/n_j`$ is an integer at least $`2`$.

Suppose the ratio is at least $`3`$ for infinitely many $`j`$. For those $`j`$,
``` math
0<D_j\bigl(X_S(t)-S_j\bigr)\le\frac{a^{n_j}\rho^{3n_j}}{(1-\rho)^2}
 =\frac{1}{(1-\rho)^2}\Bigl(\frac{b^3}{a^2}\Bigr)^{n_j}\longrightarrow0
```
when $`a^2>b^3`$. If $`X_S(t)=p/q`$, then $`qD_j(X_S(t)-S_j)`$ is a positive integer for every $`j`$, a contradiction.

Otherwise the ratio is $`2`$ from some index on, which is the case of part (b), and $`S`$ is a finite set together with $`\{d,2d,4d,\dots\}`$. With $`z=t^{-d}`$ the infinite part contributes $`g(z)`$, where
``` math
g(z)=\sum_{k\ge0}\frac{z^{2^k}}{1-z^{2^k}},\qquad
 g(z^2)=g(z)-\frac{z}{1-z}.
```
Mahler’s theorem \[mahler1929\], in the form given in \[nishioka1996\], states: if $`f\in\mathbb{Q}[[z]]`$ converges in the unit disc, is transcendental over $`\mathbb{C}(z)`$, and satisfies $`f(z^d)=A(z,f(z))/B(z,f(z))`$ with $`A,B`$ coprime polynomials of degree less than $`d`$ in the second variable, then $`f(\alpha)`$ is transcendental for every algebraic $`\alpha`$ with $`0<|\alpha|<1`$ such that the resultant of $`A`$ and $`B`$ in the second variable does not vanish at any $`\alpha^{d^k}`$. For $`g`$ we have $`d=2`$, $`A=(1-z)f-z`$ and $`B=1-z`$. They are coprime, their resultant is a power of $`1-z`$, and $`1-z`$ is nonzero at every $`\rho^{\,d2^k}`$. The function $`g`$ is transcendental: at a root of unity $`\zeta`$ of order $`2^j`$ the terms with $`k\ge j`$ are positive on the ray $`r\zeta`$ and diverge as $`r\to1`$, while the earlier terms stay bounded, so $`g`$ has infinitely many singularities on the unit circle. An algebraic function over $`\mathbb{C}(z)`$ has only finitely many singular points, so $`g`$ is transcendental over $`\mathbb{C}(z)`$. Hence $`g(\rho^{\,d})`$ is transcendental, and adding the rational finite part proves (b) and completes (a). ◻

</div>

We do not know whether $`a^2>b^3`$ is necessary in (a). The first open case is base $`4/3`$ with a chain whose ratios are $`2`$ except for infinitely many $`3`$s.

<a id="sec:base2"></a>

# Base two

<div class="proof">

*Proof of Theorem <a href="#thm:forced" data-reference-type="ref" data-reference="thm:forced">4</a>.* Fixing the first $`N`$ digits gives $`2^N`$ closed intervals of length $`R_N`$. They are pairwise disjoint because $`w_n>R_n`$, and a real in $`[0,E]`$ is not rejected in the first $`N`$ steps exactly when it lies in their union $`K_N`$, which has measure $`2^NR_N`$. For an interval $`I`$ of length $`\ell`$, the number of integers $`p`$ coprime to $`q`$ with $`p/q\in I`$ is $`\varphi(q)\ell+O(2^{\omega(q)})`$ by inclusion and exclusion. Summing over $`q\le Q`$ with $`\sum_{q\le Q}\varphi(q)=3Q^2/\pi^2+O(Q\log Q)`$ and $`\sum_{q\le Q}2^{\omega(q)}=O(Q\log Q)`$ gives $`3Q^2\ell/\pi^2+O(Q\log Q)`$. Apply this to the $`2^N`$ intervals of $`K_N`$ and to $`(0,E]`$ and divide. The second statement follows because every subsum lies in every $`K_N`$ and $`2^NR_N\to1`$. ◻

</div>

The intervals removed at step $`n`$ are explicit. Put $`g_n=w_n-R_n`$, so that $`g_n=\tfrac23 4^{-n}+O(8^{-n})`$. For a finite nonempty $`F`$ with largest element $`n`$, the interval $`(X_F(2)-g_n,\,X_F(2))`$ is removed at step $`n`$, and
``` math
[0,E]\setminus\mathcal A=\bigsqcup_{F\ne\varnothing}\bigl(X_F(2)-g_{\max F},\,X_F(2)\bigr),
 \qquad\sum_{n\ge1}2^{n-1}g_n=E-1,
```
where $`\mathcal A`$ is the set of subsums. By Theorem <a href="#thm:bases" data-reference-type="ref" data-reference="thm:bases">2</a>(b) a rational with an infinite $`S`$ is exactly a counterexample to \#257 at base $`2`$. So \#257 at base $`2`$ holds if and only if every rational in $`[0,E]`$ that is not a finite subsum lies strictly between $`X_F(2)-g_{\max F}`$ and $`X_F(2)`$ for some finite nonempty $`F`$. This is a one-sided question of approximation by the countable set of finite subsums, with an error that shrinks like $`4^{-\max F}`$.

Under \#257 the only fractions of height at most $`Q`$ that are subsums are the finite subsums, $`40`$ of the $`19{,}653`$ fractions with $`2\le q\le200`$. A model that treats later remainders as equidistributed gives the opposite extreme, a proportion tending to $`1/E`$, because the shares $`2^{n-1}g_n/E`$ of the removed intervals are summable. That model asserts that \#257 fails for a positive proportion of all rationals. It is a strong claim, and no count can support it: by Theorem <a href="#thm:forced" data-reference-type="ref" data-reference="thm:forced">4</a> every count at a fixed depth is forced. Measure does not decide either. Boes, Darst and Erdős construct symmetric Cantor sets of every measure in $`[0,1)`$ that contain essentially no rationals \[boesdarsterdos1981\].

The exact computation in \[plectisinvestigation\] agrees with Theorem <a href="#thm:forced" data-reference-type="ref" data-reference="thm:forced">4</a> step by step. Among the $`19{,}653`$ reduced fractions with $`2\le q\le200`$, the numbers rejected at steps $`1`$, $`2`$ and $`7`$ are $`4809`$, $`1470`$ and $`32`$, against $`4811`$, $`1467`$ and $`32`$ from the measures of the removed intervals. The expected number rejected at step $`n`$ is $`2^{n-1}g_n\sum_{2\le q\le Q}\varphi(q)`$, asymptotically $`(3Q^2/\pi^2)2^{n-1}g_n`$, which falls below $`1`$ once $`n>2\log_2Q-3.3`$. Past that depth a finite computation at height $`Q`$ cannot separate membership from late rejection, so running deeper adds nothing. No rational is known to have an infinite $`S`$ at base $`2`$, and beyond the forced share $`1-1/E`$ no argument is known that rejects a positive proportion of rationals.

<div id="prob:membership" class="problem">

**Problem 5**. Decide whether $`1/2`$ is a subsum of $`\sum(2^n-1)^{-1}`$. By \[plectis257, Theorem 7\] this holds if and only if the integer remainders of the greedy rule fail to increase at infinitely many steps.

</div>

The literature on rational points of Cantor sets concerns null sets such as the middle-third set, where the expected count of rationals of height at most $`Q`$ is a power of $`Q`$ \[rstw2019; chowvarjuyu2024\]. The literature on subsum sets \[nitecki2013\] does not discuss rational points. We found nothing on rational points of a subsum set of positive measure, and Problem <a href="#prob:membership" data-reference-type="ref" data-reference="prob:membership">5</a> is the simplest question of that kind.

<a id="sec:second"></a>

# Limits on methods

The companion notes prove a second kind of negative result. Each bounds what one method can do, and none follows from Theorem <a href="#thm:dichotomy" data-reference-type="ref" data-reference="thm:dichotomy">1</a>, which concerns sets of values.

- \#1049, Theorem 5 \[plectis1049\] (ordinary proof there, with the contradiction step and the comparison with $`1/2`$ checked in Lean). A family of linear forms with degrees at most $`\delta n^2`$ and decay $`-\sigma n^2\log x`$ at every $`x>1`$ has $`\sigma\le\delta`$, so its sufficient region $`\log b/\log a<\sigma/(\sigma+\delta)`$ never reaches $`1/2`$.

- \#269, Theorem 1 \[plectis269\] (Lean-checked there; Fan posted the two-prime separation \[fan2026comment\], and the three-prime statement is proved in the note). For three primes the reciprocal running-LCM kernel has nonsingular minors of every order, so no finite sum of products separates one exponent from the other two.

- \#257, Section 3 \[plectis257\] (ordinary proof). Every positive divisor cover costs at least $`e`$ times the mean of $`\log^+`$ of its multiplicity, and the averaging method cannot reach the prime support, where irrationality is known at base $`2`$ by other means \[taoteravainen2025\].

- \#249, Theorem 9 \[plectis249\] (Lean-checked there). Every admissible rank-one quotient stays at distance more than $`21/320`$ from its target.

- \#68, Section 6 \[plectis68\] (ordinary proof). The integer-gap comparison cannot hold at cutoffs within a bounded distance of the degree.

- \#243, Proposition 17 \[plectis243\] (Lean-checked there). A counterexample must have relative errors tending to $`0`$ with unbounded negative parts, so size conditions on the error do not decide.

Two of these are inequalities between a cost and a gain: $`\sigma\le\delta`$ in \#1049 and the cover cost in \#257. Whether one inequality governs both is open, and we know of no formulation that covers the other four.

<div class="thebibliography">

99 P. Erdős and R. L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf), Monogr. Enseign. Math. 28, Geneva, 1980.

P. Erdős, *On the irrationality of certain series: problems and results*, in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009).

P. Erdős, [*On the irrationality of certain series*](https://users.renyi.hu/~p_erdos/1969-09.pdf), Math. Student 36 (1968), 222–226 (issued 1969).

H. Hornich, *Über beliebige Teilsummen absolut konvergenter Reihen*, Monatshefte für Mathematik und Physik **49** (1941), 316–320. [doi:10.1007/BF01707309](https://doi.org/10.1007/BF01707309).

Z. Nitecki, [*Subsum sets: intervals, Cantor sets, and Cantorvals*](https://arxiv.org/abs/1106.3779v2), arXiv:1106.3779v2 (2013).

John A. Fridy, [*Generalized bases for the real numbers*](https://www.fq.math.ca/Scanned/4-3/fridy.pdf). The Fibonacci Quarterly **4** (1966), no. 3, 193–201.

T. Crmarić and V. Kovač, [*On the irrationality of certain super-polynomially decaying series*](https://arxiv.org/abs/2504.18712v1), Colloq. Math. **179** (2025), 55–68, doi:[10.4064/cm9628-5-2025](https://doi.org/10.4064/cm9628-5-2025). Theorem locators follow arXiv:2504.18712v1.

Vjekoslav Kovač and Terence Tao, [*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593v4). Acta Mathematica Hungarica **175** (2025), 572–608, doi:[10.1007/s10474-025-01528-0](https://doi.org/10.1007/s10474-025-01528-0); arXiv:[2406.17593v4](https://arxiv.org/abs/2406.17593v4). Statement and section numbers refer to arXiv version 4.

W. Zudilin, [*Heine’s basic transform and a permutation group for $`q`$-harmonic series*](https://geodesic.mathdoc.fr/articles/10.4064/aa111-2-4/), Acta Arith. **111** (2004), no. 2, 153–164, doi:[10.4064/aa111-2-4](https://doi.org/10.4064/aa111-2-4).

T. Tao and J. Teräväinen, [*Quantitative correlations and some problems on prime factors of consecutive integers*](https://arxiv.org/abs/2512.01739v2), arXiv:2512.01739v2 (submitted December 2025, revised April 2026).

Steve Fan, *Comment on Erdős Problem \#269, thread 269, post 7218* (2026), [source](https://www.erdosproblems.com/forum/thread/269#post-7218). 26 June 2026.

K. Mahler, *Arithmetische Eigenschaften der Lösungen einer Klasse von Funktionalgleichungen*, Math. Ann. **101** (1929), 342–367.

Ku. Nishioka, *Mahler Functions and Transcendence*, Lecture Notes in Math. 1631, Springer, Berlin, 1996.

D. Boes, R. Darst and P. Erdős, [*Fat, symmetric, irrational Cantor sets*](https://www.tandfonline.com/doi/abs/10.1080/00029890.1981.11995266), Amer. Math. Monthly **88** (1981), 340–341.

A. Rahm, N. Solomon, T. Trauthwein and B. Weiss, [*The distribution of rational numbers on Cantor’s middle thirds set*](https://arxiv.org/abs/1909.01198), arXiv:1909.01198.

S. Chow, P. Varjú and H. Yu, [*Counting rationals and diophantine approximation in missing-digit Cantor sets*](https://arxiv.org/abs/2402.18395), arXiv:2402.18395.

W. Cook, [*Two incomparable denominator exclusions for $`\sum_{n\ge2}(n!-1)^{-1}`$*](../../../paper/68/erdos-68-factorial-denominator-irrationality.pdf), Erdős Problem Notes, 2026.

W. Cook, [*Bounded increments and rational reciprocal sums*](../../../paper/243/erdos-243-reciprocal-tail-rigidity.pdf), Erdős Problem Notes, 2026.

W. Cook, [*Bases and integral relations for the $`k`$-kernel of Euler’s totient*](../../../paper/249/erdos-249-binary-totient-series.pdf), Erdős Problem Notes, 2026.

W. Cook, [*Sparse congruence-preserving perturbations of dyadic series*](../../../paper/251/erdos-251-prime-gap-dyadic-series.pdf), Erdős Problem Notes, 2026.

W. Cook, [*Weighted support criteria for reciprocal Mersenne subseries*](../../../paper/257/erdos-257-mersenne-support-subseries.pdf), Erdős Problem Notes, 2026.

W. Cook, [*No finite separable representation at three prime generators*](../../../paper/269/erdos-269-three-prime-running-lcm.pdf), Erdős Problem Notes, 2026.

W. Cook, [*Zudilin’s forms at rational bases and the exact normalised Hankel order*](../../../paper/1049/erdos-1049-rational-base-lambert.pdf), Erdős Problem Notes, 2026.

W. Cook, *Choices, contraction and rational membership*, exact computation with saved outputs in `research/experiments/choices_contraction/` of the repository, 2026.

W. Cook, [*Reading eight Erdős problems together: a working record*](../../../paper/synthesis/erdos-synthesis-reading-together-record.pdf), 2026.

</div>

<a id="declaration-of-generative-ai-use"></a>

# Declaration of generative AI use

The mathematics and text of this note were produced with large language model agents under the direction of the author, who is responsible for every claim. Each statement above names its evidence: an ordinary proof printed here, a result quoted from a companion note with the status given there, an exact computation with saved outputs, or a cited external theorem. The record \[plectisrecord\] lists what was checked, by which means, and what was found to be already known.
