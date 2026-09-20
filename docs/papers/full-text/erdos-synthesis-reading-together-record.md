<a id="erdos-synthesis-reading-together-record"></a>

# Reading Eight Erdős Problems Together

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

This record supports the note \[plectisshort\]. It proves the two lemmas about base $`2`$ that the note uses without proof, lists the negative results of the seven companion notes with their locations and status, gives in full the two wrong readings of one computation and the theorem that replaced them, records the ideas that were eliminated together with the statement that eliminated each, records what turned out to be known already, and ends with the questions we think are worth someone’s time. It is a lookup document. Each fact has one home here.

<a id="sec:map"></a>

# What the note relies on

<div class="center">

| In the note | Here |
|:---|:---|
| Theorem 1.1 (choices against contraction) | Proved in the note. Attribution in Section <a href="#sec:known" data-reference-type="ref" data-reference="sec:known">6</a>. |
| Theorem 1.2(b), base $`2`$ | Quoted from \[plectis257, Section 7\]. Removed intervals: Lemma <a href="#lem:gaps" data-reference-type="ref" data-reference="lem:gaps">1</a>. |
| Theorem 1.3 (chains) | Proved in the note. A wrong citation caught on the way: Section <a href="#sec:eliminated" data-reference-type="ref" data-reference="sec:eliminated">5</a>, item 4. |
| Theorem 1.4 (forced statistic) | Proved in the note. The readings it corrects: Section <a href="#sec:misread" data-reference-type="ref" data-reference="sec:misread">4</a>. |
| Limits on methods | Section <a href="#sec:inventory" data-reference-type="ref" data-reference="sec:inventory">3</a>, with status and sources. |

</div>

Every proof here is an ordinary proof. Nothing is checked in Lean. The computations are exact rational arithmetic with saved outputs \[plectisinvestigation\].

<a id="sec:lemmas"></a>

# Two lemmas at base two

Notation is that of the note at $`t=2`$: $`w_n=(2^n-1)^{-1}`$, $`R_N=\sum_{n>N}w_n`$, $`g_n=w_n-R_n>0`$, $`X_F=\sum_{n\in F}w_n`$ for finite $`F`$, and $`\mathcal A`$ is the set of all subsums.

<div id="lem:gaps" class="lemma">

**Lemma 1** (the removed intervals). *$`[0,E]\setminus\mathcal A`$ is the disjoint union, over finite nonempty $`F`$, of the open intervals $`(X_F-g_{\max F},\,X_F)`$. Their total length is $`\sum_n2^{n-1}g_n=E-1`$, and $`g_n=\sum_{j\ge2}\frac{2^j-2}{2^j-1}2^{-jn}=\tfrac23 4^{-n}+\tfrac67 8^{-n}+\cdots`$.*

</div>

<div class="proof">

*Proof.* Fix the digits $`\varepsilon_1,\dots,\varepsilon_{n-1}`$ and let $`s=\sum_{i<n}\varepsilon_iw_i`$. The values with these digits lie in $`[s,s+R_{n-1}]`$, and they split into $`[s,s+R_n]`$ and $`[s+w_n,s+w_n+R_n]`$. The interval between them is $`(s+R_n,s+w_n)`$. Its right end is $`X_F`$ with $`F=\{i<n:\varepsilon_i=1\}\cup\{n\}`$ and its length is $`g_n`$. Every finite nonempty $`F`$ arises once. The total length is $`E`$ minus the measure of $`\mathcal A`$, which is $`1`$ \[plectis257, Section 7\]. The series for $`g_n`$ follows from $`w_n=\sum_{j\ge1}2^{-jn}`$ and $`R_n=\sum_{j\ge1}2^{-jn}/(2^j-1)`$. ◻

</div>

<div id="lem:translate" class="lemma">

**Lemma 2** (translation by a finite subsum). *Let $`F`$ be finite with largest element $`n`$ and let $`0\le x\le R_n`$. The greedy rule applied to $`X_F+x`$ selects exactly $`F`$ among the indices up to $`n`$ and then agrees with the greedy rule applied to $`x`$. In particular $`X_F+x\in\mathcal A`$ if and only if $`x\in\mathcal A`$, and $`X_F+x`$ is rejected at a step $`m>n`$ exactly when $`x`$ is.*

</div>

<div class="proof">

*Proof.* At an index $`i\le n`$ the remainder is $`X_{F\cap[i,n]}+x`$. If $`i\in F`$ it is at least $`w_i`$ and the index is taken. If $`i\notin F`$ it is at most $`R_i-R_n+x\le R_i<w_i`$, so the index is skipped and nothing is rejected. After index $`n`$ the remainder is $`x`$. ◻

</div>

Two consequences. The map $`x\mapsto x+1`$ preserves reduced denominators, so at every step $`n\ge2`$ the number of fractions of height at most $`Q`$ rejected at that step is even; every saved table has this property. The condition is $`x\le R_{\max F}`$. It is not enough that $`X_F+x\le E`$: $`x=1/2`$ is not rejected through step $`160`$, while $`1/2+1/3=5/6`$ lies in $`(R_1,1)`$ and is rejected at step $`1`$. Counts of rejections should therefore be taken modulo these translations. At height $`200`$ the four fractions rejected at step $`12`$ are $`46/183`$ and its translates by $`1/3`$, $`1`$ and $`4/3`$, one event.

A finite subsum has odd denominator, since $`\prod_{n\in F}(2^n-1)`$ is odd. So a rational with even denominator is never a finite subsum, and if it is a subsum at all its set $`S`$ is infinite.

<a id="sec:inventory"></a>

# Negative results in the companion notes

Status is as stated in each note: L for checked in Lean there, O for an ordinary proof there, C for cited there.

| Note | Location | Statement |  |
|:---|:---|:---|:---|
| \#68 \[plectis68\] | Section 6 | The integer-gap comparison cannot hold at cutoffs within a bounded distance of the degree. Small tails alone do not give the strict comparison. | O |
| \#243 \[plectis243\] | Proposition 17 | A counterexample has errors that are eventually nonzero, relatively small, with unbounded negative parts. Size of the error does not decide; the denominators must be used. | L |
| \#249 \[plectis249\] | Section 5 | A rational series with the totient’s values at odd indices, within $`2`$ at even indices, and sum $`5/4`$. Positive tail differences need not be nonintegral. | L |
| \#249 \[plectis249\] | Theorem 9 | Every admissible rank-one quotient stays more than $`21/320`$ from its target. | L |
| \#251 \[plectis251\] | Proposition 1, Corollary 2 | Sparse nonnegative corrections below any unbounded allowance reach every real in an interval and keep all congruences. A bounded allowance is impossible. Sources: \[fridy1966\], \[crmarickovac2025, Lemma 4\], \[kovactao2024, Lemma 5.1\], \[vandoornkovac2025\]. | O |
| \#257 \[plectis257\] | Section 6 | The small-displacement quantity stays above $`1/2`$ at full support, where the value is irrational \[erdos1948\]. No proof covering full support can rest on it. | L, O |
| \#257 \[plectis257\] | Section 3 | Every positive divisor cover costs at least $`e`$ times the mean of $`\log^+`$ of its multiplicity. The averaging method cannot reach the prime support, where irrationality is known at base $`2`$ \[taoteravainen2025\]. | O |
| \#269 \[plectis269\] | Theorem 1 | Nonsingular minors of every order: no finite sum of products separates one exponent from the other two. Fan posted the two-prime separation \[fan2026comment\]; the three-prime statement is the note’s. | L |
| \#1049 \[plectis1049\] | Theorem 5 | A family of forms with degrees at most $`\delta n^2`$ and decay $`-\sigma n^2\log x`$ at every $`x>1`$ has $`\sigma\le\delta`$; its region never reaches $`\log b/\log a=1/2`$. Ordinary proof, with the contradiction step and the comparison with $`1/2`$ checked in Lean. | O, L |
| \#1049 \[plectis1049\] | Theorem 7 | The stated clearing conditions cannot be met at base $`3/2`$. | L |

Rows \#249 Section 5 and \#251 are instances of Theorem 1.1(ii) of the note. The others bound a method. We tried to state one inequality that covers \#1049 Theorem 5 and the cover cost of \#257, a cost of clearing denominators against the decay gained, and did not find a formulation that survives both sets of hypotheses. We do not claim the rows share a cause.

<a id="sec:misread"></a>

# One computation read wrongly twice

The computation \[plectisinvestigation\] runs the greedy rule in exact arithmetic on every reduced fraction in $`(0,E]`$ with $`2\le q\le Q`$.

*First reading.* At $`Q=36`$, $`382`$ of $`633`$ fractions are not rejected through step $`160`$ and $`14`$ are finite subsums, a share $`(382+14)/633=0.6256`$ close to $`1/E=0.6224`$. This was read as evidence that about $`62\%`$ of rationals are subsums, hence that \#257 is false. The reading is wrong. By Theorem 1.4 of the note the share at any fixed depth tends to $`2^NR_N/E`$ whatever the truth of \#257, because fractions equidistribute over the $`2^N`$ intervals that survive $`N`$ steps.

*Second reading.* After that correction, the rejections found at steps $`8`$, $`9`$ and $`12`$ once $`Q`$ reached $`200`$ were described as the informative data, and the $`12{,}218`$ fractions not rejected through step $`60`$ as survivors of interest. This is also wrong. The expected number rejected at step $`n`$ is $`2^{n-1}g_n\sum_{2\le q\le Q}\varphi(q)`$, asymptotically $`(3Q^2/\pi^2)2^{n-1}g_n`$, which is below $`1`$ for $`n>2\log_2Q-2\log_2\pi`$, about step $`12`$ at $`Q=200`$. Survival past that step is forced by counting, and the rejections before it confirm the measures of Lemma <a href="#lem:gaps" data-reference-type="ref" data-reference="lem:gaps">1</a> and nothing else. The error term $`O(2^N\log Q/Q)`$ of Theorem 1.4 is useful at $`Q=200`$ only for $`N`$ up to about $`5`$. At $`N=12`$ the observed share is $`0.62372`$ against $`2^{12}R_{12}/E=0.62245`$, an agreement better than the theorem guarantees.

What survives is the agreement itself. At $`Q=200`$ the counts at steps $`1`$ to $`9`$ are $`4809`$, $`1470`$, $`600`$, $`268`$, $`132`$, $`66`$, $`32`$, $`8`$, $`6`$, against $`4811`$, $`1467`$, $`604`$, $`277`$, $`133`$, $`65`$, $`32`$, $`16`$, $`8`$ from the measures of Lemma <a href="#lem:gaps" data-reference-type="ref" data-reference="lem:gaps">1</a>; steps $`10`$ and $`11`$ have none against $`4`$ and $`2`$, and step $`12`$ has $`4`$ against $`1`$. The late counts fluctuate more than independent events would, because rejections arrive in the families of Lemma <a href="#lem:translate" data-reference-type="ref" data-reference="lem:translate">2</a>.

<a id="sec:eliminated"></a>

# Eliminated ideas

1.  *If the reachable values form a null set, no rational value is reachable.* False. Take the binary series with digit $`1`$ everywhere except digit $`0`$ at positions $`n_1<n_2<\cdots`$, and allow each of those digits to be changed to $`1`$. The reachable values form a null set when the positions are sparse, by Theorem 1.1(i), yet changing all of them gives $`\sum2^{-n}=1`$. So no count of choices against contraction, and no depth depending only on sparsity, excludes a particular rational.

2.  *Every infinite subset of a host with null subsum set has an irrational sum.* A host is a set $`B`$ of allowed indices, and its subsum set is $`\{X_S(2):S\subseteq B\}`$. For hosts chosen without reference to the target this is open and is a form of \#257 itself. As a universal statement it cannot be a route: the support of any rational subsum with infinite $`S`$ would be such a host. The subsum set of a host $`B`$ has positive measure exactly when the complement of $`B`$ is finite, by Theorem 1.1(i) and the measure at full support.

3.  *The share of surviving fractions as evidence.* Section <a href="#sec:misread" data-reference-type="ref" data-reference="sec:misread">4</a>.

4.  *A wrong locator.* A draft of Theorem 1.3(b) cited Theorem 1.1 of \[adamczewskifaverjon2026\] as Nishioka’s theorem. That theorem says a value of a Mahler function at an algebraic point is rational or transcendental, which cannot prove irrationality. The proof in the note uses Mahler’s theorem \[mahler1929\], whose hypotheses are checked there.

5.  *Algebraic independence for \#1049.* With $`g`$ as in the note, $`\sum_{n\ge1}(t^n-1)^{-1}=\sum_{m\ \mathrm{odd}}g(t^{-m})`$, and each $`g(t^{-m})`$ is transcendental for rational $`t>1`$. This gives nothing for the infinite sum: limits of transcendental numbers take every value, and no form of Mahler’s method controls an infinite sum of Mahler values.

<a id="sec:known"></a>

# What was already known

- The covering argument of Theorem 1.1(ii) goes back to Kakeya; see \[hornich1941; nitecki2013; fridy1966\]. Its use to build rational series inside a class defined by soft data is the method of Kovač and Tao \[kovactao2024\], of Crmarić and Kovač \[crmarickovac2025\] and of van Doorn and Kovač \[vandoornkovac2025\].

- That the subsums of $`\sum(t^n-1)^{-1}`$ form a Cantor set at fixed $`t\ge2`$ is \[kovactao2024, Remark 4.1\].

- A closed set of positive measure can contain essentially no rationals \[boesdarsterdos1981\], so the heuristic of the note’s Section 4 cannot be a consequence of measure.

- Counting rationals of bounded height is studied for null Cantor sets \[rstw2019; chowvarjuyu2024\]. We found no work on rational points of a subsum set of positive measure, and none on rational points in the subsum-set literature. The searches were made on 20 September 2026 and are listed in the repository record.

- One identity with a consequence. Since $`\sum_{n\ge1}\mu(n)/(b^n-1)=1/b`$, the sums of $`(b^n-1)^{-1}`$ over squarefree $`n`$ with an even, respectively odd, number of prime factors are $`\tfrac12(X_{\mathrm{sf}}(b)\pm1/b)`$. Duverney and Tachiya prove that $`X_{\mathrm{sf}}(2^j)`$ is irrational \[duverneytachiya, Corollary 1.2 and Example 1.1\], as quoted in \[plectis257, Section 6\], so both sums are irrational at every base $`2^j`$. Both supports have divergent reciprocal sums. The identity at base $`2`$ is derived in \[plectis249, Section 5\]; the corollary may be known.

<a id="sec:questions"></a>

# Questions

1.  Is $`1/2`$ a subsum of $`\sum(2^n-1)^{-1}`$? The exact obligation is in \[plectis257, Theorem 7\]. By Lemma <a href="#lem:gaps" data-reference-type="ref" data-reference="lem:gaps">1</a> the general question is one-sided approximation of a rational by finite subsums $`X_F`$ to within $`g_{\max F}`$.

2.  Does the count of fractions of height at most $`Q`$ rejected at step $`n`$ stay close to $`(3Q^2/\pi^2)2^{n-1}g_n`$ in the joint range $`n\le(2-\varepsilon)\log_2Q`$, counted modulo the translations of Lemma <a href="#lem:translate" data-reference-type="ref" data-reference="lem:translate">2</a>? A persistent excess would be the first sign of an arithmetic mechanism for \#257.

3.  Is $`a^2>b^3`$ necessary in Theorem 1.3(a)? First case: base $`4/3`$, a chain with ratios $`2`$ and infinitely many ratios $`3`$.

4.  Is there one inequality behind \#1049 Theorem 5 and the cover cost of \#257?

5.  For factorial radices, is an allowance of order $`n`$ the exact threshold for a rational series within that allowance of a given one? Theorem 1.1 gives an interval when the allowance at level $`n`$ is at least $`n`$ and a null set when it is $`o(n)`$ along a sequence. This would explain why \#68 and \#251 resist opposite methods.

<div class="thebibliography">

99 W. Cook, [*Rational and irrational subsums of a Lambert series across bases*](../../../paper/synthesis/erdos-synthesis-subsums-across-bases.pdf), Erdős Problem Notes, 2026.

W. Cook, *Choices, contraction and rational membership*, exact computation with saved outputs in `research/experiments/choices_contraction/` of the repository, 2026.

P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. 12 (1948), 63–66.

H. Hornich, *Über beliebige Teilsummen absolut konvergenter Reihen*, Monatshefte für Mathematik und Physik **49** (1941), 316–320. [doi:10.1007/BF01707309](https://doi.org/10.1007/BF01707309).

Z. Nitecki, [*Subsum sets: intervals, Cantor sets, and Cantorvals*](https://arxiv.org/abs/1106.3779v2), arXiv:1106.3779v2 (2013).

John A. Fridy, [*Generalized bases for the real numbers*](https://www.fq.math.ca/Scanned/4-3/fridy.pdf). The Fibonacci Quarterly **4** (1966), no. 3, 193–201.

T. Crmarić and V. Kovač, [*On the irrationality of certain super-polynomially decaying series*](https://arxiv.org/abs/2504.18712v1), Colloq. Math. **179** (2025), 55–68, doi:[10.4064/cm9628-5-2025](https://doi.org/10.4064/cm9628-5-2025). Theorem locators follow arXiv:2504.18712v1.

Vjekoslav Kovač and Terence Tao, [*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593v4). Acta Mathematica Hungarica **175** (2025), 572–608, doi:[10.1007/s10474-025-01528-0](https://doi.org/10.1007/s10474-025-01528-0); arXiv:[2406.17593v4](https://arxiv.org/abs/2406.17593v4). Statement and section numbers refer to arXiv version 4.

Wouter van Doorn and Vjekoslav Kovač, [*Lacunary sequences whose reciprocal sums represent all rational numbers in an interval*](https://arxiv.org/abs/2509.24971v3). Acta Arithmetica **223** (2026), 275–295, doi:[10.4064/aa251001-13-1](https://doi.org/10.4064/aa251001-13-1); arXiv:[2509.24971v3](https://arxiv.org/abs/2509.24971v3). Statement numbers refer to arXiv version 3.

D. Duverney and Y. Tachiya, [*Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf), Forum Math. 31 (2019), no. 6, 1557–1566, [DOI](https://doi.org/10.1515/forum-2018-0299). Page numbers refer to the linked author preprint.

T. Tao and J. Teräväinen, [*Quantitative correlations and some problems on prime factors of consecutive integers*](https://arxiv.org/abs/2512.01739v2), arXiv:2512.01739v2 (submitted December 2025, revised April 2026).

Steve Fan, *Comment on Erdős Problem \#269, thread 269, post 7218* (2026), [source](https://www.erdosproblems.com/forum/thread/269#post-7218). 26 June 2026.

K. Mahler, *Arithmetische Eigenschaften der Lösungen einer Klasse von Funktionalgleichungen*, Math. Ann. **101** (1929), 342–367.

Boris Adamczewski and Colin Faverjon, *Mahler’s method in several variables and finite automata*, Annals of Mathematics **204**, no. 2 (2026), 455–533, [doi:`10.4007/annals.2026.204.2.1`](https://doi.org/10.4007/annals.2026.204.2.1). Locators refer to the [68-page author manuscript](https://faverjon.perso.math.cnrs.fr/AdamczewskiFaverjon_MahlerFiniteAutomata.pdf).

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

</div>

<a id="declaration-of-generative-ai-use"></a>

# Declaration of generative AI use

The mathematics and text of this record were produced with large language model agents under the direction of the author, who is responsible for every claim. The checks were these: each proof was written by one agent and refereed by a second with instructions to break it; the computations were rerun independently; the external citations were opened on 20 September 2026, and the one that failed is recorded in Section <a href="#sec:eliminated" data-reference-type="ref" data-reference="sec:eliminated">5</a>. None of this is review by a mathematician.
