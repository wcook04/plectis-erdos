<a id="writing-mathematics-from-reviewed-revisions"></a>

# Writing Mathematics from the Literature and Reviewed Revisions

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

A fluent sentence can leave the decisive inference unexplained. This guide starts with that difficulty: locate the step a reader cannot reconstruct, study a relevant argument in the literature, and explain the step using the manuscript’s own proof. Worked cases show how a remainder establishes attainment, how a target interval determines an error threshold, and why convergence of each summand is not yet convergence of an infinite sum. Other cases expose changes of scope hidden in ordinary words and distinguish what a system records, checks and demonstrates. Drawn from revisions of eight Erdős-problem papers and their supporting systems manuscript, the examples supply reasons and limits for the compact companion’s instructions. The guide documents editorial practice, not new mathematical results or measured improvements in reader understanding.

<a id="sec:reading"></a>

# Learning to explain a particular argument

<div id="exposition-reading">

</div>

Suppose a proof chooses digits one at a time to represent a target. Showing that another choice is always possible does not yet identify the infinite sum. The missing information is what remains of the target:
``` math
r_n=x-S_n,\qquad 0\le r_n\le\varepsilon_n,\qquad
 \varepsilon_n\longrightarrow0
```
so the partial sums $`S_n`$ converge to $`x`$. Replacing “we repeat” by “we continue inductively” would explain no more. The remainder bound connects the finite choices to the infinite sum; the name of the iteration does not.

To find such an explanation, locate the last fact already established and the first conclusion the reader is asked to accept. Ask what connects them. Here the connection is a remainder bound tending to zero, not merely a remainder that stays bounded. A source facing the same task can suggest how to expose this distinction. Section <a href="#sec:remainder" data-reference-type="ref" data-reference="sec:remainder">2.1</a> develops the comparison; the new manuscript must still justify its own covering and remainder bounds.

Halmos discusses audience, organisation and examples \[halmos, §§3–4\]. Knuth, Larrabee and Roberts discuss introducing symbols, connecting sentences and explaining why a step is taken \[knuth, §1\]. Gowers considers where examples should precede unfamiliar abstractions \[gowers\]; Tao cautions against sacrificing usefulness to excessive optimisation \[tao\]. This advice identifies questions. A nearby argument shows how an author answered them in a particular setting.

The cases come from revisions of papers on Erdős problems. Read them by the difficulty at hand: construction and attainment in Section <a href="#sec:remainder" data-reference-type="ref" data-reference="sec:remainder">2.1</a>; the accuracy needed from an estimate and the meaning of a failed test in Section <a href="#sec:certificate" data-reference-type="ref" data-reference="sec:certificate">3.1</a>; limits through infinite sums in Section <a href="#sec:worked-explanations" data-reference-type="ref" data-reference="sec:worked-explanations">3</a>; changes of meaning in Section <a href="#sec:review" data-reference-type="ref" data-reference="sec:review">4</a>. Section <a href="#sec:practice" data-reference-type="ref" data-reference="sec:practice">5</a> explains how to review a revision and keep its useful lesson without making every case a new rule.

<a id="choose-sources-by-the-work-the-prose-must-do"></a>

## Choose sources by the work the prose must do

Choose the reader before choosing the amount of explanation. An expert may know a lemma but not why it is used here; a neighbouring specialist may need its statement. Tao’s advice distinguishes the author’s familiarity from the reader’s knowledge \[tao-detail\]. State the assumed background, then explain what it does not supply.

Subject and genre matter too. An irrationality note may turn an assumed rational sum into a positive integer smaller than one. A geometric paper may first need to identify the component being measured and the map preserving its size. A survey compares viewpoints; a short theorem paper may develop one argument. A useful source should illuminate the particular task, not merely have an admired style.

The introduction must answer both “what changes with this result?” and “why does the proof work?” Compare assumptions and conclusions with the closest prior result: a stronger conclusion under stronger assumptions need not be a stronger theorem. Then identify the obstacle and the step that overcomes it. A list of section titles does neither. Nor does calling a hypothesis “natural” explain its force. For a conditional theorem, say which familiar cases satisfy or fail the hypothesis, where known, and where the proof uses it. One example shows applicability, not the breadth of the admissible class. Identify any unresolved premise so that a reduction does not read as though that premise were proved.

Read a close subject paper for vocabulary and attribution, and, when useful, a structurally similar proof for the explanation of a construction or estimate. A remote paper cannot settle the target field’s conventions, and frequent usage does not excuse a mismatched definition.

Use the same comparison at the scale of the proof. A roadmap should explain how its stages fit, not just name them \[halmos, §4\]. In Section <a href="#sec:estimate" data-reference-type="ref" data-reference="sec:estimate">2.2</a>, finitely many tail values give repetition; recovery is needed to make repeated values force repeated blocks. “We estimate the tails and finish the proof” hides that dependency.

Read the original passage in an identified version, including the statement, hypotheses and argument around the sentence. An abstract may establish a term, but seldom shows how the proof is explained. Record a section, theorem or equation locator and a page; numbering can change between versions. Keep source digests in the reading record. They identify the supplied bytes, whereas a public link gives the reader a route to the work.

For a difficult passage, reconstruct the local argument before borrowing its presentation. Knuth, Larrabee and Roberts give a useful worked comparison \[knuth, §§2–3, pp. 7–8\]. Their example considers vectors $`c+kb`$ whose coordinates are nonincreasing for every nonnegative integer $`k`$. Fix the vectors $`c,b`$ and coordinates $`i<j`$. Rearranging the coordinate inequality gives
``` math
c_i-c_j\ge k(b_j-b_i)\qquad(k\ge0).
```
The left side is fixed. If $`b_j-b_i`$ were positive, the right side would grow without bound; hence $`b_j\le b_i`$. The source compares a proof choosing a particular $`k`$ for a contradiction with a direct proof using this dependence. The improvement exposes what stays fixed while $`k`$ grows. The words “for arbitrarily large $`k`$” make the displayed inequality decisive; they do not merely describe a limiting procedure. This is a reason for this proof’s order, not a reason to ban contradiction arguments.

Now ask which fact in the target proof could make its own conclusion equally unavoidable. In the opening construction, that fact is a remainder bound tending to zero. When the target proof contains no such fact, the comparison has exposed a mathematical obligation; it has not supplied an explanation that can safely be inserted.

Source availability, a recipient’s reading declaration and a later reviewer’s passage inspection are separate facts. Later inspection can verify a locator or expose a poor analogy; it cannot establish what the earlier recipient read.

<a id="read-sentences-as-mathematical-relations"></a>

## Read sentences as mathematical relations

Read each explanatory phrase as part of the argument. A theorem must state the objects and assumptions needed for its conclusion; inside the proof, recall an assumption when it explains a step. “By positivity” leaves work for the reader unless the positive quantity and its use are clear. In the tail estimate of Section <a href="#sec:certificate" data-reference-type="ref" data-reference="sec:certificate">3.1</a>, positivity of the omitted tail gives the lower inequality, whereas its upper bound gives the other. Naming those two jobs is more useful than adding “clearly” to the conclusion.

Connective words deserve the same attention. “Since” introduces a reason; “hence” asserts that the conclusion follows; “provided that” makes a condition visible; “it remains to prove” identifies unfinished work. These words are not interchangeable devices for varying a paragraph. A revision that changes “provided that” to “hence” can change the logical force of the sentence while leaving every displayed formula intact.

Parallel syntax helps compare claims; a subordinate clause keeps a condition beside its consequence. Sentence length alone settles neither choice: a short sentence may hide its antecedent, while a longer one makes the dependency clear. Study that relation, then write original prose for the new argument.

Notation should receive this close reading as well. Ask when a symbol first becomes necessary, what repeated work it saves and which nearby quantities the reader might confuse with it. A new name for a standard object creates an additional translation. Removing an established term such as “Stieltjes moment sequence” can instead sever a useful connection to the literature \[wangzhu\]. Check both the name and its referent: in Section <a href="#sec:formula-choice" data-reference-type="ref" data-reference="sec:formula-choice">3.2</a>, the divisibility condition concerns a future index, not its offset from the present one. Familiar words can misidentify an object as easily as private terminology.

Give space to the reason hardest to recover, not the longest calculation. State the required accuracy before the estimate and the selecting constraint before the parameter; routine substitutions can then be brief. A one-line limit may nevertheless need a paragraph when the number of factors grows (Section <a href="#sec:fixed-partition" data-reference-type="ref" data-reference="sec:fixed-partition">3.3</a>). Expose the dependency, not an author’s cadence.

A repeated technique may serve a different purpose later in the proof. In the R11 revision, the \#243 paper uses finite differences for two distinct purposes. A fourth difference tends to zero and is integer-valued, so it eventually vanishes; this gives eventual polynomial behaviour. Later, a positive constant third difference bounds a divisibility chain of positive greatest common divisors, so that chain stabilises \[paper243, finite-difference argument\]. Naming the technique twice would not distinguish these conclusions. The added sentence identifies the second job. This is a local instance of Knuth et al.’s advice to tell the reader why a step is taken \[knuth, §1, item 12\], not a requirement to explain every routine calculation again.

<a id="use-examples-without-delaying-the-result"></a>

## Use examples without delaying the result

An example earns its place when it prepares a particular inference. Choose its size for that job: a table in which every height occurs once would conceal the multiplicity issue in Section <a href="#sec:multiplicity" data-reference-type="ref" data-reference="sec:multiplicity">2.3</a>. In the opening construction, one choice can show how the remainder stays admissible, but not that it tends to zero. An example may reveal a classification’s coordinates; the proof must still show that every admissible object has them. State which task the example performs.

Placement depends on what is unfamiliar. Gowers’s follow-up to “examples first” qualifies the recommendation by audience and genre, and considers readers who approach a text nonlinearly \[gowers-followup\]. A brief example can precede a locally unfamiliar definition while the headline theorem remains early and easy to find. An example of a familiar definition may instead belong after the statement, at the point where it explains a new use.

This distinction also governs repetition. Knuth, Larrabee and Roberts recommend complementary descriptions of important objects \[knuth, §1, item 11\]. In Section <a href="#sec:certificate" data-reference-type="ref" data-reference="sec:certificate">3.1</a>, the inequalities tell the reader what to check; the enclosure explains why those checks suffice. Removing either would lose a different use. Repeating the conclusion in new adjectives would add neither. Judge repetition by the work the second account makes possible.

<a id="sec:revisions"></a>

# Explain the choices in a proof

<div id="exposition-revisions">

</div>

These cases concern attainment and the accuracy an inference requires. They were accepted in the short-paper R6 round of 30 September 2026, not the earlier September series with the same round numbers. The records retain the passages at commit `18cedaddedd1`, its full identity and source digests \[ledger\].

<a id="sec:remainder"></a>

## From repeated choice to an attained infinite sum

The \#251 paper contains a construction in which a target $`x`$ is represented by chosen digits $`d_j`$ and weights $`w_j`$. A finite remainder $`\rho_j`$ is kept between $`0`$ and a bound $`F_j`$. The old passage began:

> Given $`x\in[0,F_0]`$, we choose $`d_0`$ so that $`x-d_0w_0\in[0,F_1]`$ and repeat this choice for each successive remainder.

This leaves two questions: why is the next digit available, and why does continuing the choices represent the whole target? The reviewed addition answers them separately:

> The covering just proved makes this possible at every stage. The invariant $`0\le\rho_j\le F_j`$ and $`F_j\to0`$ then give

and continues with the limiting identity. The first sentence says why the construction can continue. The second says why its partial sums reach the chosen target: the part still missing is forced to zero. The record is `r6-251-style_rules-04`; its full identifier includes the series date.

Crmarić and Kovač’s proof of Lemma 4(a), in the first version of their paper on sums of reciprocals, provides a close model \[crmaric, pp. 4–5\]. They keep a finite remainder in an interval and use convergence to obtain the represented value. What transfers is the separation of two questions: can the next choice be made, and does the resulting sequence attain the target?

The \#251 construction must justify its covering, invariant and $`F_j\to0`$, as well as sparsity and arithmetic constraints. Neither a finite digit example nor the literary comparison supplies those proofs. The integration preserved these obligations and the unresolved status of the original prime-gap problem.

<a id="sec:estimate"></a>

## State how accurate the estimate must be

In the \#269 argument, a rationality assumption places normalized tails $`Y_a`$ in the finite set
``` math
(K^{-1}\mathbb Z)\cap(0,1).
```
Here $`K\ge1`$ is the integer denominator in the rationality assumption. Finiteness forces two tails to agree; it does not force their successors to agree. The accepted revision makes the remaining task explicit: recover the next block and tail from the present tail. Only then does equality propagate.

Hančl and Tijdeman begin their proof of Theorem 2.1 with an integral scaled remainder obtained from rationality \[hancl, p. 373\]. The \#269 revision likewise identifies the arithmetic object before estimating it; recovery is its own additional task, not supplied by the cited proof.

The next difficulty is quantitative. The maps $`G_{53}(t)=(9+t)/30`$ and $`G_5(t)=(3+t)/10`$ encode two possible blocks of prime-power jumps. Their images overlap on the initial tail range $`[0,1]`$, so a value in the overlap does not identify its block. Both maps are increasing: to separate their images, compare the upper end of one with the lower end of the other. With the lower bound $`3/10`$ already established, the revision states the required accuracy first:

> With that lower endpoint, separating these two images requires an upper endpoint $`U`$ satisfying
> ``` math
> G_{53}(U)<G_5(3/10),\qquad
>  \frac{9+U}{30}<\frac{33}{100},\qquad U<\frac9{10}.
> ```
> This specifies the improvement needed from the arithmetic sequence.

The case is `r6-269-style_rules-03`. The threshold is sufficient for this argument, not necessary for every possible method. The return’s Knuth analogy concerns presentation; the separation inequality supplies the mathematics.

The source obtains the required improvement from the spacing of powers of $`5`$. At a block containing such a power the tail is at most $`7/15`$. Every three consecutive blocks contain at least one such block; moving backwards at most twice, each step is bounded by $`t\mapsto(1+t)/2`$. This gives $`U=13/15<9/10`$, for the actual prime-power sequence, not arbitrary block words. The source separates all five block images on this interval. The image identifies the block; its affine inverse determines the next tail. Equality can now propagate \[paper269, proof of the distinct-height theorem\].

<a id="sec:multiplicity"></a>

## An example must reveal the relevant difference

The same manuscript distinguishes summing over smooth integers from summing over the distinct values of their running least common multiple. Here the allowed prime factors are $`2,3,5`$; a positive integer with no other prime factor is called $`5`$-smooth. For $`x\ge1`$ its running least common multiple is
``` math
H(x)=\operatorname{lcm}\{u\le x:u\text{ is }5\text{-smooth}\}
     =2^{\lfloor\log_2x\rfloor}
      3^{\lfloor\log_3x\rfloor}
      5^{\lfloor\log_5x\rfloor}.
```
The formula selects the largest power of each allowed prime not exceeding $`x`$ \[paper269, definition of running least common multiples\]. For example, $`H(16)=16\cdot9\cdot5=720`$. These are the quantities called heights in the revision. The seven $`5`$-smooth integers in $`[16,32)`$ give:

<div class="center">

| $`5`$-smooth integers $`u`$ | $`H(u)`$  | Sum of $`1/H(u)`$ |
|:----------------------------|:----------|:------------------|
| $`16,18,20,24`$             | $`720`$   | $`4/720`$         |
| $`25`$                      | $`3600`$  | $`1/3600`$        |
| $`27,30`$                   | $`10800`$ | $`2/10800`$       |

</div>

The map from a smooth integer to its height is not one-to-one. Summing over smooth integers counts every visit to a height; summing over distinct heights counts it once. The multiplicities $`4`$ and $`2`$ are the sizes of the corresponding fibres. They explain why the sums cannot be identified merely because the same heights occur in both. The record `r6-269-style_rules-04` also retains an endpoint warning: the distinct-height argument uses $`(16,32]`$, whereas the table uses $`[16,32)`$. Matching the endpoint conventions is a separate task from preserving multiplicity.

The repeated heights make this table useful: they expose the counting convention. Halmos’s concrete cases and Gowers’s examples-first discussion suggest that choice \[halmos, §4\]\[gowers\]; they prescribe no order for every reader. The infinite-series theorem still needs its proof.

<a id="sec:worked-explanations"></a>

# From a formula to the sentence that explains it

These cases answer a reader’s question from an existing formula. They come from eight additional editorial returns (#1049 is labelled R9), checked against current manuscript sources. They add no theorem, formal coverage or release status.

<a id="sec:certificate"></a>

## How does the target determine the finite test?

A certificate is easier to understand when the reader sees the set it must certify before seeing its arithmetic form. In the \#251 paper, two tail differences satisfy
``` math
D'=2D-\delta,\qquad \delta=2s,\qquad s\in\{-1,1\}.
```
The already proved local criterion asks for $`1/2<sD<1`$; it then gives $`-1<sD'<0`$. The finite calculation supplies integers $`A,Q,B`$ with $`Q>0`$, $`B\ge0`$ and $`|QD-A|\le B`$ \[paper251, section on finite separation\]. It is tempting to write only that two ensuing inequalities certify the target. The missing explanation is the enclosure itself:
``` math
sD\in\left[\frac{sA-B}{Q},\frac{sA+B}{Q}\right].
```
Multiplication by either sign preserves the error bound. The lower endpoint must exceed $`1/2`$, and the upper endpoint must be below $`1`$. Thus the entire closed enclosure lies in $`(1/2,1)`$ exactly when
``` math
2sA-Q>2B,\qquad Q-sA>B.
```
The two inequalities express the two endpoint gaps. The factor $`2`$ in the first comes from the lower endpoint $`1/2`$, not an arbitrary safety margin. Strictness matters because the boundary values give $`sD'=-1`$ or $`0`$.

Now separate a failed enclosure from a failed claim. Take $`D=3/4`$, $`s=1`$, $`Q=4`$, $`A=3`$ and $`B=1`$. The error bound is valid, but the enclosure $`[1/2,1]`$ touches both forbidden endpoints. Neither strict test passes, although $`D`$ lies in the target interval. With these same $`D,Q,A`$, the sharper bound $`B=0`$ would pass both tests. The failed enclosure therefore need not mean a failed claim. The enclosure even has width less than one and still contains an integer: its position, not just its width, matters.

The \#68 remainder has a related, one-sided geometry. It is $`A_N+M(S-H_N)`$, where $`S`$ is the series sum, $`H_N`$ its $`N`$th partial sum, and $`M>0`$ scales the strictly positive omitted tail. To put this remainder between consecutive integers, it suffices to prove
``` math
0<M(S-H_N)<\lfloor A_N\rfloor+1-A_N.
```
The left inequality puts the remainder above $`\lfloor A_N\rfloor`$; the right puts it below $`\lfloor A_N\rfloor+1`$ \[paper68, section on nonintegrality\]. A tail smaller than one could still cross the next integer; it must be smaller than this particular gap. At an integral $`A_N`$ the gap is $`1`$. Replacing the strict successor by $`\lceil A_N\rceil`$ would make it zero. The endpoint distinguishes two superficially interchangeable conventions.

<a id="sec:formula-choice"></a>

## Why was this base or kernel chosen?

A change of notation should reveal a constraint or save an operation. In one \#249 comparison construction, only the even-indexed coefficients may change. Writing $`e_n`$ for the coefficient changes, their contribution to a binary series is
``` math
\sum_{m\ge1} e_{2m}\,2^{-2m}
                 =\sum_{m\ge1}e_{2m}\,4^{-m}.
```
The permitted support has selected base four. Stating this before the digit construction explains the choice and shows immediately why the odd coefficients remain untouched \[paper249long, comparison-sequence construction\]. The identity alone says nothing about which corrections can be attained under additional coefficient bounds; those are separate assertions of the construction.

The \#257 divisor kernel admits an equally direct introduction. Fix integers $`N\ge0`$ and $`d\ge1`$, and let $`B>1`$. If $`r\ge1`$ satisfies $`d\mid N+r`$, then its possible values are
``` math
d-(N\bmod d),\quad 2d-(N\bmod d),\quad\ldots.
```
Consequently
``` math
\sum_{\substack{r\ge1\\d\mid N+r}}B^{-r}
 =\frac{B^{N\bmod d}}{B^d-1}.
```
This is the weight of the future positions at which $`d`$ divides the index. It explains the kernel before averaging is introduced \[paper257, finite means for shifted divisor tails\]. Divisibility applies to $`N+r`$, not to $`r`$ alone. When $`d\mid N`$, the first positive offset is $`d`$, so the same formula applies without adding an unwanted offset zero. In that paper $`B=2^\alpha`$, with $`0<\alpha\le1`$; estimates must retain their dependence on $`B-1`$ as $`\alpha`$ becomes small.

In both examples the operation determines the notation. Even-indexed binary weights become base-four weights; offsets to future indices divisible by a fixed divisor form the progression giving the kernel. State that reason before naming the formula. Tao’s notation advice supports making important dependencies visible and translating borrowed conventions \[tao-notation\]; the support and divisibility conditions supply the mathematical reasons here.

<a id="sec:fixed-partition"></a>

## What remains to justify after an index is fixed?

Fixing a summation index need not leave a fixed finite product. In the \#1049 moment-determinant argument, a summand is indexed by a partition $`\mu_1\ge\cdots\ge\mu_\ell>0`$, with $`\mu_k=0`$ for $`k>\ell`$. The base $`q\in(0,1)`$ and the partition are fixed while $`N\to\infty`$. The ratios of shifted weights tend to one, but the Vandermonde quotient still contains factors indexed by $`k`$ up to $`N`$ \[paper1049, proof for geometric moment determinants\].

For $`N\ge\ell`$ and fixed $`1\le j\le\ell`$, cancel the common factors in the part with $`k>\ell`$:
``` math
\prod_{k=\ell+1}^{N}
       \frac{1-q^{k-j+\mu_j}}{1-q^{k-j}}
 =\frac{\displaystyle\prod_{r=0}^{\mu_j-1}(1-q^{N+1-j+r})}
        {\displaystyle\prod_{r=0}^{\mu_j-1}(1-q^{\ell+1-j+r})}.
```
The original product has $`N-\ell`$ factors, but each endpoint product has the fixed length $`\mu_j`$. Its numerator tends to $`1`$; its denominator is fixed and positive. The remaining factors have $`j,k\le\ell`$ and are independent of $`N`$, so the whole quotient converges for this fixed partition. The telescoping formula, proposed in the later return, justifies what factorwise convergence in a growing product would not.

Passing the limit through the sum requires a second argument. Extend the summand by zero when $`\ell>N`$, fixing the index set. The source’s nonnegative majorant is independent of $`N`$. Dropping the ordering of the positive parts gives an upper bound by separate sums for each part. The $`j`$th sum is at most a fixed constant times $`q^{2j-1}`$: geometric decay controls its polynomial weight. Multiplying gives a bound for the total majorant at length $`\ell`$:
``` math
K^\ell q^{\ell^2},
```
where $`K>0`$ may depend on the fixed base and the fixed weight-bound constants. Here $`\ell^2=1+3+\cdots+(2\ell-1)`$ is the minimum total displacement exponent for $`\ell`$ positive parts. Their sizes have been summed out; their number remains. The ratio of successive bounds is $`Kq^{2\ell+1}\to0`$, so the sum over $`\ell`$ converges and dominated convergence applies.

The conclusions are distinct: the whole summand converges for a fixed partition; a summable bound controls all partitions uniformly in $`N`$. Neither asserts uniformity as $`q\uparrow1`$. The fixed base is part of the statement.

<a id="sec:detection"></a>

## Does a complete test provide the required witnesses?

In the \#249 test, fix a positive integer shift $`h`$ and an index $`N\ge0`$, and write $`D`$ for that particular real tail difference. At each positive integer depth $`L`$, the paper computes an integer $`A_L`$ and proves
``` math
|2^LD-A_L|\le B_L,\qquad B_L=N+h+L+2.
```
An integer $`D`$ would put a multiple of $`2^L`$ in this closed enclosure. Hence one can certify nonintegrality by checking
``` math
B_L<(A_L\bmod 2^L)<2^L-B_L,
```
where the residue is chosen in $`\{0,\ldots,2^L-1\}`$ \[paper249, section on binary totient tails\]. The two strict margins keep the enclosure away from the neighbouring multiples of $`2^L`$.

The test also detects every nonintegral fixed $`D`$ at some depth. Its gap $`\|D\|_{\mathbb R/\mathbb Z}`$ from the nearest integer is then a positive constant. The source proves that detection follows once
``` math
2^L\|D\|_{\mathbb R/\mathbb Z}>2B_L.
```
The factor $`2`$ pays for two distances: from $`2^LD`$ to the computed centre $`A_L`$, then from that centre to an enclosure endpoint. Each is at most $`B_L`$; the displayed gap keeps the whole enclosure away from multiples of $`2^L`$. Since $`2^L`$ grows exponentially and $`B_L`$ linearly, a suitable depth exists. Thus the test has a converse, not merely a sufficient condition.

The converse has two limits. An integral value never triggers the test; failure at the depths tried does not certify integrality. Nor does detecting a fixed nonintegral value supply the inputs needed for irrationality: for every positive shift and every cutoff, some later index must have a nonintegral difference. Existence of such an index is a separate question; increasing depth only refines the test of a fixed index. Preserve the converse without mistaking it for the missing existence statement.

Whenever a proof offers arbitrarily accurate certificates, state which object stays fixed as the accuracy improves. If the object changes too, its distance from the forbidden set may shrink, and a new comparison is needed. This is the same discipline that made the fixed-base limit in Section <a href="#sec:fixed-partition" data-reference-type="ref" data-reference="sec:fixed-partition">3.3</a> readable.

<a id="sec:review"></a>

# Review changes without changing their meaning

<div id="exposition-review">

</div>

A smoother sentence can make a different claim. Compare the proposal with the current statement and proof before judging its style: what may vary, which objects must be shared, and which direction of implication is justified? The following cases show how a changed noun, verb or omitted condition can alter those answers.

Record whether the proposal was accepted, revised, rejected or left pending a named check, retaining the exact passages and the decision’s source. A text match locates a change; it does not establish equivalence. A missing argument requires mathematical review, and acceptance of a local revision does not adopt a universal writing rule.

<a id="replace-a-local-term-without-losing-its-definition"></a>

## Replace a local term without losing its definition

In the R7 \#249 revision, a private growth adjective was replaced by its defining condition:

> *Before:* tempered integer carry orbit.
>
> *Selected revision:* integer carry sequence $`u`$ with $`u(N)/2^N\to0`$.

The gain is specific. A reader no longer has to recover a private definition to know the required rate. It would be incorrect to replace this condition by the more familiar phrase “subexponential growth”, which says something stronger. Other revisions retained standard terms such as upper Banach density because those terms denote the properties the paper actually uses. The test is definitional: substitute the proposed term’s meaning back into the claim, then check that the same sequences qualify.

Removing a shorthand can also remove the visible source of its assumptions. In \#243, “positive exact state” bundled recurrence and positivity conditions. A proposed replacement referred to the same assumptions after that definition had disappeared. The integrating reviewer instead stated the recurrences for the first implication, then explicitly added natural-number domains and $`a_n>1`$, $`C_n>0`$ for the eventual consequence. In a second passage, the reviewer removed “earlier” from “earlier decreases”: the original qualification did not restrict the time at which decreases could occur.

These R7 selections are not the original proposals or later formal-correspondence and rendering checks. The replacement must carry the same assumptions and quantifiers, not merely read more easily.

<a id="check-the-ordinary-words-that-carry-scope"></a>

## Check the ordinary words that carry scope

An unchanged formula can acquire a stronger claim from its surrounding prose. The R11 \#251 revision replaces “uses all late indices” by “permits changes at every index after the prefix” in a comparison construction \[paper251long, comparison construction\]. The second describes allowed positions, not a promise that every one is changed. In the sparse construction, the containing set $`S`$ and target interval are fixed before the target is chosen; the correction depends on that target, and its support may occupy only part of $`S`$ \[paper251, sparse-perturbation proposition\].

The same revision replaces the claim that corrections can “grow arbitrarily slowly” by an eventual upper bound chosen in advance. Given any prescribed function tending to infinity, the corrections can eventually be bounded by it. This does not say that the corrections themselves tend to infinity. Read the choice order as an instruction: prescribe the bound first, then construct corrections subject to it. This exposes what the short phrases obscured. Expand the expression whose ordinary reading changes that order or turns permission into a requirement.

<a id="rejecting-an-attractive-universal-rule"></a>

## Rejecting an attractive universal rule

Earlier reviews of the \#243 manuscript illustrate why historical advice needs its original setting. One round asked for a cubic irrationality example near the beginning. A subsequent round explicitly retained the live bounded-negative result as the paper’s lead and rejected an invariant rule that an irrationality result must always come first. Later editorial routes treated page targets as subordinate to the proof’s dependencies.

The retained lesson is to choose a coherent principal contribution and explain its relation to the named problem. It does not prescribe a theorem category or a fixed page on which every proof must finish. A conditional reduction can be the useful result; an unconditional statement can be too weak to carry the paper. The choice requires comparing what the results actually say. The history record preserves the successive recommendations instead of combining them into contradictory commands.

This distinction also protects the longer research record. Shortening a paper can be appropriate when the subordinate details have a complete, checked destination. Regenerating the long record from the shortened version would lose the very argument that made the shorter presentation possible. The two documents must be compared in both directions: a stronger hypothesis, a repaired endpoint or a newly explained limiting step may appear first in either one.

<a id="distinguish-clarification-from-a-proof-repair"></a>

## Distinguish clarification from a proof repair

An earlier \#251 review found more than an unclear sentence. A condensed sparse-construction proof used a buffer quantity without assigning it a sequence coordinate or including it in the value, size and capacity accounting. The original returned memorandum did include those coordinates and their contribution to the weighted sum. The accepted ordinary repair restored the assignments and the accounting across all indices.

The distinction matters for both mathematics and attribution. The condensed proof needed repair; the recoverable original showed that the loss had occurred during shortening or integration, not in that construction. This repair was undertaken in its own mathematical review. An exposition-only pass should identify such a defect and refer it, not silently supply the missing proof. A later sharp companion construction was still unreviewed at its recorded disposition. Sharing a bundle with the repaired proof did not give it the same status.

Other cases expose similar changes of meaning in small amounts of prose. In \#1049, language suggesting that a degree bound was inevitable was repaired to state a sufficient inequality and preserve the qualification contributed by a remaining factor. In \#1041, the revision retained the fixed-polynomial scope instead of turning it into a freely varying family. For mixed irrationality criteria in \#257, two unbounded sets of candidate indices may be disjoint: the even and odd integers provide an elementary example. The proof needs one index satisfying both conditions. The source adds the two nonnegative, normalised errors on the same finite distribution. Their sum has mean below one, so it is below one at some sampled index. Nonnegativity puts both errors below one there; no independence is needed \[paper257, common-index argument\]. These are mathematical checks even when the edit is presented as compression or style.

Compare the Lean proposition with the prose, including definitions, hypotheses and quantifiers. A checked ingredient need not cover the assembled argument. An ordinary proof may lack complete formalisation. Keep named inputs and pending comparisons visible. The systems paper’s records preserve these distinctions \[systems\]; describing them does not confer proof status.

A late-September prose pass removed remarks naming mathematical inputs beside the dependent results; the integrating agent restored them. Details of running a check could recede, but the dependencies could not. Calling both kinds of sentence workflow commentary had erased a mathematical qualification.

<a id="sec:words-as-claims"></a>

## Read explanatory words as mathematical claims

Test a mathematical adjective by substituting its definition. A “convex combination” requires nonnegative weights whose sum is one. Checking only their signs leaves half the condition untested. In \#1041, Abel summation expresses $`f(t\zeta)`$ as
``` math
f(t\zeta)=\sum_{j=0}^{n-1}(t^j-t^{j+1})S_j,
 \qquad S_j=\sum_{k=0}^{j}a_k\zeta^k,
```
where $`n\ge1`$, $`f(z)=\sum_{k=0}^n a_kz^k`$ and $`f(\zeta)=0`$. For $`0\le t<1`$, the nonnegative coefficients sum to $`1-t^n`$. Thus it is $`f(t\zeta)/(1-t^n)`$ that the calculation directly presents as a convex combination of the $`S_j`$ \[paper1041, section on trinomials\]. At $`t=1`$ this quotient is undefined, and the proof instead uses $`f(\zeta)=0`$. Naming the normalised quantity checks the definition and the endpoint in the same sentence. A root-distance calculation or a statement about segments to zeros must likewise retain the particular geometric object it controls.

A shorter proof can also be clearer when its reason is already available. The \#243 arithmetic normal form is
``` math
Q(n)=m\binom{n+2}{3}+c,
                 \qquad m\in\mathbb Z_{>0},
```
and $`Q(n)`$ is known to be integral at every sufficiently large integer $`n`$. At any such nonnegative $`n`$, the binomial coefficient is integral, so $`c=Q(n)-m\binom{n+2}{3}`$ is integral \[paper243, reduction and the constant term\]. The proposed explanation uses exactly those established facts. Replacing them by “$`Q`$ is an integer polynomial” would be unsafe: an integer-valued polynomial can have nonintegral coefficients, as $`n(n-1)/2`$ shows. The useful simplification names the available arithmetic structure.

In the \#257 finite average, $`L,d,T`$ are positive integers. The residues of $`L,2L,3L,\ldots`$ modulo $`d`$ repeat with period $`d/\gcd(L,d)`$; the sample uses only the first $`T`$ terms. The inequality $`d\le LT`$ does not assert that one whole period occurs. For $`L=3,d=5,T=2`$, it holds while the period has length five. Split the sample into complete periods, possibly none, and one remainder. The kernel weights of Section <a href="#sec:formula-choice" data-reference-type="ref" data-reference="sec:formula-choice">3.2</a> are nonnegative, so that remainder contributes no more than a whole period. Allowing one extra period supplies the error term after division by $`T`$ \[paper257, finite means for shifted divisor tails\]. The example refutes the claim of a complete sampled period, not the estimate.

<a id="correct-the-source-without-rewriting-its-history"></a>

## Correct the source without rewriting its history

The R6 \#1049 return attached a reader-motivation specimen from Knuth’s notes to §1, item 18. Inspection of the original places the passage in item 12, on printed page 3 (PDF page 5). Item 18 concerns a different matter. The public lesson record retains both the reported locator and the correction.

A search hit may be a table of contents, another occurrence or an adjacent column. Inspect the original passage, then correct the locator without crediting the earlier return with that correction. Useful prose can survive a citation repair; its usefulness does not excuse the error.

The same care applies to the role of the source. A paper may supply a theorem, historical attribution, established terminology or an example of composition. Those uses call for different claims. A paragraph about proof pacing does not validate the proof being paced. A literature specimen establishes that an author made a particular choice, not that this choice is universally preferable.

<a id="sec:practice"></a>

# Keeping a useful practice small

<div id="exposition-practice">

</div>

Revise with the two-page *Writing a Good Mathematical Paper* \[compact\]; use this companion for examples and limits. The writing skill \[skill\] and its records retain the detailed cases. Locate the present difficulty, use the relevant advice and leave successful passages alone. Rereading every past return is not a prerequisite.

<a id="sec:revision-order"></a>

## Revise in an order that preserves the argument

Start with the full statement, proof and closest prior results. State the contribution, decisive inference and boundary in a few sentences, then compare them with the abstract and introduction. Trace each advertised gain to the precise statement that supplies it. Preserve sufficient-only conditions, shared witnesses and fixed parameters under compression. Agreement between summaries does not help when all inherit the same overclaim.

Next mark the point where a reader must supply a consequential step. Write down what the preceding passage establishes and what the next passage needs. In the certificate case, the first supplies an error bound and the second needs containment in an open interval. The missing explanation is the comparison with both endpoint gaps, not more description of the computation. A nearby proof can suggest how to present that comparison.

Find the answer in the manuscript’s own argument. If it is established elsewhere, bring the relevant fact or a precise reference to this point. If it is not established, record a mathematical issue rather than insert “therefore”. When it is established, write the connecting sentence with its conditions. Then check whether it makes the inference or merely renames it: “the estimate is sufficient” still leaves the certificate’s two endpoint comparisons unexplained. The source models the explanation; the local proof supplies its warrant.

Review the revised paragraph with its predecessor and successor. Definitions must arrive before they are used, and the paragraph’s conclusion must supply what the next one needs. Read displayed formulas as parts of grammatical sentences, checking punctuation and the referent of each symbol. Conrad’s examples illustrate how unspecified variables and loose quantification can make ordinary-looking prose say the wrong thing \[conrad, §§1–2\]. A sentence-level pass is valuable after the dependency structure is sound; it cannot substitute for that earlier work.

Finally, remove repetition that performs no further work. Deriving a formula and showing how to apply it are different tasks. Test a cut by reading the remaining transition: would the reader now have to rediscover a parameter choice, hypothesis or inference? Keep that explanation; cut its duplicate. Stop when another change resolves no identifiable difficulty, improves no useful reading route and corrects no inaccuracy. This is a reason to preserve an effective passage, not a ban on substantial revision when the difficulty requires it.

<a id="sec:short-long"></a>

## Keep the short paper and long record useful separately

Before moving a passage, decide what each document must let its reader do. The short paper needs an intelligible proof of its principal result or a clearly labelled sketch with a precise full-proof destination. The long record must preserve the omitted derivation, assumptions and role in the argument. A “details” link is insufficient when its destination proves a different statement or skips the difficult step.

Compare the shared assertions in both directions. A repaired endpoint in the short paper must reach the long proof; an assumption exposed in the long proof must reach the short statement. After a move, follow the link to the actual passage. Match its hypotheses to the claim, and its notation to the short paper’s quantities; a correct proof of a nearby statement is not the missing proof. Retain alternatives and counterexamples that explain scope or a failed method. Material that serves only the revision history can remain in the editorial record rather than interrupting the mathematical argument.

<a id="put-verification-details-where-they-can-be-checked"></a>

## Put verification details where they can be checked

The mathematical argument should state its hypotheses and explain the inference. An exact computation may be part of that inference; give its mathematical input, output and finite scope at the point of use. Put the software version, source identifiers, replay commands and review history in one verification and reproducibility section or appendix. Refer there from a theorem when its evidence class matters. This keeps proof status available without making a reader decode repository machinery between proof steps.

State shared limitations once, repeating a condition wherever its omission would make a dependent claim read unconditionally. Editorial disclaimers need not follow every equation. Cite an external result where it is used; locate an omitted proof by section or theorem, not merely by filename or “long record”.

<a id="how-the-practice-developed"></a>

## How the practice developed

The practice developed by comparing proposed revisions with the arguments they were meant to explain. The proposals were not a consistent programme. Earlier \#243 reviews recommended a cubic result and a bounded negative result as the lead at different stages. The useful lesson was to choose the contribution that gives the current paper a coherent argument, not to preserve a permanent ranking of result types.

Integration also distinguished delivery from acceptance. In the later second round, only one of nine candidates was accepted although the returns had passed transport checks. Third-round integration restored seventeen named-input remarks removed during compression. Intact files did not ensure that a revision preserved the mathematics or credit. Comparing short and long versions also recovered omitted detail, as in the \#251 buffer-coordinate case.

Later returns made source models and before-and-after passages more explicit. The finite-remainder explanation survived review; a Knuth locator required correction; a broad author–reader analogy did not justify a particular rule about estimates. The records retain those different outcomes rather than counting every proposal as progress.

The nine R11 returns received editorial acceptance; accepted R12 revisions refine existing advice, not nine new instructions. The \#269 case separates a short interval from one excluding an integer; the systems case separates a recorded rationale from its adequacy \[systems-r12\]. These dispositions record editorial acceptance, not reader benefit. Later criticism must be checked against the current source: an earlier defect may already be repaired.

<a id="from-one-case-to-a-bounded-amendment"></a>

## From one case to a bounded amendment

Most accepted changes should become examples of existing guidance. Before adding a rule, try the existing instruction on the case: what decision does it fail to settle? Add only that missing distinction, with its circumstance, action, evidence and limit. A page-one request can become a reminder to remove unnecessary delay without becoming a page-one quota. A failed proof can become an explanation of a missing hypothesis without becoming a claim that every alternative approach is impossible.

An edit summary without the accepted words establishes neither verbatim acceptance nor rejection. Keep the proposal, source and decision for later inspection; do not resolve the correspondence by assumption. Nor does including a source claim a review of all its mathematics.

For a failure, record the attempted implication, assumptions, witness and missing information. A failed estimate does not refute the theorem; an unrun check is not a failed one. An unavailable source limits review, not the truth of its claim. Preserve what the failed route actually ruled out.

<a id="keep-a-revision-recoverable"></a>

## Keep a revision recoverable

Keep the manuscript, the guidance used and the source passages needed for review at identified versions. A manifest of paths and byte digests identifies the supplied files; it does not establish which passages anyone read. Retain the proposed words, their reason and limit, and the decision reached against the current argument. In a cumulative revision, check each earlier improvement against the new wording: an intact archive preserves history, not necessarily the improvement in the manuscript.

A later correction to a citation or proof does not become an achievement of the earlier return. Preserve both versions rather than silently replacing its history. Adopt a general lesson only through a separate review of its scope. This is revision of documents and guidance, not training of model weights.

<a id="read-the-page-that-will-be-read"></a>

## Read the page that will be read

Render the sources that will be delivered, recording the toolchain used. After changing a figure, inspect it at the size in which it appears. Follow a reference to the intended theorem or long-form argument, rather than merely checking that a target file exists. After reflow, inspect the affected pages and their neighbours: a useful explanation can be separated from its figure, or a small heading can be stranded above a page break. Bibliographic labels, captions, interval endpoints and cross-document links belong to this review.

Read the result along three routes. First, scan the title, abstract, introduction and main statements: recover the contribution and its boundary without importing private knowledge. Second, reconstruct the proof: identify where each hypothesis is used and explain the difficult inference in your own words. Third, try to use a result: check its assumptions on an example, identify an excluded case where known, and find the cited input needed for an application.

Ask a question that requires using the explanation. In Section <a href="#sec:certificate" data-reference-type="ref" data-reference="sec:certificate">3.1</a>, why are there two inequalities, and can a failed test become successful without changing $`D`$? The target is $`(1/2,1)`$; each inequality protects an endpoint. For $`D=3/4`$, replacing the enclosure $`[1/2,1]`$ by a sharper one can change the verdict without changing the value. The reader must distinguish value from enclosure, not merely repeat “compare both endpoints”. A difficulty with that task identifies a passage to revisit, not a numerical score for understanding.

Ask an independent reader where reconstruction stopped and what seemed established. An author’s cold-start pass is useful self-review; describing this procedure does not imply that an independent reader took part.

The checks answer limited questions. A successful build establishes that the source rendered under the recorded toolchain. A passage comparison helps establish what changed. A source inspection supports a citation’s locator and role. Neither those checks nor a lower rate of phrases flagged by a style detector establishes improved comprehension. A reported style comparison must identify the versions, prose denominator and genre, and retain regressions alongside gains. A claim of improved comprehension would require evidence from readers performing a specified task on identified versions, with the comparison and its limitations recorded.

The immediate editorial test is whether the revision exposes a warranted relation and the record identifies what changed and was accepted. That test can favour a longer explanation in one proof and a shorter one in another; measured reader benefit remains a separate question.

<a id="sec:genre-transfer"></a>

# Transfer the method across research genres

A theorem needs a proof under its stated hypotheses. For a system, distinguish what is proposed, implemented and tested. A performance claim needs the implementation, workload, comparator and observed result; an artefact build does not establish unrestricted performance or usability.

Levin and Redell distinguish implemented, proposed and theoretical systems: evaluation criteria depend on the paper’s class \[levin-redell\]. SIGPLAN’s empirical-evaluation checklist aids judgement; it is not a universal score \[sigplan-evaluation\]. Read a nearby system’s opening and evaluation, then trace the target task: what each component receives, changes and passes on, and who reviews it. A component list leaves those relations unexplained. These sources guide presentation; they do not verify a particular system.

The 6 October systems revision makes the task concrete before listing record fields \[systems-current, §§1,3; Appendix B\]. Its hypothetical editor announces a solution to \#257 while the unchanged theorem still restricts the exponent set. A successful proof check would not justify that introduction. One record links a paper statement to formal supports; another links explanatory prose to sources. The reviewer must compare the proposed passage with those sources. This example motivates the design; it is not an observed trial. The exact mathematical condition remains recoverable in the case’s own paper and the systems appendix; the introduction need not reproduce its derivation.

A fair comparison names the closest corresponding object, not just a common aim. Prove2Me separates immutable theorem statements from submitted proofs and fixes a human-audited mission core. Its milestones link source statements to attested formalisations \[prove2me, §§3–4\]. The R12 systems revision compares a milestone with its coverage record, which follows a particular paper occurrence and lists the registered formal supports. Listing supports does not compose their proofs. A separate record binds explanatory prose to sources \[systems-r12, related work\]. This difference of focus establishes neither exclusivity, priority nor an advantage of repository hosting over a service.

Keep the operations distinct: builders regenerate views; release checks test consistency. The passage checker requires matching text and source digests and a nonempty rationale, not an adequate rationale \[systems-current, §3.2; Appendix A\].

The repository’s systems manuscript gives a concrete example. It reports nine rejections among ten deliberately false, author-selected edits in a historical trial. After one edit escaped, a follow-up checked the intact baseline and that escaped edit against a repair; the other nine edits were not rerun \[systems, recorded observations\]. The first report describes those ten trials, not a general $`90\%`$ reliability rate. The second describes the tested repair, not a post-repair ten-out-of-ten result. The manuscript also records missing original logs and the absence of an independent comparison. A repair that catches one escaped edit has passed that regression check; its effects on unrerun cases remain unmeasured.

In a scientific exposition, identify the study or derivation, the population or model, the reported result and the author’s synthesis. State when there is no new experiment. Check each inference against the primary study: an association is not automatically causation, and a model prediction is not an observation.

Keep the condition and comparator beside each empirical claim. The two reports above concern different trials; a distant limitation cannot undo a sentence that combines them. Use parallel clauses to make their different scopes visible.

<a id="acknowledgement"></a>

# Acknowledgement

Wouter van Doorn’s feedback on first-reader legibility, recorded in the project’s writing guidance, helped sharpen the attention to private terminology, unnecessary notation and restrictive hypotheses. This acknowledges advice on exposition; it does not attribute mathematical verification or endorsement to him.

<a id="availability-and-authorship"></a>

# Availability and authorship

The writing skill, source records, lesson history and this paper’s LaTeX source are maintained in the public repository \[ledger; skill\]. The accompanying editorial return documents the new-return examples separately from the accepted historical cases. The public writing method and its review ledger record selected guidance, with source-reading and acceptance boundaries preserved. The worked revisions were made across papers on eight Erdős problems. Some agents worked from frozen packets; others integrated changes against the live repository. Their editorial judgements do not measure how independent mathematical readers understood the papers. The method has not been tested for improved reader comprehension. Will Cook built and directed the research infrastructure and reviewed the claims when he could. AI agents did most of the research and drafting. Cook did not independently verify every claim.

<div class="thebibliography">

99 P. R. Halmos, How to write mathematics, *L’Enseignement Mathématique* (2) **16** (1970), 123–152. Cited edition: the scanned article, §§3–4. <https://doi.org/10.5169/seals-43857>.

D. E. Knuth, T. Larrabee and P. M. Roberts, *Mathematical Writing*, Stanford Computer Science report STAN-CS-88-1193 (1988), notes from the 1987 course; book edition, Mathematical Association of America, 1989. Locators here refer to §§1–3 of the report; the worked exercise and proof comparison are on printed pp. 7–8 (PDF pp. 9–10). <https://cs.stanford.edu/~knuth/klr.html>.

T. Gowers, My favourite pedagogical principle: examples first, 19 October 2007, author’s essay. <https://gowers.wordpress.com/2007/10/19/my-favourite-pedagogical-principle-examples-first/>.

T. Tao, Don’t overoptimise, author’s writing advice, source snapshot inspected 30 September 2026. <https://terrytao.wordpress.com/advice-on-writing-papers/dont-overoptimise/>.

T. Crmarić and V. Kovač, On the irrationality of certain super-polynomially decaying series, arXiv:2504.18712v1 (25 April 2025). Cited passage: Lemma 4(a), pp. 4–5. <https://arxiv.org/abs/2504.18712v1>.

J. Hančl and R. Tijdeman, On the irrationality of Cantor and Ahmes series, *Publicationes Mathematicae Debrecen* **65**, no. 3–4 (2004), 371–380. <https://doi.org/10.5486/PMD.2004.3254>.

Y. Wang and B.-X. Zhu, Log-convex and Stieltjes moment sequences, *Advances in Applied Mathematics* **81** (2016), 115–127. Cited source: arXiv:1612.04114v1, §1, pp. 2–3. <https://arxiv.org/abs/1612.04114v1>.

W. Cook, [Literature and reviewed-revision guide](https://github.com/wcook04/plectis-erdos/tree/main/docs/papers/exposition-method), with lesson, history, return and source records, 30 September 2026.

W. Cook, [Public mathematical writing](https://github.com/wcook04/plectis-erdos/blob/main/skills/public-mathematical-writing/SKILL.md), repository skill.

W. Cook, [Writing a Good Mathematical Paper](https://github.com/wcook04/plectis-erdos/blob/main/paper/exposition/writing-a-good-mathematical-paper.pdf), compact guide, 1 October 2026.

W. Cook, [Publishing Mathematical Results from a Lean Repository](https://github.com/wcook04/plectis-erdos/blob/main/paper/systems/claim-faithful-publication-systems-paper.tex), 30 September 2026. T. Gowers, Examples first II, 24 October 2007, author’s follow-up essay. <https://gowers.wordpress.com/2007/10/24/examples-first-ii/>.

T. Tao, Give appropriate amounts of detail, author’s writing advice, inspected 30 September 2026. <https://terrytao.wordpress.com/advice-on-writing-papers/give-appropriate-amounts-of-detail/>.

T. Tao, Use good notation, author’s writing advice, inspected 30 September 2026. <https://terrytao.wordpress.com/advice-on-writing-papers/use-good-notation/>.

K. Conrad, Advice on Mathematical Writing, author’s ten-page handout, §§1–2, inspected 30 September 2026. <https://kconrad.math.uconn.edu/blurbs/proofs/writingtips.pdf>.

W. Cook, Integer Linear Forms for a Factorial Reciprocal Series, \#68 short paper, supplied source dated 30 September 2026. <https://github.com/wcook04/plectis-erdos/blob/main/paper/68/erdos-68-factorial-denominator-irrationality.tex>.

W. Cook, Reciprocal Sums and the Sylvester Recurrence, \#243 short paper, supplied source dated 30 September 2026. <https://github.com/wcook04/plectis-erdos/blob/main/paper/243/erdos-243-reciprocal-tail-rigidity.tex>.

W. Cook, Integral Relations among Totient Sections, \#249 short paper, supplied source dated 30 September 2026. <https://github.com/wcook04/plectis-erdos/blob/main/paper/249/erdos-249-binary-totient-series.tex>.

W. Cook, \#249 companion research record, supplied source dated 30 September 2026, comparison-sequence construction. <https://github.com/wcook04/plectis-erdos/blob/main/paper/249/erdos249-totient-reasoning-surface.tex>.

W. Cook, Sparse Congruence-Preserving Perturbations of Dyadic Series, \#251 short paper, supplied source dated 30 September 2026. <https://github.com/wcook04/plectis-erdos/blob/main/paper/251/erdos-251-prime-gap-dyadic-series.tex>.

W. Cook, Irrationality criteria for Lambert subseries, \#257 short paper, supplied source dated 30 September 2026. <https://github.com/wcook04/plectis-erdos/blob/main/paper/257/erdos-257-mersenne-support-subseries.tex>.

W. Cook, Distinct running least common multiples, \#269 short paper, manuscript snapshot, 1 October 2026. <https://github.com/wcook04/plectis-erdos/blob/main/paper/269/erdos-269-three-prime-running-lcm.tex>.

W. Cook, Paths in Polynomial Lemniscates: A Degree-Seven Counterexample and Radial Connections, \#1041 short paper, supplied source dated 30 September 2026. <https://github.com/wcook04/plectis-erdos/blob/main/paper/1041/erdos-1041-lemniscate-newton-flow.tex>.

W. Cook, Hankel Determinants of Geometric Moments and Rational Lambert Values, \#1049 short paper, supplied source dated 30 September 2026. <https://github.com/wcook04/plectis-erdos/blob/main/paper/1049/erdos-1049-rational-base-lambert.tex>.

R. Levin and D. D. Redell, How (and How Not) to Write a Good Systems Paper, *ACM SIGOPS Operating Systems Review* 17 (1983), 35–40; authorised copy hosted by USENIX. <https://www.usenix.org/guidelines-authors>.

ACM SIGPLAN, Empirical Evaluation Guidelines, committee guidance and FAQ (updated 2018; inspected 1 October 2026). <https://sigplan-www.sigplan.hosting.acm.org/Resources/EmpiricalEvaluation/>.

W. Cook, \#251 companion research record, R11 manuscript snapshot supplied 4 October 2026, comparison construction and sparse perturbations. <https://github.com/wcook04/plectis-erdos/blob/main/paper/251/erdos251-prime-gap-reasoning-surface.tex>.

S. Chen, K. Marwaha, X. Lu, H. Yuen and T. Peng, *Prove2Me: An Open Collaborative Platform for Scaling Math Formalization*, arXiv:2608.28433v2, 31 August 2026. Cited passages: §§3–4. <https://arxiv.org/abs/2608.28433v2>.

W. Cook, *A Repository-Based System for Research and Publication*, 30 September 2026; R12 manuscript snapshot supplied 5 October 2026. <https://github.com/wcook04/plectis-erdos/blob/main/paper/systems/claim-faithful-publication-systems-paper.tex>.

W. Cook, *A Repository-Based System for Research and Publication*, source revision accepted 6 October 2026; publication gates pending. <https://github.com/wcook04/plectis-erdos/blob/main/paper/systems/claim-faithful-publication-systems-paper.tex>.

</div>

*Source inspection and reproducibility.* Historical mathematical examples retain their stated revision identities; the current-source review uses the 6 October 2026 packet. The new systems example uses that day’s accepted source revision, not the earlier R12 snapshot. The return identifies exact source bytes, inspected passages and decisions, separating earlier reading declarations from fresh inspection. Knuth’s proof comparison and Halmos’s audience and organisation advice were rechecked; the retained Prove2Me comparison uses version 2, §§3–4, without new reading credit. Repository links locate manuscript families, not immutable versions. Source availability does not imply full reading, and earlier acceptance does not accept this revision.
