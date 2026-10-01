<a id="writing-mathematics-from-reviewed-revisions"></a>

# Writing Mathematics from the Literature and Reviewed Revisions

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

A mathematical sentence can be easy to read and still conceal the inference that justifies it. This guide explains how to locate that difficulty, study a relevant passage in the literature and write an explanation warranted by the manuscript’s own proof. Worked cases connect finite choices to an attained sum, derive a certificate from its target interval and separate convergence of one summand from passage through an infinite sum. They also show how to make an example self-contained and distinguish a failed test from a negative conclusion. The cases come from recorded revisions of eight Erdős-problem papers, including proposals subsequently checked against the selected manuscript sources. We distinguish accepted revisions, proposed improvements and lessons that need a narrower scope; an example confers no new proof or release status. The compact companion collects the actions. This guide supplies their reasons, sources and limits, with a final pass through a paper’s contribution, proof and use. It documents editorial practice, not a controlled evaluation of reader understanding.

<a id="sec:reading"></a>

# Learning to explain a particular argument

<div id="exposition-reading">

</div>

Suppose a proof constructs a sequence by repeatedly choosing a digit. At every stage another choice is possible, but the intended conclusion concerns the sum of the infinite sequence. The reader needs to know what has happened to the unattained part of the target. Writing
``` math
r_n=x-S_n,\qquad 0\le r_n\le\varepsilon_n,\qquad
 \varepsilon_n\longrightarrow0
```
answers that question: the partial sums $`S_n`$ converge to $`x`$. The useful addition is the relation connecting finite choices to the conclusion. Changing “we repeat” to “we continue inductively” would leave the same question unanswered.

This example, developed in Section <a href="#sec:remainder" data-reference-type="ref" data-reference="sec:remainder">2.1</a>, suggests where to look for a useful model. Another paper that constructs an infinite sum through controlled finite remainders can show how to separate the choice from the limiting argument. It need not study the same sequence. Its relevance lies in an identifiable part of the proof, and the comparison ends where the arguments differ. The model contributes an expository choice; the new paper must supply its own mathematics.

General advice remains useful. Halmos discusses audience, organization and the selection of examples \[halmos, §§3–4\]. Knuth, Larrabee and Roberts discuss the introduction of symbols, the connection between sentences and the reader’s need to know why a step is being taken \[knuth, §1\]. Gowers examines the placement of examples relative to unfamiliar abstractions \[gowers\], while Tao cautions against sacrificing usefulness to excessive optimization of a paper \[tao\]. Such advice identifies questions to ask. A nearby mathematical argument shows how an author has answered them in a particular setting.

The examples come from revisions of papers on Erdős problems. They show how a particular mathematical difficulty led to a particular change of prose. Section <a href="#sec:practice" data-reference-type="ref" data-reference="sec:practice">5</a> records the review method and its limits.

The reader can start with the construction and estimate in Section <a href="#sec:revisions" data-reference-type="ref" data-reference="sec:revisions">2</a>, then follow the additional worked explanations in Section <a href="#sec:worked-explanations" data-reference-type="ref" data-reference="sec:worked-explanations">3</a>. Section <a href="#sec:review" data-reference-type="ref" data-reference="sec:review">4</a> concerns changes that can alter meaning; Section <a href="#sec:practice" data-reference-type="ref" data-reference="sec:practice">5</a> gives a revision procedure and explains how to retain its lessons.

<a id="choose-sources-by-the-work-the-prose-must-do"></a>

## Choose sources by the work the prose must do

Before collecting stylistic examples, identify the manuscript’s subject, genre and reader. An irrationality note may need a compact route from an assumed rational sum to a positive integer smaller than one. A geometric paper may need to explain which component is being measured and why a map preserves the quantity under discussion. A survey has to distinguish several viewpoints; a short theorem paper may need to develop just one. These differences affect terminology, notation and the amount of preparation a proof needs.

Specify the reader’s existing knowledge as carefully as the intended result. An expert in the subject may know a standard lemma and still need an explanation of an unfamiliar way of using it. A reader in a neighbouring subject may need the lemma stated and its relevance explained. Allocate detail accordingly: Tao’s advice on detail distinguishes the author’s familiarity with a step from what the intended audience can reasonably supply \[tao-detail\].

The introduction must also distinguish two questions. What does this paper add to the subject? How does its proof reach the result? The first calls for a comparison with relevant prior work. The second calls for a short account of the decisive inference and the obstacles it overcomes. A list of section titles answers neither. For a conditional theorem, explain the hypothesis’s restrictiveness: give an established example satisfying it, or say that finding such examples is the remaining problem. Do not let a useful reduction read as though its premise had already been proved.

Choose a small group of human-authored papers that addresses these needs. Include a paper close in subject for vocabulary and attribution, and, when useful, one close in proof structure for the explanation of a construction or estimate. A famous paper from a remote field can offer a comparison, but it cannot settle the conventions of the target field. Nor does frequent usage make a term appropriate when its definition differs from the object at hand.

Read the original passage in a named version. An abstract can establish the name used for an object; it seldom reveals the pacing of the proof. For that, read the argument around the sentence, including the statement it proves and the hypotheses it invokes. Record the section, theorem or equation label and page. Preprint versions can have different numbering from a published article, and a source archive may differ from the accompanying PDF. The file’s digest identifies the supplied bytes; a public link tells the reader where to seek the work. Neither should silently stand in for the other.

For a difficult passage, reconstruct the local argument before borrowing its presentation. Knuth, Larrabee and Roberts give a useful worked comparison \[knuth, §§2–3, pp. 7–8\]. Their example considers vectors $`c+kb`$ whose coordinates are nonincreasing for every nonnegative integer $`k`$. Fix the vectors $`c,b`$ and coordinates $`i<j`$. Rearranging the coordinate inequality gives
``` math
c_i-c_j\ge k(b_j-b_i)\qquad(k\ge0).
```
The left side is fixed. If $`b_j-b_i`$ were positive, the right side would grow without bound; hence $`b_j\le b_i`$. The source compares a proof choosing a particular $`k`$ for a contradiction with a direct proof using this dependence. Reading the two shows why the phrase “for arbitrarily large $`k`$” matters. It is not a reason to ban proof by contradiction elsewhere.

Now ask which fact in the target proof could make its own conclusion equally unavoidable. In the opening construction, that fact is a remainder bound tending to zero. When the target proof contains no such fact, the comparison has exposed a mathematical obligation; it has not supplied an explanation that can safely be inserted.

The record should distinguish three acts. A packet may contain a source. Its recipient may declare that particular pages were read. An integrating reviewer may later inspect the quoted passage. These are different facts. Later inspection can verify a locator or expose a poor analogy; it cannot establish what the earlier recipient actually read.

<a id="read-sentences-as-mathematical-relations"></a>

## Read sentences as mathematical relations

A useful reading pass asks what each choice allows the reader to infer. Consider the placement of a hypothesis. A theorem statement should quantify the objects and state the assumptions needed for its conclusion. Inside the proof, recalling one of those assumptions can explain a step that would otherwise look automatic. A phrase such as “by positivity” helps only if the reader can identify the positive quantity and the inference that uses it.

Connective words deserve the same attention. “Since” introduces a reason; “hence” asserts that the conclusion follows; “provided that” makes a condition visible; “it remains to prove” identifies unfinished work. These words are not interchangeable devices for varying a paragraph. A revision that changes “provided that” to “hence” can change the logical force of the sentence while leaving every displayed formula intact.

Parallel syntax helps compare parallel claims. A subordinate clause can keep a dependency beside the assertion that uses it. There is no preferred ratio of short to long sentences: a short sentence may hide its antecedent, while a longer one can keep a condition attached to its consequence. The point of studying an author’s construction is to understand that relation, then write original prose appropriate to the new argument.

Notation should receive this close reading as well. Ask when a symbol first becomes necessary, what repeated work it saves and which nearby quantities the reader might confuse with it. A new name for a standard object creates an additional translation. Conversely, removing an established term such as “Stieltjes moment sequence” can make a manuscript less connected to its literature \[wangzhu\]. A vocabulary pass should compare definitions and uses, rather than delete unfamiliar words merely because they are technical.

Proof pacing is the allocation of explanation to mathematical difficulty. The reader may need to see the accuracy required of an estimate before its derivation, or the obstruction that motivates a parameter choice. Several lines of routine substitution can be shorter than one indispensable sentence about why a limit exists. The manuscript should give the latter its space. These choices can be examined in actual passages, without imitating an author’s voice or turning a preferred cadence into a rule.

<a id="use-examples-without-delaying-the-result"></a>

## Use examples without delaying the result

An example earns its place when it prepares a particular inference. In the opening construction, a finite choice can illustrate how the remainder stays admissible; convergence still needs its own argument. In a classification, an example may reveal the coordinates, while the proof must still show that every admissible object has those coordinates. State which task the example performs so that its success is not mistaken for a proof of the whole result.

Placement depends on what is unfamiliar. Gowers’s follow-up to “examples first” qualifies the recommendation by audience and genre, and considers readers who approach a text nonlinearly \[gowers-followup\]. A brief example can precede a locally unfamiliar definition while the headline theorem remains early and easy to find. An example of a familiar definition may instead belong after the statement, at the point where it explains a new use.

This distinction also governs repetition. A second description can add meaning by connecting a formula to the operation it represents. Repeating the same conclusion in different adjectives adds little. Knuth, Larrabee and Roberts recommend complementary descriptions of important objects \[knuth, §1, item 11\]; complementarity is the test. After either description, the reader should be able to do something that the other alone made difficult.

<a id="sec:revisions"></a>

# Two revisions and the mathematics that permits them

<div id="exposition-revisions">

</div>

The following passages come from the short-paper revision round dated 30 September 2026 and labelled R6. This label is local to that series of packets; an earlier September series also used round numbers. The public lesson records retain the series, problem and source document so that the two histories cannot be confused. The accepted manuscript passages below are recoverable at repository commit `18cedaddedd1`, whose full identity and source digests appear in those records \[ledger\].

<a id="sec:remainder"></a>

## From repeated choice to an attained infinite sum

The \#251 paper contains a construction in which a target $`x`$ is represented by chosen digits $`d_j`$ and weights $`w_j`$. A finite remainder $`\rho_j`$ is kept between $`0`$ and a bound $`F_j`$. The old passage began:

> Given $`x\in[0,F_0]`$, we choose $`d_0`$ so that $`x-d_0w_0\in[0,F_1]`$ and repeat this choice for each successive remainder.

This describes the repeated choice. It leaves the reason for attainment less prominent than the construction. The reviewed addition states:

> The covering just proved makes this possible at every stage. The invariant $`0\le\rho_j\le F_j`$ and $`F_j\to0`$ then give

and continues with the limiting identity. The two sentences distinguish the finite covering argument from the passage to the infinite sum. The record is `r6-251-style_rules-04`; the full identifier carries the series date.

Crmarić and Kovač’s proof of Lemma 4(a), in the first version of their paper on sums of reciprocals, provides a close model \[crmaric, pp. 4–5\]. They control a finite remainder in an interval, then use convergence to obtain the represented value. This is more specific than an instruction to add intuition. It identifies two jobs in the proof and gives each a sentence.

The analogy has a definite boundary. For the \#251 manuscript, the covering property, the invariant and $`F_j\to0`$ must all hold for its own construction. A finite digit example proves none of them. Nor does attainment alone prove the sparsity or arithmetic constraints imposed elsewhere in the paper. The integrating decision preserved those separate obligations and the unresolved status of the original prime-gap problem. The transferable lesson concerns the exposition of an already justified limit, not permission to supply a missing convergence argument by analogy.

<a id="sec:estimate"></a>

## State how accurate the estimate must be

In the \#269 argument, a rationality assumption places normalized tails $`Y_a`$ in the finite set
``` math
(K^{-1}\mathbb Z)\cap(0,1).
```
Here $`K\ge1`$ is the integer denominator in the rationality assumption. An accepted sentence then says that equality of two tails still has to propagate. This matters: finiteness provides repetition, but a repeated value need not determine the subsequent choices. A separate recovery argument is needed before one concludes that blocks repeat.

Hančl and Tijdeman’s proof of Theorem 2.1 begins by turning a rationality assumption into an integral scaled remainder \[hancl, p. 373\]. That ordering makes the arithmetic object visible before estimating it. The \#269 revision uses the same explanatory idea while retaining its additional recovery problem. The cited proof does not establish that extra step.

The next difficulty is quantitative. The maps $`G_{53}(t)=(9+t)/30`$ and $`G_5(t)=(3+t)/10`$ encode two possible blocks of prime-power jumps. Their images overlap on the initial tail range $`[0,1]`$. The earlier paragraph observed the overlap and announced that the range would be narrowed. With the lower bound $`3/10`$ already established, the revised passage specifies the required accuracy first:

> With that lower endpoint, separating these two images requires an upper endpoint $`U`$ satisfying
> ``` math
> G_{53}(U)<G_5(3/10),\qquad
>  \frac{9+U}{30}<\frac{33}{100},\qquad U<\frac9{10}.
> ```
> This specifies the improvement needed from the arithmetic sequence.

The case is `r6-269-style_rules-03`. The inequality now explains what the following estimate is trying to achieve. It also makes a checkable distinction: this is the sufficient threshold used by the argument, not a claim that no other method could work with a different bound.

The return associated this choice with an item in Knuth’s notes about the author’s dialogue with the reader. That is a broad compositional analogy, not a source for the displayed threshold. The algebraic separation condition is the precise local reason for the new sentence. Keeping the two explanations separate prevents the general writing reference from appearing to support mathematics it does not discuss.

<a id="an-example-must-reveal-the-relevant-difference"></a>

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

The multiplicities $`4`$ and $`2`$ are the information lost by replacing repeated heights with distinct ones. This table explains a choice of counting convention; its purpose is not to decorate the definition. The associated record, `r6-269-style_rules-04`, also preserves an endpoint warning: the distinct-height argument uses $`(16,32]`$, whereas this table uses $`[16,32)`$. The writer must explain that change rather than identify the two intervals silently.

Halmos’s discussion of concrete cases and Gowers’s discussion of examples suggest asking whether an instance can reveal the unfamiliar operation before its notation accumulates \[halmos, §4\]\[gowers\]. The usefulness of this particular instance is more narrowly demonstrated: one can see the lost multiplicity in the table. It does not establish the infinite-series theorem or show that every reader would prefer this placement.

<a id="sec:worked-explanations"></a>

# From a formula to the sentence that explains it

Eight additional editorial returns supplied these cases (the \#1049 return is labelled R9). They were proposals when supplied. The explanations below were checked against the current manuscript sources; that check does not by itself establish a new theorem, formal coverage or release status. We group them by the reader’s question rather than by the order of the returns.

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
Each inequality now has a visible job. The factor $`2`$ in the first one comes from the lower endpoint $`1/2`$; it is not an unexplained safety factor. Strictness also has a purpose: the boundary values give $`sD'=-1`$ or $`0`$.

The explanation also tells us what failure means. Take $`D=3/4`$, $`s=1`$, $`Q=4`$, $`A=3`$ and $`B=1`$. The error bound is valid, but its enclosure $`[1/2,1]`$ fails both strict endpoint tests, even though $`D`$ lies in the target interval. Passing certifies membership; failure of this enclosure to fit does not certify nonmembership. This example interprets the existing certificate without changing it.

The \#68 remainder has a related, one-sided geometry. It is $`A_N+M(S-H_N)`$, where $`S`$ is the series sum, $`H_N`$ its $`N`$th partial sum, and $`M>0`$ scales the strictly positive omitted tail. To put this remainder between consecutive integers, it suffices to prove
``` math
0<M(S-H_N)<\lfloor A_N\rfloor+1-A_N.
```
The left inequality puts the remainder above $`\lfloor A_N\rfloor`$; the right puts it below $`\lfloor A_N\rfloor+1`$ \[paper68, section on nonintegrality\]. An upper bound for the tail becomes a test only after this gap is identified. At an integral $`A_N`$ the gap is $`1`$. Replacing the strict successor by $`\lceil A_N\rceil`$ would make it zero. The endpoint distinguishes two superficially interchangeable conventions.

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
This is the weight of the future positions at which $`d`$ divides the index. It explains the kernel before the averaging machinery is introduced \[paper257, finite means for shifted divisor tails\]. When $`d\mid N`$, the first positive offset is $`d`$, so the same formula applies without adding an unwanted offset zero. In that paper $`B=2^\alpha`$, with $`0<\alpha\le1`$; estimates must retain their dependence on $`B-1`$ as $`\alpha`$ becomes small.

The two examples make a formula intelligible by deriving it from the operation already being performed. Tao’s discussion of notation recommends making important parameters visible and translating borrowed notation at its use \[tao-notation\]. Here the support restriction and the divisibility condition provide the local reasons. The exposition should give those reasons before asking the reader to remember another named quantity.

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
The original product has $`N-\ell`$ factors; each endpoint product has the fixed length $`\mu_j`$. Thus every factor in the numerator tends to $`1`$, while the denominator is fixed and positive. The remaining factors have $`j,k\le\ell`$ and are independent of $`N`$. This establishes convergence of the whole quotient for a fixed partition, including its growing part. The formula is the telescoping explanation proposed in the later return; its algebra does not invoke a new asymptotic theorem.

There is still a second question: can the limit be passed through the sum over all partitions? Extend the summand by zero when $`\ell>N`$, so that the index set is fixed. The source proof supplies a bound, independent of $`N`$, whose total over partitions of length $`\ell`$ is at most
``` math
K^\ell q^{\ell^2},
```
where $`K>0`$ may depend on the fixed base and the fixed weight-bound constants. The ratio of successive terms is $`Kq^{2\ell+1}\to0`$, so this bound is summable over $`\ell`$. It controls both large parts and large lengths, and hence permits dominated convergence. A bound for each individual partition would not do that work.

The improved explanation therefore has two conclusions, in this order: the whole summand converges for a fixed partition, and a summable bound controls all partitions uniformly in $`N`$. Neither conclusion asserts uniformity as $`q\uparrow1`$. Keeping the base fixed is part of the statement, not a temporary convenience that prose may suppress.

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
Exponential growth of $`2^L`$ exceeds the linear growth of $`B_L`$, so such a depth exists. This converse is stronger than a merely sufficient test.

Completeness of positive detection does not give a stopping certificate for integrality: when $`D`$ is integral, this search never succeeds. Failure at the depths tried is therefore not, by itself, a proof of integrality. A second distinction concerns the irrationality argument. For every positive shift and every cutoff it still needs an index beyond that cutoff with a nonintegral difference. The test recognises a suitable fixed value; it has not produced this family. Its exact converse and the remaining quantifiers both belong in the explanation.

Whenever a proof offers arbitrarily accurate certificates, state which object stays fixed as the accuracy improves. If the object changes too, its distance from the forbidden set may shrink, and a new comparison is needed. This is the same discipline that made the fixed-base limit in Section <a href="#sec:fixed-partition" data-reference-type="ref" data-reference="sec:fixed-partition">3.3</a> readable.

<a id="sec:review"></a>

# What the integrating reviewer must decide

<div id="exposition-review">

</div>

A proposed revision has several possible fates. It can be accepted verbatim, accepted after a mathematical or expository repair, rejected, or left pending a named check. Its lesson may already be expressed in the writing guidance. These decisions should not be collapsed into a single “accepted” label. The revision of a paragraph and the adoption of a general rule are different acts, as are admission of a returned archive and acceptance of the mathematics inside it.

The reviewer begins with the current statement and proof. For a substantive change, the record retains the old passage, the proposed passage, the source of the proposal and the decision actually made in the canonical manuscript. A digest identifies the source bytes; a commit, path and label identify the accepted passage. An exact text match, after whitespace normalization, can help locate it. Such a match does not establish equivalence of two theorem statements or prove that a general recommendation is sound.

<a id="replace-a-local-term-without-losing-its-definition"></a>

## Replace a local term without losing its definition

The next short-paper round, R7, provides a direct example of terminology review. In the \#249 record, a local growth adjective was replaced by the condition it denoted:

> *Before:* tempered integer carry orbit.
>
> *Selected revision:* integer carry sequence $`u`$ with $`u(N)/2^N\to0`$.

The gain is specific. A reader no longer has to recover a private definition to know the required rate. It would be incorrect to replace this condition by the more familiar phrase “subexponential growth”, which says something stronger. Other revisions retained standard terms such as upper Banach density because those terms denote the properties the paper actually uses. The rule is to compare meanings, not to replace every unusual expression.

Removing a shorthand can also remove the visible source of its assumptions. In \#243, “positive exact state” bundled recurrence and positivity conditions. A proposed replacement referred to the same assumptions after that definition had disappeared. The integrating reviewer instead stated the recurrences for the first implication, then explicitly added natural-number domains and $`a_n>1`$, $`C_n>0`$ for the eventual consequence. In a second passage, the reviewer removed “earlier” from “earlier decreases”: the original qualification did not restrict the time at which decreases could occur.

The R7 lesson records distinguish these reviewed selections from the donor’s proposal and from later rendering or formal correspondence checks. These cases show why terminology, grammar and quantification belong in the same review. A plainer noun is useful only if the sentence still makes the same claim.

<a id="rejecting-an-attractive-universal-rule"></a>

## Rejecting an attractive universal rule

Earlier reviews of the \#243 manuscript illustrate why historical advice needs its original setting. One round asked for a cubic irrationality example near the beginning. A subsequent round explicitly retained the live bounded-negative result as the paper’s lead and rejected an invariant rule that an irrationality result must always come first. Later editorial routes treated page targets as subordinate to the proof’s dependencies.

The retained lesson is to choose a coherent principal contribution and explain its relation to the named problem. It does not prescribe a theorem category or a fixed page on which every proof must finish. A conditional reduction can be the useful result; an unconditional statement can be too weak to carry the paper. The choice requires comparing what the results actually say. The history record preserves the successive recommendations instead of combining them into contradictory commands.

This distinction also protects the longer research record. Shortening a paper can be appropriate when the subordinate details have a complete, checked destination. Regenerating the long record from the shortened version would lose the very argument that made the shorter presentation possible. The two documents must be compared in both directions: a stronger hypothesis, a repaired endpoint or a newly explained limiting step may appear first in either one.

<a id="distinguish-clarification-from-a-proof-repair"></a>

## Distinguish clarification from a proof repair

An earlier \#251 review identified a defect in the manuscript’s condensed account of a sparse construction: a buffer quantity was used without being assigned a sequence coordinate and included in the value, size and capacity accounting. The original returned memorandum did include those coordinates and their contribution to the weighted sum. The accepted ordinary repair assigned the relevant coordinates and performed the accounting across all indices. Calling the original paragraph unclear would have understated the issue. The condensed proof needed repair before the account of it could be trusted. Here the recoverable original prevented a loss during shortening or integration from being attributed to the original construction. This is a historical mathematical repair, undertaken in its own review. A current exposition-only assignment should locate such a defect and refer it for a separately authorised proof review. It should not silently add the missing mathematics.

That decision must be distinguished from a later sharp companion construction which remained unreviewed at its recorded disposition. The presence of both in a returned bundle does not give them the same status. A usable history names the particular construction, the defect and the accepted replacement; it does not summarize the whole problem’s sequence of returns as progress through increasingly strong theorems.

Other cases expose similar changes of meaning in small amounts of prose. In \#1049, language suggesting that a degree bound was inevitable was repaired to state a sufficient inequality and preserve the qualification contributed by a remaining factor. In \#1041, the revision retained the fixed-polynomial scope instead of turning it into a freely varying family. For mixed irrationality criteria in \#257, independently chosen witnesses cannot replace the common witness required by the argument. These are local mathematical checks, even when the proposed edit was presented as compression or style.

An ordinary proof and its formal support also require separate decisions. An accepted ordinary argument need not already have a complete Lean formalization. Conversely, a checked lemma nearby does not check every sentence in a new proof. Review should identify the exact statement supported by each kind of evidence, leaving named inputs and pending comparisons visible. The publication system’s broader evidence responsibilities are described separately \[systems\]; the writing method uses those distinctions rather than creating another proof registry.

A late-September integration supplies a concrete limit on deleting operational language. A prose pass had removed remarks that identified named mathematical inputs beside the results depending on them. The integrating agent restored those remarks. Routine details about running a check could recede, but the reader still needed to know which assertion depended on an input. Calling both kinds of sentence workflow commentary had erased a substantive qualification.

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

Even prose that seems to paraphrase a bound deserves this review. In the \#257 finite average, $`L,d,T`$ are positive integers. The residues of $`L,2L,3L,\ldots`$ modulo $`d`$ repeat with period $`d/\gcd(L,d)`$; the sample uses only the first $`T`$ terms. The inequality $`d\le LT`$ does not assert that one whole period occurs. For $`L=3,d=5,T=2`$, it holds while the period has length five. Splitting the sample into complete periods, possibly none, and one remainder is sufficient for the displayed bound \[paper257, finite means for shifted divisor tails\]. Adding the two words “possibly none” corrects a gloss while leaving the estimate unchanged. This is different from a proof whose estimate itself fails. That distinction belongs in the review decision.

<a id="correct-the-source-without-rewriting-its-history"></a>

## Correct the source without rewriting its history

The R6 \#1049 return attached a reader-motivation specimen from Knuth’s notes to §1, item 18. Inspection of the original places the passage in item 12, on printed page 3 (PDF page 5). Item 18 concerns a different matter. The public lesson record retains both the reported locator and the correction.

This small example explains why a plausible quotation and a plausible page number are insufficient. A phrase search can find the table of contents, another occurrence of a common sentence, or text from an adjacent PDF column. The reviewer must inspect the intended passage in context. A corrected locator does not invalidate an otherwise useful revision, but the revision’s success does not excuse a false citation.

The same care applies to the role of the source. A paper may supply a theorem, historical attribution, established terminology or an example of composition. Those uses call for different claims. A paragraph about proof pacing does not validate the proof being paced. A literature specimen establishes that an author made a particular choice, not that this choice is universally preferable.

<a id="sec:practice"></a>

# Keeping a useful practice small

<div id="exposition-practice">

</div>

Use the two-page *Writing a Good Mathematical Paper* \[compact\] as a working guide; use this companion when a particular instruction needs an example or a limit. The repository’s writing skill \[skill\] incorporates the literature-reading pass, while its records retain the detailed cases and exceptions. A writer need not read every past return before explaining a proof. The next revision should resolve a specific difficulty, not demonstrate that every rule has been mentioned.

<a id="sec:revision-order"></a>

## Revise in an order that preserves the argument

Begin with the full statement, proof and closest prior results. Write a brief account of the contribution, the decisive inference and the exact boundary. Check this account against the abstract and introduction. When a condition is only sufficient, a witness is shared, or a parameter is fixed, preserve that qualification in every compressed occurrence. Agreement among several summaries is not enough if all have inherited the same overstatement.

Next choose the passage where the intended reader must supply the most consequential missing explanation. Ask a concrete question: why this parameter, why this normalisation, why this error threshold, or why does this limit give the asserted object? Read a relevant local argument in an original source, then find the mathematical answer in the manuscript. Write the sentence that connects that answer to the next step. If the answer is absent, record the mathematical issue rather than concealing it with a connective.

Review the revised paragraph with its predecessor and successor. Definitions must arrive before they are used, and the paragraph’s conclusion must supply what the next one needs. Read displayed formulas as parts of grammatical sentences, checking punctuation and the referent of each symbol. Conrad’s examples illustrate how unspecified variables and loose quantification can make ordinary-looking prose say the wrong thing \[conrad, §§1–2\]. A sentence-level pass is valuable after the dependency structure is sound; it cannot substitute for that earlier work.

Finally, remove explanation that repeats an already intelligible operation. Keep a second account when it serves a different purpose, such as showing how to apply a formula after deriving it. Stop when another sentence would resolve no specific ambiguity, justify no missing transition and improve no useful route through the paper. This gives brevity a reader-facing purpose without imposing a page target.

<a id="sec:short-long"></a>

## Keep the short paper and long record useful separately

Before moving a passage, identify what a reader of each document must still be able to do. The short paper should support its principal result through an intelligible proof or a clearly identified proof sketch with a precise full-proof destination. A long record should preserve the omitted derivation, its assumptions and its relation to the main argument. A link labelled “details” is insufficient when its destination proves a different statement or omits the difficult step.

Compare the shared assertions in both directions. A repaired endpoint in the short paper must reach the long proof; an assumption exposed in the long proof must reach the short statement. After a move, follow the link to the actual passage and check that its notation can be translated. Retain substantial alternatives and counterexamples where they explain the scope or a failed method. Material that serves only the revision history can remain in the editorial record rather than interrupting the mathematical argument.

<a id="put-verification-details-where-they-can-be-checked"></a>

## Put verification details where they can be checked

The mathematical argument should state its hypotheses and explain the inference. An exact computation may be part of that inference; give its mathematical input, output and finite scope at the point of use. Put the software version, source identifiers, replay commands and review history in one verification and reproducibility section or appendix. Refer there from a theorem when its evidence class matters. This keeps proof status available without making a reader decode repository machinery between proof steps.

Give a single account of a shared limitation, then repeat it only when a different claim would otherwise appear unconditional. A conditional premise belongs beside the statement it conditions; an editorial disclaimer does not need to recur after every equation. For an omitted proof, name its mathematical destination by section or theorem and cite the original source where an external result is used. A reference to a file or a “long record” alone does not tell a reader which argument to inspect.

<a id="how-the-practice-developed"></a>

## How the practice developed

The recorded process began with reviewers proposing changes to particular papers: move the result forward, explain a construction, shorten a repetitive section or repair an unsupported implication. Successive returns did not form a single consistent programme. In the earlier \#243 reviews, a cubic result and a bounded negative result were each proposed as the lead at different stages. Comparing these requests with the manuscripts yielded a narrower instruction: choose the result that gives the current paper its most coherent argument. The historical request remains evidence about that draft, not a permanent ranking of result types.

Each returned manuscript then met a separate integration decision. In the later second round, only one of nine candidates was accepted, although the returns had passed transport checks. In the third round, integration included restoring seventeen named-input remarks removed during compression. These events exposed different questions: did the proposed files arrive intact, did the revision preserve the mathematics and credit, and did it explain the argument? A pass on the first question could not answer the others. Comparing short papers with their longer records also recovered useful material, as the \#251 buffer-coordinate case illustrates.

The recent rounds supplied more explicit literary models, before-and-after passages and proposed general lessons. We compared these with the selected native source, reopened the cited passages and retained repairs alongside acceptances. The finite-remainder explanation survived this review; a claimed Knuth locator needed correction; a broad author–reader analogy did not by itself justify a specific rule about estimates. The resulting instructions therefore combine mathematical checks with reading practice, while the records preserve the disagreements and limits that compression would hide.

This short/long pair is the next distillation of that sequence. The compact guide gives the writer actions; this companion explains why those actions are useful and when they are insufficient. A later packet can carry both at a fixed version, solicit another local revision and repeat the review. The systems paper \[systems\] describes the repository mechanisms supporting the process. Here the object of review is the editorial decision itself.

<a id="from-one-case-to-a-bounded-amendment"></a>

## From one case to a bounded amendment

Most accepted changes should become examples of existing guidance. Add a rule only when the case exposes a reusable distinction that the present instruction misses. State the circumstance in which it applies, the action to take, the evidence motivating it and a case in which it would fail. A page-one request can become a reminder to remove unnecessary delay without becoming a page-one quota. A failed proof can become an explanation of a missing hypothesis without becoming a claim that every alternative approach is impossible.

The public records separate recent proposals, historical requests, source identities and the manuscript decisions used to assess them. They retain unmatched and pending cases explicitly. A return may describe an edit in summary rather than supply the exact accepted words; this should be recorded as a correspondence still requiring inspection, not counted as either a rejected edit or a verbatim acceptance. Source passages are reviewed for their stated writing use. Inclusion in the source list does not assert a complete mathematical review of every cited paper.

The record of a failure should be equally specific. Preserve the attempted implication, its assumptions, the witness to failure and the information missing from the argument. Failure of one estimate does not refute the theorem. Failure to run a check says that the check is unrun. An unavailable source says something about the review’s evidence, not about the truth of the source’s claim. These distinctions prevent a later writer from giving a historical obstacle more force than it had.

<a id="what-the-next-packet-must-contain"></a>

## What the next packet must contain

A frozen review packet should include the exact skill and guide it asks the recipient to follow, the compact paper, the relevant lessons, the source identities and this companion paper. A manifest records their paths and byte digests. The packet must also carry the primary originals needed for its selected specimens, with versions and reading-status declarations kept separate. A title in a bibliography or a list of annex files is not a substitute for a source that the recipient can actually inspect.

The recipient can then compare those papers with the supplied manuscript: how does each introduce its object, make a hypothesis visible, motivate an estimate or credit an input? The return should identify the passage read, the feature adapted, the proposed local change and its limit. The repository agent reviews the proposal against the current mathematics, integrates an accepted change and amends the guidance only if the evidence warrants it. The next packet can consume that resulting version. This is a sequence of explicit document revisions, not training of model weights.

Freezing a version matters because guidance can change during a review. An earlier packet cannot have applied a later correction to Knuth’s locator, and a later integration should not attribute that correction to the original return. Keeping both versions makes the difference inspectable. The same principle applies to mathematical status: a later accepted ordinary proof does not turn an earlier unassessed proposal into an already checked result.

<a id="read-the-page-that-will-be-read"></a>

## Read the page that will be read

The final pass uses the repository’s native sources and rendering tools. After changing a figure, inspect it at the size in which it appears. Follow a reference to the intended theorem or long-form argument, rather than merely checking that a target file exists. After reflow, inspect the affected pages and their neighbours: a useful explanation can be separated from its figure, or a small heading can be stranded above a page break. Bibliographic labels, captions, interval endpoints and cross-document links belong to this review.

Read the result along three routes. First, scan the title, abstract, introduction and main statements: recover the contribution and its boundary without importing private knowledge. Second, reconstruct the proof: identify where each hypothesis is used and explain the difficult inference in your own words. Third, try to use a result: check its assumptions on an example, locate an excluded case and find the cited input needed for an application.

For the examples here, these tasks have specific answers. In Section <a href="#sec:certificate" data-reference-type="ref" data-reference="sec:certificate">3.1</a>, the certificate places a value in $`(1/2,1)`$; its two inequalities come from the two endpoint gaps; the value $`D=3/4`$ with the loose enclosure $`[1/2,1]`$ shows why a failed test is inconclusive. A reader who can repeat “compare both endpoints” but cannot explain that failure has not yet recovered how to use the certificate. This identifies a passage to revisit, not a numerical score for understanding.

When an independent reader is available, ask for the exact place where their reconstruction stopped and what they believed had been established there. An author’s own cold-start pass is still useful, but should be reported as self-review. No independent reader is implied by the procedure described here.

The checks answer limited questions. A successful build establishes that the source rendered under the recorded toolchain. A passage comparison helps establish what changed. A source inspection supports a citation’s locator and role. Neither those checks nor a lower rate of phrases flagged by a style detector establishes improved comprehension. A reported style comparison must identify the versions, prose denominator and genre, and retain regressions alongside gains. A claim of improved comprehension would require evidence from readers performing a specified task on identified versions, with the comparison and its limitations recorded.

The method leaves that empirical question open. It makes a particular editorial decision inspectable: a source suggests an explanatory choice, the local mathematics warrants the new sentence, and the review records its fate. The practical standard remains the reader’s ability to recover the argument. A different proof may warrant a different choice.

<a id="sec:genre-transfer"></a>

# Transfer the method across research genres

The common task is to make the relation between a claim and its warrant legible. What counts as a warrant depends on the field and the sentence. For a mathematical theorem, state the domain and hypotheses, then explain the proof’s hard implication. A systems paper may describe a design, report an implemented mechanism or compare performance under a workload. Identify which of these is being claimed. An empirical comparison needs the tested implementation, conditions, comparator and observed result; a proposed design must not be presented as an implemented one. A build or artifact check concerns the tested objects, not unrestricted performance or usability.

Levin and Redell distinguish papers about implemented systems, proposed systems and theoretical work, and caution that evaluation criteria vary across those classes \[levin-redell\]. The SIGPLAN empirical-evaluation guidance asks authors to state claims and limitations clearly, and treats its checklist as an aid to judgment rather than a universal score \[sigplan-evaluation\]. These are genre-specific primary sources, not proof authority for any particular system. A nearby systems paper’s opening and evaluation should also be read at their actual passages before transferring a sentence pattern.

The repository’s systems manuscript gives a concrete example. It reports nine rejections among ten deliberately false, author-selected edits in a historical trial. After one edit escaped, a follow-up checked the intact baseline and that escaped edit against a repair; the other nine edits were not rerun \[systems, recorded observations\]. The first report describes those ten trials, not a general $`90\%`$ reliability rate. The second describes the tested repair, not a post-repair ten-out-of-ten result. The manuscript also records missing original logs and the absence of an independent comparison. Those qualifications determine which conclusion the observations can support; they are not incidental implementation details.

In an expository scientific paper, similarly identify the underlying study or derivation, the population or model, the observed or cited result, and the author’s synthesis. If the paper contributes no new experiment, say so. Compare each inference with the cited primary study and with nearby expositions in that field; do not turn a reported association into causation or a model’s prediction into an observation.

Sentence structure should expose these dependencies. Put the condition before its consequence when the condition controls the claim; name the measured quantity and comparator in the same sentence as the reported change; keep parallel outcomes in parallel clauses. The value of this practice is local: it lets a reader test exactly which evidence licenses each statement. It is not a single prose template for mathematics, systems research and every science.

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

</div>

*Source inspection and reproducibility.* This revision additionally reads §§2–3 of Knuth et al., printed pp. 7–8 (PDF pp. 9–10), beyond the §1 passages used previously. Worked examples were checked against manuscript sources frozen in the 1 October 2026 packet; snapshot and title-page dates may differ. Historical cases retain their stated revision identities. Repository links locate manuscript families; the review record identifies the inspected versions, passages and integration decisions.
