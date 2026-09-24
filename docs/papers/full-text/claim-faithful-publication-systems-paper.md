<a id="claim-faithful-publication-systems-paper"></a>

# Problem-Sized Lean Worlds

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

A proof becomes usable by other mathematicians when it arrives with an exact statement, an explanation of its hard step, its relation to earlier work and a precise account of what remains open. This paper describes a research environment organised around a persistent unit of work, the problem-sized world: the files in a public Git repository that keep one research problem together with its results, failed routes, experiments, literature and exact open obligations. A short paper explains the strongest results to an expert, a long record keeps the complete arguments, Lean checks the formal proofs and Comparator checks selected ones against separately written statements, and a claim registry fixes the wording, evidence class and limits of every public claim. Any model, provider or person can resume from the record, and accepted work returns to it with credit. A public Lean repository maintains eight Erdős problems this way. Its results include an irrationality criterion for Problem 257, checked in Lean and by Comparator, that admits supports with divergent reciprocal sum, and a formal refutation of the Formal Conjectures statement of Problem 1041, built on a counterexample posted by the forum contributor `ani`; Google DeepMind’s Formal Conjectures now records the answer as `False` and links the proof. Worked cases from Problems 257 and 249 and from a cross-problem synthesis show what the record keeps for a result. The paper compares the design with Prove2Me and blueprint-based systems and specifies the controlled comparison that will measure whether such records reduce the work of understanding, checking and continuing a result.

<div class="center">

<div class="minipage">

------------------------------------------------------------------------

**Contribution and scope**

**Design.** The problem-sized world as the persistent unit of AI-assisted research; four separately recorded decisions about every returned result, on its evidence, its mathematical appraisal, its exposition and the next unit of work; a path from proof to public claim that separates what Lean settles, what Comparator settles and what a mathematician judges; and a contribution cycle that a person or an agent can run from a public clone. **Instance.** Eight Erdős problems in one Lean repository: sixteen problem papers totalling 773 pages, 1,823 Lean modules, and 674 results asserted in the papers, short and long versions counted separately, of which 671 carry a Lean declaration and 633 have been compared by Comparator. **Scope.** For Problem 1041 the Formal Conjectures statement is refuted; independent human review of its correspondence with the 1958 wording has not been recorded. The other seven targets remain open. The system leaves novelty and significance to experts.

</div>

</div>

<a id="sec:intro"></a>

# A theorem and the explanation it needs

Problem 257 asks whether $`\sum_{a\in A}(2^a-1)^{-1}`$ is irrational for every infinite set $`A`$ of positive integers \[erdosproblems\]. For an integer $`b\ge2`$ write $`X_A(b)=\sum_{a\in A}(b^a-1)^{-1}`$, fix a finite nonempty set $`P`$ of primes, and let $`h(a)=\prod_{p\in P}p^{v_p(a)}`$ be the $`P`$-part of $`a`$, where $`v_p(a)`$ is the exponent of $`p`$ in $`a`$. The Problem 257 short paper \[paper257\] proves that
``` math
\sum_{a\in A}\frac{h(a)}{a\,(2^{h(a)}-1)}<\infty
```
makes $`X_B(b)`$ irrational for every integer $`b\ge2`$ and every infinite $`B\subseteq A`$. Lean proves the criterion, and Comparator has checked that proof against the separately written statement (Section <a href="#sec:checks" data-reference-type="ref" data-reference="sec:checks">4</a>).

The criterion reaches past reciprocal summability. Let
``` math
A_\star=\{2^km:\ k\ge1,\ m\text{ odd},\ m\le2^{2^k}\}.
```
The $`k`$th layer of $`A_\star`$ has reciprocal mass at least $`1/4`$, so $`\sum_{a\in A_\star}1/a`$ diverges, while for $`P=\{2\}`$ an element $`2^km`$ contributes $`1/[m(2^{2^k}-1)]`$ to the weighted sum and the whole layer at most $`2^{1-k}`$. Every infinite subset of $`A_\star`$ therefore has an irrational value at every integer base. These estimates are ordinary arguments in the short paper; Lean supplies the criterion they feed.

The proof turns rationality into a lattice. For $`N\ge1`$,
``` math
0<\Delta_A(N)=\sum_{a\in A}\frac{b^{N\bmod a}-1}{b^a-1}
 =(b^N-1)X_A(b)-J(N),\qquad J(N)\in\mathbb Z,
```
so if $`X_A(b)=p/q`$ every such displacement is at least $`1/q`$, and it suffices to find arbitrarily small ones. Sampling $`N`$ along multiples of a modulus that every element of a finite part of $`A`$ divides removes that part. The infinite tail is the hard step. Each remaining term is periodic in $`N`$; averaging over the first $`T`$ multiples of the modulus bounds its complete periods by its weighted summand when the $`P`$-part of the exponent divides the modulus, and through a large common divisor otherwise. The leftover incomplete periods of infinitely many exponents need a second average, over dyadic values of $`T`$ ([`WeightedReturn.lean`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean) carries both averages).

Erdős proved the pairwise-coprime case of the reciprocal-summable criterion and stated, without details, that coprimality can be removed \[erdos1968, p. 222\]. The short paper gives a complete proof of that stated extension at every integer base, which Lean checks and Comparator has compared, and credits it to him. Erdős also remarked that reciprocal summability could be replaced by a weaker, more complicated condition, which he did not state; the short paper does not identify its weighted condition with that remark, and it credits Duverney and Tachiya for a related selection step \[duverneytachiya\]. The criterion excludes full support and the set of all odd exponents, and irrationality for every infinite support remains open.

A reader given this much can check the theorem, see why it holds, see whose idea it extends and see what is left to prove. Mathematicians writing in September 2026 describe what a proof produced at machine speed arrives without. Kra writes that the machines are producing solutions “faster than the mathematical community can read them, much less digest them” \[kra\]; Cohn calls the unexplained remainder technical debt \[cohn\]; Tao asks for analysis that “identifies insights from the solution process” \[taomining\]; a declaration first signed by twenty-five Fields Medallists names the writeup, the isolation of new methods and ideas, and the citation of earlier work as what rushed announcements lose \[fieldsdecl\]; and Sanderson writes that “every AI-generated proof is born an unsolved exposition problem” \[sanderson\]. Each of these concerns what a proof does not carry by itself: the routes that failed, the computations that chose the route, the literature it relied on and the precise statement that remains open.

This paper describes a research environment built to keep that record. Its unit of work is the *problem-sized world*: one research problem together with everything learned about it, kept in a public repository. As producing results becomes easier, helping other people understand and use them becomes the scarce part of the work, and the world is organised around that part.

<a id="sec:world"></a>

# A problem-sized world

A problem-sized world is a versioned set of files in a public Git repository, organised around one research question and kept while the question is refined, attacked, partly answered or resolved. Its short paper, 12 to 28 pages long, is the first read: the problem and its status, the strongest results and their mechanism, their relation to prior work and the exact point where the argument stops. Its long record keeps the complete arguments, failed routes, experiments with their finite domains, corrected claims and attribution for every borrowed idea. Beside them sit the Lean source, checked by a pinned kernel \[lean4\]; a claim registry with the wording, evidence class and limits of each public claim; and a ledger recording, for every result asserted in a paper, the Lean declarations that state it or that none does. A margin mark beside a result links its declaration and any Comparator receipt; an unmarked result rests on the paper’s own argument, and a dagger marks a named input the formal proof assumes.

Every result that returns to a world raises four decisions, and the world records each one separately (Table <a href="#tab:decisions" data-reference-type="ref" data-reference="tab:decisions">1</a>). A successful check in one row settles nothing in another: a valid theorem can be a routine lemma that belongs only in the long record, a promising conjecture can direct the next computation without entering the proved claims, and a clear explanation can describe the wrong formal statement.

<div id="tab:decisions">

| Decision | What the world records | For the weighted criterion |
|:---|:---|:---|
| Evidence | The exact statement, its hypotheses and named inputs, the Lean declaration and its checking receipts | Lean proves the criterion; Comparator has compared the declarations that state it |
| Appraisal | The mechanism, the closest antecedent, the strength of the result and the obstruction that survives | Two averages; Erdős’s reciprocal-summable case, credited; admits $`A_\star`$; excludes full support |
| Exposition | Whether the result belongs in the short paper or the long record, and how its hard step is explained | The theorem opens the short paper; the example and the full averaging proof follow it |
| Allocation | The next question, the test that would decide it and the condition for stopping | Irrationality for every infinite support, registered as an open proposition |

Four decisions about a returned result, with the record kept for the weighted criterion of Section <a href="#sec:intro" data-reference-type="ref" data-reference="sec:intro">1</a>.

</div>

Problem 249 asks whether $`S=\sum_{n\ge1}\varphi(n)/2^n`$ is irrational, where $`\varphi`$ is Euler’s totient function \[erdosgraham\]. Its short paper \[paper249\] starts from an exact theorem about the subsequences obtained by splitting the coefficients of $`S`$ into residue classes modulo powers of a base. With $`\mathbb N=\{0,1,2,\ldots\}`$ and $`\varphi(0)=0`$, the seven sections $`\varphi(2^jn+r)`$ with $`0\le j\le2`$ and $`0\le r<2^j`$ reduce to the five sequences
``` math
\varphi(n),\quad\varphi(2n),\quad\varphi(2n+1),\quad
 \varphi(4n+1),\quad\varphi(4n+3),
```
since $`\varphi(4n)=2\varphi(2n)`$ and $`\varphi(4n+2)=\varphi(2n+1)`$. These five are linearly independent, and the pattern holds in every base. For every base $`k\ge2`$ and level $`e\ge1`$, the sections $`\varphi(k^jn+r)`$ with $`0\le j\le e`$ and $`0\le r<k^j`$ span a space of dimension $`k^e+1`$ over $`\mathbb Q`$, with basis $`\varphi(n)`$, $`\varphi(kn)`$ and the sections with $`1\le j\le e`$ and $`k\nmid r`$; every other section is an explicit integer multiple of a basis element, and these reductions generate all integral relations. Coons proved that $`\varphi`$ is not $`k`$-regular for any $`k\ge2`$ \[coons\]; the basis theorem recovers this and gives the dimension at every level.

Lean proves the theorem for every base, and Comparator has compared it. The reductions are elementary; the independence carries the weight, through an evaluation matrix made diagonal and nonzero modulo an auxiliary prime, with evaluation points chosen by the Chinese remainder theorem and Dirichlet’s theorem so that each row asks one primitive affine form to take a prime value. Martin’s Theorem 1 already implies the affine independence \[martin\], and the separation method goes back to Yazdani, who credits it to Shallit \[yazdani\]; the short paper credits both. The record keeps the basis theorem, a statement about the coefficients, apart from the irrationality of $`S`$, whose open form it states exactly.

Write $`R_N=\sum_{j\ge1}\varphi(N+j)2^{-j}`$ for the tail of $`S`$ after $`N`$ terms, put $`H_t=\operatorname{lcm}(1,\ldots,t)`$, and write $`\mathrm{Cert}(t)`$ for a finite exact computation, on totient values just after $`H_t`$ and $`2H_t`$, showing that $`R_{2H_t}-R_{H_t}`$ is not an integer. Lean checks, and Comparator has compared,
``` math
\forall t\le82,\quad \mathrm{Cert}(t),
```
and Lean also proves, again with a Comparator comparison, that irrationality of $`S`$ is equivalent to the unbounded supply
``` math
\forall T,\ \exists t>T,\quad \mathrm{Cert}(t).
```
The finite theorem makes no $`t=83`$ or cofinal claim. What remains open is the unbounded supply itself, which is the irrationality of $`S`$ in equivalent form, and the record states it in exactly that form.

<a id="sec:production"></a>

# From corpus to insight

<div id="systems-mathloop">

</div>

The short papers are distilled from a much larger research record. Each problem keeps a research corpus of exact results, negative results, computations, literature notes and proposed next steps, including intermediate and superseded entries, and the mathematical loop runs over it in two coupled roles.

<a id="discovery-and-stewardship."></a>

#### Discovery and stewardship.

<div id="systems-coupled-goals">

</div>

A discovery pass stays close to the frontier: it runs discriminating computations, attempts proofs and returns results. A stewardship pass reads each new result against the whole corpus and makes the four decisions of Table <a href="#tab:decisions" data-reference-type="ref" data-reference="tab:decisions">1</a>: what the result establishes, whether it is routine or strong and whom it credits, where it belongs in a paper, and which obligation deserves the next unit of work. One agent may play both roles in sequence. Neither inherits the other’s authority, and neither starts new work while the frontier and the files that depend on it are unchanged.

Models do the reading, comparison and drafting under written procedures, published with the repository as agent skills. Deterministic code assembles each long record from its authored parts, records the Lean evidence of every asserted result or its absence, and checks that each result a paper states is linked and that each registered limitation stays visible. No deterministic check decides what is important; that judgement, whoever drafts it, is written into the paper, where a reader can inspect and dispute it.

Negative results are part of what the loop produces. Tao observes that withheld negative results and processes hide where a new frontier lies \[taomining\]; the record keeps them. A counterexample refutes a conjecture on its exact domain, and a Lean no-go theorem rules out a class of strategies under explicit hypotheses, so later work need not repeat either. A failed computation records its finite domain and the inference it defeats. For Problem 257, a proposed estimate said that the greedy test ruling out a rational number with denominator $`Q`$ as the sum of an infinite subseries of $`\sum_n1/(2^n-1)`$ stops within about $`2\log_2Q-3.3`$ steps; an [`exact rational probe`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/research/experiments/choices_contraction/README.md) first rules out $`189/388`$ at step 17. The record keeps both facts: the estimate is false, and the problem itself is untouched. Inside the weighted proof the same discipline explains the second average: the short paper shows why the majorant of the reciprocal-summable proof fails beyond that class.

Reading the problems together raises questions that none of them asks alone. Seven of the eight problems ask whether a series is irrational, and the synthesis paper \[synthesis\] studies what their methods share and where each stops. The sparse corrections used for Problem 251 led to a capacity criterion for factorial digits, and then to a question: can one sequence of factorial digits prescribe several derivatives at once? For $`c>0`$, let $`\mathcal H_c`$ be the class of entire functions $`f(z)=\sum_{n\ge1}e_nz^n/n!`$ with $`e_n\in\mathbb Z_{\ge0}`$, $`e_n\le n^c`$ eventually, and every fixed positive integer dividing $`e_n`$ for all large $`n`$, and for an integer $`d\ge1`$ put $`J_d(f)=(f(1),f'(1),\ldots,f^{(d-1)}(1))`$. The synthesis paper proves
``` math
\dim_{\mathrm H}\{J_d(f):f\in\mathcal H_c\}=\min(c,d),
```
that this set contains a nonempty open subset of $`\mathbb R^d`$ exactly when $`c>d`$, and that a nonpolynomial member of $`\mathcal H_c`$ with $`f(1),\ldots,f^{(d-1)}(1)`$ all rational exists exactly when $`c>d`$. So a nonpolynomial $`f\in\mathcal H_2`$ with $`f(1)`$ rational has $`f'(1)`$ irrational, while coefficients of size $`n^{2+\varepsilon}`$ allow both to be rational. The construction rests on a carry identity,
``` math
(z-1)\sum_{n\ge0}\frac{b_nz^n}{n!}
 =-b_0+\sum_{n\ge1}\frac{(nb_{n-1}-b_n)\,z^n}{n!}:
```
adding such a term to $`f`$ leaves $`f(1)`$ unchanged and moves $`f'(1)`$ by $`\sum_nb_n/n!`$, and a factor $`(z-1)^k`$ leaves $`f(1),\ldots,f^{(k-1)}(1)`$ unchanged at a cost of $`k`$ powers of $`n`$ in the coefficient allowance. Division by $`(z-1)^d`$ gives the matching obstruction: vanishing derivatives become bounded integer coefficients, which eventual divisibility forces to vanish. Both theorems are proved in the synthesis paper by ordinary argument and carry no Lean mark; Lean checks the finite carry identity and its preservation of divisibility.

<a id="sec:checks"></a>

# From a proof to a public claim

<div id="systems-lifecycle">

</div>

A proof becomes a public claim by crossing three questions that the word “verified” tends to merge: whether the proof establishes its formal statement, which the pinned Lean kernel answers in continuous integration; whether the proved statement is exactly the separately written one, using only permitted axioms, which Comparator answers for selected statements; and whether the formal statement says what the problem says and whether the result matters, which a mathematician answers.

Lean verifies that a proof establishes the formal statement written in the source; it does not verify whether that statement captures the intended mathematics or whether the paper describes it well. The gap is measurable. Feng et al. had mathematicians grade 200 candidate solutions to Erdős problems produced by Aletheia, an agent built on Gemini Deep Think: 63 were technically correct, of which 13 were meaningfully correct; the other 50 answered a reading of the problem that missed Erdős’s intent \[aletheia\].

Comparator, a checker the Lean FRO built for judging machine-written proofs \[leanfrocomparator\], answers the second question. A trusted challenge module restates each statement without its proof; the proof must be a term of exactly that type, using only the permitted axioms, and the Lean kernel must accept it. The corpus replay, run in the companion repository `plectis-erdos-lean`, also passes every compared proof through nanoda, an independent kernel \[nanodalib\]. In this repository, continuous integration requires a deliberately altered statement to fail Comparator, so the harness cannot pass vacuously. Comparator cannot decide whether a statement is the right translation of the problem. It guarantees that the separately written statement, which a reader can inspect, is the statement that was proved, so “Comparator-checked” is accurate where “independently verified” would overclaim.

The paper-to-Lean ledger makes both formal questions countable for the papers’ own statements. It holds one row for each result asserted in the sixteen problem papers, 674 in all, counting a result stated in both a short paper and a long record twice, with its statement digest and kind of correspondence. For 506 rows the named Lean declarations state the result exactly; for 140 they state it or a result that implies it by an immediate specialisation; 25 are proved from a named input, marked with a dagger; and 3 have no Lean statement. Comparator has compared 633 of the 646 exact and specialising rows, and the other 13 are queued for its next replay; every receipt in the pinned corpus replay was accepted by both the Lean kernel and nanoda. A digest detects a changed statement, and the classification of a correspondence stays the maintainer’s judgement.

The third question stays with people. The claim registry records the wording of each public claim with its evidence class, the bounded domain of each finite instance and the open statements it approaches, and the papers, README and generated views may say only what the registry allows. In this repository the maintainer is responsible for that wording, and no independent mathematical review is yet recorded. A release checker keeps those surfaces consistent with the registry and the Lean source, and requires a registered limitation to stay visible wherever its claim appears.

That requirement comes from a test in which a limitation escaped. One deliberately false README edit changed a clause saying that the finite cases of Problem 249 did not supply the open requirement into one saying that they completed it. Lean was untouched, and the checker passed because that relationship had not been registered. After registration, the post-repair witness accepts the current README and rejects a test copy containing the false clause. A small historical study tested the checker with deliberately false edits: nine of the ten edits were rejected. One escaped, for the reason just given. The edits were authored by the checker’s author. The original run logs were not retained. The other nine edits were not rerun against the extended checklist. The evidence marks a coverage boundary, not a reliability score.

The workflow does not technically force a second independent mathematician: the maintainer can edit a Lean statement, its record and its prose together so that every comparison agrees with the same mistake. Independent review is recorded as an external event when it happens. A changed result reopens what depends on it. Propagation starts from the changed object and lists every reverse import, claim record, paper, experiment and open obligation the change may affect; each must be updated, verified unchanged, deferred with a reason or marked out of scope, and an empty search never counts as evidence of no consequence.

<a id="sec:cycle"></a>

# The contribution cycle

<div id="systems-job-lifecycle">

</div>

Someone outside the original research can contribute a correction or take an argument further, and that work returns to the same record. The public repository publishes this research, checking and revision cycle as thirteen agent skills that install into common agent harnesses. Each skill owns one job, with its starting state, the changes it may make, the evidence it must return, its stopping condition and the next owner. The ordinary path orients (`explain-public-system`), works on one open obligation (`mine-open-problem`), validates (`land-lean-proofs`), propagates (`propagate-research-consequences`), packages the return with its prose held to the evidence (`public-mathematical-writing`) and proposes a pull request from a named starting commit (`submit-pull-request`). The [companion contribution protocol](../../../paper/systems/open-source-mathematics-strategy.pdf#nameddest=strategy-protocol) gives the full sequence, and the [companion runtime paper](../../../paper/systems/cold-clone-to-proof-receipt.pdf#nameddest=cold-clone-return-lifecycle) describes navigation and proof receipts in a fresh clone. Adoption replays the contributor’s original change from its named starting commit before reconciling it with the current tree, so the original work and any conflict resolution are credited separately. A cycle closes when the change has evidence and every consequence has a recorded disposition; a problem closes only when a proof or a refutation settles its original statement.

<a id="credit."></a>

#### Credit.

The [`credit policy`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/docs/research-commons/CREDIT_POLICY.md) lets an idea be credited separately from its proof, its Lean formalisation and its explanation, the roles Kra asks journals to distinguish \[kra\], and credits software as a role of its own. A first return can be a plain-language research-progress issue or email: no clone, proof, code or receipt schema is required. Accepted work receives a public receipt tied to exact artifacts. Acceptance does not establish theorem status, novelty, or release inclusion. Corrections append to the history, and an earlier contributor’s record stays in it. Work also leaves the repository: Google DeepMind’s Formal Conjectures maintainers have merged four of its contributions, linking formal proofs for Problems 257, 1049 and 1041 and a constant-base variant of Problem 258.

<a id="sec:example"></a>

## Worked example: Problem 1041

Problem 1041 shows the cycle end to end, with the decisive idea arriving from outside. It asks whether, for a monic polynomial $`f`$ with all roots in the open unit disc, two roots can always be joined inside the lemniscate $`\{|f|<1\}`$ by a path of length less than $`2`$ \[erdos1041; ehp1958\]. On 7 September 2026 the erdosproblems.com contributor `ani` posted a degree-seven counterexample, found, as the post says, with the help of GPT-6 \[aniforum\], and the record took the construction as an attributed input five days later. Lean first checked the total-variation form. On 22 September it proved that for one polynomial of that construction every preconnected subset of the strict lemniscate containing two distinct roots has one-dimensional Hausdorff measure greater than $`2`$ ([`HausdorffLength.lean`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean)), which refutes the exact path-image-length statement in Google DeepMind’s Formal Conjectures repository \[formalconjectures\]. On 23 September the Formal Conjectures maintainers merged a change that marks the problem solved with answer `False` and links this proof \[fcpr\]. The short paper and long record carry the proof with its Lean mark and credit `ani` for the construction. One judgement remains open: whether the formal statement matches the 1958 wording \[ehp1958, Problem 5, p. 139\]. The record says so beside the result.

<a id="sec:instance"></a>

# Eight problems in one repository

<div id="systems-public">

</div>

The [public repository](https://github.com/wcook04/plectis-erdos) maintains eight Erdős problems \[erdosproblems\] as problem-sized worlds. Table <a href="#tab:problems" data-reference-type="ref" data-reference="tab:problems">2</a> gives one result for each problem and the point where it stops.

<div id="tab:problems">

| Problem | A result to start with | Where it stops |
|:---|:---|:---|
| \#68, factorial denominator | Lean checks that the logarithm of the uncleared common denominator grows at least like $`N^{3/2}\log N`$, and that irrationality is equivalent to cofinally many non-unit factorial carries | Those carries are not produced |
| \#243, Sylvester-tail rigidity | For a strictly increasing sequence of positive integers, Lean checks irrationality of $`\sum 1/a_n`$ under the exact cubic rate $`a_n^2/a_{n+1}=1+3/n+o(n^{-3})`$ | The unrestricted Sylvester-tail question |
| \#249, binary totient series | For every base $`k\ge2`$ and level $`e\ge1`$, the totient sections $`\varphi(k^jn+r)`$ with $`0\le j\le e`$ and $`0\le r<k^j`$ span a space of dimension $`k^e+1`$ over $`\mathbb{Q}`$; certificates for every $`t\le82`$ | Certificates for arbitrarily large $`t`$ |
| \#251, prime-gap dyadic series | Lean and Comparator check that sparse corrections preserving the congruences fill an interval of sums; from the prime number theorem and a lemma of Schlage-Puchta as named inputs, Lean checks a sequence with the local statistics of prime gaps and a rational dyadic sum | An argument specific to actual prime gaps |
| \#257, infinite exponent supports | The weighted-support criterion of Section <a href="#sec:intro" data-reference-type="ref" data-reference="sec:intro">1</a>, at every integer base | Arbitrary infinite supports |
| \#269, three-prime running LCMs | Lean and Comparator check that the three-prime running-LCM kernel has nonsingular minors of every order, so no finite sum of separated products represents it; both two-prime sums are transcendental by a cited Hecke–Mahler theorem, the repeated-sum case first posted by Fan \[fan269\] | The three-prime case |
| \#1041, lemniscate connections | The Formal Conjectures statement is refuted with `ani`’s example | Match with the 1958 wording |
| \#1049, rational-base Lambert series | Lean checks irrationality in Zudilin’s rational-base region and exact Hankel orders | Base $`3/2`$ and all rational bases |

One result per problem, with its stopping point. The papers state each result in full with its hypotheses and sources.

</div>

The repository holds 1,823 Lean modules in its two library roots under a pinned toolchain, sixteen problem papers totalling 773 pages, a cross-problem synthesis paper and three systems papers. The claim registry holds 150 public claims in seven statuses, from proved here and formalised here to conditional reduction and open, and states 19 remaining obligations exactly. Continuous integration builds the supported Lean roots, a coverage build compiles every module a paper cites, and the release checker runs 15,666 checks over claims, papers, generated views and licences. A fresh clone needs no private file, and no public theorem depends on an unpublished lemma.

<div id="systems-comprehension">

</div>

The clone also carries the machinery for continuing a proof. A [`proof-state compiler`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/docs/agents/PROOF_STATE_COMPILER.md) takes the declarations that static queries nominate for a goal and asks the pinned Lean environment what each application does. A transition exists only when Lean reaches the state after the application; the subgoals Lean leaves form an AND set that becomes the exact remaining obligation, competing applications are OR alternatives, and a proof receipt exists only when Lean exits with no goals left. In its pilot, applying a Problem 249 totient-tail lemma without its divisibility hypothesis leaves exactly that hypothesis open, and supplying it closes the same application.

The records come from a private environment, built over the past year, that runs agents from several model providers, including Anthropic’s Claude and OpenAI’s GPT models, concurrently on one shared file system. Durable state lives in files, and before an agent opens a large source a router compiles a packet conditioned on its task, with each item labelled by evidence class and a list of what was omitted. Agents claim exact paths for a bounded lease before changing them. Lean builds pass through a semantic single-flight queue keyed by source, targets, toolchain and dependency lock, so equivalent requests share one build, and a deferral is recorded separately from theorem failures. A failure in navigation, scheduling, experimentation or validation can change a route, skill or check for later agents through a guarded proposal, and it never changes the status of a mathematical claim. The public repository replays without the private environment: the private environment explains how the records were produced, and the public evidence is what supports each claim.

<a id="sec:related"></a>

# Relation to Prove2Me and other systems

Prove2Me \[prove2me\] is the closest published system: a hosted platform on which anyone with a coding agent states Lean theorems and submits proofs. Each statement is immutable and may carry several proofs; the server accepts a proof only when its type is exactly the target’s, with no `sorry` and only whitelisted axioms, and a disproof proves the negation. Missions on papers, textbooks and open problems confine human audit to a goal, its definitions and milestone lemmas, aided by a blind agent read-back of each Lean statement, and a proof sketch may import open statements for other agents to close. Persistence, decomposition, visible negative results and exact statement checking are therefore shared features; the two designs differ in the unit they maintain (Table <a href="#tab:prove2me" data-reference-type="ref" data-reference="tab:prove2me">3</a>). Prove2Me’s paper appeared on 28 August 2026; the first public version of this paper, with its claim registry and release checks, appeared in July 2026, and the two designs developed independently. Prove2Me is the published reference for hosted statement and proof separation, audited mission cores and read-back auditing.

<div id="tab:prove2me">

|  | Prove2Me | Problem-sized worlds |
|:---|:---|:---|
| Unit of work | A mission on a paper, textbook or open problem, built from immutable statements and proofs | One research problem with its whole record |
| What persists | Statements, proofs, sketches, explanations, milestones and discussion; disproofs and deprecations stay visible | Short and long papers, failed routes, experiments, typed claims and open obligations beside the Lean source |
| Exact-statement check | Every submission, on the server | Selected statements, through Comparator, with a second kernel in the corpus replay |
| Statement fidelity | A captain audits each mission core with a blind read-back; a moderator approves public missions | The maintainer is responsible for the wording of each public claim in the claim registry; no independent review is recorded yet |
| Exposition | A description for each statement and an explanation for each proof | A short paper and a long record for each problem, with evidence marks at each result |
| Credit | Permanent names, trust scores, leaderboards and import citations | Receipts by contribution role, and attribution for outside ideas |
| Contribution path | Web platform and API, with an account | Git clone and thirteen agent skills, a pull request, an issue or an email |

Prove2Me and problem-sized worlds, from Prove2Me’s paper and public pages and from this repository, on 24 September 2026.

</div>

The two compose. Prove2Me contributes hosting, importable statements, per-submission checking and a contributor base; a world contributes the problem-level context around a statement: its papers, failed routes, obstructions and open obligations. This repository’s sharp constant in the collinear root-segment bound of Erdős, Herzog and Piranian for Problem 1041, which Comparator has also compared, is hosted on Prove2Me as a package of 21 theorems with accepted proofs, ported from Lean 4.29.1 to Prove2Me’s Lean 4.30.0 environment.

<a id="other-systems."></a>

#### Other systems.

Feng et al. ran an agent over the 700 Erdős problems then listed as open, published graded outcomes \[aletheia\], and propose reporting AI-assisted results on at least two axes, autonomy and significance, with significance judged only by mathematicians expert in the area \[autonomousmath\]; the claim registry leaves significance to experts in the same way. Tao’s community wiki listed AI contributions to the Erdős problems, failed attempts included, until its updates stopped on 30 June 2026 \[taowiki\]. Formal Conjectures \[formalconjectures\] turns open problems into formal targets, and Ringer distinguishes mathematics as a process from mathematics as a benchmark \[ringer\]; a world keeps the process around such a target. Blueprints connect informal proof plans to Lean declarations \[leanblueprint\]; LeanArchitect extracts blueprint data from annotated Lean source, infers dependencies and tracks progress \[leanarchitect\]; and LeanMarathon maintains an evolving blueprint, one Lean file serving as proof skeleton, natural-language proof graph and shared record, worked by separate construction, audit, proof and repair agents \[leanmarathon\]. These are direct precedents for durable formal development linked to its explanation, and a world can use a blueprint as its dependency map; the world adds the appraisal around the proofs, with the mechanism and antecedents of each result, the failed routes and the exact open obligations. Provers such as ReProver, built on LeanDojo, and OpenProver \[leandojo; openprover\] can supply a world with candidate proofs, and Li et al. hold generation and validation apart in research mathematics without a proof assistant \[lihai\].

<a id="sec:limits"></a>

# Limits, and what stronger models change

<div id="systems-trust">

</div>

The other seven targets remain open, and independent human review of the correspondence between the Problem 1041 refutation and the 1958 wording has not been recorded. The system records evidence classes and review events; novelty and significance are judgements it leaves to experts, as Feng et al. also propose \[autonomousmath\]. The examples here show how the record organises results; whether the workflow made those results more likely has not been measured. By 24 September 2026 no outside human contributor had opened a pull request or issue in the repository; its outside record is the Formal Conjectures merges of Section <a href="#sec:cycle" data-reference-type="ref" data-reference="sec:cycle">5</a> and the Prove2Me package. A record also leaves several of the concerns in Section <a href="#sec:intro" data-reference-type="ref" data-reference="sec:intro">1</a> where it finds them: it trains no one, it restores no signal of individual expertise \[litt\], and it answers neither the ethical objections some mathematicians raise to AI-assisted mathematics \[chu\] nor the warning of forty-two Fellows and Foreign Members of the Royal Society about catastrophic risk from AI \[greenletter\].

<div id="systems-scaling">

</div>

The same design serves stronger models. A stronger model starts from the current frontier with the failed routes already marked, and it can reorganise, re-explain and extend the record as well as the mathematics. The public interfaces admit any producer: an outside contributor can attach any agent runner to the clone, and a laboratory with many frontier models could replace the private production environment while keeping the same evidence boundary.

Gowers suggests a well-designed database of what is known, probably built with AI help, and adds that it may prove unnecessary if one can ask a language model for a bird’s-eye view of an area \[gowers\]; Koukoulopoulos proposes a public facility in which coordinated agents explore a research programme divided into subproblems under researchers’ direction \[koukoulopoulos\]. A problem-sized world supplies the shared record both proposals need, at the scale of eight problems, and the written-briefing arm of the measurement below stands in for Gowers’s alternative. Antieau writes that texts generated largely by a language model deserve a home other than the arXiv \[antieau\]; a world gives its long records one beside the proofs they explain. The same structure suits a single landmark result, and it asks three things of a field: stable result identities, a checker where one exists, and an explicit boundary on public claims.

The next measurement is comparative. With the source revision, task set, model, tool access and budget held fixed, agents receive the Lean source alone, an information-equivalent written briefing, or the whole world with its continuation tools. Independent domain readers grade whether each recovers the strongest supported claim, its hypotheses, its hard step, its antecedents and the remaining obligation, and review one returned change; statement errors, reviewer time and total work, preparation and maintenance included, are recorded, and failed and abandoned attempts are counted. Ablations separate the short paper, the evidence links and the continuation tools; historical tasks need a cutoff that hides later proofs and theorem names, and prospective tasks give a separate test. Repeating the frozen tasks with a stronger model measures what the record adds as models improve.

<a id="sec:conclusion"></a>

# Conclusion

A problem-sized world keeps the record that lets other people understand a proof, check it, credit it and build on it: its mechanism, its antecedents, its formal evidence and its exact open statements. The weighted criterion, the totient basis and the derivative-interpolation theorem show that record for three results, and the eight worlds in the public repository show that it can be kept persistent, checkable and open to contribution across several hard problems. The record is built for models stronger than the ones that produced it: each starts from the recorded frontier with the failed routes marked, and Section <a href="#sec:limits" data-reference-type="ref" data-reference="sec:limits">8</a> names the measurement that tests whether this makes it more effective.

<a id="app:repro"></a>

# Inspection routes and reproducibility

<div id="tab:routes">

| Question | Start here |
|:---|:---|
| How does the repository fit together? | [`docs/ARCHITECTURE.md`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/docs/ARCHITECTURE.md) |
| What is proved and what is open? | [`docs/RESULTS.md`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/docs/RESULTS.md) and [`docs/claims.json`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/docs/claims.json) |
| Which declaration states each paper result? | [`docs/paper_lean_coverage.json`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/docs/paper_lean_coverage.json) |
| Where is the checked mathematics? | [`lean/Erdos249257.lean`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/lean/Erdos249257.lean) and [`lean/ErdosProblems.lean`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/lean/ErdosProblems.lean) |
| What does Comparator check? | [`docs/EXTERNAL_VERIFICATION.md`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/docs/EXTERNAL_VERIFICATION.md), [`verification/comparator.json`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/verification/comparator.json) and the corpus replay index [`evidence/comparator/associations.json`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/evidence/comparator/associations.json) |
| Whose earlier work does each result use? | [`docs/PRIOR_ART.md`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/docs/PRIOR_ART.md) |
| Which checks gate a release? | [`scripts/check_release.py`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/scripts/check_release.py) and [`.github/workflows/lean.yml`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/.github/workflows/lean.yml) |
| How can work return with credit? | [`CONTRIBUTING.md`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/CONTRIBUTING.md), [`credit policy`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/docs/research-commons/CREDIT_POLICY.md) and [`architecture contributions`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/docs/research-commons/ARCHITECTURE_CONTRIBUTIONS.md) |
| Which agent skills exist? | [`skills/README.md`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/skills/README.md) |

Entry points for inspection. They lead to the authority-bearing files and add no authority of their own.

</div>

A fresh clone reproduces the control card and the structural checks without Lean:

    python3 scripts/proof_cockpit.py --format card
    python3 scripts/proof_cockpit.py --check
    python3 scripts/check_release.py

Formal authority begins with the pinned `lake build` named by the card. The paper inventory, `docs/publication_contract.json`, records source and PDF hashes and validation commands, and the evidence for the checker study in Section <a href="#sec:checks" data-reference-type="ref" data-reference="sec:checks">4</a> is recorded in `docs/publication_evidence.json`.

<div class="multicols">

2

<div class="thebibliography">

99 T. F. Bloom, *Erdős problems*, [erdosproblems.com](https://www.erdosproblems.com), accessed September 2026. W. Cook, *Weighted Support Criteria for Reciprocal Mersenne Subseries*, short paper on Erdős Problem 257, September 2026, [`PDF`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/paper/257/erdos-257-mersenne-support-subseries.pdf). P. Erdős, *On the irrationality of certain series*, Math. Student 36 (1968), 222–226 (issued 1969), [scan](https://users.renyi.hu/~p_erdos/1969-09.pdf). D. Duverney and Y. Tachiya, *Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*, Forum Math. 31 (2019), 1557–1566, [DOI](https://doi.org/10.1515/forum-2018-0299). B. Kra, *Deep theorems were scarce and difficult and so became an effective mechanism to identify deep thought. AI has broken this system*, guest post on *What’s new*, 13 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/13/deep-theorems-were-scarce-and-difficult-and-so-became-an-effective-mechanism-to-identify-deep-thought-ai-has-broken-this-system/). H. Cohn, *The technical debt of AI-generated mathematics*, guest post on *What’s new*, 15 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/15/the-technical-debt-of-ai-generated-mathematics/). T. Tao, thread on mining open problems, Mathstodon, 8 September 2026, [thread](https://mathstodon.xyz/@tao/117237320796901560). Twenty-five Fields Medallists, *A severe misalignment of AI in mathematics*, declaration posted on *What’s new*, 11 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/11/a-severe-misalignment-of-ai-in-mathematics/). G. Sanderson, *If math is more than proof, we need to better celebrate the rest of it*, guest post on *What’s new*, 18 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/18/if-math-is-more-than-proof-we-need-to-better-celebrate-the-rest-of-it/). L. de Moura and S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, in *Automated Deduction, CADE 28*, Lecture Notes in Computer Science 12699, 2021, pp. 625–635, [DOI](https://doi.org/10.1007/978-3-030-79876-5_37). P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L’Enseignement Mathématique 28, 1980, p. 61. W. Cook, *Bases and Integral Relations for the $`k`$-Kernel of Euler’s Totient*, short paper on Erdős Problem 249, revised 18 September 2026, [`PDF`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/paper/249/erdos-249-binary-totient-series.pdf). M. Coons, *(Non)Automaticity of number theoretic functions*, J. Théor. Nombres Bordeaux 22 (2010), 339–352, [DOI](https://doi.org/10.5802/jtnb.718), Theorem 3.2. G. Martin, *Simultaneous inequalities among values of the Euler phi-function*, 2006, [arXiv:math/0603053v1](https://arxiv.org/abs/math/0603053v1), Theorem 1. S. Yazdani, *Multiplicative functions and $`k`$-automatic sequences*, J. Théor. Nombres Bordeaux 13 (2001), 651–658, [Numdam](https://www.numdam.org/item/JTNB_2001__13_2_651_0/). W. Cook, *Reading Eight Erdős Problems Together*, synthesis paper, September 2026, [`PDF`](https://github.com/wcook04/plectis-erdos/blob/872d16d07a4f1456300b923bc686ab31497b4df5/paper/synthesis/optimal-sparse-perturbations.pdf). T. Feng, T. Trinh, G. Bingham, et al., *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the Erdős Problems*, 2026, [arXiv](https://doi.org/10.48550/arXiv.2601.22401). Lean FRO, *Comparator*, 2025, [GitHub](https://github.com/leanprover/comparator). `ammkrn`, *nanoda_lib*, an independent type checker for Lean 4, [GitHub](https://github.com/ammkrn/nanoda_lib). T. F. Bloom, *Erdős Problem \#1041*, [erdosproblems.com](https://www.erdosproblems.com/1041), accessed September 2026. P. Erdős, F. Herzog and G. Piranian, *Metric properties of polynomials*, J. Analyse Math. 6 (1958), 125–148, [DOI](https://doi.org/10.1007/BF02790232). `ani`, post in the Problem 1041 discussion thread, 7 September 2026, [erdosproblems.com forum](https://www.erdosproblems.com/forum/thread/1041#post-8861). Google DeepMind, *Formal Conjectures*, [GitHub](https://github.com/google-deepmind/formal-conjectures), accessed September 2026. Formal Conjectures, pull request 6505, *Erdős 1041: mark solved with answer(False) and link a formal proof*, merged 23 September 2026, [GitHub](https://github.com/google-deepmind/formal-conjectures/pull/6505). S. Fan, comment on Erdős Problem \#269, erdosproblems.com forum, 26 June 2026, [forum post](https://www.erdosproblems.com/forum/thread/269#post-7218). S. Chen, K. Marwaha, X. Lu, H. Yuen, and T. Peng, *Prove2Me: An Open Collaborative Platform for Scaling Math Formalization*, 2026, [arXiv](https://doi.org/10.48550/arXiv.2608.28433). T. Feng, T. H. Trinh, G. Bingham, et al., *Towards Autonomous Mathematics Research*, 2026, [arXiv](https://doi.org/10.48550/arXiv.2602.10177). T. Tao, *AI contributions to Erdős problems*, [GitHub](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems), accessed September 2026. T. Ringer, *Becoming a benchmark*, guest post on *What’s new*, 17 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/17/becoming-a-benchmark/). P. Massot, *leanblueprint*, plasTeX plugin for Lean formalisation blueprints, 2020, [software repository](https://github.com/PatrickMassot/leanblueprint). T. Zhu, P. Monticone, S. Welleck, and J. Avigad, *LeanArchitect: Automating Blueprint Generation for Humans and AI*, in *17th International Conference on Interactive Theorem Proving*, LIPIcs 382, 2026, pp. 25:1–25:16, [DOI](https://doi.org/10.4230/LIPIcs.ITP.2026.25). Y. Zhang, Y. Sun, T. Suzuki, J. D. Lee, and F. Liu, *LeanMarathon: Toward Reliable AI Co-Mathematicians through Long-Horizon Lean Autoformalization*, 2026, [arXiv:2606.05400](https://arxiv.org/abs/2606.05400). K. Yang et al., *LeanDojo: Theorem Proving with Retrieval-Augmented Language Models*, NeurIPS 2023. M. Kripner and M. Straka, *OpenProver: Agentic and Interactive Theorem Proving with Lean 4*, 2026, [arXiv](https://doi.org/10.48550/arXiv.2607.09217). C. Li, Z. Lai, D. An, J. Hu, and Z. Wen, *Advancing Mathematical Research via Human-AI Interactive Theorem Proving*, 2025, [arXiv:2512.09443v2](https://arxiv.org/abs/2512.09443v2). D. Litt, *A beginning for mathematics*, 13 September 2026, [blog post](https://www.daniellitt.com/blog/2026/9/13/a-beginning-for-mathematics/). T. Chu, *The AI dissenter viewpoint*, *Proofs and Prompts*, 9 August 2026, [blog post](https://proofsandprompts.com/2026/08/09/the-ai-dissenter-viewpoint/). B. Green and forty-one other Fellows and Foreign Members of the Royal Society, *Open letter to Sir Paul Nurse, President of the Royal Society*, *Proofs and Prompts*, 17 September 2026, [blog post](https://proofsandprompts.com/2026/09/17/open-letter-to-sir-paul-nurse-president-of-the-royal-society/). W. T. Gowers, *Why I didn’t sign the Fields medallists’ letter*, 17 September 2026, [blog post](https://gowers.wordpress.com/2026/09/17/why-i-didnt-sign-the-fields-medallists-letter/). D. Koukoulopoulos, *A CERN for AI-assisted science?*, guest post on *What’s new*, 17 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/17/a-cern-for-ai-assisted-science/). B. Antieau, *Fast math/slow math*, 15 September 2026, [blog post](https://antieau.github.io/2026/09/15/fast-math-slow-math.html).

</div>

</div>
