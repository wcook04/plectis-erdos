<a id="claim-faithful-publication-systems-paper"></a>

# Problem-Sized Lean Worlds

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Plectis maintains a mathematical claim together with the sources needed to publish and revise it. Its publication tools bind statements to source revisions, retain the complete set of recorded formal supports, and assemble papers from authored material. We describe the implementation through a support criterion for reciprocal Mersenne series, where omitting a hypothesis would turn a sufficient condition into an unsupported answer to an open problem. A historical test rejected nine of ten deliberately false edits; the surviving edit misstated what the mathematics established. This failure separates the checks that source binding can automate from the mathematical interpretation that still requires review. We give a protocol for testing reader understanding; no comparative reader result is reported.

<a id="sec:intro"></a>

# Introduction

A theorem may establish an implication under a support condition, while its abstract says that the motivating problem has been solved. Rebuilding the proof will reproduce the theorem with its hypotheses intact, without necessarily finding the error in the abstract. We study how a publication system can preserve the connection between the statement that was checked and the claim that a reader encounters.

We study this problem in Plectis, a collection of research records organised around problems in Bloom’s Erdős catalogue \[erdosproblems\]. Each record connects a claim to its source, the evidence recorded for it and the papers in which it appears. A short paper develops a selected argument; a longer record retains supporting proofs and the history needed to continue the research. Lean \[lean4\] and mathlib \[mathlib\] supply the formal language and library. The publication tools operate on the surrounding documents and their connections.

The implemented contribution is a source-bound publication path through these records. Given an immutable revision, the packet compiler collects a writer’s dossier in which each assertion retains all of its registered supports, including any named assumptions on which the result depends. The evidence renderer connects paper statements to recorded formal checks, an assembler rebuilds the long records from authored parts, and a prose checker detects changes to audited sentences or their declared sources. Together these operations expose stale support during revision. The mathematical relation between a sentence and its sources remains an authored judgement.

Formalisation blueprints already connect mathematical exposition to declarations. Massot’s `leanblueprint` and LeanArchitect are the closest antecedents for that connection \[leanblueprint; leanarchitect\]. Our account concerns papers that combine formal proofs with ordinary arguments, computations and unresolved claims, and that must retain those distinctions through later edits. The Equational Theories Project provides an existing example of persistent collaborative exploration \[etp\]; Prove2Me is a closely related agent-oriented formalisation platform \[prove2me\]. We claim neither priority for persistent research records nor a measured advantage over these systems.

We follow a support theorem for reciprocal Mersenne series through this path, then describe the checks and the two reading formats (Sections <a href="#sec:world" data-reference-type="ref" data-reference="sec:world">[sec:world]</a>–<a href="#sec:long" data-reference-type="ref" data-reference="sec:long">5</a>). The observations in Section <a href="#sec:instance" data-reference-type="ref" data-reference="sec:instance">6</a> precede a proposed evaluation of research sessions. Throughout, we distinguish code in the supplied revision of 29 September 2026 from additional designs described in its component reports. Appendix <a href="#app:repro" data-reference-type="ref" data-reference="app:repro">11</a> records the missing implementations and run material that limit reproduction from this attachment.

<a id="sec:predigestion"></a>

# A support condition through the publication path

<span id="sec:world" label="sec:world"></span>

Consider the series
``` math
X_A(b)=\sum_{a\in A}\frac{1}{b^a-1},
 \qquad A\subseteq\mathbb N_{>0}\text{ infinite},\quad b\in\mathbb Z,\ b\ge2.
```
For a finite nonempty set $`P`$ of primes, write $`h_P(a)=\prod_{p\in P}p^{v_p(a)}`$ for the $`P`$-part of $`a`$. The weighted support theorem in the Problem 257 paper \[paper257\] states that
``` math
\begin{equation}
\label{eq:worked-condition}
 \sum_{a\in A}\frac{h_P(a)}{a(2^{h_P(a)}-1)}<\infty
\end{equation}
```
implies that $`X_B(b)`$ is irrational for every integer $`b\ge2`$ and every infinite subset $`B\subseteq A`$. The quantifiers over $`b`$ and $`B`$ belong to the conclusion; the summability condition belongs to the hypothesis. For $`P=\{2\}`$, write $`a=2^km`$ with $`m`$ odd. The summand in <a href="#eq:worked-condition" data-reference-type="eqref" data-reference="eq:worked-condition">[eq:worked-condition]</a> becomes $`1/[m(2^{2^k}-1)]`$: the large power of two allows a support with more reciprocal mass than the unweighted criterion would permit. For example, $`A=\{2^k:k\ge0\}`$ satisfies the condition since $`2^{2^k}-1\ge2^k`$, and hence the summands are at most $`2^{-k}`$. Every infinite thinning of this support satisfies it as well.

To see how the proof works, consider the displacement
``` math
\begin{equation}
\label{eq:worked-displacement}
 \Delta_{b,A}(N)=\sum_{a\in A}\frac{b^{N\bmod a}-1}{b^a-1}
               =(b^N-1)X_A(b)-J_{b,A}(N),
\end{equation}
```
where $`J_{b,A}(N)=\sum_{a\in A,\,a\le N}\sum_{j=1}^{\lfloor N/a\rfloor}b^{N-ja}`$ is an integer. For $`N>0`$, an exponent $`a>N`$ contributes a positive term, so rationality $`X_A(b)=p/q`$ would imply $`\Delta_{b,A}(N)\ge1/q`$. The proof contradicts this lower bound by averaging along multiples of a growing modulus. The difficult estimate concerns incomplete periods: a complete-period average alone does not control the finite tails needed in the argument, so the weighted proof takes a second, dyadic average \[paper257\].

Erdős had already stated the reciprocal-summable support criterion \[erdos1968\]. The Problem 257 paper supplies its averaging proof and distinguishes the weighted extension from that earlier statement. It also compares perfect-power supports with the Lambert-series work of Duverney and Tachiya \[duverneytachiya\]. These attributions must travel with the argument: a new arrangement of a proof does not make its ingredients new.

The universal question asks for irrationality for every infinite $`A`$ in base two. For each finite $`P`$, full support, the odd exponents and the primes all fail <a href="#eq:worked-condition" data-reference-type="eqref" data-reference="eq:worked-condition">[eq:worked-condition]</a>; the theorem gives no rationality conclusion for them \[paper257\]. Thus an abstract that drops the support condition asserts more than the theorem proves, even if its Lean links remain intact.

In a writer’s dossier, we keep the exact statement beside its evidence and the remaining universal question. Fields for the mechanism and the difficult step may be empty: their content has to come from an argument such as <a href="#eq:worked-displacement" data-reference-type="eqref" data-reference="eq:worked-displacement">[eq:worked-displacement]</a>, rather than from counting the theorem’s dependencies.

<a id="sec:checks"></a>

# Source binding and evidence

<div id="systems-lifecycle">

</div>

<a id="immutable-inputs-and-complete-support"></a>

## Immutable inputs and complete support

The dossier mode extends the research-packet compiler with an immutable reader. It resolves a Git revision and reads the claim registry, paper coverage and declaration atlas at that revision, together with the dependency export and research record. Because this reader disables the index’s working-tree fallback, a missing required source causes an error instead of silently producing an empty dossier. Each source locator identifies the revision and file digest, followed by a line span, a JSON pointer or a whole-file selection. Before writing a dossier, the compiler re-resolves each selection and checks its digest; the output then carries an input-file inventory and the hashes of the generated files. With the source revision, compiler and annotations held fixed, timestamps and absolute paths are excluded from the output.

A paper occurrence, a registry assertion and an uncurated declaration have distinct record types because a statement can occur in several papers and a declaration can support several statements. We expose these relations to the writer without counting them as mathematical discoveries.

For a paper assertion to receive the dossier’s formal-evidence classification, every registered support must resolve in the pinned source and dependency export, and its recorded statement identities must agree. The support relation and any named input are retained. A successful match to just one lemma would be insufficient for a result that depends on several.

<a id="sec:graph"></a>

## Dependency records

The argument-continuation graph is built from an elaborated export whose source identity and coverage limits remain part of the graph record. Relation rows distinguish a replacement hypothesis, an endpoint route and an equivalence in a stated context. An atlas entry with a matching signature and a reachable target attests to that source projection; it does not establish that any particular continuous-integration run compiled the module. Retrieval also leaves the selection of a useful abstraction and the completeness of the literature comparison to the author.

This design follows the familiar idea that a derived object depends on the versions of its inputs. Build Systems à la Carte separates dependency scheduling from rebuilding \[buildsystems\]; de Kleer’s assumption-based truth-maintenance system records the assumptions supporting conclusions \[dekleer\]. Here the inputs include a paper statement and its declared support, which gives revision checks a finer object to track than an entire PDF. Changing a source can therefore invalidate the evidence annotation even when the mathematical sentence itself is unchanged.

<a id="what-an-evidence-mark-says"></a>

## What an evidence mark says

We separate evidence kind from checking history. A record first identifies a Lean declaration, a Comparator result, an ordinary proof or a finite computation, then gives its checking history and remaining assumptions in separate fields. This avoids treating recorded formal support as though it were a fresh independent check.

The native evidence renderer resolves every declaration selected for a Comparator mark to a challenge, a solution and an accepted replay receipt with matching digests. It also compares the recorded declaration statement at the paper’s Lean pin with the statement compiled by the compared corpus, ignoring comments and layout, and writes nothing if resolution fails. Comparator and its independent checking backend, `nanoda_lib`, are credited dependencies \[leanfrocomparator; nanodalib\]. The dossier labels its own kernel and Comparator replays as unrun.

The claim-evidence component report extends this check to dependency membership and the wording permitted beside a statement. Its diagnostic output retains unresolved supports, so a failed join remains visible for review. We describe this extension from the report, whose checker implementation is absent from the attachment.

The integration records illustrate why the revision must be part of a source identity. An earlier interface report records a partially successful join, whereas the later supplied claim-evidence report has no joined rows and gives two global `formal_pin` findings. These findings concern disagreement between source pins; they establish neither a failed Lean build nor an absence of formal evidence in the corpus.

<a id="checking-the-prose"></a>

## Checking the prose

This paper’s checker inventories its authored body as explicitly delimited sentences, each with a digest, an evidence class and a warrant referring to source spans. It rejects missing or duplicate bindings, altered text and stale source digests, without executing commands named in the evidence records.

The warrant is an assertion by the author. If the author edits both a sentence and its annotation, matching hashes cannot establish that the revision follows from the source. The historical experiment in Section <a href="#sec:instance" data-reference-type="ref" data-reference="sec:instance">6</a> contains such a failure of coverage, which still requires mathematical comparison even when the relevant source and changed passage have been brought together.

<a id="sec:short"></a>

# Short papers and longer records

<span id="sec:production" label="sec:production"></span>

A writer also needs to establish the motivating problem’s relation to the chosen result. It may be an instance of a general theorem, a related but distinct target, a conditional consequence, or the object of a counterexample. For Problem 257 we retain the sufficient support condition in the opening, together with the universal question that it leaves open.

For Problem 269 the distinction is different: the component reports separate a general ordinary-proof result about distinct prime-power heights from a formalised special case, and separate both from the catalogue question involving repetitions \[paper269\]. Calling that question an instance of the general theorem would change the target relation. The stronger ordinary result also shows why a formal proof of a special case should not determine which theorem leads the paper.

The short-paper component report describes a deterministic renderer for such authored cards. It uses the existing assertion identifiers and source spans to prepare an opening and a proof outline, with the mechanism supplied by the author. Reported checks reject altered hypotheses and missing source passages. A deliberately false statement of the relation to the original problem nevertheless survived one source-binding test, because the explanatory text still pointed to unchanged source bytes.

In the Mersenne example, an intelligible opening must explain why rationality bounds the displacement away from zero and how averaging contradicts that bound. The source links identify where to check this account, but the writer has to supply it. This is the organisational work emphasised by Halmos and by Knuth, Larrabee and Roberts \[halmos; knuth\].

<a id="sec:long"></a>

# Assembly and navigation

The native assembler rebuilds a long manuscript from an ordered list of authored source parts and checks the markers used to split it back into its owners. Its freshness check compares the assembled text with the saved manuscript, allowing a reviewer to change one part while retaining a flat source file that ordinary TeX and extraction tools can read.

For navigation between papers, the component report permits automatic matching only when the complete sets of supporting declarations agree and the evidence classes and source coordinates are compatible. A partial overlap becomes a review candidate: linking to one lemma may be correct while leaving the rest of the short-paper claim unsupported. Ordinary proofs require an authored correspondence that binds the short statement, the long statement and the proof passage separately, so a later edit to any one invalidates the saved correspondence. Even a current match leaves the proof’s mathematical sufficiency to review. The navigator retains unlinked material, including failed approaches, rather than deleting it to make the coverage appear complete.

The navigator audit left correspondences unresolved. Missing history blocked some cross-link checks, and no papers were rendered in that component audit. It therefore established neither complete proof routes from short to long papers nor an improvement in reading.

<a id="sec:instance"></a>

# Observed checks and their limits

<div id="systems-scaling">

</div>

<a id="the-documented-source-inventory"></a>

## The documented source inventory

The supplied inventory records 8 problem worlds and 22 papers (8 short papers and 8 long records among them), with 1,903 Lean modules, 160 registered claims in eight statuses, and 19 open obligations. These quantities describe artefacts at the recorded cut.

The paper-coverage ledger has 699 statement occurrences: 502 exact formal supports, 141 specialisations, 23 results conditional on named inputs and 33 occurrences without recorded Lean support. Of the 643 exact or specialising occurrences, 620 have selected Comparator records and 23 remain queued. These classifications record a relation and its checking history, rather than executions performed for this paper.

The supplied companion’s semantic-coverage macros label 139,818 of 152,386 theorem-like declarations as interpreted (91.8%). It separates 3,330 directly anchored declarations from 136,488 contextually interpreted ones, leaving 12,568 structural-only declarations. The contextual category does not amount to an individual human reading or a proof-level explanation of every declaration. Likewise, the fixed-query semantic benchmark checks expected handles and dependencies, not a reader’s understanding.

At journal head `d3ad85269386`, the generated inventory reports 7 rounds and 25 returns, of which 18 were admitted and 7 remain unreviewed; 2 rounds are sealed. The journal is absent from this attachment, so these values are retained from the supplied JSON snapshot. They describe that journal’s coverage, which need not include every round mentioned in the private history.

<a id="the-historical-false-edit-experiment"></a>

## The historical false-edit experiment

The historical publication-evidence record reports that nine of the ten deliberately false edits were rejected and one escaped. The edits were applied separately, with the baseline restored between trials. The escaped edit changed a description of an unresolved step from “does not supply” to “completes”, and the publication checks accepted it. The edits were authored by the checker’s author, the original run logs were not retained, and the other nine edits were not rerun against the extended checklist. After the escape, the recorded follow-up checked the intact baseline and that particular edit against an added check. It did not repeat the entire experiment, so the record supplies no post-repair ten-of-ten result.

The sample comes from one corpus and one author’s selection of errors, with neither a manual-review control nor an ordinary continuous-integration comparator. It shows how the checks behaved on those particular edits. General reliability, reader understanding and mathematical transfer remain unmeasured.

<a id="component-checks"></a>

## Component checks

The component reports describe regeneration checks and altered-input tests, including runs under ordinary and optimised Python where stated. Those accounts are retained as reported results because the attachment omits some implementations and raw run outputs. They are separate from the manuscript checks run for this revision.

<a id="sec:loop"></a>

# Research revisions and reader evaluation

<span id="sec:cycle" label="sec:cycle"></span> <span id="systems-research-loop"></span><span id="systems-public"></span>

<a id="a-revision-remains-part-of-the-research-record"></a>

## A revision remains part of the research record

The public research-record tool maintains an append-only, hash-linked journal of submitted work and later review. In the supplied private excerpts, receipt of a return precedes judgement of its content, so rejected or superseded work remains available. A consumer disposition records what happened after review.

The loop component specifies the domain, quantifiers and assumptions of a task, together with any finite range or approximation regime, and retains that task when a fallback is offered. An agent may then return a valid special case without erasing the unanswered original question. Whether the return is in fact such a special case requires mathematical review.

For policy proposals, the reflection tool requires a causal-trial contract, evidence from separate batches and a clean replay before promotion. Directive and objective changes remain proposals for the operator. The component’s idempotent use-tracking demonstration concerns infrastructure use, and supplies no observation of outside uptake of a theorem.

Repeated rounds supply a revision history, but a comparison must keep the task fixed to establish whether a policy helps. We would retain useful generalisations as well as unsupported claims in that comparison, since a stricter prompt may suppress either.

<a id="sec:evaluation"></a>

## A paired protocol

The proposed comparison pairs ordinary research sessions on the same task, source revision, evidence limits and effort budget. To test organisation, the treatment could receive a structured dossier while the control receives the same facts as source excerpts. Changing exactly one permitted file is mechanically checkable. Whether that file changes only the intended intervention requires inspection of its content. A separate grader receives anonymised returns in counterbalanced order, with a frozen rubric and answer key but neither the arm label nor the desired outcome. Quoted passages tie each judgement to the returned text, and severe evidence errors or changes of mathematical meaning are considered separately from ordinal exposition scores. The design prepares these materials without paid model calls or a new provider runner; preparation time, review effort and existing subscriptions remain costs.

Anonymisation may fail when a distinctive phrase or extra navigation page reveals the arm. Session identifiers also provide limited evidence of independence, so the protocol preserves disagreements and requests another grading session when necessary. Historical grading by one analyst remains calibration material.

For the Mersenne example, we would ask a reader to state the support condition and explain why rationality bounds the displacement away from zero. We would then ask which universal question remains open and where the complete proof, with its assumptions, can be found. The answer key needs to be checked against the source theorem before dispatch.

Short and long versions of one result, together with repeated sessions on it, form one analysis cluster. The proposed paired analysis reserves its uncertainty interval for completed observations under stated independence and boundedness assumptions, and does not infer zero uncertainty from constant observed scores. Every issued assignment, missing return, timeout, invalid output and adjudication should remain in the record. The exposed corpus is development material; transfer requires unseen mathematics.

No independent writing comparison, blind grading run or cold-reader experiment is reported here. We would count against the intervention a failure to improve source-faithful reader decisions, an increase in severe errors, or preparation costs that outweigh its benefit. Prepared packets and fixed-query benchmark results do not answer these questions.

<a id="sec:related"></a>

# Related work

<a id="formal-libraries-blueprints-and-proof-support"></a>

## Formal libraries, blueprints and proof support

The mathlib paper motivates library abstractions through the mathematical constructions that need them \[mathlib\], while de Moura and Ullrich introduce Lean 4 through an executable example before developing its metaprogramming facilities \[lean4\]. Plectis uses their formal infrastructure to connect an authored account to its supporting declarations. LeanArchitect generates blueprint material from annotated Lean source and environment data \[leanarchitect\]. Our dossier also depends on authored explanations and machine-readable declarations, with additional records for nonformal arguments and unresolved evidence. The long-record correspondence has a narrower purpose: locating a passage that supports a particular short-paper claim.

Hattori, Matsuzaki and Fujiwara study natural-language translation and recursive summarisation of formal proofs \[hattori\], LeanMarathon addresses long-horizon autoformalisation \[leanmarathon\], and Proof-Refactor concerns modularising generated proofs \[proofrefactor\]. The writer component places its dependency-aware documentation task beside DocAgent \[p3docagent\]. These tasks can supply useful material, while the mathematical mechanism in the present writer remains authored.

LeanDojo extracts premise locations and proof states for retrieval-augmented proving \[leandojo\]. Lean Hammer, Aesop and Sledgehammer also concern premise use and proof automation \[leanhammer; aesop; judgementday\]. In a dossier, dependencies serve the different purpose of exposing a claim’s support to a writer; using a graph to judge mathematical importance would require further justification, as the analyses of Mathlib and the Isabelle Archive of Formal Proofs make relevant \[mathlibnetwork; huch\].

Kohlenbach’s proof-theoretic methods and the automatic generalisation work of Gandhi, Tadipatri and Gowers concern the assumptions and content of arguments \[kohlenbach; gandhi\]. At a more local level, Batteries’ `unusedArguments` linter, Plausible’s property tests and work on vacuity examine statements or their use \[batteries; plausible; beyondvacuity\]. A dossier can preserve such findings, but source hashes cannot perform those analyses.

<a id="research-agents-and-reusable-knowledge"></a>

## Research agents and reusable knowledge

Reusable mathematical material is the subject of lemma mining in HOL Light and theory exploration in Hipster \[lemmamining; hipster\]. DreamCoder studies library learning, while LEGO-Prover, DreamProver and ProofEvolve examine growing libraries or evolving proof procedures \[dreamcoder; legoprover; dreamprover; proofevolve\]. LeanConjecturer generates candidate statements \[leanconjecturer\]. We address the later publication task of explaining a selected result and retaining the evidence for that explanation.

AlphaEvolve evaluates generated code against executable objectives, and its mathematical exploration report connects computational constructions to subsequent analysis \[alphaevolve; alphaevolvemath\]. Proof-length-based interestingness and its relation to downstream utility are studied in Learning to Discover Interesting Mathematics \[interestingness; patel\], with Dream-RSI another approach to recursive improvement through evolving tasks \[dreamrsi\]. We treat such objectives as possible selection signals, whose value for a paper would still need an identified use and a reader test.

Agent Hunt organises collaborative autoformalisation through bounties, OpenProver maintains planner, worker and verifier state, and OProver combines retrieval with compiler feedback \[agenthunt; openprover; oprover\]. CircuitProver studies reusable proof knowledge in hardware verification \[circuitprover\]. Prove2Me offers an open collaborative formalisation platform and AXLE supplies cloud infrastructure for Lean utilities \[prove2me; axle\]. The present evaluation concerns the publication and revision of claims, leaving comparative theorem-proving performance untested.

The Aletheia case study distinguishes technical validity from the meaning of the intended problem, and Towards Autonomous Mathematics Research separates autonomy from significance \[aletheia; autonomousmath\]. Li and colleagues describe a human–AI interactive proving protocol \[lihai\]. The claim’s relation to the motivating problem belongs in the public account for the same reason: a valid neighbouring result may leave the original question unanswered. Tao’s community register of AI contributions provides an existing place where those distinctions affect how work is recorded \[taowiki\].

<a id="evaluation-and-mathematical-judgement"></a>

## Evaluation and mathematical judgement

RE-Bench supplies an example of research-agent evaluation with explicit tasks and budgets \[rebench\]; we use its official versioned abstract because the supplied extraction also contains an earlier internal draft. Berlot-Attwell and colleagues examine compute and behaviour in library-learning evaluation \[berlotattwell\]. The reader protocol relates its questions to repository-documentation evaluation, automated proof engineering and statement-autoformalisation assessment \[p6-swd; p6-ape; p6-poiroux\]. Its outcome is what a reader can recover from a paper.

The evaluation questions also draw on accounts of mathematical understanding. Kra asks what a result teaches, Riehl emphasises explanatory generality, Cohn discusses the burden of undigested output, and Sanderson argues for motivated explanations \[kra; cohn; sanderson; essays\]. Tao’s discussion of mining open problems and Litt’s account of new research possibilities give further context \[taomining; litt\]. These writings motivate questions; they supply no evidence that Plectis answers them.

The collected discussion includes the Fields medallists’ declaration, Chu’s dissenting viewpoint and the Royal Society letter, together with Gowers’s response \[fieldsdecl; chu; greenletter; gowers\]. Ringer considers the consequences of becoming a benchmark, Koukoulopoulos discusses shared research infrastructure, and Antieau examines the pace of mathematical work \[ringer; koukoulopoulos; antieau\]. Gowers also distinguishes legitimate problem-solving and theory-building aims \[essays\]. We preserve these differing perspectives without treating them as a unanimous policy for AI-assisted mathematics.

<a id="sec:limits"></a>

# Limits and conclusion

<span id="sec:conclusion" label="sec:conclusion"></span> <span id="systems-trust"></span>

With the pinned sources available, the implemented tools let a reader recover the declared support of an assertion and detect specified changes to it. They cannot guarantee that this evidence proves the prose, that the formalisation expresses the intended question, or that the explanation communicates the argument. An error shared by a statement and its annotation may survive.

This revision reports no new Lean or Comparator execution, comparative formalisation result or autonomous-optimisation experiment. The additional component designs retain their implementation and testing limits, the historical mutation sample is too narrow for a general reliability estimate, and the reader comparison remains unrun. Transfer to unseen mathematics and understanding by independent human readers are unresolved.

For the support theorem, successful exposition would leave the reader with its hypothesis, the displacement argument and the universal question still open. Plectis connects that account to records that can be inspected and revised. Whether these connections help authors produce mathematics that others understand and reuse is an empirical question.

<a id="app:credit"></a>

# Mathematical provenance in the research records

A publication record must preserve credit at a finer level than the problem number. For the totient work \[paper249\], the supplied attribution registry identifies Coons’s non-$`k`$-regularity theorem as the antecedent refined by the finite-level ranks \[coons\]. It distinguishes Martin’s separation theorem from the paper’s own Chinese-remainder and Dirichlet argument, whose mechanism is traced to Yazdani \[martin; yazdani\]. These are separate relations between earlier mathematics and the recorded result; they should remain separate when a paper is shortened.

The running-LCM record \[paper269\] retains Fan’s public priority for the two-prime case, even though its authors report an independent derivation. The recorded route passes through Hecke–Mahler series, with credit to Loxton and van der Poorten and to Bugeaud and Laurent \[fan269; loxtonvdp1977; bugeaudlaurent2023\]. The Erdős–Graham problem source remains distinct from the subsequent theorem \[erdosgraham\]. The earlier discussion also cites Akiyama and Kaneko’s report of Dubickas’s result on multiplicative approximation \[akiyamakaneko\]; this is background credit, not an additional proof of the running-LCM claim.

For the polynomial-lemniscate record, the historical question comes from Erdős, Herzog and Piranian and is catalogued as Problem 1041 \[ehp1958; erdos1041\]. The registry credits the public degree-seven construction to `ani` \[aniforum\]. It describes the formalised instance as a counterexample to the universal total-variation formulation, while leaving correspondence with the historical curve-length question unadjudicated. The related Formal Conjectures entry \[formalconjectures; fcpr\] is a separate recorded action; its status is not a substitute for that correspondence check.

The synthesis paper records connections across the eight problem records, including the periodic-chain theorem \[synthesis\]. A connection becomes useful to a later writer only when its assumptions and destination are recoverable. For that reason, the evidence record retains the cited work and the particular relation asserted, even when a later publication gives it less space.

<a id="app:repro"></a>

# Inspection and reproduction

The source manifest for this revision identifies commit `5beb950af93e`. It describes a local integration branch, not the current public main branch. The repository links retained in the bibliography include earlier pins and should be read at those stated revisions. The canonical entry points are the architecture guide, the paper registry and the selected paper’s evidence record.

Within the supplied public tree, `python3 scripts/systems_paper_evidence.py` checks this paper’s audited passages and their native source bindings. The source ledger additionally lists the supplied component reports and literature excerpts used for the revision, with packet-relative paths and digests. Those supplemental bindings are checked separately and are not evidence that the native checker executed the reported component tests. The revision report records both scopes.

The inventory command, `python3 scripts/build_systems_paper_counts.py`, normally rebuilds the displayed counts from their source owners. In this attachment it stops at the absent research journal. Dossier reproduction also needs the full pinned repository and imported helper modules that are outside this packet. The supplied generated counts have therefore been retained without editing; the available manuscript and source-binding checks have a narrower reproduction scope. The private editorial builder also imports a dissemination helper absent from the packet, so no offline execution of that builder is claimed. The native reader-study tool has an optional execution route requiring a separately authorised provider bridge; the manual comparison described here does not use that route.

The [navigation companion](../../../paper/systems/cold-clone-to-proof-receipt.pdf#nameddest=cold-clone-problem) gives the clone-to-proof route. The [strategy companion](../../../paper/systems/open-source-mathematics-strategy.pdf#nameddest=strategy-protocol) discusses participation and resource choices. They remain separately owned documents with their own dates and evidence limits. This revision changes neither companion.

<div class="thebibliography">

99 T. F. Bloom, *Erdős problems*, [erdosproblems.com](https://www.erdosproblems.com), accessed September 2026. W. Cook, *Weighted Support Criteria for Reciprocal Mersenne Subseries*, short paper on Erdős Problem 257, September 2026, [`PDF`](https://github.com/wcook04/plectis-erdos/blob/5acddfb2d9b43ad1b876f25700c49b1c39beddde/paper/257/erdos-257-mersenne-support-subseries.pdf). P. Erdős, *On the irrationality of certain series*, Math. Student 36 (1968), 222–226 (issued 1969), [scan](https://users.renyi.hu/~p_erdos/1969-09.pdf). D. Duverney and Y. Tachiya, *Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*, Forum Math. 31 (2019), 1557–1566, [DOI](https://doi.org/10.1515/forum-2018-0299). B. Kra, *Deep theorems were scarce and difficult and so became an effective mechanism to identify deep thought. AI has broken this system*, guest post on *What’s new*, 13 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/13/deep-theorems-were-scarce-and-difficult-and-so-became-an-effective-mechanism-to-identify-deep-thought-ai-has-broken-this-system/). H. Cohn, *The technical debt of AI-generated mathematics*, guest post on *What’s new*, 15 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/15/the-technical-debt-of-ai-generated-mathematics/). T. Tao, thread on mining open problems, Mathstodon, 8 September 2026, [thread](https://mathstodon.xyz/@tao/117237320796901560). Twenty-five Fields Medallists, *A severe misalignment of AI in mathematics*, declaration posted on *What’s new*, 11 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/11/a-severe-misalignment-of-ai-in-mathematics/). G. Sanderson, *If math is more than proof, we need to better celebrate the rest of it*, guest post on *What’s new*, 18 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/18/if-math-is-more-than-proof-we-need-to-better-celebrate-the-rest-of-it/). L. de Moura and S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, in *Automated Deduction, CADE 28*, Lecture Notes in Computer Science 12699, 2021, pp. 625–635, [DOI](https://doi.org/10.1007/978-3-030-79876-5_37). P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L’Enseignement Mathématique 28, 1980, p. 61. W. Cook, *Bases and Integral Relations for the $`k`$-Kernel of Euler’s Totient*, short paper on Erdős Problem 249, revised 18 September 2026, [`PDF`](https://github.com/wcook04/plectis-erdos/blob/5acddfb2d9b43ad1b876f25700c49b1c39beddde/paper/249/erdos-249-binary-totient-series.pdf). M. Coons, *(Non)Automaticity of number theoretic functions*, J. Théor. Nombres Bordeaux 22 (2010), 339–352, [DOI](https://doi.org/10.5802/jtnb.718), Theorem 3.2. G. Martin, *Simultaneous inequalities among values of the Euler phi-function*, 2006, [arXiv:math/0603053v1](https://arxiv.org/abs/math/0603053v1), Theorem 1. S. Yazdani, *Multiplicative functions and $`k`$-automatic sequences*, J. Théor. Nombres Bordeaux 13 (2001), 651–658, [Numdam](https://www.numdam.org/item/JTNB_2001__13_2_651_0/). W. Cook, *Reading Eight Erdős Problems Together*, synthesis paper, September 2026, [source, including the periodic-chain theorem](https://github.com/wcook04/plectis-erdos/blob/af1462ce/paper/synthesis/optimal-sparse-perturbations.tex). T. Feng, T. Trinh, G. Bingham, et al., *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the Erdős Problems*, 2026, [arXiv](https://doi.org/10.48550/arXiv.2601.22401). Lean FRO, *Comparator*, 2025, [GitHub](https://github.com/leanprover/comparator). `ammkrn`, *nanoda_lib*, an independent type checker for Lean 4, [GitHub](https://github.com/ammkrn/nanoda_lib). T. F. Bloom, *Erdős Problem \#1041*, [erdosproblems.com](https://www.erdosproblems.com/1041), accessed September 2026. P. Erdős, F. Herzog and G. Piranian, *Metric properties of polynomials*, J. Analyse Math. 6 (1958), 125–148, [DOI](https://doi.org/10.1007/BF02790232). `ani`, post in the Problem 1041 discussion thread, 7 September 2026, [erdosproblems.com forum](https://www.erdosproblems.com/forum/thread/1041#post-8861). Formal Conjectures, pull request 6505, *Erdős 1041: mark solved with answer(False) and link a formal proof*, merged 23 September 2026, [GitHub](https://github.com/google-deepmind/formal-conjectures/pull/6505). T. Zheng, X. Wu, Z. Zhang, et al., *Dream-RSI: Recursive Self-Improvement through Evolving Worlds*, 2026, [arXiv:2609.14858](https://arxiv.org/abs/2609.14858). J. H. Loxton and A. J. van der Poorten, *Arithmetic properties of certain functions in several variables III*, Bull. Austral. Math. Soc. **16** (1977), 15–47. Y. Bugeaud and M. Laurent, *Transcendence and continued fraction expansion of values of Hecke–Mahler series*, Acta Arith. **209** (2023), 59–90. W. Cook, *The Three-Prime Running LCM*, short paper on Erdős Problem 269, September 2026, [`PDF`](https://github.com/wcook04/plectis-erdos/blob/5acddfb2d9b43ad1b876f25700c49b1c39beddde/paper/269/erdos-269-three-prime-running-lcm.pdf). S. Fan, comment on Erdős Problem \#269, erdosproblems.com forum, 26 June 2026, [forum post](https://www.erdosproblems.com/forum/thread/269#post-7218). N. Patel, A. Rammal, A. Hayat, R. Munos, and J. Kempe, *Learning to Discover Interesting Mathematics*, arXiv:2609.28603v1, 2026, <https://arxiv.org/abs/2609.28603>. S. Chen, K. Marwaha, X. Lu, H. Yuen, and T. Peng, *Prove2Me: An Open Collaborative Platform for Scaling Math Formalization*, 2026, [arXiv](https://doi.org/10.48550/arXiv.2608.28433). T. Feng, T. H. Trinh, G. Bingham, et al., *Towards Autonomous Mathematics Research*, 2026, [arXiv](https://doi.org/10.48550/arXiv.2602.10177). T. Tao, *AI contributions to Erdős problems*, [GitHub](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems), accessed September 2026. T. Ringer, *Becoming a benchmark*, guest post on *What’s new*, 17 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/17/becoming-a-benchmark/). P. Massot, *leanblueprint*, plasTeX plugin for Lean formalisation blueprints, 2020, [software repository](https://github.com/PatrickMassot/leanblueprint). Y. Zhang, Y. Sun, T. Suzuki, J. D. Lee, and F. Liu, *LeanMarathon: Toward Reliable AI Co-Mathematicians through Long-Horizon Lean Autoformalization*, 2026, [arXiv:2606.05400](https://arxiv.org/abs/2606.05400). S. Hattori, T. Matsuzaki, and M. Fujiwara, *Natural Language Translation of Formal Proofs through Informalization of Proof Steps and Recursive Summarization along Proof Structure*, in *Proceedings of the 18th International Natural Language Generation Conference*, 2025, pp. 376–389, [ACL Anthology](https://aclanthology.org/2025.inlg-main.23/). S. Akiyama and H. Kaneko, *Multiplicative analogue of Markoff–Lagrange spectrum and Pisot numbers*, Adv. Math. 380 (2021), 107547, p. 3, reporting the theorem of A. Dubickas, J. Number Theory 117 (2006), 222–239, [arXiv:1911.06170v6](https://arxiv.org/abs/1911.06170v6). K. Yang et al., *LeanDojo: Theorem Proving with Retrieval-Augmented Language Models*, NeurIPS 2023, Datasets and Benchmarks Track, [arXiv:2306.15626](https://arxiv.org/abs/2306.15626). C. Li, Z. Lai, D. An, J. Hu, and Z. Wen, *Advancing Mathematical Research via Human-AI Interactive Theorem Proving*, 2025, [arXiv:2512.09443v2](https://arxiv.org/abs/2512.09443v2). U. Kohlenbach, *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*, Springer Monographs in Mathematics, Springer, Berlin, 2008. A. Gandhi, A. R. Tadipatri, and T. Gowers, *Automatically Generalizing Proofs and Statements*, in *16th International Conference on Interactive Theorem Proving*, LIPIcs 352, 2025, pp. 12:1–12:18, [DOI](https://doi.org/10.4230/LIPIcs.ITP.2025.12). Lean community, *Batteries*, the `unusedArguments` linter in `Batteries/Tactic/Lint/Misc.lean`, [GitHub](https://github.com/leanprover-community/batteries), accessed September 2026. J. Xin, A. Schneidman, C. Cummins, K. Ram, S. Ganesh, and J. Limperg, *AXLE: A Cloud Infrastructure for Lean 4 Theorem Proving Utilities*, 2026, [arXiv:2606.26442](https://arxiv.org/abs/2606.26442). X. Li, N. Peng, S. Severini, and P. Shafto, *The Network Structure of Mathlib*, 2026, [arXiv:2604.24797](https://arxiv.org/abs/2604.24797). F. Huch, *Structure in Theorem Proving: Analyzing and Improving the Isabelle Archive of Formal Proofs*, extended abstract, 2022, [arXiv:2209.13305](https://arxiv.org/abs/2209.13305). J. de Kleer, *An assumption-based TMS*, Artificial Intelligence 28 (1986), 127–162, [DOI](https://doi.org/10.1016/0004-3702(86)90080-9). A. Mokhov, N. Mitchell, and S. Peyton Jones, *Build Systems à la Carte*, Proc. ACM Program. Lang. 2 (ICFP), 2018, article 79, [DOI](https://doi.org/10.1145/3236774). T. Zhu, J. Clune, J. Avigad, A. Q. Jiang, and S. Welleck, *Premise Selection for a Lean Hammer*, 2025, revised 2026, [arXiv:2506.07477](https://arxiv.org/abs/2506.07477). J. Limperg and A. H. From, *Aesop: White-Box Best-First Proof Search for Lean*, in *Proceedings of the 12th ACM SIGPLAN International Conference on Certified Programs and Proofs*, 2023, pp. 253–266, [DOI](https://doi.org/10.1145/3573105.3575671). Lean community, *Plausible*, a property testing framework for Lean 4, [GitHub](https://github.com/leanprover-community/plausible), accessed September 2026. H. Chockler, A. Gurfinkel, and O. Strichman, *Beyond Vacuity: Towards the Strongest Passing Formula*, Form. Methods Syst. Des. 43 (2013), 552–571, [DOI](https://doi.org/10.1007/s10703-013-0192-6). C. Kaliszyk and J. Urban, *Lemma Mining over HOL Light*, LPAR-19, LNCS 8312, 2013, pp. 503–517, [DOI](https://doi.org/10.1007/978-3-642-45221-5_34). M. Johansson, D. Rosén, N. Smallbone, and K. Claessen, *Hipster: Integrating Theory Exploration in a Proof Assistant*, CICM 2014, LNCS 8543, pp. 108–122, [DOI](https://doi.org/10.1007/978-3-319-08434-3_9). K. Ellis et al., *DreamCoder: Growing Generalizable, Interpretable Knowledge with Wake-Sleep Bayesian Program Learning*, 2020, [arXiv:2006.08381](https://arxiv.org/abs/2006.08381). H. Wang, H. Xin, et al., *LEGO-Prover: Neural Theorem Proving with Growing Libraries*, ICLR 2024, [arXiv:2310.00656](https://arxiv.org/abs/2310.00656). Y. Zhang, J. Sun, et al., *DreamProver: Evolving Transferable Lemma Libraries via a Wake-Sleep Theorem-Proving Agent*, 2026, [arXiv:2604.26311](https://arxiv.org/abs/2604.26311). W. Ye, Z. Guan, et al., *ProofEvolve: Neuro-Symbolic Evolution for Formal Automated Theorem Proving*, 2026, [arXiv:2608.26334](https://arxiv.org/abs/2608.26334). S. Böhme and T. Nipkow, *Sledgehammer: Judgement Day*, IJCAR 2010, LNCS 6173, pp. 107–121, [DOI](https://doi.org/10.1007/978-3-642-14203-1_9). I. Berlot-Attwell, T. Sesterhenn, F. Rudzicz, and X. Si, *Is This LLM Library Learning? Evaluation Must Account For Compute and Behaviour*, EACL 2026, pp. 3534–3568, [DOI](https://doi.org/10.18653/v1/2026.eacl-long.163). Y. Fu, P. Liu, Z. Wang, and K. Yuan, *Proof-Refactor: Refactoring Generated Formal Proofs into Modular Artifacts*, 2026, [arXiv:2606.03743](https://arxiv.org/abs/2606.03743). N. Onda et al., *LeanConjecturer: Automatic Generation of Mathematical Conjectures for Theorem Proving*, 2025, [arXiv:2506.22005](https://arxiv.org/abs/2506.22005). D. Litt, *A beginning for mathematics*, 13 September 2026, [blog post](https://www.daniellitt.com/blog/2026/9/13/a-beginning-for-mathematics/). T. Chu, *The AI dissenter viewpoint*, *Proofs and Prompts*, 9 August 2026, [blog post](https://proofsandprompts.com/2026/08/09/the-ai-dissenter-viewpoint/). B. Green and forty-one other Fellows and Foreign Members of the Royal Society, *Open letter to Sir Paul Nurse, President of the Royal Society*, *Proofs and Prompts*, 17 September 2026, [blog post](https://proofsandprompts.com/2026/09/17/open-letter-to-sir-paul-nurse-president-of-the-royal-society/). W. T. Gowers, *Why I didn’t sign the Fields medallists’ letter*, 17 September 2026, [blog post](https://gowers.wordpress.com/2026/09/17/why-i-didnt-sign-the-fields-medallists-letter/). D. Koukoulopoulos, *A CERN for AI-assisted science?*, guest post on *What’s new*, 17 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/17/a-cern-for-ai-assisted-science/). B. Antieau, *Fast math/slow math*, 15 September 2026, [blog post](https://antieau.github.io/2026/09/15/fast-math-slow-math.html). D. E. Knuth, T. Larrabee and P. M. Roberts. *Mathematical Writing*. Stanford report CS1193, based on the autumn 1987 course, Section 1. Dayu Yang et al., *DocAgent: A Multi-Agent System for Automated Code Documentation Generation*, arXiv:2504.08725v3, 2025, Sections 2–3. Xinchen Wang, Ruida Hu, Cuiyun Gao, Pengfei Gao, and Chao Peng. *Evaluating Repository-level Software Documentation via Question Answering and Feature-Driven Development*. arXiv:2604.06793v1, 2026. Huajian Xin, Luming Li, Xiaoran Jin, Jacques Fleuriot, and Wenda Li. *APE-Bench: Evaluating Automated Proof Engineering for Formal Math Libraries*. arXiv:2504.19110v3, 2026. Auguste Poiroux, Gail Weiss, Viktor Kunčak, and Antoine Bosselut. *Reliable Evaluation and Benchmarks for Statement Autoformalization*. arXiv:2406.07222v3, 2025.

T. Zhu, P. Monticone, J. Avigad and S. Welleck. *LeanArchitect: Automating Blueprint Generation for Humans and AI*. [arXiv:2601.22554v1](https://arxiv.org/abs/2601.22554v1), 2026, Methods and Case Studies. M. Bolan et al. *The Equational Theories Project: Advancing Collaborative Mathematical Research at Scale*. [arXiv:2512.07087v2](https://arxiv.org/abs/2512.07087v2), 2025, Project Management and Data Management. The mathlib Community. *The Lean Mathematical Library*. CPP 2020. DOI: [10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). Google DeepMind. *Formal Conjectures*. [Repository README](https://github.com/google-deepmind/formal-conjectures), consulted 29 September 2026; descriptive context only. A. Novikov et al. *AlphaEvolve: A coding agent for scientific and algorithmic discovery*. [arXiv:2506.13131v1](https://arxiv.org/abs/2506.13131v1), 2025, Task Specification and Evolution. B. Georgiev, J. Gómez-Serrano, T. Tao and A. Z. Wagner. *Mathematical exploration and discovery at scale*. [arXiv:2511.02864v3](https://arxiv.org/abs/2511.02864v3), 2025. N. Patel, A. Rammal, A. Hayat, R. Munos and J. Kempe. *Learning to Discover Interesting Mathematics*. [arXiv:2609.28603v1](https://arxiv.org/abs/2609.28603v1), 2026, Interestingness-Driven Mathematical Discovery. C. E. Brown, C. Kaliszyk and J. Urban. *Agent Hunt: Bounty Based Collaborative Autoformalization With LLM Agents*. [arXiv:2603.06737v1](https://arxiv.org/abs/2603.06737v1), 2026. M. Kripner and M. Straka. *OpenProver: Agentic and Interactive Theorem Proving with Lean 4*. [arXiv:2607.09217v1](https://arxiv.org/abs/2607.09217v1), 2026, State and Memory Management. D. Ma et al. *OProver: A Unified Framework for Agentic Formal Theorem Proving*. [arXiv:2605.17283v1](https://arxiv.org/abs/2605.17283v1), 2026, Introduction. Z. Yang et al. *CircuitProver: Agentic Lean 4 Theorem Proving with Reusable Circuit Proof Library for Hardware Verification*. [arXiv:2607.27259v1](https://arxiv.org/abs/2607.27259v1), 2026. H. Wijk et al. *RE-Bench: Evaluating frontier AI R&D capabilities of language model agents against human experts*. [arXiv:2411.15114v1](https://arxiv.org/abs/2411.15114v1), 2024; official abstract used here. P. R. Halmos. *How to Write Mathematics*. L’Enseignement Mathématique 16 (1970), 123–152; sections on organising a mathematical presentation. Various authors. *Writings on AI and Mathematics*. Supplied anthology, `AI_ESSAYS_SOURCE.pdf`, snapshot 22 September 2026; Kra, pp. 31–33; Riehl, pp. 39–40; Cohn, pp. 41–44; Gowers, pp. 55–60; Sanderson, pp. 73–77.

</div>
