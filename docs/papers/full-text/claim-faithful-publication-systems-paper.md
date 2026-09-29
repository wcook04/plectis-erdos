<a id="claim-faithful-publication-systems-paper"></a>

# Problem-Sized Lean Worlds

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Plectis organises mathematical source, evidence and exposition into a persistent problem-sized world whose main reader-facing outputs are a short paper and a complete reasoning record. The working route connects authored claims to Lean declarations and selected Comparator receipts, assembles long records from reviewable parts, and preserves returned work with its review and attribution. The intended writing route selects a general result, explains its mechanism and hard step, locates the motivating problem as an instance, and preserves the exact evidence boundary. We describe which parts of that route exist in the attached source snapshot, which require editorial judgement, and which remain interface contracts. This revision adds source-bound prose auditing and generated inventory counts to make unsupported changes visible during revision. A paired-packet protocol evaluates ordinary research-session returns without paid model calls; it has no completed comparative result in this report. The contribution is an inspectable research-to-paper workflow with explicit evidence limits; improved exposition, discovery and reader understanding remain hypotheses for evaluation.

<a id="sec:intro"></a>

# A research record that can become a paper

The practical question is how an existing mathematical corpus becomes a paper that another mathematician can understand, check and reuse. For this purpose a problem-sized world contains the problem, established results, scoped failed routes, literature, proof evidence and open obligations, rather than only a list of successful declarations. The short paper carries the mathematical argument a reader should remember, while the long record preserves the fuller development and provenance.

Problem 257 supplies a concrete example: for a finite nonempty set of primes $`P`$, write $`h_P(a)=\prod_{p\in P}p^{v_p(a)}`$ and $`X_A(b)=\sum_{a\in A}(b^a-1)^{-1}`$. The short paper states that convergence of $`\sum_{a\in A}h_P(a)/[a(2^{h_P(a)}-1)]`$ implies irrationality of $`X_B(b)`$ for every integer $`b\ge2`$ and every infinite $`B\subseteq A`$. Its proof makes positive displacements small by averaging over multiples of a modulus, with a further dyadic average controlling incomplete periods. The universal infinite-support problem remains outside that sufficient criterion, and failure of the criterion is not evidence of rationality.

This example fixes the writing objective: preserve the general theorem, make the hard step intelligible, distinguish it from antecedents, and state the remaining problem exactly. It supplies no measurement of whether Plectis made the theorem easier to discover or understand.

<a id="sec:predigestion"></a>

# Pre-digestion: selecting a usable result

<span id="sec:world" label="sec:world"></span><span id="sec:graph" label="sec:graph"></span>

The existing problem index joins authored questions and boundaries to derived module paths, paper routes, digests and recorded checking dispositions. The argument-continuation machinery builds a graph from an elaborated export and records the source identity and limits of that export. A relation row distinguishes a replacement hypothesis, an endpoint route and an equivalence inside the stated context. An atlas listing with a matching signature and a reachable build target is an attestation to the source projection; it does not establish that a particular continuous-integration run compiled the module.

The round contract proposes a per-problem dossier containing each result’s statement, generality, mechanism, hard step, evidence, consumers, attribution and open questions. That dossier should be an editorial selection over the existing corpus, with a reason for retaining or excluding each candidate result. Retrieval alone cannot establish that a result is the most useful abstraction or that the literature comparison is complete. The proposed acceptance test therefore requires an exact source statement, a supported generality relation and a named potential consumer, with missing information left explicit. This report does not treat the parallel dossier implementation as already delivered.

<a id="sec:checks"></a>

# From verification to a claim

<div id="systems-lifecycle">

</div>

The evidence renderer reads the paper-to-Lean coverage ledger and produces formal-evidence sidecars and result records. A Comparator mark requires all recorded declarations for the result to resolve to a challenge, a solution and an accepted replay receipt with matching source digests. It also requires agreement between the declaration statement at the paper’s Lean pin and the statement compiled by the compared corpus, after comments and layout are removed. The renderer collects failures and writes nothing when resolution fails.

The ledger distinguishes exact correspondence, an exact-or-specialising correspondence, a result depending on a named input, and a result with no Lean statement. A statement digest detects a changed assertion; the mathematical judgement that a declaration corresponds to the assertion still needs review. Lean checks the formal proposition supplied to it, whereas agreement with the intended mathematics and the quality of its explanation remain separate questions. A named open input must remain visible in the prose, and an ordinary argument cannot acquire a Lean or Comparator label merely because it is adjacent to a checked theorem.

The historical publication-evidence record reports that nine of the ten deliberately false edits were rejected and one escaped. The edits were authored by the checker’s author, the original run logs were not retained, and the other nine edits were not rerun against the extended checklist. This record identifies a missing coverage rule and provides no estimate of general reliability.

<a id="sec:short"></a>

# Writing the short paper

<span id="sec:production" label="sec:production"></span>

The supplied essays motivate this objective from different perspectives: Kra asks what a result teaches, Riehl emphasises explanatory generality, Cohn treats undigested output as a burden on readers, and Sanderson argues for recognising motivated explanations \[essays\]. Gowers distinguishes legitimate problem-solving and theory-building aims, so these views provide editorial questions rather than a unanimous policy about AI-assisted mathematics \[essays\].

The supplied private machinery contains a source-frozen editorial packet builder and a writing brief that prioritises the strongest established contribution, its antecedents and its hard idea. This is machinery for assigning and packaging editorial work; the attached source does not establish a complete automatic writer from the new dossier contract. The builder also imports a dissemination helper that is absent from the supplied private archive, so this report does not claim a successful offline run of that builder.

The proposed short-paper writer consumes the dossier and claim-evidence rows, then drafts a theorem-led account in which the motivating problem is an application of the general result. The drafting order should be mathematical question, general statement with hypotheses, mechanism, hard step, comparison with antecedents, and the exact open boundary. For the weighted-support example, the short paper should explain why incomplete periods require the second average before listing supplementary finite-denominator results. The long record can retain those supplementary developments without making the short paper an inventory of everything that was proved.

A structural linter can detect missing evidence fields, unsupported status changes and forbidden register patterns, while explanatory adequacy still needs a reader. A successful revision should enable a cold reader to recover the statement, its mechanism, its difficult step and its limitations without consulting the originating conversation.

<a id="sec:long"></a>

# Assembling the long record

The native assembler writes flat long manuscripts from authored reasoning parts and retains a visible marker before each part. Its check mode compares the generated manuscript with the assembled result and acts as a freshness gate. This arrangement lets a reviewer revise a bounded part while keeping a manuscript that ordinary TeX and text-extraction tools can read.

Assembly freshness does not imply that the long record agrees mathematically with the short paper. The proposed cross-paper check should join stable result identifiers and compare statements, assumptions, evidence classes and open boundaries before either manuscript is released. A deletion from the short paper should preserve the long-record result or record an explicit correction; it should not erase the history of a failed route. The short and long versions may use different explanations while citing the same supported mathematical assertion.

<a id="sec:loop"></a>

# The review and improvement loop

<span id="sec:cycle" label="sec:cycle"></span>

<div id="systems-research-loop">

</div>

<div id="systems-public">

</div>

The public research record maintains an append-only hash-linked journal of packets, returns, reviews and consumer dispositions. The supplied private intake tool preserves return bytes before judgement, and its reflection tool consumes outcome records separately from custody. The reflection tool can examine outcomes, policies, mathematics, context, assimilation, infrastructure and objectives, while changes to directives and objectives remain operator proposals. Its documented promotion rule requires a causal-trial contract, evidence from separate batches and a clean replay before a candidate policy becomes active.

For paper work, the proposed loop is to freeze inputs, commission a bounded revision, preserve its return, check changed claims, review its exposition, and either integrate or reject the change with reasons. An accepted component still needs a recorded consumer and an integration decision; acceptance does not itself show that a paper changed or a reader benefited. Policy changes should be tested against retained difficult cases as well as the latest successful return, because making a prompt stricter can suppress useful work. The existence of repeated rounds is evidence of an iterative process, not evidence that the process improves automatically.

<a id="sec:evaluation"></a>

# Evaluation through ordinary research packets

The existing semantic benchmark runs fixed queries and checks for expected source handles, statuses and dependency entries. Such a check can reveal broken navigation, but it does not measure reader understanding or the usefulness of a paper. The native reader-study tool prepares digest-bound materials and analysis, and its optional execution path requires a separately authorised provider bridge. The operator’s revised protocol uses the ordinary Type B research sessions as subjects and requires no paid model calls or new provider runner.

For a component comparison, both packets receive the same task, source revision, evidence boundary, budget and frozen rubric, with one declared input difference. The corresponding source-only control and structured-dossier treatment should contain the same mathematical facts when the estimand is the effect of organisation. A separate grader receives anonymised outputs in counterbalanced order, together with the frozen answer key and rubric; it receives neither the producing arm label nor the desired result. Severe mathematical or evidence-status errors are reported separately from exposition scores and cannot be cancelled by fluent prose.

The primary observations are whether a reader can state the general result, identify the hard step, locate its evidence and distinguish the remaining open question. Related short and long papers, repeated sessions and equivalent formulations are clustered by mathematical lineage instead of being treated as independent discoveries. Every issued assignment, missing return, timeout, invalid output and adjudication should remain in the record, together with preparation and review effort. Ordinary session access avoids additional model-call charges in this design, while human time and any existing subscription remain costs. A before-and-after writing round can show revision progress, whereas a causal claim about a component requires the matched comparison rather than different tasks assigned to different components. The protocol would count against the upgrade if source-faithful reader decisions did not improve, if severe errors increased, or if additional preparation outweighed the recorded benefit. No comparative scores or reader gains are reported for this revision.

<a id="sec:instance"></a>

# What the attached snapshot establishes

The attached snapshot indexes 8 problem worlds and registers 22 paper entries, including 8 short problem papers and 8 long reasoning records. The paper-to-Lean ledger contains 710 assertion occurrences: 511 exact rows, 143 exact-or-specialising rows, 25 rows depending on a named input, and 31 rows without a Lean statement. Its recorded Comparator dispositions are 633 compared and 21 pending among the 654 exact and exact-or-specialising rows. These counts are generated by the native counts builder and do not measure mathematical importance, completeness of the literature review or exposition quality.

At recorded journal head `9a0a2617ea30`, the source journal contains 7 opened rounds, 2 sealed rounds and 25 returns, with 18 admitted for integration and 7 without a recorded review. Those journal counts do not claim complete capture of all rounds mentioned in the private history. The revised paper records its prose as explicit source-bound units and checks for changed text, missing bindings, duplicate identifiers and changed evidence bytes. The associated source excerpts distinguish the supplied private machinery and literature from local run receipts. This auditing mechanism is a review aid: a maintainer who changes both an assertion and its supporting annotation can still introduce a shared mistake.

<a id="sec:related"></a>

# Relation to prior systems

LeanArchitect is the nearest listed comparator for synchronising exposition with formal declarations: its annotations and environment data support dependency extraction and generated blueprint text \[leanarchitect\]. Plectis adds a different publication path around mixed evidence classes, separately recorded statement comparison, short and long paper roles, and the custody of unresolved returned work. This combination has not been shown to produce clearer papers or better formalisation performance than LeanArchitect.

The Equational Theories Project is a stronger precedent for demonstrated collaborative exploration, including implication and non-implication data, Lean validation and shared project management \[etp\]. Persistence, correction and formal checking therefore cannot serve as standalone novelty claims for Plectis. The mathlib community supplies the reusable formal library and maintenance model on which problem-specific developments can build, while Formal Conjectures supplies formal problem statements \[mathlib; formalconjectures\].

AlphaEvolve improves code against executable evaluators and stores evaluated candidates in an evolutionary database, while its mathematical exploration report studies constructions and subsequent mathematical analysis \[alphaevolve; alphaevolvemath\]. The present paper-writing loop does not demonstrate comparable autonomous optimisation, and grammatical quality alone is not a trustworthy executable evaluator of mathematical exposition. Learning to Discover Interesting Mathematics proposes proof-length-based interestingness and studies its relation to downstream utility in formal libraries \[interestingness\]. Plectis treats such a score as a possible selection signal whose value for a short paper would still need a named consumer and a reader test.

Agent Hunt distributes autoformalisation through bounties, OpenProver maintains planner, worker and verifier state, and OProver incorporates retrieval and compiler feedback into formal proving \[agenthunt; openprover; oprover\]. CircuitProver explicitly studies reusable proof knowledge in hardware verification, so storing reusable lemmas is also an established direction \[circuitprover\]. The differentiating question here is how the resulting research record becomes trustworthy exposition, not whether this workflow proves more theorems than those systems.

RE-Bench illustrates the importance of explicit tasks, budgets and comparators in evaluating research agents; its official versioned abstract is used here because the attached extraction includes an earlier internal draft \[rebench\]. Halmos' account of mathematical writing supports treating the organisation of an argument as substantive work rather than assuming a proof transcript is already a finished paper \[halmos\].

<a id="sec:limits"></a>

# Limits and conclusion

<span id="sec:conclusion" label="sec:conclusion"></span>

<div id="systems-trust">

</div>

<div id="systems-scaling">

</div>

This report is scoped to an attached source snapshot and accompanying records, with no assertion that the snapshot is the present public main branch. The ordinary arguments, historical checking receipts and source-index classifications are reported at their own evidence levels; this revision contains no fresh Lean or Comparator result. The dossier generator, short-paper generator and prospective paired evaluation remain separately owned work until their implementations and returns are available. Better scores within a familiar corpus would still leave transfer to unseen mathematical material and understanding by independent human readers unsettled.

The useful completed object is a faithful paper together with the evidence needed to inspect it and the record needed to revise it. For Plectis, the next test is whether evidence-preserving pre-digestion and editorial revision make the existing mathematics easier to understand and reuse. Additional corpus volume and repeated packet production cannot answer that question by themselves.

<a id="app:repro"></a>

# Inspection routes and reproduction

The human entry points are `docs/ARCHITECTURE.md`, the problem-paper registry and the selected paper’s evidence record. The local command `python3 scripts/build_systems_paper_counts.py` checks the displayed inventory against the current source owners, and its snapshot option records the source digests. The command `python3 scripts/systems_paper_evidence.py` checks the explicit prose inventory and source bindings without executing any command listed as evidence. The section contract assigns pre-digestion, claim evidence, short writing, long assembly, loop and evaluation to their respective component owners, while the whole-paper editor controls the thesis and cross-section consistency. The navigation companion should retain clone-to-receipt instructions, the strategy companion should retain participation and resource choices, and the compact evidence-boundary companion should direct readers to a single claim’s support. For the external reader, the [navigation companion](../../../paper/systems/cold-clone-to-proof-receipt.pdf#nameddest=cold-clone-problem) gives an executable entry route and the [strategy companion](../../../paper/systems/open-source-mathematics-strategy.pdf#nameddest=strategy-protocol) describes participation choices.

<div class="thebibliography">

99 T. Zhu, P. Monticone, J. Avigad and S. Welleck. *LeanArchitect: Automating Blueprint Generation for Humans and AI*. [arXiv:2601.22554v1](https://arxiv.org/abs/2601.22554v1), 2026, Methods and Case Studies. M. Bolan et al. *The Equational Theories Project: Advancing Collaborative Mathematical Research at Scale*. [arXiv:2512.07087v2](https://arxiv.org/abs/2512.07087v2), 2025, Project Management and Data Management. The mathlib Community. *The Lean Mathematical Library*. CPP 2020. DOI: [10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). Google DeepMind. *Formal Conjectures*. [Repository README](https://github.com/google-deepmind/formal-conjectures), consulted 29 September 2026; descriptive context only. A. Novikov et al. *AlphaEvolve: A coding agent for scientific and algorithmic discovery*. [arXiv:2506.13131v1](https://arxiv.org/abs/2506.13131v1), 2025, Task Specification and Evolution. B. Georgiev, J. Gómez-Serrano, T. Tao and A. Z. Wagner. *Mathematical exploration and discovery at scale*. [arXiv:2511.02864v3](https://arxiv.org/abs/2511.02864v3), 2025. N. Patel, A. Rammal, A. Hayat, R. Munos and J. Kempe. *Learning to Discover Interesting Mathematics*. [arXiv:2609.28603v1](https://arxiv.org/abs/2609.28603v1), 2026, Interestingness-Driven Mathematical Discovery. C. E. Brown, C. Kaliszyk and J. Urban. *Agent Hunt: Bounty Based Collaborative Autoformalization With LLM Agents*. [arXiv:2603.06737v1](https://arxiv.org/abs/2603.06737v1), 2026. M. Kripner and M. Straka. *OpenProver: Agentic and Interactive Theorem Proving with Lean 4*. [arXiv:2607.09217v1](https://arxiv.org/abs/2607.09217v1), 2026, State and Memory Management. D. Ma et al. *OProver: A Unified Framework for Agentic Formal Theorem Proving*. [arXiv:2605.17283v1](https://arxiv.org/abs/2605.17283v1), 2026, Introduction. Z. Yang et al. *CircuitProver: Agentic Lean 4 Theorem Proving with Reusable Circuit Proof Library for Hardware Verification*. [arXiv:2607.27259v1](https://arxiv.org/abs/2607.27259v1), 2026. H. Wijk et al. *RE-Bench: Evaluating frontier AI R&D capabilities of language model agents against human experts*. [arXiv:2411.15114v1](https://arxiv.org/abs/2411.15114v1), 2024; official abstract used here. P. R. Halmos. *How to Write Mathematics*. L’Enseignement Mathématique 16 (1970), 123–152; sections on organising a mathematical presentation. Various authors. *Writings on AI and Mathematics*. Supplied anthology, `AI_ESSAYS_SOURCE.pdf`, snapshot 22 September 2026; Kra, pp. 31–33; Riehl, pp. 39–40; Cohn, pp. 41–44; Gowers, pp. 55–60; Sanderson, pp. 73–77.

</div>
