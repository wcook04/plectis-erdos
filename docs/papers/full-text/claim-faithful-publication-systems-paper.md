<a id="claim-faithful-publication-systems-paper"></a>

# A Repository-Based System for Research and Publication

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We describe a repository-based research system that connects questions, proofs, computations and failed approaches to reviewed claims and publications. The public Plectis prototype implements this workflow for eight mathematical programmes using structured records, Python command-line tools and Lean. Task routing and source indexes locate relevant work; optional recorded proof sessions retain submitted inputs and Lean results. Maintainers review proposed changes, update evidence bindings, regenerate derived files and inspect the publications; a contribution journal retains explicitly recorded outcomes, limitations and credit. A worked theorem distinguishes publication checks from mathematical review: its registered formal supports can remain linked after a paraphrase drops an essential hypothesis. A historical author-run test rejected nine of ten false edits and accepted one false completion claim. Reader benefit, discovery rate and adoption by independent laboratories remain unmeasured.

<a id="sec:intro"></a>

# Introduction

<div id="systems-lifecycle">

</div>

A research repository must support several activities: choosing a question, recovering earlier work, testing an argument, reviewing a claim and publishing an explanation. Their outputs need to remain connected when a proof, experiment or manuscript changes. Otherwise a new contributor must reconstruct the history, and a correct result can acquire a misleading description. Plectis is the public repository prototype studied here. It keeps questions, prior sources, computations, proofs and unresolved steps together, with records of proposed contributions and their review. Its implemented scope is the research and publication workflow in this repository; broader autonomous discovery and services for other scientific fields are proposals (Section <a href="#sec:limits" data-reference-type="ref" data-reference="sec:limits">9</a>). The architecture separates stored research artifacts, tools that locate or check them, and decisions made by authors and maintainers. Figure <a href="#fig:lifecycle" data-reference-type="ref" data-reference="fig:lifecycle">1</a> follows a selected result into publication and back through contributions. Source consistency, mathematical validity and the usefulness of an explanation remain distinct responsibilities.

<figure id="fig:lifecycle" data-latex-placement="htbp">

<figcaption>From accumulated work to a paper and subsequent revision. Labels name what passes between the stages; the arrows imply neither logical deduction nor automatic approval. The source and evidence records support review; they do not establish the intended meaning of the prose.</figcaption>
</figure>

Erdős Problems supplies the questions and their public discussion, while Lean and mathlib supply the formal language and library \[erdosproblems; lean4; mathlib\]. Formalisation blueprints link a written mathematical argument to named Lean declarations \[leanblueprint; leanarchitect\]. Persistent problem records and open agent collaboration have antecedents in the Equational Theories Project and Prove2Me \[etp; prove2me\]. For a selected paper statement, the paper-to-Lean ledger records its registered formal supports and their stated relation to it. A separate sentence ledger records the source passages and rationale used in an explanation. Together with the claim registry and contribution history, these records let a reviewer recover the basis of a public assertion at a specified revision. We describe the components and their responsibilities, then trace a conditional theorem through the evidence checks. The revision and contribution workflows explain how accepted changes return to the repository. Recorded observations and limits distinguish implemented procedures from their unmeasured effects; Appendix <a href="#app:worked-proof" data-reference-type="ref" data-reference="app:worked-proof">11</a> retains the mathematical calculation.

<a id="sec:world"></a>

# A repository organised around problems

<div id="systems-scaling">

</div>

Within this collection, a reader may want a proof, a counterexample to a proposed extension, or the argument behind a failed approach. Exact experiments and corrected references remain beside the original question as contributions in their own right. The first task is to find the relevant work without compiling the whole repository. Four views answer different parts of that question (Figure <a href="#fig:world" data-reference-type="ref" data-reference="fig:world">2</a>).

A declaration is a named Lean definition, theorem or lemma. The declaration index locates its source; the dependency index records which earlier declarations the selected results use. A separate graph records authored interpretations of those declarations and their connections, while a claim registry records selected mathematical assertions, their status and the obligations still open.

<figure id="fig:world" data-latex-placement="htbp">
<div class="minipage">
<p><strong>For each problem:</strong> the question and literature, Lean statements and proofs, computations and certificates, claims and open obligations, failed approaches, and the paper with its supporting record.</p>
<table>
<thead>
<tr>
<th style="text-align: left;">View available without a Lean build</th>
<th style="text-align: left;">What it records</th>
</tr>
</thead>
<tbody>
<tr>
<td style="text-align: left;">Declaration index</td>
<td style="text-align: left;">Source locations, exhaustive within its inventory.</td>
</tr>
<tr>
<td style="text-align: left;">Dependency index</td>
<td style="text-align: left;">Exact dependency edges for the selected starting declarations.</td>
</tr>
<tr>
<td style="text-align: left;">Interpretation graph</td>
<td style="text-align: left;">Selective, largely contextual accounts of declarations and their connections; not an individual reading of every proof.</td>
</tr>
<tr>
<td style="text-align: left;">Claim registry</td>
<td style="text-align: left;">Selected assertions, their status and remaining obligations.</td>
</tr>
</tbody>
</table>
<p>Across the corpus: 8 problems, 1,903 Lean modules and 24 registered papers. The claim registry contains 160 claims in eight statuses, with 19 open obligations.</p>
</div>
<figcaption>Contents of a problem collection and the four ways to inspect the recorded work. The counts refer to the whole corpus. Source locations, dependency edges, interpretations and claim statuses answer different questions.</figcaption>
</figure>

Starting from a recorded assertion, a reader can therefore locate its declarations, follow the recorded dependencies and request the specified lines of source needed for a particular question. The declaration index is exhaustive within its inventory, and the dependency edges are exact for the selected starting declarations. The recorded interpretations are selective and largely contextual; they do not document an individual reading of every proof. A source link by itself records no successful execution. When a question requires a Lean check, the reader can request a focused build and inspect its recorded result.

<a id="stored-artifacts-and-executable-tools"></a>

## Stored artifacts and executable tools

The checkout contains authored Lean and manuscript sources, JSON records for selected claims and their evidence, and a journal of research returns. Indexes, source coordinates and status summaries are derived from those records. Authors edit the sources; builders regenerate the derived views. This division gives a reviewer a source to inspect when a generated view changes. In reviewing a claim, the maintainer must still distinguish a finite computation’s tested range from a general theorem, or a failed attempt from an argument that every approach must fail. The [`architecture guide`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/ARCHITECTURE.md) identifies the source files and their derived views.

The command-line tools have bounded jobs:

<div class="center">

| Component | Input, output and responsibility |
|:---|:---|
| Task routing | [`agent_entry.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/agent_entry.py) maps a stated task to instructions, relevant files and commands; the researcher chooses the question and approach. |
| Evidence retrieval | [`query_corpus.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/query_corpus.py) returns problem, claim, declaration and paper-source records from the indexes. |
| Proof sessions | [`proof_workbench.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/proof_workbench.py) records notes and submitted Lean probes, derives verdicts from the Lean process, and binds a session claim to an accepted probe. |
| Statement evidence | [`paper_evidence.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/paper_evidence.py) resolves mathematical paper statements against source and verification records; [`paper_claim_evidence.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/paper_claim_evidence.py) projects their evidence status and reported gaps. |
| Editorial exchange | [`short_paper_writer.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/short_paper_writer.py) audits manuscripts and packages proposed revisions without applying or approving the return. |
| Research history | [`research_record.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/research_record.py) verifies the journal of entered returns and dispositions and reports what recorded outputs still owe. |
| Derived views | [`refresh_projections.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/refresh_projections.py) runs builders in dependency order; [`check_release.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/check_release.py) checks release contracts and freshness. |

</div>

A separate self-audit, [`systems_paper_evidence.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/systems_paper_evidence.py), checks this systems manuscript’s text and cited source bindings. These are inspectable software responsibilities, not measurements of research quality or new execution results.

The tools retain state in repository files rather than in the agent’s conversation. An optional proof session appends notes, probe receipts and its closing outcome to a ledger, with the exact submitted Lean inputs stored beside it. These session claims remain distinct from the reviewed public claim registry. The research journal separately retains entered returns and review dispositions and checks their sequence and hash chain. A human or agent chooses the next task and invokes these tools; recording the sequence does not make the workbench an autonomous search policy.

<a id="researcher-agent-and-maintainer-responsibilities"></a>

## Researcher, agent and maintainer responsibilities

A researcher chooses the task and the evidence needed to answer it. A coding agent can inspect files, invoke tools and prepare a proposed change using the public instructions; ordinary written arguments and explanations can also be contributed without a clone or an agent. A maintainer reviews the claim, attribution and remaining uncertainty before adoption. The contributor and reviewer may be the same agent, so this division of responsibilities does not establish independent review. Public setup and review instructions are in the [`agent quickstart`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/agents/README.md) and [`contribution guide`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/CONTRIBUTING.md).

A typical iteration starts with a question and the recorded work that bears on it. The researcher investigates, then returns an argument, experiment, correction or manuscript change with its evidence and limitations. Review may adopt it, request revision, defer it or reject it. Accepted work changes the authored claims, papers and evidence records; builders and release checks update the dependent views before the next task uses them. The journal preserves dispositions for the structured returns explicitly entered into it. Ordinary issues, pull requests and ideas can enter review without a journal session. Sections <a href="#sec:paper" data-reference-type="ref" data-reference="sec:paper">5</a> and <a href="#sec:contribute" data-reference-type="ref" data-reference="sec:contribute">6</a> give the implemented publication exchange and the wider contribution procedure.

<a id="sec:example"></a>

# Worked case: publishing a conditional theorem

<span id="sec:predigestion" label="sec:predigestion"></span>

The worked case concerns a theorem about infinite sums of reciprocals over a restricted set of positive integer exponents. A base-two weighted convergence condition restricts the allowable sets; under it, every infinite subset gives an irrational sum at every integer base at least two. Removing the condition would assert a solution of a more general problem that remains open. Appendix <a href="#app:worked-proof" data-reference-type="ref" data-reference="app:worked-proof">11</a> gives the exact statement and calculation.

The example uses two records with different jobs. In [`paper_lean_coverage.json`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/paper_lean_coverage.json), a row identifies the weighted-support theorem’s occurrence in the mathematical paper, its statement digest, source location and two Lean supports. A separate [`sentence ledger`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/systems_paper_sentences.json) binds this systems paper’s explanation to specified source passages and an authored rationale. For example, the appendix’s hereditary conclusion is bound to both the ordinary proof and its formal declaration. These records make the two correspondences inspectable; deciding whether the explanation preserves the condition remains a review task.

<a id="sec:checks"></a>

# Proof and publication checks

<span id="sec:graph" label="sec:graph"></span> <span id="systems-trust"></span> The example has two registered formal supports (Figure <a href="#fig:theorem" data-reference-type="ref" data-reference="fig:theorem">6</a>). One gives fixed-base irrationality and the all-base conclusion for every infinite subset; the other makes the fixed-base hereditary conclusion explicit. Their roles overlap. The publication check requires the registered set, even if one declaration suffices for the clause under discussion. This is an accounting requirement, not an additional hypothesis of the theorem. The resolver also follows any registered named inputs and checks the identified source revisions. A result dependent on an additional named input retains that dependency; the weighted theorem above illustrates a different issue, a restriction within the proved statement. A changed statement or source must be checked against its records again. Evidence attached to one revision cannot silently support another.

These checks make omissions and changes inspectable. Figure <a href="#fig:checks" data-reference-type="ref" data-reference="fig:checks">3</a> separates them from proof checking and from the judgements needed to publish a faithful account.

<figure id="fig:checks" data-latex-placement="htbp">
<table>
<thead>
<tr>
<th style="text-align: left;">Relation being assessed</th>
<th style="text-align: left;">Check or judgement required</th>
</tr>
</thead>
<tbody>
<tr>
<td style="text-align: left;">Formal statement and proof</td>
<td style="text-align: left;">Lean kernel checking.</td>
</tr>
<tr>
<td style="text-align: left;">Challenge and formal statement</td>
<td style="text-align: left;">Comparator checking against the selected challenge.</td>
</tr>
<tr>
<td style="text-align: left;">Paper occurrence and registered support set</td>
<td style="text-align: left;">Coverage audit: all registered declarations and their recorded revisions.</td>
</tr>
<tr>
<td style="text-align: left;">Sentence and declared source bytes</td>
<td style="text-align: left;">Sentence audit: text and source digests, with a recorded rationale.</td>
</tr>
<tr>
<td style="text-align: left;">Sentence and mathematical meaning</td>
<td style="text-align: left;">Author and reviewer judgement about what the sources establish.</td>
</tr>
<tr>
<td style="text-align: left;">Result and motivating question</td>
<td style="text-align: left;">Author and reviewer judgement about the scope of the result.</td>
</tr>
<tr>
<td style="text-align: left;">Novelty, significance and acceptance</td>
<td style="text-align: left;">Assessment by reviewers and the mathematical community.</td>
</tr>
</tbody>
</table>
<figcaption>Four checks with different objects, followed by three questions of judgement. The upper rows identify checking mechanisms, not new executions reported here. The lower rows identify review responsibilities, not evidence of independent review. A recorded rationale still requires assessment of its meaning.</figcaption>
</figure>

Lean verifies that a proof establishes the formal statement written in the source; it does not verify whether that statement captures the intended mathematics or whether the paper describes it well. Comparator adds a separately stated challenge and a check of its selected Lean implementation under the permitted axioms \[leanfrocomparator; nanodalib\].

Each marked passage in this systems paper has a recorded text, specified source lines, an evidence class and an authored rationale for citing those sources.

For the appendix’s hereditary conclusion, the cited sources explain why restriction to an infinite subset preserves the weighted condition. The sentence checker compares cryptographic hashes of the marked text and its declared source passages; it also rejects missing records or passages without a binding.

Changing the sentence alone therefore makes its recorded digest stale. Changing the sentence and updating its record can restore byte agreement without restoring the implication claimed by the prose. For example, a paraphrase could drop the support hypothesis while retaining both correct Lean links in Figure <a href="#fig:theorem" data-reference-type="ref" data-reference="fig:theorem">6</a>. A reviewer must compare its hypothesis and quantifiers with the source statement. This is an illustrative editing failure, distinct from historical edit 8, which replaced a limitation by a false completion claim (Table <a href="#tab:mutations" data-reference-type="ref" data-reference="tab:mutations">1</a>).

An entry in the declaration index with a matching type and a reachable source link identifies the recorded source; it does not establish that any particular continuous-integration run compiled the module. In the recorded design, the checking interface obtains each verdict from the specified Lean process, so callers cannot supply verdicts through that interface. This interface rule does not prevent an actor with filesystem access from changing the implementation or stored record. The protocol distinguishes contributor and reviewer roles but does not technically force a second independent mathematician. No independent human mathematical review of the corpus is recorded.

<a id="sec:paper"></a>

# Publication and revision

<span id="sec:short" label="sec:short"></span><span id="sec:long" label="sec:long"></span><span id="sec:production" label="sec:production"></span> The worked case suggests a concrete editorial task: retain the result’s conditions and scope, explain the decisive step, and link the short account to the full argument. A useful explanation lets a reader recover why the conclusion holds and where it stops applying. A dependency graph locates the ingredients. Choosing their order and explaining their role require reading the argument; the manuscript audit supplies no such judgement. The companion paper retains the complete proof and subsidiary cases. A correspondence link names the passage supporting a particular short-paper claim, so the reader can move from the explanation to the calculation without searching the whole paper. The assembler preserves these authored parts and their cross-references; it supplies no missing mathematical step. Readers may need a hint, a worked example or the full argument. The reading guide invites them to reconstruct a decisive step or change a hypothesis, and the explanation instructions require an agent to respect the requested depth. These are authoring rules; they do not establish that a reader has understood the proof.

<a id="work-assignments-and-review"></a>

## Work assignments and review

We call an agent that can alter the live repository Type A and an advisory agent returning proposals against supplied sources Type B.

Repository authority and the assigned task are separate choices. The task may be mathematical research, proof or claim audit, literature and attribution review, or exposition.

Research returns candidate arguments, an audit returns source-located findings, a literature review returns attribution proposals, and exposition returns a clearer manuscript; each product has its own review and acceptance criteria.

An exposition assignment preserves the established hypotheses, conclusions and evidence status; a suspected mathematical defect is returned for a separate audit or research assignment.

The reviewer compares hypotheses and implication directions with the whole statement and all its registered declarations. An ordinary argument retains its actual evidence class where formalisation is incomplete.

After acceptance, integration requires restoring the companion paper’s authored sections, regenerating evidence and navigation, and inspecting the compiled pages, figures and proof links.

A writing rule learned from the revision travels with its example and limits as a candidate. Its adoption requires a reviewed change to the owning writing contract.

<a id="proposing-and-reviewing-a-revision"></a>

## Proposing and reviewing a revision

A revision begins by collecting candidate results, antecedents, difficult proof transitions and unresolved questions with their source locations. The author decides which argument deserves the short paper; the checker audits source consistency and the specified manuscript rules. We freeze the selected manuscripts, their required input files, coverage ledger and audit rules under a manifest of their exact bytes, so the writer and integrating reviewer can identify what the proposed changes were based on.

An advisory model can return a proposal against those sources; a tool-enabled agent can prepare it in a checkout. In either case the integrating reviewer decides whether the mathematics and its description remain faithful. The public writer’s packet declares which manuscript paths may change and supplies its evidence records and checking tools as read-only inputs.

<figure id="fig:refinement" data-latex-placement="H">

<figcaption>The exposition workflow, read in numerical order, with the exchanged objects labelled. A proposal may be revised or declined at step 3; only accepted changes proceed to integration. The steps name responsibilities, which may be performed by the same agent. Rendering and inspection remain separate from source checks.</figcaption>
</figure>

Before that decision, the return checker tests packet identity, permitted paths, declared statement changes and retained labels, citation keys and bibliography entries. It audits the proposed manuscript in a temporary copy of the frozen sources, leaving the live repository unchanged. It neither applies the proposal nor executes returned programs. Declaring a statement change makes the review obligation explicit; it does not discharge it.

The packet and audit stages in Figure <a href="#fig:refinement" data-reference-type="ref" data-reference="fig:refinement">4</a> are implemented by [`short_paper_writer.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/short_paper_writer.py) and [`paper_refinement.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/paper_refinement.py).

A return has two possible lasting effects: accepted text changes the paper; an accepted general lesson changes the guidance supplied to later writers. The latter needs its own review, so a local improvement can be retained without becoming a new rule. This process revises documents and instructions, not model weights. The procedure supplies no measurement of reader benefit or autonomous discovery.

<a id="sec:contribute"></a>

# An open route for contributions

<span id="sec:loop" label="sec:loop"></span><span id="sec:cycle" label="sec:cycle"></span> <span id="systems-public"></span> <span id="systems-job-lifecycle"></span> A contributor may send a mathematical idea or reference without a clone, or return a patch from a recorded public commit. For executable work the return identifies the changed files, commands, results, resource use and surviving limitations, with the people and tools responsible. Figure <a href="#fig:contribute" data-reference-type="ref" data-reference="fig:contribute">5</a> separates the proposed change from replay, review and adoption. The return protocol calls for reproduction at the submitted base before reconciliation with current main, with separate credit for a substantive integration repair.

<figure id="fig:contribute" data-latex-placement="H">

<figcaption>Two entry routes and three possible review outcomes. Repository adoption applies to mathematical and methodological contributions; it establishes neither independent review nor acceptance by the wider mathematical community.</figcaption>
</figure>

<div id="systems-research-loop">

</div>

<div id="systems-coupled-goals">

</div>

The research journal records explicitly entered returns and dispositions in an append-only, hash-linked history, while a correction may withdraw something previously endorsed. Ordinary issues and pull requests need not become journal events. Discovery investigates a question, while stewardship compares the return with prior work, groups related results, reconciles affected papers and selects the next question. The proposed coupling is event-driven: a stable result or changed appraisal prompts work, whereas an unchanged repository supplies no reason for another run. The journal preserves the entered return and its recorded disposition. Judging what was learned requires comparison with earlier work and inspection of the returned evidence.

<div id="systems-mathloop">

</div>

Generalising a local result requires a separate literature and library comparison, a proof of the proposed extension, and a second useful instance before an expert takes it to an upstream project \[mathlibcontrib\]. That route is not automated and has produced no reported Mathlib contribution in the supplied record. We distinguish credit for an idea from credit for its implementation, formalisation or exposition, using CRediT as a role vocabulary rather than an authorship decision \[credit\]. Later use adds an attributed dependency or correction, with neither a scalar impact score nor a financial contract inferred from that entry. A new problem collection likewise needs a sourced question, explicit status, inspection routes and a review owner, which must still be assembled in several steps.

<a id="sec:instance"></a>

# Recorded observations

<span id="sec:evaluation" label="sec:evaluation"></span> The frozen inventory contains 689 paper occurrences, of which 640 have exact or specialising Lean support; 23 depend on a named input and 26 have no recorded Lean support. Of the 640 exact-or-specialising occurrences, 616 are recorded as compared and 24 as queued. These counts classify statement occurrences. Exact and specialising support match a paper statement directly or establish it by specialization. Named-input entries retain an additional assumed result; an entry without Lean support may still have an ordinary mathematical proof. Neither group is counted among the fully covered entries.

The historical publication-evidence record reports that nine of the ten deliberately false edits were rejected and one escaped. The edits were authored by the checker’s author, the original run logs were not retained, and the other nine edits were not rerun against the extended checklist. The edits were applied separately, with the baseline restored between trials. The escaped edit changed a description of an unresolved step from “does not supply'' to “completes'', and the publication checks accepted it.

<div id="tab:mutations">

| Edit | Change | First detector | Outcome |
|:---|:---|:---|:---|
| edit 1 | Conditional result labelled proved | Projection freshness | rejected |
| edit 2 | Open-boundary clause deleted | Boundary wording | rejected |
| edit 3 | Declaration coordinate moved | Source coordinates | rejected |
| edit 4 | Paper source link retargeted | Source coordinates | rejected |
| edit 5 | Claim assigned to two families | Registry structure | rejected |
| edit 6 | Module count hand-edited | Projection freshness | rejected |
| edit 7 | `native_decide` introduced | Proof-trust policy | rejected |
| edit 8 | “does not supply'' changed to “completes'' | None | **escaped** |
| edit 9 | Open-problem title mangled | Paper anchoring | rejected |
| edit 10 | Orientation byte budget exceeded | Byte budget | rejected |

The ten historical edits and their recorded first detectors; “proof-trust policy” refers to this repository’s permitted proof mechanisms, not to a general unsoundness claim about `native_decide`.

</div>

<div class="minipage">

**Historical trial: edit 8**\
The false completion clause passed all recorded checks.

</div>

<div class="minipage">

**Later witness: baseline and edit 8**\
Baseline accepted, edit 8 rejected; the other nine edits were not rerun.

</div>

After the escape, the follow-up checked the intact baseline and that particular edit against an added check, leaving the other edits untested under the repair and supplying no post-repair ten-of-ten result. In that recorded follow-up, the post-repair witness accepts the current README and rejects a test copy containing the false clause. The sample comes from one corpus and one author's selection of errors, with neither a manual-review control nor an ordinary continuous-integration comparator. The study locates a coverage boundary. Its nine rejections do not estimate how reliable the checker is.

On 23 September 2026, a maintainer-operated agent accepted one architecture handoff into a local integration history after focused checks of return routing and architecture packaging. The contributor and reviewer were the same agent. The receipt records no public pull request, human review or independent outside clone replay.

For readers, the proposed comparison holds the mathematical task fixed and contrasts an ordinary repository, an information-equivalent static briefing and the navigation tools. It would record understanding, severe errors and the costs of preparation, use, review and repair, including missing returns, timeouts and disagreements. No independent writing comparison, blind grading run or cold-reader experiment is reported here, and no comparative reader result is reported. General reliability, reader understanding and mathematical transfer remain unmeasured.

<a id="sec:related"></a>

# Related work

<span id="app:credit" label="app:credit"></span> The comparison with earlier systems is clearest at the relations they record. Lean and mathlib provide formal statements and proofs; blueprints link declarations to exposition; Prove2Me organises formalisation missions, reusable statements and contributions \[lean4; mathlib; leanblueprint; prove2me\]. The additional records here follow all registered supports and the source passages used in prose. Appendix <a href="#app:source-map" data-reference-type="ref" data-reference="app:source-map">12</a> preserves the wider source map of the three original accounts. Prove2Me's first arXiv version appeared on 28 August 2026, before the first public version of this paper, and already described public agent contributions, task decomposition, reusable statements and credit for reuse \[prove2me\]. Its hosted verification service and this repository-based record provide different places for those activities; we claim neither priority for persistent research records nor a measured advantage over these systems. Polymath, BOINC and GIMPS supply precedents for small mathematical contributions and donated compute \[polymath; boinc; gimps\], while the Carleson blueprint shows formalisation organised into publicly claimable tasks \[carleson\].

Our fixed-order regeneration and freshness checks address the build-system problem of keeping derived views consistent with their inputs \[buildsystems\]. The implementation runs an explicit ordered list of builders, then checks the resulting views; it is not a general incremental scheduler. Source bindings and the journal record artifact provenance, including the inputs and revision to which a claim or entered return refers. These records serve inspection and reproducibility, with research efficiency and semantic correctness left to separate evaluation.

<a id="sec:limits"></a>

# Limits

<span id="sec:conclusion" label="sec:conclusion"></span> This paper reports no comparative formalisation result or autonomous-optimisation experiment. Transfer to unseen mathematics and understanding by independent human readers are unresolved. The record supplies no controlled evidence that the contribution machinery improves the conversion from compute to mathematics or increases discovery rate. It also supplies no evidence that a new project can adopt the architecture cheaply or that an agent using it outperforms one using a good README. Full environment scans and initial builds still have costs, and an open corpus cannot establish that a model has never encountered its material.

The project remains maintainer-centred, with scarce review capacity and contestable credit; openness alone does not equalise resources or resolve conflicts and appeals. Broad mathematical acceptance is exogenous to this repository and cannot be granted by its maintainer. Returned code is untrusted, and expensive or privileged continuous-integration jobs must not execute fork code with repository secrets \[githubsecurity\]. A volunteer-compute service and extensions to physical science remain proposals requiring their own validation, resource and safety governance.

The Advisory Group on Mathematics and Artificial Intelligence at IAS recommends distinguishing papers fully understood by a responsible mathematician from AI output that its human prompters do not understand, and asks AI laboratories to support subsequent community-led understanding \[agmai2026\]. Its 29 September 2026 statement gives concrete release expectations for attribution, exposition, formalisation and disclosure of the research process.

Several of these proposed release practices have counterparts in the records described here \[agmai2026, Section 2.B, Step I\]: the short paper and companion paper explain and attribute the argument, the paper-to-Lean ledger records formal correspondence and its limits, and the challenge files and generated `formalization.yaml` expose the comparison inputs. Those records make the result inspectable; they do not certify a mathematician’s understanding. The architecture alone does not establish complete per-result model, prompt, time and cost disclosure, an account of campaign-wide selection and unsuccessful attempts, or an independent scholarly deposit. The further recommendations on funding community-led understanding and equitable model access address AI laboratories; this prototype does not demonstrate those institutional outcomes.

The present contribution is an inspectable route through the records: a reader can recover the hypothesis, argument and support of a stated result, and identify where a source check ends and mathematical review begins.

<a id="app:repro"></a>

# Inspection and reproduction

The initial unified manuscript was prepared from the frozen packet at `ced96e58b337`, a local integration commit rather than public main. A 29 September state report lists this manuscript as *Problem-Sized Lean Worlds*. Repository links in this revision use commit `992cf60a27ef`; the Comparator links below identify their separate recorded runs. No new Lean or Comparator run was performed for this revision. This paper supersedes *From a Cold Clone to a Proof Receipt* and *From Spare Compute to Cumulative Mathematics*. Their manuscripts remain available as historical accounts of navigation, proof-check records, contribution protocol and governance.

<a id="earlier-design-accounts-and-current-status"></a>

## Earlier design accounts and current status

*[`From a Cold Clone to a Proof Receipt`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/paper/systems/cold-clone-to-proof-receipt.tex)* (August 2026) explains the declaration, dependency, interpretation and claim views and the optional recorded proof session. The current task entry and the inspected implementation are described in Section <a href="#sec:world" data-reference-type="ref" data-reference="sec:world">2</a>; the earlier paper’s inventory and audit figures belong to its dated snapshot.

*[`From Spare Compute to Cumulative Mathematics`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/paper/systems/open-source-mathematics-strategy.tex)* (September 2026) explains contribution roles, original-base reproduction, later integration and role credit. Section <a href="#sec:contribute" data-reference-type="ref" data-reference="sec:contribute">6</a> describes the current public return procedure and distinguishes ordinary submissions from explicitly entered journal events. Volunteer-compute services, inexpensive adoption by new laboratories and improvements in discovery rate remain proposals or unmeasured outcomes. These two manuscripts are historical design sources, not additional current system specifications.

The weighted row in [`docs/paper_lean_coverage.json`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/paper_lean_coverage.json) names `divisibilityWeightedClaim` and `finitePrimeWeighted_fixedBase_hereditary`, in namespace `ErdosProblems.Erdos257.PaperCompleteR8`. Appendix <a href="#app:worked-proof" data-reference-type="ref" data-reference="app:worked-proof">11</a> follows the ordinary proof in \[paper257\]; these entries record formal support for the conclusion, not a line-by-line comparison of that argument with the Lean proofs. Its Comparator records are [run 35544127144](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35544127144) and [run 35624228171](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35624228171); the latter also records `PalomarCorpus/E257av` for the reciprocal antecedent. Both runs are recorded as compared; Palomar is prepared and not submitted.

For Erdős’s reciprocal-summability criterion, the formal declaration is [`Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean), with Comparator entry `PalomarCorpus/E257av` recorded as compared.

The four declarations supporting the reported 1041 refutation have namespace `Erdos1041.Counterexample`: [`erdos1041_counterexample`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/lean/ErdosProblems/Erdos1041/Counterexample/Assembly.lean), and the [`HausdorffLength.lean`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean) declarations `erdos1041_counterexample_hausdorff`, `erdos1041_hausdorff_negation` and `erdos1041_hausdorff_answer_false`. The coverage row gives exact-or-stronger Lean support, with Comparator pending.

In a complete checkout, `python3 scripts/systems_paper_evidence.py` checks this paper's source bindings, and `python3 scripts/build_systems_paper_counts.py` checks the generated inventory. The record at [`docs/publication_evidence.json`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/publication_evidence.json) holds the historical matrix and the limited follow-up, while [`docs/publication_contract.json`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/publication_contract.json) declares the publication checks. Formal entry points include [`Erdos249257.lean`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/lean/Erdos249257.lean) and [`.github/workflows/lean.yml`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/.github/workflows/lean.yml); the curated assertions are in [`docs/claims.json`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/claims.json), and [`scripts/check_release.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/check_release.py) runs the release gate. The public writer’s native packet freezes manuscript inputs, selected records and the tools used to inspect them; its input list does not include a Lean source tree. Source-binding validation does not replay Lean, Comparator or the full repository release checks.

The protected snapshot partitions 689 occurrences into 498 exact, 142 specialising, 23 named-input and 26 unsupported-by-Lean entries. The journal summary at head `d3ad85269386` records 7 rounds (2 sealed), 25 returns (18 admitted and 7 unreviewed); earlier private-history rounds are not a complete public journal. The interpretation inventory covers 139,818 of 152,386 authored theorem-like declarations (91.8%). These are selective, largely contextual interpretations, not individually reviewed proofs. Public reading starts at the [`reading guide`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/READING_GUIDE.md). [`Agent instructions`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/AGENTS.md) route source inspection, explanation and reproduction; the [`workbench guide`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/agents/AGENT_WORKBENCH.md) describes optional recorded sessions. [`Contributing`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/CONTRIBUTING.md) and the [`credit policy`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/research-commons/CREDIT_POLICY.md) govern returns. Cite repository software using [`CITATION.cff`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/CITATION.cff) at the chosen commit or release tag; cite mathematical results by the paper and version actually used.

<a id="app:worked-proof"></a>

# Calculation for the worked theorem

For an infinite set $`A`$ of positive integers and an integer $`b\ge2`$, write
``` math
X_A(b)=\sum_{a\in A}\frac1{b^a-1}.
```
The question is when a condition on the exponents forces this number, and the corresponding sum over every infinite subset of $`A`$, to be irrational.

The condition below rewards exponents divisible by large powers of a fixed collection of primes. For the prime $`2`$ alone, the relevant part of $`a=2^km`$, with $`m`$ odd, is $`2^k`$. For a finite nonempty set $`P`$ of primes, this becomes $`h_P(a)=\prod_{p\in P}p^{v_p(a)}`$, where $`v_p(a)`$ is the exponent of $`p`$ in the prime factorisation of $`a`$.

The weighted-support theorem of the Problem 257 paper states that, if
``` math
\begin{equation}
\label{eq:worked-condition}
 W_{2,P}(A):=\sum_{a\in A}\frac{h_P(a)}{a(2^{h_P(a)}-1)}<\infty,
\end{equation}
```
then $`X_B(b)`$ is irrational for every integer $`b\ge2`$ and every infinite $`B\subseteq A`$ \[paper257, Theorem 1.2\].

For a fixed base $`b`$, write $`W_{b,P}(A)`$ for the sum in <a href="#eq:worked-condition" data-reference-type="eqref" data-reference="eq:worked-condition">[eq:worked-condition]</a> with $`2`$ replaced by $`b`$. The fixed-base version assumes $`W_{b,P}(A)<\infty`$ and gives the same hereditary conclusion at that base. The calculation below gives the ordinary argument; Figure <a href="#fig:theorem" data-reference-type="ref" data-reference="fig:theorem">6</a> identifies its two registered Lean supports.

This is a sufficient condition on the support; the question for an arbitrary infinite set of exponents in base two remains open.

Erdős had already stated that $`\sum_{a\in A}1/a<\infty`$ suffices for this all-base irrationality conclusion \[erdos1968, p. 222\].

The source paper credits Duverney and Tachiya for an arithmetic-progression averaging argument of the kind used to select a small positive displacement \[duverneytachiya, Section 2, (2.3)–(2.9)\].

<figure id="fig:theorem" data-latex-placement="htbp">

<figcaption>The arrows associate a paper statement with its coverage row and the two registered supports; they do not represent deductions between these records. The support hypothesis still needs mathematical explanation. The false paraphrase is illustrative, distinct from historical edit 8 in Table <a href="#tab:mutations" data-reference-type="ref" data-reference="tab:mutations">1</a>.</figcaption>
</figure>

This appendix retains the ordinary calculation from the Problem 257 paper used by the worked case in Section <a href="#sec:example" data-reference-type="ref" data-reference="sec:example">3</a>.

The distinction from the reciprocal-summability criterion is visible in the source paper’s example
``` math
A_\star=\{2^km:k\ge1,\ m\text{ odd},\ 1\le m\le2^{2^k}\},\qquad P=\{2\}.
```
Within the layer $`v_2(a)=k`$, reciprocal summation discounts each odd $`m`$ by $`2^{-k}`$; weighted summation discounts it by $`(2^{2^k}-1)^{-1}`$.

To compare the layers, put $`S_r=\sum_{1\le m\le2^r,\ m\ \mathrm{odd}}1/m`$. Grouping the odd integers into intervals $`[2^j,2^{j+1})`$ gives $`r/4\le S_r\le r`$ for integers $`r\ge2`$.

The reciprocal contribution of each disjoint layer is at least $`2^{-k}S_{2^k}\ge1/4`$. Its weighted contribution satisfies
``` math
\frac{S_{2^k}}{2^{2^k}-1}\le\frac{2^k}{2^{2^k}-1}\le2^{1-k},
```
so the layer contributions have a convergent geometric majorant in the weighted sum.

Thus $`A_\star`$ lies beyond the reciprocal-summability criterion but satisfies <a href="#eq:worked-condition" data-reference-type="eqref" data-reference="eq:worked-condition">[eq:worked-condition]</a>. This is the source paper’s ordinary calculation, with no separate entry in the paper-to-Lean ledger \[paper257, calculation following the weighted proof\].

<a id="a-positive-displacement."></a>

#### A positive displacement.

Suppose that $`X_A(b)=p/q`$ with integers $`p,q`$ and $`q>0`$. For a positive integer $`N`$, multiplication by $`b^N-1`$ removes the complete geometric blocks from each summand, leaving
``` math
\begin{equation}
\label{eq:worked-displacement}
 \Delta_{b,A}(N)=\sum_{a\in A}\frac{b^{N\bmod a}-1}{b^a-1}
 =(b^N-1)X_A(b)-J_{b,A}(N),\qquad N\ge1,
\end{equation}
```
where $`J_{b,A}(N)=\sum_{a\in A,\,a\le N}\sum_{j=1}^{\lfloor N/a\rfloor}b^{N-ja}`$ is an integer.

Every summand is nonnegative, and one is positive because the infinite set $`A`$ contains an exponent larger than $`N`$. Hence $`q\Delta_{b,A}(N)`$ is a positive integer, and $`\Delta_{b,A}(N)\ge1/q`$.

We obtain a contradiction by finding a multiple $`N=tQ`$ with smaller displacement. Divisibility helps because the summand indexed by $`a`$ vanishes whenever $`a\mid Q`$.

Choose a finite nonempty $`F\subset A`$ outside which the weighted sum is less than $`\varepsilon`$, and make $`Q`$ a multiple of every element of $`F`$. Those terms then disappear for every $`t`$; we must control the remaining terms on average.

<a id="a-finite-orbit-and-its-unfinished-end."></a>

#### A finite orbit and its unfinished end.

With $`b=2`$, $`Q=4`$ and $`a=6`$, the residues $`tQ\bmod a`$ are $`4,2,0`$, and their mean displacement is
``` math
\frac13\left(\frac{15}{63}+\frac3{63}+0\right)=\frac2{21}\le\frac19.
```
For a general exponent $`a`$, put $`g=\gcd(a,Q)`$. The residues run through the multiples of $`g`$ in a cycle of length $`a/g`$. Replacing each numerator $`b^r-1`$ by $`b^r`$ bounds the sum over one cycle by $`1/(b^g-1)`$. There are at most $`T/(a/g)`$ complete cycles and one unfinished cycle among the first $`T`$ terms. Dividing their total by $`T`$ gives
``` math
\begin{equation}
\label{eq:worked-orbit}
 \frac1T\sum_{t=1}^T\frac{b^{tQ\bmod a}-1}{b^a-1}
 \le \underbrace{\frac{g}{a(b^g-1)}}_{\text{complete cycles}}
    +\underbrace{\frac1{T(b^g-1)}}_{\text{unfinished cycle}}.
\end{equation}
```

The first term has the shape of the weighted hypothesis once suitable prime powers have been put into $`Q`$. The second has lost the factor $`1/a`$. Summability of the first therefore gives no licence to sum the unfinished-cycle bounds over all exponents. This is the difficulty that a single progression average leaves unresolved.

<a id="a-second-average-restores-the-missing-factor."></a>

#### A second average restores the missing factor.

The source proof averages over the $`M`$ lengths $`T=2^j`$, $`M\le j<2M`$. Thus $`M`$ counts the lengths being averaged, whereas $`T`$ counts the terms in one progression average. For nonnegative weights $`\alpha_a`$ indexed by positive integers, with $`\sum_a\alpha_a/a<\infty`$, it uses
``` math
\begin{equation}
\label{eq:worked-dyadic}
 \sum_{j=M}^{2M-1}2^{-j}\sum_{a\le Q2^j}\alpha_a
 \le 2Q\sum_a\frac{\alpha_a}{a}.
\end{equation}
```
Indeed, a fixed $`a`$ enters only when $`2^j\ge a/Q`$, and the sum of the admissible $`2^{-j}`$ is at most $`2Q/a`$. This recovers the missing factor before summing over $`a`$. Dividing by the number $`M`$ of lengths then reduces the cost from $`2Q`$ to $`2Q/M`$.

<a id="balancing-the-two-costs."></a>

#### Balancing the two costs.

The modulus must cancel $`F`$ while making the remaining exponents amenable to one of two estimates. Fix a positive common multiple $`L`$ of $`F`$, put $`p_*=\max P`$, and, for $`H\ge2p_*`$, set
``` math
Q=L\prod_{p\in P}p^{\lfloor\log_p H\rfloor},\qquad
 G=\lfloor H/p_*\rfloor.
```
If $`h_P(a)\le H`$, then $`h_P(a)\mid Q`$. Since $`n/(b^n-1)`$ decreases for positive integers $`n`$, the complete-cycle term in <a href="#eq:worked-orbit" data-reference-type="eqref" data-reference="eq:worked-orbit">[eq:worked-orbit]</a> is bounded by $`h_P(a)/[a(b^{h_P(a)}-1)]`$. Its sum outside $`F`$ is less than $`\varepsilon`$.

If $`h_P(a)>H`$, then $`\gcd(a,Q)\ge G`$: either every $`P`$-prime-power component of $`h_P(a)`$ is at most $`H`$, so $`h_P(a)\mid Q`$, or one exceeds $`H`$, and its truncated component in $`Q`$ is greater than $`H/p_*\ge G`$. Summing <a href="#eq:worked-orbit" data-reference-type="eqref" data-reference="eq:worked-orbit">[eq:worked-orbit]</a> over these exponents up to $`QT`$ costs at most
``` math
\frac{G(1+\log(QT))+Q}{b^G-1}:
```
the harmonic sum supplies $`1+\log(QT)`$, and at most $`QT`$ unfinished-cycle terms supply $`Q`$.

Increasing $`M`$ therefore has two effects. It reduces the first group’s unfinished-cycle cost $`Q/M`$, but increases the second group’s cost through $`\log T<2M\log2`$. We need both $`Q/M\to0`$ and $`GM/b^G\to0`$, not merely a long average. With $`F`$ and $`L`$ fixed, $`Q\le LH^{|P|}`$ and $`G=H/p_*+O(1)`$. The choice $`M=\lfloor b^{G/2}\rfloor`$ meets both requirements.

The source proof combines these estimates into the finite mean
``` math
\begin{equation}
\label{eq:worked-mean}
\begin{aligned}
 &\frac1M\sum_{j=M}^{2M-1}\frac1{2^j}
       \sum_{t=1}^{2^j}\Delta_{b,A}(tQ)\\
 &\qquad\le \varepsilon+\frac{2QW_{b,P}(A)}M
       +\frac{G(1+\log Q+2M\log2)+Q}{b^G-1}+4\,2^{-M}.
\end{aligned}
\end{equation}
```
The terms bound, respectively, the weighted tail over complete cycles, its unfinished cycles, the exponents with large gcd, and the exponents beyond $`QT`$. The second term uses <a href="#eq:worked-dyadic" data-reference-type="eqref" data-reference="eq:worked-dyadic">[eq:worked-dyadic]</a> with $`\alpha_a=\mathbf1_A(a)/(b^{h_P(a)}-1)`$; the last uses the geometric tail bound $`4/T`$. After $`\varepsilon`$, $`F`$ and $`L`$ have been fixed, every term after $`\varepsilon`$ tends to zero as $`H\to\infty`$ \[paper257, Section 2, weighted-support proof\].

The left side of <a href="#eq:worked-mean" data-reference-type="eqref" data-reference="eq:worked-mean">[eq:worked-mean]</a> is an average with nonnegative weights summing to one: each length has weight $`1/M`$, distributed equally among its $`2^j`$ terms. For large $`H`$, at least one displacement is therefore less than $`2\varepsilon`$. Taking $`0<\varepsilon<1/(2q)`$ contradicts the lower bound $`1/q`$. This argument gives no rate of decay in $`N`$. Passing to an infinite $`B\subseteq A`$ only decreases the weighted sum, and $`b^{h_P(a)}-1\ge2^{h_P(a)}-1`$ gives the all-base conclusion from the binary hypothesis \[paper257, Section 2\].

<a id="other-mathematical-attribution-and-scope-examples"></a>

## Other mathematical attribution and scope examples

The relation to the motivating problem must also survive compression: the Problem 269 record distinguishes distinct running-LCM heights from the heights counted with multiplicity in the original question \[paper269\].

A result about the former is not automatically a result about the latter.

When a statement is sharpened, merged or moved, its complete support set and any named input must move with it, and the statement relation needs renewed review.

A new arrangement of a proof does not make its ingredients new.

The totient record refines Coons's non-$`k`$-regularity antecedent and distinguishes Martin's separation theorem from its own Chinese-remainder and Dirichlet argument traced to Yazdani \[paper249; coons; martin; yazdani\].

The running-LCM record retains Fan's public priority for the two-prime case despite an independently reported derivation, and credits its Hecke–Mahler antecedents separately \[paper269; fan269; loxtonvdp1977; bugeaudlaurent2023\].

For Problem 1041, the public degree-seven construction is ani's; the recorded Lean result refutes the exact Formal Conjectures statement, while correspondence with the 1958 curve-length wording remains unreviewed \[aniforum; formalconjectures; fcpr; ehp1958; erdos1041\].

Appendix <a href="#app:repro" data-reference-type="ref" data-reference="app:repro">10</a> names its four recorded Lean declarations; Comparator is pending.

The other seven targets remain unresolved here.

<a id="app:source-map"></a>

# Sources by role

<figure id="fig:credit" data-latex-placement="H">
<table>
<thead>
<tr>
<th style="text-align: left;">Source family</th>
<th style="text-align: left;">Role in the three source accounts</th>
</tr>
</thead>
<tbody>
<tr>
<td style="text-align: left;">Formal foundations</td>
<td style="text-align: left;">Lean and mathlib; library maintenance and contributor practice [lean4; mathlib; growingmathlib; mathlibcontrib]</td>
</tr>
<tr>
<td style="text-align: left;">Source and statement checks</td>
<td style="text-align: left;">Comparator, kernel replay, vacuity, linters and property tests [leanfrocomparator; nanodalib; beyondvacuity; batteries; plausible]</td>
</tr>
<tr>
<td style="text-align: left;">Formal-to-prose tools</td>
<td style="text-align: left;">Blueprints, source documentation, translation and refactoring [leanblueprint; leanarchitect; hattori; leanmarathon; proofrefactor; p3docagent]</td>
</tr>
<tr>
<td style="text-align: left;">Retrieval and interaction</td>
<td style="text-align: left;">Premises, proof states and exact declaration neighbourhoods [leandojo; pantograph; leanexplore; leansearchv2; theoremgraph; leanatlas]</td>
</tr>
<tr>
<td style="text-align: left;">Proof automation</td>
<td style="text-align: left;">Premise selection and tactic search [leanhammer; aesop; judgementday]</td>
</tr>
<tr>
<td style="text-align: left;">Library structure</td>
<td style="text-align: left;">Declaration networks and repository knowledge graphs [mathlibnetwork; huch; repokg]</td>
</tr>
<tr>
<td style="text-align: left;">Assumptions and reuse</td>
<td style="text-align: left;">Proof mining, generalisation, lemma mining and theory exploration [kohlenbach; gandhi; lemmamining; hipster]</td>
</tr>
<tr>
<td style="text-align: left;">Growing proof knowledge</td>
<td style="text-align: left;">Library learning, evolving procedures and candidate statements [dreamcoder; legoprover; dreamprover; proofevolve; leanconjecturer; circuitprover]</td>
</tr>
<tr>
<td style="text-align: left;">Research agents</td>
<td style="text-align: left;">Executable objectives, proof cost and evolving tasks [alphaevolve; alphaevolvemath; patel; dreamrsi; berlotattwell]</td>
</tr>
<tr>
<td style="text-align: left;">Agent collaboration</td>
<td style="text-align: left;">Bounties, planner/worker state, retrieval and compiler feedback [agenthunt; openprover; oprover; prove2me; axle; etp]</td>
</tr>
<tr>
<td style="text-align: left;">Evaluation</td>
<td style="text-align: left;">Research budgets, proof engineering and documentation tasks [rebench; p6-swd; p6-ape; p6-poiroux; documentationtest; henkel; openproofcorpus]</td>
</tr>
<tr>
<td style="text-align: left;">Validity and intended meaning</td>
<td style="text-align: left;">Research case studies, interactive proving and public accounting [aletheia; autonomousmath; lihai; taowiki]</td>
</tr>
<tr>
<td style="text-align: left;">Public infrastructure</td>
<td style="text-align: left;">Problem sources, formal conjectures, verification and collaboration [erdosproblems; formalconjectures; palomar; carleson; polymath; boinc; gimps; credit; githubsecurity]</td>
</tr>
<tr>
<td style="text-align: left;">Writing and maintenance</td>
<td style="text-align: left;">Mathematical exposition, build dependencies and provenance [halmos; knuth; buildsystems; dekleer; workflowprovenance]</td>
</tr>
<tr>
<td style="text-align: left;">Understanding and reuse</td>
<td style="text-align: left;">Explanatory generality, digestion and research possibilities [kra; cohn; sanderson; essays; taomining; litt; tao2026]</td>
</tr>
<tr>
<td style="text-align: left;">Different community views</td>
<td style="text-align: left;">Declarations, dissent, benchmarks, research infrastructure and pace [fieldsdecl; chu; greenletter; gowers; ringer; koukoulopoulos; antieau]</td>
</tr>
<tr>
<td style="text-align: left;">Mathematical antecedents</td>
<td style="text-align: left;">Weighted support, totient ranks and arithmetic separation [paper257; erdos1968; duverneytachiya; paper249; coons; martin; yazdani]</td>
</tr>
<tr>
<td style="text-align: left;">Other mathematical records</td>
<td style="text-align: left;">Running LCM, lemniscates and cross-problem connections [paper269; fan269; loxtonvdp1977; bugeaudlaurent2023; erdosgraham; akiyamakaneko; ehp1958; erdos1041; aniforum; fcpr; synthesis]</td>
</tr>
</tbody>
</table>
<figcaption>Sources grouped by the roles for which the original accounts cite them, rather than by a performance ranking; the accompanying mathematical attribution distinguishes original results, refinements and independent rediscovery.</figcaption>
</figure>

<div class="thebibliography">

999 T. F. Bloom, *Erdős problems*, [erdosproblems.com](https://www.erdosproblems.com), accessed September 2026.

W. Cook, *Weighted and Covered Supports for Mersenne Subseries*, short paper on Erdős Problem 257, September 2026, [`PDF`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/paper/257/erdos-257-mersenne-support-subseries.pdf).

P. Erdős, *On the irrationality of certain series*, Math. Student 36 (1968), 222–226 (issued 1969), [scan](https://users.renyi.hu/~p_erdos/1969-09.pdf).

D. Duverney and Y. Tachiya, *Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*, Forum Math. 31 (2019), 1557–1566, [DOI](https://doi.org/10.1515/forum-2018-0299).

B. Kra, *Deep theorems were scarce and difficult and so became an effective mechanism to identify deep thought. AI has broken this system*, guest post on *What’s new*, 13 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/13/deep-theorems-were-scarce-and-difficult-and-so-became-an-effective-mechanism-to-identify-deep-thought-ai-has-broken-this-system/).

H. Cohn, *The technical debt of AI-generated mathematics*, guest post on *What’s new*, 15 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/15/the-technical-debt-of-ai-generated-mathematics/).

T. Tao, thread on mining open problems, Mathstodon, 8 September 2026, [thread](https://mathstodon.xyz/@tao/117237320796901560).

Twenty-five Fields Medallists, *A severe misalignment of AI in mathematics*, declaration posted on *What’s new*, 11 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/11/a-severe-misalignment-of-ai-in-mathematics/).

G. Sanderson, *If math is more than proof, we need to better celebrate the rest of it*, guest post on *What’s new*, 18 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/18/if-math-is-more-than-proof-we-need-to-better-celebrate-the-rest-of-it/).

Advisory Group on Mathematics and Artificial Intelligence at IAS, *Responsible Release of AI-Generated Mathematics*, 29 September 2026, [recommendations](https://agmai.org/general-sep29/), [PDF](https://agmai.org/wp-content/uploads/2026/09/recommendations.pdf).

L. de Moura and S. Ullrich, *The Lean 4 Theorem Prover and Programming Language*, in *Automated Deduction, CADE 28*, Lecture Notes in Computer Science 12699, 2021, pp. 625–635, [DOI](https://doi.org/10.1007/978-3-030-79876-5_37).

P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L’Enseignement Mathématique 28, 1980, p. 61.

W. Cook, *Integral Relations among Totient Sections*, short paper on Erdős Problem 249, revised 30 September 2026, [`PDF`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/paper/249/erdos-249-binary-totient-series.pdf).

M. Coons, *(Non)Automaticity of number theoretic functions*, J. Théor. Nombres Bordeaux 22 (2010), 339–352, [DOI](https://doi.org/10.5802/jtnb.718), Theorem 3.2.

G. Martin, *Simultaneous inequalities among values of the Euler phi-function*, 2006, [arXiv:math/0603053v1](https://arxiv.org/abs/math/0603053v1), Theorem 1.

S. Yazdani, *Multiplicative functions and $`k`$-automatic sequences*, J. Théor. Nombres Bordeaux 13 (2001), 651–658, [Numdam](https://www.numdam.org/item/JTNB_2001__13_2_651_0/).

W. Cook, *Reading Eight Erdős Problems Together*, synthesis paper, September 2026, [source, including the periodic-chain theorem](https://github.com/wcook04/plectis-erdos/blob/af1462ce/paper/synthesis/optimal-sparse-perturbations.tex).

T. Feng, T. Trinh, G. Bingham, et al., *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the Erdős Problems*, 2026, [arXiv](https://doi.org/10.48550/arXiv.2601.22401).

Lean FRO, *Comparator*, 2025, [GitHub](https://github.com/leanprover/comparator).

`ammkrn`, *nanoda_lib*, an independent type checker for Lean 4, [GitHub](https://github.com/ammkrn/nanoda_lib).

T. F. Bloom, *Erdős Problem \#1041*, [erdosproblems.com](https://www.erdosproblems.com/1041), accessed September 2026.

P. Erdős, F. Herzog and G. Piranian, *Metric properties of polynomials*, J. Analyse Math. 6 (1958), 125–148, [DOI](https://doi.org/10.1007/BF02790232).

`ani`, post in the Problem 1041 discussion thread, 7 September 2026, [erdosproblems.com forum](https://www.erdosproblems.com/forum/thread/1041#post-8861).

Formal Conjectures, pull request 6505, *Erdős 1041: mark solved with answer(False) and link a formal proof*, merged 23 September 2026, [GitHub](https://github.com/google-deepmind/formal-conjectures/pull/6505).

T. Zheng, X. Wu, Z. Zhang, et al., *Dream-RSI: Recursive Self-Improvement through Evolving Worlds*, 2026, [arXiv:2609.14858](https://arxiv.org/abs/2609.14858).

J. H. Loxton and A. J. van der Poorten, *Arithmetic properties of certain functions in several variables III*, Bull. Austral. Math. Soc. **16** (1977), 15–47.

Y. Bugeaud and M. Laurent, *Transcendence and continued fraction expansion of values of Hecke–Mahler series*, Acta Arith. **209** (2023), 59–90.

W. Cook, *Distinct running least common multiples*, short paper on Erdős Problem 269, September 2026, [`PDF`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/paper/269/erdos-269-three-prime-running-lcm.pdf).

S. Fan, comment on Erdős Problem \#269, erdosproblems.com forum, 26 June 2026, [forum post](https://www.erdosproblems.com/forum/thread/269#post-7218).

N. Patel, A. Rammal, A. Hayat, R. Munos, and J. Kempe, *Learning to Discover Interesting Mathematics*, arXiv:2609.28603v1, 2026, [arXiv:2609.28603v1](https://arxiv.org/abs/2609.28603v1).

S. Chen, K. Marwaha, X. Lu, H. Yuen, and T. Peng, *Prove2Me: An Open Collaborative Platform for Scaling Math Formalization*, 2026, [arXiv](https://doi.org/10.48550/arXiv.2608.28433).

T. Feng, T. H. Trinh, G. Bingham, et al., *Towards Autonomous Mathematics Research*, 2026, [arXiv](https://doi.org/10.48550/arXiv.2602.10177).

T. Tao, *AI contributions to Erdős problems*, [GitHub](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems), accessed September 2026.

T. Ringer, *Becoming a benchmark*, guest post on *What’s new*, 17 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/17/becoming-a-benchmark/).

P. Massot, *leanblueprint*, plasTeX plugin for Lean formalisation blueprints, 2020, [software repository](https://github.com/PatrickMassot/leanblueprint).

Y. Zhang, Y. Sun, T. Suzuki, J. D. Lee, and F. Liu, *LeanMarathon: Toward Reliable AI Co-Mathematicians through Long-Horizon Lean Autoformalization*, 2026, [arXiv:2606.05400](https://arxiv.org/abs/2606.05400).

S. Hattori, T. Matsuzaki, and M. Fujiwara, *Natural Language Translation of Formal Proofs through Informalization of Proof Steps and Recursive Summarization along Proof Structure*, in *Proceedings of the 18th International Natural Language Generation Conference*, 2025, pp. 376–389, [ACL Anthology](https://aclanthology.org/2025.inlg-main.23/).

S. Akiyama and H. Kaneko, *Multiplicative analogue of Markoff–Lagrange spectrum and Pisot numbers*, Adv. Math. 380 (2021), 107547, p. 3, reporting the theorem of A. Dubickas, J. Number Theory 117 (2006), 222–239, [arXiv:1911.06170v6](https://arxiv.org/abs/1911.06170v6).

K. Yang et al., *LeanDojo: Theorem Proving with Retrieval-Augmented Language Models*, NeurIPS 2023, Datasets and Benchmarks Track, [arXiv:2306.15626](https://arxiv.org/abs/2306.15626).

C. Li, Z. Lai, D. An, J. Hu, and Z. Wen, *Advancing Mathematical Research via Human-AI Interactive Theorem Proving*, 2025, [arXiv:2512.09443v2](https://arxiv.org/abs/2512.09443v2).

U. Kohlenbach, *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*, Springer Monographs in Mathematics, Springer, Berlin, 2008.

A. Gandhi, A. R. Tadipatri, and T. Gowers, *Automatically Generalizing Proofs and Statements*, in *16th International Conference on Interactive Theorem Proving*, LIPIcs 352, 2025, pp. 12:1–12:18, [DOI](https://doi.org/10.4230/LIPIcs.ITP.2025.12).

Lean community, *Batteries*, the `unusedArguments` linter in `Batteries/Tactic/Lint/Misc.lean`, [GitHub](https://github.com/leanprover-community/batteries), accessed September 2026.

J. Xin, A. Schneidman, C. Cummins, K. Ram, S. Ganesh, and J. Limperg, *AXLE: A Cloud Infrastructure for Lean 4 Theorem Proving Utilities*, 2026, [arXiv:2606.26442](https://arxiv.org/abs/2606.26442).

X. Li, N. Peng, S. Severini, and P. Shafto, *The Network Structure of Mathlib*, 2026, [arXiv:2604.24797](https://arxiv.org/abs/2604.24797).

F. Huch, *Structure in Theorem Proving: Analyzing and Improving the Isabelle Archive of Formal Proofs*, extended abstract, 2022, [arXiv:2209.13305](https://arxiv.org/abs/2209.13305).

J. de Kleer, *An assumption-based TMS*, Artificial Intelligence 28 (1986), 127–162, [DOI](https://doi.org/10.1016/0004-3702(86)90080-9).

A. Mokhov, N. Mitchell, and S. Peyton Jones, *Build Systems à la Carte*, Proc. ACM Program. Lang. 2 (ICFP), 2018, article 79, [DOI](https://doi.org/10.1145/3236774).

T. Zhu, J. Clune, J. Avigad, A. Q. Jiang, and S. Welleck, *Premise Selection for a Lean Hammer*, 2025, revised 2026, [arXiv:2506.07477](https://arxiv.org/abs/2506.07477).

J. Limperg and A. H. From, *Aesop: White-Box Best-First Proof Search for Lean*, in *Proceedings of the 12th ACM SIGPLAN International Conference on Certified Programs and Proofs*, 2023, pp. 253–266, [DOI](https://doi.org/10.1145/3573105.3575671).

Lean community, *Plausible*, a property testing framework for Lean 4, [GitHub](https://github.com/leanprover-community/plausible), accessed September 2026.

H. Chockler, A. Gurfinkel, and O. Strichman, *Beyond Vacuity: Towards the Strongest Passing Formula*, Form. Methods Syst. Des. 43 (2013), 552–571, [DOI](https://doi.org/10.1007/s10703-013-0192-6).

C. Kaliszyk and J. Urban, *Lemma Mining over HOL Light*, LPAR-19, LNCS 8312, 2013, pp. 503–517, [DOI](https://doi.org/10.1007/978-3-642-45221-5_34).

M. Johansson, D. Rosén, N. Smallbone, and K. Claessen, *Hipster: Integrating Theory Exploration in a Proof Assistant*, CICM 2014, LNCS 8543, pp. 108–122, [DOI](https://doi.org/10.1007/978-3-319-08434-3_9).

K. Ellis et al., *DreamCoder: Growing Generalizable, Interpretable Knowledge with Wake-Sleep Bayesian Program Learning*, 2020, [arXiv:2006.08381](https://arxiv.org/abs/2006.08381).

H. Wang, H. Xin, et al., *LEGO-Prover: Neural Theorem Proving with Growing Libraries*, ICLR 2024, [arXiv:2310.00656](https://arxiv.org/abs/2310.00656).

Y. Zhang, J. Sun, et al., *DreamProver: Evolving Transferable Lemma Libraries via a Wake-Sleep Theorem-Proving Agent*, 2026, [arXiv:2604.26311](https://arxiv.org/abs/2604.26311).

W. Ye, Z. Guan, et al., *ProofEvolve: Neuro-Symbolic Evolution for Formal Automated Theorem Proving*, 2026, [arXiv:2608.26334](https://arxiv.org/abs/2608.26334).

S. Böhme and T. Nipkow, *Sledgehammer: Judgement Day*, IJCAR 2010, LNCS 6173, pp. 107–121, [DOI](https://doi.org/10.1007/978-3-642-14203-1_9).

I. Berlot-Attwell, T. Sesterhenn, F. Rudzicz, and X. Si, *Is This LLM Library Learning? Evaluation Must Account For Compute and Behaviour*, EACL 2026, pp. 3534–3568, [DOI](https://doi.org/10.18653/v1/2026.eacl-long.163).

Y. Fu, P. Liu, Z. Wang, and K. Yuan, *Proof-Refactor: Refactoring Generated Formal Proofs into Modular Artifacts*, 2026, [arXiv:2606.03743](https://arxiv.org/abs/2606.03743).

N. Onda et al., *LeanConjecturer: Automatic Generation of Mathematical Conjectures for Theorem Proving*, 2025, [arXiv:2506.22005](https://arxiv.org/abs/2506.22005).

D. Litt, *A beginning for mathematics*, 13 September 2026, [blog post](https://www.daniellitt.com/blog/2026/9/13/a-beginning-for-mathematics/).

T. Chu, *The AI dissenter viewpoint*, *Proofs and Prompts*, 9 August 2026, [blog post](https://proofsandprompts.com/2026/08/09/the-ai-dissenter-viewpoint/).

B. Green and forty-one other Fellows and Foreign Members of the Royal Society, *Open letter to Sir Paul Nurse, President of the Royal Society*, *Proofs and Prompts*, 17 September 2026, [blog post](https://proofsandprompts.com/2026/09/17/open-letter-to-sir-paul-nurse-president-of-the-royal-society/).

W. T. Gowers, *Why I didn’t sign the Fields medallists’ letter*, 17 September 2026, [blog post](https://gowers.wordpress.com/2026/09/17/why-i-didnt-sign-the-fields-medallists-letter/).

D. Koukoulopoulos, *A CERN for AI-assisted science?*, guest post on *What’s new*, 17 September 2026, [blog post](https://terrytao.wordpress.com/2026/09/17/a-cern-for-ai-assisted-science/).

B. Antieau, *Fast math/slow math*, 15 September 2026, [blog post](https://antieau.github.io/2026/09/15/fast-math-slow-math.html).

D. E. Knuth, T. Larrabee and P. M. Roberts. *Mathematical Writing*. Stanford report CS1193, based on the autumn 1987 course, Section 1.

Dayu Yang et al., *DocAgent: A Multi-Agent System for Automated Code Documentation Generation*, arXiv:2504.08725v3, 2025, Sections 2–3.

Xinchen Wang, Ruida Hu, Cuiyun Gao, Pengfei Gao, and Chao Peng. *Evaluating Repository-level Software Documentation via Question Answering and Feature-Driven Development*. arXiv:2604.06793v1, 2026.

Huajian Xin, Luming Li, Xiaoran Jin, Jacques Fleuriot, and Wenda Li. *APE-Bench: Evaluating Automated Proof Engineering for Formal Math Libraries*. arXiv:2504.19110v3, 2026.

Auguste Poiroux, Gail Weiss, Viktor Kunčak, and Antoine Bosselut. *Reliable Evaluation and Benchmarks for Statement Autoformalization*. arXiv:2406.07222v3, 2025.

T. Zhu, P. Monticone, J. Avigad and S. Welleck. *LeanArchitect: Automating Blueprint Generation for Humans and AI*. [arXiv:2601.22554v1](https://arxiv.org/abs/2601.22554v1), 2026, Methods and Case Studies.

M. Bolan et al. *The Equational Theories Project: Advancing Collaborative Mathematical Research at Scale*. [arXiv:2512.07087v2](https://arxiv.org/abs/2512.07087v2), 2025, Project Management and Data Management.

The mathlib Community. *The Lean Mathematical Library*. CPP 2020. DOI: [10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824).

Google DeepMind. *Formal Conjectures*. [Repository README](https://github.com/google-deepmind/formal-conjectures), consulted 29 September 2026; descriptive context only.

A. Novikov et al. *AlphaEvolve: A coding agent for scientific and algorithmic discovery*. [arXiv:2506.13131v1](https://arxiv.org/abs/2506.13131v1), 2025, Task Specification and Evolution.

B. Georgiev, J. Gómez-Serrano, T. Tao and A. Z. Wagner. *Mathematical exploration and discovery at scale*. [arXiv:2511.02864v3](https://arxiv.org/abs/2511.02864v3), 2025.

C. E. Brown, C. Kaliszyk and J. Urban. *Agent Hunt: Bounty Based Collaborative Autoformalization With LLM Agents*. [arXiv:2603.06737v1](https://arxiv.org/abs/2603.06737v1), 2026.

M. Kripner and M. Straka. *OpenProver: Agentic and Interactive Theorem Proving with Lean 4*. [arXiv:2607.09217v1](https://arxiv.org/abs/2607.09217v1), 2026, State and Memory Management.

D. Ma et al. *OProver: A Unified Framework for Agentic Formal Theorem Proving*. [arXiv:2605.17283v1](https://arxiv.org/abs/2605.17283v1), 2026, Introduction.

Z. Yang et al. *CircuitProver: Agentic Lean 4 Theorem Proving with Reusable Circuit Proof Library for Hardware Verification*. [arXiv:2607.27259v1](https://arxiv.org/abs/2607.27259v1), 2026.

H. Wijk et al. *RE-Bench: Evaluating frontier AI R&D capabilities of language model agents against human experts*. [arXiv:2411.15114v1](https://arxiv.org/abs/2411.15114v1), 2024; official abstract used here.

P. R. Halmos. *How to Write Mathematics*. L’Enseignement Mathématique 16 (1970), 123–152; sections on organising a mathematical presentation.

Various authors. *Writings on AI and Mathematics*. Supplied anthology, `AI_ESSAYS_SOURCE.pdf`, snapshot 22 September 2026; Kra, pp. 31–33; Riehl, pp. 39–40; Cohn, pp. 41–44; Gowers, pp. 55–60; Sanderson, pp. 73–77. Riehl’s essay is also available as [Why I do mathematical research](https://terrytao.wordpress.com/2026/09/14/why-i-do-mathematical-research/).

L. Becker et al., *A Blueprint for the Formalization of Carleson’s Theorem on Convergence of Fourier Series*, 2025, [arXiv:2405.06423](https://doi.org/10.48550/arXiv.2405.06423).

L. Aniva, C. Sun, B. Miranda, C. Barrett, and S. Koyejo, *Pantograph: A Machine-to-Machine Interaction Interface for Advanced Theorem Proving, High Level Reasoning, and Data Extraction in Lean 4*, in *Tools and Algorithms for the Construction and Analysis of Systems*, 2025, pp. 116–137, [DOI](https://doi.org/10.1007/978-3-031-90643-5_6).

S. Kurgan et al., *TheoremGraph: Bridging Formal and Informal Mathematics*, 2026, [arXiv:2606.25363](https://doi.org/10.48550/arXiv.2606.25363).

J. Asher, *LeanExplore: A Search Engine for Lean 4 Declarations*, 2025, [arXiv:2506.11085](https://doi.org/10.48550/arXiv.2506.11085).

G. Gao et al., *LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving*, 2026, [arXiv:2605.13137](https://doi.org/10.48550/arXiv.2605.13137).

A. Baanen, M. R. Ballard, J. Commelin, B. Gin-ge Chen, M. Rothgang, and D. Testa, *Growing Mathlib: Maintenance of a Large Scale Mathematical Library*, in *Intelligent Computer Mathematics*, 2025, [arXiv:2508.21593](https://doi.org/10.48550/arXiv.2508.21593).

B. Yanahama and A. Sannai, *Lean Atlas: An Integrated Proof Environment for Scalable Human–AI Collaborative Formalization*, 2026, [arXiv:2604.16347](https://doi.org/10.48550/arXiv.2604.16347).

R. Souza, T. Poteet, B. Etz, D. Rosendo, A. Gueroudji, W. Shin, P. Balaprakash, and R. Ferreira da Silva, *LLM Agents for Interactive Workflow Provenance: Reference Architecture and Evaluation Methodology*, WORKS at the ACM/IEEE International Conference for High Performance Computing, Networking, Storage and Analysis, 2025, [DOI](https://doi.org/10.1145/3731599.3767582).

S. Abedu, S. Khatoonabadi, and E. Shihab, *Synergizing LLMs and Knowledge Graphs: A Novel Approach to Software Repository-Related Question Answering*, 2024, revised 2025, [arXiv:2412.03815](https://arxiv.org/abs/2412.03815).

T. Tao, *Mathematics in the age of AI*, 2026, [arXiv:2608.16753](https://arxiv.org/abs/2608.16753).

D. P. Anderson, *BOINC: A Platform for Volunteer Computing*, Journal of Grid Computing 18 (2020), 99–122, [DOI](https://doi.org/10.1007/s10723-019-09497-9).

Great Internet Mersenne Prime Search, *GIMPS*, project documentation and discovery-credit record, [mersenne.org](https://www.mersenne.org/), accessed August 2026.

Polymath Project, *General polymath rules*, [project rules](https://polymathprojects.org/general-polymath-rules/), accessed August 2026.

Lean community, *Contributing to mathlib*, [contributor guide](https://leanprover-community.github.io/contribute/index.html), accessed August 2026.

Palomar Registry, *About Palomar* and *Contribution policy*, [registry documentation](https://palomar-registry.org/about) and [submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md), accessed August 2026.

J. Henkel, *The Mathematician’s Assistant: Integrating AI into Research Practice*, 2025, [arXiv:2508.20236](https://arxiv.org/abs/2508.20236).

J. Dekoninck et al., *The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathematical Proofs*, 2025, [arXiv:2506.21621](https://arxiv.org/abs/2506.21621).

NISO, *CRediT: Contributor Roles Taxonomy*, [role definitions](https://credit.niso.org/contributor-roles-defined/), accessed August 2026.

GitHub, *Preventing pwn requests*, GitHub Actions security guidance, [documentation](https://docs.github.com/en/actions/reference/security/secure-use), accessed August 2026.

M. Yuan et al., *End-to-End Testing of Open-Source Hardware Documentation Developed in Large Collaborations*, 2023, [arXiv:2309.05942](https://arxiv.org/abs/2309.05942).

</div>
