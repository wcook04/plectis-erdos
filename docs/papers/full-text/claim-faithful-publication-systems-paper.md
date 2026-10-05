<a id="claim-faithful-publication-systems-paper"></a>

# A Repository-Based System for Research and Publication

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Plectis is a repository-based research environment for retaining mathematical work across sessions and carrying selected results into publication. The public prototype brings questions, sources, proofs, computations and failed approaches together in eight problem collections. Its publication workflow records the formal-support status of paper statements and binds explanatory passages to cited sources, while keeping these records distinct. Researchers and agents choose the work; Python tools retrieve evidence, record Lean probes and regenerate views. Maintainers decide what to adopt, and a journal retains entered contributions and review decisions. A worked revision shows how an explanation can lose a hypothesis while its formal proofs remain valid. A historical author-run test rejected nine of ten false edits and accepted one false completion claim. Reader benefit, discovery rate and adoption by independent laboratories remain unmeasured.

<a id="sec:intro"></a>

# Introduction

<div id="systems-lifecycle">

</div>

Research continues across sessions, contributors and drafts. The next researcher needs more than the latest result: which question remains open, why an approach failed, and what justifies the claims already published. Even a preserved formal proof leaves room for a later explanation to drop a hypothesis or describe an unresolved step as complete. A usable research record must retain these distinctions as the work changes.

Plectis supports this work in a public repository. Questions, prior sources, computations, proofs and unresolved steps remain available alongside proposed contributions and their review. The prototype is a local research environment: a researcher or agent chooses what to investigate and which tools to invoke. Broader autonomous discovery and services for other scientific fields remain proposals (Section <a href="#sec:limits" data-reference-type="ref" data-reference="sec:limits">9</a>).

The architecture separates authored records from derived views and separates a tool’s output from a decision to adopt it. A successful proof probe can remain a session result; a revised explanation can remain a proposal. Acceptance updates the relevant source records, after which builders regenerate their indexes and summaries. Figure <a href="#fig:lifecycle" data-reference-type="ref" data-reference="fig:lifecycle">1</a> places these operations within the continuing research cycle.

Erdős Problems supplies the questions and their public discussion, while Lean and mathlib supply the formal language and library \[erdosproblems; lean4; mathlib\]. Formalisation blueprints link a written argument to named Lean declarations \[leanblueprint; leanarchitect\], and the Equational Theories Project maintains shared problem records \[etp\]. Prove2Me combines human-audited missions, source-linked milestones and separately submitted proofs, with intermediate results available for other agents to reuse \[prove2me, Sections 3–4\].

The design question here is how to keep a publication aligned with its supporting work as both are revised. A paper assertion, its formal supports, its explanation and the decision to accept a change need separate identities and links. The implementation makes these relationships inspectable and checks specified forms of disagreement. Deciding whether the explanation preserves the mathematics remains a review task.

Section <a href="#sec:world" data-reference-type="ref" data-reference="sec:world">2</a> describes the records, tools and responsibilities. Sections <a href="#sec:example" data-reference-type="ref" data-reference="sec:example">3</a>–<a href="#sec:paper" data-reference-type="ref" data-reference="sec:paper">5</a> follow a proposed explanation change through checking, review and integration. We then describe contributions, report the available observations and compare related systems. Appendix <a href="#app:repro" data-reference-type="ref" data-reference="app:repro">10</a> explains how to inspect the work; Appendix <a href="#app:worked-proof" data-reference-type="ref" data-reference="app:worked-proof">11</a> develops the mathematical example; Appendix <a href="#app:attribution" data-reference-type="ref" data-reference="app:attribution">12</a> gives further examples of scope and attribution; Appendix <a href="#app:source-map" data-reference-type="ref" data-reference="app:source-map">13</a> groups the wider references by purpose.

<figure id="fig:lifecycle" data-latex-placement="H">

<figcaption>The research and publication cycle. Arrows label work performed on artifacts, not logical implications or automatic approval. A reviewed source revision precedes rebuilding and inspection. The journal retains explicitly entered returns and decisions; source checks do not decide whether an explanation preserves the mathematics.</figcaption>
</figure>

<a id="sec:world"></a>

# A repository organised around problems

<div id="systems-scaling">

</div>

<a id="stored-records-and-derived-views"></a>

## Stored records and derived views

The repository stores research state in files. Lean and manuscript sources contain arguments; claim records state selected assertions and open obligations; evidence records identify support; the journal retains entered returns and decisions. Indexes, source coordinates and status summaries are derived views of these inputs. Freshness checks report disagreement with the inputs, and builders regenerate the views. Neither operation adopts a claim. The [`architecture guide`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/ARCHITECTURE.md) identifies the source of each view, so repairs belong in the owning record rather than a hand-edited summary.

Publication uses two correspondence records. The coverage ledger follows a *paper occurrence*: a labelled assertion in a particular manuscript, identified by its source location and statement digest. It lists registered Lean supports and their evidence status. A stronger formal result also needs an authored relation note, bound to both statements, explaining how it yields the printed claim. The passage ledger follows explanatory text instead: it records the passage, cited source spans, evidence class and rationale. The first record asks what supports the statement; the second makes the explanation’s sources available for review. Neither generates the prose from a proof.

<a id="finding-the-relevant-work"></a>

## Finding the relevant work

A problem collection preserves more than its successful proofs. Counterexamples to proposed extensions, exact experiments, corrected references and the reasoning behind failed approaches remain with the question, so later work can inspect them before choosing another route. Four views provide entry points without requiring a full Lean build (Figure <a href="#fig:world" data-reference-type="ref" data-reference="fig:world">2</a>).

A *declaration* is a named Lean definition, theorem or lemma. The declaration index locates it; the dependency index follows the declarations used by selected results. The interpretation graph adds authored accounts of declarations and their connections. The claim registry selects assertions for public reporting and records their status and remaining obligations.

<figure id="fig:world" data-latex-placement="htbp">
<div class="minipage">
<p><strong>For each problem:</strong> the question and literature, Lean statements and proofs, computations and certificates, claims and open obligations, failed approaches, and the paper with its supporting record.</p>
<table>
<thead>
<tr>
<th style="text-align: left;">View available without a Lean build</th>
<th style="text-align: left;">Question it answers</th>
</tr>
</thead>
<tbody>
<tr>
<td style="text-align: left;">Declaration index</td>
<td style="text-align: left;">Where is the declaration? Source locations are exhaustive within the inventory.</td>
</tr>
<tr>
<td style="text-align: left;">Dependency index</td>
<td style="text-align: left;">Which declarations does this result use? Exact edges are available for selected starting declarations.</td>
</tr>
<tr>
<td style="text-align: left;">Interpretation graph</td>
<td style="text-align: left;">How has the work been interpreted? Authored accounts are selective and largely contextual, not individual proof reviews.</td>
</tr>
<tr>
<td style="text-align: left;">Claim registry</td>
<td style="text-align: left;">What is being claimed, with which status and open obligations? Only selected assertions have claim records.</td>
</tr>
</tbody>
</table>
<p>Across the corpus: 8 problems, 1,903 Lean modules and 24 registered papers. The claim registry contains 160 claims in eight statuses, with 19 open obligations.</p>
</div>
<figcaption>Contents of a problem collection and the four ways to inspect the recorded work. The counts refer to the whole corpus. Source locations, dependency edges, interpretations and claim statuses answer different questions.</figcaption>
</figure>

A reader can start from a claim, locate its declarations, follow the recorded dependencies and request the source lines relevant to a question. The views have different coverage: declaration locations are exhaustive within the inventory, dependency edges are exact for selected starting declarations, and interpretations are selective and largely contextual. An interpretation entry is not a record of individual proof review. Lookup identifies source; it records no execution. A question requiring a Lean check instead calls for a focused build and inspection of its recorded result.

<a id="operations-on-the-records"></a>

## Operations on the records

The entry points below act on the same repository records. They support a research iteration; their order of use is chosen by the researcher or agent.

<div class="center">

| Component | Input, output and responsibility |
|:---|:---|
| Task routing | [`agent_entry.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/agent_entry.py) maps a stated task to instructions, relevant files and commands. It routes a request rather than choosing the research question. |
| Evidence retrieval | [`query_corpus.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/query_corpus.py) returns problem, claim, declaration and paper-source records from the indexes. |
| Proof sessions | [`proof_workbench.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/proof_workbench.py) stores notes and submitted Lean probes, obtains verdicts from Lean, and binds a session claim to an accepted probe. |
| Statement evidence | [`paper_evidence.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/paper_evidence.py) locates each registered support at the recorded revision and checks its source and verification bindings; [`paper_claim_evidence.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/paper_claim_evidence.py) derives status and gap reports from those records. |
| Editorial exchange | [`short_paper_writer.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/short_paper_writer.py) audits manuscripts and packages proposed revisions without applying or approving the return. |
| Research history | [`research_record.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/research_record.py) verifies the journal of entered returns and dispositions and reports the outstanding milestones of recorded outputs. |
| Derived views | [`refresh_projections.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/refresh_projections.py) runs builders in dependency order; [`check_release.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/check_release.py) checks release contracts and freshness. |

</div>

A separate self-audit, [`systems_paper_evidence.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/systems_paper_evidence.py), checks this systems manuscript’s text and cited source bindings. These are implemented interfaces, not reports that every operation has been executed successfully.

An optional proof session illustrates the boundary between producing evidence and adopting a result. It stores notes, exact Lean inputs, process-derived receipts and a closing outcome. Its claim command requires an accepted probe and appends a session claim; it does not alter the reviewed public claim registry. The journal separately checks the sequence and hash chain of entered returns and dispositions. Later work can therefore inspect recorded inputs and decisions without the original conversation.

<a id="responsibilities-and-adoption"></a>

## Responsibilities and adoption

A researcher chooses the question and the evidence needed to answer it. An agent can inspect files, run tools and prepare a change under the public instructions; a contributor can also send an ordinary argument or explanation without a clone or an agent. The maintainer reviews scope, attribution and unresolved obligations before adoption. These are responsibilities, not necessarily different people or agents: contributor and reviewer may coincide. The [`agent quickstart`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/agents/README.md) and [`contribution guide`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/CONTRIBUTING.md) describe setup and review.

An iteration retrieves relevant work, investigates a question and returns an argument, experiment, correction or manuscript change with its evidence and limits. Review can adopt, revise, defer or reject the proposal. Accepted changes update the authored records; builders regenerate dependent views and release checks test consistency. Structured returns explicitly entered into the journal retain their dispositions. Ordinary issues and pull requests can reach review without a journal session (Section <a href="#sec:contribute" data-reference-type="ref" data-reference="sec:contribute">6</a>).

<a id="sec:example"></a>

# Worked case: reviewing an explanation

<span id="sec:predigestion" label="sec:predigestion"></span>

The worked case comes from Erdős Problem 257, which asks whether every infinite subseries of $`1+1/3+1/7+1/15+\cdots`$ is irrational. The theorem used here proves irrationality under a weighted summability condition on the retained exponents, with the same conclusion for every infinite subset and every integer base at least two. Dropping that condition would claim the unresolved general case. Appendix <a href="#app:worked-proof" data-reference-type="ref" data-reference="app:worked-proof">11</a> introduces the series, its antecedents and the proof.

Consider a contributor revising that explanation. The coverage row `res:weighted-support` in [`paper_lean_coverage.json`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/paper_lean_coverage.json) fixes the printed statement and lists two Lean supports. The explanation here has a separate [`passage record`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/systems_paper_sentences.json), citing the ordinary proof and a formal declaration. The claim-evidence builder derives status or gap reports; the passage checker tests text and source bindings.

Dropping the weighted hypothesis need not change either Lean proof. Editing the prose alone makes its passage binding stale; updating the binding as well can remove that warning without repairing the claim. The reviewer must therefore compare the proposed wording with the cited statements. Only after acceptance are the explanation and its record integrated and the publication views regenerated. This proposed edit illustrates the division of work; it is not a new test run.

<a id="sec:checks"></a>

# Proof and publication checks

<span id="sec:graph" label="sec:graph"></span> <span id="systems-trust"></span> The two formal supports in the example overlap (Figure <a href="#fig:theorem" data-reference-type="ref" data-reference="fig:theorem">6</a>). One gives fixed-base irrationality and the all-base conclusion for every infinite subset; the other states the fixed-base hereditary conclusion explicitly. The *registered support set* is the list attached to this paper occurrence, not the dependency closure of those proofs. The publication audit checks the full registered list even when one declaration suffices for a particular clause. That checks the record; it adds no mathematical hypothesis. The resolver follows registered named inputs and checks source revisions. A named input is an additional assumed result and must remain visible. By contrast, the weighted condition in the example is a hypothesis inside the proved statement. Revising either the statement or its source requires checking the corresponding records again; evidence for one revision cannot silently support another.

Figure <a href="#fig:checks" data-reference-type="ref" data-reference="fig:checks">3</a> separates the objects checked mechanically from the questions that remain for review.

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
<td style="text-align: left;">Passage and declared source bytes</td>
<td style="text-align: left;">Passage audit: text and source digests, with a recorded rationale.</td>
</tr>
<tr>
<td style="text-align: left;">Passage and mathematical meaning</td>
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

Each marked passage in this systems paper has a text record, specified source lines, an evidence class and a rationale. A passage may contain several sentences or a figure; it is a unit of source checking, not a grammatical category.

For the appendix's conclusion about infinite subsets, the sources explain why restriction preserves the weighted condition. The passage checker compares cryptographic hashes of the marked text and declared sources, rejects missing records or unbound passages, and requires a nonempty rationale. It does not assess whether the rationale justifies the text.

A matching digest establishes agreement with recorded bytes. It does not establish that the source entails the passage. In the worked revision, review must check the hypothesis and quantifiers even if both Lean links still resolve. Historical edit 8 tested a different failure: an unresolved step was described as complete (Table <a href="#tab:mutations" data-reference-type="ref" data-reference="tab:mutations">1</a>).

Execution is a separate question. A matching declaration type and reachable source link do not identify a successful continuous-integration run for that module. The probe interface takes verdicts from the specified Lean process; callers cannot submit their own verdict through it. An actor with filesystem access can still alter the implementation or stored record. The protocol distinguishes contributor and reviewer roles but does not technically force a second independent mathematician. No independent human mathematical review of the corpus is recorded.

<a id="sec:paper"></a>

# Publication and revision

<span id="sec:short" label="sec:short"></span><span id="sec:long" label="sec:long"></span><span id="sec:production" label="sec:production"></span> Publication selects from the research record and explains the selected result. The short paper states its conditions, makes the decisive step intelligible and directs the reader to the full argument. A dependency graph can locate the ingredients; it cannot choose their explanatory order. That choice requires reading the argument. The companion retains the complete proof and subsidiary cases. Correspondence links take a short-paper claim to the passage that supports it. The assembler inlines authored companion sections into a flat manuscript with their cross-references; it supplies no missing proof step. The reading guide invites readers to try an example, reconstruct a step or vary a hypothesis. The reader chooses the amount of help; an explaining agent is instructed to respect the requested depth. These authoring choices are not measurements of understanding.

<a id="permissions-and-tasks"></a>

## Permissions and tasks

An integrating agent may change the live checkout; an advisory agent returns a proposal against supplied sources. The repository calls these permissions Type A and Type B.

Permission to edit does not determine the task. Either assignment can concern research, proof or claim audit, literature and attribution, or exposition.

The expected product differs: a candidate argument, a source-located finding, an attribution proposal or a revised manuscript. Each needs the corresponding review.

Exposition preserves established hypotheses, conclusions and evidence status. A suspected mathematical defect is returned for a separate audit or research assignment.

<a id="from-frozen-inputs-to-an-accepted-revision"></a>

## From frozen inputs to an accepted revision

The writer first identifies the result, its antecedents, the difficult explanatory step and the unresolved questions, with source locations.

Selection remains an authorial decision; the manuscript checker tests source consistency and declared rules.

The exchange freezes selected manuscripts, required inputs, coverage records and audit rules under a manifest of their file digests. Writer and integrating reviewer then work from identifiable starting bytes, including any selected uncommitted changes.

An advisory model may work from that packet; a tool-enabled agent may prepare a proposal in a checkout. The packet identifies editable manuscript paths and read-only evidence and tools. Both routes return proposed changes for the same review of mathematical scope, wording and credit.

<figure id="fig:refinement" data-latex-placement="H">

<figcaption>The exposition workflow, read in numerical order, with the exchanged objects labelled. A proposal may be revised or declined at step 3; only accepted changes proceed to integration. The steps name responsibilities, which may be performed by the same agent. Rendering and inspection remain separate from source checks.</figcaption>
</figure>

The return checker verifies packet identity and permitted paths, accounts for statement changes, and checks retained labels, citation keys and bibliography entries. It audits the proposed manuscript in a temporary copy of the frozen sources, leaving the live repository unchanged.

It neither applies changes nor executes returned programs. A declared statement change remains an explicit review obligation.

The reviewer then checks the whole statement, its hypotheses and implication directions against all registered supports. An ordinary argument keeps its actual evidence class wherever formalisation is incomplete.

After acceptance, the integrating reviewer edits the owning sources and updates affected evidence bindings. For an assembled companion, the authored sections are edited before rebuilding the flat paper. Integration then regenerates evidence and navigation and includes inspection of the compiled pages, figures and proof links.

<a id="retaining-improvements"></a>

## Retaining improvements

A reusable writing lesson is a separate proposal, with an example and limits. Adopting it requires a reviewed change to the writing contract.

The packet and audit stages in Figure <a href="#fig:refinement" data-reference-type="ref" data-reference="fig:refinement">4</a> are implemented by [`short_paper_writer.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/short_paper_writer.py) and [`paper_refinement.py`](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/paper_refinement.py). A return can change the paper without changing the rules for later writers. Accepted lessons revise documents and instructions, not model weights; the procedure itself measures neither reader benefit nor autonomous discovery.

<a id="sec:contribute"></a>

# An open route for contributions

<span id="sec:loop" label="sec:loop"></span><span id="sec:cycle" label="sec:cycle"></span> <span id="systems-public"></span> <span id="systems-job-lifecycle"></span> The same review boundary applies to contributions beyond exposition. An idea or reference needs no clone; a patch identifies the public commit on which it was prepared. An executable return includes changed files, commands and results, resource use, surviving limitations, and credit for the people and tools involved. Figure <a href="#fig:contribute" data-reference-type="ref" data-reference="fig:contribute">5</a> follows both entry routes through triage and adoption. The protocol asks reviewers to reproduce executable evidence at the submitted base before reconciling it with current main, and to credit a substantive integration repair separately.

<figure id="fig:contribute" data-latex-placement="H">

<figcaption>Two entry routes and three possible review outcomes. Repository adoption applies to mathematical and methodological contributions; it establishes neither independent review nor acceptance by the wider mathematical community.</figcaption>
</figure>

<div id="systems-research-loop">

</div>

<div id="systems-coupled-goals">

</div>

For explicitly entered returns, the journal preserves an append-only, hash-linked sequence of dispositions. A later correction can withdraw an earlier endorsement without erasing that history. Ordinary issues and pull requests need not become journal events. Research investigates the question; stewardship compares a return with prior work, groups related results, reconciles affected papers and identifies what to investigate next. The researcher or agent chooses that next task. The public journal records entered decisions and does not schedule research. To decide what was learned, a later reviewer must compare the return with earlier work and inspect its evidence; a recorded disposition alone cannot supply that assessment.

<div id="systems-mathloop">

</div>

The repository’s proposed route from a local result to an upstream library includes a literature and library comparison, a proof of the extension and a second useful instance before expert submission \[mathlibcontrib\]. This route is not automated, and the supplied record reports no Mathlib contribution from it. Credit distinguishes an idea from its implementation, formalisation and exposition. CRediT supplies a vocabulary for roles, not an authorship decision \[credit\]. An attributed dependency or correction can record later use; it implies neither a scalar impact score nor a financial contract. Opening another problem collection still requires assembling a sourced question, explicit status, inspection routes and a review owner.

<a id="sec:instance"></a>

# Recorded observations

<span id="sec:evaluation" label="sec:evaluation"></span>

<a id="inventory-and-formal-support-status"></a>

## Inventory and formal-support status

The frozen inventory contains 689 paper occurrences, of which 640 have exact or specialising Lean support; 23 depend on a named input and 26 have no recorded Lean support. Of the 640 exact-or-specialising occurrences, 616 are recorded as compared and 24 as queued. These are occurrence counts, not counts of distinct theorems or independently reviewed proofs. Exact support matches the printed statement; specialising support yields it by specialization. Named-input entries retain an additional assumed result. An entry without Lean support may have an ordinary proof; neither of these last two groups is counted as fully covered.

<a id="historical-false-edit-trial"></a>

## Historical false-edit trial

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

The follow-up tested the intact baseline and only the escaped edit against an added check. It supplies no post-repair ten-of-ten result. In that recorded follow-up, the post-repair witness accepts the current README and rejects a test copy containing the false clause. The trial uses one corpus and the checker’s own selection of errors, with no manual-review control or ordinary continuous-integration comparator. The study locates a coverage boundary. Its nine rejections do not estimate how reliable the checker is.

<a id="local-integration-and-unperformed-reader-evaluation"></a>

## Local integration and unperformed reader evaluation

On 23 September 2026, a maintainer-operated agent accepted one architecture handoff into a local integration history after focused checks of return routing and architecture packaging. The contributor and reviewer were the same agent. The receipt records no public pull request, human review or independent outside clone replay.

A proposed reader study would hold the mathematical task fixed and compare an ordinary repository, an information-equivalent static briefing and the navigation tools. It would measure understanding and severe errors alongside preparation, use, review and repair costs, retaining missing returns, timeouts and disagreements. No independent writing comparison, blind grading run or cold-reader experiment is reported, so there is no comparative reader result. The records above document inventory, a checker failure and one local integration; general reliability, reader understanding and mathematical transfer remain unmeasured.

<a id="sec:related"></a>

# Related work

<span id="app:credit" label="app:credit"></span> The closest comparisons concern the objects a system records and the work it lets contributors perform. Lean and mathlib provide formal statements, proofs and a maintained library; blueprints connect declarations to exposition \[lean4; mathlib; leanblueprint\]. Prove2Me provides a more direct comparison for agent-assisted collaboration. Appendix <a href="#app:source-map" data-reference-type="ref" data-reference="app:source-map">13</a> retains the wider source map.

<a id="prove2me."></a>

#### Prove2Me.

We use its published version 2, dated 31 August 2026; the first version appeared on 28 August 2026 \[prove2me\]. Its basic unit is an immutable theorem statement, stored separately from the proofs submitted for it. A proof is checked against the target type in a pinned verification environment. A *proof-sketch* derives a target using imported theorem statements, some of which may remain open. Contributors can prove those children separately; the target becomes verified when the required children are verified. Immutability makes those local proofs composable without changing their targets \[prove2me, Sections 3.1–3.2 and 4.2\].

Human review is part of Prove2Me's design. A mission fixes a human-audited core of goals, definitions and milestones; each milestone pairs a source statement with its attested canonical formalisation. For read-back, an independent agent receives the Lean declaration and dependent definitions without the original source; a human compares its mathematical rendering with that source. Natural-language accounts accompany statements and proofs, statement descriptions support library search, and imports give contributors reuse credit. The discussion record also includes a disproved statement followed by a corrected replacement \[prove2me, Sections 3.3 and 4.3–4.5\]. Explanation, reuse, correction and shared agent work are therefore established parts of this comparison.

For correspondence with a source, the closest analogue is Prove2Me's milestone: both designs identify the mathematical statement whose formalisation is being reviewed. Our coverage record follows a particular paper occurrence and can list several overlapping formal supports, with a relation note explaining their connection to the printed claim. It is not a proof-sketch: listing those supports does not compose proof terms or discharge open lemmas. A separate passage record binds the explanation to sources and rationale, while entered contribution records retain revision decisions and role credit. The focus here is the consistency and review of these publication records across revisions. This difference of focus establishes neither priority for persistent research records nor a measured advantage over Prove2Me.

Polymath, BOINC and GIMPS supply precedents for small mathematical contributions and donated compute \[polymath; boinc; gimps\], while the Carleson blueprint shows formalisation organised into publicly claimable tasks \[carleson\].

The regeneration tools address the familiar build-system problem of keeping derived outputs consistent with their inputs \[buildsystems\]. They run an explicit ordered list of builders and then check the resulting views; this is not a general incremental scheduler. Source bindings and the journal add provenance for assertions and entered returns at particular revisions. Together these mechanisms make dependencies and changes available for inspection. Their effect on research efficiency and semantic correctness needs separate evaluation.

<a id="sec:limits"></a>

# Limits

<span id="sec:conclusion" label="sec:conclusion"></span> The prototype establishes a set of implemented record and review operations, with the limited observations in Section <a href="#sec:evaluation" data-reference-type="ref" data-reference="sec:evaluation">[sec:evaluation]</a>. It reports no comparative formalisation result or autonomous-optimisation experiment. Transfer to unseen mathematics and understanding by independent readers require direct evaluation. In particular, no controlled comparison shows that the contribution process converts compute into useful mathematics more effectively or increases discovery rate. There is also no evidence of inexpensive adoption by a new project or an advantage over an agent using a good README. Full scans and initial builds still have costs, and an open corpus cannot rule out prior model exposure to its contents.

Governance remains maintainer-centred. Review capacity is scarce and credit is contestable; openness alone does not equalise resources or resolve appeals. Repository adoption cannot confer acceptance by the wider mathematical community. Returned code is untrusted, and expensive or privileged continuous-integration jobs must not execute fork code with repository secrets \[githubsecurity\]. A volunteer-compute service and extensions to physical science remain proposals requiring their own validation, resource and safety governance.

The Advisory Group on Mathematics and Artificial Intelligence at IAS recommends distinguishing papers fully understood by a responsible mathematician from AI output that its human prompters do not understand, and asks AI laboratories to support subsequent community-led understanding \[agmai2026\]. Its 29 September 2026 statement gives concrete release expectations for attribution, exposition, formalisation and disclosure of the research process.

Several of these proposed release practices have counterparts in the records described here \[agmai2026, Section 2.B, Step I\]: the short paper and companion paper explain and attribute the argument, the paper-to-Lean ledger records formal correspondence and its limits, and the files prepared for formal comparison identify its inputs. Those records make the result inspectable; they do not certify a mathematician’s understanding. The architecture alone does not establish complete per-result model, prompt, time and cost disclosure, an account of campaign-wide selection and unsuccessful attempts, or an independent scholarly deposit. The further recommendations on funding community-led understanding and equitable model access address AI laboratories; this prototype does not demonstrate those institutional outcomes.

The immediate contribution is a way to continue work from an inspectable record: recover a claim’s conditions and supporting argument, understand the recorded limits, and submit a correction or extension against identified sources. Checking preserves specified links; review decides what the linked work justifies. Keeping both within the revision process is the purpose of the system.

<a id="app:repro"></a>

# Reading the materials and reproducing checks

The materials support three different tasks: reading a mathematical result, inspecting the records behind a published assertion, and rerunning checks. The first requires no Lean installation. The other two require the recorded sources and, for proof replay, the matching Lean environment. The following routes distinguish these tasks so that a successful document check is not mistaken for a reproduced proof.

<a id="read-a-result-and-follow-its-sources"></a>

## Read a result and follow its sources

Start with the [reading guide](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/READING_GUIDE.md). It offers a route through one problem and a route across the papers, including the synthesis *Reading Eight Erdős Problems Together* \[synthesis\]. For one result, read the short paper first, then follow its references to the argument, prior work and formal-support record. A reader using an agent can give it the [agent instructions](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/AGENTS.md); the [workbench guide](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/agents/AGENT_WORKBENCH.md) adds optional recorded proof sessions. Corrections and extensions follow the [contribution guide](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/CONTRIBUTING.md) and [credit policy](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/research-commons/CREDIT_POLICY.md).

<a id="inspect-the-records-and-rerun-document-checks"></a>

## Inspect the records and rerun document checks

To inspect the historical false-edit experiment, open the [experiment record](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/publication_evidence.json): it contains the ten-edit matrix and the limited follow-up described in Section <a href="#sec:checks" data-reference-type="ref" data-reference="sec:checks">4</a>. The [publication-check specification](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/publication_contract.json) states which checks are required. These are structured data files for tracing the reported evidence, not substitutes for the explanation in the paper.

To check this manuscript in a complete checkout, run the following from the public repository root:

> `python3 scripts/systems_paper_evidence.py`\
> `python3 scripts/build_systems_paper_counts.py`

The first checks the recorded links between passages and source excerpts, including their stored content hashes. The second compares the generated inventory with its source records. Success establishes agreement of these records; it does not establish that a passage correctly explains its source.

Proof replay is a separate task. The [Lean entry file](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/lean/Erdos249257.lean) and the [continuous-integration workflow](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/.github/workflows/lean.yml) identify formal build entry points. The [claim register](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/claims.json) records the curated assertions, and the [release-check script](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/scripts/check_release.py) checks the wider publication requirements. Use the revisions and environment recorded for the result being reproduced.

A writing packet is not a complete checkout. The public writer’s packet specification includes manuscripts, selected records and inspection tools, but no Lean source tree. Such a packet can support document checks without being sufficient for a full Lean, Comparator or release rerun.

<a id="locate-the-formal-supports-of-the-worked-example"></a>

## Locate the formal supports of the worked example

For the weighted criterion in Appendix <a href="#app:worked-proof" data-reference-type="ref" data-reference="app:worked-proof">11</a>, the [paper-to-Lean coverage record](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/docs/paper_lean_coverage.json) identifies two formal supports: a weighted criterion and a version whose conclusion explicitly covers every infinite subset. Figure <a href="#fig:theorem" data-reference-type="ref" data-reference="fig:theorem">6</a> shows the recorded links. The exact declaration names are provided for readers locating them in Lean.[^1] These entries support the stated conclusion; they do not assert line-by-line agreement between the ordinary proof and the Lean proofs.

The recorded Comparator runs are the [first comparison run](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35544127144) and the [second comparison run](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35624228171). Comparator checks a formal result against a separately stated challenge. These records concern the specified formal statements, not the historical attribution or the correctness of this paper’s explanation.

The reciprocal-summability criterion attributed to Erdős in Appendix <a href="#app:worked-proof" data-reference-type="ref" data-reference="app:worked-proof">11</a> has its own [formal proof](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean), also recorded in the second comparison run.[^2]

Both runs are recorded as compared. Preparation for submission to Palomar is recorded separately: the entries are prepared, not submitted. A comparison record is therefore not evidence of registry acceptance.

<figure id="fig:theorem" data-latex-placement="htbp">

<figcaption>The arrows show recorded support links, not proof dependencies. The audit checks both listed supports even where their mathematical roles overlap. The support hypothesis still needs explanation. The false paraphrase is illustrative, distinct from historical edit 8 in Table <a href="#tab:mutations" data-reference-type="ref" data-reference="tab:mutations">1</a>.</figcaption>
</figure>

<a id="interpret-the-recorded-inventory"></a>

## Interpret the recorded inventory

The recorded inventory counts occurrences of paper statements, rather than distinct new theorems. Its 689 entries comprise 498 with exact-or-stronger formal support, 142 obtained by specialising a formal result, 23 linked to a named formal ingredient only, and 26 with no registered Lean support. The last two categories do not certify the whole paper statement.

The contribution journal records 7 rounds and 25 returned contributions at the recorded journal revision.[^3] Of the rounds, 2 are sealed, meaning no further arrivals are expected. Of the returns, 18 have been admitted for integration and 7 remain unreviewed; admission does not itself record integration. Earlier private-history rounds do not constitute a complete public journal.

Explanatory text is recorded for 139,818 of the 152,386 authored theorem-like declarations (91.8%). Most of these descriptions provide surrounding context. This inventory measures the presence of recorded interpretations, not individual proof review or demonstrated reader understanding.

<a id="identify-the-version-and-the-earlier-design-accounts"></a>

## Identify the version and the earlier design accounts

Repository links in this paper identify fixed file versions, so that a reader can inspect the material cited even if the working repository later changes. Unless a link states otherwise, its revision is `992cf60a27ef`; the Comparator runs identify their own inputs. No new Lean or Comparator run was performed for this revision.

For archival identification, the initial unified manuscript was prepared from the frozen packet at `ced96e58b337`, a local integration commit rather than public main. The 29 September state report lists it under the earlier title *Problem-Sized Lean Worlds*.

This paper supersedes the two earlier design accounts described below. Cite a mathematical result by the paper and version actually used; cite repository software using its [software citation record](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/CITATION.cff) at the chosen commit or release tag.

*[From a Cold Clone to a Proof Receipt](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/paper/systems/cold-clone-to-proof-receipt.tex)* (August 2026) describes the declaration, dependency, interpretation and claim views and the optional recorded proof session. Its counts and audit figures belong to that snapshot; Section <a href="#sec:world" data-reference-type="ref" data-reference="sec:world">2</a> describes the current task entry and inspected implementation.

*[From Spare Compute to Cumulative Mathematics](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/paper/systems/open-source-mathematics-strategy.tex)* (September 2026) describes contribution roles, reproduction against the original inputs, subsequent integration and role credit. Section <a href="#sec:contribute" data-reference-type="ref" data-reference="sec:contribute">6</a> gives the current procedure. The earlier paper’s volunteer-compute services, inexpensive adoption by new laboratories and increased discovery rate remain proposals or unmeasured outcomes. These manuscripts explain the design’s history; they are not additional current specifications.

<a id="app:worked-proof"></a>

# The mathematical example: a criterion for irrationality

Section <a href="#sec:example" data-reference-type="ref" data-reference="sec:example">3</a> used a theorem whose explanation could become false by losing a hypothesis. Following the Problem 257 paper \[paper257\], this appendix introduces the series and earlier work, states the weighted criterion, gives an example of its reach, and explains the averaging proof. Each part identifies information that a faithful summary must retain. The formal-support records are in Appendix <a href="#app:repro" data-reference-type="ref" data-reference="app:repro">10</a>; the calculation is optional for readers interested only in the system.

<a id="the-question-and-its-antecedents"></a>

## The question and its antecedents

Begin with the series
``` math
1+\frac13+\frac17+\frac1{15}+\cdots
 =\sum_{a=1}^{\infty}\frac1{2^a-1}.
```
An infinite subseries retains the terms whose exponents belong to an infinite set $`A`$ of positive integers. We call $`A`$ the *support*: it specifies which terms are present. To allow other integer bases $`b\ge2`$, write
``` math
X_A(b)=\sum_{a\in A}\frac1{b^a-1}.
```
These series converge by comparison with a geometric series. The question concerns their arithmetic value: can an infinite choice of retained terms have a rational sum?

Problem 257 asks whether $`X_A(2)`$ is irrational for every infinite support $`A`$. The weighted theorem below gives a sufficient condition on $`A`$; it does not settle that unrestricted question \[paper257; erdosproblems\].

Erdős proved the all-base irrationality conclusion for pairwise coprime exponents satisfying $`\sum_{a\in A}1/a<\infty`$. He also stated that coprimality could be removed, without supplying the details \[erdos1968, pp. 222, 226\]. The Problem 257 paper gives a direct proof of that stated extension, as well as the weighted criterion used here \[paper257\].

Duverney and Tachiya provide a methodological antecedent: they choose an arithmetic progression by congruences and use averaging to control the remaining contribution \[duverneytachiya, Section 2, (2.3)–(2.9)\]. The Problem 257 paper credits that selection method. Its weighted proof uses an additional average over progression lengths, which recovers a factor needed to sum the error bounds. The sources thus supply a classical criterion, an averaging method and the weighted extension, respectively.

<a id="a-weighted-condition-on-the-retained-exponents"></a>

## A weighted condition on the retained exponents

The weighted condition gives a smaller contribution to exponents divisible by large powers of a fixed set of primes. For $`a=2^km`$ with $`m`$ odd, it replaces the reciprocal weight $`1/(2^km)`$ by $`1/[m(2^{2^k}-1)]`$. More generally, for a finite nonempty set $`P`$ of primes, the *$`P`$-part* of $`a`$ is $`h_P(a)=\prod_{p\in P}p^{v_p(a)}`$, where $`v_p(a)`$ is the exponent of $`p`$ in the prime factorisation of $`a`$. Thus $`h_{\{2\}}(2^km)=2^k`$.

The weighted-support theorem of the Problem 257 paper states that, if
``` math
\begin{equation}
\label{eq:worked-condition}
 W_{2,P}(A):=\sum_{a\in A}\frac{h_P(a)}{a(2^{h_P(a)}-1)}<\infty,
\end{equation}
```
then $`X_B(b)`$ is irrational for every integer $`b\ge2`$ and every infinite $`B\subseteq A`$ \[paper257, Theorem 1.2\].

The conclusion is *hereditary*: it applies to every infinite subset of $`A`$. For a fixed base $`b`$, write $`W_{b,P}(A)`$ for the sum in <a href="#eq:worked-condition" data-reference-type="eqref" data-reference="eq:worked-condition">[eq:worked-condition]</a> with $`2`$ replaced by $`b`$. The fixed-base version assumes $`W_{b,P}(A)<\infty`$ and gives the same hereditary conclusion at that base. We prove this version below and recover all integer bases from the base-two hypothesis.

<a id="why-the-weighted-condition-reaches-further"></a>

## Why the weighted condition reaches further

To see why the weight matters, compare it with the older condition $`\sum_{a\in A}1/a<\infty`$. Both are tests on the exponents; neither is needed merely for convergence of $`X_A(b)`$. The source paper gives
``` math
A_\star=\{2^km:k\ge1,\ m\text{ odd},\ 1\le m\le2^{2^k}\},\qquad P=\{2\}.
```
This set is arranged in disjoint layers according to the power $`2^k`$ dividing an exponent. Within layer $`k`$, reciprocal summation discounts each odd $`m`$ by $`2^{-k}`$; weighted summation discounts it by $`(2^{2^k}-1)^{-1}`$. The second discount is much smaller.

Write $`S_r=\sum_{1\le m\le2^r,\ m\ \mathrm{odd}}1/m`$ for the sum of odd reciprocals up to $`2^r`$; layer $`k`$ uses $`r=2^k`$. Grouping these integers into intervals $`[2^j,2^{j+1})`$ gives $`r/4\le S_r\le r`$ for integers $`r\ge2`$.

The reciprocal contribution of each disjoint layer is at least $`2^{-k}S_{2^k}\ge1/4`$. Its weighted contribution satisfies
``` math
\frac{S_{2^k}}{2^{2^k}-1}\le\frac{2^k}{2^{2^k}-1}\le2^{1-k},
```
so the layer contributions have a convergent geometric majorant in the weighted sum.

Thus $`\sum_{a\in A_\star}1/a`$ diverges, whereas $`W_{2,\{2\}}(A_\star)`$ converges. The weighted criterion therefore applies to some supports excluded by the reciprocal-summability condition. This is the source paper’s ordinary calculation, with no separate entry in the paper-to-Lean ledger \[paper257, calculation following the weighted proof\].

<a id="the-proof-by-two-averages"></a>

## The proof by two averages

Fix an integer base $`b\ge2`$, an infinite support $`A`$ and a finite nonempty set $`P`$ with $`W_{b,P}(A)<\infty`$. The proof has two parts. Rationality would force a certain positive remainder to be at least the reciprocal of a fixed denominator. Averaging will make that remainder smaller. The main difficulty is that one average leaves an error bound that cannot be summed using the hypothesis; a second average over powers of two supplies the missing factor.

<a id="the-lower-bound-under-rationality."></a>

#### The lower bound under rationality.

Suppose that $`X_A(b)=p/q`$ with integers $`p,q`$ and $`q>0`$. For a positive integer $`N`$, multiplication by $`b^N-1`$ separates an integer contribution from each summand, leaving
``` math
\begin{equation}
\label{eq:worked-displacement}
 \Delta_{b,A}(N)=\sum_{a\in A}\frac{b^{N\bmod a}-1}{b^a-1}
 =(b^N-1)X_A(b)-J_{b,A}(N),\qquad N\ge1,
\end{equation}
```
where $`J_{b,A}(N)=\sum_{a\in A,\,a\le N}\sum_{j=1}^{\lfloor N/a\rfloor}b^{N-ja}`$ is an integer. Here $`N\bmod a`$ is the remainder on dividing $`N`$ by $`a`$. The symbol $`\Delta`$ denotes the positive remainder after this particular integer is subtracted, not necessarily a fractional part in $`[0,1)`$.

Every summand is nonnegative, and one is positive because the infinite set $`A`$ contains an exponent larger than $`N`$. Hence $`q\Delta_{b,A}(N)`$ is a positive integer, and $`\Delta_{b,A}(N)\ge1/q`$.

We obtain a contradiction by finding a multiple $`N=tQ`$ with smaller remainder. Divisibility helps because the summand indexed by $`a`$ vanishes whenever $`a\mid Q`$.

Choose a finite nonempty $`F\subset A`$ outside which the weighted sum is less than $`\varepsilon`$, and make $`Q`$ a multiple of every element of $`F`$. Those terms then disappear for every $`t`$; we must control the remaining terms on average.

<a id="averaging-over-a-residue-period."></a>

#### Averaging over a residue period.

With $`b=2`$, $`Q=4`$ and $`a=6`$, the residues $`tQ\bmod a`$ are $`4,2,0`$, and the corresponding mean contribution to $`\Delta`$ is
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

The first term has the shape of the weighted hypothesis once suitable prime powers have been put into $`Q`$. The second has lost the factor $`1/a`$. Summability of the first therefore does not justify summing the unfinished-cycle bounds over all exponents. This is the difficulty that a single progression average leaves unresolved.

<a id="averaging-over-dyadic-lengths."></a>

#### Averaging over dyadic lengths.

The source proof averages over the $`M`$ lengths $`T=2^j`$, $`M\le j<2M`$; these powers-of-two lengths are called dyadic. Thus $`M`$ counts the lengths being averaged, whereas $`T`$ counts the terms in one progression average. For nonnegative weights $`\alpha_a`$ indexed by positive integers, with $`\sum_a\alpha_a/a<\infty`$, it uses
``` math
\begin{equation}
\label{eq:worked-dyadic}
 \sum_{j=M}^{2M-1}2^{-j}\sum_{a\le Q2^j}\alpha_a
 \le 2Q\sum_a\frac{\alpha_a}{a}.
\end{equation}
```
Indeed, a fixed $`a`$ enters only when $`2^j\ge a/Q`$, and the sum of the admissible $`2^{-j}`$ is at most $`2Q/a`$. This recovers the missing factor before summing over $`a`$. Dividing by the number $`M`$ of lengths then reduces the cost from $`2Q`$ to $`2Q/M`$.

<a id="choosing-the-modulus-and-the-averaging-lengths."></a>

#### Choosing the modulus and the averaging lengths.

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

This is the information the worked explanation must preserve: the restriction on the support, the distinction from earlier criteria, and the reason for the second average. The formal-support links identify proofs of the stated conclusion. They do not by themselves explain these choices or prevent a summary from dropping the hypothesis.

<a id="app:attribution"></a>

# Attribution and scope in three further examples

The following cases distinguish a result’s exact scope, its dependence on earlier work and its formal verification. They illustrate further information a faithful account must preserve, rather than steps in the preceding proof or additional systems experiments.

<a id="counting-repeated-terms-changes-the-question"></a>

## Counting repeated terms changes the question

A running least common multiple is the least common multiple of the terms seen so far in an increasing sequence. Its value can repeat. For integers with prime factors only $`2`$, $`3`$ and $`5`$, the source paper’s example begins $`1,2,6,12,60,60,120,360,360,\ldots`$ \[paper269\]. A reciprocal sum counting every occurrence contains $`1/60`$ twice; one counting distinct values contains it once.

The Problem 269 record proves a result for distinct running least common multiples. The original question counts them with multiplicity, so the result does not automatically answer it \[paper269\].

The same record credits Fan’s earlier public two-prime result despite an independently reported derivation, and separately identifies the relevant Hecke–Mahler series literature \[paper269; fan269; loxtonvdp1977; bugeaudlaurent2023\]. Independent derivation does not remove the obligation to cite prior work.

<a id="an-explicit-description-and-a-stronger-antecedent"></a>

## An explicit description and a stronger antecedent

The Euler totient $`\varphi(n)`$ counts the integers from $`1`$ to $`n`$ coprime to $`n`$. The Problem 249 paper studies its subsequences $`\varphi(k^j n+r)`$, where $`k\ge2`$ is fixed, $`j\ge0`$ and $`0\le r<k^j`$. For each level $`j`$, it describes the integer linear relations and gives an explicit basis \[paper249\]. Coons’s non-$`k`$-regularity theorem says that no finite set generates these subsequences over all levels. Martin’s stronger separation theorem already implies the independence needed for the basis; the explicit reductions and integral relations are a different contribution. The direct proof uses the Chinese remainder theorem and Dirichlet’s theorem on primes in arithmetic progressions, following an argument in Yazdani that Yazdani credits to Shallit \[coons; martin; yazdani\].

Reorganising a proof, making its consequences explicit and formalising it are distinguishable contributions. None makes an inherited ingredient new.

<a id="a-construction-its-formalisation-and-the-historical-question"></a>

## A construction, its formalisation and the historical question

Problem 1041 concerns connecting roots of a polynomial by short curves in a strict lemniscate: for a complex polynomial $`f`$, this is the region $`|f(z)|<1`$. The degree-seven counterexample construction is due to the forum contributor ani \[aniforum; erdos1041\]. The recorded Lean result refutes the exact statement in the Formal Conjectures repository; independent human review of its correspondence with the curve-length wording in the 1958 paper has not been recorded \[formalconjectures; fcpr; ehp1958\]. The construction, its formalisation and that historical correspondence are separate claims.

Readers inspecting the formal result can follow the [counterexample assembly](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/lean/ErdosProblems/Erdos1041/Counterexample/Assembly.lean) and the [Hausdorff-length proofs](https://github.com/wcook04/plectis-erdos/blob/992cf60a27efd8c34f437e347c413bb781d75c32/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean).[^4]

The coverage row records exact-or-stronger Lean support for these statements.

Comparator remains pending for this result, so its recorded Lean support should not be described as a completed formal comparison.

The other seven motivating targets remain unresolved in this work.

A revised statement must retain its scope, attribution and registered supports. Sharpening, merging or moving it requires renewed review of its relation to every support and named input.

<a id="app:source-map"></a>

# A reading map for the wider literature

Section <a href="#sec:related" data-reference-type="ref" data-reference="sec:related">8</a> compares the closest systems; Appendices <a href="#app:worked-proof" data-reference-type="ref" data-reference="app:worked-proof">11</a> and <a href="#app:attribution" data-reference-type="ref" data-reference="app:attribution">12</a> explain the mathematical antecedents used in the examples. Figure <a href="#fig:credit" data-reference-type="ref" data-reference="fig:credit">7</a> is a guide to the remaining references and to sources cited by the two historical design accounts in Appendix <a href="#app:repro" data-reference-type="ref" data-reference="app:repro">10</a>. Its groups indicate why a source is cited, not that every listed method is implemented here or that every work has been evaluated against this system.

<figure id="fig:credit" data-latex-placement="H">
<table>
<thead>
<tr>
<th style="text-align: left;">Area</th>
<th style="text-align: left;">Reason for citation</th>
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
<td style="text-align: left;">Explanation, mathematical understanding, reuse and research possibilities [kra; cohn; sanderson; essays; taomining; litt; tao2026]</td>
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
<figcaption>Reading map for this paper and its two historical predecessors. The groups record uses of sources, not a performance ranking or a list of implemented components. Appendices <a href="#app:worked-proof" data-reference-type="ref" data-reference="app:worked-proof">11</a> and <a href="#app:attribution" data-reference-type="ref" data-reference="app:attribution">12</a> distinguish mathematical antecedents, refinements and independent rediscovery.</figcaption>
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

[^1]: Both are in namespace `ErdosProblems.Erdos257.PaperCompleteR8`: `divisibilityWeightedClaim` and `finitePrimeWeighted_fixedBase_hereditary`. The coverage row is `res:weighted-support`; the weighted comparison entries are `PalomarCorpus/E257` and `E257bc`.

[^2]: The declaration is `Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal`; its comparison entry is `PalomarCorpus/E257av`, recorded as compared.

[^3]: Journal revision: `d3ad85269386`.

[^4]: The four declarations, all in namespace `Erdos1041.Counterexample`, are `erdos1041_counterexample`, `erdos1041_counterexample_hausdorff`, `erdos1041_hausdorff_negation` and `erdos1041_hausdorff_answer_false`.
