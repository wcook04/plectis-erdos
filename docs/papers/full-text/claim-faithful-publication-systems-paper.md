<a id="claim-faithful-publication-systems-paper"></a>

# Problem-Sized Lean Worlds

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Plectis is a public Lean repository organised into problem-sized research worlds, each combining formal mathematics with computations, literature and the questions still open. We describe how a result reaches a short paper through records of its statement, every registered support and the source bytes used in its explanation. A weighted-support criterion for reciprocal Mersenne series provides a worked example of this passage. The same records admit outside contributions and preserve credit when work is revised. In a historical test, nine of ten false edits were rejected, while a false claim about mathematical scope escaped. We locate the resulting division between automated checks and the interpretation required of authors and reviewers.

<a id="sec:intro"></a>

# Introduction

<div id="systems-lifecycle">

</div>

A formal theorem can outlive the session in which it was proved, yet its hypotheses, motivation and relation to an open question may be lost when it is turned into prose. We organise the research around a persistent problem world: the question, its sources, the formal and computational work already done, and the precise obligations that survive. Figure <a href="#fig:lifecycle" data-reference-type="ref" data-reference="fig:lifecycle">1</a> follows one claim from that world to a paper and back through a contribution.

<figure id="fig:lifecycle" data-latex-placement="htbp">

<figcaption>The life of one claim: arrows name the objects exchanged, the short and long accounts remain linked, and colours distinguish kinds of responsibility throughout the paper.</figcaption>
</figure>

Erdős Problems supplies the questions and their public discussion, while Lean and mathlib supply the formal language and library \[erdosproblems; lean4; mathlib\]. Blueprints already connect exposition to declarations \[leanblueprint; leanarchitect\], and persistent problem records and open agent collaboration have antecedents in ETP and Prove2Me \[etp; prove2me\]. Our publication tools add a check of the complete registered support set and bind the surrounding prose, including explanations and limitations, to specified source bytes.

The Advisory Group on Mathematics and Artificial Intelligence at IAS recommends distinguishing papers fully understood by a responsible mathematician from AI output that its human prompters do not understand, and asks AI laboratories to support subsequent community-led understanding \[agmai2026\]. Its 29 September 2026 statement gives concrete release expectations for attribution, exposition, formalization and disclosure of the research process.

The following sections describe the world, trace a weighted-support theorem through those records, and separate the checks from the judgements made when contributions enter the corpus.

<a id="sec:world"></a>

# A problem-sized Lean world

<div id="systems-scaling">

</div>

A world has one endpoint question and many possible contributions: a proof, a counterexample, an exact experiment, a corrected reference or an explanation of a failed method. We expose four views of the existing mathematics before asking a reader to compile Lean (Figure <a href="#fig:world" data-reference-type="ref" data-reference="fig:world">2</a>). The declaration atlas locates every declaration in its inventory; the dependency index records exact edges for its loaded roots. The semantic graph adds authored interpretation, and the claim registry selects assertions with their status and open obligations.

<figure id="fig:world" data-latex-placement="htbp">

<figcaption>A world contains the evidence and unresolved work for one question; the counts describe the whole recorded corpus, and exhaustive declaration locations do not imply exhaustive mathematical interpretation.</figcaption>
</figure>

A query can therefore start with a paper claim and return its source location or dependency neighbourhood without treating an authored summary as a proof. An interpretation record may supply context rather than a proof-level explanation; these counts do not record an individual human reading of every declaration. After locating the relevant source, a contributor can request a focused build and inspect its receipt rather than infer compilation from navigation.

<a id="sec:example"></a>

# One theorem, end to end

<span id="sec:predigestion" label="sec:predigestion"></span> For an infinite set $`A`$ of positive integers and an integer $`b\ge2`$, write $`X_A(b)=\sum_{a\in A}(b^a-1)^{-1}`$. Given a finite nonempty set $`P`$ of primes, let $`h_P(a)=\prod_{p\in P}p^{v_p(a)}`$ be the part of $`a`$ supported on those primes. The weighted-support theorem of the Problem 257 paper states that, if
``` math
\begin{equation}
\label{eq:worked-condition}
 W_{2,P}(A):=\sum_{a\in A}\frac{h_P(a)}{a(2^{h_P(a)}-1)}<\infty,
\end{equation}
```
then $`X_B(b)`$ is irrational for every integer $`b\ge2`$ and every infinite $`B\subseteq A`$ \[paper257, Theorem 1.2\]. The paper also gives a fixed-base version with $`2`$ replaced by $`b`$ in the hypothesis; the recorded Lean support for both clauses is shown in Figure <a href="#fig:theorem" data-reference-type="ref" data-reference="fig:theorem">3</a>. The arbitrary infinite-support question in base two remains open.

<figure id="fig:theorem" data-latex-placement="htbp">

<figcaption>The weighted-support statement is joined to both registered declarations; the false paraphrase at lower right illustrates a meaning error and is distinct from the historical edit 8 in Table <a href="#tab:mutations" data-reference-type="ref" data-reference="tab:mutations">1</a>.</figcaption>
</figure>

Erdős had already stated that $`\sum_{a\in A}1/a<\infty`$ suffices for this all-base irrationality conclusion \[erdos1968, p. 222\]. The corresponding formal declaration is [`irrational_erdosSupportSeries_`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean)[`of_summable_reciprocal`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean), with Comparator entry `PalomarCorpus/E257av` recorded as compared. The source paper credits Duverney and Tachiya for an arithmetic-progression averaging argument of the kind used to select a small positive displacement \[duverneytachiya, Section 2, (2.3)–(2.9)\].

To see what the weighted hypothesis adds, consider the source paper's calculation
``` math
A_\star=\{2^km:k\ge1,\ m\text{ odd},\ 1\le m\le2^{2^k}\},\qquad P=\{2\}.
```
Put $`S_r=\sum_{1\le m\le2^r,\ m\ \mathrm{odd}}1/m`$; grouping the odd integers into intervals $`[2^j,2^{j+1})`$ gives $`r/4\le S_r\le r`$ for integers $`r\ge2`$. The disjoint layer with $`v_2(a)=k`$ therefore contributes at least $`2^{-k}S_{2^k}\ge1/4`$ to the reciprocal sum, whereas its weighted contribution is at most
``` math
\frac{S_{2^k}}{2^{2^k}-1}\le\frac{2^k}{2^{2^k}-1}\le2^{1-k}.
```
Thus $`\sum_{a\in A_\star}1/a`$ diverges but $`W_{2,\{2\}}(A_\star)`$ converges; this calculation is supplied in the paper's example and has no separate Lean-ledger row \[paper257, calculation following the weighted proof\].

The proof uses the nonnegative displacement
``` math
\begin{equation}
\label{eq:worked-displacement}
 \Delta_{b,A}(N)=\sum_{a\in A}\frac{b^{N\bmod a}-1}{b^a-1}
 =(b^N-1)X_A(b)-J_{b,A}(N),\qquad N\ge1,
\end{equation}
```
where the finite sum $`J_{b,A}(N)=\sum_{a\in A,\,a\le N}\sum_{j=1}^{\lfloor N/a\rfloor}b^{N-ja}`$ is an integer. If $`X_A(b)=p/q`$ with $`q>0`$, then $`\Delta_{b,A}(N)>0`$, because $`A`$ contains an exponent larger than $`N`$, and integrality in <a href="#eq:worked-displacement" data-reference-type="eqref" data-reference="eq:worked-displacement">[eq:worked-displacement]</a> gives $`\Delta_{b,A}(N)\ge1/q`$.

We seek a multiple $`N=tQ`$ at which this displacement is smaller. A finite part of $`A`$ accounts for all but an arbitrarily small weighted tail, and taking $`Q`$ divisible by that finite part makes its displacement terms vanish. Enlarging $`Q`$ by suitable powers of the primes in $`P`$ controls the orbit averages of the other terms through $`\gcd(a,Q)`$.

The difficulty is that a finite average usually ends partway through an orbit: bounds for those incomplete periods need not sum over all exponents. The source proof takes a second average over lengths $`2^j`$, with $`M\le j<2M`$, choosing $`M`$ large relative to the polynomial size of $`Q`$ and small relative to the exponential orbit saving. Both boundary errors then tend to zero, so one term contradicts the rational lower bound; the weighted sum decreases on passing to $`B\subseteq A`$, and $`b^{h_P(a)}-1\ge2^{h_P(a)}-1`$ transfers the binary hypothesis to every $`b\ge2`$ \[paper257, Section 2\].

<a id="sec:checks"></a>

# Proof and publication checks

<span id="sec:graph" label="sec:graph"></span> <span id="systems-trust"></span> We bind a paper statement to an identified source revision and compare its complete registered support set, including named inputs, with the evidence supplied for it. A record for one supporting lemma cannot stand for a result that requires several, and a changed source or statement requires the corresponding records to be checked again. Figure <a href="#fig:checks" data-reference-type="ref" data-reference="fig:checks">4</a> distinguishes the relations checked by the kernel, Comparator and publication tools.

<figure id="fig:checks" data-latex-placement="htbp">

<figcaption>Filled circles denote machine checks and open circles denote judgements; a source binding concerns declared bytes, while the relation between a sentence and its mathematical meaning remains a separate review question.</figcaption>
</figure>

Lean verifies that a proof establishes the formal statement written in the source; it does not verify whether that statement captures the intended mathematics or whether the paper describes it well. Comparator adds a separately stated challenge and a check of its selected Lean implementation under the permitted axioms \[leanfrocomparator; nanodalib\].

For prose, we retain the exact sentence and source span together with an evidence class and an authored warrant explaining the connection. The sentence checker compares those digests and rejects missing bindings or unbound prose. An author may revise a sentence and its warrant together while keeping the hashes current, so agreement of the bytes still leaves the meaning to be reviewed. Dropping the support condition from an abstract then asserts more than the theorem proves, even though its Lean links remain intact.

An atlas entry with a matching signature and a reachable target attests to that source projection; it does not establish that any particular continuous-integration run compiled the module. The notary interface derives probe verdicts from the pinned Lean process, so a caller cannot submit its own verdict through that interface. This interface rule does not prevent an actor with filesystem access from changing the implementation or stored record. The protocol distinguishes contributor and reviewer roles but does not technically force a second independent mathematician.

Several of these proposed release practices have counterparts in the records described here \[agmai2026, Section 2.B, Step I\]: the short paper and long record explain and attribute the argument, the paper-to-Lean ledger records formal correspondence and its limits, and the challenge files and generated `formalization.yaml` expose the comparison inputs. Those records make the result inspectable; they do not certify a mathematician’s understanding. The architecture alone does not establish complete per-result model, prompt, time and cost disclosure, an account of campaign-wide selection and unsuccessful attempts, or an independent scholarly deposit. The further recommendations on funding community-led understanding and equitable model access address AI laboratories; this prototype does not demonstrate those institutional outcomes.

<a id="sec:paper"></a>

# From a Lean corpus to a paper

<span id="sec:short" label="sec:short"></span><span id="sec:long" label="sec:long"></span><span id="sec:production" label="sec:production"></span> We use the dependency graph to locate the argument and then decide which contribution deserves the short paper, taking account of its natural generality and antecedents. The author supplies the proof strategy and explains the difficult step beside the registered statement. The long record provides the complete argument and subsidiary cases, and an accepted correspondence identifies the passage supporting a particular short-paper claim. The assembler combines these authored parts and preserves their cross-references, without supplying a new mathematical argument.

<a id="source-frozen-editorial-refinement"></a>

## Source-frozen editorial refinement

We first prepare a dossier from the current corpus: candidate results, their antecedents, the difficult proof transitions and the exact questions left unresolved. The author chooses the principal argument; the dossier supplies source locations and evidence, while the native manuscript checker audits source consistency and the specified manuscript rules. For a further revision, we freeze the selected short paper and long record together with their input closure, coverage ledger and native audit rules in a packet whose manifest identifies the exact source bytes. The writer may be an advisory model returning a proposed revision, or a tool-enabled agent doing the same authoring work in a checkout; either arrangement leaves mathematical acceptance with the integrating reviewer.

We call an agent that can alter the live repository Type A and an advisory agent returning proposals against supplied sources Type B. These terms describe access to the substrate; the assignment separately chooses mathematical research, proof or claim audit, literature and attribution review, or exposition. Research returns candidate arguments, an audit returns source-located findings, a literature review returns attribution proposals, and exposition returns a clearer manuscript; each product has its own review and acceptance criteria. An exposition assignment preserves the established hypotheses, conclusions and evidence status; a suspected mathematical defect is returned for a separate audit or research assignment.

<figure id="fig:refinement" data-latex-placement="htbp">

<figcaption>The writer returns a proposal against frozen sources. Review precedes integration; rendering and inspection precede the recorded outcome and next revision. Advisory and tool-enabled writers share this acceptance boundary.</figcaption>
</figure>

The native return checker verifies packet identity, permitted edit paths, statement-change declarations and preservation of labels, citations and bibliography, then reports the manuscript audit on a temporary source overlay. It neither applies the proposal nor executes returned programs, and a declared statement change remains a mathematical review obligation. The reviewer checks changed hypotheses and implication directions against the whole statement and its registered declarations, retaining an ordinary argument with its actual evidence class when formalisation is incomplete. After that review, we restore the long record's authored parts, regenerate evidence and navigation, compile the manuscripts and inspect the resulting figures and proof links. A useful returned writing rule enters the next revision as a candidate with its example and limits; adoption requires a reviewed improvement to the owning writing contract. Figure <a href="#fig:refinement" data-reference-type="ref" data-reference="fig:refinement">5</a> describes this reproducible workflow, whose packet and audit stages are implemented by [`short_paper_writer.py`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/scripts/short_paper_writer.py); it supplies no measurement of reader benefit or autonomous discovery.

The relation to the motivating problem must also survive compression: the Problem 269 record distinguishes distinct running-LCM heights from the heights counted with multiplicity in the original question \[paper269\]. A result about the former is not automatically a result about the latter. When a statement is sharpened, merged or moved, its complete support set and any named input must move with it, and the statement relation needs renewed review. A new arrangement of a proof does not make its ingredients new.

<a id="sec:contribute"></a>

# An open route for contributions

<span id="sec:loop" label="sec:loop"></span><span id="sec:cycle" label="sec:cycle"></span> <span id="systems-public"></span> <span id="systems-job-lifecycle"></span> A contributor may send a mathematical idea or reference without a clone, or return a patch from a recorded public commit. For executable work the return identifies the changed files, commands, results, resource use and surviving limitations, with the people and tools responsible. Figure <a href="#fig:contribute" data-reference-type="ref" data-reference="fig:contribute">6</a> separates the proposed change from replay, review and adoption. We first reproduce an older branch at its original base and then reconcile it with current main, assigning separate credit to any substantive integration repair.

<figure id="fig:contribute" data-latex-placement="htbp">

<figcaption>The contribution route accepts mathematical and architectural work under their own evidence classes; the feedback arrow records an adopted change and does not certify independent review or increased discovery rate.</figcaption>
</figure>

<div id="systems-research-loop">

</div>

<div id="systems-coupled-goals">

</div>

The research journal records returns and dispositions in an append-only, hash-linked history, while a correction may withdraw something previously endorsed. Discovery investigates a question, while stewardship compares the return with prior work, groups related results, reconciles affected papers and selects the next question. The proposed coupling is event-driven: a stable result or changed appraisal prompts work, whereas an unchanged repository supplies no reason for another run. The journal establishes what happened; judging what was learned requires the comparison with earlier work.

<div id="systems-mathloop">

</div>

Generalising a local result requires a separate literature and library comparison, a proof of the proposed extension, and a second useful instance before an expert takes it to an upstream project \[mathlibcontrib\]. That route is not automated and has produced no reported Mathlib contribution in the supplied record. We distinguish credit for an idea from credit for its implementation, formalisation or exposition, using CRediT as a role vocabulary rather than an authorship decision \[credit\]. Later use adds an attributed dependency or correction, with neither a scalar impact score nor a financial contract inferred from that entry. A new world likewise needs a sourced question, explicit status, inspection routes and a review owner, which must still be assembled in several steps.

<a id="sec:instance"></a>

# Recorded observations

<span id="sec:evaluation" label="sec:evaluation"></span> The frozen inventory contains 693 paper occurrences, of which 644 have exact or specialising Lean support; 23 depend on a named input and 26 have no recorded Lean support. Of the 644 exact-or-specialising occurrences, 620 are recorded as compared and 24 as queued. These are classifications of statement occurrences, with the named-input and unsupported entries exposed separately from the fully covered entries.

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
| edit 8 | “does not supply'' changed to “completes'' | None | escaped |
| edit 9 | Open-problem title mangled | Paper anchoring | rejected |
| edit 10 | Orientation byte budget exceeded | Byte budget | rejected |

The ten historical edits and their recorded first detectors; “proof-trust policy” refers to this repository’s permitted proof mechanisms, not to a general unsoundness claim about `native_decide`.

</div>

After the escape, the follow-up checked the intact baseline and that particular edit against an added check, leaving the other edits untested under the repair and supplying no post-repair ten-of-ten result. The post-repair witness accepts the current README and rejects a test copy containing the false clause. The sample comes from one corpus and one author's selection of errors, with neither a manual-review control nor an ordinary continuous-integration comparator. The study locates a coverage boundary. Its nine rejections do not estimate how reliable the checker is.

One architecture return was accepted on 23 September 2026 after focused checks of the ordinary-language return route and an architecture-packaging case. The contributor and maintainer-operated reviewer were the same agent; neither the receipt nor this paper claims an independent outside clone replay. As of 14 September 2026, no completed external cold-clone use had been recorded.

For readers, the proposed comparison holds the mathematical task fixed and contrasts an ordinary repository, an information-equivalent static briefing and the navigation tools. It would record understanding, severe errors and the costs of preparation, use, review and repair, including missing returns, timeouts and disagreements. No independent writing comparison, blind grading run or cold-reader experiment is reported here, and no comparative reader result is reported. General reliability, reader understanding and mathematical transfer remain unmeasured.

<a id="sec:related"></a>

# Related work

<span id="app:credit" label="app:credit"></span> Figure <a href="#fig:credit" data-reference-type="ref" data-reference="fig:credit">7</a> locates the inherited components and the wider literature retained from the three source accounts. Prove2Me's first arXiv version appeared on 28 August 2026, before the first public version of this paper, and already described public agent contributions, task decomposition, reusable statements and credit for reuse \[prove2me\]. Its hosted verification service and this repository-based record provide different places for those activities; we claim neither priority for persistent research records nor a measured advantage over these systems. Polymath, BOINC and GIMPS supply precedents for small mathematical contributions and donated compute \[polymath; boinc; gimps\], while the Carleson blueprint shows formalisation organised into publicly claimable tasks \[carleson\].

<figure id="fig:credit" data-latex-placement="p">

<figcaption>Sources grouped by the roles for which the original accounts cite them, rather than by a performance ranking; the accompanying mathematical attribution distinguishes original results, refinements and independent rediscovery.</figcaption>
</figure>

The totient record refines Coons's non-$`k`$-regularity antecedent and distinguishes Martin's separation theorem from its own Chinese-remainder and Dirichlet argument traced to Yazdani \[paper249; coons; martin; yazdani\]. The running-LCM record retains Fan's public priority for the two-prime case despite an independently reported derivation, and credits its Hecke–Mahler antecedents separately \[paper269; fan269; loxtonvdp1977; bugeaudlaurent2023\]. For Problem 1041, the public degree-seven construction is ani's; the recorded Lean result refutes the exact Formal Conjectures statement, while correspondence with the 1958 curve-length wording remains unreviewed \[aniforum; formalconjectures; fcpr; ehp1958; erdos1041\]. Appendix <a href="#app:repro" data-reference-type="ref" data-reference="app:repro">10</a> names its four recorded Lean declarations; Comparator is pending. The other seven targets remain unresolved here.

<a id="sec:limits"></a>

# Limits

<span id="sec:conclusion" label="sec:conclusion"></span> This paper reports no new Lean or Comparator execution, comparative formalisation result or autonomous-optimisation experiment. Transfer to unseen mathematics and understanding by independent human readers are unresolved. The record supplies no controlled evidence that the contribution machinery improves the conversion from compute to mathematics or increases discovery rate. It also supplies no evidence that a new project can adopt the architecture cheaply or that an agent using it outperforms one using a good README. Full environment scans and initial builds still have costs, and an open corpus cannot establish that a model has never encountered its material.

The project remains maintainer-centred, with scarce review capacity and contestable credit; openness alone does not equalise resources or resolve conflicts and appeals. Broad mathematical acceptance is exogenous to this repository and cannot be granted by its maintainer. Returned code is untrusted, and expensive or privileged continuous-integration jobs must not execute fork code with repository secrets \[githubsecurity\]. A volunteer-compute service and extensions to physical science remain proposals requiring their own validation, resource and safety governance. The present contribution is an inspectable route through the records: a reader can recover the hypothesis, argument and support of a stated result, and identify where a source check ends and mathematical review begins.

<a id="app:repro"></a>

# Inspection and reproduction

This revision builds on the frozen manuscript and evidence packet recorded at `ced96e58b337`, a local integration commit rather than public main. Source links in this revision point to `7308896010e6b527d283dfdd0687a717a6183fb6`; the Comparator links below identify their separate recorded runs. The two companion manuscripts remain unchanged provenance inputs for this consolidation.

The weighted row in [`docs/paper_lean_coverage.json`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/docs/paper_lean_coverage.json) names `divisibilityWeightedClaim` and `finitePrimeWeighted_fixedBase_hereditary`, in namespace `ErdosProblems.Erdos257.PaperCompleteR8`. Its Comparator records are [run 35544127144](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35544127144) and [run 35624228171](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35624228171); the latter also records `PalomarCorpus/E257av` for the reciprocal antecedent. Both runs are recorded as compared; Palomar is prepared and not submitted.

The four declarations supporting the reported 1041 refutation have namespace `Erdos1041.Counterexample`: [`erdos1041_counterexample`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/lean/ErdosProblems/Erdos1041/Counterexample/Assembly.lean), and the [`HausdorffLength.lean`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean) declarations `erdos1041_counterexample_hausdorff`, `erdos1041_hausdorff_negation` and `erdos1041_hausdorff_answer_false`. The coverage row gives exact-or-stronger Lean support, with Comparator pending.

In a complete checkout, `python3 scripts/systems_paper_evidence.py` checks this paper's source bindings, and `python3 scripts/build_systems_paper_counts.py` checks the generated inventory. The record at [`docs/publication_evidence.json`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/docs/publication_evidence.json) holds the historical matrix and the limited follow-up, while [`docs/publication_contract.json`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/docs/publication_contract.json) declares the publication checks. Formal entry points include [`Erdos249257.lean`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/lean/Erdos249257.lean) and [`.github/workflows/lean.yml`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/.github/workflows/lean.yml); the curated assertions are in [`docs/claims.json`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/docs/claims.json), and [`scripts/check_release.py`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/scripts/check_release.py) runs the release gate. The frozen packet omits the Lean checkout and several full-repository inputs, so source-binding validation here is not a replay of those broader checks.

The protected snapshot partitions 693 occurrences into 502 exact, 142 specialising, 23 named-input and 26 unsupported-by-Lean entries. The journal summary at head `d3ad85269386` records 7 rounds (2 sealed), 25 returns (18 admitted and 7 unreviewed); earlier private-history rounds are not a complete public journal. The semantic counts in Figure <a href="#fig:world" data-reference-type="ref" data-reference="fig:world">2</a> are the supplied interpretation inventory, not a count of individually reviewed proofs. Public reading begins with [`the reading guide`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/docs/READING_GUIDE.md); [`CONTRIBUTING.md`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/CONTRIBUTING.md) describes contribution channels under the existing [`credit policy`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/docs/research-commons/CREDIT_POLICY.md).

<div class="thebibliography">

999 T. F. Bloom, *Erdős problems*, [erdosproblems.com](https://www.erdosproblems.com), accessed September 2026.

W. Cook, *Weighted Support Criteria for Reciprocal Mersenne Subseries*, short paper on Erdős Problem 257, September 2026, [`PDF`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/paper/257/erdos-257-mersenne-support-subseries.pdf).

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

W. Cook, *Bases and Integral Relations for the $`k`$-Kernel of Euler’s Totient*, short paper on Erdős Problem 249, revised 18 September 2026, [`PDF`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/paper/249/erdos-249-binary-totient-series.pdf).

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

W. Cook, *The Three-Prime Running LCM*, short paper on Erdős Problem 269, September 2026, [`PDF`](https://github.com/wcook04/plectis-erdos/blob/7308896010e6b527d283dfdd0687a717a6183fb6/paper/269/erdos-269-three-prime-running-lcm.pdf).

S. Fan, comment on Erdős Problem \#269, erdosproblems.com forum, 26 June 2026, [forum post](https://www.erdosproblems.com/forum/thread/269#post-7218).

N. Patel, A. Rammal, A. Hayat, R. Munos, and J. Kempe, *Learning to Discover Interesting Mathematics*, arXiv:2609.28603v1, 2026, <https://arxiv.org/abs/2609.28603>.

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

N. Patel, A. Rammal, A. Hayat, R. Munos and J. Kempe. *Learning to Discover Interesting Mathematics*. [arXiv:2609.28603v1](https://arxiv.org/abs/2609.28603v1), 2026, Interestingness-Driven Mathematical Discovery.

C. E. Brown, C. Kaliszyk and J. Urban. *Agent Hunt: Bounty Based Collaborative Autoformalization With LLM Agents*. [arXiv:2603.06737v1](https://arxiv.org/abs/2603.06737v1), 2026.

M. Kripner and M. Straka. *OpenProver: Agentic and Interactive Theorem Proving with Lean 4*. [arXiv:2607.09217v1](https://arxiv.org/abs/2607.09217v1), 2026, State and Memory Management.

D. Ma et al. *OProver: A Unified Framework for Agentic Formal Theorem Proving*. [arXiv:2605.17283v1](https://arxiv.org/abs/2605.17283v1), 2026, Introduction.

Z. Yang et al. *CircuitProver: Agentic Lean 4 Theorem Proving with Reusable Circuit Proof Library for Hardware Verification*. [arXiv:2607.27259v1](https://arxiv.org/abs/2607.27259v1), 2026.

H. Wijk et al. *RE-Bench: Evaluating frontier AI R&D capabilities of language model agents against human experts*. [arXiv:2411.15114v1](https://arxiv.org/abs/2411.15114v1), 2024; official abstract used here.

P. R. Halmos. *How to Write Mathematics*. L’Enseignement Mathématique 16 (1970), 123–152; sections on organising a mathematical presentation.

Various authors. *Writings on AI and Mathematics*. Supplied anthology, `AI_ESSAYS_SOURCE.pdf`, snapshot 22 September 2026; Kra, pp. 31–33; Riehl, pp. 39–40; Cohn, pp. 41–44; Gowers, pp. 55–60; Sanderson, pp. 73–77.

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
