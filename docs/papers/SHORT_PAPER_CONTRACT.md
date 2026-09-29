# Short-paper contract: supported mathematics that a reader can use

Status: p3 candidate, source pin `5acddfb2d9b43ad1b876f25700c49b1c39beddde`. The executable implementation is `scripts/short_paper_writer.py`. This contract separates a publication standard from the smaller set of checks currently executable.

## The objective

A short paper should let its intended reader state the useful result, see why it is true, identify the difficult step, understand its relationship to the named problem, and find a trustworthy proof. The preferred generality is the one that reveals and reuses the mechanism. Neither maximal abstraction, a larger theorem count, a shorter abstract, nor a successful lint run is the objective.

The lead is selected by an authoring/review session from existing supported mathematics. State that theorem with its hypotheses, after only the definitions needed to understand it. Explain the mechanism in one sentence and the genuinely difficult step in a separate paragraph. Use the original problem as an instance only when it is an instance. Otherwise name the actual relationship: a conditional route, a distinct related target, or a counterexample. A paper may contain an important general result while the original problem remains open.

This last distinction matters concretely for #269. The existing general theorem concerns distinct running-LCM heights. The catalogue series repeats a height for every smooth integer attaining it. The existing paper already leads with the general theorem; this return reorganizes its exposition and preserves that separation. It discovers no new general theorem.

## Publication requirements

**Statement and reach.** The theorem must be self-contained relative to definitions already supplied. Quantifiers, parameter ranges, endpoint conditions and unresolved hypotheses remain visible. Do not silently weaken assumptions in an abstract. Record what the general result buys beyond its named example. Explain restrictive assumptions rather than hiding them in notation. A theorem that requires an unproved input remains a conditional theorem.

**Explanation and proof.** The mechanism explains the mathematical reason the result works, rather than describing the software that found it. The hard-step paragraph names the actual obstruction and how the proof overcomes it. Give a small illustration or a transfer question that tests the reader's understanding. Definitions should answer a stated need. A correct proof and a motivated explanation serve different purposes; both require review. The present renderer outputs an opening and proof skeleton, not a completed standalone proof.

**Evidence and credit.** Each displayed result retains its native coverage identity. Keep whole-statement Lean support, support modulo a named input, a selected Comparator comparison, ordinary proof, finite computation, and a cited result distinct. A compiled special case gives no formal status to the general theorem. Record who reviewed an ordinary proof and whether the review is merely reported by a source. Preserve prior attribution and bibliography. An AI check is not human peer review. Novelty requires a separate literature comparison; the writer does not infer it.

**Boundaries and recovery.** State precisely what remains open. A failure of one construction is local to that construction. Give an exact path to the long record, together with its relevant section/label. Keep proof support, formal declarations and ordinary argument attribution recoverable from the source map. Do not remove a lemma from the long record merely because it disappears from the short opening.

**Register.** Use mathematical prose, established notation, explicit connective sentences and modest claims. Avoid one-use names, result inventories in the abstract, em dashes in authored house prose, and promotional contrastive constructions. Official names and bibliographic titles require faithful quotation; a style hit on such a name is an exception to adjudicate, not a reason to alter the source's name.

## What is executable now

| Rule | Test | Boundary |
|---|---|---|
| SP01 | Resolve literal local input/include paths; refuse missing paths, cycles and symlinks. | This is not TeX expansion or a full package dependency scanner. |
| SP02 | Native assertion inventory has stable unique labels. | Plain prose claims are not all inventoried. |
| SP03 | Literal local references have labels. | Macro-generated and external references need other checks. |
| SP04 | Literal citation keys occur in local bibliography data. | Existence does not prove the source supports the assertion. |
| SP05 | Detect em dashes in literal authored prose. | Official titles may require source-bound exceptions. |
| SP06 | Locate possible not-X-but-Y constructions. | Review flag only; valid mathematical distinctions must survive. |
| SP07 | Reuse the native body hash and paper-to-Lean coverage row. | No Lean or Comparator replay is performed. |
| SP08 | Check the presence of recorded support marks and adjacent named-input remarks; flag unmarked ordinary assertions. | The native evidence producer owns URL/receipt integrity; a visible mark is not proof. |
| SP09 | Check complete draft-role maps, exact source spans and their hashes. | A matching span is not a proof of paraphrase entailment. Legacy prose is unassessed. |
| SP10 | Re-render a draft and compare all bytes and mapping fields. | Authoring changes belong in the dossier; a free-edited final paper needs a new reviewed representation. |
| SP11 | Compare lead statement, evidence class, native coverage binding and required status phrase. | Automated statement transport is limited to the native presentation normal form. |
| SP12 | Balance literal environment boundaries. | This is not a LaTeX compiler. |

The source inventory and statement normalization come from `check_lean_paper_propagation.py` and `migrate_statement_presentation.py`. The paper set comes from `docs/papers/corpus.json`; proof status comes from `docs/paper_lean_coverage.json` and the existing evidence sidecars. No second proof registry is created. New regression tests join `check_ci_release.py` in normal and optimized Python.

The theorem renderer currently accepts a lead with existing whole-statement formal support or a native-recorded ordinary proof. It refuses to promote `computed` or `cited` evidence into a proved lead theorem. Other dossier results remain available upstream but are not automatically selected. Supporting computed/cited content needs a separately typed renderer in a future amendment.

## Versioned authoring interface

The shared `dossier/1` remains the base. The candidate `extensions.short_paper_v1` adds authored title, audience, lead choice, definitions, abstract statement, motivation, mechanism, hard step, proof outline, target relationship, boundary, attribution bibliography, and long-record route. Each semantic role has a nonempty array of `{path,start_line,end_line,sha256}` source spans. Paths are repository-relative. SHA-256 covers the exact UTF-8 bytes of the complete selected lines, including their original newlines.

The lead has an explicit hypotheses field, `statement_includes_hypotheses: authored_checked`, an ordinary-review identity where applicable, the required status phrase, and a native coverage-row ID/body digest. The lead statement is compared with the current native assertion after the native presentation-only normalization; changing a mathematical hypothesis does not pass by updating the dossier's hash.

The proposed `claim_evidence/1` transport envelope is `{schema, rows}`. `claim_locator` is the literal native result label, and `statement_hash` is SHA-256 over the exact dossier statement string. It is deliberately distinct from the native assertion digest, which includes the native assertion body representation. Both are retained. Formal declaration names must occur in the chosen native coverage row. Ordinary proof routes must resolve to exact source spans. Comparator receipts are not replayed by this stage.

`short-paper-draft/1` is a derived sidecar, not a new mathematical authority. It records each rendered role, its line interval, source spans, draft hash, canonical dossier/evidence hashes, lead identity, target-relation class and bibliography-source digest. All authorship and semantic selection remains visible. `build_short_paper_demo.py` is an explicitly authored #269 fixture, not a pretend p1/p2 return or a general extraction engine.

## Admission and the known semantic gap

Machine failure blocks the affected draft. A machine pass permits semantic review; it does not produce a publication pass. Before publication, a reviewer must check every mathematical paraphrase against its source, resolve evidence/attribution questions, review the full proof or identify its actual reviewer, and run the cold-reader test. Preserve individual failures rather than averaging a false theorem or false solution claim into a high score.

The test `test_semantic_canary_is_not_misrepresented_as_verified` deliberately replaces the relation paragraph with the false claim that the distinct-height theorem settles the repeated-value problem. It passes structural rendering and is still explicitly marked as semantically unverified. That surviving mutant is a limitation of this implementation, not evidence of understanding. The separate Type B reader/grader packets test the failure mode.

The renderer uses a restricted TeX fragment convention. It rejects several source-I/O and macro-definition operations, but it is not a TeX security sandbox. Compile trusted, reviewed input only, without shell escape. Full release, arbitrary macro semantics, all prose entailment, autonomous theorem selection and readership gains are outside the demonstrated capability.
