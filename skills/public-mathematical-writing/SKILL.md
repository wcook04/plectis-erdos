---
name: public-mathematical-writing
description: Write or revise mathematical papers using nearby literature and exact evidence, either in another repository or with the public Plectis source and claim records.
---

<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Public mathematical writing

Use this skill for mathematical manuscripts, result explanations and reader-facing
repository documentation. First identify whether the target belongs to Plectis
or another project. The general method below is self-contained; its further
reading is optional. The Plectis workflow later in this file applies only to a
Plectis checkout.

## Use in another repository

Follow the destination project's instructions and preserve unrelated work.
Use its manuscript sources, proofs, evidence records, build tools and review
process. No Plectis commands, claim schema or other installed skill is required.
If the task concerns another discipline, use that discipline's evidence and
writing conventions; this method was developed for mathematics.

- **Settle meaning before prose.** Identify the intended reader, contribution,
  exact statement and argument. Preserve domains, hypotheses, quantifiers,
  implication directions, attribution and unresolved questions. Distinguish
  an ordinary proof, formal proof, cited result, finite computation and
  conjecture. Resolve a substantive disagreement before copyediting; a more
  fluent sentence cannot settle it.
- **Read nearby primary literature.** Select papers close in subject and genre.
  Inspect complete local arguments, recording edition and passage. Study how
  authors introduce objects, place hypotheses, connect deductions and explain
  difficult steps. Use established terminology for the same object; write
  original sentences rather than imitating a named voice. A source's expository
  choice does not prove the corresponding step in your argument.
- **Explain the dependence.** Give the question, principal result, reason for
  interest and proof's main idea. Motivate a construction before using it.
  Spend detail at the difficult inference and check limiting arguments and
  parameter dependence. Use an example when it clarifies the mechanism, and
  say where it stops representing the general claim. A README should explain
  one real result or capability and offer a reliable first action before an
  exhaustive inventory.
- **Use notation and sentences purposefully.** Introduce a symbol when it
  reduces repeated explanation. Replace private names with the actual object
  or property, preserving necessary technical terms. Let sentence connections
  express real reasons and dependencies. Retain a useful authorial voice;
  remove slogans, vague actors and repetitive framing without manufacturing
  certainty, personal history or a uniform sentence rhythm.
- **Review the revision as a claim.** Compare the old and new meaning, including
  compressed statements in titles, abstracts, captions and conclusions. Check
  short and long versions in both directions. Retain the exact failed inference
  and its witness when an unsuccessful approach is informative. Do not invent
  a discovery history or promote a checked lemma into a checked whole proof.
- **Keep decisions and limits.** Record each substantive change, its reason,
  source locator and accepted, repaired, rejected or pending disposition in the
  project's existing review record, or its normal change summary if none exists.
  When a paper has an accompanying agent skill, review and update that skill
  in the same change. Carry changed instructions, examples and limits into it;
  record a reason when the instructions remain applicable without alteration.
  A proposed general lesson needs its scope and an exception; an application
  of an existing rule needs no new rule.
  Distinguish a reviewer's assessment from observed reader feedback.
- **Inspect the delivered result.** Run the project's relevant checks and
  manuscript build. Read the rendered text from a cold start; check references,
  links, formulas, captions and page layout. Report what was actually inspected
  and any unavailable check. Successful compilation does not establish reader
  understanding, mathematical novelty or independent review.

Optional reading: [the compact guide](references/writing-guide.md) and
[its worked companion](references/worked-companion.md) are bundled with this
skill. Further sources include
[Halmos](https://doi.org/10.5169/seals-43857),
[Knuth, Larrabee and Roberts](https://cs.stanford.edu/~knuth/klr.html),
[Tao](https://terrytao.wordpress.com/advice-on-writing-papers/) and
[Gowers](https://gowers.wordpress.com/2007/10/19/my-favourite-pedagogical-principle-examples-first/).
These inform writing decisions; they do not endorse this skill or verify a
new argument. The instructions above remain usable without these links.
The skill is [Apache-2.0 licensed](LICENSE); the bundled guides retain their
CC-BY-4.0 licence and attribution.

For work in another repository, finish with that project's validation and
review record. The remaining workflow is specific to Plectis.

## Work in Plectis

Use this branch for the reader-facing parts of the Plectis README, result
and scope guides, paper full text, and manuscript prose. It depends only on
tracked files in this checkout. Command references, schemas and agent-only
instructions remain exact operational documentation.

### Enter from the public evidence

```sh
python3 scripts/proof_cockpit.py --format card
python3 scripts/query_corpus.py --ask "<the mathematical question>"
```

Follow the returned claim, open proposition, declaration, problem, or paper
handle. Lean source checked by the pinned Lean kernel is proof authority;
`docs/claims.json` owns reviewed claim identity and status;
`docs/methodology.json` owns claim-change responsibilities; generated indices
route; papers and Markdown explain. No private checkout, memory, prompt packet,
provider trace, or private artifact is an input to public prose.

### Read nearby mathematical prose before a substantial rewrite

Start with [Writing a Good Mathematical Paper](../../paper/exposition/writing-a-good-mathematical-paper.pdf)
for the compact, general instructions. Use the
[long companion](../../paper/exposition/writing-mathematics-from-reviewed-revisions.pdf)
and [literature and reviewed-revision guide](../../docs/papers/exposition-method/README.md)
for worked cases, review history and a manuscript-scale or cross-paper pass. Choose a small set of human papers
close in subfield and genre, then read the relevant original arguments, with
exact version and passage locators. Inspect terminology, hypothesis and
quantifier placement, the reasons expressed by sentence connections, notation
on first use, proof pacing and local attribution. Write original prose using
those conventions; do not copy sentences or imitate a named voice.

For each proposed transfer, identify both the source's writing choice and the
local mathematical fact that licenses the new sentence. A stylistic specimen
does not prove the target argument. Keep established technical terms; replace
private compounds by the actual object, bound or property when that reduces
unnecessary decoding. Use subordinate clauses for dependencies and parallel
syntax for parallel claims, without optimizing sentence counts or detector rates.

Record the actual before/after passage, source locator, native decision and
limit in the existing review record. The public [lesson ledger](../../docs/papers/exposition-method/lessons.json)
preserves examples and corrections; its proposals are not universal commands.
Keep supplied sources, donor-declared reading and your later inspection distinct.
Adopt a new general rule only when the case warrants it; otherwise record an
application of the existing rule. A frozen next packet must include the chosen
version of this skill, both writing papers, its guidance and the primary originals it asks its reader
to study. This updates repository practice, not model weights, and claims no
measured reader benefit.

### Begin from the claim, not the draft

Before changing mathematical prose, read the exact current result from its
owning Lean declaration, the matching entry in `docs/claims.json` when one
exists, and the present paper or result guide. Keep these distinctions intact:

- a Lean-checked theorem, an ordinary authored proof, a cited theorem, a finite
  computation, a conditional reduction, a counterexample, and an open
  conjecture are different kinds of evidence;
- preserve every hypothesis, quantifier, implication direction, attribution,
  and stated limit;
- never turn acceptance by Lean, Comparator, Palomar, a maintainer, or a pull
  request into novelty, peer review, importance, endorsement, or a solution;
- keep the unresolved statement beside the result that stops short of it.

If the sources disagree, stop the prose edit and repair the authority surface
first. A smoother paragraph cannot settle a mathematical discrepancy.

A declaration present in the checkout is not, by itself, a validation receipt.
Read candidate or unrun status notes and identify the checked source version
before calling it Lean-checked. When reconciling short and long papers, do not
copy the stronger evidence label merely because one version already uses it.
Conversely, a successful audit bound to the current source bytes can supersede
an older unrun header; read that receipt before repeating the older label.
Compare the exact mathematical domains as well: a local complex-parameter
chain rule does not itself formalise an integrated real-time trajectory or its
endpoint behaviour. State separately the checked lemma and any ordinary
argument that supplies the advertised conclusion.

Logical scope and evidence are separate: a conditional implication can have
an ordinary or formally checked proof. A finite verification supports an
infinite claim only through a proved reduction that covers every case.

An ordinary proof can establish a theorem before its full formalization exists.
Check that argument on its own terms, including limiting steps, endpoints and
the order of quantifiers; identify the formalized ingredients separately.
Neither an absent Lean declaration nor an unsupported kernel label settles
the validity of the ordinary argument.

Reconcile a short paper and its long record in both directions.  If either one
states a stronger theorem, recover its full argument and compare the other
statement before deciding which version is current.  Do not leave an
unnecessary hypothesis in the long record when the short proof removes it, or
let the short paper outrun the argument that the long record is meant to
preserve.  When a weaker hypothesis gives a qualitative conclusion and a
stronger hypothesis gives a numerical rate, state the two implications
separately and name the source of the stronger estimate.

Before combining separately existential criteria, write their quantifiers in
one line and check that the same witness satisfies every premise.  Two
unbounded or cofinal witness sets can be disjoint.  Finite-union closure for
exceptional sets does not align independently chosen witnesses, and an
iterated limit cannot be exchanged until the dependence of each threshold on
the other parameters has been proved.

When translating a theorem type into prose, check its ambient domain and
codomain, positive or nonzero parameters, finite index ranges, and the order
in which witnesses are chosen. Test the smallest allowed case and one case
outside a proposed guard before dropping it. A properness claim depends on
its codomain; a fraction requires a nonzero denominator; a finite-minor result
must quantify its order and say which parameters its indices may depend on.
Keep essential guards inside the statement, even when the intended application
automatically supplies them.

### Write for the reader in front of you

A human front door should first answer four ordinary questions in prose: what
problem is being studied, what has been established, why that result is worth
reading, and what remains open. Give the reader a useful next link after that.
Do not make a command, table, field name, route id, badge, or file inventory do
the work of an explanation.

Tables are fine as later reference material when genuinely parallel facts need
scanning. Commands are fine in agent and maintainer sections. Neither belongs
before a reader has been told what the mathematical object is and why the
page exists.

For a paper or theorem explanation:

1. State the strongest accurate result early and name its evidence class.
2. Explain the question and the obstruction before listing declarations or
   files.
3. Give the proof spine, then spend the most space on the step that does real
   mathematical work.
4. Introduce notation only when it lowers the total reading cost. Use one name
   for the same object across prose, Lean, figures, and indexes.
5. Put a simple nontrivial example before an abstraction when it reveals the
   mechanism, and say where the example stops representing the theorem.
6. Distinguish original proof, cited result, correction, computation, and
   exposition in citation wording.
7. End the result where the evidence ends. State the next open implication
   plainly instead of closing with promotional language.

For a substantial revision, rank the available results and reader blockers
before allocating space. Give a difficult proof transition or a useful
counterexample more attention than routine algebra or another equivalent
formulation. The short paper should sustain its principal argument; the long
record should explain the additional mechanisms and retain technical material
in a navigable order. Do not make both versions equal-weight inventories.

### Short paper, long record, and synthesis

Use this same skill for all three. A short paper sustains one principal argument:
question, motivating example, strongest accurate result, key proof idea, hard
step and precise remainder. The long record makes the proof inspectable and
keeps technical details, worthwhile failed routes and reproduction information
in a navigable order. It is not a chronological transcript. Check the statements
and evidence classes in both directions before refreshing their projections.

The synthesis pair can develop an insight arising anywhere in the corpus:
a transfer, construction, obstruction, better intermediate object or new
question. It need not solve an original problem. Put a result that changes one
problem's answer in that problem's paper too. Keep an elementary tool as a
subordinate explanation; do not turn it into a new theory through naming or
inflate an engineering improvement into a mathematical discovery.

Apply this compact review adapted from [Tao's writing advice](https://terrytao.wordpress.com/advice-on-writing-papers/)
and [Gowers's examples-first principle](https://gowers.wordpress.com/2007/10/19/my-favourite-pedagogical-principle-examples-first/):

- Describe the result accurately, motivate it, and explain its relation to prior work.
- Introduce a concrete example before an unfamiliar abstraction when that example
  gives the reader a useful mental model. Identify where the analogy stops.
- Supply the proof's map and explain the hard transition; choose detail and notation
  for this reader. Delete notation that does no repeated work.
- Motivate a decisive construction by the difficulty it fixes. A tempting failed
  approach can help, provided its failure is shown. Label a reconstructed route
  as an explanation; do not invent the history of how the result was found.
- Read from a cold start, resolve unexplained jumps, proofread, and compile the final
  document. Preserve an effective authorial voice instead of enforcing a formula.

These are practical adaptations, not endorsements or a claim that a passing
check establishes good mathematical writing. Credit supplied examples, directions,
proof ideas and corrections at their actual points of use.

The motivation test also draws on Grant Sanderson's
[essay on explanations](https://terrytao.wordpress.com/2026/09/18/if-math-is-more-than-proof-we-need-to-better-celebrate-the-rest-of-it/).
An expository contribution can clarify a known theorem. Judge it for its named
audience; distinguish actual reader feedback from an agent's assessment of
the prose. Fluency alone does not establish understanding.

### Prose pass

Use direct, understated English. Name the mathematician, contributor, program,
or formal declaration that performs an action when the actor matters. Cut
generic throat-clearing, staged revelations, slogans, repeated three-part
lists, inflated significance claims, and conclusions that merely repeat the
opening. Keep standard mathematical terminology and define repository jargon
that a new reader cannot infer.

Vary sentence length naturally. Preserve a useful irregular sentence rather
than polishing every paragraph into the same cadence. Do not invent warmth,
certainty, history, motivation, examples, sources, or a personal voice that
the source does not contain.

### Final check

Compare every changed mathematical sentence with its declaration, claim row,
computation, or cited source. Check the rendered Markdown links and compile a
changed manuscript when its toolchain is available. Then read the page from a
cold start: can a reader identify the question, principal result, reason for
interest, evidence class, hard step, and exact open boundary without learning
an internal command vocabulary first?

Audit the publication boundary from that same cold start. Every reader-facing
link must resolve from a fresh public clone or from a public browser session
without private credentials. Do not print local filesystem paths,
private-repository paths, or internal-only artifact locators. Replace them with
a stable public page or download. When an unpublished artifact is necessary
evidence, publish it through the repository's release process before linking
it; otherwise remove the dependency and state the evidence boundary plainly.

When shortening shared entry guides, keep contract-required provenance and
authority wording intact. Measure the whole first-read bundle, then run
`scripts/test_cold_clone_comprehension.py` and
`scripts/test_public_artifact_boundary.py`; a local readability check alone
does not cover those contracts.

### Keep the writing papers and this skill together

When either writing-guide paper or a local style it loads changes, review this
skill in the same change. A style can define prose as well as typography.
Update its instructions for each changed recommendation, example or limit.
For a change that leaves the instructions applicable, record why. A fresh hash
alone is not a review of meaning.

Rebuild an edited paper and its full-text copy through the publication tools.
Refresh the file hashes and edition in
`docs/papers/exposition-method/version.json`, then record `paper_skill_review`:
the current paper-input and loaded-style digests, this skill's hash, `updated` or
`verified_unchanged`, and a substantive reason. Run:

```sh
python3 scripts/sync_writing_skill.py --write
python3 scripts/sync_writing_skill.py --check
```

The synchronizer checks those bindings before copying the two guides into this
skill's `references/` directory. The normal projection and release checks reject
stale bindings or bundled text. Commit the papers, skill, review record and
generated copies together. Keep installed copies current by reinstalling the
whole skill folder; do not edit generated references directly.

Use explicit literal inputs relative to `paper/`, the full-text exporter's
working directory. The synchronizer refuses dynamic filenames, conflicting
lookup paths and inputs its export receipt does not cover. Canonicalize those
inputs and regenerate through the normal owners before copying the guides.

### Propagate each settled correction

Run [propagate-research-consequences](../propagate-research-consequences/SKILL.md)
as part of every substantive mathematical revision, even when no Lean file
changes. Do this after settling the mathematics and before closing the work.
A correction to hypotheses, a proof, evidence wording, attribution, or the
explanation of a method's limits can change other surfaces too.

Start with the exact changed statement and inspect its plausible consumers:

- the title, abstract, theorem, proof and conclusion in both short and long
  versions, including later summaries and family catalogues;
- the matching claim family, evidence record, open obligation, and any
  Comparator or Palomar entry that states the affected result;
- reader guides and public query answers that compress the result; and
- assembled sources, PDFs, full-text mirrors, source coordinates, corpus
  metadata and publication fingerprints that depend on the edited source.

Give each consumer an explicit disposition: update now, verify unchanged,
defer with an owner and re-entry condition, or outside scope with a reason.
Make semantic changes in the owning source and rebuild its projections; a
successful text replacement or export does not verify the mathematics. Check
the actual returned query or rendered passage after refreshing it.

For an ordinary paper theorem, also query its exact paper anchor. If a curated
`anchor_label_allowlist` hides the accepted result, add its existing unique
label to the owning paper row. Preserve its unregistered authored-anchor class;
discoverability does not require inventing a formal claim or Lean evidence.

When the repair teaches a reusable lesson, update the smallest public skill,
rule or regression check that can prevent recurrence. Keep the rule usable
from this clone, state its limits, and verify that the cold-agent route exposes
it. If the existing rule already covers the case, record that fact and its
locator instead of adding another copy.

Record the changed result, consumer dispositions, exact source version,
validation and review coverage in the existing review or contribution record.
Distinguish fully inspected proofs from sampled or unavailable material. Counts
of papers, declarations or passing checks are not mathematical review coverage.

### Validation and boundaries

Change source authorities before generated projections. Never hand-edit a
generated orientation, index, full-text mirror, or coordinate projection. A
paper edit proves no claim; a registry edit proves no theorem. Read the current
problem roster and open status from the corpus instead of freezing a count in
this skill.

```sh
python3 scripts/proof_cockpit.py --check
python3 scripts/test_public_writing_contract.py
python3 scripts/check_problem_note_sources.py --coverage
python3 scripts/check_release.py
```

Run `python3 scripts/lean_fast_build.py --jobs 2` after Lean changes. For paper
changes, rebuild the owning manuscript and run its registered link and corpus
checks; do not regenerate authored prose mechanically. For a native TeX edit,
build the changed PDF and run `scripts/sync_publication_pdfs.py` before
`docs/papers/refresh_paper_corpus.py --write`: the corpus records the PDF
digest as well as the manuscript text. Then restamp the source/PDF pair through
`check_publication_contract.py --restamp --apply`, reanchor any moved source
attributions, refresh projections, and run the release check. A corpus refresh
done before PDF synchronization must be repeated afterward.
