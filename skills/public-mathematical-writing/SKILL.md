---
name: public-mathematical-writing
description: Write or revise reader-facing mathematics in this public Lean repository without outrunning checked source, claim status, or the exact open boundary.
---

# Public mathematical writing

Use this skill for `docs/READING_GUIDE.md`, the reader-facing parts of `README.md`,
result and scope guides, paper full text, and manuscript prose. It travels with
the public clone and depends only on files in this repository.

Do not apply it to command references, generated JSON, schemas, or agent-only
workbench instructions. Those files should stay exact and operational. The
point is to give readers a real account of the mathematics before asking them
to understand the repository machinery.

## Enter from the public evidence

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

## Begin from the claim, not the draft

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

An ordinary proof can establish a theorem before its full formalization exists.
Check that argument on its own terms, including limiting steps, endpoints and
the order of quantifiers; identify the formalized ingredients separately.
Neither an absent Lean declaration nor an unsupported kernel label settles
the validity of the ordinary argument.

## Write for the reader in front of you

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

## Prose pass

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

## Final check

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

## Propagate each settled correction

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

When the repair teaches a reusable lesson, update the smallest public skill,
rule or regression check that can prevent recurrence. Keep the rule usable
from this clone, state its limits, and verify that the cold-agent route exposes
it. If the existing rule already covers the case, record that fact and its
locator instead of adding another copy.

Record the changed result, consumer dispositions, exact source version,
validation and review coverage in the existing review or contribution record.
Distinguish fully inspected proofs from sampled or unavailable material. Counts
of papers, declarations or passing checks are not mathematical review coverage.

## Validation and boundaries

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
checks; do not regenerate authored prose mechanically.
