---
name: public-mathematical-writing
description: Write or revise reader-facing mathematics in this public Lean repository without outrunning checked source, claim status, or the exact open boundary.
---

# Public mathematical writing

Use this skill for `HUMAN_ENTRY.md`, the reader-facing parts of `README.md`,
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

- a Lean-checked theorem, a cited theorem, a finite computation, a conditional
  reduction, a counterexample, and an open conjecture are different kinds of
  evidence;
- preserve every hypothesis, quantifier, implication direction, attribution,
  and stated limit;
- never turn acceptance by Lean, Comparator, Palomar, a maintainer, or a pull
  request into novelty, peer review, importance, endorsement, or a solution;
- keep the unresolved statement beside the result that stops short of it.

If the sources disagree, stop the prose edit and repair the authority surface
first. A smoother paragraph cannot settle a mathematical discrepancy.

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

## Conceptual structure and corpus selection

For a substantial paper revision, use the public frontier and comprehension
routes before choosing the headline. Start with
`python3 scripts/query_corpus.py --overview --format card`, then follow the
selected problem through `scripts/query_route_memory.py --problem <number>`
and its exact declaration and claim handles. Read the current manuscript only
as a candidate arrangement of that evidence. A ranked route is a starting
point for mathematical judgment, not a significance verdict; check for strong
results that the current reading route omits.

Group related declarations by the mathematical work they accomplish. Compare
the actual conclusions, removed hypotheses, decisive obstructions, and useful
consumers. An equivalence earns prominence when its new coordinates enable a
proof, a sharper reduction, a discriminating computation, or a concrete
obstruction. Proximity to the original question alone does not put a bare
reformulation ahead of a substantive theorem. Keep an exact equivalence
available even when it belongs in supporting material.

Mathematical elegance is conceptual. Choose definitions that expose the
mechanism, use an example that makes the next construction natural, and arrange
the lemmas so the reader understands each choice before carrying it through.
Explain what a transformation gains and where its gain stops. Spend the most
space on the hard step; abbreviate routine consequences. A catalogue of cases
should follow the shared argument when that argument explains the cases.
Typographic polish and promotional language cannot supply this structure.

Before shortening a theorem into a title, abstract, panel, or reading guide,
check which hypotheses exclude elementary counterexamples. In particular,
nonzero somewhere is not nonzero in an eventual tail, a finite prefix is not
an infinite support, and summability must name the sequence being summed.
Compare each compressed statement with the full declaration, including its
quantifiers. Explain a necessary hypothesis with a small counterexample when
that also reveals the mechanism.

After a stable revision, use `skills/propagate-research-consequences/SKILL.md`:
carry corrected meaning and useful reading order into their authored owners,
then regenerate corpus text and navigation through the owning builders. Record
reusable authoring lessons here without private paths, live counts, mandatory
model choices, or dependencies on another checkout.

## Read conditional results and failed routes mathematically

For a conditional theorem, inspect the final consumer to separate assumptions
used in the contradiction from assumptions intended to produce its input.
Write the shortest transparent argument before reproducing certificate
bookkeeping. A structure with a constructed example can still lack its crucial
selector; never describe that selector as proved because a docstring says so.
Check the declaration's actual parameters and proof. If a stronger consumer
with fewer assumptions is useful, expose and validate it in Lean as well.
Do not count that interface improvement as a new solution of the missing input.

A failed-route survey must include the relevant problem source and route
memory, not only one semantic query. An empty barrier result can mean limited
index coverage. Group failures by the exact obstruction they prove: a lost
hypothesis, a coordinate-dependent invariant, a quantitative incompatibility,
or a failure to pass from finite witnesses to an infinite construction. State
which proposed methods each obstruction excludes and which survive. A shared
word or failure label is not a common mathematical theorem. Where one change
of coordinates repairs a failure, show the before-and-after calculation;
where it does not, preserve the counterexample and the remaining obligation.

## Check the source universe before choosing the story

Treat a curated paper, claim matrix, or external-review roster as a selection,
not as an exhaustive inventory. Compare its modules with the actual problem
source tree and its current research frontier. Preserve an authored reading
order while making omitted source modules discoverable through the owning
index builder. Source presence alone grants no proof or review status.
When implementation and publication live in different source roots, inspect
both before declaring formalization missing. An unpromoted implementation may
already be stronger than the published result. Check its exact statement,
dependency versions and validation evidence before transferring it; repair the
missing publication route instead of rebuilding a weaker theorem.

For each substantial omission, read the proof and its consumers. Test whether
several existing ingredients discharge a premise that the paper still lists
as open; write out that bridge, including normalization, endpoint conventions,
convergence and quantifiers. An ordinary assembled proof may strengthen the
paper before its complete Lean formalization exists, but label the uncovered
bridge explicitly. Neither a theorem name nor a checked scalar ingredient
certifies the assembled statement.

When formalization is in scope, an uncovered bridge is work to undertake,
not merely a disclaimer to add. Reuse existing proofs and formalize the
mathematical step needed by the paper's actual conclusion. Prefer the bound
on the genuine series or the inequality for actual disk points to a wrapper
that assumes that conclusion. Keep the strongest justified ordinary result
visible while the formal proof is developed; report partial coverage precisely
and promote checked status only after the exact source passes Lean.

Propagate a verified omission into the existing mathematical family, claim
record, comprehension nodes, reviewer disposition and paper as appropriate.
Distinguish represented source mathematics from a configured or executed
external-verification target. Reuse existing nodes; fix a missing route or
consumer edge instead of duplicating the theorem. Refresh generated surfaces
only after the authored meaning is settled. Rank by the mathematical gain,
not the number of newly exposed modules or declarations. Verify the actual
query output too: a family can exist in a registry yet be absent from the
ordered overview. Keep default routes bounded by summarizing repeated prose
and preserving identities and detail handles; do not hide stronger results or
raise response limits to accommodate duplication.

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

After changing mathematical content, run the owning paper, corpus, and claim
checks before the validation floor below.

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

After a manuscript changes, rebuild its shipped PDF before restamping
`python3 scripts/check_publication_contract.py --restamp --apply`, then run
`python3 scripts/build_publication_entry_packet.py`. Moved text also changes
claim-owned paper anchor lines: refresh those with
`python3 scripts/refresh_source_coordinates.py --claims-only`. This preserves
the manuscript's reviewed source links. Refresh the generated paper corpus and
run the clean-ref release check after committing the complete artifact set;
a successful PDF build or digest restamp alone does not establish that the
publication projections agree. When new source links introduce modules, run
`python3 scripts/build_paper_module_aliases.py`; when the review matrix or
Palomar's authored family placements and programme order change,
run `python3 scripts/build_external_verification.py`. Refresh the semantic,
theory and corpus-descriptor projections after their inputs settle, with the
descriptor last so it records the final source-alias digest.
If pending Lean work shares the checkout, generate the publication projections
from an isolated snapshot of the committed sources. Uncommitted build inputs
and challenge fixtures alter reviewer hashes and hole inventories even when
the manuscript edits are independent of those proofs.

Run `python3 scripts/lean_fast_build.py --jobs 2` after Lean changes. For paper
changes, rebuild the owning manuscript and run its registered link and corpus
checks; do not regenerate authored prose mechanically.
