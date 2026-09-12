---
name: propagate-research-consequences
description: Audit whether result summaries represent the strongest supported mathematics in a public clone, or propagate a stable result through its downstream consumers while preserving exact evidence and open boundaries.
---

# Propagate research consequences

Use this skill to audit existing result summaries, or after a theorem,
counterexample, no-go, corrected statement, computation, exposition change,
or architecture repair has produced a stable local delta. It connects
appraisal and validation to propagation and return. It does not make the
result stronger; it finds descriptions and consumers that need correction.

## Audit existing result summaries

Use this mode when asked for the best results, the actual nontrivial progress,
or a check that summaries have not buried stronger mathematics. No new theorem
is required to start. Follow the
[cold-clone result audit](references/result-summary-audit.md): establish the
public revision, reconstruct candidates for every requested problem, compare
their logical reach and evidence, then repair and propagate the selection.

An overview's ranking and the current prose are candidates for review. They
are not the answer to the review. The output is a source-pinned selection with
reasons, incomparable alternatives, the exact remaining burden, and a
disposition for every affected consumer. The audit uses only this checkout;
private results cannot fill a gap in its public evidence.

## Continuous stewardship mode

This skill may own the appraisal half of a coupled continuous-goal system. It
re-enters on a stable mathematical or authority delta, not on a timer and not
because another agent is still busy. A theorem, counterexample, no-go,
source-status change, paper correction, Comparator result, Palomar outcome, or
external review can be a wake event. An unchanged corpus is a reason to yield,
not to emit another status report.

Before choosing one visible result, reconstruct the relevant candidate
universe from source authority. Include stronger results absent from the
current paper, Comparator roster, or navigation. Group declarations into
coherent mathematical families; do not count wrappers, equivalent
reformulations, or routine corollaries as independent discoveries merely
because they have different names.

Make four decisions separately:

- **authority**: what Lean, computation, paper argument, citation, or review
  actually establishes;
- **mathematical appraisal**: logical reach, mechanism depth, independence,
  sharpness, reuse, and surviving boundary;
- **exposition placement**: what leads, what receives detailed explanation,
  and what remains subordinate or discoverable only in the corpus; and
- **work allocation**: the next missing implication, falsifier, source check,
  formal interface, or discriminating computation worth funding.

No scalar, theorem count, file order, recency signal, or validation convenience
may decide all four. The stewardship pass is a second semantic check, not a
second proof authority. It may detect a trivial restatement, duplicate family,
stale paper, weak Comparator interface, missing attribution, or overclaim; it
may not convert significance or agreement into proof.

## Fix the change boundary

Record the starting commit, current commit, changed object, evidence class,
strongest supported conclusion, and surviving limitation. Begin with the
original branch rather than the current upstream branch. Include uncommitted
work instead of silently treating `HEAD` as the whole delta:

```sh
git status --short
git diff --name-status
git diff --cached --name-status
git diff --name-status <starting-commit>..HEAD
git log --oneline <starting-commit>..HEAD
```

For Lean changes, obtain the mechanical changed cone and exact neighbourhood:

```sh
python3 scripts/lean_fast_build.py --plan --verbose-plan --changed-from <starting-commit>
python3 scripts/query_corpus.py --connections <module-or-declaration>
python3 scripts/query_corpus.py --proof-cone <declaration>
```

Use `--claim`, `--paper-source`, and `--artifact` when the changed object is a
claim, manuscript source, or generated artifact. Search exact identifiers only
after these routes have named candidates. An empty text search does not prove
that there is no consequence.

## Classify every plausible consumer

Give each candidate one explicit disposition:

- **update now**: its statement, evidence, route, or projection changed;
- **verify unchanged**: it was inspected and its meaning is still correct;
- **defer**: record the reason, owner, and exact re-entry condition; or
- **outside scope**: explain why the apparent connection is not a consequence.

A dependency or lexical reference is only a candidate. It is not, by itself, a
semantic consequence. Never bulk-strengthen a family of claims because one
declaration became stronger.

## Inspect both propagation lanes

For a mathematical delta, inspect the affected Lean consumers and imports,
problem frontier and open obligations, computations and recorded no-gos,
claims and methodology, papers, Comparator or Palomar packets, query routes,
and generated public projections. Preserve authority and logical reach as
separate facts.

When the delta changes mathematical appraisal, update reader order and future
work deliberately. The strongest truthful result or mechanism should receive
the most prominent paper treatment; a worked example may remain prominent for
expository reasons only when that reason is stated. Return a ranked frontier
to `mine-open-problem`: the source-pinned strongest result, the exact open
boundary, missing evidence or consumer, and the cheapest next test that could
change the ranking. Do not return merely a list of touched files.

For an architecture delta, inspect the compact agent entry, contributor docs,
skills, builders, tests, generated routes, and any public paper that describes
the changed behaviour. A local workflow lesson becomes a general skill or rule
only when its scope and over-generalisation guard are explicit.

## Paper corrections and generated consequences

A manuscript correction is a propagation trigger even without a Lean diff.
Use the companion and consumer checklist in
[public-mathematical-writing](../public-mathematical-writing/SKILL.md#propagate-each-settled-correction).
Evidence labels must remain consistent in later tables and catalogue entries,
not only in the revised theorem. Preserve an ordinary proof as ordinary proof;
do not promote or withdraw a theorem merely to make the labels uniform.

Edit authored fragments before assembling a long paper, and rebuild the PDF
before restamping its publication record. Refresh downstream coordinates and
fingerprints after the source and full-text export are final. Use
`python3 scripts/refresh_projections.py` for the registered projection chain,
then inspect the affected query response. If a required export owner is absent
from the clone, record that exact unfinished consumer for the maintainer;
neither hand-edit its generated output nor report the package fully current.

In a shared checkout, isolate all transitive build inputs, including papers,
registries and attribution data as well as Lean. An unchanged generator can
still consume another task's uncommitted source. Generate from the committed
base plus the exact owned changes, copy back only owned outputs, and run
`python3 scripts/check_release_ref.py` on the resulting commit. Choose a
receipt path whose parent directory is canonical and contains no symlink.
Preserve unrelated work and reuse exact existing proof receipts when the
formal sources are unchanged.

At closeout, carry any reusable failure mode into the owning public workflow
and its discovery route. A lesson in a private chat cannot guide the next
contributor's agent. Record the public locator and check, or explain why the
existing rule already covers the case.

## Reconcile work from an older clone

An old clone is not an invalid contribution. Its starting commit is the common
ancestor that explains the original delta. Perform consequence propagation
twice:

1. inspect the contributor's change relative to its recorded starting commit;
2. after a maintainer merges, rebases, or transplants the reviewed change onto
   current main, inspect the resulting integration delta again.

Preserve the original delta and the reconciliation delta as separate evidence.
A conflict resolution is new integration work, not a silent rewrite of the
earlier contribution. Credit the original contributor and the integrator for
the work each supplied. Rerun current validation after reconciliation.

## Close with a propagation receipt

Return the changed object and starting commit; the mechanical candidates; each
semantic disposition; updated paths; checks run; deferred consequences and
re-entry conditions; the unchanged claim ceiling; and the next owner. Then use
`skills/erdos-research-return/SKILL.md` to package the result or
`skills/submit-pull-request/SKILL.md` to prepare a proposed upstream return.
