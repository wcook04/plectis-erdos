---
name: propagate-research-consequences
description: Trace the mathematical and repository consequences of one accepted or candidate result, record a disposition for every plausible downstream consumer, and rerun the trace when older-clone work is reconciled with current main.
---

# Propagate research consequences

Use this skill after a theorem, counterexample, no-go, corrected statement,
computation, exposition change, or architecture repair has produced a stable
local delta. It is the bridge between validation and return. It does not make
the result stronger; it finds the places whose recorded meaning may now be
stale.

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

When moving the pinned formal-source revision, use
`python3 scripts/semantic_review.py --rereview-moved-revision` to inspect receipt
migration before adding `--apply`. This route carries a review forward only
when its wording and evidence identity are unchanged and every cited
declaration's kind and full signature match across revisions. A source-line
move alone is not new mathematics. Refused substantive changes need a fresh
source-bound interpretation, not a hand-edited digest or a human-author gate.

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

## Keep Comparator coverage attached to claims

When a change adds or strengthens a registered claim, inspect its exact
Comparator interface as part of the same propagation pass. The coverage unit
is `docs/claims.json::claims`, not every helper declaration and not a frozen
number of result families. An open problem or cited result needs an explicit
non-executable disposition, not a fabricated proof interface.

Use the existing per-entry Challenge/Solution packages. Record the exact
claim-to-interface edge through `main_results[].claim_id` or the claim owner's
`comparator_transports[]`, with registered source declaration anchors. An
interface with a similar name is a candidate for inspection, not a confirmed
link. Check that its hypotheses and conclusion faithfully express the intended
claim; LLM source-bound interpretation is a valid authoring attempt and remains
contestable. Do not require a human mathematician to author the interface.

After source validation, run the normal projection refresh. It regenerates the
Comparator portfolio before the external-verification views. Inspect
`verification/comparator-replay-membership.json::registered_claim_coverage`;
the optional read-only gate is:

```sh
python3 scripts/build_comparator_replay_portfolio.py --require-complete-claims
```

Complete transport accounting is not complete informal-statement review and
does not establish that Comparator executed. Keep transport coverage, exact
commit-bound execution receipts, and Palomar submission/review outcomes
separate in every downstream query and presentation. Preserve explicit missing
transports until they are actually supplied and validated.

## Propagate atoms and paper placement from their owners

Keep registered claims, editorial result atoms, and result families as separate
populations. Use `scripts/result_atoms.py --candidate-jsonl <batch.jsonl>` to
validate a proposed atom batch before adding `--write`. Preserve attributed
source statements, interpretation boundaries, and stable identities. Display
bands come from `docs/PALOMAR_RESULT_SHOWCASE.json::family_display_order`;
short/long placement comes from `paper/paper-result-integration-source.json`.
Neither owner is a proof or execution receipt.

The normal refresh derives the complete family catalogues and assembles the
reasoning manuscripts before exporting their public text. Consult
`scripts/assemble_reasoning_surfaces.py::PAPERS` to find each manuscript's
authoring owner: a note-derived record reads its body and bibliography directly
from the short note, while an independent record reads its authored parts.
Do not recreate duplicate body files to repair a derived paper. Refresh the
pinned source coordinates, assemble, rebuild affected PDFs, inspect their
rendering, and rebind reviewed publication digests before exporting.

When adding a manuscript, register it in `docs/papers/paper_registry.json`;
Make derives native targets from that owner. Complete the existing publication
contract and licence coverage, then run the ordinary refresh/release route.
Inspect `--result-atom <atom_id>` and `--family-atoms <family_id>` after a
population change: the latter must show strongest-first editorial ordering,
bounded omissions, and a visible distinction between family interface metadata
and registered-claim transport coverage.

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
