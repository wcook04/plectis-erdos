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
