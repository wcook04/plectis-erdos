---
name: public-mathematical-writing
description: Write or revise reader-facing mathematics in this public Lean repository without outrunning checked source, claim status, or the exact open boundary.
---

# Public mathematical writing

Use this skill for README, Markdown, manuscript, theorem commentary, and other
reader-facing mathematical prose in this repository.

## Entry

Start from the public checkout only:

```sh
python3 scripts/proof_cockpit.py --format card
python3 scripts/query_corpus.py --ask "<the mathematical question>"
```

Then follow the exact claim, remaining-open proposition, declaration, problem,
or paper handle returned by the public corpus. No private checkout, memory,
prompt packet, provider trace, or `ai_workflow` path is an input to public prose.

## Authority order

1. Lean source checked by the pinned Lean kernel is proof authority.
2. `docs/claims.json` owns reviewed public claim identity and status.
3. `docs/methodology.json` owns evidence responsibilities for claim changes.
4. Generated indices and cockpit cards are navigation projections.
5. Papers and Markdown are authored exposition within those ceilings.

Never turn a theorem count, module count, finite computation, conditional
reduction, navigation result, workbench note, or model suggestion into a
stronger mathematical claim.

## Writing loop

1. Resolve the exact public claim or problem handle.
2. Read the cited Lean declaration and its registered status or explicit lack
   of reviewed status.
3. State what is checked in ordinary mathematical language.
4. State the surviving hypothesis, bounded range, or exact open proposition in
   the same local context.
5. Preserve attribution and distinguish formalisation from novelty,
   significance, priority, and peer review.
6. Change source authorities before generated projections. Never hand-edit a
   generated orientation, index, full-text mirror, or coordinate projection.
7. Run the smallest relevant prose/source check, then the public release gate
   when a claim-facing surface changed.

## Boundaries

- No private workflow mechanics or unpublished mathematical state may appear.
- No paper edit proves a claim; no registry edit proves a theorem.
- No `sorry`, `admit`, project-defined `axiom`, `native_decide`, unsafe or
  partial declaration, or unbounded kernel limit is permitted.
- All eight indexed Erdős problems remain open unless the Lean source, claim
  registry, authored review, and release process are explicitly changed
  together.

## Validation

```sh
python3 scripts/proof_cockpit.py --check
python3 scripts/check_problem_note_sources.py --coverage
python3 scripts/check_release.py
```

Run `python3 scripts/lean_fast_build.py --jobs 2` after Lean changes. For paper
changes, rebuild the owning manuscript and run its registered link and corpus
checks; do not regenerate authored prose mechanically.
