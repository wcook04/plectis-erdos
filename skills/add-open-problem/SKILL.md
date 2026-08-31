---
name: add-open-problem
description: Add a sourced mathematical problem as a new public problem world without silently promoting expansion work into a reviewed claim or pretending that the repository is hard-coded to the current eight.
---

# Add an open problem

Use this skill to port a problem beyond the current eight into the public
corpus. This is a governed multi-surface change, not the creation of one Lean
file. Read `AGENTS.md`, `ARCHITECTURE.md`, `paper/README.md`, and
`docs/problem_index_source.json` before editing.

## Entry requirements

The proposed world must have:

- a canonical question and a precise citation to its source;
- a current-status statement with a dated literature check;
- a licence-compatible source or link policy;
- an exact boundary between what is externally known, formalised here,
  computed here, and still open;
- at least one readable route and one bounded contribution point;
- a named maintainer or review route.

Failure to locate a proof is not evidence of novelty or openness. Keep source
roles and uncertainty explicit.

## Choose the honest entry lane

### Proposal

Open a plain-language issue or focused pull request containing the sourced
question, current-status evidence, fit with the repository, proposed first
bounded route, and requested credit. This lane works without a Lean file or
paper.

### Incubating formal lane

Add a problem-owned module under `ErdosProblems/ErdosNNN/`, import it through
the expansion root, and give the module a docstring naming the target, checked
content, and surviving obligation. Build it with the pinned Lean toolchain.
Label it incubating: the current canonical problem index requires a registered
paper and review-matrix row, so source alone cannot yet become a fully indexed
problem world.

### Fully indexed public problem

Complete the coordinated migration below. At present this requires maintainer
fan-in because `docs/papers/corpus.json` is generated outside this public
clone, structured research returns enumerate the current roster, and the
Formal Conjectures crosswalk assumes the present eight. Do not promise a
one-command import until those couplings have been removed.

## Build the fully indexed world

1. Add a problem-owned Lean namespace under `ErdosProblems/ErdosNNN/` and
   import it through the expansion root. Expansion declarations checked by
   Lean are not automatically reviewed public claims.
2. Add the authored row to `docs/problem_index_source.json`: question,
   directory, modules, checked and unchecked statements, open obligations,
   finite-search boundary, required note declarations, and honest coverage
   floor. Rebuild with:

   ```sh
   python3 scripts/build_problem_index.py
   python3 scripts/build_problem_index.py --check
   ```

3. Write a standalone problem note. Register its source and PDF through all
   five owners named in `paper/README.md`: `Makefile`,
   `docs/publication_contract.json`, `REUSE.toml`,
   `docs/claims.json::publication_architecture.problem_series`, and the
   problem-index source. Use the public mathematical-writing skill and keep
   the endpoint open unless the evidence actually changes it.
4. Add the source literature, computations, counterexamples, known failed
   routes, and exact contribution points to the problem-owned corpus. Give
   every generated projection its existing builder; do not edit generated
   JSON or full-text paper projections by hand.
5. Add or extend query routes so a cold clone can find the problem by number,
   ordinary language, open obligation, paper, module, and declaration.
6. Extend the accepted-return and route-memory roster, cold-start inventory,
   and the Formal Conjectures crosswalk where an upstream record exists. A new
   local problem without an upstream record must say so rather than inventing
   a match.
7. Add focused tests for root imports, problem-index completeness, paper
   registration, source links, cold-clone comprehension, and public/private
   boundaries. Build the focused Lean root and the paper.

Before adding many worlds, split verbose problem detail out of the bounded
index or deliberately revise its byte budget; the current index is already
close to that limit. Prefer roster-derived checks to copying another fixed
list of problem numbers.

## Promotion is separate

The expansion library is the safe intake layer. Moving a result into the
reviewed claim spine requires a separate claim-methodology change, statement
reconciliation, source coordinates, public exposition, and review. Adding a
problem must not increase a reviewed-result count by side effect.

Return the problem world through the normal pull-request and accepted-receipt
path. Credit the person who proposed the problem, source or status work,
formalisation, software, validation, and writing according to the work they
actually supplied.
