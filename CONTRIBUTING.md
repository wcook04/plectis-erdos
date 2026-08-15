<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Contributing

This repository is a pinned scholarly artefact, so contributions work a
little differently from an ordinary software project: the mathematics, the
paper, and the metadata are released together as one citable object, and
substantial changes land only as a new tagged release with refreshed claim
and citation metadata.

## What is welcome

- **Error reports.** A wrong or misstated result, a Lean build failure, a
  broken source/paper link, or an exposition mistake. Use the issue forms;
  each one asks for exactly the evidence that makes the report checkable.
- **Corrections.** Fixes to prose, citations, or documentation that do not
  change any mathematical claim.
- **Strengthenings.** New formalised results are best proposed in an issue
  first, since they change the claim registry and therefore the release.

## The rules that keep the release trustworthy

- `docs/claims.json` is the single owner of release identity and claim
  status. Never edit a status table, the scope statement, or citation
  metadata directly without updating the registry; `scripts/check_release.py`
  fails when any surface drifts from it.
- `docs/methodology.json` owns the claim-transition rules and change
  classifications; `METHODOLOGY.md` is generated from it. Follow the
  applicable change class before altering a public claim. A successful Lean
  build alone does not authorise a stronger mathematical statement.
- Do not weaken the open-problem boundary. The release states plainly that
  Erdős #249 and the universal #257 remain open; wording that blurs that is a
  defect, not an improvement.
- No `sorry`, `admit`, new `axiom`, or `native_decide` anywhere in the Lean
  proof corpus, including `examples/`. One deliberate exception sits outside
  the default build: `ExternalVerification/Challenge.lean` states the trusted
  propositions Comparator checks the solution against, so it carries `sorry`
  by construction.
- The paper pins every source link to the release tag. Changes that move
  declaration line numbers require regenerating those pins as part of a new
  release, not as a drive-by edit.

## Local checks

```sh
lake exe cache get                 # fetch the prebuilt Mathlib cache
python3 scripts/test_dependency_lock_contract.py  # verify the pinned Lean/Mathlib lock
lake build                         # elaborate and kernel-check the library
lake build Examples                # build the downstream consumer example
python3 scripts/refresh_projections.py  # regenerate every projection in dependency order
python3 scripts/check_release.py   # cross-surface release checks
python3 scripts/test_projection_checkout_independence.py  # projections ignore the checkout shape
python3 scripts/build_module_graph.py --check  # exact public Lean import graph
python3 scripts/refresh_source_coordinates.py --check  # claim/paper line pins
python3 scripts/test_methodology_contract.py  # adversarial claim-transition fixtures
python3 scripts/test_declaration_head_contract.py  # wrapped and odd-tailed declaration names stay in the atlas
python3 -m pip install cffconvert reuse  # once, for metadata and licence checks
python3 scripts/check_metadata.py  # CITATION.cff schema validation (same command as CI)
python3 scripts/test_citation_identity_contract.py  # citation/release identity and open boundary
reuse lint                         # licence validation
python3 scripts/test_license_map_contract.py  # semantic software/manuscript licence split
python3 scripts/check_cold_clone_comprehension.py --quick  # fast committed-surface readability check
python3 scripts/check_cold_clone_comprehension.py  # standalone bounded cold-reader baseline
python3 scripts/test_cold_clone_comprehension.py  # combined baseline-plus-adversarial release-gate check
python3 scripts/test_query_corpus.py  # bounded claim/declaration/module/route queries
```

CI runs the build and release-surface checks on every push.
`scripts/check_release.py` executes the bounded query suite and the combined
cold-clone baseline-plus-adversarial program. A failure therefore blocks the
release gate. The standalone quick and full comprehension commands remain
useful while editing because they produce narrower readability receipts
without running the entire release check.

Editing `docs/claims.json`, `docs/declaration_atlas.json`, `docs/methodology.json`
or the paper sources changes what the projections should say, so run
`scripts/refresh_projections.py` and commit whatever it rewrites together with
the edit that caused it. Two failure modes make this worth doing as one motion.
Regenerating only some builders leaves the rest stale: on 2026-07-19 a run of
paper edits refreshed the corpus descriptor but not the source coordinates, and
the paper anchors in `docs/claims.json` stayed pinned to pre-edit line numbers
for ten commits. And `docs/corpus_descriptor.json` records the last commit that
touched its inputs, which it cannot know while it is being written, so a content
commit pushed on its own is always red until its refresh lands.
