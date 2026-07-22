<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Agent entry

This is an ordinary public Lean project and a pinned scholarly artefact. It is
not an entrypoint into any private development system. Work only from the files
in this repository, and never infer unpublished results or private machinery.
The checkout is nevertheless a deliberately curated public projection from a
larger ongoing formal-mathematics workflow: its release discipline, claim
registry, graph structure, generated atlas, and adversarial checks are public
evidence of that workflow. They do not create hidden proof authority.

## First read

If the task is to understand the repository architecture, release
infrastructure, sources of truth, or newcomer path, read `ARCHITECTURE.md`
first. It is the plain-language human guide. The machine-readable orientation
below is the bounded route into mathematical claims and Lean source.

1. Read `docs/orientation.json`. It is the bounded first-read capsule: release
   scale, exact open propositions, mathematical programme routes, principal
   claim routes, and typed drilldowns. Its human projection is
   `docs/ORIENTATION.md`. Both are generated navigation, not proof authority.
2. Drill into `docs/claims.json` only for the selected claim or route. Its
   `machine_readable_paper` object owns the complete map from paper claims to
   Lean declarations, module imports, argument relationships, validation, and
   explicit non-claims. Its `publication_assembly` partitions every public
   claim exactly once into a contribution family with a narrative owner,
   prior-art posture, consumer or open obligation, and rendered-view decision.
   Do not load its exhaustive module graph merely to orient.
3. Read `docs/methodology.json` before changing a public claim. It defines
   the evidence responsibilities, change classes, required reviews, and local
   claim, guard, and negative-fixture references for each rule.
   `METHODOLOGY.md` is the shorter human projection.
4. Read `docs/corpus_descriptor.json` when another agent or system needs to
   register this repository as a mathematical corpus. It separates the pinned
   proof-source tag from the later navigation snapshot and content digests, and
   carries bounded principal handles plus digest-bound expansion routes for both
   authored papers and the paper-to-Lean source-sigil crosswalk. These authored
   surfaces remain distinct from Lean proof authority. The release gate keeps
   this registration envelope below 64 KB.
5. Read `docs/publication_entry_packet.json` when the task concerns the
   systems paper, publication controls, mutation evidence, or their current
   limits. It is a generated, bounded agent packet containing the thesis,
   checked claims and non-claims, historical and current evidence snapshots,
   authority owners, content hashes, validation commands, and active evidence
   residuals. It is navigation, not Lean proof authority or historical
   evidence authority. Its authored source is
   `docs/publication_entry_source.json`.
6. Read `docs/publication_contract.json` for the exact inventory of shipped
   manuscripts and PDFs, their content identities, their evidence boundaries,
   and their entry routes. It owns publication-artifact coverage, not
   mathematical claim status. In particular, the systems case study is
   evidence about release controls and does not acquire Lean proof authority.
   Read `docs/publication_evidence.json` for the typed historical mutation
   matrix, protocol, timings, M8 escape, post-repair rerun boundary, and
   explicit absence of registered raw run logs or executable mutation
   operators. `experiments/publication_mutations.json` and
   `scripts/run_publication_mutations.py` provide a separately versioned,
   deterministic reconstruction of the ten mutation classes; they are not the
   missing original run logs or exact targets.
7. Read `SCOPE.md` before describing what the project proves. Erdős #249 and
   the universal form of #257 remain open.
8. For one claim, follow its `paper_label` into
   `paper/erdos249-257-main-paper.tex`, then follow its `declarations` to the
   named Lean source coordinates. To read the surrounding exposition rather
   than locate a claim, use the generated full text in `docs/papers/`, where
   the manuscript's own section labels are HTML anchors:
   `grep -n '<a id="sec:unresolved">' docs/papers/full-text/*.md`.
9. Read `docs/papers/corpus.json` when the task concerns what the papers say
   rather than what Lean checked. It is the bounded index to all three papers —
   both authored here plus the Plectis paper, carried as a mirror so this clone
   is readable offline. It names the question each paper answers, the reading
   route each paper states for itself, every section with its label and line,
   and what each paper is not authority for. The generated Markdown is a
   projection: it resolves theorem numbers, cross-references, and Lean source
   links that the `.tex` only implies, but the `.tex` remains the manuscript and
   the hash of record. Neither is proof authority.
10. Use `docs/declaration_atlas.json` when you need the exhaustive mathematical
   scale: every declaration, signature excerpt, module, import edge, generated
   certificate marker, and principal-claim link. It is a generated navigation
   projection; drill back to Lean before trusting a statement.
11. Use `Erdos249257.lean` for the reviewed #249/#257 root and
   `ErdosProblems.lean` for the problem-owned expansion root. Kernel checking
   the expansion root does not promote its declarations into reviewed public
   claims. Use `docs/SOURCE_MAP.md` for intention-based routes and
   `docs/WAVE_INDEX.md` for mathematical chronology.

For a bounded lookup, use `python3 scripts/query_corpus.py` with one typed
handle:

- `--claim <id>`, `--open <remaining_open.id>`, or `--route <id>` for the
  mathematical story and exact frontier;
- programme routes such as `erdos249_diagonal_arithmetic`,
  `transport_curvature_programme`, `boolean_mobius_constraints`, and
  `erdos257_half_story` for a bounded map of one coherent mathematical
  programme, including its exact claim ceiling and surviving open proposition;
- `--paper-label <label>` or `--paper-anchor <label_or_source_ref>` for authored
  exposition;
- `--publication-family <id>` for one contribution family's status,
  prior-art posture, narrative owner, source route, consumer, and view decision;
- `--publication-architecture` for the gateway/companion verdict and complete
  contribution-family index;
- `--declaration <name>`, `--source <module.lean:line>`, or `--module <path_or_id>`
  for checked source;
- `--artifact <path_or_sha256>` for a registered paper, PDF, JSON owner, or
  content identity;
- `--publication-artifact <id>` for a shipped manuscript's typed role,
  expected digests, current drift status, evidence boundary, and validation;
- `--publication-evidence [MUTATION_ID]` for the historical experiment summary
  or one exact mutation row, including its detector and evidence ceiling;
- `--connections <module_or_declaration> --query "<task>"` after choosing a
  source handle; and
- `--search "what remains open for 257" --limit 10` (or another short natural
  question) only when no typed handle is known.

Run `python3 scripts/query_corpus.py --help` for the full grammar. Responses are
capped at 64 KB and route exhaustive data back to its owner. Follow adjacent
claim IDs one packet at a time; do not load the complete graph to orient. An
exact open-proposition ID must not be replaced by finite or conditional
progress. A paper label, declaration, source line, module sigil, or digest is a
navigation handle, not a fabricated claim and not proof authority.

## Authority and change order

- Lean source checked by the pinned Lean kernel is proof authority.
- `docs/claims.json` owns release identity, status taxonomy, declaration
  coordinates, typed remaining-open propositions, and the machine-readable
  navigation graph.
- `docs/methodology.json` owns mathematical methodology and claim-transition
  requirements. It is not proof authority and does not own claim status.
- `docs/corpus_descriptor.json` is a generated, compact registration envelope;
  it does not replace the claim registry, exhaustive atlas, or Lean authority.
- The paper is authored mathematical exposition. Do not generate or rewrite its
  prose mechanically from the registry.
- README, scope, source maps, and other summaries must not exceed the status in
  the claim registry.
- Provider or model output is never proof authority.

Before updating a public claim, classify the change against the
`change_classes` matrix in `docs/methodology.json`: each class states its
minimum evidence, whether human mathematical review is required, and the
effects the change must not have. The update order stays fixed: Lean source
first, then assumption and meaning review, then the claim registry, then
authored exposition, then generated projections.

## Validation

Run the focused public-surface gate after documentation or registry changes:

```sh
python3 scripts/check_release.py
python3 scripts/test_dependency_lock_contract.py
python3 scripts/test_citation_identity_contract.py
python3 scripts/test_license_map_contract.py
python3 scripts/test_methodology_contract.py
python3 scripts/build_module_graph.py --check
python3 scripts/refresh_source_coordinates.py --check
python3 scripts/build_corpus_descriptor.py --check
python3 scripts/build_publication_entry_packet.py --check
python3 scripts/check_publication_contract.py
python3 scripts/test_publication_artifact_contract.py
python3 scripts/run_publication_mutations.py --verify-operators
python3 scripts/test_query_corpus.py --programme-routes-only
python3 scripts/test_status_question_search.py
python3 scripts/test_claim_packet_boundaries.py
python3 scripts/test_publication_evidence_time_axis.py
python3 scripts/test_query_corpus.py
```

When the shared worktree contains unrelated in-progress edits, validate the
committed snapshot without cleaning or stashing anyone's files:

```sh
python3 scripts/check_release_ref.py --ref HEAD --receipt /tmp/release-head.json
```

The wrapper uses a disposable local clone and excludes all caller worktree
changes. `--probe-only` verifies ref resolution and clone preparation without
running the expensive release gate.

Run the full proof authority check after Lean changes:

```sh
lake build
```

The release checker validates claim status, declaration coordinates, paper
anchors, the machine-readable module and argument graphs, the exhaustive
declaration atlas, scope, metadata, licensing, and proof-trust guards. Do not
add `sorry`, `admit`, `axiom`, `native_decide`, unsafe/partial declarations,
or unbounded kernel limits; finite computations use kernel-checked `decide`.

After adding, removing, or rewiring Lean modules, run
`python3 scripts/build_module_graph.py` before the other projections.  It
derives paths and imports from source while preserving authored module roles;
it does not author claims or paper prose.
After declaration lines move, rebuild the declaration atlas and run
`python3 scripts/refresh_source_coordinates.py`; it changes coordinates only,
never declaration names or mathematical prose.

A separate diagnostic checks that a cold clone stays readable:

```sh
python3 scripts/check_cold_clone_comprehension.py --quick
python3 scripts/check_architecture_guide.py
python3 scripts/test_architecture_guide.py
python3 scripts/check_cold_clone_comprehension.py
python3 scripts/test_cold_clone_comprehension.py
```

The `--quick` path checks the committed compact human and agent projections
without a Lean build or typed-query sweep, so a fresh clone gets an immediate
readability receipt. The full diagnostic proves the first-contact boundary
through the same bounded public query packets a cold coding agent would follow;
it does not concatenate the claim registry, methodology, or declaration atlas
as evidence. Both check navigation semantics and response budgets, not Lean
proof correctness, and the full diagnostic runs in the release gate. A failure
means a projection, route, or typed handle dropped a distinction and should be
repaired.
The companion adversarial test removes human semantic anchors and mutates proof
authority, open-boundary, finite-bound, source-coordinate, and graph-link
facts; every mutation must make the evaluator fail.
