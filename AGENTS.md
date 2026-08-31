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

Use [docs/AGENT_WORKBENCH.md](docs/AGENT_WORKBENCH.md) for the compact command
routes and [CONTRIBUTING.md](CONTRIBUTING.md) for contribution mechanics. This
file remains the deeper authority, mutation, and validation contract.

For any reader-facing mathematical Markdown or manuscript edit, load
[skills/public-mathematical-writing/SKILL.md](skills/public-mathematical-writing/SKILL.md).
It keeps mathematical truth and evidence upstream of prose and keeps the human
front door in ordinary language; agent surfaces may remain command-heavy.

## Eight-problem cold-start card

A blank-slate agent must receive the complete problem fleet here; it must not
already know a query command or infer the fleet from directory names.
**All eight indexed problems remain open.**

Each entry states the mathematical target, then the checked frontier and live
obstruction, then the standalone paper.

**#68 — Is `∑_{n≥2} 1/(n!−1)` irrational?**

Lean checks exact factorial-successor and carry equivalences, integral-channel
and projection consumers, and the reduction from a non-unit carry to a
denominator bound. An exact finite certificate reaches `300000`; no cofinal
non-unit-carry or residual-nonintegrality producer is proved. Paper:
`erdos-68-factorial-denominator-irrationality.pdf`.

**#243 — Under rapid growth of an integer sequence, does rationality of its
reciprocal sum force the Sylvester recurrence eventually?**

Lean checks the product-cleared tail dynamics, absorbing zero state, descent on
nonnegative centred states, and bounded or periodic negative-state barriers.
Normalised vanishing makes strict centring redundant and is available for the
canonical orbit through Koizumi's results; boundedness of the negative part is
the missing hypothesis, with mixed-sign and unbounded-negative regimes still
open. Paper: `erdos-243-reciprocal-tail-rigidity.pdf`.

**#249 — Is \(\sum_{n\ge1}\varphi(n)/2^n\) irrational?**

Lean checks a rational basis for the full dyadic totient kernel, true level rank
\(2^e+1\) for \(e\ge1\), the \(7.96\times10^{34}\) finite denominator exclusion,
and diagonal certificates for every \(t\le82\). No \(t=83\) or unbounded
certificate producer is proved; the exact cofinal equivalences diagnose rather
than solve the problem. Paper: `erdos-249-binary-totient-series.pdf`.

**#251 — Is \(\sum_{n\ge1}p_n/2^n\) irrational, equivalently the associated
consecutive-prime-gap dyadic series?**

Lean checks finite summation by parts, the exact prime/prime-gap equivalence
under summability, and integral-shift recurrence consumers. Cofinal
nonintegrality or adjacent small-shift witnesses for the actual prime gaps, plus
the concrete infinite-sum bridge, remain open. Paper:
`erdos-251-prime-gap-dyadic-series.pdf`.

**#257 — For every infinite \(A\subseteq\mathbb N_{>0}\), is
\(\sum_{n\in A}1/(2^n-1)\) irrational?**

Lean checks full support, finite-period noncollapse, named structured families,
hereditary unique coding, and the compactness, topology, perfectness, and exact
measure dichotomy of restricted achievement sets. Prime support at base 2 and
squarefree support at power-of-two bases are cited prior results. No arithmetic
obstruction covers every infinite support; the universal statement and the exact
\(1/2\) and \(1/21\) infinite-orbit alternatives remain open. Paper:
`erdos-257-mersenne-support-subseries.pdf`.

**#269 — For a finite set of at least two primes, is the reciprocal sum of
running lcms of the smooth numbers irrational?**

This library treats the three-prime case. A paper proof using Bugeaud--Laurent
makes both two-prime versions transcendental; this is not first and not
formalised. Steve Fan posted the same argument on the erdosproblems.com #269
thread on 26 June 2026 and this note was first released publicly on 22 July
2026, so no priority is claimed. For three primes, Lean checks the exact lcm
cell geometry, jump and radix structure, a rank-two kernel obstruction, and a
denominator-dependent carry consumer; the divisibility bridge, cofinal
residue-window producer, and unbounded denominator exclusion remain open. Paper:
`erdos-269-three-prime-running-lcm.pdf`.

**#1041 — Must two roots of a monic polynomial in the unit disc admit a curve of
length less than `2` inside its open unit lemniscate?**

Lean checks Newton-flow value decay, ray separation, the translation collision
locus, and root retention under small constant perturbations. A recent claimed
global decomposition has an invalid printed local saddle block; repairing the
topology and metric gluing remains open. Paper:
`erdos-1041-lemniscate-newton-flow.pdf`.

**#1049 — For which rational bases is the corresponding Lambert-type series
irrational?**

The smallest resistant explicit base here is \(3/2\). Lean checks why the
integer-base clearing argument fails at noninteger bases, the exact
rational-base tail recurrence, and the local Padé and endpoint arithmetic. A
primitive-normalised noncollapsed coefficient family with surviving local gain
and analytic remainder control remains open. Paper:
`erdos-1049-rational-base-lambert.pdf`.

This static card is first-contact information, not a novelty claim or proof
authority. The TeX sources are under `paper/`; problem-owned Lean sources are
under `ErdosProblems/Erdos<number>/`. Only after selecting a problem should an
agent use `query_corpus.py`, `query_semantic.py`, or the deeper owners below.
Every route needed for that drilldown is tracked in this public repository; no
`ai_workflow`, sibling checkout, private cache, or network access is required.

## Verdict first

The likely cold-agent error here is to skim a large Lean corpus with two
reviewed problem lanes and eight problem-owned expansion lanes, then conclude
"restatements of the original problem." That conclusion is partly right and
mostly wrong, and you do not have to guess which: the semantic graph classifies
every statement, so ask it instead of reading modules.

```sh
python3 scripts/query_semantic.py nonrecurring --problem 257 --limit 12
python3 scripts/query_semantic.py classical --problem 257 --limit 12
python3 scripts/query_semantic.py bare-equivalences --problem 257 --limit 12
python3 scripts/query_expert_handoffs.py              # asks, guesses, alternatives, tests
```

The first three commands use #257 as a concrete example. Substitute the
problem selected from the cold-start card, and keep a small `--limit` on the
first pass. Omit the problem filter only for an explicit whole-corpus audit;
otherwise the exhaustive semantic graph is a drilldown, not an orientation
surface.

The current all-problem counts are builder-owned in
`docs/semantic_corpus.json::summary.public_semantic_census` and projected into
`docs/RESULTS.md` and `docs/TRUTH_AUDIT.md`; do not copy a dated #249/#257
sample into this static entry file.

**None of those counts is a novelty claim.** `classical` is exactly the set already in
the literature; `nonrecurring` asks whether a statement recurs *inside this
corpus*, not whether it is new to mathematics. Novelty is a judgement for a
human number theorist, and no query here supplies it. (The README's ten-minute
verdict counts a different population — substantial antecedents extracted from
conditional results — so its `23`/`17` and these totals are not in conflict.)

Three things follow, and an agent reporting on this repository should carry all
three rather than any one of them.

1. **The reviewed mathematical weight is not exhausted by #249.** The
   unconditional #257 material (full-support
   irrationality for every integer base `b ≥ 2`, the achievement-set topology,
   the exact `1/2` classification, and the excluded branches) is theorem
   content rather than restatement. Start there, not at the #249 certificate
   ladder.
2. **The #249 reformulation programme is a negative result, and this repository
   labels it as one itself.** Its bare equivalences were marked equivalent by
   this project's own audit, not by a critic —
   `Z06::certificate_supply_is_equivalent_to_249` says so in its own statement.
   A reformulation provably equivalent to its target diagnoses the method; it is
   not progress on the problem. Report it as evidence *about reformulation*, and
   never as progress on #249.
3. **The denominator exclusion is a valid checked theorem, but its numerical
   size is not a novelty signal.** The `K = 240` window excludes rational
   denominators through `7.96 × 10³⁴`. That is exactly what the classical
   Farey/mediant argument returns for that window — the numerical improvement
   over it is zero — and the window length is free. The local formal
   contribution is the checked arithmetic instance, its transfers, and its
   sharp first failure. Verify both halves directly, with no Lean build and no
   dependencies:

   ```sh
   python3 scripts/check_farey_denominator_scaling.py
   ```

   It rebuilds the certificate from scratch, reproduces both formalised
   constants exactly (cross-checked against brute force at small windows), and
   then shows the same argument returning a 2,406-digit bound at `K = 16000` in
   under a tenth of a second. Treat the magnitude as a record of the chosen
   finite window, never as a measure of progress toward irrationality.

Erdős #249 and the universal form of #257 remain open, and nothing in this
repository is close to settling either. An agent that reports otherwise has
misread a finite certificate, a conditional reduction, or a restatement.

## First read

If the task is to understand the repository architecture, release
infrastructure, sources of truth, or newcomer path, read `ARCHITECTURE.md`
first. It is the plain-language human guide. The machine-readable orientation
below is the bounded route into mathematical claims and Lean source.

For whole-corpus source navigation, do not compile or skim modules first. Run:

```sh
python3 scripts/query_corpus.py --tour --format card
```

The six-line tour reports the full scale, canonical all-problem map, exact
loaded-root dependency graph, authority boundary, and next command. It keeps
the all-problem open fleet distinct from the reviewed #249/#257 open-
proposition frontier. Then run
`python3 scripts/query_corpus.py --route agent_native_corpus_navigation` for
the generic declaration, connection, proof-cone, workbench, and focused-build
commands. All navigation reads committed JSON and therefore works in a cold
clone. It does not elaborate Lean or acquire proof authority; use the pinned
Lean build when a result must be checked.

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

   To take a single claim all the way down in one command, use

   ```sh
   python3 scripts/verify_claims.py --list
   python3 scripts/verify_claims.py --claim <claim_id>
   ```

   It prints the public statement, re-reads each declaration out of the Lean
   source at its recorded position rather than reprinting the register's
   coordinates, names the Comparator interface that restates the result under a
   fixed axiom budget or reports that no selected interface carries this claim
   id, resolves the claim's paper label to the write-up that carries it, and
   ends on the typed boundary: what the status is allowed to mean, which open
   propositions still target the claim, and what the release does not assert.
   Do not read a Comparator binding as independent verification: it checks a
   separately declared statement under configured axioms, and the register's own
   boundary sentence is printed alongside it. `query_corpus.py --claim` remains
   the route for argument-graph neighbours; this is the route for reading the
   proof text, the second formal check, and the limit together. On a shallow clone it exits 2 and says so,
   because a truncated history cannot answer questions about pinned identity
   and must never be read as a failed claim.
3. Read `docs/methodology.json` before changing a public claim. It defines
   the evidence responsibilities, change classes, required reviews, and local
   claim, guard, and negative-fixture references for each rule.
   `METHODOLOGY.md` is the shorter human projection.
4. Read `docs/corpus_descriptor.json` when another agent or system needs to
   register this repository as a mathematical corpus. It separates the pinned
   proof-source commit from the content-addressed navigation projection, and
   carries bounded principal handles plus digest-bound expansion routes for
   both authored papers and the paper-to-Lean source-sigil crosswalk. Generated
   navigation does not pretend to contain the Git commit that first contains
   its own bytes. These authored surfaces remain distinct from Lean proof
   authority. The release gate keeps this registration envelope below 64 KB.
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
8. For one claim, use `docs/papers/corpus.json` to resolve its `paper_label`
   to the owning individual problem paper, then follow its `declarations` to
   the named Lean source coordinates. The archived combined #249/#257
   manuscript is provenance, not the default gateway. To read surrounding
   exposition rather than locate a claim, use the generated full text in
   `docs/papers/`, where each manuscript's own section labels are HTML anchors:
   `grep -n '<a id="sec:unresolved">' docs/papers/full-text/*.md`.
9. Read `docs/papers/corpus.json` when the task concerns what the papers say
   rather than what Lean checked. It is the bounded index to every registered
   manuscript, including the Plectis paper carried as a mirror so this clone is
   readable offline. It names the question each paper answers, the reading
   route each paper states for itself, every section with its label and line,
   and what each paper is not authority for. The generated Markdown is a
   projection: it resolves theorem numbers, cross-references, and Lean source
   links that the `.tex` only implies, but the `.tex` remains the manuscript and
   the hash of record. Neither is proof authority.
10. Read `docs/problems.json` when the task names a single Erdős problem
   covered by the `ErdosProblems` expansion library. It is the generated,
   bounded problem-owned index: one row per currently indexed problem giving
   its modules with declaration counts, its Erdős Problem Note, what is
   checked, what is not checked, the obligation that survives, the standalone
   paper that writes the problem up, and the Comparator disposition of every
   contribution family. The last two are joins into `docs/papers/corpus.json`
   and the review matrix in `docs/claims.json`; a disposition says whether
   Comparator was asked to check that family, not whether it is true. The #249
   and #257 rows index expansion modules and do not replace the separately
   reviewed `Erdos249257` claim registry.
   Its authored source is `docs/problem_index_source.json` and it is rebuilt by
   `python3 scripts/build_problem_index.py`. **These declarations carry no
   reviewed public claim status.** The claim registry has no row for them, and
   a passing kernel check of `ErdosProblems.lean` does not create one; do not
   report a problem as advanced because its module count grew.
11. Use `docs/declaration_atlas.json` when you need the exhaustive mathematical
   scale: every declaration, signature excerpt, module, import edge, generated
   certificate marker, and principal-claim link. It is a generated navigation
   projection; drill back to Lean before trusting a statement.
12. Read `docs/semantic_corpus.json` when the question is *what this corpus
   proves and how its statements relate*, rather than where one declaration
   lives. It is the layer between the atlas and the claim registry: one node
   per mathematically distinct statement, typed mathematical relations between
   nodes, and an explicit semantic role for every declaration in both
   libraries. `docs/semantic/README.md` explains the two objects and why
   equivalences are preserved rather than deduplicated away. Do not answer
   "what is actually proved here" by rereading modules; ask the graph:

   ```sh
   python3 scripts/query_semantic.py nonrecurring --problem 257
   python3 scripts/query_semantic.py barriers
   python3 scripts/query_semantic.py open-antecedents
   python3 scripts/query_semantic.py coverage
   python3 scripts/query_semantic.py problem-registry
   python3 scripts/query_semantic.py paper-coverage
   python3 scripts/query_semantic.py population-backlog
   python3 scripts/query_semantic.py structural-backlog --problem 257
   python3 scripts/query_semantic.py semantic-reviews
   ```

   Provenance for emitted modules is owned by
   `docs/generated_certificate_manifest.json`, never by a filename pattern: a
   module is generated if and only if the manifest lists it.
   `docs/semantic/reviews.json` separately records digest-bound semantic
   reviews for selected high-value nodes and relations. A model receipt means
   exact source-to-wording consistency review within its stated ceiling, not
   human review, novelty authority, or Lean proof authority.
   Read the `coverage` result by tier: `authored_statement` is mathematical
   interpretation, `source_structural_family` is exact module/signature
   discoverability only, and direct proposition evidence is stricter than
   contextual membership in an authored certificate family.
13. Read `docs/theory_lab.json` when the question is *why* a proof works, what
   happens if the mathematics is perturbed, or whether an explanation here has
   ever been tested. It sits above the semantic corpus and holds the mechanism
   basis (an invariant plus a transformation plus the observable it controls),
   typed interventions with predictions stamped before their outcomes, failure
   receipts for routes that were tried and blocked, and blinded holdout
   evaluations. `docs/semantic/lab/README.md` explains the design.

   ```sh
   python3 scripts/query_semantic.py mechanisms --problem 257
   python3 scripts/query_semantic.py explains <node_id>
   python3 scripts/query_semantic.py unexplained
   python3 scripts/query_semantic.py receipts
   python3 scripts/query_semantic.py benchmark
   ```

   Two rules matter when you add to it. A receipt that rules a mechanism out
   must name the sibling mechanisms it does **not** reach -- omitting that is
   how a barrier here nearly went out described as closing a family of engines
   while a weaker one survived. And a mechanism is not a theorem family: if the
   record cannot be used to predict whether a *new* nearby statement is
   reachable, it is a label and the contract rejects it.
14. Use `Erdos249257.lean` for the reviewed #249/#257 root and
   `ErdosProblems.lean` for the problem-owned expansion root. Kernel checking
   the expansion root does not promote its declarations into reviewed public
   claims. Use `docs/SOURCE_MAP.md` for intention-based routes and
   `docs/WAVE_INDEX.md` for mathematical chronology. For arbitrary Lean,
   including auxiliary modules intentionally excluded from compact import
   roots, start with the module-agnostic inventory:

   ```sh
   python3 scripts/query_semantic.py problem-registry
   python3 scripts/query_semantic.py inventory <text> \
     --module <optional/path.lean> --role <optional-role> --zone <optional-zone>
   ```

   The inventory is exhaustive source navigation, not semantic interpretation.
   Exact elaborated dependency neighborhoods cover declarations loaded through
   either supported compact root. Authored statement-node links remain the only
   statement-level semantic claims.

For a bounded lookup, use `python3 scripts/query_corpus.py` with one typed
handle:

- `--vocabulary` for the compact executable mathematical Rosetta stone:
  question operators, ordinary-language aliases, corpus terms of art,
  transparent query expansions, and typed route hints;
- `--ask "<question>"` to compile ordinary mathematical language into a
  bounded witness graph while keeping kernel, claim-status, authored-digestion,
  and navigation provenance separate; support and trace cells use the
  source-joined elaborated dependency index when it is fresh, and the contract
  and evaluation levels are documented in `docs/SEMANTIC_COMPILER.md`;
  relational trace questions with explicit `from ... to ...` endpoints resolve
  each endpoint independently before searching for an exact formal path;
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
- `--goal-support "<Lean or mathematical goal>"` for theorem candidates ranked
  by precomputed elaborated conclusion shape, conclusion constants, exact
  context phrases, and binder structure; this is a navigation affordance, not
  an applicability proof, so the emitted `apply` candidates still require
  Lean elaboration;
- `--proof-plan "<Lean or mathematical goal>" --depth <1..8>` to extend the
  best goal-support candidate with its Lean-classified term/proposition
  telescope, a context-match or missing-obligation ledger, and a bounded exact
  proof-term dependency spine;
- `python3 scripts/proof_state_compiler.py --pilot-controls` to cross the
  static/runtime boundary: candidate applications are executed against actual
  Lean examples, accepted transitions become AND/OR obligation hyperedges,
  rejected applications retain typed failures, and closed runs carry replay
  receipts.  Use `--request-file` or `--request-stdin` for another explicit
  bounded goal; this runtime packet is documented in
  `docs/PROOF_STATE_COMPILER.md` and remains distinct from claim status;
- `python3 scripts/proof_workbench.py {open,note,probe,claim,close,replay,show}`
  for the agent-native session notary: typed cognitive moves in an
  append-only ledger, kernel probes whose verdicts the agent cannot author,
  claims that must cite kernel-accepted probe receipts, and byte-exact
  session replay.  The inhabitation contract — instruments versus agent
  policy, and the assisted / context-blind / prospective invention ladder —
  is `docs/AGENT_WORKBENCH.md`;
- `--proof-cone <declaration> --depth <1..8>` for a bounded,
  theorem-prioritized cone of exact proof-term dependencies, or
  `--dependency-path <source> <target> --depth <1..8>` for the shortest exact
  directed path between two source-resolved declarations;
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
python3 scripts/check_problem_note_sources.py --coverage
python3 scripts/build_problem_index.py --check
python3 scripts/build_semantic_corpus.py --check
python3 scripts/check_semantic_corpus.py
python3 scripts/semantic_review.py --check
python3 scripts/build_theory_lab.py --check
python3 scripts/check_theory_lab.py
python3 scripts/test_declaration_head_contract.py
python3 scripts/test_dependency_lock_contract.py
python3 scripts/test_citation_identity_contract.py
python3 scripts/test_license_map_contract.py
python3 scripts/test_methodology_contract.py
python3 scripts/build_module_graph.py --check
python3 scripts/build_module_synopsis_index.py --check
python3 scripts/build_lean_dependency_index.py --check
python3 scripts/refresh_source_coordinates.py --check
python3 scripts/build_corpus_descriptor.py --check
python3 scripts/build_publication_entry_packet.py --check
python3 scripts/check_publication_contract.py
python3 scripts/test_publication_artifact_contract.py
python3 scripts/run_publication_mutations.py --verify-operators
python3 scripts/test_query_corpus.py --programme-routes-only
python3 scripts/test_query_corpus_resilience.py
python3 scripts/benchmark_semantic_reasoning.py --split held_out
python3 scripts/audit_semantic_corpus.py
python3 scripts/dogfood_semantic_proof.py
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
