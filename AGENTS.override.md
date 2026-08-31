<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Compact cold-clone agent entry

This is the first-contact contract for repository-aware agents.
[AGENTS.md](AGENTS.md) remains the deep change, authority, and validation
contract; open its relevant section after selecting a task lane here.

This is a self-contained public Lean repository and scholarly artefact. Use
only tracked files in this checkout. Do not depend on `ai_workflow`, sibling
repositories, private caches, auto-memory, unpublished state, or inferred
results.

## Route the task before reading broadly

### Mathematics, theorem status, problem progress, or paper synthesis

Query the public corpus before reading papers or Lean source:

```sh
python3 scripts/query_corpus.py --ask "<question>"
```

For “what is in this repository?”, “give me the lay of the land”, “walk me
through this codebase”, “what are the interesting/non-trivial results?”, “what
has been formalized?”, or a request for full coverage, the ordinary-language
query must resolve to the same complete bounded overview as:

```sh
python3 scripts/query_corpus.py --overview
```

That overview covers every mathematical programme, all claim-status classes,
every exact remaining-open proposition, the publication-family index, and the
companion Plectis boundary. Do not answer a repository-wide question from one
flagship problem or a theorem count. Follow its `answer_contract`: weight
substantive reductions, reusable interfaces, and honest obstructions above raw
volume, while retaining the exact open boundary.

Follow the returned claim, remaining-open, declaration, module, and paper
handles. For a corpus-wide progress review, the bounded route must include:

```sh
python3 scripts/query_corpus.py --route instant_orientation
python3 scripts/query_corpus.py --route erdos249_certificate_story
python3 scripts/query_corpus.py --route erdos257_half_story
python3 scripts/query_corpus.py --route browse_claim_status
```

If free text returns no semantic cells, use those stable routes; do not replace
machine evidence with manuscript-only inference. Erdős #249 and universal
#257 remain open.

### Lean proof work or source mutation

Start from a typed mathematical handle, then cross into source:

```sh
python3 scripts/query_corpus.py --goal-support "<Lean or mathematical goal>"
python3 scripts/query_corpus.py --proof-plan "<Lean or mathematical goal>" --depth 4
```

Use the emitted declarations/modules and verify applicability with Lean. Before
editing, read [AGENTS.md](AGENTS.md) sections `Authority and change order` and
`Validation`, plus [METHODOLOGY.md](METHODOLOGY.md) when a public claim could
change. Lean source checked by the pinned kernel is proof authority.

### Repository architecture, agent entry, cold-clone organization, or docs routing

This lane is not a mathematical query. Start with the committed cold-clone
contract and bounded orientation:

```sh
python3 scripts/test_compact_agent_entry.py
python3 scripts/check_cold_clone_comprehension.py --quick
```

Then read `docs/orientation.json::agent_entry`, [ARCHITECTURE.md](ARCHITECTURE.md),
or [docs/ORIENTATION.md](docs/ORIENTATION.md), depending on the returned owner.
Generated orientation, source maps, indices, aliases, and publication packets
must be changed through their builder, never by hand.

### Publication, systems-paper, or artifact-boundary work

For paper choice, role, availability, or reading order, start with:

```sh
python3 scripts/query_corpus.py --papers
```

For external assurance and release qualification, use the exact bounded routes:

```sh
python3 scripts/query_corpus.py --route comparator_assurance
python3 scripts/query_corpus.py --route palomar_qualification
```

`comparator_assurance` reports the configured comparison packet, modules,
axioms, and receipt; it does not establish novelty, significance, priority, or
peer review. `palomar_qualification` reports repository-local policy readiness
and its remaining operator-only decisions; it does not confer acceptance,
registration, publication, or external endorsement.

The same guide must answer ordinary requests such as “which papers should I
read?” through `--ask`. It separates the mathematical gateway, specialist
companion, repository-systems guide, and reciprocal Plectis route; it also
refuses to send a cold reader into a registered artifact absent from the
checkout. After choosing a paper, follow its typed claim, open, declaration,
source, or publication handles rather than treating prose as authority.
`docs/papers/README.md` is the human question-first index, while
`docs/papers/corpus.json` is the machine inventory of every carried manuscript
and section anchor.

For publication mutation, open `docs/publication_entry_packet.json` first, then
`docs/publication_contract.json` or one typed query-corpus paper/publication
handle. These surfaces own publication organization and evidence boundaries;
they do not acquire Lean proof authority. Authored prose is digested exposition,
not a substitute for the claim registry or checked source.

### General Plectis machinery

The companion [`plectis`](https://github.com/wcook04/plectis) repository owns
the runnable system/corpus machinery. This repository owns the public
mathematical corpus. Do not infer one repository's authority from the other,
and do not require the companion checkout for any command listed above.

## Authority order

1. Lean source checked by the pinned Lean kernel: proof authority.
2. `docs/claims.json`: public claim identity, status, declarations, and exact
   remaining-open propositions.
3. `docs/methodology.json`: evidence responsibilities and claim-change rules.
4. Generated orientation, declaration, module, and publication packets:
   bounded navigation projections.
5. Papers and human summaries: authored exposition within the registered claim
   ceiling.
6. Model output, plans, memory, and prose drafts: working aids only.

No navigation handle, theorem count, finite computation, conditional reduction,
paper sentence, or provider output may be promoted past that order.

## Mutation and concurrency

- Preserve unrelated staged and unstaged work. Do not reset, restore, clean, or
  broad-stage a shared checkout.
- Modify source authorities before their generated projections and run the
  named owner builder/checker.
- A paper edit does not authorize a claim change; a registry edit does not
  prove a theorem; a passing navigation check does not prove mathematics.
- Never add `sorry`, `admit`, project-defined `axiom`, `native_decide`,
  unsafe/partial declarations, or unbounded kernel limits.
- Use `python3 scripts/lean_fast_build.py --jobs 2` for bounded builds when
  appropriate; do not overlap competing root and focused builds.

## Validation

Use the smallest relevant proof first:

```sh
python3 scripts/test_compact_agent_entry.py
python3 scripts/check_cold_clone_comprehension.py --quick
python3 scripts/check_architecture_guide.py
```

For a committed-snapshot release check in a dirty shared checkout:

```sh
python3 scripts/check_release_ref.py --ref HEAD --receipt /tmp/release-head.json
```

Run the relevant projection builders in `--check` mode and the focused public
tests named by [AGENTS.md](AGENTS.md). Run `lake build` after Lean changes.

Do not absorb the complete deep contract, exhaustive declaration atlas, module
graph, or both papers merely to discover the first action.
