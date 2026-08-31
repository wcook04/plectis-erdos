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

For a repository overview or full-coverage request, use:

```sh
python3 scripts/query_corpus.py --overview --format card
```

It covers every programme, status class, exact open proposition, paper family,
and the companion boundary. Do not answer from one flagship or theorem count;
follow its `answer_contract` and preserve every exact open boundary.

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

Mathematical prose follows
[the writing skill](skills/public-mathematical-writing/SKILL.md).

For paper choice, role, availability, or reading order, start with:

```sh
python3 scripts/query_corpus.py --papers
```

For external assurance and release qualification, use the exact bounded routes:

```sh
python3 scripts/query_corpus.py --route comparator_assurance
python3 scripts/query_corpus.py --route palomar_qualification
```

`comparator_assurance` does not establish novelty, significance, priority, or
peer review. `palomar_qualification` does not confer acceptance, registration,
publication, or external endorsement.

For paper choice use `--ask`, `docs/papers/README.md`, and the machine inventory
`docs/papers/corpus.json`. Follow typed claim and source handles; prose is not
proof authority.

For publication mutation, open `docs/publication_entry_packet.json`, then the
publication contract or emitted handle. These own organisation, not Lean proof.

### Explain, install, mine, validate, propagate, or add a problem

Use the clone-local skills in `skills/`: `explain-public-system`,
`install-clone-skills`, `run-coupled-research-goals`, `mine-open-problem`,
`lean-concurrent-validation`, `propagate-research-consequences`, `add-open-problem`, and
`submit-pull-request`. The mining skill may coordinate subagents, but the
integrating agent verifies every return. After a stable mathematical or
architecture delta, the propagation skill gives each plausible downstream
consumer a disposition before the result is packaged. The submission skill may
prepare and commit locally; it pushes or opens a pull request only after
explicit authorisation.

### Return research from a clone

For contributed or resumable work, load:

```sh
cat skills/erdos-research-return/SKILL.md
```

Keep the human account in the pull request or plain-language issue. Bind public
provenance and exact credit in the returned package; accepted receipts travel
to older clones in Git history. Never require a private repository.

An older clone remains a valid source of work. Preserve its recorded starting
commit and original delta, reconcile the reviewed change with current main,
then rerun current validation and consequence propagation. A material conflict
resolution is a separately credited integration change.

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
