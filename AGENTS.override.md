<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Compact cold-clone agent entry

First-contact contract. [AGENTS.md](AGENTS.md) owns deep change,
authority, and validation rules; open only the section the route names.

This is a self-contained public Lean repository and scholarly artefact. Use only
tracked files in this checkout. Do not depend on `ai_workflow`, sibling
repositories, private caches, auto-memory, or unpublished state.

Route the actual task before opening broad files:

```sh
python3 scripts/agent_entry.py --entry "<task in ordinary language>"
```

It recommends a task lane, the smallest read set, and the relevant skills;
`python3 scripts/agent_entry.py --skills` is the complete catalog. Its routing
metadata is navigation, not mathematical authority.

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

It covers every programme, status class, exact open proposition, and paper
family. Do not answer from one flagship or theorem count; follow its
`answer_contract` and preserve every exact open boundary.

Follow the returned claim, remaining-open, declaration, module, and paper
handles. For a corpus-wide progress review, the bounded route must include:

```sh
python3 scripts/query_corpus.py --route instant_orientation
python3 scripts/query_corpus.py --route erdos249_certificate_story
python3 scripts/query_corpus.py --route erdos257_half_story
python3 scripts/query_corpus.py --route browse_claim_status
```

If free text returns no semantic cells, use those stable routes; do not replace
machine evidence with manuscript-only inference. All eight indexed problems
remain open.

### Lean proof work or source mutation

Start from a typed mathematical handle, then cross into source:

```sh
python3 scripts/query_corpus.py --goal-support "<Lean or mathematical goal>"
python3 scripts/query_corpus.py --proof-plan "<Lean or mathematical goal>" --depth 4
```

Use the emitted declarations and verify applicability with Lean. Before editing,
read [AGENTS.md](AGENTS.md) sections `Authority and change order` and
`Validation`, and [METHODOLOGY.md](METHODOLOGY.md) when a public claim could
change.

### Repository architecture, agent entry, cold-clone organization, or docs routing

Route first; if selected, open
[the infrastructure skill](skills/maintain-public-infrastructure/SKILL.md):

```sh
python3 scripts/agent_entry.py --entry "<task in ordinary language>"
```

Then run the bounded checks:

```sh
python3 scripts/proof_cockpit.py --format card
python3 scripts/test_compact_agent_entry.py
python3 scripts/check_cold_clone_comprehension.py --quick
```

Open [ARCHITECTURE.md](ARCHITECTURE.md) or [orientation](docs/ORIENTATION.md)
only when routed; builders own generated projections.

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

`comparator_assurance` reports the comparison packet, modules, axioms, and
receipt; it does not establish novelty, significance, priority, or peer
review. `palomar_qualification` reports repository-local policy readiness
and its remaining operator-only decisions; it does not confer acceptance,
registration, publication, or external endorsement.

`--ask` answers ordinary requests such as “which papers should I read?”, keeps
the gateway, companion, systems guide and Plectis route apart, and refuses to
send a cold reader into a registered artifact absent from the checkout. After
choosing a paper, follow its typed claim, open, declaration, source, or
publication handles; prose is not authority. `docs/papers/README.md` is the
human index and `docs/papers/corpus.json` the machine inventory.

For publication mutation, open `docs/publication_entry_packet.json`, then the
publication contract or emitted handle. These own organisation, not Lean proof.

### Explain, install, mine, validate, propagate, or add a problem

Do not guess from filenames. Run `python3 scripts/agent_entry.py --skills`, or
route with `--entry`, before opening one `skills/<id>/SKILL.md`. The mining
skill may coordinate subagents; the integrating agent verifies every return.
After a stable delta, propagation gives each plausible downstream consumer a
disposition before packaging. Submission may commit locally; it pushes or opens
a pull request only after explicit authorisation.

### Return research from a clone

For contributed or resumable work, load:

```sh
cat skills/erdos-research-return/SKILL.md
```

Keep the human account in the pull request or plain-language issue. Bind public
provenance and exact credit in the returned package. Never require a private
repository.

An older clone is still a valid source. Preserve its recorded starting commit
and original delta, reconcile with current main, then rerun validation and
propagation. A material conflict resolution is a separately credited change.

### General Plectis machinery

The companion [`plectis`](https://github.com/wcook04/plectis) repository owns
the runnable machinery; this one owns the public mathematical corpus. Neither
repository's authority follows from the other, and no command above needs the
companion checkout.

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
- For Lean edits, run `python3 scripts/lean_fast_build.py --jobs 2
  --changed-from HEAD`; never overlap builds.

## Validation

Use the smallest relevant proof first:

```sh
python3 scripts/test_compact_agent_entry.py
python3 scripts/test_proof_cockpit.py
python3 scripts/check_cold_clone_comprehension.py --quick
python3 scripts/check_architecture_guide.py
```

For a committed-snapshot release check in a dirty shared checkout:

```sh
python3 scripts/check_release_ref.py --ref HEAD --receipt .validation-singleflight/release-head.json
```

After Lean edits, run `python3 scripts/lean_fast_build.py --jobs 2
--changed-from HEAD`; full roots are release-only.

Do not absorb the complete deep contract, declaration atlas, module graph, or
the papers merely to find the first action.
