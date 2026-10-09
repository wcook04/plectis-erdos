<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Agent instructions

Start here when acting on this checkout. [README.md](README.md) introduces the
research to human readers. The [agent guide](docs/agents/AGENT_GUIDE.md) owns
authority, change order and validation; open only the section your task needs.

This is a self-contained public Lean repository. Use tracked public files;
do not depend on sibling repositories, private caches or unpublished state.

## Route the task

From the repository root:

```sh
python3 scripts/agent_entry.py --entry "<task in ordinary language>"
```

The router returns a task lane, its smallest read set and the relevant
`skills/<id>/SKILL.md`. `python3 scripts/agent_entry.py --skills` lists all
workflows. Follow the selected workflow before making changes. Routing
metadata helps navigation; it is not mathematical authority.

For latest-work tasks, run
`python3 scripts/agent_entry.py --checkout --check-upstream`. Record the
revision and preserve older work. The [agent quickstart](docs/agents/README.md#start-with-current-public-work)
explains setup, provenance and prompts.

## Find the mathematical evidence

For mathematics, theorem status, progress or paper synthesis, query before
reading broad papers or Lean files:

```sh
python3 scripts/query_corpus.py --ask "<question>"
python3 scripts/query_corpus.py --overview --format card
```

Use the overview for whole-corpus coverage. Follow its `answer_contract` and
returned claim, remaining-open, declaration, module and paper handles. Keep
hypotheses and exact open boundaries attached to each result. Never infer
progress from theorem counts or one flagship example.

For a corpus-wide progress review, include these stable routes:

```sh
python3 scripts/query_corpus.py --route instant_orientation
python3 scripts/query_corpus.py --route erdos249_certificate_story
python3 scripts/query_corpus.py --route erdos257_half_story
python3 scripts/query_corpus.py --route browse_claim_status
```

If free text returns no semantic cells, use `python3 scripts/query_corpus.py --routes`
and the applicable stable route. Select open work with
`python3 scripts/query_corpus.py --open`. Lean refutes the exact Formal
Conjectures #1041 path-image claim; correspondence with the 1958 wording remains
unreviewed.

For learning, respect the requested depth: a hint request does not authorise
revealing the proof or starting proof search. Follow the
[reading guidance](skills/explain-public-system/SKILL.md#help-a-reader-work-through-an-argument).
For prior work, read [PRIOR_ART.md](docs/PRIOR_ART.md), the paper's references
and primary sources. Distinguish discovery, formalisation and reuse; model
agreement does not establish novelty. Keep finite experiments attached to
their inputs, bounds and recheck commands.

### Proof work

Start from a typed mathematical handle, then cross into source:

```sh
python3 scripts/query_corpus.py --goal-support "<Lean or mathematical goal>"
python3 scripts/query_corpus.py --proof-plan "<Lean or mathematical goal>" --depth 4
```

Verify returned declarations and hypotheses with Lean. Before editing, read
`Authority and change order` and `Validation` in the
[agent guide](docs/agents/AGENT_GUIDE.md). Read
[METHODOLOGY.md](docs/METHODOLOGY.md) if public claim wording or status could
change. [The Lean guide](lean/README.md) explains the two source libraries.

### Papers and publication

For paper choice, role, availability or reading order:

```sh
python3 scripts/query_corpus.py --papers
```

[The paper index](docs/papers/README.md) is a navigation projection;
`docs/papers/corpus.json` owns its machine inventory. After choosing a paper,
follow its typed claim and source handles. The human reading catalogue is
[paper/README.md](paper/README.md).

For publication mutation, open `docs/publication_entry_packet.json` and its
emitted contract. Run [public mathematical writing](skills/public-mathematical-writing/SKILL.md),
then [consequence propagation](skills/propagate-research-consequences/SKILL.md)
to reconcile companions, consumers and public guidance.

For selected external checks:

```sh
python3 scripts/query_corpus.py --route comparator_assurance
python3 scripts/query_corpus.py --route palomar_qualification
```

Comparator reports configured statement, axiom and kernel checks; it
does not establish novelty, significance, priority, or peer review.
Qualification reports repository-local policy readiness and operator-only
decisions; it does not confer acceptance, registration, publication or endorsement.

## Maintain the repository

For architecture, README, folder organization or agent routing, follow
[maintain-public-infrastructure](skills/maintain-public-infrastructure/SKILL.md).
[ARCHITECTURE.md](docs/ARCHITECTURE.md) explains folder ownership;
[orientation](docs/ORIENTATION.md) provides generated navigation.

Use the bounded checks selected for the change:

```sh
python3 scripts/proof_cockpit.py --format card
python3 scripts/test_compact_agent_entry.py
python3 scripts/check_cold_clone_comprehension.py --quick
python3 scripts/check_architecture_guide.py
```

Builders own generated files and marked regions. Change the source authority
first and use the named builder/checker. Keep preserved research returns and
immutable source citations attached to their recorded revisions.

## Authority and mutation

1. Lean source checked by the pinned Lean kernel is proof authority.
2. `docs/claims.json` owns public claim identity, status, declarations and exact
   remaining-open propositions.
3. `docs/methodology.json` owns evidence responsibilities and claim-change rules.
4. Generated orientation, declaration, module and publication packets provide
   navigation, not new mathematical evidence.
5. Papers and human summaries explain work within the registered claim ceiling.
6. Model output, plans, memory and drafts are working aids only.

A paper edit cannot change a claim; a registry edit cannot prove a theorem;
a passing navigation check cannot establish mathematics.

- Preserve unrelated staged and unstaged work. Do not reset, restore, clean or
  broad-stage a shared checkout.
- Never add `sorry`, `admit`, project-defined `axiom`, `native_decide`,
  unsafe/partial declarations or unbounded kernel limits.
- For Lean edits, use `python3 scripts/lean_fast_build.py --jobs 2 --changed-from HEAD`.
  Never overlap builds. Full Lean roots are release-only.

## Validate and return the work

Use the changed owner's focused checks while editing. README changes need both
`python3 scripts/test_human_first_contact.py` and the cold-clone quick check:
they enforce different reading budgets. Before publication, follow the
[agent guide's validation contract](docs/agents/AGENT_GUIDE.md#validation),
including source freshness and the prepared release gate.

For a committed snapshot in a dirty shared checkout:

```sh
python3 scripts/check_release_ref.py --ref HEAD --receipt "$(pwd -P)/release-head.json"
```

Before packaging a stable change, give each plausible downstream consumer an
explicit disposition through the consequence-propagation skill. For contributed
or resumable research, read [erdos-research-return](skills/erdos-research-return/SKILL.md).
Preserve the starting commit, original delta, evidence and credit. Reconcile
older-clone work with current main; a material conflict resolution is a
separately credited change. Keep the human account in the issue or pull request.

Submission may commit locally. Pushing or opening a pull request requires
explicit authorisation. Never require a private repository to produce or
review a contribution.

Do not absorb the complete deep contract merely to find the first action.
