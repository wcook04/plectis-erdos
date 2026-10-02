<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Agent instructions

Base repository status and instructions on this public checkout. Check primary
sources for mathematical and prior-art claims; do not depend on private files.
The [repository map](README.md#repository-map) explains the folders.

## Start with the task

Run commands from the repository root. Route the actual request:

```sh
python3 scripts/agent_entry.py --entry "<task in ordinary language>"
```

Open the returned `skills/<id>/SKILL.md` and smallest source set; follow local instructions.
`python3 scripts/agent_entry.py --skills` lists `skills/registry.json`.
Routes locate evidence; they do not prove it.

Entry reports revision and edits. For latest-work tasks, run
`python3 scripts/agent_entry.py --checkout --check-upstream`. Record the starting
commit and preserve older work. [Setup and prompts](docs/agents/README.md#start-with-current-public-work).

## Read, investigate or choose a question

For mathematics and status:

```sh
python3 scripts/query_corpus.py --ask "<question>"
```

For corpus-wide questions, use
`python3 scripts/query_corpus.py --overview --format card` and follow its
`answer_contract`. Cover the requested programmes and exact open boundaries;
a flagship or theorem count does not stand for the corpus. If free text misses
the question, use `python3 scripts/query_corpus.py --routes` to find a stable route.

Follow returned claim, paper and source handles. For learning, respect the
requested depth: a hint request is not permission to reveal the proof or start
proof search. [Reading guidance](skills/explain-public-system/SKILL.md#help-a-reader-work-through-an-argument).

For research:

- **Find what is worth developing:** [explore the corpus](skills/explore-the-corpus/SKILL.md).
  Compare several papers and explain the selected direction.
- **Attack a stated question:** [mine an open problem](skills/mine-open-problem/SKILL.md).
  State hypotheses, obstruction and a decisive first test.
- **Continue sustained research:** [coupled research goals](skills/run-coupled-research-goals/SKILL.md)
  connects discovery with review and propagation.
- **Add a sourced problem:** [add an open problem](skills/add-open-problem/SKILL.md).
  Record its source and incubation status.

`python3 scripts/query_corpus.py --open` lists recorded questions; research
may also produce a new one.

For prior work, inspect [PRIOR_ART](docs/PRIOR_ART.md) and the selected paper's
references, then primary papers and original discussions. Cite the exact source,
edition and statement. Distinguish earlier work, formalisation, deduction and
conjecture. State search limits; agent agreement does not establish novelty.

[Experiments](research/README.md) and [exact computations](computations/README.md)
provide runnable examples. Preserve inputs, bounds, outputs and a recheck command.
A finite search establishes only its finite conclusion. [Returned research](research_corpus/README.md)
preserves dated investigations; check current status before relying on an old return.

If delegating, give subagents bounded questions and disjoint write scopes. The integrating
agent verifies their evidence and makes the final decisions.

## Work with Lean or reproduce a check

Start from the exact mathematical statement:

```sh
python3 scripts/query_corpus.py --goal-support "<Lean or mathematical goal>"
python3 scripts/query_corpus.py --proof-plan "<Lean or mathematical goal>" --depth 4
```

Verify applicability with Lean. Use the [proof-state guide](docs/agents/PROOF_STATE_COMPILER.md)
for an actual goal and [land Lean proofs](skills/land-lean-proofs/SKILL.md)
for its consumers. Before source edits, read the guide's
[change order](docs/agents/AGENT_GUIDE.md#authority-and-change-order) and
[validation](docs/agents/AGENT_GUIDE.md#validation).

[Reproducibility](docs/REPRODUCIBILITY.md) distinguishes checking a recorded
claim trail, rerunning a computation and compiling Lean. [Verification files](verification/README.md)
and [replay instructions](docs/verification/README.md) cover selected external
statements; [evidence](evidence/README.md) holds recorded outcomes.

## Write papers, check attribution or prepare publication

For paper roles and reading order, run `python3 scripts/query_corpus.py --papers`.
[Writing](skills/public-mathematical-writing/SKILL.md) governs exposition;
[propagation](skills/propagate-research-consequences/SKILL.md) updates affected
consumers. Preserve original-source and contributor credit. [CITATION.cff](CITATION.cff)
covers the repository; [paper records](docs/papers/README.md) identify editions.

For external assurance and release qualification:

```sh
python3 scripts/query_corpus.py --route comparator_assurance
python3 scripts/query_corpus.py --route palomar_qualification
```

`comparator_assurance` reports selected statements, axioms and receipts; it
does not establish novelty, significance, priority, or peer review.
`palomar_qualification` reports local readiness and remaining decisions; it
does not confer acceptance, registration, publication or endorsement.
For publication changes, open `docs/publication_entry_packet.json`, then its
emitted contract. This organises evidence; it does not prove a theorem.

## Improve tools, documentation or agent routes

Use [infrastructure maintenance](skills/maintain-public-infrastructure/SKILL.md)
and the [plain-language human guide](docs/ARCHITECTURE.md). [Repository tools](scripts/README.md)
map tasks to commands. Reproduce a bad route before changing its owner;
update affected links and checks. The [workbench](docs/agents/AGENT_WORKBENCH.md) holds details.
Use `python3 scripts/proof_cockpit.py --format card` for a compact evidence view.

## Authority and safe changes

1. Lean source checked by the pinned Lean kernel establishes the exact formal
   statement, under its assumptions.
2. `docs/claims.json` owns public claim identity, status and remaining-open
   propositions; it does not prove them.
3. `docs/methodology.json` owns evidence responsibilities and claim-change rules.
4. Generated maps and publication packets provide navigation.
5. Papers explain the arguments within their stated evidence boundaries.
6. Model output, plans and memory are working aids.

Use [METHODOLOGY](docs/METHODOLOGY.md) before changing public status.
A new file or a passing navigation check creates no theorem.

- Preserve unrelated staged and unstaged work. Do not reset, restore, clean or
  broad-stage a shared checkout.
- Edit source authorities before generated projections; run their owner builder.
- Never add `sorry`, `admit`, project-defined `axiom`, `native_decide`,
  unsafe/partial declarations or unbounded kernel limits.
- For Lean edits, use `python3 scripts/lean_fast_build.py --jobs 2 --changed-from HEAD`;
  coordinate builds through [Lean validation](skills/lean-concurrent-validation/SKILL.md).
  Never overlap builds. Full Lean roots are release-only.

## Validate and return the work

Run the focused checks for the change. Agent-entry work uses
`python3 scripts/test_compact_agent_entry.py`; documentation uses
`python3 scripts/check_cold_clone_comprehension.py --quick`.
The [validation guide](docs/agents/AGENT_GUIDE.md#validation) owns the full gate
and prerequisites. Do not rerun components after a full pass.

[CONTRIBUTING](CONTRIBUTING.md) accepts an ordinary issue or pull request.
Use [research returns](skills/erdos-research-return/SKILL.md) for resumable work.
Preserve the starting commit, delta, attribution, commands, outcomes and limits.
Credit material integration changes separately. Report unresolved work.

[Submission](skills/submit-pull-request/SKILL.md) owns scoped commits, release
admission and PR preparation. Follow task and standing authorisation; ask again
only for a concrete issue requiring a new decision. Respect local-only requests.

Do not absorb the complete deep contract merely to find the first action.
