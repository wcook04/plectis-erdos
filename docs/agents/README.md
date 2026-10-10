<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Working with a coding agent

Start a research session from [AGENTS.md](../../AGENTS.md). It routes the task
to the relevant skill and a small set of files. If you are deciding what to
work on, the [research-shift guide](../FRONTIER_RELAY.md) explains how to choose
a question, record what happened and return the work.

These guides are for the next step, once you have a problem, statement or tool
to inspect. Without a clone, give your model the
[reading edition](../reading-edition/README.md); it carries the same research
instruction as the clone.

## Start with current public work

Use a coding agent that can read local files and run terminal commands. Its
provider does not matter; the shared entry is the root `AGENTS.md`. No plugin,
private checkout, model API key or Lean installation is needed to route a task.
Proof work later uses the toolchain described by its selected skill.

For a new workspace, use Git and Python 3.11 or later for navigation. Check
which version your `python3` command selects before running the commands below:

```sh
python3 -c 'import sys; print(sys.version); sys.exit(0 if sys.version_info >= (3, 11) else "Python 3.11 or later is required; select a supported interpreter.")'
```

If it reports an older version, install Python 3.11 or later, or select a
supported interpreter already installed. For example, check `python3.12 --version`
and replace `python3` with `python3.12` in the commands below if that interpreter
is available. You can also use the absolute path to your supported Python
executable. Use that same interpreter for the route and its returned commands.

The [full release check](../REPRODUCIBILITY.md#3-run-the-release-surface-checks)
separately uses Python 3.12 and Elan to prepare dependencies and its live Lean
pilot; navigation needs no Lean installation.

Then clone and route the task:

```sh
git clone --filter=blob:none --branch main https://github.com/wcook04/plectis-erdos.git
cd plectis-erdos
python3 scripts/agent_entry.py --checkout --check-upstream
python3 scripts/agent_entry.py --entry "Can you explain when the weighted criterion applies and help me change a hypothesis?"
```

The checkout comparison reads public `main` without fetching or changing your files.
It distinguishes an equal commit, a different commit, and an unavailable
comparison, and reports local modifications separately. An offline task still
works; omit `--check-upstream`. Matching `main` is an observation at check time,
not a promise that no new commit will appear. Record the starting commit.

If you already have a clone with work in it, keep it. Compare its revision first;
do not reset or overwrite it to obtain newer material. A separate clone in a
new directory gives you current public work while preserving the old delta.
For a historical reproduction, check out the requested tag explicitly.
[Issue #106](https://github.com/wcook04/plectis-erdos/issues/106) reproduces a
frozen edition; [#105](https://github.com/wcook04/plectis-erdos/issues/105)
introduces research frontiers. This checkout's router and source files describe
the capabilities actually available to your agent.

Give the agent this prompt, replacing the bracketed task:

> Read the root AGENTS.md. My task is [a concrete question or change, or: read
> the corpus and decide what is worth developing]. Route it
> with scripts/agent_entry.py and follow the selected skill. Record the checkout
> commit and local modifications; check public main if I asked for latest work.
> Read the smallest relevant source set, do the task, and run its relevant
> checks. Return the source paths, result, exact commands and outcomes, and any
> remaining assumptions or unresolved step. Preserve unrelated work. Prepare
> proposed contributions using this repository's contribution workflow.

Start with a task below. For research, you can begin with a listed question
or with the mathematics itself. For learning, specify how much help you want.

| Task to give your agent | Useful result |
|---|---|
| Help me work through the #257 weighted theorem, one hint at a time | The named statement and one hint matched to your background, followed by space for your attempt. [Reading guidance](../READING_GUIDE.md#work-through-an-argument) |
| Show me the open questions and help me choose one | The list from `python3 scripts/query_corpus.py --open`, one chosen row, and the checked results that bear on it |
| Read the corpus and decide what is worth developing | A direction stated early with its reason, the sources it rests on, what was proved, computed or conjectured, the prior work found, and the next question. [One investigation](../../research/experiments/choices_contraction/README.md) shows the shape |
| Explain how this repo works to a newcomer | A source-linked map and one relevant next action |
| Check the claim records for `eb_full_support` | Record-check output, checkout commit, assumptions and remaining open boundary; no Lean compilation |
| Improve cold clone navigation | One reproduced failure, a focused repair and the corresponding regression check |
| Package the work from my old checkout for maintainers | A contribution with the original starting commit and replay evidence |

For the record-checking task, run `python3 scripts/verify_claims.py --claim
eb_full_support`. This checks the recorded claim trail; it does not elaborate
Lean. For proof, computation, or paper work, let the task router choose the
workflow and its stronger validation. [CONTRIBUTING](../../CONTRIBUTING.md)
explains how to return work and receive credit. An agent's successful run does
not itself establish a new mathematical result.

## Continue or hand over a conversation

The [portable prompts](prompts/README.md) cover incorporating new material,
continuing from an existing conversation, and compacting context for a restart.
They are the short versions used alongside the Agent Trace demonstration.

## Apply a result to a changed example

Start with the [small weighted #257 task packet](../reading-edition/weighted-257-task.md).
It works without a clone; save the [raw text](https://raw.githubusercontent.com/wcook04/plectis-erdos/main/docs/reading-edition/weighted-257-task.md)
for offline reading. Choose one hint, a second hint, or the full worked answer.

> Help me apply the weighted #257 criterion to $A(c,p)$ in the task packet.
> Decide the three cases $c=2,p=1,b=2$; $c=2,p=1,b=3$; and $c=2,p=2$
> at every integer base at least two. Give me one hint first and stop.
> When I ask for the answer, state the failed or satisfied hypothesis,
> exact source and open boundary. Distinguish the Lean-checked criterion
> from the ordinary deduction for this family.

For an agent started elsewhere, see the [portable companion](PORTABLE_COMPANION.md)
for the directory skill package, supported installation routes and observed client limits.

With a clone, use Git and Python 3.11 or later; Lean is needed only for proof compilation.
After setup, route the actual task:

```sh
python3 scripts/agent_entry.py --entry "Can you explain when the weighted criterion applies and help me change a hypothesis?"
python3 scripts/research_query.py get claim finite_prime_weighted_support
python3 scripts/query_corpus.py --open remaining_open.universal_257_all_infinite_supports --format json
```

Read the task packet and selected sources, then do the mathematical task.
Printing a query response alone does not answer it. `verify_claims.py` checks
recorded source relationships; it does not compile a proof. The Lean build
instructions in [reproducibility](../REPRODUCIBILITY.md) cover proof execution.

### Observe an outside attempt

For a willing reader, use the same packet and chosen learning depth. Record
edition fingerprint, environment, selected case, requested hints, interventions,
answer and source locations. Assess whether the answer respects all hypotheses,
withholds an arithmetic verdict when the test fails, distinguishes the ordinary
deduction from the formal criterion, and identifies the unresolved universal
claim. Ask the reader for one related question of their own; record time and
obstacles when they agree. Return observations or corrections through
[Contributing](../../CONTRIBUTING.md), preserving attribution and any limits.
This is an attempt protocol; it records no participants or measured outcomes.

## Find the tool for the job

| Your next step | Guide | What you get |
|---|---|---|
| Find a claim, source declaration, paper passage or check | [Agent workbench](AGENT_WORKBENCH.md) | Commands grouped by the question they answer. |
| Inspect the evidence before choosing a task | [Proof cockpit](PROOF_COCKPIT.md) | A compact view of the current records and routes into the details. |
| Work from an actual Lean goal | [Proof-state compiler](PROOF_STATE_COMPILER.md) | The proof context, relevant source and available follow-up tools. |
| Understand how statements and relationships are indexed | [Semantic compiler](SEMANTIC_COMPILER.md) | The query layer and the source records behind it. |
| Change source, claims or public wording | [Agent guide](AGENT_GUIDE.md) | Authority, change order, validation and contribution rules. |
| Offer research sessions through a community or hosted service | [Frontier distribution](FRONTIER_DISTRIBUTION.md) | Setup and distribution instructions. |

## Make and return a change

Read [Contributing](../../CONTRIBUTING.md) before preparing a return. It accepts
an ordinary issue or pull request; a structured research package is useful
when another session needs to resume your investigation. The
[research commons](../research-commons/README.md) explains how provenance,
review and credit stay with the returned work.

Use [reproducibility](../REPRODUCIBILITY.md) for the clone and proof-build
instructions, and the [agent guide](AGENT_GUIDE.md) for checks specific to the
kind of change. Run the relevant tool's own tests as well. Keep mathematical
judgement with the researcher: a query result helps locate evidence, while
Lean checks the exact formal proof submitted to it.

For the design behind these tools, read [the architecture guide](../ARCHITECTURE.md)
or the [project papers](../../paper/README.md#project-papers).
For the mathematics, return to [the problem papers](../../paper/README.md#problem-papers).
[All documentation](../README.md).

The [compact query contract](RESEARCH_QUERY.md) describes source snapshots, structured errors, bounded reading and the four read-only operations.
