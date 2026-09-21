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

For a new workspace, use Git and Python 3:

```sh
git clone --filter=blob:none --branch main https://github.com/wcook04/plectis-erdos.git
cd plectis-erdos
python3 scripts/agent_entry.py --checkout --check-upstream
python3 scripts/agent_entry.py --entry "explain how this repo works to a newcomer"
```

The version check reads public `main` without fetching or changing your files.
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

Start with one of these tasks. The first two are the two ways to begin research:
with a listed question, or with the mathematics itself.

| Task to give your agent | Useful result |
|---|---|
| Show me the open questions and help me choose one | The list from `python3 scripts/query_corpus.py --open`, one chosen row, and the checked results that bear on it |
| Read the corpus and decide what is worth developing | A direction stated early with its reason, the sources it rests on, what was proved, computed or conjectured, the prior work found, and the next question. [One investigation](../../research/experiments/choices_contraction/README.md) shows the shape |
| Explain how this repo works to a newcomer | A source-linked map and one relevant next action |
| Independently reproduce the checked claim `eb_full_support` | Verifier output, checkout commit, assumptions and remaining open boundary |
| Improve cold clone navigation | One reproduced failure, a focused repair and the corresponding regression check |
| Package the work from my old checkout for maintainers | A contribution with the original starting commit and replay evidence |

For the reproduction task, run `python3 scripts/verify_claims.py --claim
eb_full_support`. This checks the recorded claim trail; it does not elaborate
Lean. For proof, computation, or paper work, let the task router choose the
workflow and its stronger validation. [CONTRIBUTING](../../CONTRIBUTING.md)
explains how to return work and receive credit. An agent's successful run does
not itself establish a new mathematical result.

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
