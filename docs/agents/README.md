<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Working with a coding agent

Start a research session from [AGENTS.md](../../AGENTS.md). It routes the task
to the relevant skill and a small set of files. If you are deciding what to
work on, the [research-shift guide](../FRONTIER_RELAY.md) explains how to choose
a question, record what happened and return the work.

These guides are for the next step, once you have a problem, statement or tool
to inspect.

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
