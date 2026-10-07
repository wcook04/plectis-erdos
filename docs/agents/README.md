<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Working with a coding agent

## Start with current public work

Start with [AGENTS.md](../../AGENTS.md) and route your actual question through
`python3 scripts/agent_entry.py --entry "<task>"`. Follow the selected skill;
its task boundaries and validation determine what the agent should do.
[Reproducibility](../REPRODUCIBILITY.md) owns clone setup and proof execution.
No private checkout, plugin or model API key is required for repository routing.

## Apply a result to a changed example

The [weighted #257 task packet](../reading-edition/weighted-257-task.md) works
without a clone. Ask for one hint, a second hint or the worked answer, and
identify the exact failed or satisfied hypothesis. Its
[observation protocol](../reading-edition/weighted-257-task.md#observe-an-outside-attempt)
explains how to record a willing reader's attempt without claiming measured
outcomes. For broader reading without a clone, use the
[reading edition](../reading-edition/README.md).

### Observe an outside attempt

Follow the task packet's [observation protocol](../reading-edition/weighted-257-task.md#observe-an-outside-attempt)
to preserve the reader's consent, requested help, source identity and evidence limits.

## Find the tool for the job

| Your next step | Maintained guide |
|---|---|
| Find a claim, declaration, paper passage or check | [Agent workbench](AGENT_WORKBENCH.md) |
| Inspect the current evidence and routes | [Proof cockpit](AGENT_WORKBENCH.md#proof-cockpit) |
| Compile the context of an actual Lean goal | [Proof-state compiler](PROOF_STATE_COMPILER.md) |
| Query indexed statements, relationships and captured sources | [Semantic compiler](SEMANTIC_COMPILER.md), including the [compact query contract](SEMANTIC_COMPILER.md#compact-research-queries) |
| Trace an argument through dependencies | [Argument graph](ARGUMENT_GRAPH.md) |
| Change source, claims or public wording | [Agent guide](AGENT_GUIDE.md) |
| Choose bounded research and return a checkable result | [Research shift](FRONTIER_RELAY.md) |
| Install the companion from another workspace | [Portable companion](PORTABLE_COMPANION.md) |
| Offer a community or hosted research session | [Distribution runbook](FRONTIER_RELAY.md#distribution-and-community-operation) |

## Make and return a change

[Contributing](../../CONTRIBUTING.md) owns issues, pull requests, provenance and
credit; the [research commons](../research-commons/README.md) explains structured
returns. Follow the [agent guide](AGENT_GUIDE.md#validation) for the affected
owner's checks. Query and record-check outputs locate evidence; they do not
compile a proof or establish a new mathematical result.

Read [architecture](../ARCHITECTURE.md) for the tool design, the
[project papers](../../paper/README.md#project-papers) for its exposition, and
the [problem papers](../../paper/README.md#problem-papers) for mathematics.
[All documentation](../README.md).
