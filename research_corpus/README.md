<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Returned research records

This directory preserves research returns and their source files so another
researcher can inspect the arguments, corrections and unresolved obligations.
These records have their own dates and evidence boundaries. Their presence in
the checkout does not give every statement the status of a published claim or
every Lean file the status of a checked proof.

The original [#1041 agent instructions](Erdos1041/AGENTS.md.txt) are retained as
an archival text file. Use the current root [AGENTS.md](../AGENTS.md) for work
in this public checkout.

| Collection | Start here | Then inspect |
|---|---|---|
| Erdős #1041 | [Frontier and corrections](Erdos1041/FRONTIER.md) | [Result records](Erdos1041/STRONGEST_RESULTS.json), the [file manifest](Erdos1041/CORPUS_MANIFEST.json), and the [export checkpoint](Erdos1041/PUBLIC_CORPUS_CHECKPOINT.json). |
| Erdős #1049 | [Research notes and formal-status boundary](Erdos1049/README.md) | The named arguments, source audit and remaining approximation problem. |

For a result's public wording and current status, return to
[Results and limits](../docs/RESULTS.md) and the [claim records](../docs/claims.json).
The [papers](../paper/README.md) explain the accepted arguments and their sources.
The [research-record guide](../docs/reference/RESEARCH_RECORD.md) explains how
returns and corrections are reconciled.

For runnable experiments and small examples, use [research/](../research/README.md).
Preserve each returned packet's recorded source version when proposing a
correction. Update generated manifests and frontier summaries through their
owning tools rather than editing them by hand.
