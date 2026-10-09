<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Lean source

The formal development uses the Lean and Mathlib versions pinned at the
repository root. Begin with a [paper](../paper/README.md) or a claim in the
[source map](../docs/SOURCE_MAP.md), then follow its declaration into this
folder. A file's presence does not by itself mean the current build checks it.
[Results and limits](../docs/RESULTS.md) records what the public claims establish.

## The two libraries

| Location | Role |
|---|---|
| [ErdosProblems.lean](ErdosProblems.lean) | Main import root for the programme library. |
| [ErdosProblems/](ErdosProblems/) | Developments grouped by problem, plus shared mathematics, synthesis and recorded argument relationships. |
| [Erdos249257.lean](Erdos249257.lean) | Import root for the original #249/#257 library. |
| [Erdos249257/](Erdos249257/) | Earlier developments and certificate families used by subsequent work. The name is retained in imports and citations. |

The eight programme folders are [#68](ErdosProblems/Erdos68/),
[#243](ErdosProblems/Erdos243/), [#249](ErdosProblems/Erdos249/),
[#251](ErdosProblems/Erdos251/), [#257](ErdosProblems/Erdos257/),
[#269](ErdosProblems/Erdos269/), [#1041](ErdosProblems/Erdos1041/) and
[#1049](ErdosProblems/Erdos1049/). [Shared/](ErdosProblems/Shared/) and
[Synthesis/](ErdosProblems/Synthesis/) hold work used across problems.
Versioned development folders preserve the organization of particular
arguments; their names do not establish a result's current status.

## Find and check a statement

[Reproducibility](../docs/REPRODUCIBILITY.md) gives installation, dependency
and build commands. [The source map](../docs/SOURCE_MAP.md) connects all eight
programmes to paper passages and declarations. The
[agent workbench](../docs/agents/AGENT_WORKBENCH.md) gives precise claim,
declaration and dependency queries; agents begin at [AGENTS.md](../AGENTS.md).

Generated certificate shards record many individual arithmetic checks.
Their number is not the number of mathematical contributions. Their manifests
and builders own regeneration. Keep generated families and their import roots
together; do not rename modules or rearrange namespaces without updating
imports, Lake, paper links, evidence records and generated indexes.

Selected external statement interfaces live in [verification/](../verification/README.md).
Experiments and downstream examples live in [research/](../research/README.md).
The [architecture guide](../docs/ARCHITECTURE.md) explains those boundaries.
