<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Repository tools

These programs inspect the mathematical corpus, build navigation records and
validate changes. Run documented commands from the repository root. The guides
below own the commands and prerequisites; running every script is neither a
setup step nor a proof check.

| Task | Guide | Main entry |
|---|---|---|
| Inspect a claim or reproduce an example | [Reproducibility](../docs/REPRODUCIBILITY.md) | [verify_claims.py](verify_claims.py) |
| Find a problem, result, paper or open question | [Agent workbench](../docs/agents/AGENT_WORKBENCH.md) | [query_corpus.py](query_corpus.py) |
| Route a task for a coding agent | [Agent quickstart](../docs/agents/README.md) | [agent_entry.py](agent_entry.py) |
| Build selected Lean modules | [Lean setup and builds](../docs/REPRODUCIBILITY.md#2-reproduce-the-pinned-lean-environment) | [lean_fast_build.py](lean_fast_build.py) |
| Check a documentation edit | [Documentation checks](../docs/REPRODUCIBILITY.md#check-a-documentation-change) | [check_cold_clone_comprehension.py](check_cold_clone_comprehension.py) |
| Refresh generated maps | [Architecture and authority](../docs/ARCHITECTURE.md#which-file-is-authoritative-for-what) | [refresh_projections.py](refresh_projections.py) |
| Validate a proposed release | [Release checks](../docs/REPRODUCIBILITY.md#3-run-the-release-surface-checks) | [check_release.py](check_release.py) |

By convention, `build_*.py` produce a named projection, `check_*.py` validate a
contract, and `test_*.py` exercise program behaviour. Read a tool's help and its
guide before running it: builders can write files, and some checks require Lean,
dependencies or commit history. Query output and passing documentation checks
are navigation evidence; they do not establish a mathematical theorem.

To improve these tools, follow the [infrastructure workflow](../skills/maintain-public-infrastructure/SKILL.md)
and [contribution guide](../CONTRIBUTING.md). Source authorities change before
their generated projections.
