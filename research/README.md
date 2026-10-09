<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Experiments and investigations

Runnable experiments, downstream Lean examples and records of research sessions
live here. Each experiment's guide states its inputs, checks and limits. For the
current mathematical conclusions, use [Results and limits](../docs/RESULTS.md)
and the [papers](../paper/README.md).

## Run or vary an example

| Investigation | What you can inspect |
|---|---|
| [Exact-rational subsum probe](experiments/choices_contraction/README.md) | A Python-only exclusion test you can vary, with exact fractions and a separately checkable witness. |
| [Weighted support transfer](experiments/weighted_support_transfer/README.md) | Examples and hypothesis tests around the #257 weighted-support criterion. |
| [Changing a premise](experiments/premise_exchange/README.md) | Experiments with transferring a proof to a related statement. |
| [Prime-gap computations](experiments/erdos251/README.md) | The #251 computations, saved outputs and reproduction commands. |
| [Sparse interpolation](experiments/sparse_interpolation/README.md) | Exact checks and counterexamples used in the cross-problem investigation. |
| [Complete experiment index](experiments/README.md) | Further investigations grouped by problem or method. |

A finite experiment establishes only its stated finite result. In particular,
survival through a finite subsum search does not prove membership in the
infinite sum set. Read the example's interpretation before extending its range.

## Other research files

| Location | Role |
|---|---|
| [examples/](examples/Examples.lean) | A downstream Lean consumer of the library; setup is in [Reproducibility](../docs/REPRODUCIBILITY.md#use-the-library-in-another-lean-project). |
| [adapters/](adapters/) | Lean bridges to selected Formal Conjectures statements. |
| [probes/](probes/) | Bounded Lean investigations and checks from recorded research rounds. |
| [workbench/](workbench/) | Session records, probe files and replay evidence. |
| [Erdos243V5/](Erdos243V5/) and [residualbench/](residualbench/) | Additional development and validation modules; inclusion here alone is not evidence of a checked build. |

The separate [research_corpus/](../research_corpus/README.md) directory preserves
dated returned research packets. [Contributing](../CONTRIBUTING.md) explains
how to return a result, correction or useful failed approach with evidence and
credit. Coding agents begin at [AGENTS.md](../AGENTS.md).
