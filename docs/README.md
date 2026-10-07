<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Reading and working with the research

This repository studies eight Erdős problem programmes through papers, Lean
proofs of selected statements, exact computations and records of approaches
that stopped. You do not need Lean to read the mathematics. This is a
self-contained public record: reading and checking its claims require no
private development system.

Start with the [#257 paper](../paper/257/erdos-257-mersenne-support-subseries.pdf):
its finite-prime weighted criterion proves irrationality for some infinite
supports with divergent reciprocal sum; arbitrary infinite support remains
open. Then read [#1049](../paper/1049/erdos-1049-rational-base-lambert.pdf),
which formalises irrationality in a known rational-base region, or
[#1041](../paper/1041/erdos-1041-lemniscate-newton-flow.pdf), which examines
ani's degree-seven counterexample to the exact Formal Conjectures statement.
[Results and limits](RESULTS.md) states the checked conclusions and remaining
questions across all eight programmes.

## Choose a way in

| Your question | Guide |
|---|---|
| What has been established, and what remains open? | [Results and limits](RESULTS.md) |
| How do I inspect a claim, rerun a calculation or compile a proof? | [Reproducibility](REPRODUCIBILITY.md) |
| What evidence and review does a public claim require? | [Methodology and scope](METHODOLOGY.md) |
| How do proofs, papers, records and tools fit together? | [How the repository works](ARCHITECTURE.md) |
| Which earlier sources and contributors does the work rely on? | [Prior art and attribution](PRIOR_ART.md) |

## Work through an argument

Try a small example before reading the proof. Note where you get stuck, find
the step that overcomes that difficulty, then reconstruct it with the paper
closed. Change a hypothesis and see what breaks. If you use an agent, ask for
one hint at a time and wait for your attempt before revealing more. Name the
paper, statement and your background so you control the amount of help.

The [weighted-support exercise](research-commons/PROVE2ME_WEIGHTED_257_PACKET.md#try-changing-a-hypothesis)
and [runnable examples](../research/experiments/weighted_support_transfer/README.md)
give concrete starting points. A failed sufficient test proves nothing about
rationality. To read across the corpus, use the
[reading edition](reading-edition/README.md) or the
[synthesis paper](../paper/synthesis/optimal-sparse-perturbations.pdf).

## The eight problems

Each short paper states its question, results and main arguments. Its longer
record preserves technical detail, unsuccessful routes and surviving
obligations. The [paper catalogue](../paper/README.md) identifies both editions.

<!-- BEGIN problem_programme_card -->
[Problem 68](../paper/68/erdos-68-factorial-denominator-irrationality.pdf). Is the series sum_{n >= 2} 1/(n! - 1) irrational? [Work on this paper](research-commons/CONTRIBUTE_BY_PAPER.md#problem-68).

[Problem 243](../paper/243/erdos-243-reciprocal-tail-rigidity.pdf). Under a rapid-growth hypothesis on an integer sequence, does rationality of its reciprocal sum force the sequence to satisfy the Sylvester recurrence eventually? [Work on this paper](research-commons/CONTRIBUTE_BY_PAPER.md#problem-243).

[Problem 249](../paper/249/erdos-249-binary-totient-series.pdf). Is the binary Lambert series sum phi(n)/2^n irrational? [Work on this paper](research-commons/CONTRIBUTE_BY_PAPER.md#problem-249).

[Problem 251](../paper/251/erdos-251-prime-gap-dyadic-series.pdf). Is the dyadic series of consecutive primes irrational? Equivalently, is the corresponding consecutive-prime-gap dyadic series irrational? [Work on this paper](research-commons/CONTRIBUTE_BY_PAPER.md#problem-251).

[Problem 257](../paper/257/erdos-257-mersenne-support-subseries.pdf). Is the sum of 1/(2^n-1) over every infinite set of positive exponents irrational? [Work on this paper](research-commons/CONTRIBUTE_BY_PAPER.md#problem-257).

[Problem 269](../paper/269/erdos-269-three-prime-running-lcm.pdf). For a finite set of at least two primes, is the sum of reciprocals of the running least common multiples of the smooth numbers irrational? This library treats the three-prime case. [Work on this paper](research-commons/CONTRIBUTE_BY_PAPER.md#problem-269).

[Problem 1041](../paper/1041/erdos-1041-lemniscate-newton-flow.pdf). Must two roots of a monic polynomial in the open unit disc be joined by a sub-two-length curve inside its unit lemniscate? Ani’s degree-seven example refutes the exact Formal Conjectures statement; correspondence with the 1958 wording awaits human review. [Work on this paper](research-commons/CONTRIBUTE_BY_PAPER.md#problem-1041).

[Problem 1049](../paper/1049/erdos-1049-rational-base-lambert.pdf). For which rational bases is the corresponding series irrational? The first resistant explicit base is three halves. [Work on this paper](research-commons/CONTRIBUTE_BY_PAPER.md#problem-1049).
<!-- END problem_programme_card -->

## Read the evidence

Lean checks precise statements under their assumptions. It does not establish
novelty, importance or faithful correspondence with a historical question.
The verification concordance at the end of each paper links statements to
proofs and recorded checks; named assumptions, pending support and partial
coverage remain explicit. A finite computation covers its tested range.

The [source map](reference/SOURCE_MAP.md) locates evidence, and
[claim records](claims.json) own selected public wording and status.
[External verification](EXTERNAL_VERIFICATION.md) describes the
selected Comparator interfaces. Comparator is a statement and axiom-budget
check; it is not peer review. The
[Palomar guide](verification/PALOMAR_QUALIFICATION.md) separates local packaging
from recorded service decisions.

## Contribute

AI tools did much of the research, code and drafting under Will Cook's
direction. Will is responsible for the claims, sources and release; independent
human mathematical review has not been recorded.

Corrections, explanations, counterexamples and earlier references are welcome.
An insight can be useful before it has a formal proof. The
[contributor guide](../CONTRIBUTING.md) explains how to return evidence and
preserve credit; [work on a paper](research-commons/CONTRIBUTE_BY_PAPER.md)
connects each programme to its recorded questions. Clearer understanding,
reusable methods and new questions count as contributions too.

For AI-assisted research, start from [AGENTS.md](../AGENTS.md) and the
[research-shift guide](agents/FRONTIER_RELAY.md). The
[research commons](research-commons/README.md) records contribution, review and
credit responsibilities.

## Specialist guides and records

| Location | What it contains |
|---|---|
| [Agent guides](agents/README.md) | Query and proof tools, including the [argument graph](agents/ARGUMENT_GRAPH.md). |
| [Verification guides](verification/README.md) | Statement comparisons, replay and submission requirements. |
| [Technical reference](reference/README.md) | [Orientation](reference/ORIENTATION.md), the [argument frontier](reference/ARGUMENT_FRONTIER.md), [related problems](reference/RELATED_PROBLEMS.md), and dated research records. |
| [Paper full text](papers/README.md) | Generated Markdown editions and the detailed inventory. |
| [Semantic index](semantic/README.md) | Recorded relationships between formal statements. |

[Privacy](PRIVACY.md) and [third-party notices](THIRD_PARTY_NOTICES.md) describe
contribution data and source-artifact boundaries. The
[repository map](../README.md#repository-map) identifies proof libraries,
manuscripts and working records; [naming conventions](ARCHITECTURE.md#directory-and-naming-conventions)
explain similarly named folders.
