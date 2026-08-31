<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Plectis Lean: eight open Erdős problems

This repository studies Erdős Problems 68, 243, 249, 251, 257, 269, 1041,
and 1049 in Lean. It contains formalised theorems from the literature, new
checked reductions and obstructions, finite certificates, countermodels, and
eight problem-specific mathematical papers.

**All eight problems remain open.** A formal reduction is not a solution, and
a large finite computation does not change an infinite quantifier.

## Start here

If you are arriving as a reader, begin with
[A reader's way in](HUMAN_ENTRY.md). It explains what the project is trying
to do, what the formal work can and cannot tell you, and how to choose a
mathematical thread without first learning the repository's internal
machinery.

The [results and open boundaries](docs/RESULTS.md) give a fuller mathematical
account. The papers below are the main reading objects, and the
[scope](SCOPE.md) and [prior-art guide](docs/PRIOR_ART.md) explain the limits
and attribution around them. Readers who want to trace a claim into Lean can
use the [source map](docs/SOURCE_MAP.md) and
[verification dossier](docs/EXTERNAL_VERIFICATION.md).

If you want to contribute, the [human contributor guide](CONTRIBUTING.md)
explains how work from a clone comes back with provenance and credit. To
understand how the repository is organised, continue to the
[documentation guide](docs/README.md) and
[architecture and repository guide](ARCHITECTURE.md). Coding agents have a separate
[compact entry](AGENTS.override.md) and
[workbench](docs/AGENT_WORKBENCH.md); those operational surfaces are not the
human introduction.

## What is here

The strongest completed results concern restricted forms of Problem 257. The
library checks the classical full-support irrationality theorem for every
integer base `b ≥ 2`, a pairwise-coprime support theorem under explicit
summability hypotheses, and an irrationality theorem for nonnegative rational
eventually-periodic coefficients with a positive periodic tail. It also proves
global topological and measure statements for Mersenne achievement sets.
Universal Problem 257, which quantifies over every infinite support, remains
open.

The sharpest current open socket for Problem 1041 is geometric rather than
computational: on the ray-separated locus, prove that some admissible critical
hub has total spoke length at most `2`, then pass to the boundary by lower
semicontinuity. Its degree-five `SPOKE-5` instance would settle that degree.
Neither statement is proved; the Lean library supplies local ray separation
and root retention, not the missing global hub selection and path containment.

For Problem 249, the library gives exact finite-level structure for the
dyadic sections of Euler's totient and several routes that would imply
irrationality if their stated cofinal hypotheses were proved. Those hypotheses
remain open. The repository also records why several tempting finite-state or
fixed-precision arguments cannot close the problem.

The other six programmes isolate similarly precise boundaries: a carry
characterisation for Problem 68; conditional recovery criteria for Problem
243; a prime-gap reformulation and tail criteria for Problem 251; running-LCM
cell and carry structure for Problem 269; local Newton-flow and root-retention
results for Problem 1041; and a growing-rank four-jet collision kernel plus
explicit Padé-model obstructions for Problem 1049. The #1049 kernel produces
finite selector collisions under its rank inequality, not approximating
polynomials, nonzero remainders, or an irrationality theorem. Each paper states
what has been checked and what still prevents an endpoint theorem.

The public order of mathematical attention comes from the canonical
[Palomar result showcase](docs/PALOMAR_RESULT_SHOWCASE.json), joined to exact
claim boundaries in [the claim registry](docs/claims.json). File order,
problem number, theorem count, and the table below are not independent
rankings.

## The eight problem papers

These papers are the main mathematical reading objects. Each is available as
a PDF and as navigable Markdown. Specialist companion papers and repository
systems papers are listed separately in the [complete paper index](docs/papers/README.md).

| Problem | Mathematical question | Paper |
|---|---|---|
| **68** | Is `∑_{n≥2} 1/(n!−1)` irrational? | [PDF](erdos-68-factorial-denominator-irrationality.pdf) · [full text](docs/papers/full-text/erdos-68-factorial-denominator-irrationality.md) |
| **243** | Does rationality of a rapidly converging reciprocal sum force the Sylvester recurrence eventually? | [PDF](erdos-243-reciprocal-tail-rigidity.pdf) · [full text](docs/papers/full-text/erdos-243-reciprocal-tail-rigidity.md) |
| **249** | Is `∑_{n≥1} φ(n)/2ⁿ` irrational? | [PDF](erdos-249-binary-totient-series.pdf) · [full text](docs/papers/full-text/erdos-249-binary-totient-series.md) |
| **251** | Is the dyadic series formed from consecutive prime gaps irrational? | [PDF](erdos-251-prime-gap-dyadic-series.pdf) · [full text](docs/papers/full-text/erdos-251-prime-gap-dyadic-series.md) |
| **257** | Is `∑_{n∈A} 1/(2ⁿ−1)` irrational for every infinite support `A`? | [PDF](erdos-257-mersenne-support-subseries.pdf) · [full text](docs/papers/full-text/erdos-257-mersenne-support-subseries.md) |
| **269** | Is the reciprocal sum of running least common multiples irrational for three or more primes? | [PDF](erdos-269-three-prime-running-lcm.pdf) · [full text](docs/papers/full-text/erdos-269-three-prime-running-lcm.md) |
| **1041** | Can two roots in the unit disc be joined by a curve of length less than `2` inside the open lemniscate? | [PDF](erdos-1041-lemniscate-newton-flow.pdf) · [full text](docs/papers/full-text/erdos-1041-lemniscate-newton-flow.md) |
| **1049** | For which rational bases is the associated Lambert-type series irrational? | [PDF](erdos-1049-rational-base-lambert.pdf) · [full text](docs/papers/full-text/erdos-1049-rational-base-lambert.md) |

The eight papers are the canonical public starting point for the mathematics.
The combined [printable PDF](claim-faithful-publication-systems-paper.pdf)
is retained for archive and provenance; it is not a ninth mathematical
programme or a replacement for the individual papers. It assumes no Lean or
project history. The
[cold-clone navigation paper](cold-clone-to-proof-receipt.pdf) explains the
repository's verification design rather than asserting another mathematical
result.

## How a public claim is checked

The public verification route re-reads a recorded Lean declaration, reports
its assumptions, shows the separately configured Comparator statement, and
points to the paper and release receipt. The full-support example formalises
Erdős's 1948 theorem; it is not a novelty claim and does not prove universal
Problem 257. Exact commands and contribution procedures live in the
[agent workbench](docs/AGENT_WORKBENCH.md).

The evidence order is simple:

1. Lean source checked by the pinned kernel is formal proof authority.
2. `docs/claims.json` records the public statement, status, and exact open
   boundary.
3. Papers and human-facing pages explain the mathematics within that boundary.
4. Comparator checks configured statements, while Palomar orders candidates
   for possible review. Neither establishes novelty, significance, acceptance,
   or solution status.

The repository is self-contained: its public claims do not depend on a private
checkout, an agent's memory, or unreleased work. In particular, do not infer results from private or unreleased work. See the [methodology](METHODOLOGY.md)
for the complete claim discipline and [reproducibility guide](docs/REPRODUCIBILITY.md)
for build and release checks.
