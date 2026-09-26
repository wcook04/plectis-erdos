<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Mathematics that emerges between the problems

[Reading Eight Erdős Problems Together](optimal-sparse-perturbations.pdf)
([source](optimal-sparse-perturbations.tex)) is the single cross-problem paper.
For `c>0` and integers `d≥1`, consider the set of vectors
`(f(1), f′(1), …, f^(d−1)(1))` from entire functions
`f(z) = ∑_(n≥1) e_n z^n/n!` with nonnegative integer `e_n` eventually at most
`n^c` and, for each fixed positive integer `q`, eventually divisible by `q`.
This set has Hausdorff dimension `min(c,d)` and contains an open set exactly when `c>d`; at
`c=d` they are full-dimensional but null and meagre. The paper also proves
a capacity and congruence criterion, Lambert-subsum results and method
limits. Its principal proofs are ordinary mathematical arguments; cited
formal ingredients retain their stated scope. This paper consolidates the former
synthesis note, working record and capacity account. Their earlier versions
remain in Git history.

The paper also proves that a chosen family of positive dyadic shifts detects
irrationality in every integer-digit recurrence, at any fixed threshold
`0<c<τ`, exactly when the family contains a multiple of every positive
integer. Factorial shifts work; power-of-two shifts fail on a rational orbit.
This is an ordinary proof using a cited sharp bound of Dubickas; the
[`1/3` transfer](../../lean/ErdosProblems/Synthesis/DyadicShiftEscape.lean)
is its Lean-checked starting point. Try the
[shift-family exercise](../../research/experiments/premise_exchange/shift_family_exercise.md)
before reading the proof.

The paper is a place for insights that arise while working with the full
corpus: connections between problems, reusable constructions, obstructions,
new intermediate objects and questions worth investigating. A contribution
can matter without settling one of the eight Erdős problems.

Begin with an example or question you understand. Follow a construction to
another setting, identify an assumption that prevents its reuse, or explain
why a tempting transfer fails. Compare it with existing work before deciding
whether it needs a new theorem, a corrected paper, an experiment or a simpler
explanation. An investigation may change direction. The useful outcome is the
insight and the evidence, not a required paper count.

The [admissible-choice experiment](../../research/experiments/sparse_interpolation/README.md)
is one executable starting point. Its [exact interval-cover calculation](../../research/experiments/sparse_interpolation/coverage.md)
shows how additional congruences can remove admissible remainders. This is an
elementary diagnostic with an ordinary proof and exact tests, not a claimed
new theory or a completed ninth-paper result.

When a substantial account is ready, use the existing
[paper-writing skill](../../skills/public-mathematical-writing/SKILL.md).
The short paper should carry the principal argument; the long record should
explain the technical work and useful failures. Results affecting a particular
problem also belong with that problem. Machinery belongs in the experiment or
systems account unless it produces a mathematical insight worth explaining.

[Return the work](../../CONTRIBUTING.md#return-what-you-learned) by GitHub or email,
with your preferred credit, the source edition, the idea, inspectable evidence
and the remaining question. Reading and ordinary proof are enough; a clone,
Lean installation or AI agent is optional. Agents use
[explore-the-corpus](../../skills/explore-the-corpus/SKILL.md) and a subject-based
research session when no single problem owns the work.
