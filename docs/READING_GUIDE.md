<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# A reader's way in

This repository follows eight problem programmes associated with Paul Erdős.
For each one it holds a short paper, a longer research record, Lean proofs of
selected statements, finite computations, and a written account of the
approaches that stopped and why. You do not need Lean to read the papers.

The degree-seven counterexample found by the erdosproblems.com contributor ani
refutes the total-variation formulation of Erdős #1041; this repository
formalises it in Lean. The other seven target problems are not resolved here. Independent human
review of correspondence with the historical curve-length formulation has not
been recorded. Comparator checks only its selected exact statements, configured
axioms and kernel acceptance; it does not assess novelty or historical
correspondence. The work also proves intermediate theorems, writes out proofs
of results that were stated but not printed in the literature, checks exact
finite cases, and records obstructions to tempting shortcuts.

## Two ways to begin

You can continue a particular question, or you can read the mathematics and
decide what comes next. Both are supported. The second treats the papers as one
body of work: a method from one problem may explain an obstruction in another,
a recorded example may suggest a general theorem, and a worthwhile new question
is itself a contribution. The [reading edition](reading-edition/README.md)
serves this route without a clone. It is one file to read or to give to an AI
model, with a short research instruction and the opening of each short paper.
[Choices, contraction and rational membership](../research/experiments/choices_contraction/README.md)
is one investigation that began this way.

## What is here

The [front page](../README.md) lists the eight problems with a short paper and
a longer paper for each. The short paper is the first read. The longer record
keeps failed routes, finite experiments, and the exact obligations that
survive. The [paper catalogue](../paper/README.md) groups the manuscripts and
their sources by problem, with three further papers on how the project is run.

The [results guide](RESULTS.md) states the strongest checked result for each
problem next to what still blocks its endpoint. [Prior work](PRIOR_ART.md)
records earlier arguments and attribution. [Scope](SCOPE.md) lists the claims
the project does not make. The [architecture guide](ARCHITECTURE.md) explains
the checks and generated indexes; it is not needed for the mathematics.

## What formalisation adds

Lean checks a precise statement against a precise proof. That forces
assumptions, quantifiers, and dependencies into the open. It does not decide
whether a theorem is new, important, or the right way to attack an open
problem, and it does not turn a conditional result into an unconditional one.
Many results here are ordinary mathematical arguments with no Lean proof; each
paper says which is which.

## The eight problems in brief

Choose a question below to open its short paper. The
[problem-by-problem results guide](RESULTS.md#problem-by-problem-guide) explains
the main arguments, their formalisation and the questions left open. Keeping
those assessments in one place avoids conflicting summaries.

<!-- BEGIN problem_programme_card -->
[Problem 68](../paper/68/erdos-68-factorial-denominator-irrationality.pdf). Is the series sum_{n >= 2} 1/(n! - 1) irrational?

[Problem 243](../paper/243/erdos-243-reciprocal-tail-rigidity.pdf). Under a rapid-growth hypothesis on an integer sequence, does rationality of its reciprocal sum force the sequence to satisfy the Sylvester recurrence eventually?

[Problem 249](../paper/249/erdos-249-binary-totient-series.pdf). Is the binary Lambert series sum phi(n)/2^n irrational?

[Problem 251](../paper/251/erdos-251-prime-gap-dyadic-series.pdf). Is the dyadic series of consecutive primes irrational? Equivalently, is the corresponding consecutive-prime-gap dyadic series irrational?

[Problem 257](../paper/257/erdos-257-mersenne-support-subseries.pdf). Is the sum of 1/(2^n-1) over every infinite set of positive exponents irrational?

[Problem 269](../paper/269/erdos-269-three-prime-running-lcm.pdf). For a finite set of at least two primes, is the sum of reciprocals of the running least common multiples of the smooth numbers irrational? This library treats the three-prime case.

[Problem 1041](../paper/1041/erdos-1041-lemniscate-newton-flow.pdf). For a monic polynomial whose roots lie in the open unit disc, must two roots be joinable by a curve of length less than two inside the open unit lemniscate? The registry has not adjudicated whether the checked total-variation formulation exactly matches this historical curve-length question.

[Problem 1049](../paper/1049/erdos-1049-rational-base-lambert.pdf). For which rational bases is the corresponding series irrational? The first resistant explicit base is three halves.
<!-- END problem_programme_card -->

If the comparison across the problems is what you are after rather than one of
them, read the [synthesis note](../paper/synthesis/erdos-synthesis-subsums-across-bases.pdf),
which proves which subsums of a Lambert series are rational or irrational as
the base varies. Its
[working record](../paper/synthesis/erdos-synthesis-reading-together-record.pdf)
holds the inventory of negative results, the ideas that were eliminated and the
questions left open.

## How to read the evidence

The project keeps kinds of evidence apart. A Lean proof tells you a formal
statement was checked. A claim record tells you how that statement may be
described in public and what remains open. A paper supplies motivation and an
argument a mathematician can read. A finite calculation covers only the range
it reached.

Comparator gives selected statements a second, independently declared formal
interface under a fixed set of assumptions, and reports whether the two agree.
It exposes mismatches between formal surfaces. It is not peer review and does
not establish novelty. The [Palomar guide](verification/PALOMAR_QUALIFICATION.md)
links the separately pinned repository units and explains how to check local
packaging. Service submission, registration and acceptance require their own
recorded evidence; local readiness does not establish them.

This repository is a self-contained public record. It is not an entrypoint
into any private development system. The number of files, declarations, or
computed cases does not measure the importance of a result.

## Reviewing one result

Pick one statement in a short paper. Read its assumptions and the step that
does the work, then open the longer record if you want the attempts that led
there. If a hard step is compressed, a routine step gets too much space, or
you cannot tell where an idea came from, that is useful feedback. A checked
proof still needs an explanation a mathematician can understand and reuse.

## Contributing

AI tools did much of the research, code, and drafting under my direction. I am
responsible for the claims, the sources, and the release. Nothing here has had
independent mathematical review.

The most useful contribution is a mathematical one: a proof correction, a
clearer explanation of a hard step, an attribution correction, a counterexample
to an intermediate claim, or an earlier reference. The
[contributor guide](../CONTRIBUTING.md) explains how to send that back with its
evidence and credit intact. If this work helps you solve one of the eight, the
solution and the credit are yours.
