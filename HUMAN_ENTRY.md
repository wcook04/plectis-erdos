<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# A reader's way in

This repository follows eight unsolved problems of Paul Erdős. It contains
Lean proofs, mathematical papers, explanations for readers, and checks that
compare the claims in those different forms. You do not need to know Lean or
understand the directory layout to begin.

All eight problems remain open. The project proves intermediate theorems,
formalises results already known in the literature, tests exact finite cases,
and records obstructions that rule out tempting approaches. Some of that work
is substantial. None of it should be mistaken for a solution merely because a
proof assistant checked it or because a computation reached a large number.

## What formalisation adds

Lean checks a precise mathematical statement against a precise proof. This is
valuable because it forces assumptions, quantifiers, and dependencies into the
open. It can show that a stated reduction really follows, that a finite
certificate is correct, or that a proposed argument needs a hypothesis that
informal prose had hidden.

Lean does not decide whether a theorem is new, important, well motivated, or
the right way to attack an open problem. It also does not turn a conditional
result into an unconditional one. The papers and result guides explain why a
formal statement matters and where it stops; the formal source is there when a
reader wants to inspect the exact statement.

## A good first mathematical thread

Problem 257 is the clearest place to begin with a completed theorem family.
The repository checks irrationality for several restricted classes of supports
and develops the topology and measure theory of the associated achievement
sets. The universal question, covering every infinite support, is still open.

Problem 249 shows something different: what a failed route can teach. It
contains exact reductions, finite denominator exclusions, and a long
certificate programme. It also proves that several attractive reformulations
are equivalent to the original open problem, so they do not remove its hard
step. A future researcher can see which apparent shortcuts have already been
tested and why they stop.

The other six programmes each have their own paper. They concern factorial
denominators, rapidly growing reciprocal sums, prime gaps, running least common
multiples, short curves in polynomial lemniscates, and Lambert-type series at
rational bases. You can choose one from the paper list on the front page
without understanding the rest of the corpus.

## How to read the evidence

The project keeps several kinds of evidence separate. A Lean proof tells you
that a formal statement has been checked. A claim record tells you how that
statement may be described publicly and what remains open. A paper supplies
motivation, context, and an argument a mathematician can read. A finite
calculation establishes only the range it actually covers.

Comparator and Palomar belong to this evidence story, but neither is a
mathematical oracle. Comparator gives selected statements a second,
independently declared formal interface under a fixed set of assumptions. It
helps expose mismatches between what two formal surfaces say; it is not
independent peer review and does not establish novelty. Palomar organises a
small set of candidates for possible external review and records whether the
repository is structurally ready for that process. It does not confer
acceptance, importance, publication, or endorsement.

Start with the mathematical question. Read each result together with its
stated limit, then follow the formal source when you want the exact theorem.
The number of files, declarations, or computed cases does not measure the
importance of a result.

## Where to go next

The front page lists all eight mathematical papers. The results guide gives a
problem-by-problem account of what is known inside this repository and what
still blocks each endpoint. The scope and prior-art guides explain attribution
and guard against claims the project does not make. The architecture guide is
for readers who want to understand how the checks and generated indexes fit
together.

If you contribute, the most useful starting point is still a mathematical
question: a proof correction, a clearer explanation of a hard step, a source
or attribution correction, a counterexample to an over-strong intermediate
claim, or a reproducible improvement to the public checks. The repository's
machinery exists to support that work. It is not the subject a human reader
must learn before the mathematics becomes visible. The
[contributor guide](CONTRIBUTING.md) explains how work from any clone can come
back with its evidence and credit intact, without asking a human to speak in
commands or machine field names.

## Where I actually am

I am 22. I took a year out of my economics degree at Bristol for mental health
reasons, and working on this became my life. I am about a month from running
out of money, and I rushed this release because real life caught up with me.
That is not a pity play, it is just where I am. As this is written the
repository has zero stars.

This repository is the output. The private system behind it is bigger: the
videos show the entire frontend, the docs on the website carry how I think
about AI and safe systems, and Plectis is the prototype of what the system
could look like in a year or two with support. There are other apps I use
daily that I would happily open-source too; I keep choosing the mathematics
because it is the part a stranger can verify.

I have been doing this alone for a year and I do not really know how to
interact with people, especially Silicon Valley, where everyone is rightfully
busy. So I designed this to be cloned instead of pitched. That is what this
repository is for: the eight problems mapped to their exact open steps, every
claim bound to what is actually proved, and the machinery for working on them
already built, where an agent cannot mark its own work and the kernel decides.
It was made on the bet that models improve, so that whoever points better ones
at it starts from here instead of from zero. A solution found that way is
yours, credit included. I do not care about prestige or glory. I need support,
or at least people using what I built.
