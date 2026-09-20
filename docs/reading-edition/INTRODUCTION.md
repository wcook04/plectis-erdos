<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

## How to use this edition

This file is a reading edition of the Plectis mathematics: papers on eight
Erdős problems, written so that a mathematician, or an AI model working for
one, can start reasoning from them without cloning a repository or installing
anything. Give the whole file to your model, or read it yourself. Everything in
it is generated from the same sources as the public papers, at the source
fingerprint printed above.

Two ways of starting are equally supported.

- **Work on a particular question.** Each paper states what is proved, what is
  computed and what remains open. Pick a statement and continue it.
- **Read the mathematics and decide what comes next.** The question is then an
  output of your work. The research instruction below describes this route.

The degree-seven counterexample found by the erdosproblems.com contributor ani
refutes the total-variation formulation of Erdős #1041; the repository
formalises it in Lean. The other seven target problems are not resolved here.
Independent human review of correspondence with the historical curve-length
formulation of #1041 has not been recorded. No paper in this edition has been
externally peer reviewed.

## Words used for evidence

The papers keep the following kinds of support apart, and work built on them
should do the same.

| Word | Meaning |
|---|---|
| Lean-checked | The pinned Lean kernel accepted a proof of the exact formal statement in the cited source. Whether that statement expresses the intended mathematics is a separate human judgement. |
| Ordinary proof | A mathematical argument written in the paper and not formalised. |
| Cited | A result of other authors, used with its reference. |
| Computed | An exact or numerical computation with a stated finite range. It settles only that range. |
| Open | Stated and unresolved. A reduction of an open statement to another open statement stays open. |

## A worked example of open reading

[Choices, contraction and rational membership](https://github.com/wcook04/plectis-erdos/blob/main/research/experiments/choices_contraction/README.md)
began from reading the short papers side by side. It recasts Erdős #257 at base
2 as a finite-rejection statement about rational numbers, tests it in exact
arithmetic, corrects its own first reading of the data, and ends with five
concrete ways to continue. It is one example of the route, and other ways of
working are as welcome.

## Sending work back

You do not need a clone to contribute. Send a mathematical account through the
[research-progress form](https://github.com/wcook04/plectis-erdos/issues/new?template=research_progress.yml)
or by [email](https://wcook04.github.io/plectis/#contact), and say which
edition fingerprint you started from. Useful prose is kept as written.
Accepted work is credited by name in the repository's contribution record
under its [credit policy](https://github.com/wcook04/plectis-erdos/blob/main/docs/research-commons/CREDIT_POLICY.md).
If you work in a clone, start at
[AGENTS.md](https://github.com/wcook04/plectis-erdos/blob/main/AGENTS.md).
