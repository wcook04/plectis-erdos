<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Verification and external review

There are several things you might mean by checking a result: compiling its
Lean proof, comparing the statement with the original problem, or asking
whether the paper explains the proof faithfully. This directory helps you
choose the check that answers your question.

If this is your first visit, [follow one claim to its source](../REPRODUCIBILITY.md#try-one-claim-without-lean).
That takes Git and Python. To compile its proof, continue with
[the Lean setup instructions](../REPRODUCIBILITY.md#2-reproduce-the-pinned-lean-environment).
You can also read the [papers](../../paper/README.md) and inspect the linked
statements before installing anything.

## Choose the question

| Your question | Where to go | What you learn |
|---|---|---|
| Does the formal proof compile? | [Reproduce the Lean environment](../REPRODUCIBILITY.md#2-reproduce-the-pinned-lean-environment) | Whether Lean accepts the selected modules with the pinned dependencies. |
| Does a selected proof meet a separately stated interface? | [Replay a selected statement](EXTERNAL_VERIFICATION_REPLAY.md) | How to run Comparator against the specified statement and source version. |
| How does our statement relate to the upstream problem? | [Formal Conjectures crosswalk](FORMAL_CONJECTURES_CROSSWALK.md) | The corresponding declarations, assumptions and recorded comparison. |
| What exactly does the #1049 calculation establish? | [The numerical certificate](COMPARATOR_1049_NUMERICAL_HEIGHT.md) | The checked numerical claim, source and bounds of the calculation. |
| What is ready for external submission? | [Palomar qualification](PALOMAR_QUALIFICATION.md) | The candidate evidence, submission requirements and outstanding external decisions. |

Comparator checks a selected interface. Its coverage is recorded in
[the external-verification dossier](../EXTERNAL_VERIFICATION.md); a successful
check of one interface does not certify everything in the repository.
Palomar is a separate external submission and review route. The local
qualification record shows what was prepared and what still needs an external
decision.

The runnable interfaces and certificates live in [verification/](../../verification/).
[Methodology](../METHODOLOGY.md) explains the responsibilities of Lean,
repository checks and human mathematical review. Judging whether a statement
captures the intended mathematics, whether an argument is useful, and how it
relates to prior work still requires reading the mathematics.

[Back to the documentation](../README.md).
