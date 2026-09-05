<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Palomar: the current result portfolio

**Local structure is ready; release verification is still pending.** All 79
independent Challenge/Solution packages have valid configurations and trusted
Challenge imports. Together they expose 221 exact interfaces. The combined
project still needs its final Lean replay and commit-bound Linux Comparator
receipts before release.

The selected mathematical headline is the all-base reciprocal-summable support
theorem: for every integer base b ≥ 2 and every infinite set A of positive
integers with ∑ₐ∈A 1/a < ∞, the series ∑ₐ∈A 1/(bᵃ − 1) is irrational. No
pairwise-coprimality hypothesis is needed. Read the
[formal theorem](../Erdos249257/AllBaseReciprocalSupportIrrationality.lean#L395)
and the [#257 paper](../erdos-257-mersenne-support-subseries.pdf).

Its close-return argument controls an integer orbit using the summable
reciprocal tail. The theorem includes squares and other supports excluded by
the older coprimality hypothesis. It does not settle every reciprocal-divergent
support. The classical full-support theorem supplies a distinct settled case
in that regime. All eight indexed Erdős problems remain open.

## What the portfolio preserves

The headline is a reading choice, not a reason to discard other mathematics.
The [shared family order](PALOMAR_RESULT_SHOWCASE.json) covers all 93 registered
result families. It places complete theorems, exact reductions, route
obstructions, computations and remaining obligations in one public landscape.
Its editorial judgments are attributed to agents and remain open to specialist
correction; they are not novelty or priority assessments.

Each independent package has its own exact statement boundary. The
[entry catalogue](../verification/palomar-entry-catalog.json) links all 79
configurations. The [aggregate replay candidate](../verification/comparator-replay-candidate.json)
checks their 221 interfaces together. The older
[Comparator configuration](../verification/comparator.json) retains 54
interfaces, all accounted for in the result crosswalk. These are different
verification surfaces, not different counts of mathematical contributions.

The strongest #257 package includes the unrestricted reciprocal-summable
support theorem, its unconditional all-base bouquet corollary, and the generic
real-target repair equivalence. Its negative fixture restores the discarded
coprimality premise and must be rejected for a statement mismatch. The #249
squared-Lambert and #251 bounded-perturbation packages are also included.

A source-faithful wrapper does not establish novelty or the intended meaning
of a theorem by itself. The papers explain the mathematics, while explicit
claim-to-declaration transports record which source statements each interface
uses. Wrapper namespace differences are not evidence that a result is absent.

## What is checked, and what remains

The local qualification checker verifies the current catalogue, exact
configurations, trusted Challenge import closures, source envelopes, axiom
ceilings, result crosswalk and selection partitions. It reports **READY** for
that structural contract. The
[reconciliation record](PALOMAR_POLICY_RECONCILIATION.json) records the decision
and its pinned upstream policy sources.

Release assurance additionally requires the combined project kernel replay,
the correct published formal-source checkpoint, and actual positive and
negative Comparator execution on Linux using the configured fixed kernel and
sandbox. The runtime receipt and release manifest must bind the exact source,
configurations and all six uploaded log files, including the Strong257
negative log. The [replay and release guide](EXTERNAL_VERIFICATION_REPLAY.md)
gives the commands and evidence requirements.

No Palomar submission, registration, editorial endorsement or external replay
is asserted here. Those events are recorded separately if they occur.
