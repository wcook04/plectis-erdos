<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# The research commons

The research commons lets somebody clone the repository, work independently,
and send the result back without losing its origin, evidence, or credit. The
whole process is public: the records, examples, checks, and accepted credit
pages all live in this repository.

Mathematical work and architecture work share this provenance rail. The
[architecture contribution path](ARCHITECTURE_CONTRIBUTIONS.md) welcomes ideas
and implementations for workflows, navigation, validation, reproducibility,
tooling, governance, and contributor experience without assigning them a fake
Erdős problem number.

A contributor starts from a particular public commit and follows a bounded
question. They might return a proof, correction, counterexample, negative
result, useful stopping point, or tooling improvement. The return says where
the work began, what changed, what another person can check, what conclusion
the evidence supports, and what remains unresolved.

The default mathematical routes are designed or reviewed by mathematicians
and formalisation contributors. A compute donor does not have to invent a
research objective or decide whether an agent has solved a problem. They can
run a bounded packet with an exact question, source neighbourhood, permitted
experiment, expected evidence, and stop condition, then return what happened.

An agent's `solution found` message remains an unreviewed candidate. The
commons can replay it, ask independent contributors or agents to attack it,
reconcile the formal and informal statements, and decide whether it deserves
scarce specialist attention. A mature formal result may then be packaged with
Comparator for [Palomar](https://palomar-registry.org/), and relevant
mathematical work can be placed before the
[Erdős Problems](https://www.erdosproblems.com/) community. Those are external
routes. Palomar is a formal registry and automated filter rather than human
peer review, and this repository cannot grant novelty, endorsement, or broad
mathematical acceptance.

There are two ways in. A person can open an ordinary pull request or a
research-progress issue and describe the work in their own words. An agent or
an experienced contributor can also attach the structured package produced by
the continuation tools. That package makes later checking and attribution
easier. It is not an entrance exam for contributors.

When maintainers accept returned work, a committed receipt ties it to the
accepted commit. It records the contributor, collaborators, tool operators,
and any disclosed model systems as separate roles. The public credit pages are
rebuilt from those receipts. Acceptance does not establish novelty, peer
review, mathematical truth, or a stronger claim.

The receipt and accepted artifact are ordinary tracked files, so older clones
receive both when they update. A later correction points back to the earlier
receipt instead of erasing it. The history therefore records who did what,
what was known at the time, and what the work did not establish.

Several independent contributions may make a candidate cheaper for an expert
to inspect, but headcount is not evidence. The useful signal is legible work:
independent replay, adversarial checking, repaired failure modes, a stable
formal interface, and an exposition that a specialist can audit.

Begin with the [human contributor guide](../../CONTRIBUTING.md). Read the
[credit and stewardship policy](CREDIT_POLICY.md) when attribution matters.
The [return package template](RETURN_PACKAGE_TEMPLATE.md) is the detailed
agent-facing contract, while [accepted contributions](CONTRIBUTIONS.md) and
[contribution recognition](CONTRIBUTION_RECOGNITION.md) are generated views of
work that has actually been accepted.
