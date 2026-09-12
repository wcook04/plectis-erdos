<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# The research commons

Contributors can clone this repository, work independently, and send back a
proof, correction, failed attempt or tooling improvement. The research commons
documents how to record the starting commit, evidence and contributor roles,
and how maintainers record acceptance. The records, examples, validation
programs and accepted credit pages all live in this repository.

Mathematical work and architecture work use the same contribution records. The
[architecture contribution path](ARCHITECTURE_CONTRIBUTIONS.md) welcomes ideas
and implementations for workflows, navigation, validation, reproducibility,
tooling, governance, and contributor experience without assigning them a fake
Erdős problem number.

A contributor starts from a particular public commit and follows a bounded
question. They might return a proof, correction, counterexample, negative
result, useful stopping point, or tooling improvement. The return says where
the work began, what changed, what another person can check, what conclusion
the evidence supports, and what remains unresolved.

The default mathematical routes are authored in the public problem corpus and
expose their exact question, source neighbourhood, permitted experiment,
expected evidence, and stop condition. A compute donor does not have to invent
a research objective or decide whether an agent has solved a problem. A growth
phase should add qualified mathematical review before these packets are
distributed at scale; such review is not claimed for every present route.

An agent's `solution found` message remains an unreviewed candidate. Maintainers
and reviewers can rerun its evidence commands, ask independent contributors or
agents to look for errors, compare the formal and informal statements, and
decide whether to request specialist review. A mature formal result may then be packaged with
Comparator for [Palomar](https://palomar-registry.org/), and relevant
mathematical work can be placed before the
[Erdős Problems](https://www.erdosproblems.com/) community. Those are external
routes. Palomar is a formal registry and automated filter rather than human
peer review, and this repository cannot grant novelty, endorsement, or broad
mathematical acceptance.

A contributor can open an ordinary [pull request](../../CONTRIBUTING.md) or
[research-progress issue](../../.github/ISSUE_TEMPLATE/research_progress.yml)
and describe the work in their own words. Include the starting commit, changed
files or failed route, commands actually run and their results, limitations,
and who did the work. No structured session or JSON package is required.

For an optional structured package, [start a continuation session](RETURN_PACKAGE_TEMPLATE.md#start-a-structured-continuation)
from a clean checkout before editing. `continue_research.py start` records the
current commit, question and identities under `workbench/sessions/<session>/`.
After the work, [fill the return files, close the session and package them](RETURN_PACKAGE_TEMPLATE.md#fill-and-package-the-structured-return).
The output directory contains `return.json`, `route-memory.json`, session
records and a `package.json` manifest listing the packaged files and hashes.
Keep the proposed commit or patch with the package: the packager does not copy
every changed source file. The template also gives the recipient's
[replay instructions](RETURN_PACKAGE_TEMPLATE.md#4-evidence-and-replay).

When maintainers accept returned work, a committed receipt ties it to the
accepted commit. It records the contributor, collaborators, tool operators,
and any disclosed model systems as separate roles. The public credit pages are
rebuilt from those receipts. Acceptance does not establish novelty, peer
review, mathematical truth, or a stronger claim.

The receipt and accepted artifact are ordinary tracked files, so older clones
receive both when they update. Work returned from an older starting commit is
reviewed in two passes: the original delta is replayed from its common ancestor,
then the accepted substance is reconciled with current main and checked again.
Any material conflict resolution is preserved as separately credited
integration work. A later correction points back to the earlier receipt
instead of erasing it. The history therefore records who did what, what was
known at the time, and what the work did not establish.

After a stable result, agents follow the clone-local consequence-propagation
skill to inspect the Lean, claim, paper, computation, route, validation, and
contributor files that may now be stale. Each candidate is updated, verified unchanged,
deferred with a re-entry condition, or excluded with a reason before the
return is packaged.

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

Scholarly sources and implemented external advice use a separate rail. Read
the generated [source-attribution index](SOURCE_ATTRIBUTIONS.md), or query its
machine-readable owner with
`python3 scripts/build_source_attributions.py --query <name-or-problem-or-id>`.
Check projection freshness with
`python3 scripts/build_source_attributions.py --check`. These source records
do not create accepted contribution receipts or imply endorsement.
