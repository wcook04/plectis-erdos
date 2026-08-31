<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Contributing

This repository is meant to be cloned, explored, improved, and brought back
into contact with the people who are working on it. A contribution does not
have to solve an Erdős problem to be useful. A corrected proof step, a failed
route with a reproducible reason, a counterexample, a sharper boundary, a
better explanation, or a repaired public check can all save future work.

The simplest contribution path is the familiar one. Fork or clone the public
repository, make a focused change on a branch, and open a pull request against
the public repository. Explain the mathematical question or repository
problem you started from, what you changed or learned, what evidence another
person can inspect, and what remains unresolved. If you have an observation
but no finished patch, open a plain-language research-progress issue instead.
You do not need to understand the repository's receipt format before telling
us something useful.

## What happens to returned work

Every proposed change keeps its delivery history in the public issue or pull
request. When work is accepted, the repository can also record a small,
committed receipt that says who contributed, which exact artifacts are being
credited, which public generation the work began from, what evidence was
checked, and which limitations survived. Generated contribution views are
built from those accepted receipts. This makes credit travel with the
repository rather than living only in a private notebook, a chat transcript,
or a disappearing web page.

Acceptance and mathematical claim status are deliberately separate. An
accepted correction can be credited without being called a new theorem. A
negative or inconclusive result can be credited when it rules out a route or
leaves a reproducible stopping point. A formal proof can be accepted as an
artifact while novelty, exposition, or a stronger public claim still needs
work. Earlier credit remains visible when a later contribution corrects or
supersedes it.

Credit is attached to the work actually returned. Contributors, collaborators,
people operating tools, and disclosed model systems remain distinct rather
than being collapsed into one author field. The project does not rank people
by commit count, diff size, or the number of generated records. See the
[credit and stewardship policy](docs/research-commons/CREDIT_POLICY.md) for the
full boundary and the [accepted contributions](docs/research-commons/CONTRIBUTIONS.md)
for the public, receipt-backed view.

## Staying in sync

A clone records the public commit from which its work began. That starting
point lets later readers distinguish the contributor's change from work that
landed in the meantime. Once accepted work reaches the public main branch or
a tagged release, anyone with an older clone can fetch it and merge or rebase
in the ordinary Git way. The accepted receipt, the credited artifact, and the
generated recognition view arrive together because they are public repository
files. None of that route depends on the private development repository.

If two contributions overlap, preserve both histories and reconcile them in a
new change; do not silently rewrite the earlier return. If a later discovery
shows an accepted artifact was wrong, make a corrective return that names the
earlier one and says whether it should be retained as history, superseded, or
withdrawn from current use.

## What is welcome

Mathematical errors and overstatements are especially valuable reports. So are
Lean build failures, broken source or paper links, missing attribution,
exposition that hides an assumption, counterexamples to intermediate claims,
and improvements to the clone-local checks. New formal results are welcome,
but their public description must be no stronger than the evidence, and all
eight headline Erdős problems remain open unless an extraordinary independent
mathematical process establishes otherwise.

Ordinary prose, citation, and tooling corrections can arrive as normal pull
requests. A research return is useful when the provenance matters: for
example, a bounded investigation that another person should be able to resume,
or a negative result whose exact starting point and evidence should not be
lost. The [research commons guide](docs/research-commons/README.md) explains
that lifecycle without requiring you to read a schema.

## For agents and maintainers

The human route above is the contract. The commands below implement it; they
are not prerequisites for reporting a useful result. Agents should use the
clone-local [research-return skill](skills/erdos-research-return/SKILL.md), and
maintainers should preserve the contributor's prose rather than replacing it
with machine field names.

To open and package a bounded, attributable structured research session, use
`scripts/continue_research.py`. Its `start`, `check`, and `package` commands
bind the public origin, starting commit, contributor identity, problem route,
evidence, and route-memory receipt. The resulting `return.json` and
`route-memory.json` may accompany a pull request. Validate them with
`scripts/validate_research_return.py` before submission. The detailed field
contract is in the [return package template](docs/research-commons/RETURN_PACKAGE_TEMPLATE.md).

After a contribution has actually landed, `scripts/accept_research_return.py`
can bind the reviewed result to its accepted public commit. Then
`scripts/build_research_contributions.py` and
`scripts/build_research_contribution_recognition.py` rebuild the accepted-only
credit views. A submitted return must never appear there before acceptance,
and an accepted receipt must never silently strengthen `docs/claims.json`.

For an ordinary source change, run the narrow checks named by the agent entry
and the affected subsystem. Lean changes must build with the pinned toolchain.
Changes to claims, papers, or generated projections must follow the authority
and builder order in [AGENTS.md](AGENTS.md). CI exercises the public return
validator, the acceptance boundary, and the accepted-only attribution views.
