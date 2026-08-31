<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Contributing to the architecture

This project has two equal contribution tracks: advancing the mathematics and
improving the machinery that helps people and agents advance it. You may
propose or implement a better workflow, skill, navigation route, validation
check, reproducibility tool, contributor experience, governance rule, or other
piece of public infrastructure. You do not need to solve an Erdős problem to
make a first-class contribution.

The repository gives credit for the accepted work you actually supply. An idea
can be credited as conceptualization or methodology; code can be credited as
software; tests and review can be credited as validation. These roles may be
combined and are recorded beside the exact accepted paths. They describe the
contribution and do not silently transfer authorship of the surrounding corpus.

## Architecture contribution path

1. Open an [architecture proposal](../../.github/ISSUE_TEMPLATE/architecture_proposal.yml)
   for an idea, or fork the repository and open a focused pull request for a
   bounded implementation. Early proposals are welcome; a polished patch is
   not an entrance requirement.
2. Name one observable problem and one stop condition. For example: “a cold
   clone cannot discover the validation command; stop when the new route is
   discoverable and its regression test passes.”
3. Preserve a public starting commit and provide the smallest replay another
   contributor can run. New agent workflows must remain clone-local and must
   not depend on private files, credentials, or an unpublished service.
4. In the pull request, request the contribution roles and display name you
   want recorded. Name material collaborators and prior art separately.
5. A maintainer reviews the exact change and its evidence. Acceptance records
   artifact adoption, not universal quality, mathematical truth, novelty, or
   release status.
6. If accepted, a receipt with `frontier.track: architecture` records the area,
   starting generation, paths, evidence, limitations, review state, and credit.
   The same builders used for mathematical returns add it to the public
   contribution and recognition views.

An issue-only idea can still receive durable repository credit. If the idea is
adopted, the accepting change should add a short public design note or other
artifact, cite the issue, name the originator, and include that path in the
accepted receipt. This keeps credit available to every clone rather than only
to readers of the issue tracker.

## Areas and machine contract

Structured architecture receipts use one of these areas:

- `agent_workflow`
- `navigation`
- `validation`
- `reproducibility`
- `public_experience`
- `governance`
- `tooling`
- `other`

They use an architecture-specific claim ceiling:
`architecture_proposal`, `validated_architecture_change`, or
`architecture_correction`. They cannot request mathematical proposition or
core promotion. Mathematical review fields are marked `not_required` when no
mathematical claim changes; structural validation, replay evidence, and the
explicit acceptance decision remain visible.

## Review and execution boundary

Architecture pull requests can change code that later runs in CI or inside an
agent session, so maintainers review them as executable contributions. Pull
requests from forks run only with the permissions and secrets made safe for
untrusted code. A proposal is never executed merely because it was submitted.
Changes that affect public mathematical wording or reviewed claims must also
follow the mathematical authority and release checks in [AGENTS.md](../../AGENTS.md).

The generated [accepted contributions](CONTRIBUTIONS.md) and
[contribution recognition](CONTRIBUTION_RECOGNITION.md) views remain
non-scalar: they answer who contributed what, with which evidence and review
state, without turning commits, lines, receipts, or compute into a score.
