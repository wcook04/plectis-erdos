<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Credit and stewardship

Credit follows the accepted work. A receipt names the person who returned it
and the exact public files, results, or evidence being credited. It does not
reassign authorship of the surrounding corpus or imply that every idea from an
exploration became part of the accepted result.

A contributor may be different from a collaborator, a tool operator, or a
disclosed model or service used during the work. The receipt records those
roles separately. This makes assistance visible without obscuring human
responsibility or inventing authorship. It does not guess at undisclosed use.

Within artifact credit, optional CRediT-aligned roles describe what each person
supplied: for example conceptualization, formal analysis, investigation,
methodology, software, validation, visualization, or writing. Multiple roles
may apply. The role list describes contributions; it does not by itself decide
authorship, ownership, correctness, or priority.

Positive, negative, inconclusive, and corrective work can all receive credit.
The returned artifact must be useful, bounded, traceable, and accepted. It does
not need to look like a theorem or increase a score. The repository does not
rank contributors by commits, lines changed, receipt counts, model usage, or
another activity count.

Architecture ideas and implementations receive the same treatment. An adopted
idea should become a public design note, implementation, test, or other tracked
artifact that cites the proposal and names its originator. An issue mention by
itself is delivery history; the accepted artifact and receipt make the credit
durable in every clone.

Submission is not acceptance. Issues, pull requests, and Git history preserve
the delivery history, but work appears on the accepted credit pages only after
a receipt is committed against an exact public commit. Acceptance alone does
not establish correctness, novelty, peer review, release inclusion, or a
change in mathematical claim status. Each of those needs its own evidence.

Corrections preserve lineage. A newer receipt names the earlier return and
records whether it retains, supersedes, or withdraws the affected artifact.
The earlier contributor and historical evidence remain discoverable. Disputes
about attribution should be handled as corrective contributions with concrete
artifact and provenance evidence rather than by rewriting history silently.

All contributions remain subject to the repository's licences and source
attribution requirements. A contributor should cite prior work, identify any
material collaborators, and state limitations honestly. Maintainers must keep
the credit narrow, durable, public, and no stronger than the accepted evidence.

Prior literature, catalogues, public website contributions, and implemented
advice are indexed separately in [source attributions](SOURCE_ATTRIBUTIONS.md).
That view is built from `source-attributions.json` with
`python3 scripts/build_source_attributions.py`; use `--check` for freshness or
`--query <name-or-problem-or-id>` for a bounded lookup. It is source-credit and
navigation evidence, not an accepted-contribution receipt, authorship transfer,
mathematical review, or endorsement. Private correspondence remains anonymous
until the contributor confirms public naming; its private evidence stays out
of this repository.

## Directions, email, and work across tracks

A useful direction, reference, correction, example or explanation can be the
contribution. Describe that contribution precisely; conceptualization and
methodology credit do not depend on supplying code or finishing the proof.
The person who develops an idea later has a different role. Retain both when
both materially contributed, including when one return has mathematical and
architecture receipts.

The intake channel does not determine credit. For an email contribution,
maintainers record the date, the contributor's preferred public name or
anonymous designation, a public-safe account of the idea, and the permission
to publish that account. Confirm naming and quotation preferences before
publishing private correspondence; retain the message outside the public
repository. Put adopted substance and its attribution in a tracked artifact,
then use the same acceptance and recognition builders as for a GitHub return.
The public record can cite that artifact without exposing an email address.
An unadopted suggestion remains acknowledged as a suggestion, not an accepted
result. A receipt never grants authorship of unspecified future consequences.
