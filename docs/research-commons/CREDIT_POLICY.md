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

The same builder populates the references in [CITATION.cff](../../CITATION.cff).
Each citable source records its bibliographic metadata in `citation`; a reviewed
`citation_alias` can identify another source record for the same work while
preserving both attribution histories. Distinct editions keep separate records.
The generated references link to the source attribution entries, which in turn
identify the papers, bibliography keys and Lean passages that use them. The
paper catalogue supplies citations for the repository's own manuscripts,
including their publication state and source edition.

Adding a bibliography entry requires linking its source and citation metadata,
including when the entry lives in an included TeX file. The builder's `--check`
rejects missing coverage and stale CFF output. A `citation_exclusion` must give
an explicit reason for material that is not a bibliographic work, such as
private correspondence. Bibliography-only sources remain bibliography-only:
their inclusion in CFF does not claim a primary-source audit or strengthen a
mathematical claim.
The generated CFF is a consumer of these records. Bind local evidence to its
authored manuscript, toolchain or dependency manifest; retain historical CFF
credit through a commit-pinned source locator rather than a current line range.

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

## The credit ledger and naming

Advice received privately that changed public files is listed in the
[credit ledger](CREDIT_LEDGER.md). Each entry gives the date the advice arrived,
one sentence on what the person said, one sentence on what changed, and the
exact lines (and, where one commit made the change, the commit) where a reader
can see the change. The ledger is generated from the `correspondence` rows of
`source-attributions.json` by `python3 scripts/build_source_attributions.py`.

Every entry starts with the name withheld and the person described only by a
neutral role, such as "a mathematician". Only the person who gave the advice
can change that. If they confirm the public name they want, the row records it
with the confirmation date (`named_with_permission`). If they would rather stay
anonymous, the row says so (`anonymous_by_request`) and the advice stays
credited. These three states follow the pending, accepted and declined credits
of GitHub security advisories. Either change is a one-row edit followed by the
build command above; the message itself stays private. Acknowledgement in the
ledger does not say that the person reviewed, checked or endorsed the
mathematics.
