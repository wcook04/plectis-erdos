<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Accepted contribution recognition and impact

This generated public view answers which contributor or disclosed system contributed which accepted artifact, to which bounded problem, with what evidence and review state. It consumes accepted receipts only.

Each accepted row carries a `public_frontier` route to the complete result-family fan-in and exact surviving boundary for its problem. That route is navigation context only; it does not create credit or promote the returned claim.

The aggregate counts below are factual accepted-receipt counts with the stated denominator. They are not rankings, measures of mathematical importance, proof quality, novelty, ownership, endorsement, or model quality. Entries are sorted by stable key, not by count; equal counts remain tied and the stable-key order is navigation, not a rank. Human contributors, operators, collaborators, model systems, and providers remain separate identities; undisclosed and not-used states are not inferred to be disclosed.

Credit boundary: each row records only the narrow artifact paths and evidence named by its accepted receipt. Contributors retain clear credit for that work; Will Cook's pre-existing corpus authorship, provenance, and prior contributions remain distinct and are not reassigned by this projection.

Detached route-memory sidecars may bind an accepted-return intake, but they remain separate route authority and are not copied into or counted by this accepted-receipt view.

The denominator is the total accepted-receipt count. Facets are independent: a receipt can appear in multiple entries within a multi-valued facet such as collaborators or evidence, so entry counts are not percentages and must not be summed as a total.

Accepted-receipt denominator: `0`.

Machine-readable projection: [contribution-recognition.json](contribution-recognition.json). Contributor contract: [CONTRIBUTING.md](../../CONTRIBUTING.md) and [CREDIT_POLICY.md](CREDIT_POLICY.md).
Projection contract: [research-contribution-recognition.schema.json](schema/research-contribution-recognition.schema.json).
Cold-clone validation: `python3 scripts/check_research_contribution_recognition.py` (read-only; verifies committed receipts and both generated views).

Retrieve one accepted record by its exact return id:

```sh
jq --arg return_id "<accepted-return-id>" \
  '.chronological[] | select(.return_id == $return_id)' \
  docs/research-commons/contribution-recognition.json
```

The row's `receipt_path`, `receipt_sha256`, and `repository.accepted_commit` are the provenance anchors for every displayed facet. An empty match is correct for a submitted, rejected, or sidecar-only return until an accepted receipt is committed.

## How to read an accepted record

A `checked_positive`, `negative`, `inconclusive`, or `corrective` return can be recognized after acceptance. Recognition credits only the exact artifact and evidence named by its accepted receipt; it is not a score for commits, diff size, model use, or contributor activity.

- Start with the result class, claim ceiling, limitations, and surviving boundary. These fields describe the returned artifact and do not promote a mathematical claim.
- Follow the artifact-credit paths, accepted receipt, accepted commit, evidence records, and review-authority links. A missing authority remains missing, and acceptance is not independent mathematical review.
- For a corrective record, follow `correction_lineage` and its `retain`, `supersede`, or `withdraw` disposition; the prior receipt remains discoverable.
- Treat `tagged_release_inclusion_state` as a release fact only. It does not imply inclusion, endorsement, ownership, or mathematical importance.

## Accepted artifact records

## Factual accepted-receipt aggregates

### Contributor

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Artifact Credit

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Material Collaborator

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Model System

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Provider

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Operator Relationship

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Track

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Problem

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Architecture Area

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Result Class

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Requested Disposition

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Evidence State

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Reproduction State

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Review State

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Correction Lineage

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Problem Owned Proposition State

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Core Promotion State

Denominator: `0` accepted receipts; entries are stable-key sorted.


### Tagged Release Inclusion State

Denominator: `0` accepted receipts; entries are stable-key sorted.


The accepted receipt remains the attribution evidence. Its evidence, limitations, correction lineage, and surviving boundary control the meaning of every projection row; Git history, claim authority, and release authority remain separate.
