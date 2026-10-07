<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Accepted contribution recognition and impact

This generated public view answers which contributor or disclosed system contributed which accepted artifact, to which bounded research or architecture question, with what evidence and review state. It consumes accepted receipts only.

Each accepted row carries a `public_frontier` route to its problem result family, cross-problem subject frontier, or architecture contribution path. The receipt retains the exact surviving boundary; the route is navigation context only and does not create credit or promote the returned claim.

Result summaries and limitations record the submission-time evidence; review fields record the later acceptance decision.

The aggregate counts below are factual accepted-receipt counts with the stated denominator. They are not rankings, measures of mathematical importance, proof quality, novelty, ownership, endorsement, or model quality. Entries are sorted by stable key, not by count; equal counts remain tied and the stable-key order is navigation, not a rank. Human contributors, operators, collaborators, model systems, and providers remain separate identities; undisclosed and not-used states are not inferred to be disclosed.

Credit boundary: each row records only the narrow artifact paths and evidence named by its accepted receipt. Contributors retain clear credit for that work; Will Cook's pre-existing corpus authorship, provenance, and prior contributions remain distinct and are not reassigned by this projection.

Detached route-memory sidecars may bind an accepted-return intake, but they remain separate route authority and are not copied into or counted by this accepted-receipt view.

The denominator is the total accepted-receipt count. Facets are independent: a receipt can appear in multiple entries within a multi-valued facet such as collaborators or evidence, so entry counts are not percentages and must not be summed as a total.

Accepted-receipt denominator: `1`.

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

<a id="accepted-rr-public-return-routing-20260923"></a>

### 2026-09-23T07:36:38Z — Architecture — navigation — checked\_positive

- Receipt: [receipt:rr-public-return-routing-20260923](https://github.com/wcook04/plectis-erdos/blob/cf81c4df43f0df35b3eb0cb307593e8b7d512333/docs/research-commons/returns/rr-public-return-routing-20260923.json)
- Contributor: OpenAI Codex
- Operator relationship: `same_as_contributor` — OpenAI Codex
- Material collaborators: none recorded
- Model/system disclosure: `disclosed` — GPT-6
- Provider disclosure: `disclosed` — OpenAI
- Track/frontier: `architecture` — Architecture — navigation — `public-contribution-return-entry`
- Public frontier: [architecture contribution path](ARCHITECTURE_CONTRIBUTIONS.md#architecture-contribution-path)
- Result and claim ceiling: `checked_positive` / `validated_architecture_change`
- Requested disposition: `consider_architecture_adoption`
- Reproduction state: `reproduced`
- Review states: structural\_validation=valid; reproduction=reproduced; mathematical\_review=not\_required; claim\_boundary\_review=not\_required; accepted\_handoff=accepted; problem\_owned\_proposition=not\_requested; core\_promotion=not\_requested; tagged\_release\_inclusion=not\_requested
- Review decision details: structural_validation: state=`valid`; authority_ref=git:8cec1bb66576a7582fb8dc076cbbced166ed196b; decided_at=2026-09-23T07:36:38Z; reviewer=OpenAI Codex (maintainer-operated; same contributor); notes=Native submitted-return validation with complete proposed diff passed; package hashes, exact changed paths, merge ancestry, resolved documentation, and focused public tests inspected. This is same-agent validation, not independent human review.; authority_url=[`git:8cec1bb66576a7582fb8dc076cbbced166ed196b`](https://github.com/wcook04/plectis-erdos/commit/8cec1bb66576a7582fb8dc076cbbced166ed196b) | reproduction: state=`reproduced`; authority_ref=git:8cec1bb66576a7582fb8dc076cbbced166ed196b; decided_at=2026-09-23T07:36:38Z; reviewer=OpenAI Codex (maintainer-operated; same contributor); notes=The seven recorded no-Lean evidence commands and focused acceptance, return-validator, recognition, and architecture-guide tests passed on the integration tree. This replay was performed by OpenAI Codex, the same contributor/operator; no independent external clone replay is claimed.; authority_url=[`git:8cec1bb66576a7582fb8dc076cbbced166ed196b`](https://github.com/wcook04/plectis-erdos/commit/8cec1bb66576a7582fb8dc076cbbced166ed196b) | mathematical_review: state=`not_required`; authority_ref=none; decided_at=none; reviewer=none; notes=Architecture navigation change; no mathematical claim changed. | claim_boundary_review: state=`not_required`; authority_ref=none; decided_at=none; reviewer=none; notes=No mathematical claim transition requested. | accepted_handoff: state=`accepted`; authority_ref=git:8cec1bb66576a7582fb8dc076cbbced166ed196b; decided_at=2026-09-23T07:36:38Z; reviewer=OpenAI Codex (maintainer-operated; same contributor); notes=Local maintainer-operated decision to adopt this bounded architecture change into the detached integration history. Exact proposed commit 582871aa remains an ancestor. No public push, pull request, human review, tagged release, or mathematical claim transition is asserted.; authority_url=[`git:8cec1bb66576a7582fb8dc076cbbced166ed196b`](https://github.com/wcook04/plectis-erdos/commit/8cec1bb66576a7582fb8dc076cbbced166ed196b) | problem_owned_proposition: state=`not_requested`; authority_ref=none; decided_at=none; reviewer=none; notes=No problem proposition requested. | core_promotion: state=`not_requested`; authority_ref=none; decided_at=none; reviewer=none; notes=No core mathematical promotion requested. | tagged_release_inclusion: state=`not_requested`; authority_ref=none; decided_at=none; reviewer=none; notes=No tagged release inclusion requested.
- Impact projection: track=`architecture`; scope=Architecture — navigation; result_class=`checked_positive`; claim_ceiling=`validated_architecture_change`; requested_disposition=`consider_architecture_adoption`; evidence_states=`passed/reproduced; passed/reproduced; passed/reproduced; passed/reproduced; passed/reproduced; passed/reproduced; passed/reproduced`; reproduction_state=`reproduced`; review_states=structural\_validation=valid; reproduction=reproduced; mathematical\_review=not\_required; claim\_boundary\_review=not\_required; accepted\_handoff=accepted; problem\_owned\_proposition=not\_requested; core\_promotion=not\_requested; tagged\_release\_inclusion=not\_requested; correction_lineage_state=`none`; problem_owned_proposition_state=`not_requested`; core_promotion_state=`not_requested`; tagged_release_inclusion_state=`not_requested`
- Core-promotion state: `not_requested`
- Tagged-release inclusion: `not_requested`
- Summary: An ordinary-language request to return a bounded public tooling contribution now reaches return\_research, and the native packager accepts a checked-positive architecture return with passed source checks while its Lean-only workbench outcome remains open.
- Surviving claim boundary: The detached source commits and local return package are candidates only; maintainer review, public acceptance, release inclusion, and all mathematical claims remain separate.
- Evidence/replay states: `passed/reproduced; passed/reproduced; passed/reproduced; passed/reproduced; passed/reproduced; passed/reproduced; passed/reproduced`
- Evidence records: command=`python3 scripts/agent_skill_catalog.py --check`; observed=Registry valid and generated catalog current: 13 skills, 6 families, 17 lanes.; environment=Public checkout 582871aa49a4029b216055a1b7a87996695e8524; Python 3 standard library on macOS.; exit=`passed`; replay=`reproduced`; artifacts=[`skills/registry.json`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/skills/registry.json); command=`python3 scripts/test_agent_entry.py`; observed=105 task fixtures passed, including the observed return-for-acceptance failure and neighboring route controls.; environment=Public checkout 582871aa49a4029b216055a1b7a87996695e8524; Python 3 standard library on macOS.; exit=`passed`; replay=`reproduced`; artifacts=[`scripts/test_agent_entry.py`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/scripts/test_agent_entry.py), [`skills/registry.json`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/skills/registry.json); command=`python3 scripts/test_contribution_entry.py`; observed=Contribution entry prose, clone-local return, provenance, credit, and update route passed.; environment=Public checkout 582871aa49a4029b216055a1b7a87996695e8524; Python 3 standard library on macOS.; exit=`passed`; replay=`reproduced`; artifacts=[`scripts/test_agent_entry.py`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/scripts/test_agent_entry.py), [`skills/registry.json`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/skills/registry.json); command=`python3 scripts/test_compact_agent_entry.py`; observed=Compact agent entry passed with 7984-byte seed.; environment=Public checkout 582871aa49a4029b216055a1b7a87996695e8524; Python 3 standard library on macOS.; exit=`passed`; replay=`reproduced`; artifacts=[`scripts/test_agent_entry.py`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/scripts/test_agent_entry.py); command=`python3 scripts/test_clone_skills.py`; observed=Clone skill discovery and live CLI grammar checks passed.; environment=Public checkout 582871aa49a4029b216055a1b7a87996695e8524; Python 3 standard library on macOS.; exit=`passed`; replay=`reproduced`; artifacts=[`skills/registry.json`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/skills/registry.json); command=`python3 scripts/check_cold_clone_comprehension.py --quick`; observed=Committed human and agent first-contact projections verified; no Lean build or corpus-query sweep run.; environment=Public checkout 582871aa49a4029b216055a1b7a87996695e8524; Python 3 standard library on macOS.; exit=`passed`; replay=`reproduced`; artifacts=[`skills/registry.json`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/skills/registry.json); command=`python3 scripts/test_continue_research.py`; observed=Start, check, package, and adversarial cases passed; a synthetic checked-positive architecture return now packages with workbench outcome open while mathematical checked-positive closure remains established-only.; environment=Public checkout 582871aa49a4029b216055a1b7a87996695e8524; Python 3 standard library on macOS.; exit=`passed`; replay=`reproduced`; artifacts=[`scripts/continue_research.py`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/scripts/continue_research.py), [`scripts/test_continue_research.py`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/scripts/test_continue_research.py)
- Limitations: Focused public checks passed; no full release gate or independent external clone replay is claimed.; The proposed commits are detached and not in public main; a maintainer must review the code, identity, and credit wording after PR201 reconciliation.
- Accepted commit: [`8cec1bb66576a7582fb8dc076cbbced166ed196b`](https://github.com/wcook04/plectis-erdos/commit/8cec1bb66576a7582fb8dc076cbbced166ed196b)
- Receipt source hash: `sha256:c0445b253348adb770d1f2fd4aa018f4e48b6919619669ea0676edb9d40435e4`
- Artifact-credit paths: OpenAI Codex (software, validation): [`scripts/continue_research.py`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/scripts/continue_research.py), [`scripts/test_agent_entry.py`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/scripts/test_agent_entry.py), [`scripts/test_continue_research.py`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/scripts/test_continue_research.py), [`skills/registry.json`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/skills/registry.json)
- Evidence-artifact paths: [`scripts/continue_research.py`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/scripts/continue_research.py), [`scripts/test_agent_entry.py`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/scripts/test_agent_entry.py), [`scripts/test_continue_research.py`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/scripts/test_continue_research.py), [`skills/registry.json`](https://github.com/wcook04/plectis-erdos/blob/8cec1bb66576a7582fb8dc076cbbced166ed196b/skills/registry.json)

## Factual accepted-receipt aggregates

### Contributor

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `OpenAI Codex` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Artifact Credit

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `scripts/continue_research.py` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)
- `scripts/test_agent_entry.py` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)
- `scripts/test_continue_research.py` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)
- `skills/registry.json` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Material Collaborator

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `none recorded` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Model System

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `GPT-6` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Provider

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `OpenAI` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Operator Relationship

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `same_as_contributor — OpenAI Codex` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Track

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `architecture` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Problem

Denominator: `1` accepted receipts; entries are stable-key sorted.


### Architecture Area

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `navigation` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Result Class

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `checked_positive` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Requested Disposition

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `consider_architecture_adoption` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Evidence State

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `passed/reproduced` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Reproduction State

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `reproduced` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Review State

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `accepted_handoff=accepted` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)
- `claim_boundary_review=not_required` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)
- `core_promotion=not_requested` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)
- `mathematical_review=not_required` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)
- `problem_owned_proposition=not_requested` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)
- `reproduction=reproduced` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)
- `structural_validation=valid` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)
- `tagged_release_inclusion=not_requested` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Correction Lineage

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `none recorded` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Problem Owned Proposition State

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `not_requested` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Core Promotion State

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `not_requested` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

### Tagged Release Inclusion State

Denominator: `1` accepted receipts; entries are stable-key sorted.

- `not_requested` — accepted receipts: `1` — [Accepted record `rr-public-return-routing-20260923`](#accepted-rr-public-return-routing-20260923)

The accepted receipt remains the attribution evidence. Its evidence, limitations, correction lineage, and surviving boundary control the meaning of every projection row; Git history, claim authority, and release authority remain separate.
