<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Public return package

Copy this file into a proposed public return or issue, then replace every
angle-bracket field. Keep the package limited to public paths and the exact
evidence needed to replay the result. A return records work; it does not by
itself promote a reviewed claim.

## Canonical routes

For cold-clone orientation, begin with the [reader orientation](../ORIENTATION.md)
and choose a bounded problem route from the generated [problem index](../problems.json),
then return here to record the exact evidence and attributable outcome.
When the return names a problem, preserve its exact stable `erdos_<n>` route id
from `python3 scripts/query_corpus.py --route erdos_<n>` and use the
[complete eight-problem return matrix](../SOURCE_MAP.md#complete-eight-problem-return-matrix)
for the human crosswalk; do not invent an anchor from wave chronology.

Start with the [agent workbench cold-start route](../AGENT_WORKBENCH.md) and
keep the [accepted-contribution index](CONTRIBUTIONS.md) beside the return.
For continuation, retain the route-memory sidecar described in section 4 and
follow the selected problem's frontier route in the [complete eight-problem
return matrix](../SOURCE_MAP.md#complete-eight-problem-return-matrix). The
[accepted-receipt recognition and impact view](CONTRIBUTION_RECOGNITION.md)
and its [machine-readable projection](contribution-recognition.json) expose
contributor, artifact, result, evidence, review, promotion, correction, and
release-inclusion details only after an accepted receipt exists. They preserve
distinct human, operator, collaborator, model, and provider identities and do
not rank activity. The generated [accepted-contributions view](CONTRIBUTIONS.md)
remains the compact receipt-backed artifact-credit index. After acceptance, follow
the row's `public_frontier` path and use the matching row in the [complete
eight-problem return matrix](../SOURCE_MAP.md#complete-eight-problem-return-matrix);
it exposes
the complete result-family frontier and surviving boundary, but creates no extra
recognition credit. Validate a saved return with
[`scripts/validate_research_return.py`](../../scripts/validate_research_return.py);
if the return would change a reviewed claim, consult the authoritative
[methodology](../methodology.json).

## Formal handoff from exposition

Resolve the public navigation handle before filling the bounded route. For a
paper or reviewed packet with a canonical paper label, start at the paper
anchor; for a registered problem-owned note, start at the problem packet:

```sh
# For a reviewed paper or claim packet, use:
python3 scripts/query_corpus.py --paper-anchor <canonical_paper_label>
# For a registered problem-owned note, start with:
python3 scripts/query_corpus.py --problem <number>
# Then continue with the registered note artifact:
python3 scripts/query_corpus.py --publication-artifact erdos_<number>_note
# To enumerate that note's exact paper anchors, use its returned artifact id:
python3 scripts/query_corpus.py --search "erdos_<number>_note::" --limit 100
python3 scripts/query_corpus.py --paper-anchor erdos_<number>_note::<label>
# For source-only #68 or #1041, continue with the module returned above:
python3 scripts/query_corpus.py --module <module-or-path returned by --problem>
```

The namespaced `<artifact_id>::<label>` handle keeps repeated paper labels
attached to the correct problem note; the [public-evidence return route](../PROOF_STATE_COMPILER.md#return-to-public-evidence)
documents the same bridge. A note's `source_path` or
`paper.source_ref` remains a reading locator, not a selector input; the
source-only #68 and #1041 routes continue through their returned Lean module.

Then carry the returned claim, declaration, and source handles into the
formal evidence section:

```sh
python3 scripts/query_corpus.py --claim <claim_id_from_packet>
python3 scripts/query_corpus.py --module <module-or-path>
python3 scripts/query_corpus.py --declaration <qualified_declaration>
python3 scripts/query_corpus.py --source <module>:<positive_line>
```

Use the module query as the context-preserving step between a returned claim
and its exact declaration: it exposes imports and the declaration inventory
before a reviewer narrows to a source coordinate. It is a navigation witness,
not proof authority; preserve the pinned Lean source, registered claim, and
problem boundary in the return.

For the public problem route, start with the generated
[problem index](../problems.json), which exposes every `material_result_families`
entry—its mechanism, exact scope, Lean route, and open boundary—before you
follow named Lean interfaces. For the reader-facing proof/paper/source
crosswalk and compact grouped route to its strongest distinct public results,
use the [complete eight-problem return matrix](../SOURCE_MAP.md#complete-eight-problem-return-matrix);
the
legacy `strongest_result` field must not stand in for that full frontier. For
the complete family census and a reverse route to one selected family, run
`python3 scripts/query_corpus.py --search "all result families"`, then
`python3 scripts/query_corpus.py --publication-family <family_id>`. The returned
`significance_rank` is a navigation order, not a novelty or priority claim. For
the all-eight proof-to-paper/source dispatch table, use the
[proof-state public-evidence route](../PROOF_STATE_COMPILER.md#return-to-public-evidence).
It is a navigation aid, not proof authority.

For the paper-to-formal crosswalk, use the
[complete eight-problem return matrix](../SOURCE_MAP.md#complete-eight-problem-return-matrix).
For a registered problem note, continue through its exact note-anchor
crosswalk in that matrix before
following the returned declaration and source-coordinate route. The map
connects canonical paper and source records to problem, claim, module,
declaration, and source-coordinate routes; it is a navigation aid, not proof
authority.

The packet's `paper.source_ref` or note `source_path` is a manuscript locator,
not proof authority and not necessarily a selector input. Record the exact
declaration and source-coordinate results actually used; checked Lean source,
the registered claim, and the problem boundary remain the authorities.

## 1. Identity and starting generation

- **Contributor name or handle:** `<name>`
- **Submitted at:** `<ISO-8601 date-time with an explicit timezone, e.g. 2026-08-27T19:30:00+01:00>`
- **Starting release tag:** `<exact public tag, or “untagged commit”>`
- **Starting commit:** `<full 40-character commit from git rev-parse HEAD>`
- **Repository:** `https://github.com/wcook04/plectis-lean-erdos249-257`
- **Repository origin recorded by the continuation session:** `https://github.com/wcook04/plectis-lean-erdos249-257`
- **Proposed commit:** `<full 40-character descendant of the starting commit, or null>`
- **Public artifact commit or patch:** `<commit, attached patch, or exact file set>`

The artifact must be intelligible as a change from the starting commit. If the
checkout already contained unrelated work, list it and do not attribute it to
this package.

## 2. Bounded route

- **Erdős problem:** `#<68|243|249|251|257|269|1041|1049>`
- **Exact problem/claim/open handle:** `<identifier and command or file>`
- **Publication family and significance rank:** `<exact family id and rank from the complete family query, or “not applicable”>`
- **Bounded question:** `<one sentence with a stop condition>`
- **Starting source or declaration:** `<public path and declaration, if any>`
- **Why this route is in scope:** `<replay, correction, exposition, or bounded expansion>`

Use the public query route before describing the frontier:

```sh
python3 scripts/query_corpus.py --problem <number>
python3 scripts/query_corpus.py --open <remaining-open-id>
```

For a source-only problem, record the exact module or declaration returned by
the problem route. For example, #68 may cite
`ErdosProblems.Erdos68.AdjacentUnitCarryWindow` and its named declarations;
the checked finite interface remains source evidence, not a reviewed claim or
a solution of Erdős #68. Keep the problem packet's open obligation beside the
returned source handle.

When this package follows an initialized continuation session, copy its exact
bounded question and stop condition; do not silently broaden either field.

## 3. Artifact and result class

- **Changed public paths:**
  - `<path>`
- **Artifact description:** `<what a cold reader can inspect>`
- **Result class:** `checked_positive | negative | inconclusive | corrective`
- **Exact positive conclusion, if any:** `<statement no stronger than evidence>`
- **Exact negative or inconclusive boundary, if any:** `<route ruled out or work stopped>`
- **Open proposition that remains:** `<identifier and wording>`

State whether the object is a source change, finite computation, proof
workbench record, exposition correction, or another public artifact. A checked
declaration is not automatically a reviewed claim.

## 4. Evidence and replay

For a fresh-machine replay, start from the pinned public snapshot and record
the toolchain and dependency bootstrap before running any consumer.  Use
exactly one fresh contributor checkout for the replay; do not create a second clone,
worktree, copied tree, or duplicate dependency cache:

```sh
git clone --filter=blob:none https://github.com/wcook04/plectis-lean-erdos249-257 <destination>
cd <destination>
git checkout --detach <starting commit>
test "$(git status --porcelain)" = ""
test -s lean-toolchain
toolchain="$(cat lean-toolchain)"
elan toolchain install "$toolchain"
test -s lake-manifest.json
cache_receipt="$(python3 scripts/validation_singleflight.py submit --class toolchain-cache)"
cache_key="$(printf '%s\n' "$cache_receipt" | python3 -c \
  'import json,sys; print(json.load(sys.stdin)["key"])')"
python3 scripts/validation_singleflight.py status --key "$cache_key"
python3 scripts/validation_singleflight.py collect --key "$cache_key" \
  --wait --timeout-seconds 1800
```

The cache is an optional accelerator. The tracked source, `lean-toolchain`,
and `lake-manifest.json` are the reproducibility inputs; do not rely on a
machine-local cache or an ambient default toolchain. Record the exact
parallelism, timeout, and first next action when a replay is bounded or stops.

List each command actually run, from the repository root, with its exit state.
Do not write `passed` for a command that was not run.

Before running the evidence commands, start from the exact public generation
recorded above in a clean clone:

```sh
git checkout --detach <starting commit>
git rev-parse HEAD
```

Record that checkout as the replay ref so a later repository generation cannot
silently change the observed result.

```text
command: <exact command>
exit: <0, nonzero, or not-run>
observed: <short output or failure class>
environment: <pinned toolchain / relevant public dependency>
```

Minimum useful evidence, as applicable:

```sh
git diff --check
python3 scripts/check_cold_clone_comprehension.py --quick
python3 scripts/query_corpus.py --problem <number>
python3 scripts/validate_research_return.py return.json \
  --require-submitted --check-git \
  --require-route-memory-receipt \
  --route-memory-receipt route-memory.json
```

For a continuation package, keep the canonical route-memory sidecar beside
`return.json`; the sidecar-gated command above is the GitHub-intake form.

When the return follows a provider-neutral continuation session, run the
session join before packaging the artifact so the public starting generation,
repository origin, problem route, frontier, identity, and result class are
checked against the opened session:

```sh
python3 scripts/continue_research.py check \
  --session <session> \
  --return-json return.json \
  --replay
```

This join check makes the return replayable from the recorded public
generation; it does not promote a claim or bypass methodology review.

When the continuation session supplies a detached `route-memory.json`, keep
that sidecar beside `return.json` and bind it at intake. The sidecar is the
separate authority for the consulted route and its digest; do not copy
canonical route text into this package. Run the provider-neutral join and the
GitHub-intake validator with the sidecar required:

```sh
python3 scripts/continue_research.py check \
  --session <session> \
  --return-json return.json \
  --route-memory-receipt route-memory.json
python3 scripts/validate_research_return.py return.json \
  --require-submitted --check-git \
  --require-route-memory-receipt \
  --route-memory-receipt route-memory.json
python3 scripts/continue_research.py package \
  --session <session> \
  --return-json return.json \
  --route-memory-receipt route-memory.json \
  --output <plain-package-directory>
```

Record the exact `route_memory.sha256`, `return_id`, route relationship, and
changed-evidence paths from the sidecar; the validator rejects a different
problem or route, a stale canonical digest, or changed evidence that is absent
from `return.repository.changed_paths`. See the [accepted contribution
recognition view](CONTRIBUTION_RECOGNITION.md) for the corresponding
accepted-receipt command and its authority boundary.
The package transition copies `return.json` and `route-memory.json` together;
do not submit a return without the sidecar, and do not treat a successful
local join as accepted recognition.

At a route-provenance-required intake, the exact rejection boundary also
includes a missing sidecar, a non-canonical route-memory path, a return ID or
problem mismatch, a route ID belonging to another problem, or an observed
status that inflates the canonical record. Duplicate or unsafe changed
evidence is rejected; `supersedes` must name changed evidence included in the
return, while every other relationship must leave `changed_evidence` empty.
Passing these checks binds route provenance only. It does not accept the
return, create contributor recognition, promote a claim, or establish tagged
release inclusion; those remain separate committed review decisions.

For Lean, include the focused build or replay command and the exact source
module. For a finite computation, include its bounded parameters and the
script path. For an inconclusive attempt, include the last completed step and
the first next command instead of hiding the failure.

## 5. Claim ceiling, attribution, and limitations

- **Authority used:** `<Lean kernel / registered claim / public source / finite script>`
- **Claim ceiling:** `<formalised here, verified finite instance,
  conditional reduction, cited only, or open>`
- **No-claim statement:** `<what this package does not prove or establish>`
- **Prior work and attribution:** `<citation and how it relates>`
- **Existing corpus/authorship boundary:** `Pre-existing repository material
  remains credited to its existing authors and notices.`
- **Contributor credit requested:** `<name/handle and exact artifact to attribute>`
- **Operator relationship:** `<same_as_contributor | operated_for_contributor | other>`
- **Material collaborators:** `<each person and the exact material role, or none>`
- **Disclosed model system:** `<name/version/resources, undisclosed, not_used, or not_recorded>`
- **Disclosed provider:** `<name/version/resources, undisclosed, not_used, or not_recorded>`
- **Known limitations:** `<assumptions, bounded range, missing review, or unresolved failure>`

For source-backed claims, begin with the [prior-art and attribution map](../PRIOR_ART.md#principal-sources)
and record the exact artifact, digest, and locator you checked; a citation
label alone is not evidence. If the map marks the source unresolved, carry that status into the
return and do not state a theorem-level conclusion from metadata or an
unreadable publisher route.

Credit the contributor for the work actually returned. Do not infer novelty,
independent review, ownership of the pre-existing corpus, or authorship from
commit count, model assistance, or activity volume.

### Correction lineage

Complete this subsection for an original correction record and for every later
revision. A later correction is append-only: it must preserve the earlier
return, contributor credit, evidence, and result boundary rather than silently
strengthening or replacing them.

- **Prior return reference:** `<none for an original return, or exact path/ref>`
- **Affected paths and starting generation:** `<exact public paths and commit>`
- **Changed evidence or wording:** `<what was corrected and why>`
- **Correction reason:** `<source, replay, attribution, or wording reason>`
- **Correction disposition:** `retain | supersede | withdraw | request review`

## 6. Resume state and promotion request

After acceptance, use the [recognition view](CONTRIBUTION_RECOGNITION.md) to
find the receipt-backed attribution and impact record for this return. An
unaccepted, rejected, or merely local return must not be described as a
recognition record.

For an accepted return, copy these source-bound recognition fields from the
accepted receipt and its generated views:

- **Accepted return id:** `<exact return_id, or null before acceptance>`
- **Accepted receipt path and digest:** `<repository-relative path and exact sha256, or null before acceptance>`
- **Accepted commit (accepted artifact generation):** `<repository.accepted_commit and pinned URL, or null before acceptance>`
- **Accepted receipt source URL:** `<recognition URL whose blob matches the receipt digest, or null before acceptance>`
- **Provenance note:** `<the accepted artifact commit and receipt-payload commit may differ>`
- **Recognition human view:** [`CONTRIBUTION_RECOGNITION.md`](CONTRIBUTION_RECOGNITION.md)
- **Recognition machine view:** [`contribution-recognition.json`](contribution-recognition.json)

Verify the committed views and retrieve this return by its exact accepted id:

```sh
python3 scripts/check_research_contribution_recognition.py
jq --arg return_id "<accepted-return-id>" \
  '.chronological[] | select(.return_id == $return_id)' \
  docs/research-commons/contribution-recognition.json
```

Bind any displayed facet to the matched row's `receipt_path`,
`receipt_sha256`, and `repository.accepted_commit`. A missing or non-matching
row is expected before acceptance: submitted, rejected, local, or
route-memory-only work has no recognition credit.

Keep these fields empty until the return is accepted. They identify the narrow
artifact and evidence record; they do not rank contributors or systems, imply
independent review, or promote a mathematical claim.

The accepted projection is an evidence index, not an adjudication. Read its
`impact_state` together with the source-bound receipt: problem and result class,
claim ceiling, evidence exit and replay states, review decisions and authority
references, correction lineage, core-promotion state, tagged-release inclusion,
limitations, and surviving boundary. Contributor, material-collaborator,
operator-relationship, disclosed-model, and provider facets remain separate;
accepted-receipt counts are denominated lookup facts, not scientific rankings.
Commits, diff size, model usage, unaccepted activity, or this template's
illustrative prose cannot supply recognition, ownership, endorsement, or
independent mathematical review.

- **Last completed step:** `<exact public action>`
- **Next bounded action:** `<one command or proof/exposition task>`
- **Stop condition:** `<when to record negative/inconclusive and stop>`
- **Requested disposition:** `accept as handoff | review correction |
  consider core promotion | no promotion yet`
- **Canonical owner to review:** `<claim/source/release owner, if known>`

If this would change a reviewed claim, request review before editing the claim
registry and identify the methodology change class. Otherwise leave it in the
problem-owned or continuation route. The repository owner controls any public
merge, tag, release, submission, or external contact.

## 7. Public-safety check

- [ ] No private repository, absolute local path, cache, credential, log, or
      unpublished correspondence is included.
- [ ] The starting generation and changed public paths are exact.
- [ ] Every command has a truthful exit state.
- [ ] Positive, negative, or inconclusive status is stated plainly.
- [ ] The open boundary and limitations are preserved.
- [ ] Licenses and existing authorship are not overwritten or overclaimed.
