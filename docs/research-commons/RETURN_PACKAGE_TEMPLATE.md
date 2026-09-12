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

Start with the [agent workbench cold-start route](../agents/AGENT_WORKBENCH.md) and
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

## Start a structured continuation

This section is optional for an ordinary issue or pull request. For a
structured continuation package, run `start` from the repository root before
editing or committing research changes. It records the current `HEAD`; it does
not recover the starting commit after the work. Use Git and Python 3.11 or
newer, as in the [clone setup](../REPRODUCIBILITY.md#1-start-with-a-complete-committed-checkout).
The command refuses a dirty checkout by default. Record unrelated work
explicitly if you use its `--allow-dirty` option.

Replace the quoted fields with the selected route and contributor details.
Choose a new session name; retain it for the later commands.

```sh
SESSION='<new-session-name>'
python3 scripts/continue_research.py start \
  --session "$SESSION" \
  --problem '<problem number>' \
  --frontier '<exact frontier handle>' \
  --intent '<bounded question>' \
  --stop-condition '<when to stop>' \
  --contributor '<name or handle>'
```

Use `--operator` if the operator differs from the contributor. The optional
`--model-system`, `--provider` and repeatable `--material-collaborator 'Name::Role'`
fields record the identities known at the start; omitted model/provider fields
are recorded as `undisclosed`. For a fork or local mirror, use
`--repository-origin` with the public repository URL to which the return is
addressed. This does not change the recorded starting commit.

The command queries the selected problem and opens a workbench session. It
writes `continuation.json`, `route.json`, `route-memory-consultation.json`,
`route-memory-return-template.json` and the workbench ledger under
`workbench/sessions/$SESSION/`, then prints JSON with the starting commit and
next commands. The route-memory files record which previous routes were
consulted. Keep the generated originals unchanged. `start` does not create the
main `return.json`; [fill and package the return](#fill-and-package-the-structured-return)
after recording the work and its outcome.

## Formal handoff from exposition

Resolve the public navigation handle before filling the bounded route. For a
paper or reviewed packet with a canonical paper label, start at the paper
anchor; for a registered problem-owned note, start at the problem packet:

```sh
# For a reviewed paper or claim packet, use:
python3 scripts/query_corpus.py --paper-anchor <canonical_paper_label>
# For a registered problem-owned note, start with:
python3 scripts/query_corpus.py --route erdos_<number>
# Then continue with the registered note artifact:
python3 scripts/query_corpus.py --publication-artifact erdos_<number>_note
# To enumerate that note's exact paper anchors, use its returned artifact id:
python3 scripts/query_corpus.py --search "erdos_<number>_note::" --limit 100
python3 scripts/query_corpus.py --paper-anchor erdos_<number>_note::<label>
# For source-only #68 or #1041, continue with the module returned above:
python3 scripts/query_corpus.py --module <module-or-path returned by the problem route>
```

The namespaced `<artifact_id>::<label>` handle keeps repeated paper labels
attached to the correct problem note; the [public-evidence return route](../agents/PROOF_STATE_COMPILER.md#return-to-public-evidence)
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
[proof-state public-evidence route](../agents/PROOF_STATE_COMPILER.md#return-to-public-evidence).
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
- **Repository:** `https://github.com/wcook04/plectis-erdos`
- **Repository origin recorded by the continuation session:** `https://github.com/wcook04/plectis-erdos`
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
python3 scripts/query_corpus.py --route erdos_<number>
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

Run the evidence commands on the contributed files. The starting commit
identifies the base of the change; checking out that commit alone does not
reproduce a proposed patch. For a fresh-machine replay, use one new checkout
and keep the supplied package outside it:

```sh
git clone --filter=blob:none https://github.com/wcook04/plectis-erdos '<destination>'
cd '<destination>'
git checkout --detach '<starting commit>'
test "$(git status --porcelain)" = ""
```

Then select the artifact recorded in section 1. For an attached patch, inspect
and apply it to the recorded base, including newly added files:

```sh
git apply --stat '<supplied patch>'
git apply --check --index '<supplied patch>'
git apply --index '<supplied patch>'
git diff --cached --check
git diff --cached --stat
```

For a proposed commit, fetch that commit from the public remote named in the
return, verify that it descends from the recorded base, and select it instead
of applying a patch:

```sh
git fetch '<public remote containing the contribution>' '<proposed commit>'
git merge-base --is-ancestor '<starting commit>' '<proposed commit>'
git checkout --detach '<proposed commit>'
git rev-parse HEAD
```

Stop if the patch does not apply or the ancestry command fails; record the
failure before attempting integration changes. For an exact file attachment,
copy the supplied files to their declared paths in the base checkout and
record their hashes. Record the starting commit and the tested artifact:
proposed commit, patch hash, or file paths and hashes. Do not reset to the
starting commit before running the evidence commands.

Install Lean only when replaying a Lean proof, build or workbench probe. Follow
[the pinned Lean environment instructions](../REPRODUCIBILITY.md#2-reproduce-the-pinned-lean-environment)
for elan installation, the version in `lean-toolchain`, and the dependencies
in `lake-manifest.json`. The dependency cache is an optional accelerator.
A prose review or Python computation does not require Lean unless its recorded
command invokes Lean. Use the dependencies required by that command. Record
the exact parallelism, timeout, and first next action when a replay is bounded
or stops.

List each command actually run, from the repository root, with its exit state.
Do not write `passed` for a command that was not run.

```text
command: <exact command>
exit: <0, nonzero, or not-run>
observed: <short output or failure class>
environment: <pinned toolchain / relevant public dependency>
```

Select the commands relevant to the returned change. For example, a
navigation/documentation change may use
`python3 scripts/check_cold_clone_comprehension.py --quick`, while a problem
route can be inspected with `python3 scripts/query_corpus.py --route erdos_<number>`.
For Lean, include the focused build or replay command and the exact source
module. For a finite computation, include its bounded parameters and script
path. For an inconclusive attempt, include the last completed step and first
next command. Validation of the return's JSON fields does not execute these
evidence commands.

### Fill and package the structured return

Run this sequence in the contributor checkout containing the session opened
above. A recipient replaying only a patch does not need to start a replacement
session or create an accepted receipt.

Choose a new directory outside the checkout for the filled return files:

```sh
RETURN_DIR='../research-return'
mkdir "$RETURN_DIR"
cp "workbench/sessions/$SESSION/route-memory-return-template.json" \
  "$RETURN_DIR/route-memory.json"
```

Write `$RETURN_DIR/return.json` using the
[return schema](schema/research-return-receipt.schema.json) and
[JSON example](../../scripts/fixtures/research_returns/valid_inconclusive.json).
The example is a validation fixture: replace its identity, dates, paths,
evidence and outcomes with the actual work, and use
`"record_kind": "submitted_return"` for a proposed return. Copy the starting
commit, repository origin, question, stop condition and identities from the
session's `continuation.json`; preserve the boundaries recorded in sections
1–3 and 5–7 of this template.

Fill the copied `route-memory.json` with the same `return_id` and the actual
relationship to the consulted routes. Preserve its canonical route-memory
path and digest. Do not edit the generated consultation or return template
inside the session. The packager requires both filled files; it does not
infer them from the source diff or from this Markdown account.

After recording the work and following the clone's consequence-propagation
skill, close the workbench session with an outcome and summary:

```sh
python3 scripts/proof_workbench.py close \
  --session "$SESSION" \
  --outcome '<established|open|abandoned>' \
  --summary '<actual outcome and remaining limitation>'
```

Choose one outcome. `checked_positive` requires `established`, which the
workbench permits only with a kernel-accepted probe and an attributable claim.
`negative` permits `established` or `abandoned`; `inconclusive` permits `open`
or `abandoned`; `corrective` requires `established`. Use the result class supported by
the work, not whichever makes packaging succeed.

Then validate the filled records and their agreement with the opened session:

```sh
python3 scripts/continue_research.py check \
  --session "$SESSION" \
  --return-json "$RETURN_DIR/return.json" \
  --route-memory-receipt "$RETURN_DIR/route-memory.json"
python3 scripts/validate_research_return.py "$RETURN_DIR/return.json" \
  --require-submitted --check-git \
  --require-route-memory-receipt \
  --route-memory-receipt "$RETURN_DIR/route-memory.json"
python3 scripts/continue_research.py package \
  --session "$SESSION" \
  --return-json "$RETURN_DIR/return.json" \
  --route-memory-receipt "$RETURN_DIR/route-memory.json" \
  --output "$RETURN_DIR/package"
```

Run the next command only if the previous command succeeds. `check` validates
session/return agreement but does not require closure; `package` also requires
a closed session with a compatible outcome. Add `--replay` to `check` or
`package` only to rerun stored workbench Lean probes in the current checkout.
It does not apply the proposed patch or run every command listed in
`return.json`.

The package directory must not already exist. The command copies the filled
inputs as `return.json` and `route-memory.json`, copies selected session
records and probe files, and writes `package.json` with file hashes. Keep the
proposed source commit, patch or file attachments beside this directory;
packaging does not copy every changed source file or publish the return.

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
