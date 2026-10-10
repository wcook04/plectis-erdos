---
name: maintain-public-infrastructure
description: Dogfood, organize, consolidate, and repair the public clone's agent, query, validation, contribution, credit, and projection infrastructure without depending on private systems.
---

# Maintain the public infrastructure

Use this skill when a clean clone is confusing, a routed workflow is stale or
duplicated, an advertised command only works in an authoring environment, or a
new capability has not reached entry, validation, contribution, and downstream
consumer surfaces. The product is a self-contained public journey, not more
explanatory prose by default.

## Start from the observed journey

Replay the real task before editing:

```sh
python3 scripts/agent_entry.py --entry "<the task as the user or agent stated it>"
python3 scripts/agent_entry.py --skills
python3 scripts/check_cold_clone_comprehension.py --quick
```

Record the expected first lane, the actual lane or failure, and the first file
or command that became unusable. A file existing is not evidence that an agent
can find or operate it. Preserve the exact task as a regression fixture when it
reveals a reusable failure class.

For a request that combines stages, verify the order of the returned skills,
not just whether one relevant skill appears. Test natural modifiers and plural
objects as well as the exact failed wording. Registry `task_intents` can require
an action token and an object token without requiring adjacent words; keep both
conditions so merely mentioning a paper does not select manuscript editing.
Check neighboring tasks that should retain their original lane. Keep purpose and scope separate: a problem or paper identifies the object,
while research, method development or infrastructure work identifies the action.
An existing mathematical proof offered for review belongs to the research-return
lane, which preserves provenance and credit before pull-request preparation.
A request to find or prove a theorem remains research work; a generic pull
request remains contribution submission. Keep all three as route fixtures.
Explicit `agent_entry.py --purpose` must win over words in `--scope`, and the
handoff must retain the original request. Exercise the complete architecture
session, validation and package path as well as the mathematics path; a receipt
schema alone does not prove that contributors can produce a valid return.

For reports that an outside agent missed recent capabilities, inspect the
checkout provenance returned by `agent_entry.py` before repairing the router.
Use `--checkout --check-upstream` for an explicit live comparison with canonical
public main. Never label a cached remote ref, a release tag, or an offline
checkout as latest. Preserve older-clone work and its starting commit; a
different revision is not evidence that the contributor's work is invalid.
When reconciling authored evidence ledgers, compare rows by stable ID against
the common base. Keep independent edits from both branches; regenerate derived
records separately. Replacing a whole ledger to settle one digest conflict can
silently discard valid source bindings.
Keep the human clone/prompt instructions in `docs/agents/README.md`
and the behavioral provenance cases in `scripts/test_agent_entry.py`, which
the release gate already runs. Exercise forks, tags, archives, dirty worktrees,
and unavailable network access without requiring a network in tests. Check the
combined first-contact route budget as well as each entry file: newcomer setup
belongs in the agent index, not in an already full technical reading bundle.

## Design the human reading surfaces

For a public demonstration, replay the smallest advertised action without the
authoring environment. If an existing standalone example avoids a large clone,
make it findable at first contact with a raw-file link, prerequisites, expected
output and the exact boundary of the result. Keep recorded editions pinned;
do not link an HTML source page as a downloadable script. State availability
beside films of private interfaces so viewers know what they can actually use.

For a README or folder index, inspect the rendered page before editing. Keep
one clear opening, a useful first argument and a consistent heading hierarchy.
Use real project imagery with descriptive alt text; retain dates on captured
views. Stack long publication titles on narrow screens and place general setup
before specialized examples. GitHub owns fonts, colours and interaction: use
native Markdown instead of adding a frontend framework to a README.

Keep the claim boundary visible. Collapse supporting inventories, not limitations
needed to understand a result. Preserve existing anchors, manuscript paths and
citation identities; check light and dark modes and phone-width wrapping.
These principles adapt the [pinned Taste Skill redesign guidance](https://github.com/leonxlnx/taste-skill/blob/b482f7a970abb98c4108d4a9f761e458c64cefc8/skills/taste-skill/SKILL.md)
to the public clone; no external skill installation is needed.

Keep the website's maths map prominent in the README opening and link it to the
live map. Keep the explanatory diagram visible near the bottom, before credit
and citation, with its editable source linked. Preserve both visuals when the
reader asks for both; the compact linked reading sequence can remain alongside
them. Recover an earlier refinement from history before redrawing it. Do not
hide either requested visual in a disclosure. Use the requested dark theme for
both the live website capture and the diagram, maintaining readable contrast.
For a rendered diagram,
give arrows a stated meaning, preserve its editable source and inspect the
export at phone width. Keep evidence qualifications beside the relevant labels.

When documenting external review, separate the observed request lifecycle from
local proof or adapter evidence. Record the observation date and public source;
keep individual reviews, aggregate approval requirements and merge state distinct.
The Formal Conjectures crosswalk owns this distinction and its generated guide.

## Separate contribution discovery from mathematical work

For a repository governance or documentation task, verify that entry selects
this maintenance workflow. For finding contribution guidelines or preparing a
finished patch, entry should name `CONTRIBUTING.md` and the submission workflow.
A nearby proof, theorem-status or returned-proof request must retain its own
lane. Preserve these neighboring requests as fixtures alongside the observed
failure; contribution words alone should not turn proof search into Git work.

GitHub [discovers contributor guidelines](https://docs.github.com/en/communities/setting-up-your-project-for-healthy-contributions/setting-guidelines-for-repository-contributors)
from `CONTRIBUTING.md` in `.github/`, the root or `docs/`, in that order. Check
the repository's actual role before copying another project's community files.
A release-only companion can explain how to report a packaging defect locally
and hand mathematical contributions to the primary repository's existing
process. Preserve the commit, exact entry, evidence and requested credit across
that handoff. A community-health score reports recognized files; it does not
certify their content, successful cold-clone use or an accepted contribution.

Replay hosted contribution links in their rendered context as well as checking
clone-local paths. GitHub issue-form Markdown is rendered on `issues/new`, so a
relative link that works beside the YAML source can leave the repository or
point to an issue path. Use public repository file URLs and actual
`issues/new?template=<filename>` form URLs. Preserve field IDs and contribution
or credit boundaries; validate destinations in `scripts/test_contribution_entry.py`
and inspect the rendered form without entering or submitting a report.

## Preserve boundaries across every reader

Claim readers and record checkers share `scripts/claim_relationships.py`.
Resolve both forward remaining-open references and reverse target links, retain
their different meanings, and reject dangling references. Add a registry-wide
coverage regression when a local example exposes lost edges. Read-only adapters
must bind caches and cursors to captured source identity, preserve full
statements, and report unavailable history explicitly for source archives.
`scripts/research_query.py` owns the compact contract; the rich corpus routes
remain owned by `scripts/query_corpus.py`.

## Know the public owner graph

- `skills/registry.json` owns skill families, task lanes, composition edges,
  and complete skill coverage.
- Each `skills/<id>/SKILL.md` owns one executable workflow. Extend an existing
  skill when the work is another step in that workflow; create a new skill only
  for a distinct trigger, owner, validation contour, and output.
- `scripts/agent_skill_catalog.py` validates the registry and owns the generated
  `skills/README.md` catalog.
- `scripts/agent_entry.py` renders the smallest task-conditioned read set. It is
  navigation, not mathematical authority.
- Lean source, `docs/claims.json`, and `docs/methodology.json` retain the
  authority order described in `docs/agents/AGENT_GUIDE.md`.
- `scripts/refresh_projections.py` is the single refresh route for registered
  generated projections. Never repair a generated artifact by hand.
- `skills/erdos-research-return/SKILL.md` owns clone-to-upstream return and
  accepted-receipt assimilation; `skills/propagate-research-consequences/SKILL.md`
  owns downstream dispositions; `skills/submit-pull-request/SKILL.md` owns the
  reviewable Git return.

This map is deliberately compact. Open the owner named by the failing journey;
do not read every registry, graph, paper, or skill as a startup ritual.

Update metadata through its full schema path and artifact role. A manuscript
title and a theorem-environment anchor can both use a key named `title`; a
recursive replacement would change their meanings together. Preserve the
anchor's exact semantic target and run the coordinate builder before stamping
publication metadata.

Validate an immutable source link against the repository and revision named
in the URL: the commit must exist there, the path must exist at that commit,
and the cited line must contain the named declaration.  A filename and line
matching the current checkout or a generated mirror do not validate an older
URL.  When a cited module was added after a paper's global source pin, use an
explicit module-specific immutable pin that has been checked this way.  Do not
move the global pin merely to repair that link unless every pin-relative link
in the paper has been audited at the proposed revision.

When a producer regenerates text cited by `source-attributions.json`, its own
`--check` does not validate that attribution anchor. Run
`python3 scripts/reanchor_source_attributions.py --base <previous-accepted-commit>`
first as a dry run and review each changed excerpt against its recorded
relation. Unchanged excerpts may move with their original digest; changed
implementation evidence needs semantic review before the owner recomputes its
digest. Keep the original advice, identity and credit, and preserve its historical
edition. Do not relabel a quotation or silently extend a reviewed claim.
`--preserve-excerpts` refuses changed content; it is not a way to approve it.
After review, use the same explicit base with `--write`, run
`python3 scripts/build_source_attributions.py` and its `--check`, then refresh
the corpus through `python3 scripts/corpus_substrate.py --write`. Run
`python3 scripts/refresh_projections.py --preflight` before exact-head release
admission. Never hand-edit the generated attribution index or register.

The systems paper also binds source bytes in the authored
`docs/systems_paper_sentences.json` ledger. After changing one of its sources,
run `python3 scripts/systems_paper_evidence.py`; projection preflight alone
does not establish that these bindings are current. Review the affected
sentences and warrants before updating only the relevant source spans and
digests. Preserve evidence classes, reported execution limits and historical
identity; a new digest cannot supply new semantic or empirical evidence.

## Classify before changing

Choose the first matching class:

1. **Routing drift** — the correct skill exists but the task selects another
   lane. Repair task cues or priority in the registry and add the exact task to
   `scripts/test_agent_entry.py`.
2. **Catalog drift** — a skill, family, description, or lifecycle edge exists
   in one surface but not another. Repair registry/frontmatter authority, then
   regenerate the catalog.
3. **Workflow duplication** — two skills repeat the same trigger and outcome.
   Keep one owner, move distinct steps into it, redirect registry composition,
   and remove the redundant surface only after every route and reference moves.
4. **Private dependency** — a public instruction names an untracked checkout,
   private cache, absolute user path, internal service, or ambient memory.
   Replace it with a tracked public command or state the capability is optional.
5. **Projection drift** — source is current but a generated index or adapter is
   stale. Run the owning builder and add its `--check` path to the release gate
   if release could otherwise pass while stale.
6. **Return or credit gap** — useful clone work cannot be proposed, reconciled,
   accepted, attributed, or replayed from public files. Repair the structured
   return/accepted-receipt path; do not invent a private intake dependency.
7. **Propagation gap** — a stable proof, correction, architecture change, or
   accepted return does not reach plausible consumers. Run the consequence
   skill and give each consumer `update now`, `verify unchanged`, or `defer`
   with a reason.
8. **Nominal validation** — tests prove files or tokens exist but do not replay
   the user journey. Add a behavioral fixture and make the ordinary release
   gate consume it.

## Repair through one authority

Prefer consolidation over another guide:

- descriptions live in skill frontmatter and are read by the registry loader;
- organization and composition live in the registry;
- the skill index is generated;
- compact agent entry points to the router and the selected workflow;
- deep guides explain authority and mutation boundaries, not a second routing
  taxonomy.

If two public surfaces must repeat a fact, identify which one owns it and give
the other a route pointer or a generated projection. Do not copy a private
system's full doctrine into this repository; port only the public capability
and the check that proves it works here.

For a public front-door review, examine the complete tracked directory inventory
before proposing moves. Name each area's purpose and owner, and distinguish
authored sources, generated outputs, external inputs and historical evidence.
Review actual responsibilities and dependencies before imposing a conventional
folder name. Classify exact duplicates by their consumers: archived
returns, generated projections, licence texts and test fixtures often need to
remain separate. Improve missing folder indexes before renaming established
proof or publication paths. Keep a real website/map preview linked to its live
route, identify it as a dated capture, and update reader sparse-checkout paths
and image licensing with the asset, including any linked editable source.
Human introductions explain the work;
agent entry gives commands, authority and validation. Verify both journeys at
GitHub reading width and on a narrow screen.

Keep the AI-use disclosure consistent with the papers' production note. A
clearer presentation must not imply independent review, human authorship or
demonstrated understanding that the evidence does not record. Give readers a
bounded argument to explore and a specific correction route.

When reorganising the checkout, keep one shared root `AGENTS.md` and keep
provider adapters limited to loading that entry. Keep the main reader guides
in `docs/`, operational agent guides in `docs/agents/`, specialist checking
instructions in `docs/verification/`, and research/tool records in
`docs/reference/`. Link each guide from its folder index. Preserve stable
machine-readable corpus paths when reorganising reader documents. Preserve root filenames required by Lake, Comparator,
citation and licence tools. A move must update relative links, sparse checkout
manifests, CI, source registries and their builders together. Pinned historical
artifacts retain the filenames belonging to their recorded revision.

Record each proposed consolidation as `keep`, `consolidate` or `archive`, with
its consumers and reason. For a move, write an old-to-new path map and check
imports, links, published URLs, paper IDs and builder inputs before changing
files. Move the content and its live references together, then run the owning
validators. Similar names, age and byte equality alone do not establish that
one copy is disposable.

Apply the same ownership review to commands. Keep cold-checkout release setup
in `docs/REPRODUCIBILITY.md#3-run-the-release-surface-checks`, validation choices
in `docs/agents/AGENT_GUIDE.md#validation`, and committed-branch submission in
`skills/submit-pull-request/SKILL.md`. Other guides should give the appropriate
entry command and link to its owner. Preserve the distinction between the
preparing wrapper, the underlying gate and immutable-snapshot admission; do not
copy their orchestration into another guide or rerun leaves after a full pass.

This ownership review draws on
[Architecture Guardian](https://github.com/PolakiniO/AI-Engineering-Playbook/blob/492387a8572f564f95c2dbe5e67f4b721595518c/skills/architecture-guardian/SKILL.md)
(MIT). The corpus classifications and migration checks above are local rules;
the repository does not need the external skill installed to use this workflow.

## Validate behavior, not decoration

For bulk Git reads, keep request storage separate from response drainage. A
file-backed request stream prevents a large response and queued requests from
blocking each other's pipes. Preserve the clean environment, timeout, exact
snapshot identity and missing-object behavior. Exercise large blobs, many
requests and timeout cleanup; a small successful batch does not rule out the
write contention seen during a full release.

For recurring CI failures, compare the failed run's tested commit and start time
with the repair, and inspect the affected branch as well as the default branch.
An unmerged infrastructure fix does not protect existing branches. Carry the
guard onto an affected branch together with its repair, regenerating that branch's
projections through their owners instead of copying evidence from another branch.
Report branch repair, default-branch rollout and exact-head CI results separately;
do not declare prevention deployed while its pull request is still unmerged.

When integrating concurrent implementations of one owner, reconcile its API,
environment variables and diagnostics before regenerating its consumers. Run
the relevant tests from both parent revisions on the combined implementation;
a clean merge or a passing test from only one parent does not establish that
the combined contract works. For corpus-wide contribution changes, exercise
all eight programmes and each supported contribution track.

When a Python entry point starts another Python script under a sanitized
subprocess environment, use its own `sys.executable` or an explicit pinned
interpreter. Test the child invocation itself: a reduced `PATH` can resolve an
older Python that lacks dependencies available to the parent.

For skill installation, content identity must survive an edit that preserves
file size and timestamp. Exercise the actual preview, check, refused collision
and explicitly forced replacement; metadata equality is not content equality.
Keep the repair compatible with the minimum supported Python version.

For publication growth, conservation means preserving each existing artifact's
identity and download name while admitting newly registered papers. Test a
valid addition as well as a removed or renamed publication; equality of the
old and new inventories would prevent the corpus from growing.

For a README change, follow the
[documentation-check recipe](../../docs/REPRODUCIBILITY.md#check-a-documentation-change).
The cold-clone quick check and the human-first-contact
test enforce different limits: a 14,000-byte first-contact prefix and 2,100
prose words. Run both before the full release gate; passing the quick check
does not establish that the prose budget still fits.

During the edit, run the narrow owner checks:

```sh
python3 scripts/agent_skill_catalog.py --check
python3 scripts/test_agent_entry.py
python3 scripts/test_clone_skills.py
python3 scripts/test_contribution_entry.py
python3 scripts/test_compact_agent_entry.py
python3 scripts/check_cold_clone_comprehension.py --quick
python3 scripts/test_human_first_contact.py
```

Use the exact previously failing task with `agent_entry.py --entry` as a manual
smoke. Before publication, follow the prerequisites in the
[release instructions](../../docs/REPRODUCIBILITY.md#3-run-the-release-surface-checks)
and run `python3 scripts/run_release_check.py` once; do not serially rerun every
component after that full gate passes. Committed-branch submission still uses
the separate admission procedure in `skills/submit-pull-request/SKILL.md`.

A long command is a concurrency window. While it runs, continue only work that
cannot change its inputs or outputs: audit another route, inspect a disjoint
skill family, prepare a fixture, or trace downstream consumers. Never spend the
turn repeatedly polling a build when task-coupled work remains. Lean validation
still goes through `skills/lean-concurrent-validation/SKILL.md`; do not launch a
competing build to look busy.

## Return, assimilate, and propagate

An external contributor normally forks the repository, commits a coherent
branch, pushes that branch to their fork, and opens a pull request asking this
repository to pull the change. A plain-language issue is also valid for an
idea, failed route, or evidence that is not yet a patch.

For research returns, preserve the starting commit, original delta, replay
evidence, claim ceiling, requested disposition, contributor roles, tool/model
provenance, and exact credited paths. Maintainer reconciliation with newer main
is a separate material contribution when it changes the patch. Acceptance is a
committed review decision that creates the accepted receipt and regenerates the
accepted-only recognition views; it is not implied by a passing pull request.

After any stable infrastructure repair, load
`skills/propagate-research-consequences/SKILL.md`. At minimum inspect compact
agent entry, deep agent guidance, skill routing, human contribution entry,
release checks, CI, generated projections, and any query or proof consumer
named by the changed contract. Package or submit only after those dispositions
are explicit.

## Closeout

Return:

- the observed journey and failure class;
- the owner surface changed and any consolidated/retired duplicate;
- the exact behavior fixtures and checks that passed;
- the downstream consumer dispositions;
- commit and publication status; and
- a precise residual only when it cannot be repaired safely in the same scope.

Let the working commands, bounded packets, receipts, and one coherent path show
the system's quality. Do not add praise, inflated claims, or a tour of internal
machinery to prove that the infrastructure is sophisticated.
