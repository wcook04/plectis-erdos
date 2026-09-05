---
name: maintain-public-infrastructure
description: Dogfood, organize, consolidate, and repair the public clone's agent, query, validation, contribution, credit, and projection infrastructure without depending on private systems.
---

# Maintain the public infrastructure

Use this skill when a clean clone is confusing, a routed workflow is stale or
duplicated, an advertised command only works in an authoring environment, or a
new capability has not reached entry, validation, contribution, and downstream
consumer surfaces. Repository cleanup, bootstrap friction, and architectural
simplification belong here too. The product is a self-contained public journey, not more
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

Replay ordinary contributor wording as well as owner terminology. A route that
recognizes "architecture" but misses "clean up duplicated workflows" is not
discoverable enough. Add focused registry cues and pair each repair with a
nearby explanation or proof task that must keep its existing lane.

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
  authority order described in `AGENTS.md`.
- `scripts/refresh_projections.py` is the single refresh route for registered
  generated projections. Never repair a generated artifact by hand.
- `skills/erdos-research-return/SKILL.md` owns clone-to-upstream return and
  accepted-receipt assimilation; `skills/propagate-research-consequences/SKILL.md`
  owns downstream dispositions; `skills/submit-pull-request/SKILL.md` owns the
  reviewable Git return.

This map is deliberately compact. Open the owner named by the failing journey;
do not read every registry, graph, paper, or skill as a startup ritual.

## Module graphs, labels, and projection freshness

For module dependency inspection or graph maintenance, start with
`python3 scripts/build_module_graph.py --check`. The graph lives at
`docs/claims.json::machine_readable_paper.module_graph`: Lean source owns paths
and import edges; each node's `role` is authored navigation metadata. The
builder preserves existing roles and supplies defaults for new nodes.

Correct a role at that authored field. Change an import in Lean source, then
run `python3 scripts/build_module_graph.py` to derive the graph; do not repair
an import edge by editing the JSON. Lean edits also require focused validation
through `skills/lean-concurrent-validation/SKILL.md`. A clearer label does not
change the corresponding theorem or claim status.

For broader stale projections, use
`python3 scripts/refresh_projections.py --check` to identify the failing owner.
After the source correction, `python3 scripts/refresh_projections.py` runs the
registered builders in dependency order. Claim their output paths first in a
shared checkout. Do not regenerate unrelated projections over another
contributor's work. Use the changed module's
`python3 scripts/query_corpus.py --connections <module>` packet to verify that
its downstream navigation still resolves.

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

## Make the architecture easier to use

Judge elegance by what the next contributor must understand and coordinate.
A good repair removes a decision, a duplicate owner, a hidden dependency, or
an opportunity to enter inconsistent state. Visual polish alone does not do
that work. Keep one ordinary route for a task, put complexity behind its owning
component, and expose a recovery action when that component cannot proceed.

Before introducing an abstraction, identify the repeated behavior it replaces
and its lifetime. For example, a committed reader may share immutable bytes
after pinning a revision; a live worktree or staged-index reader must still see
edits. Keep fixture overrides explicit and ahead of shared reads. Do not make
callers learn a cache protocol to obtain correct source identity.

After a repair, replay the workflow from a fresh contributor's position:
can they find the right skill, run the default command, understand its result,
and take the next action without consulting another parallel guide? Simplify
the owning route when the answer is no.

## Remove measured delays

Start with commands that take more than a second. Measure the same task and
input before and after; aim to bring interactive commands below one second
before polishing already-fast paths. Keep the original output or compare its
structured meaning, and retain the adversarial cases that protect the boundary.

For a release in a shared checkout, use
`python3 scripts/check_release_ref.py --ref HEAD --receipt .validation-singleflight/release-head.json`.
Its receipt records elapsed time for every gate, including timeouts. Profile
the slow gate next. When profiling `check_release.py` itself, its normal entry
dispatches through singleflight: profile the worker inside a disposable clean
snapshot so the measurement covers validation rather than receipt collection.
Do not bypass singleflight to launch competing builds in the working checkout.

Look for repeated file parsing, repeated index construction, serial Git
subprocesses, and duplicated validation ownership before adding concurrency.
JSON loaders can decode UTF-8 bytes directly instead of translating newlines;
verify exact output equivalence. Batch known immutable Git reads through the
reader that owns the snapshot. Test binary framing, missing paths, moving refs,
and live index/worktree changes when changing that boundary.

When many fixtures consult one historical checkpoint, share its small derived
summary within the reader's lifetime instead of rebuilding or retaining the
whole atlas. Return a copy to each consumer. Reuse only successful immutable
identities: missing objects can be fetched, symbolic refs can move, and a new
reader must observe the repository again.

Use profiler output to locate repeated work, then measure ordinary wall time:
instrumentation can exaggerate a hot loop with hundreds of thousands of calls.
For a text scanner, compare the old and new results over real inputs and
adversarial grammar cases. A literal candidate search may avoid scanning large
payloads with a regex, but must preserve the original match, escape, duplicate,
and non-overlap rules. Faster extraction does not justify skipping validation
or recovery checks.

Reject an optimization when its measured saving does not justify its extra
passes or abstraction. A successful microbenchmark is not sufficient: prefer
removing a multi-second delay from the actual journey over complicating an
already-subsecond component. Keep the evidence and remove the unused approach.

For large generated JSON, first separate the data a command needs from the
exhaustive export. Prefer a small byte-range index in an existing owner receipt
over duplicating the corpus or adding another command. Bind ranges to the exact
output bytes, validate their boundaries and member digests, and retain source
freshness checks. Missing or unusable indexes should fall back to the ordinary
reader. Compare indexed and complete reads across the affected command family;
regenerate dependent input-digest receipts through their own builders.

When filtered inventory still parses an exhaustive array, check whether its
rows already form contiguous groups. A compact range table can select those
groups without a second dataset. Keep selection labels inside the canonical
digest boundary, check complete range coverage, and compare substring, case,
empty-result, and combined-filter behavior with the full reader.

## Validate the changed journey

During the edit, run the narrow owner checks:

```sh
python3 scripts/agent_skill_catalog.py --check
python3 scripts/test_agent_entry.py
python3 scripts/test_clone_skills.py
python3 scripts/test_contribution_entry.py
python3 scripts/test_compact_agent_entry.py
python3 scripts/check_cold_clone_comprehension.py --quick
```

Use the exact previously failing task with `agent_entry.py --entry` as a manual
smoke. Before publication, run `python3 scripts/check_release.py` once; do not
serially rerun every component after that full gate passes.

In a shared checkout, validate the committed result with
`python3 scripts/check_release_ref.py --ref <commit>`. If another contributor's
inputs change during a projection refresh, use an isolated committed checkout
to distinguish the intended output from concurrent edits. Compare structured
fields before assigning the cause of drift. Regenerate through the owner and
land only the verified change; a failed aggregate gate can expose an earlier
missing refresh rather than a defect in the current patch.

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

Carry each reusable lesson into this public skill or the more specific public
owner skill during the work. State the trigger, the correct action, and the
boundary that prevents misuse; do not accumulate dated benchmark logs here.
Keep measured evidence with the change. A private note or conversation summary
does not make the lesson available to the next public-clone contributor.

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
