# Working guide for the problem-centric Lean corpus

This is a navigation guide, not a status ledger and not a proof plan. It
helps a contributor select the right owner surfaces before reading or changing
Lean. Mathematical claim status remains with the proof-bearing Lean source and
the problem-owned `research_packet.json`.

## Jump by task

- [Choose a problem before browsing](#choose-a-problem-before-browsing)
- [Find papers, comparator corpora, or research returns](#route-by-source-kind-not-by-folder-name)
- [Compare owner surfaces and compact frontier routes](#know-which-surface-answers-which-question)
- [Trace mathematical connections without treating them as proof](#trace-mathematical-connections)
- [Organize cross-corpus computation evidence](#cross-corpus-computational-frontier)
- [Route the effects of an existing source change](#route-the-consequences-of-a-source-change)
- [Route an incoming research return](#route-an-incoming-research-return)
- [Plan a focused Lean validation](#inspect-before-building)

## Choose a problem before browsing

New work belongs under `ErdosProblems/Erdos<N>/`; the legacy
`Erdos257PeriodNoncollapse` namespace is shared machinery and a compatibility
surface, not the default home for unrelated problem work. Do not rename
existing compatibility imports as a cleanup step.

For a new agent entering the corpus, start with the compact entry card. It
lists only the known problem IDs and routes to the cockpit, selected or
all-problem frontier overview/detail, computation overview, later source
topology, and the selected problem's bounded evidence neighborhood for papers,
comparator corpora, and research handoffs. Its `recommended_routes` map
distinguishes those entry purposes; it does not open packets or run
computations:

```sh
../../repo-python scripts/corpus_navigation.py --entry --json
```

Choose one listed ID and use its number in the cockpit template before reading
problem-owned material.

Before any ranking, promotion, or "what is our strongest result" pass, read the
generated claim frontier for the problem first
(`docs/formal_math/claim_frontier/erdos<N>.md`, built from
`state/formal_math/claim_frontier_v1.json` by
`./repo-python tools/meta/formal_math/build_claim_frontier.py`); it carries every
programme-carrying claim with its evidence class, altitude, band, prior-art
disposition, publication state and supersessions, and the cockpit's
`claim_frontier` section is its bounded projection.

Every manifest-listed `Erdos<N>/` directory also carries a thin local
`AGENTS.md`. It repeats only the exact cockpit, selected-problem control panel,
research-packet boundary, and supported focused-build plan for that problem;
this guide remains the shared policy surface. The live structure checker
requires those local adapters and their problem-specific coordinates, so a
new problem cannot silently become a directory that is easy to enter only by
broad browsing.

For a selected problem, the default navigation row is a compact control panel:

```sh
../../repo-python scripts/corpus_navigation.py --problem 257 --json
```

Its `problem_navigation_routes` connect the packet frontier, source topology,
bounded source inventory, packet-bound computation coverage, explicitly tagged
corpus computations, focused Lean build plan, corpus structure checker,
supported-root plan, and aggregate axiom-audit plan. These are non-executing
routes; the row does not open a packet, run a probe, build Lean, or infer
mathematical status. Planning the aggregate is distinct from validating the
selected module, and neither plan is a successful build receipt.

From the repository root, ask the problem cockpit for one exact Erdős number:

```sh
./repo-python -m system.lib.mathematical_working_memory \
  --query "Erdos #257" --problem-cockpit --context-budget 12000
```

The cockpit resolves the relevant packet, formal source, open-obligation IDs,
and source coordinates. It is preferable to filename or broad text search at
first contact. Replace `257` with the requested problem number.

## Route by source kind, not by folder name

For one selected problem, the cockpit's bounded `evidence_neighborhood` is
the entry route for material that does not live neatly beside its Lean module:

| Need | Use the cockpit's evidence class, then open the exact returned source |
|---|---|
| Local Lean or executable evidence | `lean_and_executable_sources` |
| Staged papers and publication-adjacent sources | `papers_and_publication_sources` |
| Primary literature | `primary_literature` |
| Public/comparator corpus sources | `public_and_comparator_corpora` and `cross_problem_and_comparator_surfaces` |
| Returned research or handoff packets | `returned_external_research` and `research_handoffs_and_packets` |

The cockpit keeps these routes bounded and representative; it does not turn a
paper, comparator, or research return into a proof or a replacement for the
problem-owned packet and exact Lean declaration. Use the source summary below
only when you need physical file topology after selecting the problem.

For public-corpus or comparator identity, start from the compact registry reader rather
than opening a checkout or the full descriptor:

```sh
./repo-python -m system.lib.formal_math_corpus_registry --json
```

When a problem is already selected, add `--problem erdos_<N> --json`. Every
manifest problem receives the same public-corpus applicability route. A zero-row
result signals registry drift rather than private, unpublished, or lower-priority
status. Select one returned corpus ID and follow its `identity_view_command` or
`paper_view_command`. Those views open only registry-declared descriptor
selectors and retain the separate attachment-verification command. A checkout
candidate is not an identity match; the formal-source commit, navigation
digests, and authored paper artifacts remain distinct authority classes. The
reader projects `codex/doctrine/formal_math_corpus_registry.json`; it does not
replace that registry authority. Public applicability, current attachment
parity, paper coverage, and proof status are separate axes; routing is not
source parity, theorem equivalence, or proof transfer.

The same live entry card supplies a bounded `problem_choices` index with each
problem's owner directory, research packet, and supported Lean module. Use it
instead of opening or scripting over the full manifest:

```sh
../../repo-python scripts/corpus_navigation.py --entry --json
```

These fields are routing coordinates read live from the manifest. Claim-like
manifest state is deliberately omitted from first contact: select the problem,
then use its packet/frontier route for research status and its exact Lean
declaration plus focused validation for proof authority.

For compact source-shape counts across every problem—without opening packets
or emitting every path—use the corpus topology overview. It reports only
owner-directory counts, supported-entry presence, and manifest companion
location categories; it is not a relevance or status ranking.

```sh
../../repo-python scripts/corpus_navigation.py --source-overview --json
```

Each overview row carries a non-executing `source_topology_command` to that
problem's compact `--source-summary` view; use it before opening a large owner
directory or requesting the exact source inventory.

For an all-problem frontier chooser that opens only packet metadata, emits no
target statement or identifier preview, and keeps one row per problem, use:

```sh
../../repo-python scripts/corpus_navigation.py --frontier-overview --json
```

The declared target status and record counts are routing coordinates, not a
ranking, proof status, or mathematical progress measure. Use the row's exact
detail command only after selecting a problem.

## Know which surface answers which question

| Question | Authority / tool |
|---|---|
| What is still open, what was ruled out, and what is the claim ceiling? | `ErdosProblems/Erdos<N>/research_packet.json` |
| Which module is the problem's supported formal entry? | `ErdosProblems/assimilation_manifest.json`, then the module itself |
| What does Lean actually establish? | The exact `.lean` declaration and its focused `lean_fast_build.py` result |
| What reaches all problem-owned modules? | `ErdosProblems/Root.lean` |
| Which assumptions are exposed by the supported aggregate? | `ErdosProblems/AxiomAudit.lean` |
| Which live check validates manifest rows, entry routes, and aggregate wiring? | `../../repo-python scripts/check_problem_corpus_index.py --json` |
| Which compact view compares packet frontiers before selecting a problem? | `../../repo-python scripts/corpus_navigation.py --frontier-overview --json` |
| Which bounded view exposes corpus-wide declaration hubs and connection scale? | `./repo-python -m system.lib.mathematical_working_memory --mode global --query "Lean corpus connection index" --context-budget 12000` |
| Where are papers, comparator corpora, and research handoffs for one problem? | `./repo-python -m system.lib.mathematical_working_memory --query "Erdos #<N>" --problem-cockpit --context-budget 12000` |
| Which computations bear on an open producer? | `./repo-python -m system.lib.formal_math_probe_registry --problem erdos_<N> --coverage` |
| Which corpus-level scripts literally declare a selected problem? | `../../repo-python scripts/corpus_computation_routes.py --problem erdos_<N> --json` |
| Which corpus scripts still lack literal problem metadata, grouped without a 280-row dump? | `../../repo-python scripts/corpus_computation_routes.py --json`, then its `unclassified_role_choices` and `--unclassified-role <role> --path-limit 40 --json` drilldown |
| Which script roles and scopes exist before opening a corpus tool? | `../../repo-python scripts/script_catalog.py`; add `--role <role>` and/or `--scope corpus` before browsing shared tools |
| What axioms does this declaration actually rest on? | `../../repo-python scripts/axiom_audit.py --module <M> --namespace <N> --declaration <d>` |
| A research return just arrived — what might it duplicate, which named boundary should it close, and what moves downstream? | `../../repo-python scripts/assimilation_surface.py --problem <N>` |
| How does a public note relate to a private packet? | `ErdosProblems/EXPOSITION.md` |

Generated reports, computational receipts, and prose labs are useful routing
evidence. They do not replace a kernel-checked declaration or promote a
finite computation into a solution.

## Trace mathematical connections

The entry card's `global_mathematical_connection_index` route exposes a
bounded, live graph view before a declaration is selected:

```sh
./repo-python -m system.lib.mathematical_working_memory --mode global \
  --query "Lean corpus connection index" --context-budget 12000
```

Use its relationship scale and declaration hubs to choose one exact theorem,
definition, or claim. Then rerun working memory in `concept` or `premise` mode
with that exact name to obtain directional candidate prerequisites and
consumers. The global and directional edges are navigation projections with
their evidence classes attached: lexical references, generated families, and
cross-problem analogies are routes to inspect, never Lean dependencies or
mathematical transfers until the exact source and kernel check establish them.

## Cross-corpus computational frontier

The probe registry is the corpus-level bridge from a packet's named open
producers to computation receipts that explicitly bind to them. It is an
organization and coverage surface, not a ranking algorithm or a proof claim.
Run it from the repository root:

```sh
# Start with one compact row per problem: receipt-coverage counts, integrity
# counts, each packet authority, and the exact next drill-down command. This
# does not rank problems or state mathematical progress.
./repo-python -m system.lib.formal_math_probe_registry --overview

# Full cross-problem map of every receipt-to-producer binding and integrity
# finding. Use this only when the compact overview identifies a problem whose
# computational evidence you need to inspect.
./repo-python -m system.lib.formal_math_probe_registry --report

# Restrict the map to one problem when choosing a computation to inspect.
./repo-python -m system.lib.formal_math_probe_registry \
  --problem erdos_257 --coverage

# Inspect only dangling mechanism references and receipts whose declared
# source slice has changed since they were recorded.
./repo-python -m system.lib.formal_math_probe_registry --integrity
```

Use the report to find the right packet and receipt, then read those exact
surfaces. A stale source record is a revalidation prompt for that computation;
it does not by itself revise the problem's mathematical claim status.

Every `--overview` problem row also carries a small
`problem_navigation_routes` bundle. It returns directly to that problem's
cockpit, packet frontier, source topology, and explicitly declared
corpus-level computation sources. Use it to move from a cross-corpus coverage
count back to the bounded owner surface without inferring a priority, result,
or change in mathematical status.

To inventory the locations and filename-level operational roles of computation
sources without running them, start with the compact read-only script catalog
from the Lean project root. Use `--json` only after selecting an inventory
drill-down:

```sh
../../repo-python scripts/script_catalog.py

# Restrict to sources physically owned by one selected problem.
../../repo-python scripts/script_catalog.py --problem 257 --json

# Restrict by filename-level operational role before opening implementations.
# Combine role, problem, and scope filters when the owner surface is known.
../../repo-python scripts/script_catalog.py --role verification --json
../../repo-python scripts/script_catalog.py \
  --problem 257 --role experiment_or_helper --json
../../repo-python scripts/script_catalog.py \
  --scope corpus --role corpus_navigation --json

# Some historical computations still live in the corpus-level `scripts/`
# directory. Start with the all-problem map when organizing those shared
# sources: its summary separates filename-level roles with and without a
# literal `problem_id` declaration. An untagged role can be a legitimate
# shared helper, so this is a routing/completeness observation, not a request
# to add metadata or a status judgment.
../../repo-python scripts/corpus_computation_routes.py --json

# After choosing a problem, find only corpus-level scripts that literally
# declare its ID. Each compact row includes their catalogued role counts before
# listing representative paths, without guessing from filenames or running a
# script. It also supplies problem_cockpit_command for that problem's bounded
# papers, comparator, and research-handoff neighborhood. Its
# computation_surface_routes keeps physical ownership, literal metadata, and
# packet-bound probe receipts separate:
../../repo-python scripts/corpus_computation_routes.py --problem 243 --json

# Join the manifest's supported Lean entry, packet authority, problem-owned
# computation source counts, and any locally staged TeX source routes.
# A TeX route is only a source-location fact; it does not indicate publication
# state, mathematical status, or freshness of an exposition.
../../repo-python scripts/corpus_navigation.py --problem 257 --json

# For a minimal all-problem frontier chooser, first use --frontier-overview.
# It gives packet title, declared target status, record counts, the exact
# frontier-detail command, and a selected-problem cockpit command for bounded
# papers, comparator-corpus, and research-handoff routing—without target
# statements or identifier previews.
../../repo-python scripts/corpus_navigation.py --frontier-overview --json

# Then get packet-owned frontier detail only for the selected problem, or use
# the all-problem detail view when a cross-packet audit is necessary: its
# stated target, open-producer IDs (a representative preview), and counts of
# packet records, including named exact- and negative-result previews. This
# relays source fields; it does not rank work, infer
# progress, or change the packet's claim ceiling. Pass --problem to expand
# only that packet's complete open-producer, exact-result, and negative-result ID lists.
# Each row also supplies exact commands for the cockpit, source topology,
# complete source inventory, packet-bound computation coverage, explicitly
# tagged corpus-level computations, and a read-only plan for the manifest's
# supported Lean entry. These are routes to inspect, not results or builds.
../../repo-python scripts/corpus_navigation.py --frontier-summary --json
../../repo-python scripts/corpus_navigation.py --problem 257 --frontier-summary --json

# Before reading a large problem directory, get its compact source topology:
# owner-file counts, the supported Lean entry, and any manifest-declared
# companion modules that physically live in a shared/legacy namespace.
# This is a location map, not a ranking or a status report.
../../repo-python scripts/corpus_navigation.py --problem 257 --source-summary --json

# The selected summary supplies problem_cockpit_command for the bounded papers,
# comparator, and research-handoff neighborhood, plus source_inventory_command
# when the exact Lean, Markdown, and problem-owned script paths are needed.

# When returning to an existing problem, enumerate its exact Lean, Markdown,
# and problem-owned computation source paths without a broad repository search.
# This is an inventory of locations, not a relevance ranking or status report.
../../repo-python scripts/corpus_navigation.py --problem 257 --source-paths --json
```

This is a filesystem map for choosing a source to inspect. Its roles classify
how a file is used for navigation, not the strength of its mathematical
evidence: `verification` is a script role rather than Lean proof authority,
and `experiment_or_helper` output remains finite computational evidence. The
probe registry above maps mechanism-bound receipts instead; neither surface
infers a mathematical result.

## Audit axioms before recording a proof claim

`grep -c sorry` over a source file is not an axiom audit. It false-positives on
the word "admit**s**" in a docstring, and it says nothing about a `sorry` reached
through an import. `grep -ac sorryAx` over one `.olean` is better but still
local to that module. The check that means something is `#print axioms`, which
follows the whole dependency closure.

```sh
../../repo-python scripts/axiom_audit.py \
  --module ErdosProblems.Erdos243.CumulativeLcmTransfer \
  --namespace ErdosProblems.Erdos243 \
  --declaration cumulativeOverlapDebt_dvd_tailNumerator \
  --declaration lcmFresh_pairwiseCoprime
```

It reports one line per declaration against `{propext, Classical.choice,
Quot.sound}` and exits 0 only when every requested declaration is clean.

**A deferral is not a pass.** `lean` and `lake` here are shimmed through
`tools/meta/control/lake_command_guard.py`, and the host firewall allows one
concurrent Lean process. Under contention the guard returns exit 75 or 241, or a
JSON command-future payload, with *empty* diagnostics — which reads like a broken
tool rather than a queue. **Do not retry in a loop**: each deferred
attempt spawns a command future that consumes the capacity the next attempt
needs, so a tight loop lengthens the queue. Wait, then run once. The audit reports that as `status: deferred` with an
empty `audited` list, never as success, and always prints the launch context
(project root, toolchain, guard behaviour, re-entry condition) so a deferred run
can be resumed rather than rediscovered. Only `status: clean` licenses writing an
axiom claim into a packet, a claim-frontier row, or a comparator entry.

## Route an incoming research return

`corpus_navigation.py` answers what a problem owns and the claim frontier
answers what it claims. Neither answers the question an agent actually has when
a Type B return arrives: what already exists that this return might duplicate,
which named boundary it is supposed to close, and which downstream surfaces have
to move if it lands. That answer used to require reading the packet, grepping
the Lean tree, listing the return-batch capsules, opening the claim frontier,
scanning the comparator directories and running the probe registry — six
surfaces that do not point at each other.

```sh
../../repo-python scripts/assimilation_surface.py --problem 1049
../../repo-python scripts/assimilation_surface.py --problem 1049 --json
```

The card joins, for one problem: Type B return-batch custody (with the exact
`verify` command); the packet's declared Lean boundaries, gathered recursively
from nested `claim_boundary` and `authority_boundary` fields rather than only
top-level keys; claim-frontier rows split into Lean-backed and not, with the
evidence-class upgrade candidates named; the per-family Comparator directories
and any Palomar-required file each is missing; probe receipts bound to the
problem's mechanisms; and the ordered downstream commands.

Read `declared_lean_boundary` before the return's own summary. A return that
does not close a named boundary is adjacent work, not an assimilation. The card
opens no Lean, runs no build, and never decides whether a return is correct,
novel, or already known — the packet, the exact declaration and its focused
build remain the authorities.

Before deep reading, give the return byte custody:

```sh
./repo-python tools/meta/bridge/type_b_return_intake.py open --batch-id <id> \
  --campaign "<what these returns are>" --evidence-boundary "<what they are not>"
./repo-python tools/meta/bridge/type_b_return_intake.py add --batch-id <id> \
  --return-id <return> --source <path>
```

A return with no capsule row has no custody, and compaction can erase the
source boundary that tells a later reader what the bytes were.

## Route the consequences of a source change

After changing a Lean module, experiment receipt, or research-state document,
compile a source-current consequence map before deciding which packet,
exposition, or dependent module needs attention:

```sh
./repo-python -m system.lib.mathematical_consequence_map \
  --query "route this landed formal-math change" \
  --changed-path formal_math/erdos257_period_noncollapse/ErdosProblems/Root.lean \
  --context-budget 12000
```

Replace `--changed-path` with the exact changed path and repeat the flag for
multiple paths. The map supplies candidate consumers and related authority
surfaces from source structure; it is navigation evidence, not an inferred
mathematical consequence or a publication decision.

## Inspect before building

Run these commands from `formal_math/erdos257_period_noncollapse`.

```sh
# Confirm that the manifest, packets, declared modules, and supported root
# still agree before or after an organizational change.
../../repo-python scripts/check_problem_corpus_index.py --json

# Show the exact local import cone and bounded prebuild waves; does not build.
../../repo-python scripts/lean_fast_build.py --plan \
  ErdosProblems.Erdos257.HalfCounterexampleFrontier

# Build one selected proof-bearing target.
../../repo-python scripts/lean_fast_build.py --jobs 2 \
  ErdosProblems.Erdos257.HalfCounterexampleFrontier

# Integration target for the supported problem-owned root.
../../repo-python scripts/lean_fast_build.py --jobs 1 ErdosProblems
```

The current #1041 supported-root route includes the existing modules
`Erdos1041.NewtonFlowRaySeparation`, `Erdos1041.LevelSeparation`,
`Erdos1041.CassiniTreeBudget`, `Erdos1041.CubicCriticalHub`,
`Erdos1041.NearFeketeHubOrbit`, `Erdos1041.CriticalTwoRootProximity`,
`Erdos1041.BarycentricEnvelope`, `Erdos1041.BarycentricTargetDisc`,
`Erdos1041.ConnectedClusterAreaForcing`,
`Erdos1041.CriticalEllipseMinimaxStationarity`, and
`Erdos1041.GenericSufficiencyClosure`. These names expose existing source
files; the problem packet remains the authority for their claim ceilings and
open boundary.

Replace the example module with the module chosen from the manifest or
cockpit. Do not run a focused build and the aggregate `ErdosProblems` build at
the same time. Exit `75` from the wrapper means the build is already owned or
capacity-deferred; it is not a theorem failure.

## Keep changes legible

- Put a new problem-specific Lean module, lab note, or script in its
  `ErdosProblems/Erdos<N>/` owner directory when it has one.
- Update the owning packet or manifest only through their established
  maintenance lane; they are live status authorities, not incidental docs.
- Keep a narrow Lean module build as the validation receipt for a scoped code
  change. Treat the aggregate root build as separate integration validation.
- Keep `Root.lean` and `AxiomAudit.lean` as explicit aggregate surfaces; do
  not make a convenience import silently become the public claim boundary.

For the problem-by-problem mathematical map and live throat descriptions, see
the parent [`README.md`](README.md). For broader repository setup and the
build-wrapper contract, see [`../README.md`](../README.md).
