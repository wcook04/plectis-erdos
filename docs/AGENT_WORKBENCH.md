# Agent workbench

This corpus is agent-native. It is not an autonomous theorem prover and
is deliberately not trying to become one. It is a deep, instrumented
mathematical environment designed to be *inhabited* by an intelligent
agent — a reasoning model or a human — where the agent supplies the
search policy, the conjectures, and the judgment, and the environment
supplies what raw intelligence cannot supply for itself: exactness,
honesty, and replayability.

Use this page for agent operations. Start with [CONTRIBUTING.md](../CONTRIBUTING.md)
before proposing a correction, strengthening, claim change, or release change;
then use the authority and validation contract in [AGENTS.md](../AGENTS.md).
Reader introductions belong in the README and results guide rather than here.

## Design thesis

Every mechanized proof-search policy we examined ends the same way: an
exact core it can fully justify (a kernel receipt, an algebra of
supports and cuts, a leakage-controlled evaluator) wrapped around a
policy layer it cannot (which candidate to probe next, which bridge
shape to invent, which representation to abandon). Systems ordinarily
fill that second slot with heuristics and then defend the heuristics.
We leave the slot open on purpose. The policy slot is occupied by an
agent with actual intelligence, and everything around it is built so
that the agent's work is exact where it must be and auditable
everywhere else.

Three consequences fall out of this inversion:

1. **Instruments, not pipelines.** Each tool here answers one question
   exactly and refuses to answer neighbouring questions it cannot
   ground. Nothing chains them automatically; the agent composes them.
2. **The unit of progress is the receipted session.** A session of
   reasoning — observations, conjectures with declared falsifiers,
   kernel probes, revisions, claims — is recorded as a durable artifact
   that a third party can replay end to end. The repository accumulates
   not just theorems but the audited cognition that produced them.
3. **Authority is structural, not rhetorical.** An agent cannot author
   a kernel verdict. Claims must cite kernel-accepted probe receipts,
   and the notary refuses the record otherwise.

## Eight-problem cold-start route

When a session begins from a problem number, read the matching row in the
generated [problem index](problems.json), then follow the detailed
[source map](SOURCE_MAP.md). The row supplies the question, status, paper
note, module inventory, paper/source coordinates, and open obligations; the
source map supplies the bounded proof/paper/source traversal. The current
mathematical gateways are the eight individual problem papers:

| Problem | Canonical paper |
|---|---|
| #68 | `erdos-68-factorial-denominator-irrationality.pdf` |
| #243 | `erdos-243-reciprocal-tail-rigidity.pdf` |
| #249 | `erdos-249-binary-totient-series.pdf` |
| #251 | `erdos-251-prime-gap-dyadic-series.pdf` |
| #257 | `erdos-257-mersenne-support-subseries.pdf` |
| #269 | `erdos-269-three-prime-running-lcm.pdf` |
| #1041 | `erdos-1041-lemniscate-newton-flow.pdf` |
| #1049 | `erdos-1049-rational-base-lambert.pdf` |

`erdos249-257-main-paper.pdf` and its TeX source are a retired joint manuscript
kept for archive and provenance. Do not use that manuscript as the current
gateway for either problem.

For a machine-readable return from any roster row, run the bounded registry
route before opening a large source file:

```sh
python3 scripts/query_corpus.py --route erdos_<n>
# <n> is one of 68, 243, 249, 251, 257, 269, 1041, or 1049
```

The packet returns the problem question, public status, note, formal module
coverage, and exact open-obligation handles. Follow the matching row in
`problems.json` for its `modules`, `paper`, `note.source_path`,
`note.rendered_path`, and exact open-obligation statements, then use the
[complete eight-problem return matrix](SOURCE_MAP.md#complete-eight-problem-return-matrix)
for the strongest checked source, paper/source record, and exact frontier
route. For #249 and #257, the matrix continues to the reviewed result route
and its registered claim/paper/source reverse links. For #68, #243, #251,
#269, and #1049, use the matrix together with the generated problem-index row:
its `what_is_checked` and `what_is_not_checked` lists expose the complete
checked-result inventory and evidence ceiling, while the matrix supplies the
principal checked module and unresolved producer. These results remain
source-level evidence, not reviewed claim rows. The route is navigation
evidence only; it does not promote problem-owned notes into reviewed claims or
close an open problem.

For the reviewed #249/#257 core, begin with `docs/orientation.json` and one
typed `query_corpus.py` route. For #68, #243, #251, #269, and #1049, use the
corresponding generated row and complete return matrix to reach the
checked-result inventory, principal checked module, paper/source record, and
exact unresolved producer. For #1041, read the dated
[`FRONTIER.md`](../research_corpus/Erdos1041/FRONTIER.md) before its machine
result map: it contains current refutations and surviving premise families
that the older paper note does not enumerate. None of these dispatches
changes problem status or turns source-level records into reviewed claims.

## The instrument panel

Six instruments. Each states the question it answers exactly, then its entry
point.

**Proof-state compiler.** Which candidate applications does Lean actually
accept from this exact goal, and what are the exact resulting obligations?

```sh
python3 scripts/proof_state_compiler.py --pilot-controls
```

**Blocker algebra.** Three non-interchangeable projections: per-plan AND
residuals (`plan_blocker_sets`), smallest additions completing some route
(`minimal_missing_interventions`), smallest removals defeating every known
route (`minimal_blocker_cuts`). Entry: packet fields + `blocker_algebra_semantics`.

**Session notary.** What did the agent observe, conjecture, probe, and
establish — and can a stranger replay it byte-for-byte?

```sh
python3 scripts/proof_workbench.py {open,note,probe,claim,close,replay,show}
```

**Blind harness.** Can a candidate bridge be kernel-checked in a historical
parent environment that provably lacks the future answer?

```sh
python3 scripts/historical_bridge_experiment.py --compact
```

**Static semantic compiler.** Which declarations are structurally relevant to
this goal (nomination only — never applicability)?

```sh
python3 scripts/query_corpus.py
```

**The corpus itself.** More than 150,000 indexed declarations — 8,171 of them
explicitly marked as generated certificate shards (a floor: further emitted
families predate the markers), counted as source rather than as claims —
across the reviewed library, problem-owned expansion, and auxiliary inventory
forest; exact dependency neighborhoods cover both compact roots. Entry:
`Erdos249257/`, `ErdosProblems/`, and:

```sh
python3 scripts/query_semantic.py inventory
```

The corpus is the quiet load-bearing one. This environment is deep
rather than broad: decades-hard problems, attacked far past the first
wall, with the failures formalized alongside the successes. Depth is
what makes probes decisive. When an agent conjectures here, the corpus
usually answers back — with a landed counterexample, a no-go theorem,
or an exact boundary — instead of with silence. A broad shallow corpus
cannot do that.

## The move grammar

A workbench session is a sequence of typed moves in an append-only
ledger (`workbench/sessions/<slug>/ledger.jsonl`):

- `observation` — what the agent read or measured, with sources.
- `conjecture` — a falsifiable guess. Conjectures should declare their
  falsifier; the notary records a warning when they do not.
- `plan` / `interpretation` / `abandonment` — the agent's reasoning,
  recorded honestly, including dead ends.
- `probe` — one Lean invocation. The notary stores the exact input
  bytes and computes the verdict (`kernel_accepted`,
  `kernel_accepted_with_sorry`, `kernel_rejected`) from the Lean exit
  status itself. Probes are the only moves that carry authority.
- `claim` — a statement bound to a cited kernel-accepted probe. The
  notary refuses claims citing anything weaker.
- `session_closed` — outcome plus move accounting.

`replay` re-runs every stored probe and reports whether recorded
verdicts still hold in the current environment. A session whose claims
survive replay is evidence; a session whose claims do not is a detected
drift, which is also evidence.

## The invention ladder

Agent-produced mathematics is claimed at exactly one of three rungs,
and the rung is part of the claim:

1. **Assisted proof.** The agent proved something with full access to
   the corpus. Claim: the theorem, its kernel receipt, and the session
   that produced it. No originality claim beyond what the ledger shows.
2. **Context-blind rederivation.** The agent worked inside the blind
   harness: a historical parent checkout that provably lacks the future
   module and name, with the future identifiers denied from its inputs.
   Claim ceiling: the agent rederived the bridge without access to the
   answer *in its context*. This does not rule out indirect exposure
   through model training; the claim is context-blindness, not
   training-blindness, and must be worded so.
3. **Prospective invention.** The agent proved a theorem that did not
   exist anywhere — in this corpus or its history — when the session
   opened. Blindness holds by construction: there was no answer to
   leak. This is the strongest rung, and the only one that supports the
   word "new".

Rung-3 sessions are the point of the whole design. The first landed
example is the carry-pivot session recorded in
`workbench/sessions/carry_pivot_2026_07_27/`, which produced
`Erdos249257/SuffixCylinderCarryPivot.lean`: the binary carry-pivot
normal form for numeral-adjacent boundary words and the exact
divisor-incidence identity that sharpens the previously landed
coarse `≤ +1` coefficient bound into an equality. The theorems were
derived and proved by reasoning agents inside this workbench, with the
kernel as the only judge, and the session ledger is committed beside
the mathematics.

## Evaluation

The workbench is judged on what it lets an inhabiting agent establish,
measured from ledgers rather than asserted:

- kernel-accepted probes per session, and probes-to-verdict per claim;
- refutation density — how often the corpus falsifies a conjecture
  (high is good; it means probes are decisive);
- ladder rung reached, with its receipts;
- replay integrity — whether closed sessions still verify from their
  stored bytes alone.

## Source-current continuation route: Erdős #1041

The public #1041 corpus is a useful continuation surface for an agent, but it
has a stricter reading order than an ordinary claim route. Read
[`research_corpus/Erdos1041/FRONTIER.md`](../research_corpus/Erdos1041/FRONTIER.md)
before [`STRONGEST_RESULTS.json`](../research_corpus/Erdos1041/STRONGEST_RESULTS.json):
the dated frontier note records which activation rows were refuted on
2026-08-29 and therefore prevents an agent from spending a new session on a
known dead strategy. Use [`CORPUS_MANIFEST.json`](../research_corpus/Erdos1041/CORPUS_MANIFEST.json)
to resolve the complete published file set and its source/public digests.

For a bounded agent session, follow:

1. `AttachmentAwareReeb.md` → `GenericSufficiencyClosure.md` for the
   surviving hub-selection carrier and the generic-to-closed extension.
2. `NearFeketeRadialAngularSplit.md` → `Degree5AssemblyAndSharpenedCuts.md`
   for the current near-Fekete and degree-five residuals.
3. `PartialClusterPreimagePerimeterIdentity.md` →
   `TiedNewtonFaceFibreProduct.md` → `ExteriorRootProductCovering.md` for
   exact perimeter, moment, and covering premises.
4. `MinimalHubArmBudgetRefutation.md` and `SeparatrixAggregateReduction.md`
   for refutation evidence and the surviving machinery whose original target
   has been falsified.

Every step must carry its own hypotheses and evidence class. These files are
source-level research records, not entries in the reviewed `docs/claims.json`
authority. The parent problem remains open; the exact remaining producers are
listed in `FRONTIER.md`. The paper-facing checked route is
[`erdos-1041-lemniscate-newton-flow.md`](papers/full-text/erdos-1041-lemniscate-newton-flow.md),
which leads back to the Lean declaration coordinates without upgrading the
source-only frontier.

## Boundaries

- Ledger notes, rankings, and static nominations are advisory. Only
  kernel receipts assert.
- A bounded search that finds nothing is an abstention, never an
  impossibility claim. Family-level impossibility requires a landed
  theorem.
- Sessions record cognition; they do not certify that the cognition was
  optimal. The honesty is the feature.
- Nothing here claims progress on the open problem statuses tracked in
  `docs/RELATED_PROBLEMS.md` unless a landed theorem says so.

The README is held to a short word budget as the human front door. The two sections below were moved here verbatim so an agent following the front page still reaches the whole-corpus navigation contract.

## Recovered from the front page: read or run it

A single claim can be followed without installing Lean. `verify_claims.py`,
shown above, also prints the Lean proof text, and both it and `--verify-all`
work on a `git clone --depth 1` checkout. Run with no argument it performs an
environment check, which exits `2` and prints `git fetch --unshallow` when a
truncated history cannot reach the gates that read pinned commits; it never
exits `1` in that case, so a shallow clone cannot be misread as a claim that
failed. `check_release.py` remains the authority for locators.

A mathematician can follow the reading order above and then trace one result
from the [SOURCE MAP](docs/SOURCE_MAP.md) into Lean. The per-problem papers
are the live route; the [joint PDF](erdos249-257-main-paper.pdf) is retired.

A coding agent is routed by job description. The clone-local entry router
maps ordinary language to a bounded lane, a minimum read set, and a skill
recommendation, so the agent does not select a workflow file by guessing:

```bash
python3 scripts/agent_entry.py --entry "improve cold-clone skill discovery"
python3 scripts/agent_entry.py --skills
```

The skills work from the clone; `scripts/install_agent_skills.py --list`
previews installing them elsewhere. The agent reading order is
[`AGENTS.override.md`](AGENTS.override.md), then the bounded
[`docs/orientation.json`](docs/orientation.json), selecting one programme or
claim before expanding the registry; [`AGENTS.md`](AGENTS.md) is the complete
reference.

Whole-corpus agent navigation runs without a Lean build.
`python3 scripts/query_corpus.py --tour --format card` and
`python3 scripts/query_corpus.py --route agent_native_corpus_navigation`
expose corpus scale, the mathematical map, the canonical eight-problem map,
the distinct reviewed #249/#257 open-proposition frontier, and authority
boundaries. `query_semantic.py problem-registry` lists every indexed problem
and `structural-backlog` lists authored replacement. Committed indexes expose
every indexed declaration and exact dependencies for both loaded roots;
coverage keeps direct evidence, family context, and structural discovery
distinct. These are navigation projections, not proof authority.

The [proof cockpit](docs/PROOF_COCKPIT.md) produces one cold-clone
status and frontier card (`python3 scripts/proof_cockpit.py`), and
[the Agent Workbench](docs/AGENT_WORKBENCH.md) records typed reasoning moves
and kernel probes under `workbench/sessions/`. The one landed prospective
session,
[`carry_pivot_2026_07_27`](workbench/sessions/carry_pivot_2026_07_27/ledger.jsonl),
produced [`SuffixCylinderCarryPivot.lean`](Erdos249257/SuffixCylinderCarryPivot.lean).
Only kernel receipts assert; ledger notes and static nominations stay
advisory.

For proof-search construction, `hypOf%` lifts an unresolved hypothesis out of
binder position into a `Prop`, so whether a sketch's remaining obligation
differs from the target it started from becomes a question for the kernel
rather than for a rater; this is the failure mode
[AlphaProof Nexus](https://arxiv.org/abs/2605.22763) reports prompting could
not prevent. [Deciding whether a sketch reduced its target or renamed
it](docs/RESIDUAL_PROGRESS.md) documents the evaluator, its eight labelled
fixtures, and what it refuses to decide.
[The proof-state compiler](docs/PROOF_STATE_COMPILER.md) asks the pinned Lean
environment which candidate applications it actually accepts from a goal, and
[the semantic compiler](docs/SEMANTIC_COMPILER.md) nominates declarations
structurally without claiming they apply.

Publication topology is reported by
`python3 scripts/query_corpus.py --publication-architecture` and
`python3 scripts/query_corpus.py --publication-family <id>`.

The [Formal Conjectures crosswalk](docs/FORMAL_CONJECTURES_CROSSWALK.md)
places the corpus against the public benchmark: it binds all eight programmes
to Google DeepMind's Formal Conjectures statements at a pinned upstream
commit, with a SHA-256 per source file and the indexing, ambient-type, and
cast differences a reviewer must inspect. It is statement identity and
adapter-review metadata, not a Lean equivalence proof or a
submission-readiness decision; every row is `not_ready_to_submit`.
[Related problems](docs/RELATED_PROBLEMS.md) places five of the eight
programmes among the neighbouring numbered problems, each external status as
listed on its erdosproblems.com page.

`python3 scripts/check_cold_clone_comprehension.py --quick` checks the
reading surfaces without Lean; `python3 scripts/check_release.py` runs the
full public-surface and query sweep.

## Recovered from the front page: how the repository fits together

The package has two compact supported roots. [`Erdos249257.lean`](Erdos249257.lean)
preserves the reviewed #249/#257 corpus. [`ErdosProblems.lean`](ErdosProblems.lean)
is the problem-owned expansion surface: work lives under its actual Erdős
problem number instead of being forced into the historical #249/#257 tree.
Kernel checking of that second root establishes its exact Lean propositions;
it does not by itself promote them into the reviewed claim registry or claim
that an open problem is solved.

The source has five reader-facing layers. The assembled kernel,
[`CertificateKernel.lean`](Erdos249257/CertificateKernel.lean), contains the
common series machinery, the full-support Erdős-Borwein theorem, named
support-family interfaces, and the unconditional #249 denominator exclusion.
The #249 reduction spine, comprising the period-killer, lcm-diagonal, cone,
diagonal pincer, fresh-loss, and transport modules, turns the open
irrationality problem into exact certificate or avoidance obligations; finite
certificate modules verify explicit parameters and do not supply the
unbounded family required by the reduction. The #257 carry trunk, comprising
the tail-orbit, achievement-set, Boolean-Möbius carry, reciprocal-mass, and
divisor-coverage modules, gives exact criteria and necessary conditions, not
the universal #257 theorem. The navigation layer finds every declaration and
import through the atlas; selected semantic meanings carry scoped reviews
(`python3 scripts/query_semantic.py semantic-reviews`), which are neither
human, novelty, nor proof authority, and the theory lab records nine
mechanisms, nine transfer capsules, and three failure receipts, with four
holdouts that have no results, so no measured transfer is claimed. The
problem-owned expansion, `ErdosProblems/Erdos<N>/`, contains bounded results
and explicit open frontiers for one problem at a time; new entries remain
outside the reviewed claim registry until mathematical review establishes
their intended meaning and public framing.

[SOURCE MAP](docs/SOURCE_MAP.md) gives module order; [METHODOLOGY](METHODOLOGY.md)
governs claim changes; [WAVE INDEX](docs/WAVE_INDEX.md) gives chronology, not
reading order.

## Recovered from the front page: build and verify

Everything above this heading runs with Python alone. Building the Lean source
needs the toolchain, and `lake` arrives with it: install `elan`, Lean's
toolchain manager, from the
[Lean setup guide](https://leanprover-community.github.io/get_started.html).
`elan` then reads [`lean-toolchain`](lean-toolchain) and selects
`leanprover/lean4:v4.29.1`; [`lake-manifest.json`](lake-manifest.json) pins the
matching Mathlib.

```sh
python3 scripts/lean_fast_build.py --jobs 2
```

The wrapper fetches the pinned cache when needed. A focused build uses
`python3 scripts/lean_fast_build.py --jobs 2 [target]`. With restored `.lake`
outputs, `--lake-staleness` makes it trust Lake content traces, not checkout
times. Without a target it checks both roots; `--plan` reports waves without
building. Partial caches stay on that trace-aware path even when a root output
is absent. One verbose no-build verdict identifies the stale frontier, which is
expanded through local import dependents; same-wave targets then share Lake
graph scans in batches capped by `--jobs`.
A cold clone can navigate before this step; formal editing needs the
pinned toolchain. Later builds reuse outputs and rebuild only the selected or
stale dependency cone; `--changed-from <git-ref>` selects changed modules.
The dependency-index validator stores an exact `.lake` receipt: unchanged
inputs make `--check` constant-time; `--check --full-check` forces an audit.

The public release surfaces are checked separately:

```sh
python3 scripts/check_cold_clone_comprehension.py --quick
python3 scripts/check_release.py
python3 scripts/test_methodology_contract.py
```

The pinned public Lean proof corpus contains no `sorry`, `admit`, project-defined
`axiom`, or `native_decide`; finite computations use kernel-checked `decide`.
One deliberate exception is outside the default build:
[`ExternalVerification/Challenge.lean`](ExternalVerification/Challenge.lean)
states the trusted propositions Comparator checks the solution against; they
carry `sorry` by construction.

## Use as a Lean package

The reviewed #249/#257 root is imported with:

```lean
import Erdos249257
```

The problem-owned expansion surface is imported with:

```lean
import ErdosProblems
```

[`examples/Examples.lean`](examples/Examples.lean) is the minimal downstream
consumer; its conditional shell-pressure example leaves the analytic
hypothesis explicit and does not prove universal #257.
