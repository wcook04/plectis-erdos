# Semantic query compiler

The query compiler turns a short mathematical question into a bounded set of
typed corpus handles. It does not prove the answer to the question. Its purpose
is to recover the declarations, claim records, open propositions, programme
routes, and source coordinates that a proof attempt or mathematical
explanation must inspect.

The main entry points are:

```sh
python3 scripts/query_corpus.py --vocabulary
python3 scripts/query_corpus.py --search "<text>"
python3 scripts/query_corpus.py --ask "<question>"
python3 scripts/query_corpus.py --goal-support "<Lean or mathematical goal>"
python3 scripts/query_corpus.py --proof-plan "<Lean or mathematical goal>"
```

`--search` returns ranked handles. `--ask` expands at most four handles into an
`erdos249257-semantic-slice/1` packet. The latter is the reasoning interface.
It includes the interpreted question operator, semantic cells, a
query-relative witness graph, explicit rejected over-interpretations, and
typed omissions. It also returns an operator synthesis. This final object
relates the cells without changing their authority: a support synthesis
separates checked consumer signatures from unproved requirements and emits
namespace-qualified `apply <theorem>` tactic candidates that still require
Lean elaboration, an analogy
synthesis records shared claim and open handles while declining to infer a
formal bridge, and a frontier or falsification synthesis preserves the exact
open records and claim ceilings.
Private and local declarations remain navigable as source witnesses, but they
are marked non-addressable and are never emitted as external scratch-module
`apply` candidates.

Goal-support queries use a compact projection of the elaborated Lean types.
For each source-resolved declaration, the dependency index records the number
of outer `forall`/`let` binders, the head constant of the conclusion, and all
constants occurring below that conclusion. The compiler compares those formal
affordances with goal shapes such as irrationality, equality, divisibility,
existence, inequalities, and integer membership. It then combines conclusion
shape with formal-symbol, exact-context, and statement overlap. Ordinary
support questions that contain a recognizable goal shape use the same ranking
and attach the candidate receipt to their semantic slice.

This ranking requires the stored elaborated environment, but it is not Lean
unification and does not establish that a candidate applies. The result
records the extracted goal cues, formal match reasons, and a
namespace-qualified `apply` candidate that must still elaborate in the user's
actual local context.

Declaration cells retain the short authored name for display and carry a
namespace-qualified canonical handle for expansion, witness-graph identity,
and Lean tactic candidates. This matters because the atlas contains many
short names repeated across modules. If an authored module synopsis is the
strongest match for a support question, the compiler performs a bounded local
declaration ranking inside that module so the mathematical organ can lead to
an exact theorem rather than stopping at a file name.

The witness graph is pruned by operator. A support question retains the
claim-to-declaration consumer edges; a frontier or falsification question
retains the open-boundary edges; an analogy retains the programme boundaries;
and a trace or digest may retain the wider argument path. The complete typed
cell remains expandable even when an internal edge is omitted from the
query-relative graph.

## Authority planes

The four provenance planes in a semantic cell are not interchangeable.

| Plane | Owner | What it contributes |
|---|---|---|
| kernel | the pinned Lean source and Lean kernel | elaborated declarations, signatures, and exact source coordinates |
| status | `docs/claims.json` | claim status, argument relations, and the exact remaining-open boundary |
| digestion | declaration docstrings, Lean module headers, and authored paper coordinates | mathematical explanation |
| navigation | `scripts/query_corpus.py` | query translation, ranking, selection, and bounded graph assembly |

A navigation edge is not a theorem. A docstring is not claim-status authority.
A conditional reduction is not promoted to an unconditional result. When an
authored paper is absent from the worktree, its coordinate is returned as
unavailable; the claim and Lean witnesses remain available.

## Problem-owned return routes

The public problem registry is an exact first hop for every indexed Erdős
problem, including the expansion problems outside the reviewed #249/#257
claim programmes. `docs/problems.json` is the registry authority; the query
layer does not infer a problem from a declaration scan or silently promote an
expansion note into a claim.

Use the problem id from that registry as a runnable return route:

```sh
python3 scripts/query_corpus.py --route erdos_68
python3 scripts/query_corpus.py --search "Erdős problem 1041"
python3 scripts/query_corpus.py --vocabulary
```

For each of the eight current registry rows (`#68`, `#243`, `#249`, `#251`,
`#257`, `#269`, `#1041`, and `#1049`), the route packet preserves the exact
question, public status, problem-owned note, formal directory and module
counts, open-obligation ids, and typed semantic follow-up commands. The
packet is a navigation handoff, not proof authority. Expand the matching row
in `docs/problems.json` for the exact paper/source paths and each open
obligation statement; the [complete eight-problem return matrix](SOURCE_MAP.md#complete-eight-problem-return-matrix)
keeps that proof/paper/source crosswalk in one canonical reader surface and
provides the source-to-problem back-route. Then continue the bidirectional
traversal with:

```sh
python3 scripts/query_corpus.py --module <problem-module-path>
python3 scripts/query_corpus.py --paper-anchor <paper-source-or-label>
python3 scripts/query_corpus.py --source <module.lean:line>
python3 scripts/query_semantic.py structural-backlog --problem <n>
```

Module and source packets carry reverse paper-anchor links, while paper-anchor
packets carry formal source links. This makes the route explicit in both
directions: problem → checked/source-owned entry and exact frontier, then proof
or paper → its counterpart. The `note` remains authored exposition,
the Lean module remains the proof-bearing source, and `open_obligations` remain
unresolved regardless of which route selected them. Erdős #1041 additionally
exposes a dated `research_corpus` handoff; read its `FRONTIER.md` before
`STRONGEST_RESULTS.json`, and keep that source-current evidence separate from
the claim registry and Lean proof authority.

The current declaration atlas contains 13 declaration-shaped phrases captured
from inside Lean block comments by its line-oriented builder. The query layer
excludes those exact row ids. `scripts/audit_semantic_corpus.py` strips nested
Lean comments from the source and fails unless the derived false-positive set
is exactly the configured suppression set. The atlas remains the raw
projection until its builder and active downstream projections can be
regenerated together; query summaries therefore report both raw and effective
declaration counts.

## Question operators

The controlled vocabulary defines seven operators:

- `locate` finds an exact typed handle;
- `support` recovers premises or proof sockets;
- `frontier` returns an exact open proposition and nearby reductions;
- `analogy` constructs two subject slices without transporting truth between
  them;
- `trace` follows typed argument and source relations;
- `digest` assembles a bounded formal-plus-authored explanation;
- `falsify` recovers no-go results, measured negative verdicts, and claim
  ceilings.

The vocabulary is deliberately small. It translates a few recurring ordinary
phrases into the corpus terminology and records every expansion in the output.
It is not a second mathematical paper.

The same packet exposes the route-discovery lexicon generated from
`docs/claims.json`. That is the Rosetta source of truth for first-contact
phrasing: each authored term names the typed route it is allowed to select.
A unique exact normalized term may use a constant-time fast path; ambiguous or
unseen language still goes through the visible operator/vocabulary
interpretation and ranked corpus search. The optimization therefore does not
turn undocumented phrase luck into a navigation contract.

## Witness slices

Each semantic cell carries its typed handle, the reason it was selected, an
expansion command, and evidence appropriate to its kind. For example:

- a declaration cell contains the signature, source line, pinned Lean
  identity, docstring, and attached claim links; for `support` and `trace`
  questions it also carries exact direct constant references from the
  elaborated declaration and bounded reverse consumers;
- a claim cell contains the authored status record, formal declaration
  handles, argument neighbourhood, programme ceiling, and remaining-open
  propositions;
- an open-proposition cell contains the exact statement, target claim, and
  the proved or conditional results that narrow it;
- a programme cell contains its mathematical focus, core claims, exact claim
  ceiling, and open propositions;
- a module cell contains the authored `/-! ... -/` synopsis, declaration
  preview, attached claims, and import neighbourhood.

The module synopsis index is generated from the Lean headers:

```sh
python3 scripts/build_module_synopsis_index.py
python3 scripts/build_declaration_atlas.py --check
python3 scripts/build_module_synopsis_index.py --check
```

Its stored source fingerprint must match the declaration atlas. The index is a
performance projection; the Lean header remains the authored source.

The formal dependency index is generated from the imported Lean environment:

```sh
python3 scripts/build_lean_dependency_index.py
python3 scripts/build_lean_dependency_index.py --check
python3 scripts/build_lean_dependency_index.py --check --full-check
```

It separates references in an elaborated declaration's type from references
in its value or proof term, then joins public corpus constants back to exact
atlas source coordinates. Corpus membership follows Lean's owning module
rather than declaration namespace, so declarations intentionally living in
top-level mathematical namespaces remain covered. The builder first runs the
incremental `lake build Erdos249257 ErdosProblems` targets so both supported
compact-root `.olean` environments are current with the source fingerprint.
After an exact full check, a receipt under the ignored `.lake` directory binds
the complete supported Lean source, toolchain and Lake locks, exporter and
builder inputs, declaration atlas and generated manifest, the claim registry's
formal-source release slice, the dependency-extraction helper definitions, and
committed index bytes. The ordinary `--check` reuses that receipt only while every bound byte is
unchanged; `--full-check` deliberately bypasses it. Because CI restores
`.lake`, documentation-only and otherwise unchanged revisions do not repeat
the environment export, while any formal or exporter input change forces the
incremental Lake build and a fresh full export.
The exhaustive declaration inventory remains the route for auxiliary forest
modules that intentionally are not imported into a compact mathematical root:

```sh
python3 scripts/query_semantic.py inventory <text> \
  --module <optional/path.lean> --role <optional-role> --zone <optional-zone>
```

That split is deliberate. Inventory gives every live Lean declaration a source
route without inventing meaning; exact dependency neighborhoods are available
where Lean has loaded the declaration into a supported compact root. Version 3
of the dependency index also stores
compact elaborated conclusion affordances and the unreduced outer binder
telescope used by `--goal-support` and `--proof-plan`. Each binder records its
name, explicitness, type head and constants, and whether Lean classifies its
type as a proposition. The unreduced boundary matters: a conclusion such as
`¬ P` remains a goal with head `Not`; it is not misreported as another theorem
argument. These tables add no Lean invocation to an individual query.

A goal can therefore be routed without knowing its theorem name:

```sh
python3 scripts/query_corpus.py --goal-support \
  "I need to prove totientTail (N + h) - totientTail N is an integer \
from a rational totient series; which theorem applies?"
```

For the pinned corpus this ranks
`tail_diff_int_of_den_dvd` first, with conclusion head `Membership.mem` and
the direct-integer-membership shape. That is an exact navigation benchmark,
not a hard-coded theorem alias or a proof that the caller has its hypotheses.

The proof-plan form makes that boundary operational:

```sh
python3 scripts/query_corpus.py --proof-plan \
  "I need to prove totientTail (N + h) - totientTail N is an integer \
from a rational totient series; which theorem applies?" --depth 4
```

It separates term parameters from proposition obligations, marks the
rational-series equality as a context match, and reports `hdvd` as unmatched.
The plan is therefore blocked rather than pretending the selected theorem is
immediately applicable. For the SharpCurvatureSupply irrationality goal, the
sole proposition binder is context-matched and the exact proof-term spine
includes the curvature non-integrality, period-lcm positivity, and lcm-cone
flatness theorems. Context matching remains lexical navigation; only the
dogfood Lean elaboration validates an application.

Two explicit drilldowns expose longer formal structure:

```sh
python3 scripts/query_corpus.py \
  --proof-cone <declaration> --depth 4 --limit 20
python3 scripts/query_corpus.py \
  --dependency-path <source_declaration> <target_declaration> --depth 8
```

The proof cone follows value/proof-term references, prioritizes theorem-like
nodes inside its byte-bounded selection, and reports exact reachable/emitted
node and edge counts plus the first omitted handles. The dependency-path query
returns the shortest directed path inside the source-resolved value-reference
graph and exact source coordinates for every hop. These are compositions of
kernel-extracted direct edges, not claims that every reference is a decisive
premise or that the path is a causal mathematical explanation.

An ordinary trace question can invoke the same path search without knowing
Lean names:

```sh
python3 scripts/query_corpus.py --ask \
  "trace the formal chain from sharp curvature irrationality to denominator divisibility"
```

For explicit `from ... to ...`, `why X uses Y`, and `X depends on Y` forms,
the compiler searches each endpoint independently, tests the bounded
declaration pairs against the exact value-reference graph, and selects the
shortest path before using endpoint rank as a tiebreaker. The output records
the lexical endpoint alternatives, tested-pair count, selected ranks, exact
path, and authority boundary. Endpoint selection remains navigation: the
kernel witnesses the selected edges, but does not prove that the lexical
interpretation matches the user's intent.

Internal compiler/private references and public constants that cannot be
source-joined are counted as omissions; atlas declarations absent from the
loaded root or owned by a different loaded module are classified separately.

Declaration-local source-use rows remain as a weaker, transparent projection.
They identify theorem or lemma names occurring in a source span and exclude
trailing `#print` audit commands. They are labelled lexical dependency
candidates and never substitute for the elaborated dependency edges.

## Evaluation

The evaluation has three separate levels:

```sh
python3 scripts/benchmark_semantic_reasoning.py --split held_out
python3 scripts/audit_semantic_corpus.py
python3 scripts/dogfood_semantic_proof.py
```

The benchmark checks required-handle recall, operator classification, witness
edges, provenance separation, status fidelity, and packet size. Its held-out
questions are required not to activate any authored vocabulary row. The
reported ranked-search recall is an ablation against the four-result search
surface; compiled recall measures the expanded witness slice.

The corpus audit checks every declaration source coordinate and every curated
claim, open proposition, and reading route. It also expands every typed claim,
open, and route packet, checks all vocabulary hints, and asks one natural
language question for each mathematical programme.

The proof dogfood runs seven tasks. The first recovers two conditional #249
proof sockets and asks Lean to check a new disjunctive irrationality
corollary. The second recovers two sufficient #257 half-membership consumers
and checks their disjunctive composition. The third begins from ordinary
language about a direct dyadic curvature certificate, resolves the authored
module and exact non-integrality consumer, and checks that application. The
fourth starts from a trace question, recovers two exact proof-term
dependencies of the sharp-curvature irrationality consumer, and asks Lean to
check a reconstructed proof using those intermediate theorems rather than the
packaged consumer. The fifth follows the exact three-hop path from that
consumer through lcm-cone flatness and eventual tail periodicity to the
denominator-divisibility theorem starting only from the ordinary-language
endpoint question above, reconstructs the cone-flatness bridge, and uses the
reconstruction inside the curvature proof. The sixth starts only from the
ordinary-language integer-valued totient-tail goal above, selects the exact
formally shape-compatible theorem, and asks Lean to check its application in a
fresh scratch theorem while requiring the plan to expose `hdvd` as missing
from the stated context. The seventh starts from the SharpCurvatureSupply
goal, requires a context-covered application telescope and the exact
three-theorem top-level dependency spine, then validates the reconstructed
curvature chain in the same scratch module. The corollaries prove none of
their antecedents. In particular, they make no progress on the unbounded #249
producer or the open #257 half-membership question. These tests measure
premise recovery and formal composition, not solutions of the Erdős problems.

## Limits

The compiler is query-relative and bounded. It can omit relevant handles; the
packet records the omitted count and gives a refinement command. Lexical and
controlled-vocabulary matching do not replace mathematical judgement. An
analogy cell does not supply a transport theorem, and a support cell does not
assert that its premises are jointly sufficient unless a checked consumer
states that implication.

The benchmark measures the questions encoded in its task table. It is evidence
for those operator and witness contracts, not a claim of general mathematical
omniscience. New proof work should add genuinely different questions and
kernel-checked compositions rather than merely paraphrasing the existing
tasks.
