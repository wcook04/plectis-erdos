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
```

`--search` returns ranked handles. `--ask` expands at most four handles into an
`erdos249257-semantic-slice/1` packet. The latter is the reasoning interface.
It includes the interpreted question operator, semantic cells, a
query-relative witness graph, explicit rejected over-interpretations, and
typed omissions.

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

## Witness slices

Each semantic cell carries its typed handle, the reason it was selected, an
expansion command, and evidence appropriate to its kind. For example:

- a declaration cell contains the signature, source line, pinned Lean
  identity, docstring, and attached claim links;
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

The proof dogfood query recovers two conditional proof sockets and asks Lean to
check a new disjunctive corollary. The corollary states that either of two
unproved supply hypotheses would imply irrationality. It proves neither
supply hypothesis and makes no progress on the open producer problem. This
test measures premise recovery and formal composition, not a solution of
Erdős problem #249.

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
