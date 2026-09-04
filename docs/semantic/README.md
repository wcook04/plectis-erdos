<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# The semantic corpus layer

This directory owns a bounded answer the repository could not previously give
without being reread: **what does the selected interpreted subset state, and
how are those statements recorded as relating to each other?**

## Why it exists

The repository had the two ends of a three-layer stack and nothing in the
middle.

```
Lean source
    ↓  structural extraction
docs/declaration_atlas.json          exhaustive declaration inventory
    ↓  exact structural families + authored interpretation   ← THIS DIRECTORY
docs/semantic_corpus.json            statement nodes, typed relations, coverage receipt
docs/semantic_corpus_check.json      content-addressed fast-check receipt
    ↓  selected_as
docs/claims.json                     curated ledger: 100 reviewed claims
    ↓  rendered_as
problem notes · README · packets
```

The atlas knows that a declaration exists. The claims ledger knows that 300
declarations were reviewed and published. Neither knows that a theorem is a
reformulation of the open problem, that a finite computation instantiates an
infinite family nobody has proved, or that a barrier closes two engines and
leaves a third alive.

That last one is not hypothetical. A parity obstruction on the squarefree
support was carried to the edge of publication as closing the block-certificate
engines for Erdős #257. A third, weaker engine — the low-carry socket — existed
in the same file, was not closed by it, and was found by accident. Nothing in
the repository could have caught the error, because no surface recorded which
engines existed or what a barrier reached. This layer records it, and
`scripts/check_semantic_corpus.py` fails if a barrier node does not say what it
fails to rule out.

## What is here

| path | role |
|---|---|
| `zones/<zone>.json` | **authored.** Per-zone statement nodes, declaration roles, intra-zone edges |
| `relations_<lens>.json` | **authored.** Cross-zone typed edges, one file per relation lens |
| `frontier.json` | **authored.** Open antecedents, engine hierarchies, nonrecurring candidates |
| `reviews.json` | **authored.** Digest-bound reviews for selected nodes and relations |
| `../semantic_corpus.json` | **generated.** The merged graph plus coverage receipts and views |
| `../semantic_corpus_check.json` | **generated.** Content-addressed input, output, and public-census freshness receipt |
| `../generated_certificate_manifest.json` | **authored.** Which modules are emitted, and the schema each instantiates |

## The two objects

A **statement node** is one selected mathematically distinct statement — not
one declaration, and not one theorem family. Several declarations that
establish the same content in different dress may share a node. It carries a
canonical prose statement, its evidence declarations, its logical class, its
problem membership, the open antecedents it still depends on, its prior-art
state, and for barriers a mandatory scope caveat.

The graph has two interpretation tiers. Every theorem or lemma has exact
source-structural linkage: declarations in the same module with the same
normalised Lean proposition schema share a generated structural-family node.
That makes the long tail discoverable without guessing mathematics from names.
It is not an authored paraphrase.

Above that floor, authored statement nodes record mathematical interpretation.
Their declaration links are reported in two subtiers: exact proposition
evidence and contextual participation in a bounded family such as a
digest-verified certificate roster. A declaration routed only through a
source-structural family remains locatable but not mathematically interpreted.
The generated coverage receipt keeps all three populations separate.

A **relation** is a typed mathematical edge with a required evidence basis.

Two relation classes are deliberately kept apart, and conflating them is the
main way this layer could go wrong:

- **Proof dependency** — Lean theorem `A` was used in the proof of `B`. This is
  structural, it is machine-extractable, and it lives in the module and
  argument graphs inside `claims.json`.
- **Mathematical relation** — `B` specialises, reformulates, transports or is a
  finite instance of `A`. This is semantic. Premise extraction cannot infer it.
  It lives here and every edge must name its basis.

## Equivalences are preserved, not deduplicated

The tempting move is to collapse the corpus by merging everything provably
equivalent. Do not. The equivalences and transports *are* the associative
structure this layer exists to expose; they are what a later interpolation
process has to reason over. A restatement is not noise to be deleted, it is an
edge to be labelled.

Collapsing happens in **views**, which are projections over one graph, never
separate sources of truth:

- `publication` — quotient aliases and definitional duplicates, collapse each
  generated family to a single node, keep object theorems, scoped barriers and
  classical formalisations.
- `research` — every node and every edge.
- `audit` — every declaration with its typed route, plus an owning node where
  statement-level interpretation is present.
- `frontier` — open antecedents, bare equivalences, unblocked sibling engines.
- `nonrecurring` — a mechanically filtered candidate pool inside the selected
  graph. Its much shorter `reviewed_shortlist` is the adjudicated set; neither
  is a novelty claim without external prior-art review.

Non-recurring candidates are therefore a **query**, not a hand-maintained list
that silently rots:

```sh
python3 scripts/query_semantic.py nonrecurring --problem 257
python3 scripts/query_semantic.py barriers
python3 scripts/query_semantic.py coverage
python3 scripts/query_semantic.py problem-registry
python3 scripts/query_semantic.py paper-coverage
python3 scripts/query_semantic.py population-backlog
python3 scripts/query_semantic.py population-backlog --paper erdos249-totient-reasoning-surface
python3 scripts/query_semantic.py structural-backlog --problem 257
```

The semantic graph is an interpretation layer, not a replacement for
problem-owned evidence. For public problem → strongest checked result → paper
or source record → exact frontier traversal, start at the canonical [complete
eight-problem return matrix](../SOURCE_MAP.md#complete-eight-problem-return-matrix).
It is also the reverse route for a semantic reader: use
`python3 scripts/query_corpus.py --source <module.lean:line>` or
`--paper-anchor <TeX_label_or_source_ref>` to recover the corresponding claim
or problem row, then resume with the row's open-obligation handle. For example,
the #249 `probabilistic_gcd_geometry` family returns through that matrix to
the exact gcd-moment and Stern–Brocot declarations, paper anchors, and the
still-open irrationality boundary.

For exact external statement identity, use the generated [Formal Conjectures
crosswalk](../FORMAL_CONJECTURES_CROSSWALK.md). Its eight rows bind the pinned
upstream declaration and source hash to the matching local problem route, so a
semantic interpretation can be checked against primary statement evidence
before it is treated as a local result.

For module-level traversal, use
`python3 scripts/query_corpus.py --module <module_path_or_sigil>`. A source
path selects the exact Lean module; a paper sigil selects the same module from
the paper-facing alias table. The packet returns the authored synopsis,
declaration preview, source identity, attached claims, and any bound
route-memory context before the reader drills into a declaration or source
coordinate.

For relation-aware traversal around one ranked family, use

```sh
python3 scripts/query_semantic.py family-relations first_harmonic_pivot_decomposition
python3 scripts/query_semantic.py family-relations fixed_precision_transport_no_go
```

This packet projects Palomar's canonical `programme_family_order` and
`family_relations` into a bidirectional neighborhood: outgoing and incoming
prerequisites, supports, conditional endpoint peers, and contrary evidence.
Each peer retains its exact source and wrapper declarations, mechanism,
summary, and open boundary, so a reader can follow the relation without
mistaking it for a new claim or proof authority. `stronger_peers` and
`weaker_peers` are derived from the canonical programme position; relation
array order never supplies rank. This is a navigation projection, not a
parallel ranking store, and its exhaustive `relations` list preserves the
long-tail drilldown.

### Problem-to-family return packets

The public problem route is the bounded return surface for every indexed
problem, not just the reviewed #249/#257 graph. Run

```sh
python3 scripts/query_corpus.py --route erdos_<problem_number>
```

for one of #68, #243, #249, #251, #257, #269, #1041, or #1049. The packet
returns the authored paper record, every review-matrix result family in its
recorded order, each family's evidence mode and claim ceiling, declaration
expansion commands where the authority record supplies them, and the full
open-obligation statements. Use `--format card` for the compact family/paper/
frontier summary, then expand a declaration or source coordinate with the
corresponding `query_corpus.py` handle. These family rows are navigation
context from `docs/claims.json`; they do not promote expansion material into
reviewed claims or close an Erdős problem.

To enumerate the exact anchors in a dedicated problem note, take its
`paper.source` from the packet and run

```sh
python3 scripts/query_corpus.py --paper-source paper/erdos-<number>-<slug>.tex
```

This bounded discovery packet lists every section, theorem, proposition, and
allowlisted result anchor found in that paper, with an exact
`--paper-anchor <canonical_handle>` follow command for each one. It is an
exposition-navigation projection: Lean source remains proof authority, and the
claim registry remains the authority for claim status and result-family
boundaries. Searching an exact review-matrix family id likewise returns its
ranked family row with the problem route and dedicated-paper source route.

`population-backlog` is the semantic authoring queue.  It scans every authored
paper, resolves both public `\lword` links and reasoning-surface `\lean` links
to exact live declaration roles, deduplicates qualified and short spellings,
and ranks paper-selected declarations that still lack an
`authored_statement` interpretation. A structural-family link therefore stays
in the backlog rather than making it disappear. A paper citation nominates a
target; the Lean signature and proof cone still decide the authored statement.
The command does not promote helpers automatically or treat a larger node
count as quality.

`problem-registry` is derived from the canonical public problem index rather
than from a hardcoded #249/#257 specimen. It joins every indexed problem to its
modules, authored note, open obligations, declaration routes, semantic nodes,
and exact follow-up commands. `structural-backlog` then ranks the lower-tier
families that still need authored interpretation: paper-selected roles first,
then larger exact source modules. Its replacement hint is an anti-filler
contract, not an invitation to paraphrase declaration names.

## Prior art is staged, never a boolean

`prior_art_state` is never inferred from Lean. Kernel checking establishes that
a proposition was proved; it establishes nothing about novelty. The states run
`not_assessed → known_classical | formalisation_only |
routine_corollary_or_specialisation | candidate_new_statement →
external_review_pending → externally_supported_as_new | prior_art_found`, and
the default is `not_assessed`.

External status is time-stamped for the same reason. Tao and Teräväinen settled
`∑ ω(n)/2ⁿ` in December 2025, which moved every prime-support statement in
#257 from frontier to cited prior art without a line of Lean changing. A live
registry has to absorb that; a PDF cannot.

## Review receipts are stronger than authorship

Authored wording, a confidence label, and a nonempty relation basis do not prove
that the wording was checked against its cited Lean signatures. Selected
high-value nodes and relations can therefore carry a receipt from
`reviews.json`. The receipt is bound to the formal-source revision, the
declaration-atlas fingerprint, and a digest of the exact semantic subject.
Changing the statement, evidence, relation label, endpoints, or basis makes the
builder fail until the subject is reviewed again.

The receipt records its reviewer type and claim ceiling. A Type A model review
is represented as a source-to-wording consistency review, never as independent
human mathematical review, Lean proof authority, or a novelty judgement.
Unreceipted nodes remain authored navigation. Use
`python3 scripts/query_semantic.py semantic-reviews` to inspect the reviewed
subjects and `python3 scripts/semantic_review.py --check` for the focused
freshness gate.

The generated corpus keeps two different identities separate. Its
`source_provenance.formal_source` is the committed Lean source anchor declared
by `claims.json`; its `evidence_fingerprint` and
`semantic_input_fingerprint` content-address the generated navigation
projection. It deliberately does not label the projection with the checkout
`HEAD`: that would become stale after an unrelated documentation commit and
would make safe regeneration depend on Git state.

## The coverage contract

`scripts/check_semantic_corpus.py` keeps four levels separate.

1. **Inventory.** The declaration atlas fixes the live population.
2. **Typed routing.** Every live declaration has exactly one role-and-zone
   receipt, or one manifest-owned generated-family receipt. Duplicate authored
   receipts and missing routes fail the check.
3. **Exact structural linkage.** Every authored theorem-like declaration is
   linked either to an authored node or to an exact module-and-signature family.
   This closes navigation coverage but makes no claim of mathematical
   interpretation.
4. **Authored statement-level interpretation.** Selected declarations point to
   authored canonical statement nodes. The receipt separately counts exact
   theorem evidence and contextual family links, so assigning more helpers to
   a certificate family cannot masquerade as new proposition evidence.
   Explicit narrow-zone replacement receipts allow a reviewed packet to refine
   a broad zone-only substrate route without creating duplicate ownership.
5. **Public selection.** Every declaration selected by `claims.json` has a
   semantic route and, when theorem-like, a statement node.

The checker also requires generated-family provenance, named open antecedents
for conditional nodes, scope caveats for barriers, live relation endpoints, and
an evidence basis for every relation. These are referential and typing
guarantees. They do not establish that an authored canonical statement is the
right informal meaning of its Lean evidence, that the chosen nodes are
complete, or that a relation is mathematically correct. Those remain review
and evaluation questions.

`claims.json` stays small and reviewed. Expanding it to one row per declaration
would destroy the thing it is for. It selects from this graph; it does not
replace it.
