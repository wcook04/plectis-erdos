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
python3 scripts/query_semantic.py paper-coverage
python3 scripts/query_semantic.py population-backlog
python3 scripts/query_semantic.py population-backlog --paper erdos249-totient-reasoning-surface
```

`population-backlog` is the semantic authoring queue.  It scans every authored
paper, resolves both public `\lword` links and reasoning-surface `\lean` links
to exact live declaration roles, deduplicates qualified and short spellings,
and ranks paper-selected declarations that still lack an
`authored_statement` interpretation. A structural-family link therefore stays
in the backlog rather than making it disappear. A paper citation nominates a
target; the Lean signature and proof cone still decide the authored statement.
The command does not promote helpers automatically or treat a larger node
count as quality.

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
