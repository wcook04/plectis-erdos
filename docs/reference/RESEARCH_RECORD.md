<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# The research record

The research record is the committed account of how outside research enters
this programme and what each piece of it still owes. It keeps custody of every
returned answer, the decisions made about it, the results those answers are
meant to produce, and the relations and contrasts that later questions must
respect. Its files live in `docs/research-commons/record/`, and four
standard-library scripts in `scripts/` read and check them.

The record keeps custody and decisions. It confers no mathematical authority.
A statement is proved when the pinned Lean build checks it; the record says
what was asked, what came back, what was done with it, and which evidence
class each entry carries.

## What the record holds

| Part | Where it lives | What it records |
|---|---|---|
| Rounds | `journal.jsonl`, `round_opened`, `round_sealed` | A packet sent for research, its declared consumers and the returns expected; sealing closes it to further arrivals. |
| Returns | `journal.jsonl`, `return_received` | Custody of one returned file: bytes, sha256, the private intake that holds it, and an optional public copy. |
| Reviews | `journal.jsonl`, `review_recorded` | A reviewer's disposition of a return, with its rationale. |
| Component dispositions | `journal.jsonl`, `component_disposed` | Each component of a return taken, adapted, rejected or deferred, and where it landed; a deferral names an owner and a re-entry trigger, and the latest disposition of a component is the one that counts. |
| Consumer dispositions | `journal.jsonl`, `consumer_disposed` | What each declared consumer did with a return or output; a deferral names an owner and a re-entry trigger. |
| Outputs and milestones | `journal.jsonl`, `output_declared`, `milestone_reported` | A result the programme owes and the milestones it needs, computed from the checkout wherever the checkout can answer. |
| Relations | `relations.json` | How two statements compare inside one context, each row bound to a certificate declaration in [RelationCertificates.lean](../../lean/ErdosProblems/ArgumentGraph/Results/RelationCertificates.lean). |
| Contrasts | `contrasts.json` | Distinctions this programme has read wrongly, each with its evidence, provenance, triggers and four uses. |

The journal is append-only. Each line is one canonical JSON object whose
`event_sha` hashes its body, and whose `previous` field names the hash of the
line before it. `verify` checks that chain, every hash, the canonical form of
each line, a torn final line, each kind's schema and the references between
events. Appending is refused when `CI` is set: a maintainer writes the record,
commits it, and the release check verifies it.

The relation vocabulary is fixed in
[Contracts.lean](../../lean/ErdosProblems/ArgumentGraph/Contracts.lean):
`equivalent`, `endpoint_route`, `slot_replacement`, `strictly_stronger`,
`separates`, and the single-statement relations `refuted`, `feasible` and
`supplied`. A contrast row names a distinction in one sentence, the wrong and
right readings, source spans and declarations that expose it, and its four
uses: a packet obligation, a return gate, a regression specimen and an
experiment intervention.

## Invariants

- A slot certificate, in which a replacement `R` reconstructs a hypothesis `H`
  inside a context, never counts as weakening `H`. A proof of the converse
  makes the two equivalent in that context. Strictness needs a separator in the
  same context. A failed or timed-out search reads `unknown`.
- An endpoint route, in which a statement gives the endpoint of a result, is a
  different certificate type from a slot replacement.
- Equivalent formulations are one question for credit and separate views for
  search.
- Logical evidence transports along checked relations: supply moves forward
  along an entailment and refutation moves backward. Outcomes, costs and
  failures never transport.
- A failed attempt is evidence about an attempt. Only a scoped obstruction or
  counterexample excludes a route, and only on its own assumptions.
- Custody comes before interpretation. Every arrival is kept, including the
  ones a review rejects.
- No JSON field confers kernel authority. Authority comes from the Lean build
  at the pin, from a kernel-probe receipt of the right evidence class, or from a
  reviewed decision labelled as such.
- A budget never truncates a mandatory guard. When a packet cannot cover its
  obligations, the compiler refuses and returns the unmet obligations.

## Evidence classes

Every computed milestone, relation row and contrast item states its evidence
class. The table says what each class establishes and what it leaves open.

| Evidence class | Establishes | Leaves open |
|---|---|---|
| `declaration_atlas_at_pin` | The name is listed in [the declaration atlas](../declaration_atlas.json), a navigation projection of the Lean source at the pin. | That a CI job compiled the module (see compiled targets below), and the statement's reading. |
| `paper_coverage_projection` | A row of [the paper-to-Lean ledger](../paper_lean_coverage.json) for a short or long paper names the declaration. | That the paper's prose states the same result. |
| `claim_registry_entry` | [The claim records](../claims.json) list the declaration or its external-verification wrapper. | The claim's status, which the claim record and its review own. |
| `comparator_config_entry` | A Comparator configuration under `verification/` names the declaration or its wrapper, so it is queued for comparison. | That a comparison ran or passed. Comparator checks a statement against a challenge; review of the mathematics is separate. |
| `git_ancestry` | The merge commit is an ancestor of `HEAD`. | The review of the merged change. A shallow clone without the commit reads `unknown`. |
| `kernel_probe_verdict` | A kernel-probe run returned this verdict for the stated pair. | That the result is part of the library; probe verdicts are never written into the registry. |
| `recorded_relation` | A relation id exists in `relations.json`. | The row's attestation state, which `relation_registry.py check` computes. |
| `source_span_bound_to_file_hash` | The cited lines exist at the git ref and contain every required literal. | What the lines mean. |
| `lean_source_at_ref`, `lean_source_worktree`, `lean_source_worktree_uncommitted` | The declaration header is in the Lean source at the ref, in the working tree, or only in uncommitted work (with a warning). | That the declaration elaborates. |
| `authored_review`, `reported`, `external_receipt`, `ci_receipt` | A person, an outside run or a CI job recorded the decision or result. | Anything the checkout can compute; a reported milestone never carries a computed class. |

**Compiled targets.** `research_record.compiled_modules` is the set of modules
that the default build roots (the module graph's `root` and `additional_roots`
in [docs/claims.json](../claims.json)) and the targets of the
[coverage build](../../.github/workflows/lean-coverage-build.yml) reach through
the module graph's import edges. The milestone `lean_on_main` is done only when
the declaration is listed in the atlas and its module is in that set; a listed
declaration in any other module reads `missing` with `compiled_target: false`.
A relation row is `attested` only when its certificate is listed with the
recorded signature hash, has the right type head and sits in a compiled
module. A row that meets the first two and fails the third is
`listed_not_compiled`, and `relation_registry.py check` fails on it. A test in
`scripts/test_lean_fast_build.py` requires every auxiliary root of the module
graph to be a compiled target or a named exclusion with its reason.

## The four command-line tools

`scripts/research_record.py` verifies the journal, projects what each round,
return and output still owes, reports the computed milestones for one
declaration, and appends events outside CI:

```sh
python3 scripts/research_record.py milestones \
  --declaration ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap
```

`scripts/relation_registry.py` validates and attests every relation row, and
answers questions over the usable rows: equivalence classes, the rows that
mention a statement, and what supplying or refuting a statement implies.
Anything other than supply or refutation is refused:

```sh
python3 scripts/relation_registry.py transport \
  ErdosProblems.ArgumentGraph.RelationCertificates.GoodBaseGap supplied --include-pending
```

`scripts/contrast_ledger.py` checks that every cited span, declaration and
relation is present, and selects the contrasts a problem, a text or a
declaration triggers:

```sh
python3 scripts/contrast_ledger.py triggered --problem 1041
```

`scripts/compile_research_packet.py` compiles a packet specification into
content-addressed excerpts, a handoff manifest and an owner receipt. It covers
every obligation within the byte budget in the fewest bytes, or refuses with the
unmet obligations and a deletion-minimal core:

```sh
python3 scripts/compile_research_packet.py compile spec.json --out packet --budget 16000
```

The release checks run `research_record.py verify`,
`relation_registry.py check` and `contrast_ledger.py check`, and the four test
suites both plainly and under `python3 -O`.

## How the record serves the research loop

The programme runs as a loop between its maintainers and outside research runs.
The maintainers choose a question and assemble a packet; an outside run
returns a written answer; the maintainers review it and carry what survives
into Lean, the papers and the records. The record keeps that loop honest in
three places.

1. **The packet is compiled from the record.** The contrasts triggered by the
   target problem, text or declarations become obligations, each covered by
   one bundle of its evidence, so the cheapest excerpt can never drop one side
   of a distinction. Withheld material is blocked, and so is material dated
   after a cutoff or undated under one; the block spreads to anything that
   repeats or depends on it. The return gate of each contrast
   becomes the disconfirming check the packet asks for.
2. **Custody comes before interpretation.** A return is recorded with its
   bytes and hash as it arrives, and the journal refuses a review of a return
   it has not received. The review comes next, then a disposition for every component, so the component ledger
   shows what was taken, adapted, rejected or deferred and where each one
   landed.
3. **Dispositions reach every consumer.** Each round declares its consumers.
   The status projection lists any consumer without a disposition, every
   deferral with its owner and re-entry trigger, and any output whose computed
   milestones are still missing. A later review of a return invalidates the
   consumer dispositions made before it.

The status projection lists what remains owed:

```sh
python3 scripts/research_record.py status --format md
```

For how residual obligations are classified, see
[residual progress](RESIDUAL_PROGRESS.md); for the review a claim change
requires, see [methodology](../METHODOLOGY.md).
