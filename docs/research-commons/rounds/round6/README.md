<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Round 6: the three prose returns

Round 6 (packet `plectis_round6_20260928`, built from public main `f18ed012`) asked outside
research runs, which the packet calls Type B, four questions about the infrastructure around the
corpus:

1. what the infrastructure is, which parts carry its value, and what it should become, with the
   first three things to build specified to code level;
2. what can be built from the corpus's many restatements, equivalences and conditional
   reductions, each of which is, or can be made, a kernel-checked implication between exact
   statements;
3. what would make the systems paper the definitive description of the infrastructure;
4. the highest-leverage change nobody had asked for.

Three independent returns answered. Each came as a prose answer and a ZIP of code, Lean
candidates and evidence. The prose answers are published here verbatim.

## The files

Each file is a byte-for-byte copy of the return as it was taken into custody. The SHA-256 and
byte count below are the ones recorded at intake, and the `return_received` events of the
research record carry the same values (`docs/research-commons/record/journal.jsonl`).
`MANIFEST.json` lists the same rows in machine-readable form.

- `return-a.md` (return A, research-state compiler): 32,769 bytes, SHA-256
  `aeed70bc7ea71becec287192579bf1dde23fb143346bcc5342d230db54c41f5d`
- `return-b.md` (return B, contrastive research compiler): 32,782 bytes, SHA-256
  `a8f760f80331477c47a272c28e40c5369963836a68d51dcb9ffbb3b156ef1524`
- `return-c.md` (return C, checked route record): 36,383 bytes, SHA-256
  `a7d2ad7ee8c3479b9c7bf3ffc6be55d87eb31d6509dbb49484be187167c6f83a`

Because the files are exact copies, they keep the returns' own wording, formatting and links.
Links of the form `sandbox:/mnt/data/...` pointed into the returning model's workspace and do not
resolve here. The returns' claims about this repository are the returning runs' own; the review
that checked them is recorded in the journal as `review_recorded` events.

## Where the designs landed

The three returns agreed on relation contracts between statements, one question per set of
equivalent formulations for credit, packets compiled to cover a declared set of distinctions,
and custody before interpretation. The parts taken or adapted are:

- `lean/ErdosProblems/ArgumentGraph/Contracts.lean`: the relation vocabulary (entailment,
  separation, feasibility, refutation, supply), the `SlotReplacement` and `EndpointRoute`
  certificate types with their laws, and canaries recording comparison shapes the corpus has
  produced;
- `lean/ErdosProblems/ArgumentGraph/Results/RelationCertificates.lean`: relation certificates
  over existing corpus declarations, transcribed in `docs/research-commons/record/relations.json`;
- `scripts/relation_registry.py`: the relation registry, attested through the declaration atlas
  at the formal-source pin;
- `scripts/contrast_ledger.py` and `docs/research-commons/record/contrasts.json`: the ledger of
  distinctions this programme has read wrongly, each with checkable evidence;
- `scripts/compile_research_packet.py`: the packet compiler, an exact cover search with
  withholding, cutoffs and taint;
- `scripts/research_record.py` and `docs/research-commons/record/journal.jsonl`: the round
  journal, with milestones computed from the checkout.

Each component's disposition (taken, adapted, rejected or deferred, with its reason) is a
`component_disposed` event in the journal; `python3 scripts/research_record.py status` shows them.

## What stays in private custody

The three ZIP archives are held in private custody and recorded in the journal by hash and size
only. Four evidence files inside them carry a local filesystem path from the machine that built
the packet, so the archives are not republished as they stand.
