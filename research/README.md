<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Experiments and investigations

Use this directory to replay a finite calculation, vary a mathematical example,
or inspect a recorded research attempt. Current conclusions belong in
[Results and limits](../docs/RESULTS.md) and the [papers](../paper/README.md).
Each guide states its inputs, prerequisites and evidence boundary. A saved
output covers its recorded source and range; it does not certify changed code,
an infinite claim, or a new Lean build.

## Mathematical experiments and reader exercises

| Folder | Purpose and evidence |
|---|---|
| [chain_transcendence](experiments/chain_transcendence/README.md) | Exact rational bookkeeping for an ordinary transcendence proof using an external theorem; the finite checks are not that proof. |
| [choices_contraction](experiments/choices_contraction/README.md) | Rational subsum rejection and greedy-orbit controls; finite survival does not establish infinite membership. |
| [erdos68](experiments/erdos68/) | Factorial-series continued-fraction, local-arithmetic and critical-fibre checks. Start with the [enclosure checker](experiments/erdos68/check_cf.py); it does not replay the historical carry census. |
| [erdos251](experiments/erdos251/README.md) | Replay the certified continued fraction and finite prime-gap tail computations. |
| [erdos257](experiments/erdos257/README.md) | Replay truncation ladders, quotient identities, greedy decisions and tail margins; inspect each case's range and runtime first. |
| [erdos269](experiments/erdos269/README.md) | Exact shell checks and finite escape certificates. The nested [distinct-height investigation](experiments/erdos269/distinct_height/README.md) concerns a different sum from the catalogue problem. |
| [erdos1041-hub](experiments/erdos1041-hub/README.md) | Rational interval certificates for limiting signs; they supply no explicit small-parameter remainder bound. |
| [erdos1049](experiments/erdos1049/README.md) | Rational-base, polynomial and determinant computations with recorded receipts; none runs Lean. |
| [premise_exchange](experiments/premise_exchange/README.md) | Test a transfer's missing premise and work through the selected-shift exercise; source material, finite controls and formal probes have separate roles. |
| [sparse_interpolation](experiments/sparse_interpolation/README.md) | Computations and counterexamples around capacity and derivative interpolation; the guide separates ordinary proofs from finite Lean ingredients. |
| [weighted_support_transfer](experiments/weighted_support_transfer/README.md) | Change a weighted-support hypothesis and check the ordinary deduction; the example supports are not separate formalised results. |

## Evaluation controls and dated research records

These six folders serve narrower research or tooling tests. Their examples and
recorded outcomes are not evidence of a general discovery advantage.

| Folder | Purpose and evidence |
|---|---|
| [construction_synthesis](experiments/construction_synthesis/README.md) | Reconstruction control recovering an already-known coordinate from update rules; its validator receipt owns the checking outcome. |
| [interestingness](experiments/interestingness/README.md) | Source-graph measurement and negative controls at a pinned commit; reuse counts are not mathematical-value rankings. |
| [replay_worlds](experiments/replay_worlds/README.md) | Dated route reopenings, their accepted mathematical outcomes and surviving boundaries; follow the linked source evidence. |
| [round8_finite](experiments/round8_finite/README.md) | Four finite controls from returned research. The [manifest](experiments/round8_finite/manifest.json) preserves source, implementation and output hashes. |
| [erdos249](experiments/erdos249/round8_signed_pulse.py) | The signed-pulse control governed by that same Round 8 manifest; it supplies no simultaneous infinite construction. |
| [short_paper_writer](experiments/short_paper_writer/README.md) | Authored #269 writing fixture with bound source spans; a rendering check is not mathematical or human review. |

## Formal examples, probes and session archives

[Examples.lean](examples/Examples.lean) is the downstream library consumer;
[ExternalVerificationPortfolio](examples/ExternalVerificationPortfolio/README.md)
shows selected interfaces. [Adapters](adapters/) bridge Formal Conjectures
statements. [Erdos243V5](Erdos243V5/) and [residualbench](residualbench/) hold
development and validation modules; their location alone establishes no build.

[Probes](probes/) preserve Round 7 and 8 Lean investigations. Read their
[Round 7 frozen evidence manifest](../docs/research-commons/rounds/round7/evidence/MANIFEST.json)
and [Round 8 custody/disposition manifest](../docs/research-commons/rounds/round8/MANIFEST.json)
for the recorded edition and outcome, rather than treating an old receipt as
verification of today's source.

[Workbench sessions](workbench/sessions/) retain three dated investigations:
[carry pivot](workbench/sessions/carry_pivot_2026_07_27/ledger.jsonl),
[congruence support](workbench/sessions/congruence-support-20260920/continuation.json)
and [admissible feedback](workbench/sessions/admissible-feedback-20260920/replay.json).
Their ledgers, source pins and probe receipts preserve what happened; session
notes are advisory. The [workbench guide](../docs/agents/AGENT_WORKBENCH.md)
owns current operation. [research_corpus](../research_corpus/README.md) separately
preserves returned research packets. Use [Contributing](../CONTRIBUTING.md)
to return work with evidence and credit.
