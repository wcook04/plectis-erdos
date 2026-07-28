<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Prior art for the theory-laboratory layer

`docs/PRIOR_ART.md` maps the *mathematical* sources for #249 and #257. This file
maps the *systems* prior art for the layer described in `README.md`, and it exists
to keep the layer's description honest. Most of what this layer does is already
done elsewhere, frequently at larger scale. Recording that plainly is cheaper
than having a reviewer do it.

Searched 25 July 2026. A dated negative search result is not a novelty claim.

## What is not new

| Layer | Verdict | Prior art |
|---|---|---|
| Exhaustive declaration atlas with provenance | **Not novel.** Standard 2024–2026 tooling. | LeanGraph / TheoremGraph, [2606.25363](https://arxiv.org/abs/2606.25363) — 388,105 declaration nodes, 11.3M typed edges over 25 Lean projects. *The Network Structure of Mathlib*, [2604.24797](https://arxiv.org/abs/2604.24797) — 308,129 declarations. LeanExplore, [2506.11085](https://arxiv.org/abs/2506.11085), whose `StatementGroup` is the same dedup idea. |
| Statement graph with typed logical relations | **Core already done twice, larger.** | Equational Theories Project, [2512.07087](https://arxiv.org/abs/2512.07087) — 4,694 mathematically distinct nodes, **all 22,028,942 implication and anti-implication edges resolved**, anti-implications witnessed by explicit magmas, open frontier tracked as a graph, Lean-validated. Reverse Mathematics Zoo and π-Base do implications *and* non-implications with automated closure. MMT/OMDoc theory graphs supply typed truth-preserving morphisms. |
| Mechanism records (invariant + transformation + controlled observable) | **The schema is thirty years old.** | Bundy's proof planning: *methods* are declarative preconditions + tactic + postconditions, *critics* are declarative specifications of **when a method fails** plus a patch. **Rippling** is literally skeleton-preservation as invariant, wave rules as transformation, annotation as controlled observable. Ireland & Bundy, [*Productive Use of Failure in Inductive Proof*](https://link.springer.com/article/10.1007/BF00244460), JAR 16:79–111 (1996); Ireland & Stark, [*Invariant Discovery via Failed Proof Attempts*](https://link.springer.com/chapter/10.1007/3-540-48958-4_15), LOPSTR 1998; *Rippling*, CUP 2005. See also Bundy's own [*A Critique of Proof Planning*](https://www.inf.ed.ac.uk/publications/online/1311.pdf) on why it underdelivered. |
| Corpus-induced abstraction validated by downstream success | **Done, and it works.** | TacMiner, [2503.24036](https://arxiv.org/abs/2503.24036) — abstractions mined from Tactic Dependence Graphs, +172% relative downstream proof success in Rocq. Strat2Rocq, [2510.10131](https://arxiv.org/abs/2510.10131). LEGO-Prover, [2310.00656](https://arxiv.org/abs/2310.00656). |
| Typed interventions on statements, Lean-checked | **Done, at far larger scale.** | *Learning to Disprove*, [2603.19514](https://arxiv.org/html/2603.19514v1) — hypothesis-dropping with redundancy stripped first, 575K problems, Lean 4 verified. Alchemy, [2410.15748](https://arxiv.org/abs/2410.15748) — 110k → 6M by equivalent-form rewriting. ALF, [2606.12594](https://arxiv.org/html/2606.12594v1) — five typed variant categories. Trocq (TOPLAS 2025) and Isabelle `Transfer` mechanise transport; Pumpkin Pi mechanises repair. |
| Temporal holdout by commit date in a Lean library | **Canonical method, must be cited.** | miniCTX / miniCTX-v2, [2408.03350](https://arxiv.org/html/2408.03350v2), ICLR 2025 oral — holdout by first-commit timestamp, ablation over preceding file context. APE-Bench, SorryDB, RLMEval ([2510.25427](https://arxiv.org/abs/2510.25427)), ArXivLean all do commit- or publication-date splits. |
| An Erdős corpus in Lean with reformulations and variants | **Not novel.** | Formal Conjectures, [2605.13171](https://arxiv.org/html/2605.13171v1) — **1,318 Erdős-derived Lean statements across 353 problems**, with disproof first-class via `answer(sorry)`. And [2605.22763](https://arxiv.org/abs/2605.22763) reports an agent resolving **9 open Erdős problems** in Lean. |
| Negative space as typed records | **Partially done.** | OProofs/OProver, [2605.17283](https://arxiv.org/abs/2605.17283) — 869k failure-conditioned proofs, ablated at 6–9 points, but **explicitly declines to impose a taxonomy**. *Negative Knowledge as Failure-aware Shared Memory*, [2606.21024](https://arxiv.org/html/2606.21024v1) — closed five-field failure taxonomy with `ruled_out_routes`, measured transfer; non-formal and non-mathematical. |

## What appears uncovered

Not the layers. The **measurement**. No located work uses a formal-library
temporal holdout to score an *explanation artifact*, or decomposes the context
into signatures / +graph / +mechanisms / +failures arms. Every formal-library
temporal benchmark measures proof success, diff correctness, or formalisation
validity. The simulatability literature that does score explanations by whether a
simulator recovers behaviour — ALMANACS [2312.12747](https://arxiv.org/pdf/2312.12747),
ConSim [2501.05855](https://arxiv.org/pdf/2501.05855) — has not been ported to
mathematics.

Also apparently uncovered, though smaller: `barrier_for` and `repair_of` as edges
in one graph over a research Lean corpus, and failure records carrying the same
structured schema as success records inside a machine-checked corpus.

## The hypothesis, stated so it can fail

> In a machine-checked mathematical corpus, mechanism records — invariant plus
> transformation plus controlled observable, induced from both successful and
> failed proof routes — raise an agent's recovery rate on theorems held out by
> pre-landing git commit above a compute-matched arm given the same corpus plus
> its typed statement graph, and above shuffled and off-problem mechanism
> controls.

Falsified if any existing system already stores and validates such records, or if
the mechanism arm does not beat the graph arm under compute-matched,
difficulty-stratified, shuffled-control conditions.

## Two controls that are not optional

The design is constrained by two published results, and omitting either makes a
positive outcome uninterpretable.

- *LLM Library Learning Fails: A LEGO-Prover Case Study*,
  [2504.03048](https://arxiv.org/abs/2504.03048) — found no evidence of direct
  reuse, evidence against soft reuse, and **gains that vanish once compute is
  matched**. This is the null hypothesis any mechanism-transfer claim is measured
  against.
- *Compressive KG Hypothesis*, [2605.27176](https://arxiv.org/abs/2605.27176) —
  compact subgraphs recover full-graph behaviour under **many unrelated selection
  rules**, so "the graph helped" needs shuffled and random controls.

Hence the `mechanism_shuffled` and `mechanism_offproblem` arms, and hence rule 11
in `scripts/check_theory_lab.py`, which refuses to let a mechanism-arm result
stand in the record without a control arm and both baselines.

Difficulty stratification is required for a third reason: DRIFT
([2510.10815](https://arxiv.org/pdf/2510.10815)) measured extra context acting as
a **distractor on easy problems**, so an unstratified null is uninterpretable.

## Systems most likely to refute this

- **DreamProver**, [2604.26311](https://arxiv.org/abs/2604.26311) — the only
  located system inducing abstractions from a formal corpus into a persistent,
  consolidated library and evaluating transfer to new Lean theorems. Adding a
  commit-time split is a small increment; if its library shows compute-matched
  transfer, this layer collapses into "skill library, already done".
- **TacMiner** — already demonstrates the value half of the hypothesis in Rocq
  with no mechanism semantics at all.
- **OProofs/OProver** — already holds the failure corpus and ablates its value;
  the only thing between it and this layer is a design choice it made
  deliberately and could reverse.

## Naming

Do not describe this as *proof mining*: that is Kohlenbach's unrelated programme
for extracting quantitative bounds from non-constructive proofs.
