<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Plectis: a public frontier across eight open Erdős problems

Plectis applies AI search, computation, ordinary mathematics, and Lean to eight
long-standing open Erdős problems: 68, 243, 249, 251, 257, 269, 1041, and 1049.
**All eight problems remain open.** This repository does not solve any of them.
They are a hard stress test: the aim is to publish exact, reusable progress
that another researcher can continue.

Each problem exposes checked results, failed routes, and its open obligation.
Lean checks formal statements, not intended meaning, novelty, or significance.

Large-language-model agents drafted prose, proofs, and software. Recorded model
reviews are source-bound best attempts at mathematical interpretation, not
independent specialist review. Will Cook maintains the project and is
responsible for the release.

## A result to start with

For every integer base **b ≥ 2** and every infinite set **A of positive integers**
with **∑ₐ∈A 1/a < ∞**, the series **∑ₐ∈A 1/(bᵃ − 1) is irrational**.
The support need not be pairwise coprime: the theorem includes, for example,
the squares. Its proof uses close returns of an integer-valued orbit, with
summable reciprocal mass controlling the tail.

Read the [formal theorem](Erdos249257/AllBaseReciprocalSupportIrrationality.lean#L395)
and the [#257 paper](erdos-257-mersenne-support-subseries.pdf).
The universal problem remains open in the reciprocal-divergent regime;
some supports in that regime, including full support, are already known to
give irrational series. Novelty and priority of this result are unassessed.

The [result guide](docs/RESULTS.md) separates other exact reductions,
denominator exclusions, counterexamples, and open obligations.

![System map: pipeline, problem-sized Lean worlds, public artifacts, and the clone-work-return-credit loop](.github/system-map.png)

If you solve one, the result and credit are yours. If Plectis materially helped,
cite the release. The contribution record distinguishes mathematical credit,
prior work, tools, and infrastructure.

The design draws on Terence Tao's
[*Mathematics in the age of AI*](https://arxiv.org/abs/2608.16753): producing a
result is only part of the work; checking, explaining, and making it useful to
other mathematicians matter too. The [open-source strategy paper](open-source-mathematics-strategy.pdf)
develops that idea and the contribution process.

Start with [A reader's way in](HUMAN_ENTRY.md), the human tour.

To work on a question, clone the repository and read the
[contributor guide](CONTRIBUTING.md). You can propose mathematics, correct a
reference, improve an explanation, or fix a tool. Return your changes in a
pull request; the [credit policy](docs/research-commons/CREDIT_POLICY.md)
explains how accepted work is attributed. The
[accepted contribution record](docs/research-commons/CONTRIBUTIONS.md) is public.

Choose a checkout. Each block below is complete on its own; the first
three are exclusive sparse manifests of the same clone.

Clone without a checkout, then pick one sparse manifest:

```sh
git clone --depth=1 --filter=blob:none --single-branch --no-checkout https://github.com/wcook04/plectis-erdos.git
```

Quick proof check (the first proof's import cone only):

```sh
git -C plectis-erdos cat-file -e HEAD:scripts/lean-quick-sparse-checkout && git -C plectis-erdos show HEAD:scripts/lean-quick-sparse-checkout | git -C plectis-erdos sparse-checkout set --no-cone --stdin
git -C plectis-erdos checkout
```

Complete Lean proof source:

```sh
git -C plectis-erdos cat-file -e HEAD:scripts/lean-sparse-checkout && git -C plectis-erdos show HEAD:scripts/lean-sparse-checkout | git -C plectis-erdos sparse-checkout set --no-cone --stdin
git -C plectis-erdos checkout
```

Reader files only (papers, notes, and metadata; no Lean):

```sh
git -C plectis-erdos cat-file -e HEAD:scripts/reader-sparse-checkout && git -C plectis-erdos show HEAD:scripts/reader-sparse-checkout | git -C plectis-erdos sparse-checkout set --no-cone --stdin
git -C plectis-erdos checkout
```

Complete current corpus, then fetch its pinned history and inspect one claim:

```sh
git clone --depth=1 --filter=blob:none --single-branch https://github.com/wcook04/plectis-erdos.git plectis-current
cd plectis-current
git fetch --filter=blob:none --unshallow origin main
python3 scripts/verify_claims.py --claim eb_full_support
```

Blobless full history for release validation:

```sh
git clone --filter=blob:none --single-branch https://github.com/wcook04/plectis-erdos.git plectis-release
```

In a Lean-source checkout, one bounded proof build. Lean itself is installed
through elan; the [Lean community setup guide](https://leanprover-community.github.io/get_started.html)
covers that step.

```sh
cd plectis-erdos
python3 scripts/lean_fast_build.py --jobs 2 ErdosProblems.Erdos249.PeriodMultipleEscape
```

For smaller checkouts, proof builds, or release validation, follow the
[setup and reproduction guide](docs/REPRODUCIBILITY.md). Agents should start
at [the agent entry](AGENTS.md), which routes them to the mathematical map,
formal claims, and focused checks. Humans can ask their agent to follow that
route without learning the commands themselves.

If you use a model in a web app, ask a repository-connected agent to prepare
a source packet for one question. The packet contains selected committed
files in one attachment; bring the answer back through the same review and
credit process. [The reader's guide](HUMAN_ENTRY.md) explains this route.

The [architecture and repository guide](ARCHITECTURE.md) and its
[printable PDF](claim-faithful-publication-systems-paper.pdf) explain how the
research record is maintained. Both assume no Lean or project history.
Cloning runs no project code; see [security](SECURITY.md) for the execution
boundary.

## Problem papers

[**#68**](erdos-68-factorial-denominator-irrationality.pdf) reduces irrationality
to infinitely many failures of one divisibility test; producing them remains
open.

[**#243**](erdos-243-reciprocal-tail-rigidity.pdf) excludes a bounded negative
part after Koizumi's normalised vanishing. The required bound remains open.

[**#249**](erdos-249-binary-totient-series.pdf) gives explicit rational bases for
the dyadic sections of Euler's totient, exact level rank `2ᵉ + 1`, denominator
exclusion to about `7.96 × 10³⁴`, and diagonal certificates for every `t ≤ 82`.
No unbounded producer is proved.

[**#251**](erdos-251-prime-gap-dyadic-series.pdf) checks the prime-gap identity
and a tail-shift equivalence. The concrete prime-tail bridge remains open.

[**#257**](erdos-257-mersenne-support-subseries.pdf) proves irrationality for
every infinite reciprocal-summable support at every integer base at least two.
It also develops finite-period noncollapse and the Mersenne achievement set's
topology and measure. The universal statement and the `1/2` and `1/21` targets
remain open.

[**#269**](erdos-269-three-prime-running-lcm.pdf) records a two-prime
transcendence argument. **This is not first and not formalised.** Steve Fan
posted the same argument on erdosproblems.com on 26 June 2026, before this note;
no priority or Lean theorem is claimed. Three or more primes remain open.

[**#1041**](erdos-1041-lemniscate-newton-flow.pdf) checks Newton-flow decay, ray
separation, collision geometry, and root retention. Topology and metric gluing
remain open.

[**#1049**](erdos-1049-rational-base-lambert.pdf) checks construction-specific
no-go theorems and four-jet cancellation at base `3/2`. It proves no
irrationality result, and the primitive construction remains open.

## What the checks establish

Comparator compares proof-bearing modules against separately declared
statements and a fixed axiom budget; an altered statement must be rejected.
The portfolio is derived from registered packages.
Configuration is not execution: only a green receipt for an exact commit
licenses the description **Comparator-checked**.
[`formalization.yaml`](formalization.yaml) records each selected result's source,
boundary, `sorry` count, and axioms. The
[verification packet](docs/EXTERNAL_VERIFICATION.md) covers all eight problem
programmes. Comparator does not assess exposition, citations, computation,
meaning, novelty, or significance.

[`docs/claims.json`](docs/claims.json) owns every claim record and its status,
[`docs/PALOMAR_RESULT_SHOWCASE.json`](docs/PALOMAR_RESULT_SHOWCASE.json) owns the
reader-priority ranking, and [prior art](docs/PRIOR_ART.md) records classical,
subsuming, and earlier public work. Status labels describe evidence rather than
score it: a checked rendering is not a priority claim, and a conditional
reduction still depends on its named open condition.

`v0.9.0` is the citation anchor, and [`docs/claims.json`](docs/claims.json) pins
its formal-source checkpoint. This is a self-contained public checkout of
Plectis. It is not an entrypoint into any private development system; only its
pinned Lean source is proof authority; do not infer results from private or
unreleased work.

## Give your agent a research shift

[Start a bounded research shift](docs/FRONTIER_RELAY.md): inspect one exact
public revision, attempt a substantive continuation, and prepare a checkable
local return with contributor credit. The
[portable `plectis-frontier` skill](.agents/skills/plectis-frontier/SKILL.md)
wraps the existing mining and return workflows for OpenClaw and other skill
clients. It does not require the private Plectis system or a new account.
Installation, source smoke tests and actual hosted-agent compatibility remain
separate checks; the guide states what each establishes.

Working in a web app instead? Ask a repository agent to prepare a
[source attachment](skills/erdos-research-return/SKILL.md#send-sources-to-a-model-without-a-repository-harness)
for one question. Give the model the selected text, then bring its answer back
for checking and contribution credit.

## Read or run it

The reading order is [RESULTS](docs/RESULTS.md), [SCOPE](SCOPE.md), the
[source map](docs/SOURCE_MAP.md), and [prior art](docs/PRIOR_ART.md).
[METHODOLOGY](METHODOLOGY.md) governs claim changes.

[`examples/Examples.lean`](examples/Examples.lean) is the minimal downstream
consumer; its conditional shell-pressure example leaves the analytic hypothesis
explicit and does not prove universal #257.

An agent arriving cold starts at [`AGENTS.override.md`](AGENTS.override.md).
[The Agent Workbench](docs/AGENT_WORKBENCH.md) keeps machine routing and kernel
probes out of the human reading path; only kernel receipts assert.

Historical #249/#257 module names and the
[joint manuscript](erdos249-257-main-paper.pdf) remain for archive and provenance.
The eight per-problem papers and complete reasoning records are the
live reading route; the
[agent-navigation paper](cold-clone-to-proof-receipt.pdf) audits it.

## Citation and licence

Citation metadata for `v0.9.0` is in [`CITATION.cff`](CITATION.cff). Code,
scripts, and documentation are Apache-2.0; the manuscript layer is CC-BY-4.0, and
[`REUSE.toml`](REUSE.toml) is complete. Corrections are received through the
issue forms; [`CONTRIBUTING.md`](CONTRIBUTING.md) explains the local checks and
credit route, [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md) states the participation
standard, and [`SECURITY.md`](SECURITY.md) gives the private route.

The independently authored `.agents/skills/plectis-frontier` distribution
wrapper is the narrow MIT-0 exception recorded in `REUSE.toml`. It does not
relicense the research corpus or transfer credit for participants' mathematics.

<!-- BEGIN generated_corpus_at_a_glance -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Corpus at a glance

The layer a mathematician should judge is small: 132 curated claim records in 30 contribution families, reaching Lean source through 409 principal declaration links. `SCOPE.md` gives its shape and `docs/RESULTS.md` gives the strongest checked result per problem.

The rest is engineering inventory. About 92% of the 155,018 declarations (142,668 across 695 modules) are machine-emitted certificate shards: one integer checked prime, one position excluded. The remainder is not all hand-written either.

| Engineering inventory | Current size |
|---|---:|
| Lean modules (the two library roots) | 1,126 |
| Formal results and supporting lemmas | 152,474 |
| Curated claim records | 132 |
| Contribution families | 30 |

Generated shards are counted as formal source and never as separate
mathematical claims. Claim records span every status, including cited and
open, and are partitioned exactly once.
These are navigation counts, not novelty claims.
<!-- END generated_corpus_at_a_glance -->

<!-- BEGIN generated_principal_declaration_anchors -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Following a result into Lean

The paper links each headline result to the relevant source. For a particular
topic, start with the [source map](docs/SOURCE_MAP.md); it gives the module
order without asking you to decode Lean declaration names first.
<!-- END generated_principal_declaration_anchors -->

## Where I actually am

[Where I actually am](HUMAN_ENTRY.md#where-i-actually-am) says who wrote this and
why it was released in the state it is in. The
[routes are on the site](https://wcook04.github.io/plectis/#contact).
