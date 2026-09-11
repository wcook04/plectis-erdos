<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Plectis: research on eight open Erdős problems

Plectis is an open-source, AI-assisted research project organised around eight
open Erdős problems. This repository brings together the papers, Lean proofs,
computations, failed approaches, and questions that remain, so another
researcher or coding agent can inspect the work and continue from it.
**All eight problems remain open.** This repository does not solve them.

**[Visit the website](https://wcook04.github.io/plectis/)** ·
**[Explore the mathematics](https://wcook04.github.io/plectis/maths/)** ·
[Browse all papers](https://wcook04.github.io/plectis/docs/papers.html) ·
[About the project](https://wcook04.github.io/plectis/#why) ·
[Contact me](https://wcook04.github.io/plectis/#contact)

![Eight open problems: papers, checked results, failed routes, and questions another researcher can continue](.github/system-map.png)

## Why this exists

The idea is to make mathematical research cumulative. Once the tools for
navigation, proof checking, recording experiments, and crediting contributions
exist, someone else should be able to bring an idea, a correction, or spare
compute without having to build them again. A useful partial result or a
failed approach with a checkable reason can save the next person work, even
while the original problem remains open.

The problems were chosen for their difficulty, to test the research process
and preserve what each attempt teaches the next researcher.

I am responsible for all claims, sources and the release. Plectis is an
independent, AI-assisted prototype. It has had no independent mathematical
review, and I need help. Novelty and significance still need human judgement.

Two papers explain the project in more detail:

- **[From Spare Compute to Cumulative Mathematics](paper/systems/open-source-mathematics-strategy.pdf)**
  explains the open-source idea, how different contributions can help, and how
  credit is recorded.
- **[Problem-Sized Lean Worlds](paper/systems/claim-faithful-publication-systems-paper.pdf)**
  explains how the research is organised and how finding a result, checking it,
  and deciding what may be claimed are kept separate.

## Where to start

- **Read the mathematics:** the [website's maths pages](https://wcook04.github.io/plectis/maths/)
  give each problem and its short and long papers. [A reader's way in](HUMAN_ENTRY.md)
  is the command-free guide in this repository.
- **Inspect a result:** start with [RESULTS](docs/RESULTS.md), then follow the
  [source map](docs/SOURCE_MAP.md) and the claim verifier in
  [REPRODUCIBILITY](docs/REPRODUCIBILITY.md).
- **Contribute:** bring an idea, review, correction, infrastructure improvement,
  or a research run. [Contribute](#contribute) explains the return and credit paths.
- **Use a coding agent:** navigation, validation and contribution workflows
  start at [`AGENTS.override.md`](AGENTS.override.md). An agent is not required
  to read the papers.

The notes follow Terence Tao's public guidance on writing mathematics produced
with AI assistance; that is a writing standard, not a review of this project.

## Problem papers

Each problem has a short paper and a longer research record covering failed
routes, finite evidence, and remaining obligations. For a first look, start
with **#257** for full-support irrationality and achievement-set measure, or
**#249** for exact kernel rank, finite certificates, and recorded routes that
stopped. [RESULTS](docs/RESULTS.md) summarises progress across all eight.

### #68: Factorial-denominator irrationality

[Problem page](https://wcook04.github.io/plectis/maths/problems/erdos_68.html) ·
[Original question](https://www.erdosproblems.com/68) ·
[short paper](paper/68/erdos-68-factorial-denominator-irrationality.pdf) ·
[longer paper](paper/68/erdos68-factorial-reasoning-surface.pdf).

A GMP non-unit carry at `m = 300000` and a continued-fraction bound
`q ≥ 2^39990` are incomparable finite exclusions. Producing cofinal carries
remains open.

### #243: Reciprocal-tail rigidity

[Problem page](https://wcook04.github.io/plectis/maths/problems/erdos_243.html) ·
[Original question](https://www.erdosproblems.com/243) ·
[short paper](paper/243/erdos-243-reciprocal-tail-rigidity.pdf) ·
[longer paper](paper/243/erdos243-reciprocal-tail-reasoning-surface.pdf).

After Koizumi's normalised vanishing, a bound on the upward steps of the
unreduced integer numerator forces eventual Sylvester recurrence; the
numerator itself need not be assumed bounded. Unbounded upward excursions
of that numerator remain open. Duverney (2001) and the Tao–Kovač line are
prior art on the page; cubic-rate vanishing is not claimed as empty-page
news.

### #249: Binary totient series

[Problem page](https://wcook04.github.io/plectis/maths/problems/erdos_249.html) ·
[Original question](https://www.erdosproblems.com/249) ·
[short paper](paper/249/erdos-249-binary-totient-series.pdf) ·
[longer paper](paper/249/erdos249-totient-reasoning-surface.pdf).

Bounded-residue series `A_m` are irrational for `m ≥ 3`, with a complete
dyadic-modulus classification ([§2](paper/249/erdos-249-binary-totient-series.pdf);
ordinary mathematics, not Lean). Separately: exact dyadic-kernel rank
`2^e + 1`, denominator exclusion to about `7.96 × 10³⁴`, diagonal
certificates through `t ≤ 82`, and no-go theorems for the shortcuts. This is
not an infinite witness for irrationality.

### #251: Prime-gap dyadic series

[Problem page](https://wcook04.github.io/plectis/maths/problems/erdos_251.html) ·
[Original question](https://www.erdosproblems.com/251) ·
[short paper](paper/251/erdos-251-prime-gap-dyadic-series.pdf) ·
[longer paper](paper/251/erdos251-prime-gap-reasoning-surface.pdf).

A sparse perturbation of the prime gaps can have a rational dyadic sum
while retaining the prime growth scale, every fixed eventual congruence,
and asymptotically the same short-block statistics. The later positions
are not asserted to be prime. This is complementary to Land's conditional
result, not a refutation; the original problem remains open.

### #257: Mersenne-support subseries

[Problem page](https://wcook04.github.io/plectis/maths/problems/erdos_257.html) ·
[Original question](https://www.erdosproblems.com/257) ·
[short paper](paper/257/erdos-257-mersenne-support-subseries.pdf) ·
[longer paper](paper/257/erdos257-mersenne-reasoning-surface.pdf).

For every infinite reciprocal-summable support, the Mersenne subseries is
irrational at every integer base `b ≥ 2` (short paper §2; ordinary
mathematics, not Lean). Erdős stated that coprimality-free extension; the
note writes out an averaging proof. Full-support irrationality at every
integer base is classical (Erdős 1948) and Lean-checked here.
The base-2 achievement set has measure one.
Pairwise-coprime plus summable-reciprocal support is Lean. Arbitrary
infinite support, and the `1/2` and `1/21` branches, remain open.

### #269: Three-prime running LCM

[Problem page](https://wcook04.github.io/plectis/maths/problems/erdos_269.html) ·
[Original question](https://www.erdosproblems.com/269) ·
[short paper](paper/269/erdos-269-three-prime-running-lcm.pdf) ·
[longer paper](paper/269/erdos269-running-lcm-reasoning-surface.pdf).

Steve Fan's two-prime factorisation
([erdosproblems.com/269](https://www.erdosproblems.com/forum/thread/269),
26 June 2026) is his; no priority or Lean theorem is claimed for it. At
three primes, one binary carry produces nonsingular selected kernel minors
of every order. The actual-series reduction is given; the source-specific
cofinal escape remains unproved. Three-prime irrationality remains open.

### #1041: Lemniscates and Newton flow

[Problem page](https://wcook04.github.io/plectis/maths/problems/erdos_1041.html) ·
[Original question](https://www.erdosproblems.com/1041) ·
[short paper](paper/1041/erdos-1041-lemniscate-newton-flow.pdf) ·
[longer paper](paper/1041/erdos1041-lemniscate-reasoning-surface.pdf).

Every monic trinomial `z^n + a z^m + b` with roots in the open unit disc
has each root-to-origin segment inside `{|f|<1}`, so any two roots join
through the origin with length less than `2`. Separately, a sharp Poisson
critical-value mean holds for zeros in the closed unit disc. Both are
ordinary proofs. Lean checks Newton-flow decay, ray-separating translations,
and perturbative root retention; three solved-family kernels are
Comparator-checked. The unrestricted path problem remains open. Forum
discussion of a degree-7 counterexample is a reported external claim, not a
theorem of this repository.

### #1049: Rational-base Lambert series

[Problem page](https://wcook04.github.io/plectis/maths/problems/erdos_1049.html) ·
[Original question](https://www.erdosproblems.com/1049) ·
[short paper](paper/1049/erdos-1049-rational-base-lambert.pdf) ·
[longer paper](paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf).

An ordinary specialization of Zudilin 2004 proves `F(31/4)` (and its positive
powers) irrational; that headline is not a Lean theorem. Lean checks
supporting height-region arithmetic, the `3/2` corridor exclusion, the
cleared-tail recurrence, and selected Hankel identities. The outstanding
`3/2` obligation is an approximant family with remainder control.

The [joint #249/#257 manuscript](paper/archive/erdos249-257-main-paper.pdf) is
archive and provenance only; the papers above are the current entrances.

## What the checks establish

Lean checks that a proof establishes the exact formal statement written in
the source. The papers explain the mathematics; the other records let you
trace a public claim back to its statement, evidence, and limitations.

- The [comprehension graph](docs/semantic/README.md) maps declarations,
  their statements, and the relations between them. It helps distinguish a
  reformulation or finite instance from the original open problem.
- **Comparator** gives the 47 selected interfaces in
  [`formalization.yaml`](formalization.yaml) a second formal check. Each
  statement is declared again without its proof, then checked against a
  proof-bearing solution and a fixed axiom budget.
- The [verification dossier](docs/EXTERNAL_VERIFICATION.md) covers all eight
  problem programmes. The [claim records](docs/claims.json) give public claim
  status, and [prior art](docs/PRIOR_ART.md) records earlier and subsuming work.

The [methodology](METHODOLOGY.md) explains what each check establishes.
These checks do not decide whether a statement captures the intended problem,
is new, or solves anything. That requires expert review. Do not infer results
from private or unreleased work.

## Contribute

An idea, a correction, a counterexample, a failed route with a checkable
reason, clearer exposition, a validation of a claim or a repaired check all
count. You can also contribute mathematical direction, infrastructure
improvements, or a research run using your own coding agent and compute.

- **Have an idea or correction?** Use the
  [research-progress form](https://github.com/wcook04/plectis-erdos/issues/new?template=research_progress.yml)
  or [email me](https://wcook04.github.io/plectis/#contact).
- **Have a change to the repository?** Open a pull request following
  [CONTRIBUTING](CONTRIBUTING.md).
- **Want to work on an open question?** The
  [eight-frontier issue](https://github.com/wcook04/plectis-erdos/issues/105)
  lists starting points; the [frontier relay](docs/FRONTIER_RELAY.md) explains
  how to return a research run from an exact public revision.

Accepted work gets a public receipt. The
[credit policy](docs/research-commons/CREDIT_POLICY.md) explains how contributions
are attributed.

If you solve a problem, the credit is yours. If this repo helped, please cite
the release and say how. Anyone can contribute, including by formalising
mathematics already known analytically, and receive due credit.

**Experts:** email me any insight. I will do the work and fully credit you.

## Read or verify locally

[REPRODUCIBILITY](docs/REPRODUCIBILITY.md) and the
[agent workbench](docs/AGENT_WORKBENCH.md) contain the commands for checking a
claim, making a small reading or Lean checkout, and replaying a full release.
[ARCHITECTURE](ARCHITECTURE.md) and the [source map](docs/SOURCE_MAP.md)
assume no Lean and no project history.

Cloning runs no project code; there are no submodules, Git LFS filters or
hooks. Proof builds run the pinned Lean toolchain and Mathlib.
[SECURITY](SECURITY.md) explains the boundary.
Agents arriving cold start at [`AGENTS.override.md`](AGENTS.override.md); the
[agent-navigation paper](paper/systems/cold-clone-to-proof-receipt.pdf) explains that design.

<!-- BEGIN generated_corpus_at_a_glance -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Corpus at a glance

The reviewed layer a mathematician should judge: 141 curated claim records in 30 contribution families, reaching Lean source through 451 principal declaration links. `SCOPE.md` gives its shape and `docs/RESULTS.md` gives the strongest checked result per problem. The website and the papers are the human reading path.

The rest is engineering inventory. About 91% of the 156,245 declarations (142,668 across 695 modules) are machine-emitted certificate shards: one integer checked prime, one position excluded. The remainder is not all hand-written either.

| Engineering inventory | Current size |
|---|---:|
| Lean modules (the two library roots) | 1,274 |
| Formal results and supporting lemmas | 153,502 |
| Curated claim records | 141 |
| Contribution families | 30 |

Generated shards are counted as formal source and never as separate
mathematical claims. Claim records cover every status, including cited and
open, and are partitioned once.
These are navigation counts, not novelty claims. They still need expert validation.
<!-- END generated_corpus_at_a_glance -->

<!-- BEGIN generated_principal_declaration_anchors -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Following a result into Lean

The paper links each headline result to the relevant source. For a particular
topic, start with the [source map](docs/SOURCE_MAP.md); it gives the module
order without asking you to decode Lean declaration names first.
<!-- END generated_principal_declaration_anchors -->

## Citation and licence

Cite release `v0.10.0` via [CITATION.cff](CITATION.cff). Code, scripts, and
documentation are Apache-2.0. The manuscript layer, including the paper source
and rendered PDFs, is CC-BY-4.0. Prior work and the MIT-0 wrapper are recorded
in [REUSE.toml](REUSE.toml) and the [licence texts](LICENSES/Apache-2.0.txt).
[SCOPE](SCOPE.md) defines the corpus; [`CONTRIBUTING.md`](CONTRIBUTING.md)
covers corrections.
