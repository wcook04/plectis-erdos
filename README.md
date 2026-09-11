<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Plectis: research on eight open Erdős problems

![Eight open problems: papers, checked results, failed routes, and questions another researcher can continue](.github/system-map.png)

The full-support Mersenne series is irrational in every integer base `b ≥ 2`,
and the base-2 achievement set has measure one. That is a completed theorem
family in this checkout, not a solution of Erdős #257: every infinite support,
and the `1/2` and `1/21` branches, remain open.

This public commons also holds checked work on seven further Erdős problems —
[68](https://www.erdosproblems.com/68),
[243](https://www.erdosproblems.com/243),
[249](https://www.erdosproblems.com/249),
[251](https://www.erdosproblems.com/251),
[257](https://www.erdosproblems.com/257),
[269](https://www.erdosproblems.com/269),
[1041](https://www.erdosproblems.com/1041) and
[1049](https://www.erdosproblems.com/1049).
**All eight problems remain open.** This checkout does not solve them. The checkout is self-contained:
eight short notes, eight long reasoning records, Lean sources, a Comparator
gate, and the checks that bind claims to source. It is not an entrypoint into
any private development system. The notes follow Terence Tao's public guidance
on how AI mathematics should be expositioned; that is a writing standard, not
a review of this project.

I am responsible for all claims, sources and the release. Plectis is an
independent, AI-assisted prototype. It has had no independent mathematical
review, and I need help. We show the routes that stopped so later models and
mathematicians can reuse them; novelty and significance still need human judgement. If you solve a problem, the credit is yours. If this
repo helped, please cite the release and say how. Anyone can contribute,
including by formalising mathematics already known analytically, and receive
due credit. Start with [A reader's way in](HUMAN_ENTRY.md). A longer personal
note lives there as well.

The [website](https://wcook04.github.io/plectis/) is the human browse path:
[mathematics pages](https://wcook04.github.io/plectis/maths/) for each short
and long paper. Navigation, validation and contribution workflows also plug
into coding agents via [`AGENTS.override.md`](AGENTS.override.md); they are
not required to read the papers.

## Problem papers

For a first look, start with **#257** for full-support irrationality and
achievement-set measure, or **#249** for exact kernel rank, finite certificates
and recorded failed routes. Progress by problem is in [RESULTS](docs/RESULTS.md).
Do not infer results from private or unreleased work.

- **[#68](https://www.erdosproblems.com/68)** · Factorial-denominator irrationality ·
  [short paper](paper/68/erdos-68-factorial-denominator-irrationality.pdf) ·
  [longer paper](paper/68/erdos68-factorial-reasoning-surface.pdf).
  Irrationality is equivalent to cofinally many non-unit factorial carries;
  producing those carries remains open.
- **[#243](https://www.erdosproblems.com/243)** · Reciprocal-tail rigidity ·
  [short paper](paper/243/erdos-243-reciprocal-tail-rigidity.pdf) ·
  [longer paper](paper/243/erdos243-reciprocal-tail-reasoning-surface.pdf).
  After Koizumi's normalised vanishing, a bounded or summably small negative
  centred error forces eventual Sylvester recurrence. The unbounded mixed-sign
  regime remains open. Duverney (2001) and the Tao–Kovac line are prior art
  on the page; cubic-rate vanishing is not claimed as empty-page news.
- **[#249](https://www.erdosproblems.com/249)** · Binary totient series ·
  [short paper](paper/249/erdos-249-binary-totient-series.pdf) ·
  [longer paper](paper/249/erdos249-totient-reasoning-surface.pdf).
  Exact dyadic-kernel rank `2^e + 1`, denominator exclusion to about
  `7.96 × 10³⁴`, diagonal certificates through `t ≤ 82`, and no-go theorems
  for the shortcuts. This is not an infinite witness for irrationality.
- **[#251](https://www.erdosproblems.com/251)** · Prime-gap dyadic series ·
  [short paper](paper/251/erdos-251-prime-gap-dyadic-series.pdf) ·
  [longer paper](paper/251/erdos251-prime-gap-reasoning-surface.pdf).
  The prime-to-gap identity is already Tao's (summation by parts on the
  forum); this checkout checks consequences and the cofinal non-integral tail
  shift. The actual-prime tail witness remains open.
- **[#257](https://www.erdosproblems.com/257)** · Mersenne-support subseries ·
  [short paper](paper/257/erdos-257-mersenne-support-subseries.pdf) ·
  [longer paper](paper/257/erdos257-mersenne-reasoning-surface.pdf).
  Irrationality for the full support in every integer base `b ≥ 2`, and for
  structured supports under summability; the base-2 Mersenne achievement set has
  measure one. Every infinite support, and the `1/2` and `1/21` branches,
  remain open and are kept distinct from the full-support theorem.
- **[#269](https://www.erdosproblems.com/269)** · Three-prime running LCM ·
  [short paper](paper/269/erdos-269-three-prime-running-lcm.pdf) ·
  [longer paper](paper/269/erdos269-running-lcm-reasoning-surface.pdf).
  Three-prime height identity, nonsingular kernel minors, and the `(2,3,5)`
  minor `-1/15`. The two-prime transcendence argument is Steve Fan's
  ([erdosproblems.com/269](https://www.erdosproblems.com/forum/thread/269),
  26 June 2026); no priority or Lean theorem is claimed for that. Three or
  more primes remain open.
- **[#1041](https://www.erdosproblems.com/1041)** · Lemniscates and Newton flow ·
  [short paper](paper/1041/erdos-1041-lemniscate-newton-flow.pdf) ·
  [longer paper](paper/1041/erdos1041-lemniscate-reasoning-surface.pdf).
  Newton-flow decay, ray-separating translations, and perturbative root
  retention are the checked supporting results. A length-`<2` curve remains
  the ordinary headline here; forum discussion of a degree-7 counterexample
  is not a theorem of this repository.
- **[#1049](https://www.erdosproblems.com/1049)** · Rational-base Lambert series ·
  [short paper](paper/1049/erdos-1049-rational-base-lambert.pdf) ·
  [longer paper](paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf).
  Exact rational-base tail recurrence, sharp Hankel order, and a checked height
  region that includes `31/4`. No irrationality at `3/2`; the approximant
  construction remains open.

The [joint #249/#257 manuscript](paper/archive/erdos249-257-main-paper.pdf) is
archive and provenance only; the papers above are the current entrances.

## What the checks establish

Three things come between a Lean proof and a claim in this repo. The
[comprehension graph](docs/semantic/README.md) is the map: every declaration in
the atlas, the statements they make, and typed relations between them, so a
theorem can be seen as a reformulation or finite instance of the open problem
rather than the problem itself. Comparator is a second formal check: nineteen
proof-bearing modules against separately declared statements and a fixed axiom
budget, with [`formalization.yaml`](formalization.yaml) recording source,
boundary, `sorry` count and axioms for each. A separate Palomar registry cut
is unfinished work in another session and is not a claim of this edition.
[`docs/PALOMAR_RESULT_SHOWCASE.json`](docs/PALOMAR_RESULT_SHOWCASE.json) remains
the local ranking projection only.

The [verification dossier](docs/EXTERNAL_VERIFICATION.md) covers all eight
problem programmes; the [methodology](METHODOLOGY.md) outlines what each check does
and does not establish. [`docs/claims.json`](docs/claims.json) covers claim
status and [prior art](docs/PRIOR_ART.md) records earlier and subsuming work.
None of it decides whether a statement captures the intended problem, is new,
or solves anything, which requires expert review.

Two papers explain the design. [Problem-Sized Lean Worlds](paper/systems/claim-faithful-publication-systems-paper.pdf)
is how finding a result, checking it and deciding what may be claimed are kept
separate. [From Spare Compute to Cumulative Mathematics](paper/systems/open-source-mathematics-strategy.pdf)
is why the work is public and how credit is recorded.

## Contribute

An idea, a correction, a counterexample, a failed route with a checkable
reason, clearer exposition, a validation of a claim or a repaired check all
count. Open the
[plain-language research-progress form](https://github.com/wcook04/plectis-erdos/issues/new?template=research_progress.yml)
or a pull request. Accepted work gets a public receipt. The
[credit policy](docs/research-commons/CREDIT_POLICY.md) gives the exact
boundary. You can also email me.

## Read or verify locally

- **Read** a problem in [A reader's way in](HUMAN_ENTRY.md).
- **Check** a stated result with the claim verifier in
  [REPRODUCIBILITY](docs/REPRODUCIBILITY.md).
- **Continue** from one exact public revision via the
  [frontier relay](docs/FRONTIER_RELAY.md) and [CONTRIBUTING](CONTRIBUTING.md).
- **Experts:** [email me](https://wcook04.github.io/plectis/#contact) any
  insight. I will do the work and fully credit you.

Every command lives in [REPRODUCIBILITY](docs/REPRODUCIBILITY.md) and the
[agent workbench](docs/AGENT_WORKBENCH.md): claim verifier, reader-only and
quick Lean checkouts, complete proof source, full release replay.
[ARCHITECTURE](ARCHITECTURE.md) and the [source map](docs/SOURCE_MAP.md)
assume no Lean and no project history.

Cloning runs no project code; there are no submodules, Git LFS filters or
hooks. Proof builds run the pinned Lean toolchain and Mathlib.
[SECURITY](SECURITY.md) explains the boundary.
Agents arriving cold start at [`AGENTS.override.md`](AGENTS.override.md); the
[agent-navigation paper](paper/systems/cold-clone-to-proof-receipt.pdf) explains that design.

## Citation and licence

Cite release `v0.9.0` via [CITATION.cff](CITATION.cff). Code, scripts, and
documentation are Apache-2.0. The manuscript layer, including the paper source
and rendered PDFs, is CC-BY-4.0. Prior work and the MIT-0 wrapper are recorded
in [REUSE.toml](REUSE.toml) and the [licence texts](LICENSES/Apache-2.0.txt).
[SCOPE](SCOPE.md) defines the corpus; [`CONTRIBUTING.md`](CONTRIBUTING.md)
covers corrections.
[Where I actually am](HUMAN_ENTRY.md#where-i-actually-am) says why this is
being released now.

<!-- BEGIN generated_corpus_at_a_glance -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Corpus at a glance

The layer a mathematician should judge has been denoised (tried): 140 curated claim records in 30 contribution families, reaching Lean source through 449 principal declaration links. `SCOPE.md` gives its shape and `docs/RESULTS.md` gives the strongest checked result per problem. Again, agents advised, website or papers are what's designed for humans.

The rest is engineering inventory. About 91% of the 156,245 declarations (142,668 across 695 modules) are machine-emitted certificate shards: one integer checked prime, one position excluded. The remainder is not all hand-written either.

| Engineering inventory | Current size |
|---|---:|
| Lean modules (the two library roots) | 1,274 |
| Formal results and supporting lemmas | 153,502 |
| Curated claim records | 140 |
| Contribution families | 30 |

Generated shards are counted as formal source and never as separate
mathematical claims. Claim records cover every status, including cited and
open, and are partitioned once.
These are navigation counts, not novelty claims; this needs expert validation, again: credit provided for this. With funding I would also be happy to provide some kind of compensation, alas, currently challenged in that department.
<!-- END generated_corpus_at_a_glance -->

<!-- BEGIN generated_principal_declaration_anchors -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Following a result into Lean

The paper links each headline result to the relevant source. For a particular
topic, start with the [source map](docs/SOURCE_MAP.md); it gives the module
order without asking you to decode Lean declaration names first.
<!-- END generated_principal_declaration_anchors -->
