<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Plectis: research on eight open Erdős problems

![Eight open problems: papers, checked results, failed routes, and open questions another researcher can continue](.github/system-map.png)

We focused on eight arbitrarily hard Erdős problems: 68, 243, 249, 251, 257,
269, 1041 and 1049. **All eight problems remain open.** This repository does
not solve any of them. It holds formal statements, Lean checks, a Comparator
gate and a Palomar submission, and two papers per problem, one short and one
long, written with Terence Tao's public guidance on how AI mathematics should
be reported in mind.

I prioritised expository quality and a collaborative structure over trying to
solve the problems; I hope to solve them with others rather than alone. With
the unreleased frontier models, these could probably be solved if enough
compute were poured at them. The difference here is that we show every one of
the routes that stopped, and turn intermediary findings into something reusable
by mathematicians who actually understand the material, and by later models.
Meaning, novelty and significance still need human judgement.

The repo is built around AI agents; I would not recommend driving it by hand
with commands. Its navigation, validation, contribution and
mathematical-reasoning workflows plug into your own agents. Progress varies by
problem and is stated in [RESULTS](docs/RESULTS.md) and the source records your
agent can find for you. Lean checks the formal statements. Coverage is not the
100% I wanted, because I am pretty broke at this point. That is why anyone can
contribute, even by formalising maths already established analytically, and
receive due credit.

Claude Code, Codex and Cursor agents wrote every line of code. I am
responsible for all claims, sources and the release. Plectis is an independent, AI-assisted prototype, not
something I am declaring finished. It has had no independent mathematical
review, and I need help to get anywhere near that.

If you solve a problem, the credit and the result are yours. If this repo or my
intermediary progress helped, please cite this release and say how, so others
find it and we make progress together instead of hoarding partial results out
of fear of being scooped, or rebuilding the same infrastructure instead of
improving one cumulatively.

The [website](https://wcook04.github.io/plectis/maths/) is the ergonomic way
to browse: each short paper, each long paper, and a map to the relevant Lean
sources. The API behind it is machine generated so nothing hard-coded drifts.

Ways in:

- **Read** a problem in [A reader's way in](HUMAN_ENTRY.md), a command-free
  tour of the problems and the evidence boundary.
- **Check** a stated result with the claim verifier in
  [REPRODUCIBILITY](docs/REPRODUCIBILITY.md).
- **Continue** from where I left off: a bounded research shift from one exact
  public revision, via the [frontier relay](docs/FRONTIER_RELAY.md) and
  [CONTRIBUTING](CONTRIBUTING.md). Use a coding agent. This is the part I am
  most excited about.
- **Experts:** [email me](https://wcook04.github.io/plectis/#contact) any
  insight. I will do the work and fully credit you for the insight and whatever
  follows from it.

## Problem papers

For a first look, start with **#257** for restricted irrationality and
achievement sets, or **#249** for exact reductions, finite certificates and
recorded failed routes.

- **#68** · Factorial-denominator irrationality ·
  [paper](erdos-68-factorial-denominator-irrationality.pdf) ·
  [record](erdos68-factorial-reasoning-surface.pdf).
  Reduces irrationality to infinitely many failures of one divisibility test;
  producing those failures remains open.
- **#243** · Reciprocal-tail rigidity ·
  [paper](erdos-243-reciprocal-tail-rigidity.pdf) ·
  [record](erdos243-reciprocal-tail-reasoning-surface.pdf).
  Bounded or summably small negative error is controlled after Koizumi's
  normalised vanishing; the unbounded mixed-sign regime remains open.
- **#249** · Binary totient series ·
  [paper](erdos-249-binary-totient-series.pdf) ·
  [record](erdos249-totient-reasoning-surface.pdf).
  Exact rank of the dyadic totient kernel, finite denominator exclusions,
  conditional routes to irrationality, and no-go theorems for the shortcuts.
  The infinitely many witnesses required are not produced.
- **#251** · Prime-gap dyadic series ·
  [paper](erdos-251-prime-gap-dyadic-series.pdf) ·
  [record](erdos251-prime-gap-reasoning-surface.pdf).
  The prime-gap identity, tail-shift equivalences and a coefficient-only
  countermodel. The concrete prime-tail bridge remains open.
- **#257** · Mersenne-support subseries ·
  [paper](erdos-257-mersenne-support-subseries.pdf) ·
  [record](erdos257-mersenne-reasoning-surface.pdf).
  Irrationality for the full support in every integer base and for structured
  supports under summability, plus the Mersenne achievement set's topology and
  measure. Every infinite support, and the 1/2 and 1/21 branches, remain open.
- **#269** · Three-prime running LCM ·
  [paper](erdos-269-three-prime-running-lcm.pdf) ·
  [record](erdos269-running-lcm-reasoning-surface.pdf).
  Three-prime LCM cell geometry, height identities and a rank obstruction. The
  two-prime argument in the record is Steve Fan's (erdosproblems.com, 26 June
  2026, before this note); no priority or Lean theorem is claimed. Three or
  more primes remain open.
- **#1041** · Lemniscates and Newton flow ·
  [paper](erdos-1041-lemniscate-newton-flow.pdf) ·
  [record](erdos1041-lemniscate-reasoning-surface.pdf).
  Newton-flow decay, ray separation, collision geometry and root retention.
  Topology and metric gluing remain open.
- **#1049** · Rational-base Lambert series ·
  [paper](erdos-1049-rational-base-lambert.pdf) ·
  [record](erdos1049-rational-base-lambert-reasoning-surface.pdf).
  The rational-base tail recurrence and no-go theorems for specific Padé
  constructions, including four-jet cancellation at base 3/2. No irrationality
  result; the approximant construction remains open.

The [joint #249/#257 manuscript](erdos249-257-main-paper.pdf) is kept for
archive and provenance only; the papers above are the current entrances.

## What the checks establish

Comparator checks nineteen proof-bearing modules against separately declared
statements and a fixed axiom budget; [`formalization.yaml`](formalization.yaml)
records source, boundary, `sorry` count and axioms for each. The
[verification dossier](docs/EXTERNAL_VERIFICATION.md) covers all eight problem
programmes; the [methodology](METHODOLOGY.md) says what each check does and does
not establish. [`docs/claims.json`](docs/claims.json) owns claim status,
[`docs/PALOMAR_RESULT_SHOWCASE.json`](docs/PALOMAR_RESULT_SHOWCASE.json) owns
reader-priority ranking, and [prior art](docs/PRIOR_ART.md) records earlier and
subsuming work. None of it decides whether a statement captures the intended
problem, whether a result is new, or whether a problem is solved.

## Contribute

An idea, a correction, a counterexample, a failed route with a checkable
reason, clearer exposition, or a repaired check all count. Open the
[plain-language research-progress form](https://github.com/wcook04/plectis-erdos/issues/new?template=research_progress.yml)
with no patch, or a pull request for a focused change. Accepted work gets a
public receipt naming you, the exact files or results, the starting commit, and
what was checked. The
[open-source mathematics paper](open-source-mathematics-strategy.pdf) explains
the design; the [credit policy](docs/research-commons/CREDIT_POLICY.md) gives
the exact boundary.

## Read or verify locally

Every command your agent can run lives in [REPRODUCIBILITY](docs/REPRODUCIBILITY.md) and the
[agent workbench](docs/AGENT_WORKBENCH.md), not here: the claim verifier, the
reader-only and quick Lean checkouts, the complete proof source and the full
release replay. [ARCHITECTURE](ARCHITECTURE.md) and the
[source map](docs/SOURCE_MAP.md) assume no Lean and no project history.

Cloning runs no project code; there are no submodules, Git LFS filters or
hooks. Proof builds run the pinned Lean toolchain and Mathlib.
[SECURITY](SECURITY.md) explains the boundary and the private reporting route.
Agents arriving cold start at [`AGENTS.override.md`](AGENTS.override.md); the
[agent-navigation paper](cold-clone-to-proof-receipt.pdf) explains that design.

## Citation and licence

Cite release `v0.9.0` via [CITATION.cff](CITATION.cff). Apache-2.0, with prior
work and the MIT-0 wrapper recorded in [REUSE.toml](REUSE.toml) and the
[licence texts](LICENSES/Apache-2.0.txt). [SCOPE](SCOPE.md) defines the corpus;
[`CONTRIBUTING.md`](CONTRIBUTING.md) covers corrections.
[Where I actually am](HUMAN_ENTRY.md#where-i-actually-am) says why this is
being released now.

<!-- BEGIN generated_corpus_at_a_glance -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Corpus at a glance

The layer a mathematician should judge is small: 140 curated claim records in 30 contribution families, reaching Lean source through 449 principal declaration links. `SCOPE.md` gives its shape and `docs/RESULTS.md` gives the strongest checked result per problem.

The rest is engineering inventory. About 92% of the 155,274 declarations (142,668 across 695 modules) are machine-emitted certificate shards: one integer checked prime, one position excluded. The remainder is not all hand-written either.

| Engineering inventory | Current size |
|---|---:|
| Lean modules (the two library roots) | 1,214 |
| Formal results and supporting lemmas | 152,720 |
| Curated claim records | 140 |
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
