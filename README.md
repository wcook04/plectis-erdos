<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Plectis: a public frontier across eight open Erdős problems

![System map: pipeline, problem-sized Lean worlds, public artifacts, and the clone-work-return-credit loop](.github/system-map.png)

Plectis applies AI search, computation, ordinary mathematics, and Lean to eight
long-standing open Erdős problems: 68, 243, 249, 251, 257, 269, 1041, and 1049.
**All eight problems remain open.** This repository does not solve any of them.
They are a hard stress test: the aim is to publish exact, reusable progress
that another researcher can continue.

Each problem exposes its current frontier: checked results, failed routes, and
the obligation still blocking the endpoint. Lean checks exact formal
statements, not their intended meaning, novelty, or significance.

Large-language-model agents drafted prose, Lean proofs, and software. Will Cook
set the objectives, reviewed the public claims and cited sources, and is
responsible for the release.

If you solve one, the result and credit are yours. If this repository or
Plectis materially helped, cite the release and say so. The contribution record
keeps solvers, collaborators, prior work, tools, and infrastructure distinct.

New readers should begin with [A reader's way in](HUMAN_ENTRY.md), a
command-free tour of the problems, evidence boundary, and open frontier.

Choose the checkout that matches what you want to inspect. The two sparse
manifests below are alternatives applied to the same no-checkout clone.
The proof build needs `elan`; install it from the
[Lean setup guide](https://leanprover-community.github.io/get_started.html).

```bash
# Lean source or reader files: choose one sparse manifest
git clone --depth=1 --filter=blob:none --single-branch --no-checkout https://github.com/wcook04/plectis-lean-erdos249-257.git
git -C plectis-lean-erdos249-257 show HEAD:scripts/lean-sparse-checkout | git -C plectis-lean-erdos249-257 sparse-checkout set --no-cone --stdin
git -C plectis-lean-erdos249-257 show HEAD:scripts/reader-sparse-checkout | git -C plectis-lean-erdos249-257 sparse-checkout set --no-cone --stdin
git -C plectis-lean-erdos249-257 checkout

# Complete current corpus, then inspect one claim
git clone --depth=1 --filter=blob:none --single-branch https://github.com/wcook04/plectis-lean-erdos249-257.git plectis-current
cd plectis-current
python3 scripts/verify_claims.py --claim eb_full_support
cd ..

# Blobless history for release validation
git clone --filter=blob:none --single-branch https://github.com/wcook04/plectis-lean-erdos249-257.git plectis-release

# In the Lean-source checkout, run one bounded proof build
cd plectis-lean-erdos249-257
python3 scripts/lean_fast_build.py --jobs 2 ErdosProblems.Erdos249.PeriodMultipleEscape
```

The verifier resolves the statement to its Lean declaration, paper, receipts,
and explicit stopping point. `--verify-all` checks every registered claim.
[REPRODUCIBILITY](docs/REPRODUCIBILITY.md) gives the smaller reader checkout,
the 43-module quick Lean checkout, the complete proof source, and the full
release replay. The [architecture guide](ARCHITECTURE.md) explains why those
profiles exist.

Cloning runs no project code and the repository defines no submodules, Git LFS
filters, or hooks. The verifier runs tracked Python; proof builds run the pinned
Lean toolchain and Mathlib. [SECURITY](SECURITY.md) explains the boundary and
private reporting route.

## What is here

One paper per problem, each pairing checked progress with its open obligation.

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

[**#257**](erdos-257-mersenne-support-subseries.pdf) checks full support,
finite-period noncollapse, and the coding, topology, perfectness and measure of
the Mersenne achievement set. The universal statement and the `1/2` and `1/21`
targets remain open.

[**#269**](erdos-269-three-prime-running-lcm.pdf) records that for two primes both
sums are transcendental by a paper argument. **This is not first and not
formalised.** Steve Fan posted the same argument on the erdosproblems.com #269
page on 26 June 2026 and this note was first released on 22 July 2026, so no
priority is claimed and no Lean declaration asserts it. From three primes the
problem remains open.

[**#1041**](erdos-1041-lemniscate-newton-flow.pdf) checks Newton-flow decay, ray
separation, collision geometry, and root retention. Topology and metric gluing
remain open.

[**#1049**](erdos-1049-rational-base-lambert.pdf) checks construction-specific
no-go theorems and four-jet cancellation at base `3/2`. It proves no
irrationality result, and the primitive construction remains open.

## What the checks establish

Comparator checks nineteen proof-bearing modules against separately declared
statements and a fixed axiom budget; an altered statement must be rejected.
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
its formal-source checkpoint. This public checkout is self-contained; only its
pinned Lean source is proof authority.

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

The repository began with #249 and #257 and keeps that name so old citations
resolve. The [joint #249/#257 manuscript](erdos249-257-main-paper.pdf) and the
two claim-bounded reasoning surfaces
([#249](erdos249-totient-reasoning-surface.pdf),
[#257](erdos257-mersenne-reasoning-surface.pdf)) are kept
for archive and provenance, not as a reading route; the per-problem papers are
the live route.
The [agent-navigation paper](cold-clone-to-proof-receipt.pdf) audits that route.

## Citation and licence

Citation metadata for `v0.9.0` is in [`CITATION.cff`](CITATION.cff). Code,
scripts, and documentation are Apache-2.0; the manuscript layer is CC-BY-4.0, and
[`REUSE.toml`](REUSE.toml) is complete. Corrections are received through the
issue forms; [`CONTRIBUTING.md`](CONTRIBUTING.md) explains the local checks and
credit route, [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md) states the participation
standard, and [`SECURITY.md`](SECURITY.md) gives the private route.

<!-- BEGIN generated_corpus_at_a_glance -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Corpus at a glance

The layer a mathematician should judge is small: 130 curated claim records in 30 contribution families, reaching Lean source through 404 principal declaration links. `SCOPE.md` gives its shape and `docs/RESULTS.md` gives the strongest checked result per problem.

The rest is engineering inventory. About 93% of the 153,671 declarations (142,668 across 696 modules) are machine-emitted certificate shards: one integer checked prime, one position excluded. The remainder is not all hand-written either.

| Engineering inventory | Current size |
|---|---:|
| Lean modules (the two library roots) | 1,058 |
| Formal results and supporting lemmas | 151,397 |
| Curated claim records | 130 |
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
