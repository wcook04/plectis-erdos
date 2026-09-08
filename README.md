<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Plectis: research on eight open Erdős problems

![System map: pipeline, problem-sized Lean worlds, public artifacts, and the clone-work-return-credit loop](.github/system-map.png)

For a monic cubic whose three roots lie in the open unit disc, Lean proves
that two root occurrences can be joined inside the open unit lemniscate by
an explicit two-segment path of length strictly less than two. Its endpoints
are distinct when the polynomial is squarefree; repeated roots permit a
constant path. See the [complete theorem](https://github.com/wcook04/plectis-erdos/blob/bb4e24651b37cd096d3749ef299c3317930b3a3b/ErdosProblems/Erdos1041/PaperCubicCompletion.lean#L297).

This repository studies eight Erdős problems: 68, 243, 249, 251, 257, 269,
1041, and 1049. It contains Lean proofs, computations, papers, failed
approaches, and precise remaining questions. The cubic theorem settles the
degree-three case of #1041. It does not solve the unrestricted problem; all
eight problems remain open in their unrestricted forms.

The work was developed inside a private research system built with coding
agents. This public repository carries its own navigation, validation, and
contribution workflows, so the released work can be read, checked, and
continued without that system. Individual results have different statuses,
stated in [RESULTS](docs/RESULTS.md) and in their source records. Lean checks
formal statements; what a result means, whether it is new, and whether it
matters need separate mathematical judgement.

Large-language-model agents drafted prose, proofs, and software. Will Cook
reviewed the claims and sources and is responsible for the release.

If you solve one, the result and credit are yours. If this repository or
Plectis materially helped, cite the release and say so. If useful, star or share
the repository so another researcher finds it.
The contribution record keeps solvers, collaborators, prior work, tools, and
infrastructure distinct.

Three ways in, each sufficient on its own. Read a problem:
[A reader's way in](HUMAN_ENTRY.md) is a command-free tour of the problems and
the evidence boundary. Check a stated result: the second block below runs the
claim verifier. Continue the work: [start a bounded research shift](docs/FRONTIER_RELAY.md)
from one exact public revision.

Choose one checkout. Make one no-checkout clone, then apply exactly one of
the three sparse manifests to it; they are alternatives, and applying two
leaves the last one in place. The proof build needs `elan`; install it from
the [Lean setup guide](https://leanprover-community.github.io/get_started.html).

```bash
# One no-checkout clone. Then apply ONE manifest from the three blocks below.
git clone --depth=1 --filter=blob:none --single-branch --no-checkout https://github.com/wcook04/plectis-erdos.git
```

```bash
# Manifest 1 of 3: the 43-module quick proof checkout
git -C plectis-erdos cat-file -e HEAD:scripts/lean-quick-sparse-checkout && git -C plectis-erdos show HEAD:scripts/lean-quick-sparse-checkout | git -C plectis-erdos sparse-checkout set --no-cone --stdin
git -C plectis-erdos checkout
```

```bash
# Manifest 2 of 3: the full Lean source, then one bounded proof build
git -C plectis-erdos cat-file -e HEAD:scripts/lean-sparse-checkout && git -C plectis-erdos show HEAD:scripts/lean-sparse-checkout | git -C plectis-erdos sparse-checkout set --no-cone --stdin
git -C plectis-erdos checkout
cd plectis-erdos && python3 scripts/lean_fast_build.py --jobs 2 ErdosProblems.Erdos249.PeriodMultipleEscape
```

```bash
# Manifest 3 of 3: reader files (papers, maps, claim records; no Lean source)
git -C plectis-erdos cat-file -e HEAD:scripts/reader-sparse-checkout && git -C plectis-erdos show HEAD:scripts/reader-sparse-checkout | git -C plectis-erdos sparse-checkout set --no-cone --stdin
git -C plectis-erdos checkout
```

```bash
# Complete current corpus, fetch its pinned history, then inspect one claim
git clone --depth=1 --filter=blob:none --single-branch https://github.com/wcook04/plectis-erdos.git plectis-current
cd plectis-current
git fetch --filter=blob:none --unshallow origin main
python3 scripts/verify_claims.py --claim eb_full_support
cd ..

# Blobless history for release validation
git clone --filter=blob:none --single-branch https://github.com/wcook04/plectis-erdos.git plectis-release
```

The verifier links a claim to its declaration, paper, receipts, and stopping
point; `--verify-all` checks them all.
[REPRODUCIBILITY](docs/REPRODUCIBILITY.md) gives the smaller reader checkout,
the 43-module quick Lean checkout, the complete proof source, and the full
release replay. The [architecture and repository guide](ARCHITECTURE.md) and
its [printable PDF](claim-faithful-publication-systems-paper.pdf) assume no Lean
or project history.

Cloning runs no project code and the repository defines no submodules, Git LFS
filters, or hooks. The verifier runs tracked Python; proof builds run the pinned
Lean toolchain and Mathlib. [SECURITY](SECURITY.md) explains the boundary and
private reporting route.

## What is here

Each problem has a short note and a retained long reasoning record. The
[searchable paper corpus](docs/papers/README.md) carries both, with source
links and the remaining obligations; the short notes are the first reading route.

## Problem papers

[**#68**](erdos-68-factorial-denominator-irrationality.pdf) proves that any
rational representation of the factorial-gap series has denominator
[`q > 10¹²⁰⁴⁰`](https://github.com/wcook04/plectis-erdos/blob/25ef6245d15a47548c6926369ae8f1a0f0a14a80/ErdosProblems/Erdos68/PaperCompleteFiniteSizeCertificate.lean#L58).
The finite certificate is checked in Lean. Irrationality is equivalent to
infinitely many failures of a divisibility test; that infinitude remains open.

[**#243**](erdos-243-reciprocal-tail-rigidity.pdf) characterises eventual
Sylvester recurrence by [summability of weighted excess at records of the
canonical LCM orbit](https://github.com/wcook04/plectis-erdos/blob/25ef6245d15a47548c6926369ae8f1a0f0a14a80/ErdosProblems/Erdos243/PaperCompleteR8/CanonicalWeightedRecords.lean#L268).
The equivalence assumes a positive increasing integer sequence with rational
reciprocal sum and consecutive-term ratio tending to its quadratic scale.
The [factored growth-defect form](https://github.com/wcook04/plectis-erdos/blob/d4fed71423840f70f10edf27b9ad27c22fc4f49a/ErdosProblems/Erdos243/PaperCompleteR8/GrowthDebtSummability.lean#L234) is
also checked, with the same hypotheses and actual LCM record indices.
Proving the summability condition remains open.

[**#249**](erdos-249-binary-totient-series.pdf) gives explicit bases and
reduction formulas for the sections of Euler's totient: [finite-level
all-base kernels and the full dyadic kernel](https://github.com/wcook04/plectis-erdos/blob/25ef6245d15a47548c6926369ae8f1a0f0a14a80/ErdosProblems/Erdos249/PaperCompleteR8/FullKernelAssemblies.lean#L35),
with exact dyadic level rank `2ᵉ + 1`. It also proves denominator exclusion to
about `7.96 × 10³⁴` and diagonal certificates for every `t ≤ 82`.
No unbounded producer is proved.

[**#251**](erdos-251-prime-gap-dyadic-series.pdf) checks the prime-gap identity
and a tail-shift equivalence. The concrete prime-tail bridge remains open.
A [synthetic countermodel](https://github.com/wcook04/plectis-erdos/blob/d4fed71423840f70f10edf27b9ad27c22fc4f49a/ErdosProblems/Erdos251/AllResidueLogarithmicR9.lean#L503) has positive even,
non-eventually-periodic coefficients bounded by 4 log(n+1)+24, with values
2 and 4 recurring arbitrarily late in every index residue class. Its complete
dyadic sum is 6, every tail shift is integral, and its cumulative positions
satisfy P_n/(n log n)→1. These positions are not asserted to be prime.

[**#257**](erdos-257-mersenne-support-subseries.pdf) checks full support,
finite-period noncollapse, and the Mersenne achievement set's topology and
measure. The universal statement and the `1/2` and `1/21` targets remain open.
The [exact span bounds](https://github.com/wcook04/plectis-erdos/blob/d4fed71423840f70f10edf27b9ad27c22fc4f49a/ErdosProblems/Erdos257/PaperCompleteR8/GeometryUpgrade.lean#L94) place its total weight strictly
between 1.60669 and 1.60670. A [finite-prefix certificate](https://github.com/wcook04/plectis-erdos/blob/d4fed71423840f70f10edf27b9ad27c22fc4f49a/ErdosProblems/Erdos257/PaperCompleteR8/FinitePrefixExclusion.lean#L46)
excludes the interval (2/3,1), including 3/4; this classical gap does not settle
either distinguished target.

[**#269**](erdos-269-three-prime-running-lcm.pdf) records a two-prime
transcendence argument. **This is not first and not formalised.** Steve Fan
posted the same argument on erdosproblems.com on 26 June 2026, before this note;
no priority or Lean theorem is claimed. Three or more primes remain open.

[**#1041**](erdos-1041-lemniscate-newton-flow.pdf) proves the complete cubic
path theorem above, including containment, continuity, rectifiability, and
the strict length bound. The proof combines a
[closed-disc root count](https://github.com/wcook04/plectis-erdos/blob/bb4e24651b37cd096d3749ef299c3317930b3a3b/ErdosProblems/Erdos1041/PaperCubicSchur.lean#L283) with the
[reflected critical-value inequality](https://github.com/wcook04/plectis-erdos/blob/bb4e24651b37cd096d3749ef299c3317930b3a3b/ErdosProblems/Erdos1041/PaperReflectedCompletion.lean#L254).
The corpus also checks Newton-flow decay, ray separation, collision geometry,
and root retention. The unrestricted path problem remains open. From the
proof checkout, run `lake build ErdosProblems.Erdos1041.PaperCubicCompletion`.

The [monic-cubic adapter](https://github.com/wcook04/plectis-erdos/blob/3be82b1a7340284aea72e9a5c8493cb020843921/ErdosProblems/Erdos1041/PaperCubicMonic.lean#L32)
derives the root enumeration from monicity and degree three. It supplies the
same connector under the usual polynomial hypotheses; squarefreeness makes
its endpoints distinct. A separate [central-disk theorem](https://github.com/wcook04/plectis-erdos/blob/3be82b1a7340284aea72e9a5c8493cb020843921/ErdosProblems/Erdos1041/FreePointCentralCompletion.lean#L39)
proves that, for every positive `m` and complex points with
`|c_j| ≤ sqrt(1-exp(-2))`, the sum of the geometric row means of
`|1-conj(c_j)c_k|` is at most `m`. This includes the analytic energy and
variance proofs, but asserts neither an equality case nor a full-disk bound.
It does not itself produce a short connecting path.

The analytic proof now also has checked [Poisson norm-square majorization](https://github.com/wcook04/plectis-erdos/blob/d4fed71423840f70f10edf27b9ad27c22fc4f49a/ErdosProblems/Erdos1041/PoissonNormSquare.lean#L114) for a holomorphic function continuous on the closed unit disk, and [termwise circle integration](https://github.com/wcook04/plectis-erdos/blob/d4fed71423840f70f10edf27b9ad27c22fc4f49a/ErdosProblems/Erdos1041/CircleSeriesTransport.lean#L49) under a summable uniform norm bound. The weighted kernel identity is checked as well. These are analytic steps toward the full-disk weighted inequality; they do not enlarge the checked central-region free-point conclusion.

[**#1049**](erdos-1049-rational-base-lambert.pdf) proves an
[Archimedean obstruction for approximants valid at every base greater than
one](https://github.com/wcook04/plectis-erdos/blob/25ef6245d15a47548c6926369ae8f1a0f0a14a80/ErdosProblems/Erdos1049/PaperShortCapR9.lean#L162):
under the stated quadratic degree, height, and error asymptotics, the decay
rate cannot exceed the degree rate. It also checks construction-specific
obstructions and four-jet cancellation at base `3/2`. No irrationality result
is proved; the primitive construction remains open.

The [no-decay theorem](https://github.com/wcook04/plectis-erdos/blob/3be82b1a7340284aea72e9a5c8493cb020843921/ErdosProblems/Erdos1049/PaperNoDecayR9.lean#L69)
further shows that, under its base-uniform polynomial degree, height and
error hypotheses, the actual-degree homogenised remainders cannot tend to
zero at natural ratios `a/b` with `1 ≤ b < a < b²`. It requires no convergence
of the normalised degrees. This is an obstruction to that approximation
method; it asserts neither divergence nor irrationality.

## What the checks establish

Comparator checks nineteen proof-bearing modules against separately declared
statements and a fixed axiom budget; an altered statement must be rejected.
[`formalization.yaml`](formalization.yaml) records each selected result's source,
boundary, `sorry` count, and axioms. The
[verification packet](docs/EXTERNAL_VERIFICATION.md) covers all eight problem
programmes. Comparator does not assess exposition, citations, computation,
meaning, novelty, or significance.

Six focused packages have authenticated positive and deliberate-mismatch
receipts at [`3dda234b`](https://github.com/wcook04/plectis-erdos/actions/runs/34195347556).
Those receipts cover their exact selected statements at that commit. Expanded
packages and later analytic results require their own replay; a wrapper or
a successful Lean build does not extend the earlier Comparator coverage.

[`docs/claims.json`](docs/claims.json) owns every claim record and its status,
[`docs/PALOMAR_RESULT_SHOWCASE.json`](docs/PALOMAR_RESULT_SHOWCASE.json) owns the
reader-priority ranking, and [prior art](docs/PRIOR_ART.md) records classical,
subsuming, and earlier public work. Status labels describe evidence rather than
score it: a checked rendering is not a priority claim, and a conditional
reduction still depends on its named open condition.

`v0.9.0` is the citation anchor, and [`docs/claims.json`](docs/claims.json) pins
its formal-source checkpoint. This public checkout is self-contained; only its
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

The repository began with #249 and #257 and was named for them; it is now
`plectis-erdos`, and the old address `plectis-lean-erdos249-257` redirects, so
existing citations resolve. The [joint #249/#257 manuscript](erdos249-257-main-paper.pdf) and the
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

The independently authored `.agents/skills/plectis-frontier` distribution
wrapper is the narrow MIT-0 exception recorded in `REUSE.toml`. It does not
relicense the research corpus or transfer credit for participants' mathematics.

<!-- BEGIN generated_corpus_at_a_glance -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Corpus at a glance

The layer a mathematician should judge is small: 143 curated claim records in 30 contribution families, reaching Lean source through 432 principal declaration links. `SCOPE.md` gives its shape and `docs/RESULTS.md` gives the strongest checked result per problem.

The rest is engineering inventory. About 92% of the 154,750 declarations (142,668 across 695 modules) are machine-emitted certificate shards: one integer checked prime, one position excluded. The remainder is not all hand-written either.

| Engineering inventory | Current size |
|---|---:|
| Lean modules (the two library roots) | 1,143 |
| Formal results and supporting lemmas | 152,257 |
| Curated claim records | 143 |
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

## Further in

If the mathematics has held your attention this far, there is more behind
it, and you can go as deep as you like.

The whole repository is also a website,
[wcook04.github.io/plectis](https://wcook04.github.io/plectis/): the eight
problems as pages, every paper readable in the browser with its PDF and LaTeX
source beside it, and a glossary that explains the vocabulary on hover. The
[Will Cook page](https://wcook04.github.io/) is the shorter front door to the
same work.

The mathematics was produced inside a private research system built with
coding agents. The site's front page says why that system exists: so that work
done with AI can be understood, checked, and continued. Two public parts of it
are open. The [Plectis repository](https://github.com/wcook04/plectis) holds
88 small tools taken from it, each stating one claim, taking one fixed input,
running one local check and writing a receipt you can read; its
[paper](https://wcook04.github.io/plectis/maths/papers/plectis-public-system.html)
says what a stranger can and cannot conclude from such a check. Three
[recorded videos](https://wcook04.github.io/plectis/#demo-videos) show the
private frontend itself, in one-, five- and thirty-minute cuts. They are
demonstrations, not validation records.

Down that rabbit hole: the component map, the agent workflows the system runs
on, and how a claim of finished work is read against the evidence before it
counts. None of it is needed to read or continue the mathematics above.

## Where I actually am

[Where I actually am](HUMAN_ENTRY.md#where-i-actually-am) says who wrote this and
why it was released in the state it is in. The
[routes are on the site](https://wcook04.github.io/plectis/#contact).
