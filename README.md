<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Plectis: a public frontier across eight open Erdős problems

Plectis is an AI-assisted public Lean corpus for Erdős Problems 68, 243, 249,
251, 257, 269, 1041, and 1049: reductions, theorems, countermodels,
boundaries, and certificates.
**All eight problems remain open. This repository does not solve them.**

**Start with one checked claim.** No Lean build is needed:

```bash
python3 scripts/verify_claims.py --claim eb_full_support
```

Prints statement, Comparator, paper, receipts, and boundary.
`--verify-all` checks all. [Read or run](#read-or-run-it) gives Lean routes.

[RESULTS](docs/RESULTS.md) → [SCOPE](SCOPE.md) → [SOURCE MAP](docs/SOURCE_MAP.md)
→ [verification](docs/EXTERNAL_VERIFICATION.md) → [prior art](docs/PRIOR_ART.md)
→ [architecture and repository guide](ARCHITECTURE.md) · [printable PDF](claim-faithful-publication-systems-paper.pdf)

The [agent-navigation paper](cold-clone-to-proof-receipt.pdf) explains the
cold-clone route. It assumes no Lean or project history. This is not a
private-system entrypoint.
Will Cook reviewed claims. **Lean source checked by the pinned Lean kernel**
is formal proof authority, not for meaning or novelty.

## Read the signal first

All eight problems remain open. The most useful first pass is mechanism-first,
not a novelty or priority ranking:

- **#257 leads with a completed unconditional endpoint theorem for full
  support.** Its checked divisor-block proof combines a bounded Bertrand/CRT
  first block, middle-window divisor-pair averaging, weighted tail control,
  and parameter closure ([source](Erdos249257/CertificateKernel.lean)); it
  proves the canonical full-support series irrational for every integer base
  `b ≥ 2`. This is not universal #257.
- A distinct adaptive-CRT extension handles every infinite pairwise-coprime
  support with summable reciprocal mass ([source](Erdos249257/CertificateKernel.lean));
  its structured-support hypotheses do not settle arbitrary infinite support.
- A deeper support route proves the base-2 series irrational under an explicit
  finite-core orthogonal-petal bouquet and uniform tail-selection predicate
  ([source](Erdos249257/SupportSunflowerDichotomy.lean)). Those structural
  hypotheses are the unresolved selector: neither is constructed for arbitrary
  supports, so this remains a conditional reduction rather than another
  settled support family.
- A separate coefficient-class theorem proves irrationality when a rational
  weight sequence is nonnegative, eventually periodic, and positive at a
  positive index in its periodic tail; denominator clearing feeds a periodic
  divisor-orbit sieve ([source](Erdos249257/CertificateKernel.lean)). This is
  not the mixed-sign or arbitrary-support theorem.
- A separate geometric boundary is substantial but different: the full
  base-2 Mersenne achievement set has Lebesgue measure one, while supported
  achievement sets have a finite-complement/zero-measure dichotomy ([source](Erdos249257/GreedyAchievementSet.lean); [source](ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean)). This classifies neither rational points nor universal irrationality.
- **#249's endpoint-facing frontier is conditional.** An actual-LCM orbit is
  approximated by an odd-rank raw block with an explicit error radius: the
  separate sufficient (not equivalent) condition
  `PowerTwoActualLcmOrbitSeparationSupply` would force the existing signed-margin
  producer and hence irrationality
  ([source](Erdos249257/TotientActualLcmOrbitSeparation.lean#L254)). Its
  quantitative separation supply is unproved, and sign/top-edge information
  does not supply it. Separately, the dyadic totient kernel has rank `2^e + 1`
  with an explicit odd-core basis ([source](Erdos249257/TotientKernelConditional.lean));
  its all-base extension is conditional on affine independence. That rank
  spine is a finite-level mechanism, not a rationality-to-finite-rank bridge
  or a solution of the binary totient endpoint. The public actual-LCM
  consumer also exposes one coherent support family: `actualLcmTailDiff_shift_pos`
  gives the positive shift, `actualLcm_trueEndpointSurvivor_neg` records the
  negative true survivor, and `actualLcm_integral_forces_topEdgeResidue`
  identifies the exact top-edge residue
  ([consumer](ExternalVerification/Challenge.lean#L198)). Positivity does not
  exclude that survivor, so no cofinal separation supply is claimed. A separate
  public
  [first-harmonic pivot route](ExternalVerification/Challenge.lean) is now
  represented in Comparator: its four-term decomposition and sufficient
  `9X/10` certificate budget are exposed alongside a conditional cofinal
  residual-decorrelation endpoint. A concrete overlap at `X=16` shows why
  global supplier-prime isolation is unavailable, and the cofinal producer
  remains open
  ([source](Erdos249257/FirstHarmonicPivot.lean#L514)).
- **#68 has an exact endpoint reduction.** Irrationality is equivalent to
  cofinally many strict factorial-top divisibility misses, equivalently
  non-unit carries ([source](ErdosProblems/Erdos68/FactorialZeroPlateau.lean));
  the cofinal producer is still open.

The next boundary results are also worth reading: #243 excludes bounded-rise
and periodic negative-orbit regimes ([source](ErdosProblems/Erdos243/ReciprocalTailRigidity.lean));
#251 gives unbounded prime gaps and an exact prime-gap equivalence, while a
public, non-Comparator [denominator classifier](ExternalVerification/Challenge.lean#L245)
reduces rationality of a dyadic tail to eventual integrality of one positive
shift ([source](ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)); #269 checks a
running-LCM height identity and rank-two obstruction, and a separate
weighted-phase carry observer splits each digit into a finite residue digit
plus an uncontrolled integral coboundary; only its explicit finite-dimensional
factorisation yields finite realised span
([source](ErdosProblems/Erdos269/WeightedPhaseCarry.lean#L109)); #1041 isolates
finite ray separation/root retention while a topology/gluing step is missing
([source](ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean)); and #1049
rules out a literal `3/2` corridor while a finite four-jet/Padé obstruction
records selector collisions and content barriers, leaving irrationality open
([source](ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean)).

This order is a value audit of the 40 declarations in the committed Comparator
roster, not a claim that the remaining rows are unimportant. [RESULTS](docs/RESULTS.md#signal-audit-dispositions)
records the promote/retain/consolidate/demote/replace/long-tail-only decisions
and their mathematical reasons; the per-problem sections and [source map](docs/SOURCE_MAP.md)
keep every lower-signal route reachable.

Finite searches, routine certificate shards, cited inputs, and conditional
predicate stacks remain valuable evidence, but they are supporting routes—not
cofinal results or solutions. [RESULTS](docs/RESULTS.md) gives the complete
signal audit, exact hypotheses, evidence, and surviving boundary.

## Problem papers

[`docs/papers/corpus.json`](docs/papers/corpus.json) indexes the papers; map is
readable without a query or network.

| Problem | Question |
|---|---|
| **#68** | Is `∑_{n≥2} 1/(n!−1)` irrational? |
| **#243** | Does rationality of a fast sequence's reciprocal sum force Sylvester recurrence? |
| **#249** | Is `∑ φ(n)/2ⁿ` irrational? |
| **#251** | Is the prime-gap dyadic series irrational? |
| **#257** | Is `∑_{n∈A} 1/(2ⁿ-1)` irrational for every infinite `A ⊆ ℕ_{>0}`? |
| **#269** | Is the running-LCM reciprocal sum irrational for at least two primes? |
| **#1041** | Do two unit-disc roots have a curve `<2` in their open lemniscate? |
| **#1049** | Which rational bases give an irrational Lambert series, starting at `3/2`? |

### Eight open endpoints

Links name checked routes and limits; reductions are not solutions.

- [**#68: factorial denominators**](erdos-68-factorial-denominator-irrationality.pdf) — [cofinal equivalence](ErdosProblems/Erdos68/FactorialZeroPlateau.lean): irrationality iff cofinally strict factorial-top misses divisibility; [band](ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean): nonzero-moment cancellation forces index ≥2d. q≥67; 300000 external; cofinal producer open.
- [**#243: reciprocal-tail rigidity**](erdos-243-reciprocal-tail-rigidity.pdf) — [bounded-rise obstruction](ErdosProblems/Erdos243/ReciprocalTailRigidity.lean): bounded rises cannot avoid fresh pairwise-coprime moduli as `u`→∞; normalized-vanishing no-go; mixed-sign bridge open.
- [**#249: binary totients**](erdos-249-binary-totient-series.pdf) — [actual-LCM frontier](Erdos249257/TotientActualLcmOrbitNonintegrality.lean): irrationality iff cofinal non-integrality; [quantitative separation bridge](Erdos249257/TotientActualLcmOrbitSeparation.lean#L254): a sufficient, non-equivalent cofinal orbit-to-signed-margin reduction, with its supply open; [public support](ExternalVerification/Challenge.lean#L198): positive corridor, negative true survivor, and exact top-edge residue; none excludes the survivor or supplies cofinal separation.
- [**#251: prime-gap dyadic tails**](erdos-251-prime-gap-dyadic-series.pdf) — [tail equivalence](ErdosProblems/Erdos251/PrimeGapDyadicTail.lean): irrationality iff cofinally nonintegral tail shifts under its checked recurrence; [public integral-shift classifier](ExternalVerification/Challenge.lean#L245) ([source](ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1279)): rationality iff one positive shift is eventually integral for a dyadic tail recurrence; it remains outside Comparator and supplies no prime-tail bridge.
- [**#257: reciprocal Mersenne subseries**](erdos-257-mersenne-support-subseries.pdf) — [shifted tails](Erdos249257/RationalSupportCarrySkeleton.lean): positive/recursive; [two-adic band](Erdos249257/HalfGreedyTwoThirdsBand.lean) excludes odd 1,3,5 (sharp at 7); [composite dilation](Erdos249257/CompositeDilationDefect.lean): foreign-divisor budget (zero for prime support); arbitrary defects lack a bound/tail selector; [pairwise-coprime](Erdos249257/CertificateKernel.lean): adaptive CRT gives irrationality for infinite pairwise-coprime `A` with summable reciprocals; hypotheses explicit; [half frontier](Erdos257/HalfCounterexampleFrontier.lean) could refute universality if built. Half-membership open.
- [**#269: three-prime running lcms**](erdos-269-three-prime-running-lcm.pdf) — [height](ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean): distinct-prime LCM = `threePrimeHeight`; rank-2 minor `-1/15` rules out rank one only. A separate [weighted-phase observer](ErdosProblems/Erdos269/WeightedPhaseCarry.lean#L109) splits a carry into finite residue and uncontrolled integral coboundary; finite realised span needs an explicit finite-dimensional factorisation. This source-only family proves no finite-state quotient or irrationality. Irrationality open.
- [**#1041: short lemniscate connections**](erdos-1041-lemniscate-newton-flow.pdf) — [ray separation/root retention](ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean): finite shifts avoid shared rays; strict margins keep roots in the open disc; decay is a checked hypothesis. Invalid saddle block leaves topology/gluing and operator-owned proof open.
- [**#1049: rational-base Lambert obstructions**](erdos-1049-rational-base-lambert.pdf) — [q-Apéry no-go](ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean): n=0 residual < 0 for p>1; [four-jet/Padé obstruction](ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L129): rank-bounded binary selectors collide and row-content barriers remain; 3/2 corridor; 7/2 height bound; no irrationality, noncollapse, or remainder control.

## What the formal source establishes

**Formalised** means checked Lean, not priority; **proved** is our argument;
**conditional reduction** names an open hypothesis; **verified finite instance** checks inputs. For each
integer `b ≥ 2`, `∑ 1/(bⁿ - 1)` is irrational (a checked rendering of Erdős
(1948)). #257's `1/2` criterion gives an infinite-support consequence; last-skip
rules out its upper branch and `-3`, while `-2`/`-1` remain conditional. #249 has
rank, finite-moment, and denominator interfaces plus an
irrationality/unbounded-certificate equivalence; Martin's theorem and its
independence premise are not formalised.

**Farey/mediant bound** at `K=240` is Farey's bound (delta `0`); no
improvement; next denominator fails this window; fixed cutoffs only. Packages: **fair-coin coprimality**,
**squared-Lambert gcd moments**, **Stern–Brocot law** `(2/3)^d`, **Fibonacci
stability** `F_{r+3}`, **tempered tails**, **Möbius-shadow denominator**, and
**scalar height obstruction**; [gcd](Erdos249257/GcdMomentCalculus.lean),
[run](Erdos249257/SternBrocotRunGeometry.lean). It gives eventual-periodic
nonnegative/signed irrational/base-terminating dichotomies, five binary-carry
criteria, and two scoped #249 no-go models—not orbit avoidance or solution.

## What remains open

- Open: #249's irrationality and unbounded certificate; #257's irrationality for every infinite `A` beyond named formalised families.

“The wall” records failures; [expert handoff questions](docs/RESULTS.md#exact-questions-for-a-human-expert) name input, guess, alternatives, evidence, consumer, and endpoint boundary; or run `python3 scripts/query_expert_handoffs.py`.

<!-- BEGIN generated_corpus_at_a_glance -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Corpus at a glance

The layer a mathematician should judge is small: 103 curated claim records in 21 contribution families, reaching Lean source through 333 principal declaration links. `SCOPE.md` gives its shape and `docs/RESULTS.md` gives the strongest checked result per problem.

The rest is engineering inventory. About 93% of the 153,320 declarations (142,668 across 683 modules) are machine-emitted certificate shards: one integer checked prime, one position excluded. The remainder is not all hand-written either.

| Engineering inventory | Current size |
|---|---:|
| Lean modules (the two library roots) | 1,023 |
| Formal results and supporting lemmas | 151,085 |
| Curated claim records | 103 |
| Contribution families | 21 |

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

## Read or run it

- **No-build:** `python3 scripts/verify_claims.py --verify-all` or
  `--claim <id>` follows claims to source, receipts, and boundary on a
  `git clone --depth 1`; missing history uses `git fetch --unshallow`.
- **Mathematician:** [RESULTS](docs/RESULTS.md) → papers → [SOURCE MAP](docs/SOURCE_MAP.md) → Lean; joint PDF is exposition.
- **Coding agent:** read [`AGENTS.override.md`](AGENTS.override.md), [`AGENTS.md`](AGENTS.md), and [`docs/orientation.json`](docs/orientation.json); choose a problem/claim before the registry.
- **Navigate without Lean:** run
  `python3 scripts/query_corpus.py --tour --format card`; add
  `--route erdos_<n>` for its paper, source, and open handles.
  `--route agent_native_corpus_navigation` exposes scale, map, and reviewed
  #249/#257; [family census](docs/ORIENTATION.md#publication-family-census)
  lists 21 families; [wave routes](docs/WAVE_INDEX.md) expose continuations.
  `query_semantic.py problem-registry` drills down; indexes expose declarations.
  Navigation only, not proof authority.
- **Continue/compare:** [`docs/AGENT_WORKBENCH.md`](docs/AGENT_WORKBENCH.md) defines
  the ladder; `proof_workbench.py show` or `replay --session <slug>`
  rechecks append-only work. `hypOf%` and [residual progress](docs/RESIDUAL_PROGRESS.md)
  separate reductions from renamed targets. [Verification dossier](docs/EXTERNAL_VERIFICATION.md)
  groups selected interfaces and limits; [replay contract](docs/EXTERNAL_VERIFICATION_REPLAY.md)
  pins `source.commit`/`source.tree`. [crosswalk](docs/FORMAL_CONJECTURES_CROSSWALK.md)
  binds eight statements; each is `not_ready_to_submit`.

## Build and verify

Install `elan` from the [Lean setup guide](https://leanprover-community.github.io/get_started.html); [`lean-toolchain`](lean-toolchain) selects `leanprover/lean4:v4.29.1` and [`lake-manifest.json`](lake-manifest.json) pins Mathlib.

```sh
lake exe cache get
lake build
```

Cold clones navigate first. Focus with
`python3 scripts/lean_fast_build.py --jobs 2 [target]`; `--lake-staleness` trusts
traces and `--changed-from <git-ref>` selects modules. It rebuilds only the
selected/stale cone; dependency-index `--check` is constant-time when unchanged.

Release checks: `python3 scripts/check_cold_clone_comprehension.py --quick`
and `python3 scripts/check_release.py`.

Pinned public Lean corpus: no `sorry`, `admit`, project-defined `axiom`, or
`native_decide`; finite computations use kernel-checked `decide`.
`ExternalVerification/Challenge.lean` deliberately carries `sorry` for Comparator.

## Use, contribute, and cite

Use `import Erdos249257` or `import ErdosProblems`. [`examples/Examples.lean`](examples/Examples.lean)
is the minimal consumer: its conditional shell-pressure example
leaves the analytic
hypothesis explicit and does not prove universal #257. Public work
is clone → orient → choose → work/resume → return an attributable result; see
[`CONTRIBUTING.md`](CONTRIBUTING.md) and the [`ExternalVerificationPortfolio`](examples/ExternalVerificationPortfolio).

## Release identity, licence, and privacy

`v0.9.0` is the latest tagged release and citation anchor; [`docs/claims.json`](docs/claims.json) pins the formal-source checkpoint this release ships; [`CITATION.cff`](CITATION.cff) is the citation record. Code, scripts, and documentation use Apache-2.0; manuscripts use CC-BY-4.0; [`REUSE.toml`](REUSE.toml) inventories licences. [`SECURITY.md`](SECURITY.md) and [`PRIVACY.md`](PRIVACY.md) state the public/private boundary.

do not infer results from private or unreleased work. Private `ai_workflow` is not proof authority here. Publication, Palomar submission, and posting remain operator-owned activation; this repository only prepares evidence.
