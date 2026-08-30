<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Plectis: a public frontier across eight open Erdős problems

Plectis is an AI-assisted mathematical research system with a self-contained
public proof corpus for Erdős Problems 68, 243, 249, 251, 257, 269, 1041, and
1049: exact reductions, theorems, countermodels, boundaries, and certificates.
**All eight problems remain open; this repository does not solve them.**

**Start with one checked claim.** No Lean build is needed:

```bash
python3 scripts/verify_claims.py --claim eb_full_support
```

This prints the statement, re-resolves its declaration, shows the Comparator
interface, paper, release receipts, and claim boundary. `--verify-all` checks the
complete set. [Read or run it](#read-or-run-it) gives routes that need Lean.

[RESULTS](docs/RESULTS.md) → [SCOPE](SCOPE.md) → [SOURCE MAP](docs/SOURCE_MAP.md)
→ [verification](docs/EXTERNAL_VERIFICATION.md) → [prior art](docs/PRIOR_ART.md)
→ [architecture and repository guide](ARCHITECTURE.md) · [printable PDF](claim-faithful-publication-systems-paper.pdf)

The [agent-navigation paper](cold-clone-to-proof-receipt.pdf) explains the
cold-clone route. It assumes no Lean or project history. This checkout is
not an entrypoint into any private development system.
Will Cook reviewed claims. **Lean source checked by the pinned Lean kernel**
is formal proof authority, not for meaning or novelty.

## Problem papers

[`docs/papers/corpus.json`](docs/papers/corpus.json) indexes the papers. This
blank-slate map is readable without a query and does not require `ai_workflow`,
private cache, or network access.

| Problem | Question |
|---|---|
| **#68** | Is `∑_{n≥2} 1/(n!−1)` irrational? |
| **#243** | Does rationality of a rapidly growing sequence's reciprocal sum force Sylvester recurrence? |
| **#249** | Is `∑ φ(n)/2ⁿ` irrational? |
| **#251** | Is `∑ p_n/2ⁿ` irrational (the consecutive-prime-gap dyadic series)? |
| **#257** | Is `∑_{n∈A} 1/(2ⁿ-1)` irrational for every infinite `A ⊆ ℕ_{>0}`? |
| **#269** | Is the reciprocal sum of running lcms of smooth numbers irrational for at least two primes? |
| **#1041** | Must two unit-disc roots admit a curve `<2` in its open lemniscate? |
| **#1049** | Which rational bases yield an irrational Lambert-type series, starting with `3/2`? |

### Public checked frontier; what remains

Links name a strongest checked route and its limit; reductions are not solutions.

- [**#68: factorial denominators**](erdos-68-factorial-denominator-irrationality.pdf) — divisibility-failure equivalence; `67` checked, `300000` external, cofinal source open.
- [**#243: reciprocal-tail rigidity**](erdos-243-reciprocal-tail-rigidity.pdf) — normalised vanishing and Lean no-go results exclude bounded/finite negative mass; unbounded mixed signs open.
- [**#249: dyadic Euler totients**](erdos-249-binary-totient-series.pdf) · [reasoning surface](erdos249-totient-reasoning-surface.pdf) — ranks, moments, completeness, anti-compression, [visible mass](Erdos249257/GcdMomentCalculus.lean); Farey `K=240`; diagonal certificates through `t=82`; unbounded supply open.
- [**#251: prime-gap dyadic tails**](erdos-251-prime-gap-dyadic-series.pdf) — summation by parts, tail recurrence, rational shifts, cofinal non-integral-shift equivalences; prime-tail bridge open.
- [**#257: reciprocal Mersenne subseries**](erdos-257-mersenne-support-subseries.pdf) · [reasoning surface](erdos257-mersenne-reasoning-surface.pdf) — full support, finite-period noncollapse, topology, carry criteria; universal #257 and `1/2`/`1/21` open.
- [**#269: three-prime running lcms**](erdos-269-three-prime-running-lcm.pdf) — maximal powers, logarithmic cells, grouped sums, shell bounds, rank-two obstruction; three-prime problem open.
- [**#1041: short lemniscate connections**](erdos-1041-lemniscate-newton-flow.pdf) — Newton-flow decay, ray separation, collisions, root retention; an invalid saddle block leaves topology, gluing, and operator-owned proof open.
- [**#1049: rational-base Lambert obstructions**](erdos-1049-rational-base-lambert.pdf) — corridor, height, Hermite–Padé, determinant, prime-support no-go mechanisms at `3/2` and `7/2`; no irrationality, noncollapse, or remainder control is proved.

## What the formal source establishes

**Formalised here** means rendered and kernel-checked in Lean, not a priority
claim; **proved here** is this project's argument; **conditional reduction** names
an open hypothesis; **verified finite instance** checks listed inputs. For every
integer `b ≥ 2`, `∑ 1/(bⁿ - 1)` is irrational (a checked rendering of Erdős
(1948)). #257's `1/2` criterion gives an infinite-support consequence; last-skip
rules out its upper branch and `-3`, while `-2`/`-1` remain conditional. #249 has
rank interfaces, finite moments, denominator exclusions, and an
irrationality/unbounded-certificate equivalence; Martin's theorem and its
independence premise are not formalised.

The classical **Farey/mediant bound** at `K=240`: Farey's method supplies the
number directly, with delta `0`—exactly the Farey bound, not an improvement. The
next denominator fails this window; that does not prove success past every fixed
cutoff. Packages: **fair-coin coprimality**, **squared-Lambert gcd moments**,
**Stern–Brocot law** `(2/3)^d`, **Fibonacci run stability** `F_{r+3}`,
**tempered tail rigidity**, **Möbius-shadow denominator**, and **scalar
height obstruction**; [gcd](Erdos249257/GcdMomentCalculus.lean),
[run](Erdos249257/SternBrocotRunGeometry.lean). The map exposes eventually-periodic
nonnegative weighted irrationality, a
signed irrational-or-base-terminating dichotomy, five binary-carry criteria,
and two scoped #249 no-go countermodels. These routes do not show the orbit
avoids an unsafe band or settle its open problem.

## What remains open

- Prove that `S = ∑ φ(n)/2ⁿ` is irrational; produce the unbounded certificate supply required by #249.
- Prove irrationality of `∑_{n∈A} 1/(2ⁿ - 1)` for every infinite `A ⊆ ℕ`, beyond named formalised families.

Working records state failed routes in “The wall”. Exact expert handoffs name
what input is requested, current guess, alternatives, discriminating evidence,
checked consumer, and endpoint-or-counterexample boundary: [handoff questions](docs/RESULTS.md#exact-questions-for-a-human-expert)
or `python3 scripts/query_expert_handoffs.py`.

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
  `--claim <id>` follows a claim to source, receipts, and stopping point on a
  `git clone --depth 1`; missing history is reported with `git fetch --unshallow`.
- **Mathematician:** [RESULTS](docs/RESULTS.md) → papers → [SOURCE MAP](docs/SOURCE_MAP.md) → Lean; joint PDF is exposition.
- **Coding agent:** read [`AGENTS.override.md`](AGENTS.override.md), [`AGENTS.md`](AGENTS.md), and [`docs/orientation.json`](docs/orientation.json); choose one problem or claim before the registry.
- **Whole-corpus agent navigation without a Lean build:** run
  `python3 scripts/query_corpus.py --tour --format card`; add
  `--route erdos_<n>` for a problem's paper, source, and open handles.
  `--route agent_native_corpus_navigation` exposes corpus scale, the canonical
  eight-problem map, and the reviewed #249/#257 frontier. `query_semantic.py
  problem-registry` drills down; indexes expose declarations and dependencies for
  both roots. These are navigation projections, not proof authority.
- **Continue/compare:** [`docs/AGENT_WORKBENCH.md`](docs/AGENT_WORKBENCH.md) defines
  the ladder; `proof_workbench.py show --session <slug>` or `replay --session <slug>`
  rechecks append-only work. `hypOf%` and [residual progress](docs/RESIDUAL_PROGRESS.md)
  separate reductions from renamed targets. [Verification dossier](docs/EXTERNAL_VERIFICATION.md)
  groups selected interfaces and limits; [replay contract](docs/EXTERNAL_VERIFICATION_REPLAY.md)
  pins `source.commit`/`source.tree`. [crosswalk](docs/FORMAL_CONJECTURES_CROSSWALK.md)
  binds eight statements; each is `not_ready_to_submit`.

## Build and verify

Install Lean's toolchain manager, `elan`, from the [Lean setup guide](https://leanprover-community.github.io/get_started.html); [`lean-toolchain`](lean-toolchain) selects `leanprover/lean4:v4.29.1` and [`lake-manifest.json`](lake-manifest.json) pins Mathlib.

```sh
lake exe cache get
lake build
```

A cold clone can navigate before this step. A focused build is
`python3 scripts/lean_fast_build.py --jobs 2 [target]`; `--lake-staleness` trusts
traces and `--changed-from <git-ref>` selects modules. It rebuilds only the
selected or stale dependency cone; dependency-index `--check` is constant-time
when inputs are unchanged.

The compact release checks are `python3 scripts/check_cold_clone_comprehension.py
--quick` and `python3 scripts/check_release.py`.

Pinned public Lean corpus: no `sorry`, `admit`, project-defined `axiom`, or
`native_decide`; finite computations use kernel-checked `decide`.
`ExternalVerification/Challenge.lean` deliberately carries `sorry` for Comparator.

## Use, contribute, and cite

Use `import Erdos249257` or `import ErdosProblems`. [`examples/Examples.lean`](examples/Examples.lean)
is the minimal downstream consumer: its conditional shell-pressure example
leaves the analytic
hypothesis explicit and does not prove universal #257. Public work
is clone → orient → choose → work or resume → return an attributable result; see
[`CONTRIBUTING.md`](CONTRIBUTING.md) and the [`ExternalVerificationPortfolio`](examples/ExternalVerificationPortfolio).

## Release identity, licence, and privacy

`v0.9.0` is the latest tagged release and citation anchor; [`docs/claims.json`](docs/claims.json) pins the formal-source checkpoint this release ships; [`CITATION.cff`](CITATION.cff) is the citation record. Code, scripts, and documentation use Apache-2.0; manuscripts use CC-BY-4.0; [`REUSE.toml`](REUSE.toml) inventories licences. [`SECURITY.md`](SECURITY.md) and [`PRIVACY.md`](PRIVACY.md) state the public/private boundary.

do not infer results from private or unreleased work. The private `ai_workflow` factory is not proof authority for this checkout. Publication, Palomar submission, and public posting remain operator-owned activation; this repository prepares evidence only.
