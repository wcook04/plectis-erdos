<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Tail certificates and achievement-set geometry for Erdős Problems 249 and 257

Lean 4 work on two open irrationality problems. Start with:
[RESULTS](docs/RESULTS.md) → [SCOPE](SCOPE.md) →
[PRIOR ART](docs/PRIOR_ART.md) → [SOURCE MAP](docs/SOURCE_MAP.md).
[architecture and repository guide](ARCHITECTURE.md).
It assumes no Lean or project history.
[agent-navigation paper](cold-clone-to-proof-receipt.pdf): navigation,
receipts, incremental builds.

[**#249 — exact ranks for the dyadic sections of Euler's totient**](erdos-249-binary-totient-series.pdf) ·
[**#257 — settled supports and exact finite periods**](erdos-257-mersenne-support-subseries.pdf)

[Joint technical exposition](erdos249-257-main-paper.pdf) ·
[printable PDF](claim-faithful-publication-systems-paper.pdf) ·
[![Lean CI](https://github.com/wcook04/plectis-lean-erdos249-257/actions/workflows/lean.yml/badge.svg)](https://github.com/wcook04/plectis-lean-erdos249-257/actions/workflows/lean.yml)

## The two problems

- **Erdős #249 asks whether** the totient constant
  `S = ∑ φ(n)/2ⁿ` is irrational.
- **Erdős #257 asks whether** `∑_{n∈A} 1/(2ⁿ - 1)` is irrational for every
  infinite `A ⊆ ℕ`.

Both remain open. **This project does not solve Erdős #249 or universal Erdős
#257.** Results stay within Lean source.

**Ten-minute verdict.** Checked non-restatement centre:

- #257 has exact finite-period noncollapse, irrationality for eventually
  periodic supports, a signed periodic-weight dichotomy, achievement-set
  geometry, and scoped method barriers.
- #249 has exact dyadic-section ranks and infinite-dimensionality,
  denominator-shadow growth, and scoped barriers and case trichotomies.
- The project also diagnoses its own failed reformulation routes: 17 of 23
  substantial hypotheses extracted from conditional theorems are proved
  endpoint-equivalent. Those equivalences are evidence about the methods, not
  progress on either open problem.

Audit: 196 mechanically nonrecurring candidates (121 #257, 59 #249, 16
shared), 25 bare equivalences, and 70 classical/prior-art formalisations.
184 candidates lack prior-art assessment; 17 of 23 substantial hypotheses
extracted from conditional theorems are proved endpoint-equivalent.

The finite #249 result is the classical Farey/mediant bound at `K=240`
(numerical delta `0`); Farey's method supplies the number directly. The local
contribution is checked arithmetic, transfers,
and the sharp first failure.
[RESULTS](docs/RESULTS.md) gives the typed census and limits.

This self-contained public Plectis checkout is not an entrypoint into any private
development system. `v0.6.0` is the latest tagged release and citation anchor;
[`docs/claims.json`](docs/claims.json) pins a post-tag formal-source checkpoint,
not a new tagged release. Lean source checked by the pinned Lean kernel is
proof authority; do not infer results from private or unreleased work.

## What the formal source establishes

Labels are descriptions, not scores. **Verified finite instance** means
Lean checked only the listed inputs; **conditional reduction** means the
conclusion depends on a named open condition.

| Status | Result |
|---|---|
| **formalised here** | For every integer `b ≥ 2`, the full-support series `∑ 1/(bⁿ - 1)` is irrational. Several named infinite-support families are also formalised; this does not cover every infinite support. |
| **formalised here** | The base-2 Mersenne achievement set is compact, perfect, totally disconnected, nowhere dense, and has Lebesgue measure one. Membership is equivalent to greedy survival at every level. |
| **proved here** | For the #257 test value `1/2`, achievement-set membership is equivalent to infinitely many greedy skips and would produce an infinite support of rational sum, refuting universal #257. Under a last-skip hypothesis, the upper branch and the middle coordinate `-3` are impossible. |
| **conditional reduction** | Within that same last-skip contradiction schema, the two still-unexcluded middle coordinates, `-2` and `-1`, would also be ruled out if one current contribution were larger than the sum of all later possible contributions. That inequality is not proved. |
| **proved here** | The dyadic sections of Euler's totient have an explicit rational basis; the level-`e` span has dimension exactly `2ᵉ + 1`. This is a theorem about the coefficient sequence, not the irrationality of `S`. |
| **formalised here** | Applying the classical Farey/mediant bound directly to the committed `K=240` interval excludes rational denominators through `79 639 646 646 701 375 323 355 774 875 831 053` (about `7.96 × 10³⁴`). This is exactly the Farey bound, not an improvement on it; Lean also checks that the next denominator fails this finite window. |
| **proved here** | `S` is irrational exactly when every positive binary tail difference is non-integral, equivalently when every fixed pair has a finite certificate. Finishing the argument would require certificates at arbitrarily large stages; that step is not proved. |
| **verified finite instance** | Lean proves a diagonal certificate at every `t ≤ 82`. Historical free-position audit: 125 verified log rows represent 123 distinct off-diagonal `(h,N,L)` certificates in 122 Lean files. This finite evidence does not prove successful cases beyond every fixed cutoff. |

### Other exact mathematics in the corpus

| Package | Exact checked content | Boundary |
|---|---|---|
| Fair-coin coprimality | `S = 1/2 + P(gcd(X,Y)=1)` for independent `P(X=n)=2⁻ⁿ`. | Irrationality remains open. |
| Squared-Lambert gcd moments | Two exact divisor-sum identities for squared Lambert denominators. | No transfer to the open Möbius row. |
| Stern–Brocot cylinder law | Exact stop/child splitting; depth error at most `(2/3)^d`. | Probability law, not irrationality. |
| Fibonacci/continuant run stability | Height at least `F_{r+3}` with exact defect expansion. | No analytic denominator-clearing theorem. |
| Tempered binary tail rigidity | Exact rationality/carry-orbit classification for `c(n) ≤ n`. | Needs problem-specific orbit control. |
| Exact Möbius-shadow denominator | Exact reduced denominator and an explicit divisor lower bound. | No unbounded avoidance supply. |
| Scalar-localisation height obstruction | If `H ∣ x.den` and `(c·x).den ∣ H`, then `x.den/H ∣ |c|`. | Local obstruction only. |

Typed routes expose sources: `probabilistic_gcd_geometry` for the first four
rows, `boolean_mobius_constraints` for tail rigidity, and
`arithmetic_obstruction_interfaces` for the last two. Orientation also lists
eventually-periodic nonnegative weighted irrationality, a signed
irrational-or-base-terminating dichotomy, five binary-carry
criteria/consequences, and two scoped #249 no-go countermodels.
Five further obstructions are stated with their limits in
[RESULTS](docs/RESULTS.md#other-standalone-exact-obstructions).

An exact final-skip band formula does not show that the actual orbit avoids
an unsafe band.

[Orientation](docs/ORIENTATION.md) routes claims; the
[mathematics paper](erdos249-257-main-paper.pdf) owns the exposition.

## What remains open

- Prove that `S = ∑ φ(n)/2ⁿ` is irrational without placing a bound on a possible
  rational denominator.
- Produce the unbounded certificate supply required by the exact #249
  reduction.
- Prove irrationality of `∑_{n∈A} 1/(2ⁿ - 1)` for every infinite
  `A ⊆ ℕ`, rather than only the named support families formalised here.

[`SCOPE.md`](SCOPE.md) is the short boundary statement. The exact expert
handoffs—what input is requested, current guess, alternatives, discriminating
evidence, checked consumer, and endpoint-or-counterexample boundary—are in
[RESULTS](docs/RESULTS.md#exact-questions-for-a-human-expert) and
`python3 scripts/query_expert_handoffs.py`.

<!-- BEGIN generated_corpus_at_a_glance -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Corpus at a glance

| Library | Current size |
|---|---:|
| Lean modules | 991 |
| Formal results and supporting lemmas | 149,807 |
| Curated claim records | 100 |
| Contribution families | 21 |

Claim records span every status, including cited and open, and are partitioned
exactly once. These are navigation counts, not novelty claims.
<!-- END generated_corpus_at_a_glance -->

## Read or run it

- **Mathematician:** use the top reading route, then follow one result from
  [SOURCE MAP](docs/SOURCE_MAP.md) into Lean. The [Exposition PDF](erdos249-257-main-paper.pdf)
  is the longer route, not the truth-status entrypoint.
- **Coding agent:** read [`AGENTS.md`](AGENTS.md), then the bounded
  [`docs/orientation.json`](docs/orientation.json); select one programme or
  claim before expanding the registry.
- **Whole-corpus agent navigation, without a Lean build:** run
  `python3 scripts/query_corpus.py --tour --format card`, then follow
  `python3 scripts/query_corpus.py --route agent_native_corpus_navigation`.
  The no-build tour exposes corpus scale, a mathematical map, the exact open
  frontier, and an authority boundary. Committed indexes expose every indexed
  declaration and exact dependencies for both loaded roots after cloning.
  Use `python3 scripts/query_semantic.py mechanisms --problem 249`,
  `receipts`, and `population-backlog` for mechanisms, failed routes, and
  paper-seeded semantic gaps. These are navigation projections, not proof
  authority.
- **Publication topology:** run
  `python3 scripts/query_corpus.py --publication-architecture` or
  `python3 scripts/query_corpus.py --publication-family <id>`.
- **Verify:** `python3 scripts/check_cold_clone_comprehension.py --quick`
  checks reading surfaces without Lean; `python3 scripts/check_release.py`
  runs the full public-surface/query sweep.

## How the repository fits together

The package has two compact supported roots. [`Erdos249257.lean`](Erdos249257.lean)
preserves the reviewed #249/#257 corpus. [`ErdosProblems.lean`](ErdosProblems.lean)
is the problem-owned expansion surface: work lives under its actual Erdős
problem number instead of being forced into the historical #249/#257 tree.
Kernel checking of that second root establishes its exact Lean propositions;
it does not by itself promote them into the reviewed claim registry or claim
that an open problem is solved.

The source has five reader-facing layers:

- **Assembled kernel.** [`CertificateKernel.lean`](Erdos249257/CertificateKernel.lean)
  contains the common series machinery, the full-support Erdős-Borwein theorem,
  named support-family interfaces, and the unconditional #249 denominator
  exclusion.
- **The #249 reduction spine.** The period-killer, lcm-diagonal, cone, diagonal
  pincer, fresh-loss, and transport modules turn the open irrationality problem
  into exact certificate or avoidance obligations. Finite certificate modules
  verify explicit parameters; they do not supply the unbounded family required
  by the reduction.
- **The #257 carry trunk.** The tail-orbit, achievement-set, Boolean-Möbius
  carry, reciprocal-mass, and divisor-coverage modules give exact criteria and
  necessary conditions, not the universal #257 theorem.
- **Navigation.** The atlas finds every declaration and import. Selected
  semantic meanings carry scoped reviews (`python3 scripts/query_semantic.py
  semantic-reviews`)—not human, novelty, or proof authority. The theory lab
  adds nine mechanisms, nine transfer capsules, and three failure receipts;
  four holdouts have no results, so no measured transfer is claimed.
- **Problem-owned expansion.** `ErdosProblems/Erdos<N>/` contains bounded
  results and explicit open frontiers for one problem at a time. New entries
  remain outside the reviewed claim registry until mathematical review
  establishes their intended meaning and public framing.

[SOURCE MAP](docs/SOURCE_MAP.md) gives module order; [METHODOLOGY](METHODOLOGY.md)
governs claim changes; [WAVE INDEX](docs/WAVE_INDEX.md) gives chronology, not
reading order.

<!-- BEGIN generated_principal_declaration_anchors -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Following a result into Lean

The paper links each headline result to the relevant source. For a particular
topic, start with the [source map](docs/SOURCE_MAP.md); it gives the module
order without asking you to decode Lean declaration names first.
<!-- END generated_principal_declaration_anchors -->

## Build and verify

[`lake-manifest.json`](lake-manifest.json) pins Mathlib for
`leanprover/lean4:v4.29.1`.

```sh
lake exe cache get
lake build
```

For a focused build, run
`python3 scripts/lean_fast_build.py --jobs 2 [target]`. Add `--lake-staleness`
with restored `.lake` outputs so it trusts Lake content traces, not checkout
times. Without a target it checks both roots; `--plan` reports waves without
building. A cold clone can navigate before this step; formal editing needs the
pinned toolchain. Later builds reuse outputs and rebuild only the selected or
stale dependency cone; `--changed-from <git-ref>` selects changed modules.
The dependency-index validator stores an exact `.lake` receipt: unchanged
inputs make `--check` constant-time; `--check --full-check` forces an audit.

Check the public release surfaces separately:

```sh
python3 scripts/check_cold_clone_comprehension.py --quick
python3 scripts/check_release.py
python3 scripts/test_methodology_contract.py
```

The pinned public Lean source contains no `sorry`, `admit`, project-defined
`axiom`, or `native_decide`; finite computations use kernel-checked `decide`.

## Use as a Lean package

Import the reviewed #249/#257 root:

```lean
import Erdos249257
```

For the problem-owned expansion surface, import:

```lean
import ErdosProblems
```

[`examples/Examples.lean`](examples/Examples.lean) is the minimal downstream
consumer; its conditional shell-pressure example leaves the analytic
hypothesis explicit and does not prove universal #257.

## Citation and licence

Use [`CITATION.cff`](CITATION.cff) for `v0.6.0`.
Code, scripts, and documentation are Apache-2.0. The manuscript layer, including
the paper source and rendered PDFs, is CC-BY-4.0.
[`REUSE.toml`](REUSE.toml) is complete.

Use the issue forms for corrections. [`CONTRIBUTING.md`](CONTRIBUTING.md)
explains local checks; [`SECURITY.md`](SECURITY.md) gives the private route.
