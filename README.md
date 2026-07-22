<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Tail certificates and achievement-set geometry for Erdős Problems 249 and 257

**New here?** See the [architecture and repository guide](ARCHITECTURE.md), or
the systems paper as a [printable PDF](claim-faithful-publication-systems-paper.pdf).
It assumes no Lean or project history.

Lean 4 formal work on two unsolved irrationality problems.

[**Mathematics paper**](erdos249-257-main-paper.pdf) ·
[**Publication systems paper**](claim-faithful-publication-systems-paper.pdf) ·
[All 3 papers, offline](docs/papers/) ·
[Release v0.6.0](https://github.com/wcook04/plectis-lean-erdos249-257/releases/tag/v0.6.0) ·
[![Lean CI](https://github.com/wcook04/plectis-lean-erdos249-257/actions/workflows/lean.yml/badge.svg)](https://github.com/wcook04/plectis-lean-erdos249-257/actions/workflows/lean.yml) ·
[Plectis](https://wcook04.github.io/plectis/)

This repository and [Plectis](https://github.com/wcook04/plectis)
demonstrate a private system: machinery there, mathematics here.

## The two problems

- **Erdős #249 asks whether** the totient constant
  `S = ∑ φ(n)/2ⁿ` is irrational.
- **Erdős #257 asks whether** `∑_{n∈A} 1/(2ⁿ - 1)` is irrational for every
  infinite `A ⊆ ℕ`.

Both remain open. **This project does not solve Erdős #249 or universal Erdős
#257.** Every table row stays within Lean source.

This self-contained public checkout is not an entrypoint into any private
development system; do not infer results from private or unreleased work.

`v0.6.0` is the latest tagged release and citation anchor.
[`docs/claims.json`](docs/claims.json) pins the post-tag formal-source
checkpoint, not a new tagged release. Lean source checked by the pinned Lean
kernel is proof authority.

## What the formal source establishes

Labels are descriptions, not scores. **Verified finite instance** means
Lean checked only the listed inputs; **conditional reduction** means the
conclusion depends on a named open condition.

| Status | Result |
|---|---|
| **formalised here** | For every integer `b ≥ 2`, the full-support series `∑ 1/(bⁿ - 1)` is irrational. Several named infinite-support families are also formalised; this does not cover every infinite support. |
| **formalised here** | The base-2 Mersenne achievement set is compact, perfect, totally disconnected, nowhere dense, and has Lebesgue measure one. Membership is equivalent to greedy survival at every level. |
| **unconditional progress** | If `S` is rational, its denominator is greater than `79 639 646 646 701 375 323 355 774 875 831 053` (about `7.96 × 10³⁴`). |
| **exact equivalence / open step** | `S` is irrational exactly when every positive binary tail difference is non-integral, equivalently when every fixed pair has a finite certificate. Finishing the argument would require certificates at arbitrarily large stages; that step is not proved. |
| **verified finite instance** | Lean checks 28 explicitly listed cases through `t = 64`. This finite list does not prove successful cases beyond every fixed cutoff. |
| **proved here** | For the #257 test value `1/2`, achievement-set membership is equivalent to infinitely many greedy skips and would produce an infinite support of rational sum, refuting universal #257. Under a last-skip hypothesis, the upper branch and the middle coordinate `-3` are impossible. |
| **conditional reduction** | The two remaining cases, `-2` and `-1`, would also be ruled out if one current contribution were larger than the sum of all later possible contributions. That inequality is not proved. |

### Other exact mathematics in the corpus

| Package | Exact checked content | Boundary |
|---|---|---|
| Fair-coin coprimality | For independent waiting times with `P(X=n)=2⁻ⁿ`, `S = 1/2 + P(gcd(X,Y)=1)`. The probability has no rational representation with denominator at most `39 819 823 323 350 687 661 677 887 437 915 526`. | Irrationality of the probability, and hence of `S`, remains open. |
| Squared-Lambert gcd moments | `∑ 1/(2ᵈ-1)² = ∑ (σ(n)-τ(n))/2ⁿ` and `∑ φ(d)/(2ᵈ-1)² = ∑ (P(n)-n)/2ⁿ`, where `P` is Pillai's gcd-sum function. | These identities do not transfer the cited irrationality of the first series to the open Möbius-weighted row. |
| Stern–Brocot cylinder law | Positive reduced slopes have total Mersenne weight one. Each cylinder splits exactly into a stop mass and two children; the depth-`d` error is at most `(2/3)^d` times the cylinder mass and tends to zero. | This is an exact probability/continued-fraction package, not an irrationality theorem or novelty claim. |
| Fibonacci/continuant run stability | `r` nonempty alternating runs have height at least `F_{r+3}`, with equality on the all-unit spine. Defects `eᵢ` give an exact multiaffine expansion, gain at least `F_{r+1}∑eᵢ`, and have one-site weight `F_{i+2}F_{r-i+1}`. The first induced run layer has mass `1/2`. | The natural denominator exponent is `F_{r+3}-2`; no theorem here says the analytic run tail survives denominator clearing. |
| Tempered binary tail rigidity | For every coefficient sequence with `c(n) ≤ n`, `∑ c(n)/2ⁿ` is rational exactly when there is a tempered integer carry orbit; every such orbit is the scaled tail itself. | This is a general rationality classification. Applying it still requires problem-specific control of the resulting orbit. |
| Exact Möbius-shadow denominator | The reduced denominator of the lcm-height scaled Möbius shadow is computed exactly; an explicit upper-half product of Mersenne factors divides it and gives a quantitative lower bound. | This is denominator survival on the diagonal reduction, not the missing unbounded avoidance supply. |
| Scalar-localisation height obstruction | If `H ∣ x.den` and `(c·x).den ∣ H`, then `x.den/H ∣ |c|`: denominator clearing transfers the complement into the coefficient. | Local height obstruction, not an irrationality criterion. |

Typed routes expose sources: `probabilistic_gcd_geometry` for the first four
rows, `boolean_mobius_constraints` for tail rigidity, and
`arithmetic_obstruction_interfaces` for the last two. Orientation lists
eventually-periodic nonnegative weighted irrationality, a signed
irrational-or-base-terminating dichotomy, five binary-carry
criteria/consequences, and two scoped #249 no-go countermodels.

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

[`SCOPE.md`](SCOPE.md) is the short boundary statement.

<!-- BEGIN generated_corpus_at_a_glance -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Corpus at a glance

| Library | Current size |
|---|---:|
| Lean modules | 635 |
| Formal results and supporting lemmas | 11,539 |
| Curated claim records | 99 |
| Contribution families | 21 |

Claim records span every status, including cited and open, and are partitioned
exactly once. These are navigation counts, not novelty claims.
<!-- END generated_corpus_at_a_glance -->

## Read or run it

- **Mathematician:** start with the
  [Exposition PDF](erdos249-257-main-paper.pdf), then use
  [`docs/SOURCE_MAP.md`](docs/SOURCE_MAP.md) to follow one result into Lean.
- **Coding agent:** read [`AGENTS.md`](AGENTS.md), then the bounded
  [`docs/orientation.json`](docs/orientation.json). Select one mathematical
  programme or claim before expanding the exhaustive registry.
- **Exact boundary or claim status:** read [SCOPE.md](SCOPE.md), the human
  [orientation](docs/ORIENTATION.md), and [methodology](METHODOLOGY.md).
- **Publication topology or contribution family:** run
  `python3 scripts/query_corpus.py --publication-architecture` or
  `python3 scripts/query_corpus.py --publication-family <id>`.
- **Verify:** `python3 scripts/check_cold_clone_comprehension.py --quick`
  checks committed reading surfaces without Mathlib or a Lean build.
  `python3 scripts/check_release.py` runs the full public-surface/query sweep.
  After Lean changes, run `lake build` or
  `python3 scripts/lean_fast_build.py --jobs 2`.

## How the repository fits together

The package has two supported roots. [`Erdos249257.lean`](Erdos249257.lean)
preserves the reviewed #249/#257 corpus. [`ErdosProblems.lean`](ErdosProblems.lean)
is the problem-owned expansion surface: each new line of work lives under its
actual Erdős problem number instead of being folded into the historical
#249/#257 tree. Kernel checking of that second root establishes its exact Lean
propositions; it does not by itself promote them into the reviewed public claim
record or claim that an open problem is solved. The source has five
reader-facing layers:

- **Assembled kernel.** [`CertificateKernel.lean`](Erdos249257/CertificateKernel.lean)
  contains the common series machinery, the full-support Erdős-Borwein theorem,
  named support-family interfaces, and the unconditional #249 denominator
  exclusion.
- **The #249 reduction spine.** The period-killer, lcm-diagonal, cone, diagonal
  pincer, fresh-loss, and transport modules turn the open irrationality problem
  into exact certificate or avoidance obligations. Finite certificate modules
  verify explicit parameters; they do not supply the unbounded family that the
  reduction requires.
- **The #257 carry trunk.** The tail-orbit, achievement-set, Boolean-Möbius
  carry, reciprocal-mass, and divisor-coverage modules describe what a rational
  support value would force. They give exact criteria and necessary conditions,
  not the universal #257 theorem.
- **The reading layer.** The exposition gives the mathematical account; the
  [source map](docs/SOURCE_MAP.md) gives code routes, and the declaration index
  supplies exact Lean names.
- **Problem-owned expansion.** `ErdosProblems/Erdos<N>/` contains bounded
  formal results and explicit open frontiers for one problem at a time. New
  entries stay outside the reviewed claim registry until human mathematical
  review establishes their intended meaning and public framing.

[`docs/SOURCE_MAP.md`](docs/SOURCE_MAP.md) gives the exact module order within
each band. [`docs/WAVE_INDEX.md`](docs/WAVE_INDEX.md) gives the development
chronology; it is not the recommended first reading order.

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

For memory-constrained builds:

```sh
python3 scripts/lean_fast_build.py --jobs 2
```

When `.lake` outputs come from a restored CI or local cache, add
`--lake-staleness` to use Lake's content traces instead of checkout mtimes.
The wrapper keeps at most `--jobs` independent Lake processes active and
serializes final authority checks, so its stated memory bound remains real even
for a wide dependency wave. With no target it checks both supported public
roots; pass a module or `.lean` path to keep an edit/test loop focused.
`--plan` prints compact dependency-wave counts; use `--verbose-plan` only when
you need every planned module name.

Check the public release surfaces separately:

```sh
python3 scripts/check_cold_clone_comprehension.py --quick
python3 scripts/check_release.py
python3 scripts/test_methodology_contract.py
```

The quick check needs no Lean build; `lake exe cache get` only downloads pinned
dependencies.

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
consumer. It proves one base-3 result and exercises the conditional rational shell-pressure
interface, leaving its analytic hypothesis explicit. This does
not prove the still-open universal Erdős #257 statement.

## Citation and licence

Use [`CITATION.cff`](CITATION.cff) for release `v0.6.0`; cite the included
exposition for the mathematics.

Code, scripts, and documentation are Apache-2.0. The manuscript layer, including
the paper source and rendered PDFs, is CC-BY-4.0. The complete licence map is in
[`REUSE.toml`](REUSE.toml).

Use the issue forms for corrections. [`CONTRIBUTING.md`](CONTRIBUTING.md)
explains local checks; [`SECURITY.md`](SECURITY.md) gives the private route.
