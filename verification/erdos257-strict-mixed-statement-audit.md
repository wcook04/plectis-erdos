<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Erdős #257 Corollary 5.2: statement correspondence audit

This audit concerns the complete existential corollary, including the support
outside both individual sufficient classes. The ordinary argument and the
separately written formal interface were reviewed against the public source on
18 October 2026. This is an AI-assisted mathematical and source review, not
independent human review, peer review, or an assessment of historical priority.

## Source identity

The starting public revision is
`654ebe81d8b856e953cf60f83d88d5c18d30e687` of `wcook04/plectis-erdos`.
These SHA256 digests identify the papers as read at that revision, before
subsequent evidence-status edits:

| Paper | Source SHA256 |
|---|---|
| [Short paper](../paper/257/erdos-257-mersenne-support-subseries.tex) | `2676b3e9f6a5ba6f3ea8fceeed9684ff6ced0fa3bef9c3c0b6a3a878288af5d3` |
| [Long companion](../paper/257/erdos257-mersenne-reasoning-surface.tex) | `47cf6a152738f17c6879bd5070adb73c34a1254775afd44dbf7b6ccd346aa100` |
| [Reciprocal-summable exposition](../paper/257/erdos257-expository-sums-never-fractions.tex) | `5efdc16fe9917b634a2af0068bab9ce0e17127b58d5e82e6ab3e412c1e791352` |

The short paper's stable label is `res:strict-mixed-supports`, numbered
Corollary 5.2 at the starting revision, lines 763–779. The class definitions
are at lines 606–611, Proposition 5.1 at 613–621, and the two constructions
at 677–756. The long companion's label `record257:strict-mixed-proof`,
lines 1067–1080, gives the same union argument.

The exact UTF-8 block from `\begin{corollary}[a support requiring the mixed criterion]`
through its `\end{corollary}`, excluding any following newline, has SHA256
`48f9e1066369ee24adb2d23b6a010345a1aee25182af8bea57d8b9e37ff1de12`.
The coverage ledger's existing `statement_sha256` for the same corollary is
`sha256:ec8cba3f6409742197fa4fa63d81b4e71f2aba928597821a4600ea8cfa8c3f4a`;
that owner-normalized statement identity is preserved as well.

## Exact formal target

The proof endpoint is
[`exists_strict_mixed_support_host`](../lean/ErdosProblems/Erdos257/PaperCompleteR8/AnalyticIncomparability.lean),
in namespace `ErdosProblems.Erdos257.PaperCompleteR8`:

```lean
∃ U : Set ℕ, U.Infinite ∧ 0 ∉ U ∧ ¬ HasStrengthenedPositiveCover U ∧
  (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b U) ∧
  (∀ A : Set ℕ, A ⊆ U → A.Infinite → ∀ b : ℕ, 2 ≤ b →
    Irrational (erdosSupportSeries b A))
```

Normalize the text of the type between the theorem's colon and `:= by` by
replacing each whitespace run with one ASCII space and stripping outer
whitespace. Its UTF-8 SHA256 is
`dec1b97ecbbedc3f5651f91735821b70076c56cea12c123d57871efa9699afea`.
The [separate challenge](ExternalVerification/StrictMixed/Challenge.lean)
has the identical normalized type.
Its complete source-file SHA256 is
`32d10dc2ebb5e3840667f6faf0a49dafd036493e0818ce4523402d54d95d4c9c`.

| Paper requirement | Formal correspondence |
|---|---|
| There exists one infinite positive support | `∃ U : Set ℕ, U.Infinite ∧ 0 ∉ U`; positivity means all elements are at least one. |
| This same support has no strengthened positive cover | `¬ HasStrengthenedPositiveCover U`, with the literal dyadic cost (V). |
| It satisfies no weighted condition at any integer base at least two | `∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b U`. Every integer at least two is represented by exactly one such natural number. |
| Every infinite subset has an irrational sum at every such base | The final `∀ A`, subset and infinitude premises, and `∀ b` occur inside the same existential witness. |

There is no base-dependent replacement for `U`, no reciprocal-summability
premise on its subsets, and no assumption that those subsets individually
satisfy either sufficient criterion.

## Definition and indexing audit

The [Mathlib-only challenge](ExternalVerification/StrictMixed/Challenge.lean)
imports `Mathlib` directly and defines its statement vocabulary inline, with
no submitted helper or proof-bearing corpus import. The following nine
declarations were compared with their public owners after whitespace
normalization; their bodies match. For `erdosSupportSeries`, the source's
`noncomputable` declaration modifier was omitted from the textual comparison.

- `erdosSupportSeries`: [CertificateKernel](../lean/Erdos249257/CertificateKernel.lean), line 8897.
- `primeSetPart`, `primeWeightedTerm`, and `FinitePrimeWeighted`:
  [PrimeWeightedDefinitions](../lean/ErdosProblems/Erdos257/PaperCompleteR7/PrimeWeightedDefinitions.lean), lines 16–27.
- `PositiveCoverData`, its `cost`, `host`, `StrengthenedCostSummable`, and
  `HasStrengthenedPositiveCover`:
  [AnalyticTargets](../lean/ErdosProblems/Erdos257/PaperCompleteR7/AnalyticTargets.lean), lines 23–48.

In particular, a weighted witness uses one finite **nonempty** set of primes
for the whole support and the full prime-power part of each exponent. The
cover frames contain positive integers; exponents satisfy `0 < α ≤ 1`;
positive-divisor coefficients are nonnegative; each column is summable; and
the divisor sum majorises the frame's divisor count raised to `α`.

The paper indexes cover frames from one. Lean's frame `j : ℕ` represents
paper frame `j + 1`, so the copied cost is exactly
`C.cost j * 2 ^ ((j + 1) * C.exponent j) / (2 ^ C.exponent j - 1)`.
It has one inverse power of the denominator, as in (V). It is not the older
stronger cost with a squared denominator, and it does not replace the fixed
dyadic weights by arbitrary positive weights. Division at zero is immaterial:
the asserted host and all its subsets exclude zero.

## Ordinary mathematical proof

Proposition 5.1 supplies positive infinite supports `E` and `V`, with
`E` weighted at base two but outside the cover class, and `V` in the cover
class but outside every weighted class `W_b`, for every integer `b ≥ 2`.
Take `U = E ∪ V`. It is positive and infinite. Any cover of `U` also covers
`E`, contradicting the first separation. Any weighted summability witness
for `U` at a fixed base restricts to `V`, using the same finite prime set,
because the summands are nonnegative. This contradicts the second separation
at that base. Finally, the mixed theorem applies to these actual `E,V` and
gives irrationality for every infinite subset of their union at every base.
Separate irrationality of two summands is not used.

The formal composition extracts the already constructed witnesses from
`exists_incomparable_hosts_with_mixed_heredity`, takes their union, restricts
an alleged cover to the first witness, and applies
`finitePrimeWeighted_subset` to restrict an alleged weighted witness to the
second. Its final hereditary conclusion is the mixed conclusion on that
same union. Thus it closes the existential corollary rather than restating
the conditional mixed implication.

The printed constructions were also checked as ordinary mathematics. For
`E`, the finite-prime weighted sum decays exponentially while finite-period
means of the logarithmic divisor count grow without bound, excluding every
cover. For `V`, disjoint prime alphabets make any finite-prime weighted sum
receive a fixed positive contribution from infinitely many frames; the
chosen fractional exponents make the full index-weighted cover cost bounded
by a summable multiple of `j 4⁻ʲ`. No obstruction was found in those arguments.
The formal existential witness may use the already checked squarefree
divisor-cube construction with different parameters; the corollary does not
specify which witness must be chosen.

The formal witnesses were also inspected beyond their endpoint types. In
[`ReverseStrengthenedHost`](../lean/ErdosProblems/Erdos257/PaperCompleteR8/ReverseStrengthenedHost.lean),
`reverseHost_no_weighted_sum` chooses a sufficiently late row for an arbitrary
finite prime set, makes its prime part equal to one throughout that row, and
contradicts the supposed finite total using an unbounded row reciprocal mass
divided by `b - 1`. Its cover proof bounds the full `j + 1` cost term by
`exp(1)^2 / 2^(j + 2)`. The weighted witness in
[`DyadicHostSeparation`](../lean/ErdosProblems/Erdos257/PaperCompleteR8/DyadicHostSeparation.lean)
constructs the prime sets and proves their unbounded logarithmic means;
its existence theorem assumes neither those means nor absence of a cover.

## Verification boundary

The exact source type and independent challenge were checked for the
correspondence described above. Lean build, recursive-axiom inspection and
Comparator replay outcomes are recorded by their own generated output and
receipts; this prose does not substitute for those checks. The configured
axiom budget is `propext`, `Quot.sound`, and `Classical.choice`.

The challenge's single statement hole is an input to Comparator, not a proof.
The selected solution imports the actual source proof and does not import
the trusted challenge. The printed fresh-prime construction itself is not
being claimed as formalised by this existential theorem.

The exposition treats the reciprocal-summable theorem, Theorem A.1 of the
short paper: see its lines 930–965 and receipt `E257_47`. That receipt remains
attached to A.1. It does not certify Corollary 5.2. Universal Erdős #257 and
the membership questions for `1/2` and `1/21` remain open. This audit claims
neither novelty nor human or community acceptance.
