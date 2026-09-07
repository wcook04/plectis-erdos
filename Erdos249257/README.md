# `Erdos249257/` in the private authoring tree

Copied 2026-09-06 from the release candidate at
`public-source-redacted://release-final-20260905`, branch
`release/final-20260905`, HEAD `8a28b2521e`. Byte-identical copies, made by
the Erdős #249 corrective-integration pass so that private memory is not
behind the candidate.

These three modules exist in the release candidate and had no counterpart
anywhere in this tree:

| file | proves |
|---|---|
| `TotientKernelReduction.lean` | the arithmetic spanning layer for every integer base: `totient_mul_eq_of_primes_dvd`, the zero-residue relation `F_{j,0} = k^(j-1) F_{1,0}`, and the exact composite-base and affine cross corrections |
| `TotientKernelIndex.lean` | the combinatorial index layer: the two zero-residue channels, unique representation `r = k q + (d+1)` at each level, level cardinality `k^(j+1) - k^j`, and total index cardinality `k^e + 1` |
| `TotientKernelConditional.lean` | unconditional canonical spanning, and the exact rank `k^e + 1` conditional on linear independence of the canonical family |

## Why they are inert here

They carry the release tree's namespace `Erdos249257`, which this tree spells
`Erdos257PeriodNoncollapse`, and their imports name that namespace. This
directory is not a `lean_lib` in `lakefile.toml` and no module of a declared
library imports it, so `lake` does not build these files and they cannot break
this tree's build. They are preserved source, not a live target.

## Obligation for the next Lean cycle

`TotientKernelConditional.lean` proves the all-base rank conditionally. This
tree already proves it UNCONDITIONALLY in
`Erdos257PeriodNoncollapse/AllBaseTotientKernel.lean`, with
`finrank_allBaseTotientKernel_eq` at line 1231, an explicit `Basis` at line
1248, and the relation-module dimension at line 1344. So the reconciliation is
one-directional: the release tree should receive `AllBaseTotientKernel.lean`,
after which `TotientKernelConditional.lean` becomes the weaker sibling rather
than the public statement. Do not delete either file before that lands.

## Added by the Erdős #257 corrective-integration pass, same day, same source

Three further modules of the release candidate had no counterpart anywhere in
this tree. Copied byte-identical from the same HEAD `8a28b2521e`.

| file | proves |
|---|---|
| `BouquetReciprocalIrrationality.lean` | `Erdos249257.SupportSunflowerDichotomy.OrthogonalPetalBouquet.summable_reciprocalSupportTerm` at line 19, the summability of the actual support reciprocals of a finite-core orthogonal-petal bouquet, and `irrational_erdosSupportSeries_of_orthogonalPetalBouquet_allBase` at line 85, the all-base corollary. Its own docstring reads "No forced-slot selection is assumed", and its proof is one application of `irrational_erdosSupportSeries_of_summable_reciprocal` to the bouquet reciprocal bound. So it supersedes the selector hypothesis carried by the base-two statement `irrational_erdosSupportSeries_of_orthogonalPetalBouquet` in `SupportSunflowerDichotomy.lean:540` |
| `HalfGreedyUnitPrefix.lean` | the unit-numerator dyadic safety of the half-greedy prefix: `halfGreedy_skip_dyadic_safe_of_unit_numerator` at line 69, the prefix identity `halfGreedyPrefixRat_eq_half_sub_remainder` at line 89, the residual unit-numerator statement through rank 19 at line 97, and the resulting safety at line 107 |
| `SuffixCylinderCarryPivot.lean` | the carry-pivot layer for suffix cylinders: existence of a carry pivot at a suffix-numeral successor at lines 89 and 141, the divisor-count identity across a pivot at line 163, and the profiled-adjacency stage form at line 228 |

`HalfGreedyUnitPrefix.lean` is a partial variant rather than a pure gain:
`halfGreedyPrefixRat_eq_half_sub_remainder` also occurs in this tree, in
`Erdos257PeriodNoncollapse/HalfGreedyDyadicSafe.lean`. The other declarations of
the release module have no counterpart here, so the disposition is union: keep
both files and reconcile in the next Lean cycle rather than choosing one.

The same three reasons hold for these files as for the ones above: they carry
the release tree's `Erdos249257` namespace, this directory is not a `lean_lib`
in `lakefile.toml`, and nothing imports them, so `lake` does not build them.

One further copy from the same pass sits outside this directory. The comparator
package `ExternalVerification257Strong/` exists only in the release candidate
and is copied here at the repository root of this tree, with its own README.
