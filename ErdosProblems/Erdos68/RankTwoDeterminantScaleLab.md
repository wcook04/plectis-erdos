# Erdős 68: what the rank-two producer would actually give you

## Claim boundary

Finite computation plus elementary reasoning about identities already landed in
this packet. It reclassifies a priority-1 producer's output; it does not prove
the producer, and Erdős 68 remains open.

## The producer

`erdos68_rank_two_strict_nonvanishing`:

> Using the Lean-checked uniform factorial-grid Cramer kernel and prime unit
> translator, prove that the nearest-integer-rounded residual is strictly
> nonzero. […] strict nonvanishing is now explicitly equivalent to proving
> `det(A)·S` is nonintegral.

The supporting identities are landed. `full_residual_mod_integers_classification`
gives `R_D(c) = det(A)·S + K` with `K` integral and `det(A)` the nonzero
augmented determinant. `conditional_rank_two_nearest_integer_rounding` gives
`|R| ≤ 1/2` after rounding. `PrimeUnitTranslator.lean`, which carries the whole
construction, contains no occurrence of `Irrational` — nothing downstream
consumes the nonvanishing.

Three things the packet does not say about it.

## 1. Its output is a divisibility exclusion, not a size bound

Suppose `S = a/q` in lowest terms. Then `det(A)·S = det(A)·a/q` is an integer
exactly when `q ∣ det(A)`, because `gcd(a,q) = 1`. So

> **`det(A)·S` nonintegral *is* `q ∤ det(A)`.**

That is the same species of statement as the Kempner-index exclusion
`q ∤ 299999!` landed alongside it — a smoothness constraint on the denominator —
and not a lower bound on its size. The producer has been sitting in the packet
next to size-bound producers without that being written down.

## 2. Nonvanishing alone cannot give irrationality

Under `S = a/q`, a nonzero `R` is a nonzero multiple of `1/q`, so `|R| ≥ 1/q`.
The only smallness on record is `|R| ≤ 1/2`. Those are compatible for every
`q ≥ 2`, so the pair can never contradict rationality.

A linear-form argument needs `0 < |R| < 1/q`; the nearest-integer rounding step
is precisely what destroys that, since it replaces whatever the construction's
own `K` was by the one minimising `|R|` — which under rationality is bounded
below by `1/q`. This is consistent with what the packet already records:
`scalar_canonical_product_height_no_go` says the natural scalar linear form's
smallness diverges. **Smallness is the missing half, and nonvanishing is not a
step toward it.**

## 3. The continued-fraction bound discharges it for free, but only twice

`certified_continued_fraction_denominator_exclusion` gives `q > 10^12038`.
Combined with the observation above, that yields unconditionally

> `N·S ∉ ℤ` for every nonzero integer `|N| ≤ 10^12038`

— if `S` is irrational this is trivial, and if `S = a/q` then `q` cannot divide
such an `N`. So every grid instance with a determinant that small has the
producer's hypothesis already proved.

Computing the determinants literally from `PrimeUnitTranslator.lean` —
`factorialGridScale D = (D!)²`, `factorialGridIndex n t j = (t+j)(D!)²` with
`D = n+2`, and the augmented matrix with first row `(index j)!` and row `d+1`
equal to `(index j)!/(d+2)!^{⌊index j/(d+2)⌋}`, by fraction-free Bareiss:

The entries below are the exact decimal digit counts of the absolute determinants.

| `n` | matrix | `t=1` | `t=2` | `t=3` | `t=5` | discharged |
|---|---|---:|---:|---:|---:|---|
| 0 | 2×2 | 6 | 12 | 21 | 40 | yes |
| 1 | 3×3 | 300 | 493 | 704 | 1160 | yes |
| 2 | 4×4 | 15208 | 22145 | 29413 | 44619 | no |

For these four tested values of t, the bound discharges n=0 and n=1;
it does not discharge n=2. This finite table does not assert coverage for
all t or all larger grid sizes.

## The `n = 0` closed form, and a concrete target

At the smallest grid the determinant is explicit. With `D = 2`, scale `4`, and
indices `4t, 4t+4`:

```
det(A) = −3·(4t)!·(4t+4)! / 2^{2t+2}
```

verified exactly against the Lean matrix at `t = 1, 2, 3, 5`.

So at `n = 0` the producer's output is `q ∤ 3(4t)!(4t+4)!/2^{2t+2}`. Since
`299999!` divides that number once `4t+4 ≥ 299999`, and `q ∤ B` is the stronger
statement when `A ∣ B`, proving nonvanishing at `n = 0` for any

```
t ≥ 74999
```

would **strictly strengthen the landed `q ∤ 299999!`**. That is a concrete,
single-instance target with an explicit determinant, rather than a cofinal
family — and it is what this producer is actually good for.

## Reading

The producer is not a broken route; it is a mis-filed one. As an irrationality
producer it cannot work, because its two ingredients are nonvanishing and a
smallness of `1/2`, and no contradiction lives in that gap. As a **smoothness
exclusion** producer it is live, it composes directly with the Kempner-index
result, and it has an explicit closed-form target at its smallest grid.

## Replay

```
./repo-python formal_math/probes/erdos68_rank_two_determinant_scale.py
./repo-python formal_math/probes/erdos68_publish_receipts.py --rank-two-scale
```

## Correction, 2026-09-06 (corrective-integration desk, Erdős #68)

Two points, appended without rewriting anything above.

**Number, confirmed.** The `q > 10^12038` used at section 3 and in the
displayed nonintegrality range matches the receipt
`verification/erdos68-continued-fraction.json`
(`denominator_lower_bound_power_of_two_exponent = 39990`,
`strict_decimal_power_lower_bound = 12038`). No change is needed here. The
`10^12039` form that appears elsewhere in the corpus is the stale one.

**Label.** The research packet records this producer as "dead as an
irrationality route, live as a smoothness-exclusion route". The precise
negative-knowledge label is `counterexample_to_proposal` for the irrationality
reading: the proposal that `det(A) * S` nonintegral is a step toward
irrationality is refuted by the exact comparison `|R| >= 1/q` against the only
recorded smallness `|R| <= 1/2`, which are compatible for every `q >= 2`. The
word "dead" is stronger than what is shown, because the same declarations
remain a live smoothness-exclusion route with an explicit closed-form target
at `n = 0`, namely `|det(A)| = 3(4t)!(4t+4)!/2^(2t+2)`. Nothing here is
kernel-checked; the classification is an ordinary argument over the landed
Lean identity and the landed rounding bound.

## Correction, 2026-09-07 (Type B r3)

The one-kernel reading above is unchanged: nonintegrality of `R = M S + K`
is `q` not dividing `M`. The promotion to a prohibition on every unbounded
factorial-grid family is false for the compressed primitive grids of step
`L = lcm(2..D)`: those primitive moments eventually absorb every fixed
denominator, so cofinal nonintegrality is equivalent to irrationality for that
family. An extra bound below `1/q` is unnecessary there. The nonintegrality
producer remains open. This does not revive `0 < |N| < gcd(minors)`.
