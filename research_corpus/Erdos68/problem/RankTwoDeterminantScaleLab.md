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

`certified_continued_fraction_denominator_exclusion` gives `q > 10^12039`.
Combined with the observation above, that yields unconditionally

> `N·S ∉ ℤ` for every nonzero integer `|N| ≤ 10^12039`

— if `S` is irrational this is trivial, and if `S = a/q` then `q` cannot divide
such an `N`. So every grid instance with a determinant that small has the
producer's hypothesis already proved.

Computing the determinants literally from `PrimeUnitTranslator.lean` —
`factorialGridScale D = (D!)²`, `factorialGridIndex n t j = (t+j)(D!)²` with
`D = n+2`, and the augmented matrix with first row `(index j)!` and row `d+1`
equal to `(index j)!/(d+2)!^{⌊index j/(d+2)⌋}`, by fraction-free Bareiss:

| `n` | matrix | `t=1` | `t=2` | `t=3` | `t=5` | covered by `q > 10^12039` |
|---|---|---|---|---|---|---|
| 0 | 2×2 | `10^6` | `10^13` | `10^21` | `10^40` | yes |
| 1 | 3×3 | `10^300` | `10^493` | `10^704` | `10^1160` | yes |
| 2 | 4×4 | `10^15208` | `10^22146` | `10^29413` | `10^44619` | **no** |

So the free discharge covers grid sizes `n ≤ 1` and stops immediately: at `n = 2`
the determinant is already `10^15208`. The continued-fraction bound does not
help this producer beyond its two smallest instances.

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
