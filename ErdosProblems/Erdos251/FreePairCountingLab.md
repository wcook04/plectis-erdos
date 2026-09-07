# Free-pair dyadic-window counts

Type B file 05, Proposition B, independently checked. The lattice
`free_pair_integral_iff_modEq` already decides each pair. The count is the
cardinality of that decision in a window `[X, 2X)`.

## Exact classification (Lean)

`FreePairCounting.lean` (predicates; `RealIntegral` is not a decidable
`Finset.filter`):

- Irrational `T 0`: `IsFreePair T t X N M ↔ (N,M) ∈ congruentPairSet t X`.
- Rational `T 0`, past an odd-denominator cutoff: free iff `t`-congruent and
  not `lcm(t, ord)`-congruent.
- At the order itself: no free pair past the cutoff.

## Ordinary asymptotic

Among `X` consecutive integers, each residue class modulo a fixed `v` has
size `X/v + O(1)`. Unordered pairs inside a class contribute
`X^2/(2v) + O_v(X)`. Hence, writing `C_t(X) = # freePairSet T t X`,

- irrational: `C_t(X) = X^2/(2t) + O_t(X)`;
- rational: `C_t(X) = X^2/2 (1/t - 1/lcm(t,λ)) + O_{t,λ}(X)`.

A linear lower bound that lets only the larger index grow is not equivalent
to irrationality.  The repaired witness is `T 0 = 5/2`, `T 1 = 3`,
`T N = 2` for `N ≥ 2`, with digits `a₁ = 2`, `a₂ = 4`, and `aₙ = 2` for
`n ≥ 3`.  Every pair of indices `≥ 1` is integral, while `T M − T 0 = −1/2`
for `M ≥ 2`.  The previous integer-valued tail `3,2,2,…` had *no*
nonintegral pairs at all; `earlyFreePair_nonintegral_of_zero` is the landed
repair.

Nothing here produces free pairs for the actual primes. The live equivalent
of irrationality remains cofinal free-pair nonintegrality, not a windowed
density.
