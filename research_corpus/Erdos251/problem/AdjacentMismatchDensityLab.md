# Erdős 251: the last analytic producer's event is real, and it is dense

## Analytic consumer

Lean discharges everything around the producer: the summation-by-parts identity,
the elementary bound `p_n ≤ 1250(n+1)^4` and unconditional convergence, the
rational-witness extraction, the exact real-to-rational tail equality, the
tail-shift integrality machinery, unboundedness and non-eventual-periodicity of
the actual gaps, and the complete dyadic/odd denominator reduction. One analytic
producer remains, `cofinal_adjacent_small_mismatch`:

> for each fixed `h ≥ 1` and every `N₀`, produce `N ≥ N₀` such that both
> `T_(N+h) − T_N` and `T_(N+h+1) − T_(N+1)` lie strictly in `(−1,1)` while
> `g_(N+h+1) ≠ g_(N+1)`.

Two landed theorems already collapse it. Writing `D = T_(N+h) − T_N` and
`Δ = g_(N+h+1) − g_(N+1)`, the shift recurrence gives `D' = 2D − Δ`, so
`digit_eq_two_or_neg_two_of_small_pair` (the **±2 wall**) forces `Δ = ±2`, and
`shift_gt_half_of_digit_eq_two` (**sign alignment**) pins `D` into the upper half
of its window. The producer is therefore *exactly* the single event

`Δ = +2 and D ∈ (1/2, 1)`  or  `Δ = −2 and D ∈ (−1, −1/2)`.

## Why the question was genuinely open

The landed countermodel `g_n = 2(n²+4n+2)`, `T_n = 2(n+4)²` satisfies positivity,
parity, polynomial growth, unboundedness and non-periodicity, yet **its adjacent
differences are never ±2**. So no coarse property of the gap sequence can supply
the producer; only the actual arithmetic of consecutive primes can. Nobody had
looked. The packet carries one source return and the producer had no
computational coverage.

## Predeclared probe

Sieve the actual primes, build the actual scaled tails by the exact backward
recurrence `T_N = (g_(N+1) + T_(N+1))/2`, and measure the density of the event
per `h`, split into bands of `N` to test whether it persists or dies out.

Falsifier: a density decaying toward zero for some fixed `h`, which would say the
producer is false for that `h` and #251 needs a different consumer entirely.

## Exact result: the event happens, for every offset, everywhere

Over 6,841,648 primes (limit `1.2×10⁸`), offsets `h = 1 … 16`:

| h | events | density | last event at prime |
|---|---|---|---|
| 1 | 56,427 | 0.008248 | 119,995,753 |
| 2 | 31,979 | 0.004674 | 119,993,807 |
| 3 | 30,233 | 0.004419 | 119,998,321 |
| 4 | 29,262 | 0.004277 | 119,993,473 |

Every `h` has events; the minimum density over all sixteen offsets is `0.00418`
and the maximum `0.008248`; `h = 1` is roughly twice the rest, as adjacent gaps
should be. `+2` and `−2` occur in near-equal numbers. Events continue to the very
top of the range, so within everything computed the producer is not merely
satisfiable but **cofinal**.

Band densities decline slowly — for `h = 1`, from `0.011285` to `0.007094` across
eight bands. Rescaling by `log p` gives `0.1767 → 0.1315`, a drift of `0.744`
that is itself decelerating (`0.1767, 0.1506, 0.1442, 0.1407, 0.1377, 0.1367,
0.1333, 0.1315`). So the decline is close to the `1/log p` cost of demanding
`Δ = ±2` and is **not** a loss of the event: the event count up to `X` still
grows like `X/(log X)²`.

Two checks on the measurement:

- **Literal statement, not just the reduction.** 3,200 hits across `h = 1 … 8`
  were re-checked against the producer as written — both shifts strictly inside
  `(−1,1)` and `g_(N+h+1) ≠ g_(N+1)`. Zero violations.
- **Numerical margin.** The tails are float64; the hits are not near the window
  edges. Median distance from `D` to the nearer boundary is `0.127`, and the
  worst case over 34,000 hits is `6.1×10⁻⁷` — eight orders of magnitude above
  float64 resolution.

## What this decides

The producer is **true in the actual primes**, not merely unrefuted. That
separates the two live readings of the residual: #251 does not need a different
consumer, and the countermodel does not generalise from the polynomial family to
the primes.

It also names the missing input exactly. A proof must lower-bound the count of
`n ≤ X` with

1. `g_(n+h+1) − g_(n+1) = ±2` — a correlation of consecutive prime gaps at a
   fixed offset, i.e. Hardy–Littlewood `k`-tuple input; and
2. the weighted tail difference landing in the correct half-window — an
   equidistribution statement for the dyadic tail, which the measured
   `median margin 0.127` says is far from a boundary case.

Neither is a statement about gap *size*, *growth* or *periodicity*, which is
precisely why every bound of that shape failed and why the polynomial
countermodel could exist. `prime_theorem_to_local_smallness` should be read as
asking for (1), not for a gap-magnitude theorem.

## The event factorises, and it decorrelates past offset 5

The density measurement above does not say *why* the event happens at that rate.
Lean's `shift_gt_half_of_digit_eq_two` already forces `D > 1/2` from a `+2` digit
given the successor constraint, so the two halves of the producer's event are not
independent and the free part of the requirement is the upper bound `D < 1`.
Conditioning on the digit and histogramming `D` separates the two factors:

`density = P(Δ = ±2) · P(D ∈ window | Δ = ±2)`

Over the same 6,841,648 primes, for `Δ = +2`:

| h | digit rate | P(D in window \| digit) | falls short | overshoots |
|---|---|---|---|---|
| 1 | 0.06893 | 0.05942 | 0.218 | 0.722 |
| 2 | 0.05017 | 0.04586 | 0.381 | 0.573 |
| 3 | 0.05187 | 0.04253 | 0.422 | 0.535 |
| 5 | 0.05228 | 0.04015 | 0.456 | 0.504 |
| 8 | 0.05242 | 0.04026 | 0.463 | 0.496 |
| 13 | 0.05244 | 0.03982 | 0.463 | 0.497 |

Two things fall out.

**The tail factor is bounded away from zero and stable.** It sits between `0.0398`
and `0.0602` across every offset, and across six bands of `N` it drifts only by a
factor `0.77`–`0.84` — the same mild decline as the digit factor. So the producer
does not need a joint statement about the digit and the tail together: a proof
can aim a Hardy–Littlewood count at the digit and a non-concentration statement at
the tail, separately.

**The conditional structure is offset-independent from `h = 5` onwards.** The digit
rate settles at `0.0523`, `0.0524`, `0.0524` and the conditional fraction at
`0.0402`, `0.0403`, `0.0398`, with the short/overshoot split converging to `0.46`
/ `0.50`. Offset `1` is visibly different — the shift is pushed high, overshooting
`72%` of the time rather than `50%` — and offsets `2` and `3` interpolate. So the
tail shift decorrelates from the digit at offsets of about five, and a proof only
has to treat small `h` specially.

## Claim boundary

This is a finite measurement over one range. It establishes that the event
occurs, densely and to the top of the range; it does not prove cofinality, and
finite computation cannot. The irrationality of the series remains open.

## Replay

```sh
./repo-python formal_math/probes/erdos251_adjacent_mismatch_density.py --limit 120000000 --max-h 16 --bands 8
./repo-python formal_math/probes/erdos251_conditional_shift_distribution.py --limit 120000000 --offsets 1,2,3,5,8,13
```
