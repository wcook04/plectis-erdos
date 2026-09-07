# Erdős 68: the gap scalar is uniform to 300000 — one input remains

## The scalar

`GapScalarNormalForm.lean` (new, this wave) packages what every #68 producer
was secretly tracking into one real number per index:

```
t_m = m · g_m,     g_m = factorialGapPredecessorGap m ∈ (0,1]
b_m = −⌊1 + ε_m − t_m⌋
```

with the exact three-window reading:

| window | condition | meaning |
|---|---|---|
| `b = 0` | `ε < t ≤ 1+ε` | lower cylinder — tail-free certificate fails (`D=−1`) |
| `b = 1` | `1+ε < t ≤ 2+ε` | unit carry — the rationality track |
| `b ≥ 2` | `t > 2+ε` | upper jump |

The module also proves the corrected carry-stream expansion (the engine
docstring previously omitted the carry stream; fixed this wave):

```
g_m = ∑_{j=m}^{J} (b_j + ε_j)(m−1)!/j!  +  (m−1)!/J! · g_{J+1},   0 < remainder ≤ (m−1)!/J!
```

and its consumer: a finite block of certified digits that dominates
`(2+ε)/m` from below is a Lean-side **frontier-miss certificate** at index
`m` (`factorialGapStepCarry_ne_one_of_stream_domination`). Digit stream in,
divisibility miss out — no real intervals on the consumer side.

## What was measured

Certified digit stream to **m = 300000**, scalars reconstructed through the
Lean-matched expansion (0 consistency violations against the certified
digits):

| family | count to 300k | null expectation |
|---|---|---|
| unit carries (`D=0`) | 9, last at 21236 | ~11.5 |
| threshold failures (`D=−1`) | 11, last at 65768 | ~11.5 |
| maximal digits | 18 | ~11.5 (Poisson-consistent) |
| closest edge approach (`m≥61`) | 1.65e−3 at `m=1724` | min-of-range typical |

Nothing approached either decision edge closer than 1.65e−3 anywhere in
294k further indices; the null expectation for beating that record is ~0.017
events. Renewal gaps between rare-family members stay exponential-shaped.

## What this decides

The digit-law collapse ("three producers are three level sets of one
scalar") now holds at the **continuous-scalar level across the entire
certified range**, not just to 50000. Every statistic we can throw at the
orbit says *generic*. The surviving Archimedean input is exactly the packet's
non-concentration statement — cofinal escape of `m·g_m` from the rational
window `(1+ε, 1+ε+2/m]` already formalized as
`irrational_factorialGapSeries_of_cofinal_predecessorGap_outside_window`.

There is no digit-side arithmetic left to exploit: any construction route
must beat uniformity, and the data say uniformity is what you get.

## Claim boundary

Finite computation over certified digits to 300000 plus Lean-checked
equivalences. Cofinality is untouched; Erdős #68 remains open.

## Replay

```sh
./repo-python formal_math/probes/erdos68_gap_scalar_spectrum.py --max-m 300000
```
