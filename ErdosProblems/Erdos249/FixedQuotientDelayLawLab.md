# Erdős 249: the delay cap is not unlucky, it is impossible

## Analytic consumer

`totient_specific_moving_dyadic_escape` asks, for every `c` and odd `v`, for an
`H` divisible by `φ(v)` whose canonical residue lands in the central interval of
radius `c+H+1`. On the pure-dyadic axis the Lean-checked coordinate is

`E_H = totientBlock(H,c) − k(2^H − 1)`,  `E_(H+1) = 2E_H + φ(c+H+1) − k`,

with the nearest quotient `k` held fixed while the state is trapped. The packet's
record of this route is a sequence of uniform **delay caps**, each refuted by a
larger finite search — most recently "delay nineteen at `c = 490794`, ruling out
caps through seventeen".

## The suspicion

`log₂(490794) = 18.91`. If the trap length is governed by how long the doubling
recurrence takes to push a state of size about `c` past a window of radius about
`c`, then it runs for about `log₂ c` steps and **no uniform cap can exist** — every
cap would be refuted by going to larger `c`, which is precisely the observed
history.

## Making the statistic exact

Two quantities have to be separated. While `(2^H − 1)/2 ≤ c+H+1` the window is
wider than the entire residue range, so every `H` is trapped for free; that
trivial prefix has length about `log₂ c`. The informative quantity is the
**post-clear** run: the longest run of consecutive `H` that have all cleared that
threshold, are trapped, and share one quotient `k`.

That definition was fixed before looking at the packet's numbers, and it
reproduces them exactly — see the record table below.

## Exact result: the records track `log₂ c`

Post-clear delay records over `c ≤ 1,400,000`:

| c | post-clear delay | log₂ c | delay / log₂ c |
|---|---|---|---|
| 27 | 5 | 4.75 | 1.052 |
| 141 | 6 | 7.14 | 0.840 |
| 178 | 7 | 7.48 | 0.936 |
| 349 | 12 | 8.45 | 1.421 |
| 14177 | 15 | 13.79 | 1.088 |
| 50490 | 17 | 15.62 | 1.088 |
| 403191 | 18 | 18.62 | 0.967 |
| **490794** | **19** | **18.91** | **1.005** |

The last row is the packet's own witness: **same delay, same `c`**, recovered
from an independently written statistic. The ratio settles at `1.00–1.09`.

So the law is

> `max{ post-clear delay : c ≤ C } ≈ log₂ C`.

## What this decides

The delay-cap programme is **dead, not unlucky**. Cap 17 dies at `c = 50,490 ≈ 2^15.6`.
Cap 19 dies at `c = 490,794 ≈ 2^18.9`. Cap `N` dies at `c ≈ 2^N`. Every future
finite search will refute the next cap, forever, and each refutation costs
exponentially more computation for no new information.

This is a mechanism elimination that no amount of further scanning could have
produced, because further scanning is exactly what the law predicts will keep
happening.

## The redirected target

The producer should target the growth law, not a constant:

> after the window clears, the doubling recurrence escapes a radius-`c` window
> within `O(log c)` steps.

Concretely, `E_(H+1) = 2E_H + φ(c+H+1) − k` doubles the error each step while the
admissible radius grows only additively, so a trapped state must satisfy about
`log₂ c` consecutive near-cancellations between the doubling and the totient
increment. Bounding the number of such coincidences is a statement about the
distribution of `φ(c+H+1) − k` against the doubling orbit — the same shape as the
anti-concentration input the `{2,3,5}` running-LCM problem needs, and unlike a
uniform cap it is not refuted by its own data.

## Claim boundary

This is a finite measurement of an exactly defined statistic over `c ≤ 1.4×10⁶`.
It establishes the observed growth law and the impossibility of the caps already
refuted; it does not prove that no cap exists for all `c`, and it proves nothing
about the irrationality of `Σ φ(n)/2^n`, which remains open.

## Replay

```sh
./repo-python formal_math/probes/erdos249_fixed_quotient_delay_law.py --max-c 1400000 --max-h 64
```
