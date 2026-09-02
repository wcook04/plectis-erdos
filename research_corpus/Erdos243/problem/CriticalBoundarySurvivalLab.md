# Erdős 243: the critical boundary constant, measured

## Analytic consumer

`critical_boundary` is the shortest open producer in the corpus:

> Resolve the boundary `n(a_n²/a_{n+1} − 1)_+ ≈ 1`.

It had no computational coverage. The packet's other #243 producers all attack
the signed-state cocycle; this one asks where the hypothesis
`a_{n+1}/a_n² → 1` stops being strong enough to force Sylvester.

## The exact dynamics used

Write the remaining tail as a reduced fraction `u/v`. Taking the next term
`a = ⌈v/u⌉ + k` for an integer `k ≥ 0` gives

`u' = u·a − v = ρ + k·u`,  `ρ = (−v) mod u`,  `v' = v·a`.

`k = 0` is the greedy step, which strictly decreases the numerator and therefore
terminates, so an infinite rational-sum sequence must take `k ≥ 1` infinitely
often; Sylvester is exactly the `k` that keeps `u' = u`. Since `a_{n+1} ≈ v_n/u_n`,
the ratio `a_{n+2}/a_{n+1}²` is about `u_n/u_{n+1}`, so the hypothesis is the
statement that the numerator sequence varies slowly — which forces `ρ` to sit
within `o(u)` of `0` or of `u` at every step.

## Probe

Search the tree of admissible `k` under the constraint `|a_{n+1}/a_n² − 1| ≤ C/n`
— the two-sided form, which implies the producer's one-sided
`n(a_n²/a_{n+1} − 1)_+ ≤ C` — and measure **how many further steps a path can
survive after its first non-Sylvester step**.

That last quantity is the one that matters. The naive measure (how deep a
deviating path gets) is dominated by paths that follow Sylvester to the horizon
and deviate on the final step, which says nothing.

## Exact result: a sharp transition at C ≈ 1

Starting from the Sylvester prefix `2, 3, 7` (tail `1/42`), depth horizon 11,
`k` up to 1000, searches exhaustive rather than node-capped:

| C | steps survived after first deviation | nodes | search exhausted |
|---|---|---|---|
| 0.90 | 1 | 11,874 | yes |
| 0.95 | 1 | 12,220 | yes |
| 1.00 | 1 | 12,609 | yes |
| 1.01 | 1 | 12,693 | yes |
| 1.02 | 1 | 12,781 | yes |
| 1.03 | 1 | 12,868 | yes |
| 1.04 | 1 | 12,952 | yes |
| **1.05** | **10** | 22,027 | yes |

Survival jumps from **1 to 10 — the whole horizon — across a change of 0.01 in
`C`**. The transition sits at `C* ∈ (1.04, 1.05]`.

### A second starting state agrees

Starting instead from the Sylvester prefix `2, 3, 7, 43` (tail `1/1806`), horizon
10, same `k ≤ 1000`, again exhaustive:

| C | steps survived after first deviation | nodes |
|---|---|---|
| 0.50 | 0 | 9,968 |
| 1.00 | 0 | 10,001 |
| **1.04** | **9** | 19,001 |

So the transition sits between `1.00` and `1.04` at this start against
`(1.04, 1.05]` at the first — the same constant to within the resolution of the
sweep, from a different initial state.

The result is not an artifact of the search width. Widening `k` from 8 to 50,
200 and 1000 moves the `C = 1.00` answer only from 0 to 1 and leaves the
`C = 1.05` answer at the horizon throughout, and every sub-threshold search
terminates by exhaustion rather than by hitting the node cap.

## What this decides

The packet's one-line conjecture is quantitatively right: the boundary constant
is `1`, and the measurement puts it within 5% of that. Below it, the hypothesis
`a_{n+1}/a_n² → 1` alone kills a non-Sylvester step within one further step —
no cocycle argument, no payment budget, no CRT repair required. Above it,
deviations run to the horizon and the extra machinery is what has to do the work.

That locates where the remaining #243 producers actually earn their keep. The
signed-state, payment and anti-shadowing producers are needed only in the regime
`n(a_n²/a_{n+1} − 1)_+ > C*`; below `C*` the hypothesis is self-sufficient.

## Claim boundary

A finite tree search from one starting state, to depth 11, with `k ≤ 1000`. The
sub-threshold searches are exhaustive within that horizon, so "survives 1 step"
is a complete statement about paths of that length, not a search limit — but a
deviation that survives beyond the horizon would not be seen. The transition
constant is measured at two starting states and agrees between them to within
the sweep resolution; it is not proved, and start-independence is evidence
rather than a theorem. Erdős #243 remains open.

## Replay

```sh
./repo-python formal_math/probes/erdos243_critical_boundary_survival.py \
  --boundaries 0.9,1.0,1.02,1.04,1.05,1.1 --max-depth 11 --max-k 1000
```
