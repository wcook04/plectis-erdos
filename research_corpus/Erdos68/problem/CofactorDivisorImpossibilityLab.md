# Erdős 68: a priority-1 producer asks for an object that cannot exist

## Claim boundary

Elementary integer algebra plus a check on the implementation. It removes a
producer from the frontier; it proves nothing about the target, and Erdős 68
remains open.

## The producer, and the search that failed

`erdos68_appended_channel_determinant_beats_determinantal_divisor`, priority 1:

> Find arbitrarily far-out index sets whose channel matrix has corank one and
> nonzero appended factorial determinant, while the exact surviving-channel
> determinant residual is nonzero and has absolute value strictly below the gcd
> of maximal minors.

and the packet's own record of trying:

> `primitive_cofactor_determinant_divisor_bottleneck` — The returned corank-one
> cofactor construction reduces an unbounded certificate family to an
> appended-row determinant residual `N(I,D)` satisfying `0 < |N(I,D)| < Δ(I,D)`,
> where `Δ` is the gcd of maximal minors. **No unbounded family satisfying this
> inequality was obtained.**

## Why it failed

Not for want of an unbounded family. **No single instance satisfies it.**

Expand the appended determinant along the appended row. Each cofactor is a
maximal minor of the unappended channel matrix, and `Δ` divides all of them by
definition. So `Δ ∣ N`, and

```
N ≠ 0  ⟹  |N| ≥ Δ .
```

`0 < |N| < Δ` is unsatisfiable over the integers. The producer asks for an
object that does not exist, and the recorded search failure is the expected
outcome rather than a hard open case.

## The reading does not matter

The definitions of `N` and `Δ` live only in packet prose — there is no Lean
declaration and no script in this repository that defines either. So the reading
cannot be checked against a definition. It does not need to be; every available
reading gives the same conclusion:

| reading of `Δ` | conclusion |
|---|---|
| gcd of maximal minors of the **unappended** channel matrix | `Δ ∣ N` by the expansion, so `|N| ≥ Δ` |
| gcd of maximal minors of the **appended square** matrix | the only maximal minor is `N`, so `Δ = |N|` and `|N| < Δ` is false outright |
| channel matrix wider than `k+1` columns, `N` a `(k+1)`-minor | expansion still yields `k`-minors of the channel matrix, all divisible by `Δ` |

That the packet carries a priority-1 producer with no definitional source is
itself worth recording. It is how an unsatisfiable condition survived on the
frontier: nothing could be checked against it.

## Check

`formal_math/probes/erdos68_cofactor_divisor_impossibility.py`, over channel
shapes `k×n` for `(k,n) ∈ {(2,3),(3,4),(3,5),(4,5),(4,6),(5,6)}`, random integer
entries in `[−40,40]`, taking **every** `(k+1)`-column selection of the appended
matrix rather than only the square case:

**6000 nonzero appended determinants, 0 escaping `Δ`.**

The divisibility is a theorem, so the run is a check on the implementation and a
concrete witness count, not the proof.

## Reading, next to the rank-two result

This is the second producer in this packet found to be filed against the wrong
conclusion, by the same question: *what does this producer actually output?*

* `erdos68_rank_two_strict_nonvanishing` — output is `q ∤ det(A)`, a smoothness
  exclusion, not irrationality; nonvanishing alone cannot contradict rationality
  because `|R| ≥ 1/q` while the only recorded smallness is `|R| ≤ 1/2`. Live,
  mis-filed. See `RankTwoDeterminantScaleLab.md`.
* `erdos68_appended_channel_determinant_beats_determinantal_divisor` — the
  condition is unsatisfiable. **Dead.**

The two share a cause. Both are linear-form producers, and a linear-form
producer `0 < |c·S + k|` closes the irrationality question only when the
construction forces `c` to be a multiple of the hypothetical denominator `q`, so
that the form is an *integer* and `0 < |·| < 1` is immediate. Checked against
the rest of the packet, `erdos68_scalar_factorial_tail_orbit_nonintegrality`
passes that test — it explicitly takes `m` divisible by `lcm(b, L_D)` with `b`
the hypothetical denominator — and is correctly filed. The two above do not.

## Replay

```
./repo-python formal_math/probes/erdos68_cofactor_divisor_impossibility.py
./repo-python formal_math/probes/erdos68_publish_receipts.py --cofactor-impossibility
```
