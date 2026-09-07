# Erdős 68: the predecessor-gap scan is cheap, and failures never repeat

## What this adds

`PredecessorGapThresholdLab.md` evaluated the priority-1 producer
`cofinal_tailfree_predecessor_gap_threshold` for `m = 3 … 210` and recorded the
cost barrier explicitly: `den(Q_m)` grows like `Π(n!−1)`, so exact rational
arithmetic stalls. That barrier is removable.

From the definition `Q_m = (m−1)!·Σ_{n=2}^{m−1} 1/(n!−1)`,

    Q_{m+1} = m·Q_m + 1 + 1/(m!−1),

so the fractional part obeys

    θ_{m+1} = { m·θ_m + δ_m },      δ_m = 1/(m!−1),

and **the scan never forms `den(Q_m)` at all**. The only cost is precision: each
step inflates the error by `m`, so a seed error of `10^{−D}` at `m₀` becomes
`10^{−D}·M!/m₀!` at `M`. Take `D > log₁₀(M!) + margin` and the scan is sound. The
seed `Q_{m₀}` is built exactly as a `Fraction`, so nothing approximate enters.

## Exact result

`probes/erdos68_predecessor_gap_recursion_scan.py`, `m = 30 … 12,000`
(11,971 certificates), working precision 44,141 digits, realised error bound
**1.359e−411** against a soundness threshold of 8.333e−8 — sound by 400 orders
of magnitude.

| | |
|---|---|
| certificates checked | 11,971 |
| fires | 11,968 |
| failures | **3**, at `m = 60, 470, 3026` |
| fire rate | 0.999749 |
| expected failures under uniformity | 6.01 |
| observed / expected | 0.499 |

**CORRECTION (same session).** An earlier version of this note claimed `m = 470`
and `m = 3026` were new findings. **They are not.**
`FactorialDigitLawLab.md` already records the complete `D_m = −1` level set for
`m ≤ 50000`: `5, 9, 23, 60, 470, 3026, 19222, 27472, 30324, 35366`. That lab
reached 50,000 via the GMP certificate stream, well past the `m ≤ 210` of
`PredecessorGapThresholdLab.md`, which is the only range this note originally
checked against. The claim was made without reading the third lab first, and it
was wrong.

What survives is a **method** result, not a discovery result. The recursion route
reproduces `60, 470, 3026` on `[30, 12000]` **exactly**, from an exact `Fraction`
seed and `mpmath` alone — no GMP certificate, no 708,453-bit precision stream, no
exact-rational denominator blowup. That is an independent cross-validation of the
certificate stream by a completely different computational path, which is worth
having: the two methods share no code and no arithmetic backend.

## The structural point: failures never repeat

Every observed failure is **isolated**. The longest run of consecutive failures in
11,971 certificates is **1**.

That is exactly what the recursion predicts. Failure at `m` means `η_m < τ_m ≈ 1/m`
where `η_m = 1 − θ_m`. The map `η ↦ {m·η − δ_m}` expands by `m`, so the portion of
the failure window `[0, τ_m)` that lands back in `[0, τ_{m+1})` has relative
measure `≈ τ_{m+1} ≈ 1/m`. Hence

    P(failure at m and at m+1)  ≈  1/m²,

which is **summable**. Two consecutive failures should occur finitely often, and
in the computed range they occur **never**.

## Why this matters for the producer — corrected scope

**Also corrected.** An earlier version claimed this weakens the obligation from
equidistribution. `FactorialDigitLawLab.md` had already done that, and more
sharply: it states the single remaining Archimedean input as

> for infinitely many `m`, `A_(m−1)` avoids the interval `((1+ε_m)/m, (2+ε_m)/m]`,

and says in terms that it "is weaker than equidistribution and weaker than the
tail-free threshold". So the weakening is not new here either.

What this note adds on top of that is narrower: the **run** observation. Over
11,971 consecutive certificates the longest run of `D_m = −1` is **1**, and the
recursion explains why — failure at `m` means `η_m < τ_m ≈ 1/m`, the map
`η ↦ {m·η − δ_m}` expands by `m`, so `P(fail at m and m+1) ≈ 1/m²`, which is
summable. `FactorialDigitLawLab.md` measures lag-one correlation of `D_m`
(`+0.00080`, `z = 0.18`) but does not state the run structure of the level set,
which is the form the producer actually consumes: cofinality follows from
"finitely many consecutive failure pairs", strictly weaker again than the
interval-avoidance statement above.

The real contribution of this note is therefore the **cost removal and the
independent backend**, not a new obstruction and not a new weakening.

## Join with the level-set identification

`factorial_digit_level_sets_and_uniformity` (packet, `3 ≤ m ≤ 50000`) proves the
rounding digit `D_m = m·N_{m−1} − N_m` resolves all three tracked families at once:

| | |
|---|---|
| `D_m = −1` | **exactly** the predecessor-gap failure set = zero set of the canonical digit `d_m(S)` |
| `D_m = 0` | **exactly** the unit-carry set = maximal set `d_m(S) = m−1` |
| `D_m ≥ 1` | everything else |

So the scan above is simultaneously a scan of the `D_m = −1` level set, and the
recursion `θ_{m+1} = {m·θ_m + δ_m}` is the same orbit as the packet's
`A_m = m·A_{m−1} − 1 − 1/(m!−1) − D_m` — independently re-derived here, which is a
cross-check on both. Failure at `m` is `A_{m−1} < (1+δ_m)/m`; unit carry at `m` is
`A_{m−1} ∈ [(1+δ_m)/m, (2+δ_m)/m)`. **Both are windows of width `≈ 1/m` on the same
orbit**, adjacent to each other, which is why the packet can say the surviving
Archimedean input is one non-concentration statement rather than three.

The two level sets behave alike in the data. Unit carries: 9 in `m ≤ 300000`
(52, 591, 1030, 1407, 1438, 2164, 4258, 10991, 21236), none past 21236, against
`Σ1/m ≈ 12.6` expected. Threshold failures: 6 in `m ≤ 12000` (5, 9, 23, 60, 470,
3026), against `≈ 9.4` expected. Both are generic-rate, both isolated.

**What the run structure adds.** `prime_unit_carry_endpoint_cylinder_dichotomy`
records that rationality would force the lower endpoint cylinder at every
sufficiently large prime. Any such forcing pins the orbit near an endpoint, and
the recursion then holds it there for many consecutive indices — i.e. rationality
predicts **runs** in these level sets, not isolated hits. Runs are exactly what
the data excludes most strongly: over 11,971 consecutive certificates the longest
run of threshold failures is **1**, and the packet's 300,000-deep carry certificate
likewise shows no two adjacent unit carries. Testing for runs is far cheaper than
certifying every carry, so this is a practical route to extending the finite
exclusions.

## Claim boundary

Finite range `m ≤ 12,000`. It does not prove cofinality and does not prove
irrationality; Erdős #68 remains open. The `1/m²` estimate is a heuristic on the
expanding map, not a theorem — turning it into one needs the same kind of
non-concentration input, but for a summable rather than a uniform statement.

## Replay

```sh
./repo-python formal_math/probes/erdos68_predecessor_gap_recursion_scan.py --max-m 12000
```
