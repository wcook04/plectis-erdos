# Erdős #1041: collective radial window (ordinary, not substituted for 71/10)

Status: independently checked ordinary analysis, 2026-09-07. Rational
comparisons replay from

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_r2_revision_exact_cores.py --quick
```

Not Lean-checked. Not inserted into the short note: the inspectable
constant-factor theorem remains `71/10` in `K_{2μ}`
(`unconditional_constant_factor_pair_geodesic`). This note records a
sharper coefficient in the same sublevel, obtained by averaging complete
precritical lifts and counting every nontrivial component. Erdős #1041
remains open.

## Collision

The registered `71/10` proof in `UnconditionalConstantFactorBound.md`
stops the precritical lift at `rμ` and uses Koebe pointwise, then
assembles inside one ancestor component. The argument below averages the
*complete* radial length of each one-root inverse (no Koebe cutoff) and
sums over all nontrivial components of `K_σ`. It is a different
derivation of a stronger constant in the same `K_{2μ}`, not a new
containment level and not a replacement of `13/25`.

## Lemma (radial mean)

Let `φ` map the unit disc conformally onto a finite-area domain `U`.
Then

```text
(1/2π) ∫_0^{2π} ∫_0^1 |φ'(r e^{iθ})| dr dθ  ≤  sqrt(Area(U)/π).
```

The constant is sharp for affine maps.

Write `φ(z) = a_0 + Σ_{m≥1} a_m z^m`. Cauchy–Schwarz for the probability
measure `dr dθ / 2π`, Parseval, and Tonelli give

```text
(mean |φ'|)^2  ≤  mean |φ'|^2
               =  Σ_{m≥1} m^2/(2m−1) |a_m|^2
               ≤  Σ_{m≥1} m |a_m|^2
               =  Area(U)/π,
```

using `m^2 ≤ m(2m−1)` and the injective area formula. Equality holds for
`φ(z) = a_0 + a_1 z`.

## Collective window

Let `f` be monic of degree `n ≥ 2`, `μ = min |f(c)|` over critical
points, `K_t = {|f| ≤ t}`, and for `σ ≥ μ` let `M(σ)` be the number of
roots in components of `K_σ` that contain at least two roots. For
regular `s`, coarea gives `A'(s) = ∫_{|f|=s} |dz|/|f'|`. Pólya supplies
`A(T) ≤ π T^{2/n}`.

**Theorem.** For every `T > σ ≥ μ > 0` there are distinct roots joined
inside `K_t` for some regular `t ∈ (σ, T)` with

```text
length  ≤  sqrt(2/M(σ)) · T^{1/n}
           · sqrt( 2 + (sqrt(log(T/μ)) + π / sqrt(log(T/σ)))^2 ).
```

No root-location, simplicity, or separation hypothesis is used.

*Proof sketch (checked).* Average `s A'(s)` against `ds/s` on `(σ, T)`
to obtain a regular `t` with `t A'(t) ≤ Y / log(T/σ)`, where
`Y = A(T) − A(μ)`. Retain every component of `K_t` that contains a
nontrivial piece of `K_σ`; write `k` for their total root count, so
`k ≥ M(σ)`. Each such component is a Jordan domain of degree `k_j ≥ 2`
mapped properly onto `{|w| < t}`, hence `∫ |f'| |dz| = 2π k_j t` on its
boundary and Cauchy–Schwarz gives `P_j^2 ≤ 2π k_j t A_j'(t)`. Summing
and using the mean-value choice,

```text
Σ P_j  ≤  sqrt(2π k t A'(t))  ≤  sqrt(2π k Y / log(T/σ)).
```

For almost every argument `θ`, the segment `[0, t e^{iθ}]` has `k`
inverse lifts in the retained components. Split each lift at modulus
`μ`. Below `μ` the lobes are one-root; the radial-mean lemma and
Cauchy–Schwarz over `k` roots bound the mean low length by
`sqrt(k X / π)`, `X = A(μ)`. On the annulus, Cauchy–Schwarz with weights
`sqrt(u)/|f'|` and `1/sqrt(u)`, together with the Jacobian identity
`Area = ∫∫ Σ u / |f'|^2 du dθ`, bounds the mean high length by
`sqrt(k log(t/μ) Y / 2π)`. Choose an argument realising the mean. In
each component, cyclically hop between consecutive fibre points using
the two lifts and the intervening boundary arc. Across the `k`
candidates every lift is used twice and every retained boundary once, so
some candidate satisfies the displayed bound. A last Cauchy–Schwarz on
the disjoint budgets `X` and `Y`, then Pólya, finishes the estimate.

## Coefficient `C_* < 573/100` in `K_{2μ}`

Take `σ = μ` and `T = 2μ`. Then `M(μ) ≥ 2` and, for `n ≥ 4`,

```text
length  ≤  2^{1/n} μ^{1/n} sqrt(2 + log 2 + 2π + π^2/log 2)
        ≤  C_* μ^{1/n},
```

with `C_* = 2^{1/4} sqrt(2 + log 2 + 2π + π^2/log 2)`. The exact-core
checker bounds `log 2` by the positive `artanh(1/3)` series, `π` by
Machin, and `sqrt(2)` by `1414213563/10^9`, and verifies
`C_*^2 < (573/100)^2` with positive rational margin. The selected level
is strictly below `2μ`. Degree two is the root segment of length
`2 sqrt(μ)` inside `K_μ`. Degree three is the scale-free cubic hub bound
already in `CubicCriticalHub.md` (length `≤ 2 μ^{1/3}` inside `K_μ`).

This improves the coefficient, not the containment. The short note keeps
`71/10` as the inspectable lead constant.

## Occupancy: fourteen critical points at `|f(c)| ≤ 3/5`

If `μ ≤ 13/25`, the registered all-degree theorem already joins two
roots inside `{|f| < 1}` with length `< 2`. If `μ > 13/25` and at least
fourteen critical points, counted with multiplicity, satisfy
`|f(c)| ≤ 3/5`, then `N(3/5) ≥ 14` implies `M(3/5) ≥ 15` by the
component formula `M = N + q` at a regular (or right-limits) level.
Applying the collective window with `σ = 3/5` and `T = 1` gives

```text
L^2  ≤  (2/15) [ 2 + (sqrt(log(25/13)) + π / sqrt(log(5/3)))^2 ].
```

The checker verifies the rational comparison
`sqrt(log(25/13)) < 81/100`, `sqrt(log(5/3)) > 71/100`, `π < 22/7`,
whence the displayed upper bound is `< 4`. The path lies at a regular
level `t < 1`.

A stronger formulation is `M(3/5) ≥ 15`, which can hold for many
separate small mergers. This is a sufficient occupancy criterion beyond
the single threshold `μ ≤ 13/25`. It does not empty the high-critical
residual.
