# Erdős 1041: the turning-inflation route dies on a turning floor

Status: one proved proposition, one refuted route, and one instrument defect
found in a shared engine. 2026-08-23. Erdős #1041 remains open; nothing here
bears on the truth of the conjecture, only on one mechanism for proving it.

## The route that is refuted

[CriticalBudgetLab.md](CriticalBudgetLab.md) names the live reformulation with
the best odds: bound the total variation `α` of `arg f'` along the two descent
branches at a hub, since a curve whose tangent stays in a cone of half-angle
`α/2` has length at most chord over `cos(α/2)`. Combined with the global budget
theorem `d₁ + d₂ ≤ 2R`, the proposed chain is

```text
L(c)  <=  (|z_a − c| + |z_b − c|) / cos(α_max/2)   <=   2R / cos(α_max/2),
```

and the hope is that this closes below `2R` at a selectable hub. The note also
records the encouraging half: `α = 0` exactly on the extremal family `zⁿ − rⁿ`.

**The chain cannot close at any degree `n ≥ 3`.** It closes only at `n = 2`, and
there with equality.

## The turning floor

> **Proposition (turning floor).** Let `c` be a *simple* critical point with
> `|f(c)| < 1`, let its two descent branches reach roots `a` and `b`, let
> `α_A, α_B` be the total variations of the tangent direction along them, and let
> `φ` be the angle that `a − c` and `b − c` subtend at `c`. Then
>
> ```text
> α_A + α_B  >=  π − φ,        hence   α_max  >=  (π − φ)/2.
> ```

*Proof.* At a simple critical point `f(z) − f(c) ≈ ½f''(c)(z−c)²`, so the two
descending directions are exactly opposite: `+s` and `−s`. A curve's chord
direction lies in the closed convex hull of its tangent directions, so
`|arg(a−c) − arg(s)| ≤ α_A` and `|arg(b−c) − arg(−s)| ≤ α_B`. Since `arg(s)` and
`arg(−s)` differ by `π`,

```text
φ = |arg(a−c) − arg(b−c)| >= π − α_A − α_B.  ∎
```

Measured: **0 violations in 978 hubs**, minimum slack `3.5e-4` rad at
`φ = 179.98°`.

## Why that kills the chain

The budget theorem is saturated **exactly** on `zⁿ − rⁿ` at `c = 0` — confirmed
as `max (d₁+d₂)/(2R) = 1.000000000000` over `24048` critical points, attained on
that family at every degree. There the two endpoint roots are adjacent vertices
of the regular gon, so `φ = 2π/n`, and the turning floor gives
`α_max ≥ π/2 − π/n`. Substituting into the chain, where the budget is tight the
best the mechanism can return is

```text
2R · sec(π/4 − π/(2n))
```

| n | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| factor | **1.0000** | 1.0353 | 1.0824 | 1.1223 | 1.1547 | 1.1810 | 1.2027 |

strictly above `2R` for every `n ≥ 3`.

**The recorded `α = 0` on the extremal family is correct but inapplicable**, and
this is the whole point. It holds at the *degenerate* central hub of multiplicity
`n−1`, whose `n` branches are the `n` radii. The construction needs a *simple*
hub with two branches, and resolving the degeneracy forces the pair onto one
smooth curve, which cannot follow two radii meeting at `2π/n`. So `α` does not
vanish in the extremal limit — it converges to a positive constant while the
budget converges to its maximum. Those two limits are what kill the route.

## Measurements

Extremal-limit configurations `clamp(0.9·exp(2πik/n)(1+ε·offset))`, `ε` from
`1e-2` down to `1e-7`. Worst `(d₁+d₂)/(2R cos(α_max/2))` at the least-`|f(c)|`
hub, **monotone increasing as `ε → 0` at every degree**, so these are lower
bounds on the limit rather than maxima:

| n | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|
| worst ratio | 1.066402 | 1.136610 | 1.187424 | 1.175054 | 1.166093 | 1.212491 |
| `α` there | 40.71° | 57.35° | 66.94° | 67.81° | 70.75° | 79.05° |

On the corpus's own bit-exact QC witnesses, **with no search at all**: degree 6,
both admissible hubs give `1.100817` and `1.138117`; degree 9 gives `0.992548`,
`0.998101`, `1.329302`.

**The margin is far larger than the first search suggested.** Maximising `α`
directly, rather than maximising the chain ratio, finds at **degree 3** — the
easiest case, and the one already fully proved by other means — a clean
admissible hub with

```text
alpha = 114.65 deg,   (d1+d2)/2R = 0.96942,   chain ratio = 1.79561,
```

verified at tight tolerance. So the route fails at degree three by about **80
percent**, not by the 7 percent that a ratio-targeted search reached, and not by
the 6.6 percent of the extremal limit. Every earlier number here understated the
failure because the search was optimising the wrong objective — the same lesson
this file records six times over, arriving once more.

At the least-critical-value hub specifically, maximised `α` runs
`44.95, 75.18, 95.15, 106.69` degrees for `n = 3,4,5,6` while the budget there
falls `0.960, 0.725, 0.654, 0.541`. So at that hub the chain ratio is an
interior trade-off between turning and budget, which is exactly why the
selector's own refutation lives on the extremal family, where the budget goes to
1 while the turning stays bounded away from 0.

**Steelman.** The minimum over *all* clean admissible hubs of the chain ratio
exceeds one in `16/260` random configurations (max `1.098862` at `n = 5`), at
`1.073844` and `1.116444` under attack at `n = 3, 4`, and at `1.100817` on the
degree-6 witness. So the *mechanism* fails, not merely the least-critical-value
selector.

**The supremum is `+∞`, not a pinned value.** `α` exceeds `π` at `5/436` clean
hubs at tight tolerance, maximum `224.03°`, at which point `cos(α/2) < 0` and the
bound is vacuous. Inside the extremal family at `n = 8`, `ε = 1e-6`, a hub
reaches `α = 192.574°` with endpoint error `2.1e-14`.

## Instrument defect in a shared engine

`system/lib/formal_math_lemniscate.descending_pair` locates branch starts by
`np.roots` on the level polynomial. At `u₀ = 1e-6` the two preimages `c ± s·u₀`
are about `1e-7` apart while the residual to resolve is `|v|u₀² ~ 1e-14` against
a constant term `|v| ~ 1e-2`. Measured **start directions came out up to 50°
wrong**, and a Newton polish on `f(z) − (1−u₀²)v` does not fix it.

**Lengths are unaffected** — the level-set flow contracts the initial error by
`|f'(start)|/|f'(end)| ~ 1e-7`, and an independent tracker agrees with
`descending_pair` to `1.1e-7`, so the repository's recorded arc lengths are
sound. **`α` is exactly the quantity that is not protected**: the argument error
at the start is the position error divided by `|z − c|`. A first run of this
probe showed `0.145` rad of pure artifact.

The fix used here: Taylor-expand `f` at `c` by repeated synthetic division, set
`a₁ = 0` exactly, and Newton on `aₙdⁿ + … + a₂d² + u²v = 0`, which cancels
`a₂d²` against `u²v` (both of size `|v|u²`) instead of against `|v|` — a `1/u²`
conditioning gain — then track the branch in the `d` coordinate. **Anyone
measuring angular quantities on these branches must not use the shared engine's
start direction as it stands.**

## The repair the refutation points at: weight the turning by arclength

The cone bound loses because it charges the **supremum** of the turning over the
whole branch. On the extremal family the turning is genuinely large — the floor
above says so — but it is **concentrated near the hub, where `ds` is tiny**, and
the branch is straight everywhere else. So the true length equals the chord sum
while `sec(α_max/2)` charges as if the whole branch were bent. That is a defect
of the estimate, not of the conjecture, which is why MIN survives here.

The sharp replacement is an exact identity, not an estimate. For a branch from
`p` to `q` with unit tangent `T(s)` and chord direction `e = (q−p)/|q−p|`,
`∫ T ds = q − p`, so `∫ <T,e> ds = |q − p|` and therefore

> **(CD)**  `L  =  chord  +  ∫ (1 − cos θ(s)) ds`,   `θ(s) = angle(T(s), e)`.

Summing the two branches at a hub,

```text
L(c)  =  (d₁ + d₂)  +  D(c),        D(c) = ∫_A (1 − cos θ) ds + ∫_B (1 − cos θ) ds >= 0.
```

This is exactly tight on the extremal family: there `L(c) → 2r` and
`d₁ + d₂ → 2r`, so `D(c) → 0` even though `α_max → π/2 − π/n > 0`. The identity
sees the concentration; the cone bound cannot.

**Restated target.** The global budget theorem already gives
`d₁ + d₂ < 2` strictly at every critical point for roots in the open disk. So
MIN reduces to a statement about the deficit alone:

```text
at some admissible hub,   D(c)  <  2 − (d₁ + d₂).
```

Both sides vanish together on the extremal family, which is the correct
behaviour for a sharp statement and the reason no uniform positive margin can
exist (the Cassini no-slack theorem says the same thing from the other side).
Note also `1 − cos θ ≤ θ²/2`, so `D(c) ≤ ½∫θ² ds`: a *weighted* `L²` turning
bound would suffice, whereas the refuted route needed an `L^∞` one. That is the
gap in a sentence.

Nothing here is proved. `(CD)` is elementary; the content would be an estimate
for `D(c)` in terms of the polynomial, and none is offered. It is recorded
because a closed mechanism should name its own repair rather than leave a dead
end.

## What is not claimed

**MIN is not refuted, and is not claimed to survive.** Worst `L(c)/(2R)` at the
minimum-length hub was `0.9827` under attack at `n = 3` and `0.999956` in the
extremal limit, still rising. That is the pinned-just-below-threshold pattern
this directory has been wrong about six times; here a known equality family
(`zⁿ − rⁿ` gives `L = 2r = 2R` at the degenerate hub) means the supremum is *at
least* 1, and the adversarial search was demonstrably weaker than the parameter
scan at `n ≥ 5`. **No floor should be quoted.**

Validation gates, all passing: `z² − a²` gives `L = 2a`, `α = 0`, every ratio
exactly `1.000000000000`; the degree-6 witness minimum branch-pair total
reproduces as `1.7639419` against the recorded `1.763942`, and degree 9 as
`1.5459951` against `1.545995`; the cone bound `L ≤ chord/cos(α/2)` has zero
violations; the turning floor has zero violations. `TIGHT → ULTRA` drift on
reported ratios is about `1e-6`, so quote six significant figures and no more.

Receipt: [`scripts/check_erdos1041_turning_inflation.py`](scripts/check_erdos1041_turning_inflation.py).
Run `--modes selftest` first; it is the gate.

## Claim boundary

Proved: the turning-floor proposition, by an ordinary convex-hull argument at a
simple saddle. Its consequence that the stated chain returns at least
`2R sec(π/4 − π/(2n))` where the budget is tight, hence cannot close for `n ≥ 3`.

Measured: every ratio table above, and the saturation of `d₁+d₂ ≤ 2R` on the
extremal family.

Not established: anything about MIN, AVG, or the truth of Erdős #1041. This note
closes one mechanism and leaves the problem open.
