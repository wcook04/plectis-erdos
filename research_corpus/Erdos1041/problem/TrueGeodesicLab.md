# Erdős 1041: the refuting polynomials are nowhere near extremal

## What the packet's ten negative results actually establish

Every negative result on file kills a specific **path family**: direct root
chords, fixed-origin broken lines, metric-selected critical-point spokes, the
Newton descending inverse-ray branches at that critical point, spanning-tree
budgets, and the radial-lift angular average. Each exhibits a polynomial on which
that family fails.

None of them computes the shortest path. So the statement the problem actually
makes — that the infimum over **all** curves is below 2 — has never been measured
on the very polynomials that refute the explicit families.

## Method

The lemniscate sits inside `|z| < 2`: with all roots in the unit disk,
`|z| ≥ 2` forces `|f(z)| ≥ (|z|−1)ⁿ ≥ 1`. Grid that box, keep the cells with
`|f| < 1`, and build a graph on them with a 16-neighbour stencil (all offsets with
`|dx|,|dy| ≤ 2` and `gcd = 1`), which cuts grid-metric anisotropy well below a
percent. A move is admitted only when every sampled interior point of the segment
is also inside, so no path can cut a corner through the exterior. Dijkstra from
each root then gives the pairwise geodesics.

A grid path is a genuine path in the domain, so the measurement **overestimates**
the true geodesic: a value below 2 witnesses that the infimum is below 2.

**Validation.** On `f = z² − a²` with `a = 1/2` the chord `[−a, a]` is interior and
the geodesic is exactly `2a = 1`. Measured: `1.0025`, `1.0026`, `0.9987` at grids
400, 700, 1100. On the cubic below the value is stable to `±3×10⁻³` across grids
500 → 1400. So the method resolves to about 0.3%, ample against a threshold of 2.

## Exact result

| configuration | which family it refutes | true geodesic | slack below 2 |
|---|---|---|---|
| `z³ − (99/100)³` | direct root chords | 1.782 | 0.218 |
| five-root exact, `r = 99999/100000` | origin-spoke broken lines | **0.061** | 1.939 |
| `z⁴ + 0.01z − (0.99)⁴` | coalescing critical-value arguments | 1.496 | 0.504 |
| `z⁶ + 0.01z − (0.99)⁶` | as above | 1.102 | 0.898 |
| `z² − a²`, `a = 0.9` | the Cassini family | 1.803 | 0.197 |
| `z² − a²`, `a = 0.99` | as above | 1.977 | 0.023 |
| `z² − a²`, `a = 0.999` | as above | 1.997 | 0.003 |

The five-root configuration is the sharpest case. It defeats the origin-spoke
construction, and its true geodesic is **0.061**: its five roots all sit on the
circle of radius `r`, at angles `0`, `±101.4°`, `±98.2°`, so two of them are
`3.2°` apart. It refutes a construction; it is not remotely a hard instance.

## What this decides

**The bound is tight in exactly one place, and it is not where the negative
results live.** Only the degenerate quadratic family `z² − a²` approaches 2, and
it approaches from below for the trivial reason that its chord is interior, so
the geodesic *equals* the root distance `2a < 2`. Every other refuting polynomial
carries slack between 0.2 and 1.9.

So the packet's first negative result — "no polynomial-independent positive
length slack is available, even for the quadratic Cassini family: root distances
`2 − 2/m` approach two" — is about **uniformity of a construction**, not about the
geometry being tight. The geodesic data separates the two readings that the
path-family results could not:

1. A proof cannot use a fixed path family with a uniform margin. That is settled,
   and the Cassini degeneration is why.
2. But away from that one-parameter degeneration the true slack is large. So a
   construction is allowed to depend on the polynomial, and the search for one
   should not be calibrated against the five-root or cubic configurations — they
   are easy for the actual statement and hard only for a particular recipe.

That redirects the remaining producers. `critical_point_selection_with_inverse_ray_length_control`
asks for a critical point whose two descending branches total below 2; the branch
lengths at these configurations exceed the true geodesic substantially, so the
producer is asking for more than the statement needs.

## The degree-two case is exact, and it is why that family is extremal

For `n = 2` the chord is **always** interior. Write `f = (z−z₁)(z−z₂)`,
`d = |z₁−z₂| < 2`, and parametrise the chord as `z = z₁ + t(z₂−z₁)`. Then
`|z−z₁| = td` and `|z−z₂| = (1−t)d`, so

`|f| = t(1−t)d² ≤ d²/4 < 1`  for all `t ∈ [0,1]`.

So the geodesic equals the root distance `d`, and `sup d = 2` is approached but
never attained. That is the whole content of the Cassini degeneration: it is
extremal for the trivial reason that its geodesic *is* the chord.

## A methodological result: the optimiser finds the method's failure mode first

Maximising the raw grid geodesic over configurations returned a leader **above
2** at `n = 2`, with several higher degrees reporting a pair as unreachable
altogether. Both are artifacts, and the exact statement above proves it: at the
reported leader the roots are at modulus `0.999` and nearly antipodal, so
`d = 1.998` and the chord is interior with `|f| = 0.996` at its midpoint. The
corridor where `|f| < 1` around that chord is far thinner than a grid cell, so the
grid cannot see it and reports a detour of `2.003` — and an optimiser rewarded for
large values walks straight into that regime.

The fix is to score by an **upper bound that never touches the grid**: sample a
candidate polyline densely, and if `|f| < 1` at every sample, its length bounds the
true geodesic. Chords and broken lines through the origin and through each
critical point are enough. Capping the grid value by the best such bound restores
soundness in the direction that matters — the reported number can only
overestimate the truth, so a value above 2 would mean something.

With the guard in place the reported leader at that configuration drops from
`2.0028` to `1.9980`, the grid overestimate being `0.0048`, and the validated
cases are unchanged (`z²−a²` at `a=1/2` still gives `0.997`, the cubic still
`1.784`).

**This is worth recording because the same trap is set for any search over this
problem.** A numerical counterexample to #1041 will appear first, and most often,
as a thin-corridor resolution failure near the boundary of the disk — exactly
where a real counterexample would also have to live.

## The constant 2 is sharp at every degree — with a proof

The degree-two case above is not special. The whole symmetric family is extremal,
and the reason is exact.

**Theorem.** Let `f(z) = zⁿ − rⁿ` with `0 < r < 1`. Every curve joining two
distinct roots inside `{|f| < 1}` has length at least

`2(r − (1−rⁿ)^{1/n})`.

Consequently the minimum such length tends to `2` as `r → 1⁻`, for **every**
degree `n ≥ 2`.

*Proof.* `{|f| < 1} = {z : zⁿ ∈ D(rⁿ, 1)}`. Put `ε = (1−rⁿ)^{1/n}`, so the disk
`B(0, 1−rⁿ)` has radius `1−rⁿ` and centre distance `rⁿ` from the centre of
`D(rⁿ,1)`. Since `rⁿ = 1 − (1−rⁿ)`, that disk is **internally tangent** to
`∂D(rⁿ,1)`. Hence `D(rⁿ,1) ∖ B(0,1−rⁿ)` is a crescent: simply connected, and
avoiding `0`. The preimage of a simply connected domain avoiding `0` under
`z ↦ zⁿ` splits into `n` disjoint components, one containing each root. So a path
that stays outside `|z| < ε` cannot join two distinct roots. Any path that does
join them therefore comes within `ε` of the origin, and must travel from a root
at distance `r` in and back out again: length `≥ 2(r − ε)`. ∎

Checked against the measured geodesics at `n = 3,4,5,6` and `r = 0.99, 0.999,
0.9999` — twelve cases, bound respected in all twelve, e.g. `n=3, r=0.9999`:
bound `1.86592`, measured `1.93925`.

**Corollary.** The constant `2` in Erdős #1041 is sharp, and the extremal
degeneration is the symmetric family `zⁿ − rⁿ` as `r → 1⁻`, at every degree — not
only at `n = 2`.

This is the mechanism behind it: `f' = n z^{n−1}`, so the **only** critical point
is the origin, with critical value `rⁿ → 1`. At `r = 1` the lemniscate splits into
`n` disjoint petals. The components therefore merge only at the origin, and every
path between distinct roots is squeezed through it as the pinch closes.

### The search finds the same family without being told

Maximising the guarded minimum pairwise geodesic over root configurations, from
seeded and random starts, at degrees 2 through 8:

| n | best guarded geodesic | min chord | root moduli |
|---|---|---|---|
| 2 | 1.998 | 1.998 | all 0.999 |
| 3 | 1.895 | 1.730 | all 0.999 |
| 4 | 1.734 | 1.413 | all 0.999 |
| 5 | 1.515 | 1.174 | all 0.999 |
| 6 | 1.353 | 0.999 | all 0.999 |
| 7 | 1.212 | 0.867 | all 0.999 |
| 8 | 1.104 | 0.765 | all 0.999 |

Every leader has all roots at exactly the modulus cap with
`min chord = 2r·sin(π/n)` — the optimiser converged on `zⁿ − rⁿ` at every degree
independently. Nothing exceeded 2; the best was `1.998`, the `n = 2` case where
the geodesic is exactly the root distance. The decrease with `n` at fixed `r` is
what the theorem predicts: `ε = (1−rⁿ)^{1/n}` grows with `n`, so a larger degree
needs `r` closer to `1` to approach the bound.

### What this settles for the programme

Three independent lines agree — a proof, a direct measurement, and a blind
search — so the packet's recurring "no uniform slack" findings now have a single
explanation rather than a family of separate obstructions. The bound is sharp,
the degeneration realising it is explicit and the same at every degree, and it is
governed by one fact: `zⁿ − rⁿ` has a single critical point whose critical value
rises to `1`.

Any proof of #1041 must therefore have zero slack in that one limit. What the
geodesic table earlier in this lab adds is that **away** from it the slack is
large, so the difficulty is concentrated entirely in this one-parameter family
rather than spread across the configurations the negative results use.

## A sharp conjecture that would prove the problem

The sharpness theorem does more than identify the extremal family: it says what
shape a proof has to have. Any true bound must be attained by `zⁿ − rⁿ` as
`r → 1⁻`, at every degree. That is a strong constraint, and exactly one simple
quantity meets it.

> **Conjecture (radius bound).** For monic `f` with all roots in the open unit
> disk, the minimum geodesic between two roots inside `{|f| < 1}` is at most
> `2·maxᵢ|zᵢ|`.

It implies Erdős #1041 immediately, since `maxᵢ|zᵢ| < 1`. And it is **tight**: on
`zⁿ − rⁿ` every root has modulus `r`, the two radii through the origin form an
interior path of length `2r`, and the theorem above shows nothing shorter
survives as `r → 1`. A conjecture that implies a sharp statement has to be tight
somewhere, and this is tight in precisely the right place.

Measured ratio `geodesic / (2·maxᵢ|zᵢ|)`:

| configuration | ratio |
|---|---|
| `z² − a²`, a = 0.9 | **1.00000** |
| `z² − a²`, a = 0.999 | 0.99955 |
| `z³ − r³`, r = 0.999 | 0.95193 |
| `z⁴ − r⁴`, r = 0.999 | 0.86525 |
| `z⁶ − r⁶`, r = 0.999 | 0.67578 |
| cubic that kills direct chords | 0.89832 |
| five-root that kills origin spokes | **0.02836** |

Nothing exceeds 1. The maximum seen is exactly `1.00000`, at the degree-two
equality case where the geodesic *is* the root distance, and a configuration
search driving the ratio upward got no further.

### Two sharper forms, and where the origin route really fails

The bound has a natural strengthening that also implies the problem:

> **Form A.** Some pair satisfies `geodesic(a,b) ≤ |z_a| + |z_b|` — the length of
> the broken line through the origin, without requiring that broken line to be the
> path taken.

Form A holds with real margin everywhere tested: slack `−0.201` on the cubic,
`−1.943` on the five-root configuration, `−0.241` on `z³ − r³` at `r = 0.9`,
`−0.647` on `z⁶ − r⁶` at `r = 0.999`. At `n = 2` the slack is **exactly
`0.00000`** — tight in precisely the place the radius bound is tight, where the
origin route and the chord coincide.

That exact zero took a correction, and it is the thin-corridor trap for the third
time. Comparing the *raw grid* geodesic against `|z_a| + |z_b|` reported Form A as
**failing** at `n = 2` for `a = 0.99` and `a = 0.999`, by `+0.0012` and `+0.0048`.
But there the geodesic *is* the chord, so the true slack is exactly zero and a few
thousandths of grid error flips an equality into a violation. Capping **each pair**
by its own exactly verified polyline before the comparison restores the zero. The
lesson generalises: wherever a conjecture is tight, an unguarded numerical test of
it will report failure.

The distinction that matters is with the literal origin route:

> **Form A′.** Some pair has *both* radial segments `[0,z_a]`, `[0,z_b]` interior.

Form A′ is **false** — that is exactly the packet's five-root negative result,
where four of the five spokes leave the lemniscate. So the gap between A and A′ is
the whole difficulty: the *length* `|z_a| + |z_b|` is affordable, but the straight
broken line realising it is not always available. A proof needs a path of that
length taking some other route, and the geodesic data says one exists with room to
spare whenever `n ≥ 3`.

That is a much more specific target than "find a construction", and it is the
first statement in this problem's file that is both sharp and not already refuted
by its own witnesses.

## Claim boundary

The theorem and its corollary are exact. Everything else is numerical: geodesics
on a grid, validated to about 0.3% against an exactly-known
case and stable across resolutions, and capped by exactly verified interior
polylines so that a reported value cannot exceed the truth through a resolution
failure. Values below 2 are witnesses that the
infimum is below 2 for those polynomials; nothing here is a proof, and #1041 is
open — and separately contested by a public manuscript claiming the full result,
whose status this lab does not assess.

## Replay

```sh
./repo-python formal_math/probes/erdos1041_geodesic.py --grid 1000
./repo-python formal_math/probes/erdos1041_geodesic_search.py --max-n 8 --restarts 6 --steps 40
./repo-python formal_math/probes/erdos1041_sharpness.py --degrees 2,3,4,5,6
./repo-python formal_math/probes/erdos1041_radius_bound.py --grid 800 --max-n 7
```
