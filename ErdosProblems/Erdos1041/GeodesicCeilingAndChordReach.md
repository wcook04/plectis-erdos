# Erdős 1041: the true geodesic, maximised over the whole configuration space

Status: two measurements that had not been made, one exact constant, and one
unconditional sufficient condition. 2026-08-24. **This does not prove Erdős
#1041.** It measures the statement itself rather than a mechanism, which
[TrueGeodesicLab.md](TrueGeodesicLab.md) is the only other file here to do — and
that file measures the geodesic only on **stored refuting witnesses**. Every
adversarial search in this directory maximises a *construction* (spokes, chords,
free hub, straight critical-hub paths). None maximises the quantity the problem
is about.

Scope: unlike the near-field notes, everything here is about honest polynomials
with all roots in the closed unit disk — no limit model.

## 1. The instrument, and its calibration against the existing one

Same method as `TrueGeodesicLab.md`: the lemniscate sits inside `|z| < 2`; grid
the box, keep cells with `|f| < 1`, build the 16-neighbour stencil (offsets with
`|dx|,|dy| <= 2` and `gcd = 1`), admit a move only when every sampled interior
point of the segment is also inside, then Dijkstra from each root. **A grid path
is a genuine path, so the measurement overestimates the true geodesic** — which
is the safe direction for an upper bound, and the reason the maximisation below
means something.

Independent implementation, checked against that lab's own numbers:

| configuration | measured here | `TrueGeodesicLab.md` |
|---|---|---|
| `z^2 - (1/2)^2`, exact answer `1.0` | `1.00200` (`G = 500`) | `0.9987`–`1.0026` |
| `z^3 - (99/100)^3` | `1.7755` | `1.782` |
| `z^2 - a^2`, `a = 0.9` | `1.8043` | `1.803` |
| `z^2 - a^2`, `a = 0.99` | `1.9761` | `1.977` |

Agreement to `0.4%`, on code sharing nothing with theirs.

## 2. The regular polygon is the maximiser (at a fixed radius cap)

Adversarial hill-climbing on the **true geodesic** — five restarts per degree
seeded from the regular polygon, from perturbed polygons and from random
configurations, roots capped at `|z| <= 0.99` so the origin passage stays
macroscopic (a single-point pinch is invisible to any grid, per
[LemniscateCapacityBudget.md](LemniscateCapacityBudget.md)):

| `n` | max geodesic found | maximiser | regular `n`-gon value | `2R` |
|---|---|---|---|---|
| 3 | `1.78267` | regular triangle | `1.78943` | `1.9800` |
| 4 | `1.50105` | **exactly** the regular square | `1.52058` | `1.9800` |
| 5 | `1.27083` | regular pentagon | `1.27334` | `1.9800` |
| 6 | `1.09938` | **exactly** the regular hexagon | `1.11790` | `1.9800` |

The cap matters and §3 says why; the point of the table is the ARGMAX, not the
value. The searcher cannot beat the regular polygon at any degree; at `n = 4` and `n = 6`
it returns to it exactly, to four decimals in every coordinate. So on the evidence
the regular `n`-gon is the **global** maximiser of the geodesic, not merely a
strict local one — `NearFeketeCuspLaw.md` §4 proves local maximality of
`min_c L(c)/(2R)`; this is the corresponding global statement for the geodesic,
measured.

## 3. The rate at which `2` is approached, and why it is a cube root

**First, a correction to the obvious reading of §2.** Those ceilings are at
`r <= 0.99`. The constant `2` *is* sharp at every degree — as `r -> 1` the
geodesic of `z^n - r^n` tends to `2r -> 2`, because the lemniscate degenerates:
at `r = 1` exactly, `{|z^n - 1| < 1}` is `n` petals meeting only at the excluded
point `0`, and no two roots can be joined at all. What §2 measures is not that
`2` is unreachable but **how slowly it is reached**, and that is worth a lemma.

> **Neck lemma.** For `f = z^n - r^n`, the open disk `|z| < rho` with
> `rho := (1 - r^n)^{1/n}` lies inside `{|f| < 1}`.

*Proof.* `|z^n - r^n| <= |z|^n + r^n < (1 - r^n) + r^n = 1`. ∎

So the passage at the origin is not a narrow neck at any resolvable radius:
`rho = 0.3096` at `n = 3`, `r = 0.99`, and still `0.2465` at `r = 0.995`. It
closes like `(n(1-r))^{1/n}` — a **cube root** at degree three — which is why the
approach to `2` is far slower than the mechanism value `2r` suggests, and why no
grid can see the limit.

The lemma also improves the extremal family's own ceiling. Going radially from a
root to the disk, straight across it (the disk is convex, so the segment between
the two points at radius `rho` in directions `0` and `2 pi/n` stays inside), and
out again:

> **Corollary.** `geodesic(z^n - r^n) <= 2r - 2 rho (1 - sin(pi/n))`.

At `n = 3`, `r = 0.99` that is `1.897`, against the recorded mechanism value
`2r = 1.980` and the measured geodesic `1.783`. The corollary is strictly below
`2r` for every `n >= 3` and every `r < 1`, so the two-radius broken line is never
the geodesic away from degree two.

### 3a. The ratio at fixed radius

The extremal family's recorded cheapest connection is `2r`, the two-radius broken
line through the origin. **That is a mechanism value, and the geodesic is
strictly shorter:**

| `n` | `r = 0.8` | `0.9` | `0.95` | `0.98` | `0.99` | `0.995` |
|---|---|---|---|---|---|---|
| 2 | `0.99687` | `0.99745` | `0.99769` | `1.00143` | `1.00288` | `0.99784` |
| 3 | `0.86117` | `0.86755` | `0.86584` | `0.88356` | `0.90046` | `0.91506` |
| 4 | `0.70120` | `0.70202` | `0.70539` | `0.73420` | `0.76293` | `0.79659` |
| 6 | `0.49582` | `0.49640` | `0.50239` | `0.53419` | `0.55697` | `0.59506` |

(entries are geodesic / `2r`; the `n = 2` row exceeding `1` at `r >= 0.98` is the
`0.3%` grid overestimate, since there the chord is interior and the geodesic is
exactly `2a`.)

Two readings.

* **At `n = 2` the ratio is `1` at every radius**: the chord is interior, the
  geodesic *equals* `2a`, and there is no slack at all. Degree two is the only
  place where the extremal mechanism and the geodesic coincide.
* **At `n >= 3` the ratio is well below `1` at every resolvable radius** —
  `0.92` at `n = 3`, `0.60` at `n = 6` — and climbs toward `1` only at the cube-root
  rate of §3. At `n = 3`, `r = 0.995` the geodesic is `1.821` against `2r = 1.990`.

So for `n >= 3` the difficulty of Erdős #1041 at any *fixed* radius is not the
length of the best path — there is `8%` slack at `n = 3` and `40%` at `n = 6`
against the mechanism value. The difficulty is exhibiting a path at all, and the
sharpness of `2` lives entirely in the `r -> 1` limit, where §3's `rho -> 0`.

## 4. How far the chord family alone reaches

For **any** pair of roots the chord has length `|a - b| <= 2R < 2`, so length is
free for every pair and only containment can fail. The whole chord family is
therefore governed by one number,

```text
Q(f) := min over pairs (a,b) of  max_{[a,b]} |f|,
```

and Erdős #1041 holds for `f` as soon as `Q(f) < 1`. `research_packet.json`
records that direct root chords fail; it does not record by how much. Maximising
`Q` adversarially:

| `n` | 3 | 4 | 5 | 6 | 7 | 8 | 10 |
|---|---|---|---|---|---|---|---|
| `sup Q` | **`1.125`** | `1.0298` | `1.0472` | `1.0291` | `1.0089` | `1.0000` | `1.0114` |
| regular gon | `1.125` | `1.0000` | `1.0113` | `1.0000` | `1.0017` | `1.0000` | `1.0000` |

**The chord family misses by at most `12.5%`, and by under `5%` from degree four
on.** At `n = 3` the supremum is exactly `9/8`, attained at the regular triangle:
for `z^3 - r^3` the adjacent-chord midpoint is `m = (r/2)e^{i pi/3}`, so
`|f(m)| = r^3(1 + cos^3(pi/3)) = (9/8) r^3` while `mu = r^3`. That is the
`r^3 > 8/9` threshold already recorded in
[FirstMergeReductionState.md](FirstMergeReductionState.md), here identified as the
global maximum of `Q` at degree three.

### 4a. An unconditional sufficient condition

Sharper, using the hub. Let `c*` be the critical point of least critical value
`mu = min_k |f(c_k)|` and let `a, b` be the two roots **nearest** `c*`. Then
`|a - b| <= d_1 + d_2 <= 2 mu^{1/n} < 2` — the budget theorem of
`CriticalTwoRootProximity.lean` — so that chord is short. And its height is
controlled by `mu`:

```text
C_n  :=  sup over configurations of   max_{[a,b]} |f| / mu.
```

> **Consequence.** If `mu < 1/C_n` then the nearest-pair chord at `c*` is
> contained and has length below `2`, so Erdős #1041 holds for `f` outright.

Measured, by adversarial search over the closed unit disk:

| `n` | 3 | 4 | 5 | 6 | 8 | 10 | 12 | 16 |
|---|---|---|---|---|---|---|---|---|
| `C_n` | **`1.125`** | `1.3087` | `1.5289` | `1.7119` | `1.9520` | `2.4687` | `2.9837` | `4.5333` |
| `mu <` | `0.8889` | `0.7641` | `0.6541` | `0.5841` | `0.5123` | `0.4051` | `0.3352` | `0.2206` |

`C_3 = 9/8` exactly, again at the regular triangle, so at degree three the
condition is `mu < 8/9` — and the extremal cubic has `mu = r^3`, giving
`r < 0.9615`. Above that radius the near-Fekete machinery is needed and below it
nothing is.

Sampling confirms the threshold shape directly: over 1500 configurations per
degree, the nearest-pair chord is contained in **100%** of cases with `mu < 0.6`
at every degree tested, and in **0%** of cases with `mu > 0.95`.

**The limitation is the degree.** `C_n` grows roughly like `n/4`, so the window
`mu < 1/C_n` closes like `4/n`. Since `mu <= D^{1/(n-1)}` with
`D = disc/n^n` ([HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md)),
`mu < 1/C_n` is implied by `D < C_n^{-(n-1)}`, which is a far stronger demand than
"`D` bounded away from `1`". So this is **not** the `D`-bounded-away-from-1 half;
it is an explicit unconditional slice of it, exact at `n = 3` and thinning with
degree.

## 5. Claim boundary

Proved: the length statements — `|a-b| <= 2R` for every pair, and
`|a-b| <= d_1 + d_2 <= 2 mu^{1/n}` for the nearest pair at `c*`, the latter being
`CriticalTwoRootProximity.lean`'s, not new here. The consequence in §4a is
elementary given `C_n`. The `n = 3` value `9/8` is exact arithmetic on
`z^3 - r^3`, and the identity `|f(m)| = r^n(1 + cos^n(pi/n))` at the
adjacent-chord midpoint is `FirstMergeReductionState.md`'s.

Measured, not proved: every table. `C_n` and `sup Q` are adversarial suprema, and
`research_packet.json::negative_results` entry 19 warns that such a supremum
pinned below a threshold is not proof the threshold is never crossed — the answer
here is that these suprema are **not** pinned below anything: they sit *above* `1`
and identify a named maximiser (the regular gon at `n = 3`, exactly `9/8`), which
is the calibration entry 19 asks for. The geodesic maximisation is capped at
`|z| <= 0.99` and degrees `3..6`, and the grid overestimates, so §2's ceilings
bound the true geodesic from above on the configurations visited and nowhere else.

Not established: that the regular `n`-gon is the global geodesic maximiser — §2
is a search, not a proof, and it is the natural conjecture to attack next. No
bound on `C_n` is proved for any `n >= 4`. Nothing here touches the near-field
model, the `O(rho^2)` remainder, or the two-segment mechanism.

**Erdős #1041 remains open.**

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/\
scripts/check_erdos1041_geodesic_ceiling.py
```
