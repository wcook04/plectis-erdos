# Erdős #1041: the tie race — why every fixed path family fails by a hair, measured

Status: one exact negative result (certified in rational arithmetic) and a set of
measured laws, 2026-09-05, conductor lab. Nothing here settles a regime of Erdős
#1041; the value of the note is that it pins, with numbers, the shape of the
obstruction that the surviving regime `2/5 < mu < 1` presents to every
fixed-path completion, and it records four natural statements that are false by
`10^-4` to `10^-3` precisely at near-ties. Read with
[HubTaylorSpokeCertificate.md](HubTaylorSpokeCertificate.md) (the exact quintic
that defeats the canonical hub set), [MiddleRegimeCanonicalHub.md](MiddleRegimeCanonicalHub.md)
(the `eta`-cap `1.21e-5` and the chord-minimum conjecture), and
[NearFeketeInnerModelWidening.md](NearFeketeInnerModelWidening.md) §5.4 (the
saddle-connection wall).

Notation: `mu = min_c |f(c)|` over critical points, `c*` a least critical point,
`nu_2 <= ... <= nu_max` the other critical-value moduli, `T*` the persistence
level of the two-root component of `{|f| < t}` containing `c*` (the first level at
which it acquires a third root), and for a hub `h` the *second spoke maximum*

```text
m2(h) = second smallest over roots a of  max_{s in [0,1]} |f(h + s(a - h))|.
```

`m2(h) < 1` with two spokes of total length `< 2` is the target.

## 1. Certified negative result

> **Theorem 1.** "At the least critical point the second spoke maximum is at most
> the largest critical value", i.e. `m2(c*) <= nu_max`, is FALSE. Witness: the
> monic octic with the Gaussian-rational roots stored in
> `scripts/check_erdos1041_tie_race_landscape.py`, all roots strictly inside the
> open unit disc. Every critical point is enclosed in a certified
> Kantorovich disc of radius `10^-6`, the discs are pairwise disjoint, the least
> critical point is separated from the others, `nu_max` is bounded above on the
> discs, and at least `n - 1` of the `n` straight spokes from `c*` carry a
> rational parameter `s` at which `|f| - 10^-6 sup|f'| > nu_max` for every `h`
> in the `c*` disc.

The excess is small: `m2(c*) - nu_max = +0.0026` at `mu = 0.7865` (certified
`nu_max <= 0.78904`, seven of eight spokes above it). A second floating witness,
a quintic with excess `+0.0007` at `mu = 0.838`, loses its excess under
five-decimal rationalisation and is not certified. The witness is a near-tied
near-regular configuration (all critical values within `0.3%` of one another)
with `c*` displaced from the centre of the cluster; the spoke from the displaced
saddle runs slightly off the petal axis and overshoots the level of the cluster.
On the same witness a free hub near the cluster reaches `min_h m2(h) = mu`
exactly (§2, L8), so the excess is a hub-placement effect, not a property of the
level sets.

## 2. Measured laws in the surviving regime (floating, falsification evidence)

All samples have every root in the open unit disc and `mu > 2/5`; families are
jittered regular polygons, translated central-root polygons
`z(z^{n-1} - r^{n-1})` and their translates, two-level walls
`(z^k - a^k)(z^k + b^k)`, and shell-random configurations.

**(L1) The canonical hub's margin is `1 - mu`.** Over 6000 samples per degree at
`n = 5, 6, 8, 10, 12`, binned by `mu`, the worst `m2(centroid)` is about
`mu + 0.02` in every bin: `[0.7,0.8) -> 0.82`, `[0.8,0.9) -> 0.90..0.92`,
`[0.9,0.95) -> 0.95`, `[0.95,0.99) -> 0.989`. The origin is within `0.01` of the
centroid. Below `mu ~ 0.5` the adjacent chord adds a second cover (worst
`min(m2(centroid), chord) = 0.55..0.60`). The spoke maximum sits at the hub end,
where `|f(h)| ~ mu`; on `(z - tau)^n - lambda` it is exactly `|f(tau)| = mu`
since `|f(tau + s(a - tau))| = mu (1 - s^n)` is decreasing.

**(L2) Fixed-hub failures live only in the shell.** Continuation of the exact
quintic of HubTaylorSpokeCertificate.md Theorem 4 downward in `mu`: at the
witness the failure objective is `1.000003` (margin `3e-6`, `mu = 0.999988`);
with `mu` capped at `0.9999` the failure is lost (`0.999925` after 4500 climb
steps); shell seeds at `n = 6, 7` climb only to `0.999997` and never fail. Random
climbs at `n = 5..8` with `mu <= 0.999` find no failure of the set
`{c*, admissible critical points, 0, centroid}` plus chords. MiddleRegimeCanonicalHub.md
turns the witness into the exact cap `1 - mu >= 1.21e-5` for any canonical-hub
theorem of the form `2/5 < mu <= 1 - eta`.

**(L3) Spoke maxima track the critical level.** Over 3500 survivors,
`m2(c*) / nu_max <= 1.0000` in bulk, `m2(c*) / nu_2 <= 1.011`; the adversarial
supremum of `m2(c*) - nu_max` is `+0.00008, +0.0010, +0.0015, +0.0026` at
`n = 4, 5, 6, 8` (`mu <= 0.95`), and Theorem 1 certifies the `n = 8` one.

**(L4) Over the hub cluster the race is exactly balanced.** Statement Q,
`min over admissible critical hubs c of m2(c) <= nu_max`, has no violation in a
census of 667 survivors at `n = 4, 5, 6, 8`; adversarial climbs reach
`sup (min_c m2(c) - nu_max) = +0.000000` (equality at ties, e.g. the near-square
at `mu = 0.775`); at the deep-shell quintic (`mu = 0.9999875`, `nu_max = 1.0000025`)
the gap is `+2.2e-7`, a violation, but there `nu_max > 1` and no hub is
admissible for the target anyway. So Q is an equality-at-ties statement whose
sign in the tie-splitting directions is what the shell decides.

**(L5) Conjecture P is false, and false in the middle regime.** P: the straight
spokes from `c*` to the two roots of its two-root component have `max |f| <= T*`
(the component is star-shaped from its saddle along the two root directions at
every level below attachment). With `T*` and the merging pair computed exactly
from the merge tree (steepest descent from `c_j +- delta u_j` identifies the two
lobes each critical point joins; union-find over critical points sorted by value),
the ratio `pair_max / T*` exceeds `1` at `n = 4` (`1.000005`, `mu = 0.532`),
`n = 5` (`1.000195`, `mu = 0.787`), `n = 6` (`1.000207`, `mu = 0.645`),
`n = 8` (`1.004089`, `mu = 0.308`) and at the three stored shell witnesses
(`1.00003..1.00007`). Every violation is a near-tied configuration with
`T*/mu - 1` between `10^-5` and `10^-3`. A first test with a `700 x 700` grid
flood fill reported `0/534` violations because it could not resolve the necks:
grid connectivity is not an instrument for near-ties.

**(L6) For cubics P is true with equality exactly on the tie line.** With
`c* = 0`, `f(0) = 1`, `f' = 3z(z - c_2)`, the spoke to a merging root `a` is
`g(s) = (1 - s)[1 + s + (1 - beta) s^2]` with `beta = (3/2) c_2 a^2` and
`T* = |1 - c_2^3/2|`; over 22695 admissible parameters the supremum of
`max_s |g(s)| / T*` is `1.000000`, attained only where `T* = 1 = mu`. This is the
only degree where P holds.

**(L7) The merging-pair length floor has room.** `(|a - c*| + |b - c*|)/(2 mu^{1/n})`
for the merging pair is at most `0.89, 0.82, 0.75, 0.66` at `n = 4, 5, 6, 8` in a
small census and climb, and the merging pair coincided with the nearest pair in
every sampled configuration (Claim L is known to fail only inside near-ties).

**(L8) The free hub reaches `mu` exactly.** On the eight maximisers of (L3) a grid
plus local search over hubs near the critical cluster finds
`min_h m2(h) = mu` to five digits in every case; the optimal hub lies inside one
lobe, on the line through the other root and `c*`, so that one spoke passes
through the saddle with value exactly `mu` and the other stays inside its lobe.
This is the two-segment path of `two_segment_containment_reduction` at level
`mu`, and it exists exactly when some spoke `[c*, a]` is sublevel-contained
(negative result 58's degree-seven witness has none, so the level must be raised
there; the level-one form `V_E <= 1` is the open statement).

## 3. What the numbers say about a completion

Four natural fixed statements — `m2(c*) <= nu_max`, P, the canonical hub set,
and the absolute-value spoke criterion — are each false by `10^-4..10^-3` at
near-ties and true with margin away from them. The regular polygon is an
equality case of every candidate inequality, and generic tie-splitting
perturbations break each fixed path family while some path survives (the
runner-up hub, the free hub, the other lobe). A completion therefore has to be a
selection principle that is automatically optimal at ties: a minimum over the
tied hub cluster (statement Q, exact balance), a continuously placed hub
(`V_E <= 1`, free-hub existence), or a hub-free statement whose margin does not
vanish at ties. The chord-minimum conjecture of MiddleRegimeCanonicalHub.md is
the first of the third kind: its margin `(1 - cos^n(pi/n)) mu` is `0.35 mu` at
`n = 5` and only tends to zero as `n -> infinity`.

## 4. Claim boundary

Theorem 1 is an exact rational certificate (Kantorovich critical discs, Taylor
bounds for the derivative on discs and along segments, integer square roots
rounded in the safe direction); the roots are stored as exact rationals and the
polynomial is rebuilt from them. Everything in §2 is measurement at finite
precision over finitely many configurations and carries no universal
quantifier; the adversarial suprema are basin records in the sense of negative
result 28. No Lean module exists. Erdős #1041 remains open.

## 5. Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_tie_race_landscape.py
```

One JSON line: `status`, `evidence_class`, and per witness the `mu` bounds,
`nu_max` upper bound, the disc radius, and the rational spoke parameters with
their certified lower bounds on `|f|`. The measurement scripts of §2 are session
scratch and are described by their method here, not shipped.
