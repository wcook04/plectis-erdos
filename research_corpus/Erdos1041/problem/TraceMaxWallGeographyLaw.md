# Erdős 1041: the chamber wall geography LAW — annular projection, wall sup at the `mu = -10` corner, `|mu+10|` is the margin coordinate, the tangent orbit is a conical vertex and only a local ridge

Date: 2026-08-30.  Origin: wave-1 opus fleet (wall-geography agent: 2,762
in-chamber `mu`, 5,524 wall samples, 567 refined corner points, support
function in 720 directions; real-slice profiler agent: 6,183 real-slice
plus 3,850 complex-`mu` evaluations; independent engines agreeing to
`1e-13`, mpmath 30-dps spot checks), plus main-loop exact derivations
replayed in the checker.  Checker:
`scripts/check_erdos1041_wall_geography_law.py`.  This is a COMPUTATIONAL
LAW note in the sense of `TraceMaxRadialExcessLaw.md`, downstream of the
proved reduction in `QuinticChamberWallReduction.md`: measured geography
for the (EX-W) certification program, not a theorem, except the rows
marked exact/symbolic (checker-replayed).

## 1. The chamber `mu`-projection is an ANNULUS (exact-shape headline)

`{mu : A(mu) != emptyset}` is one connected region with ONE HOLE:

- Outer boundary: closed curve of length `~1441.2`, real crossings
  exactly `alpha_1 = -197.4409737432` and `alpha_3 = 5.2478789224`;
  support function maximal at `theta = 180 deg` with
  `rho = 197.440973743215` — the conjectured sharp bound
  `sup |mu| = |alpha_1|` CONFIRMED to `1.5e-12` (the crude proved bound
  is `67500`).  20-point polyline (agent data, `Re, Im`):
  `(-197.40,-3.80) (-184.34,66.60) (-144.13,125.80) (-83.20,163.25)
  (-12.20,171.07) (54.60,145.92) (100.30,91.47) (108.70,21.00)
  (70.40,38.09) (2.30,42.83) (4.38,3.60) (-3.72,-38.40) (64.00,-41.94)
  (106.95,-13.80) (103.20,-84.46) (60.61,-141.50) (-4.80,-170.00)
  (-76.10,-165.53) (-138.60,-130.88) (-181.34,-73.50)`.
- Inner boundary (the hole): lens-shaped closed curve of length `~17.6`,
  `Re in [-9.95, -2.844]`, `|Im| <= 1.154`; its real trace is EXACTLY
  the (R1) real gap `(-10, alpha_2)`.  12-point polyline:
  `(-9.90,-0.05) (-9.20,0.32) (-7.50,0.84) (-5.70,1.12) (-4.90,1.15)
  (-4.00,1.11) (-3.10,0.95) (-3.84,0.00) (-3.10,-0.95) (-4.80,-1.15)
  (-6.60,-1.01) (-8.30,-0.62)`.
- The corner locus (allowed arc collapsed to a point; two gap conditions
  tight) is EXACTLY the projection boundary: `arclen(mu) = G_max - pi`
  is continuous, positive inside, negative outside.
- Area `~76,757`; mean allowed arc `0.1125`; max arc `3.083` near
  `mu ~ -2.0 + 0.1i`.

## 2. Wall sup and the margin law (the certification-shaping rows)

Over 5,524 wall samples plus adversarial maximisation:

```text
sup_wall mathcal E = the mu -> -10 corner limit = -0.0602107442
```

(adversarial drive pins the sampling guard `|mu+10| = 0.2` at
`-0.0644766`, mpmath-confirmed; the limit value is the one the landed
endpoint certificates bound: `mathcal E(-10, +-arctan(1/(2 sqrt2)))
< -1/80` exactly, `QuinticMinusTenEndpointExcessCertificate.md`).  Max
wall `mathcal E` is MONOTONE in `|mu+10|`:

```text
|mu+10| in [0.2,0.5): -0.0665   [0.5,1): -0.0736   [1,2):  -0.0908
          [2,5):      -0.1038   [5,10): -0.1465   [10,20): -0.1772
          [20,40):    -0.2123   [40,80): -0.2380  [160,400): -0.2379
```

Binned instead by distance to the tangent orbit the law is FLAT
(`-0.170..-0.194` out to distance 80): **`|mu+10|` is the margin
coordinate; the tangent orbit is not.**  Wall quantiles: `q50 -0.2718`,
`q90 -0.2264`, `q99 -0.1698`, `q99.9 -0.0739`; the distribution is
bimodal (bulk `~-0.27`, a `~15%` mode at `-1.2..-1.38` — the two
arm-pair branches).  The `phi`-max of `mathcal E` sat at an arc ENDPOINT
in 25/25 full-arc scans (and in 663/687 real-slice rows, the exceptions
below resolution) — the measured `phi`-half of the wall reduction, with
mechanism: `mathcal E(mu, .)` is even about the arc centre and convex in
`phi` on every tested arc.  Zero same-tract arm pairs in all `~6,100`
wall/corner/approach evaluations.

## 3. The `mu = -10` corner: exact cubic gap-zero and the propeller

Exact (checker-replayed): at `mu = -10` the nonzero critical gaps are
`12 +- 24 i sqrt2` (so the allowed arc is `|tan phi| <= 1/(2 sqrt2)`,
width `2 phi_0 = 0.6796738`), and the vanishing gap has the EXACT cubic
leading term

```text
x_0(mu) = -(mu+10)/15 - 2(mu+10)^2/675 + O((mu+10)^3),
2mu + 20 - 3 mu x_0 = (mu+10)^2/9 + O((mu+10)^3),
g_3(mu) = -(mu+10)^3/675 + O((mu+10)^4).
```

(The `a_2` correction matters: dropping it gives the wrong constants
`(mu+10)^2/5` and `-1/375`; the checker replays the correct series
symbolically.)

The argument of `g_3` winds THREE times per loop around `-10`, so the
chamber near `-10` is a 3-fold propeller (three excluded sectors) with
in-chamber fraction EXACTLY `1/2 + phi_0/pi = 0.6081748...` (measured
`0.608175`), and `mathcal E` is genuinely DISCONTINUOUS at `-10` with at
least two limit branches: `-0.0602/-0.0688` (the certificate branch,
arms in tracts 4,1; approaches `theta = 120..180 deg`) and
`-0.921/-1.133` (tracts 0,1; approaches `theta = 0..90 deg`).  The
corner is approached linearly along the wall (slope `~0.0288` in
`|mu+10|` on the real side), and the real axis is a KINK of the 2D wall,
not a smooth maximum (off-axis wall values on `|mu+10| = rho` circles
exceed the real-slice values by `O(rho)` toward `arg(mu+10) ~ 157.5
deg`, still below the corner limit).

## 4. The tangent orbit demoted; `mu*` and collision points benign

- `mathcal E(50+30 sqrt3, -pi/2) = -0.1694610452` (two agents, three
  engines, `1e-13` internal agreement) — a LOCAL ridge of the wall
  (neighbourhood wall max `-0.1696`), NOT the sup.  In `C` the tangent
  point is a CONICAL VERTEX of the outer corner curve: on circles of
  radius `r = 1e-5 .. 1` the in-chamber fraction is constant `0.267725`
  (two mirror wedges `90 +- 24.095 deg`, total `96.379 deg`; max arc
  `~1.73e-3 r`).  It is isolated only inside the REAL slice —
  `QuinticTraceMaxUniversalChamber.md` (R1) remains correct as a
  real-slice statement.  Reminder from `QuinticChamberWallReduction.md`
  §6: the measured `-0.0363` extremal of `TraceMaxRadialExcessLaw.md` is
  the `|c| mathcal E` core normalization; the two normalizations have
  different extremals.
- At `mu* = (-70 +- 10 i sqrt5)/27` (the other gap-zero points) the two
  SURVIVING gap conditions coincide — their ratio is exactly `2 + sqrt3`
  (checker-replayed numerically to `1e-9`) — so the allowed arc is a
  full half-circle (length exactly `pi`); `mathcal E` near `mu*` lies in
  `[-1.357, -1.025]`.  At the foreign-collision points
  `(-50 +- 10 i sqrt2)/27` (`disc C_mu = 0`): arc `2.8018`, `mathcal E`
  near them `<= -1.121`.  Both families are interior to the projection
  and deep in the safe zone, as `QuinticChamberWallReduction.md` §5
  requires.
- Exact algebra bank (checker-replayed): `Res_x(C_mu, x(2mu+20-3mu x))
  = -4 (mu+10)^3 (27 mu^2+140 mu+200)`; `disc(gap cubic) =
  -16 (mu^2-100mu-200)^2 (27mu^2+100mu+100)^3 / 9765625`; `F == -g mod
  C_mu` with ratio exactly `-1`; and the alternative normalizer form
  `F = y^5 + mu y^2 - (2mu+5) y + (mu+4)`, `y = 1+x`.

## 5. What this fixes for the (EX-W) certification program

1. The tight zone is ONLY the punctured disk `0 < |mu+10| <= ~1`
   (wall values `<= -0.066` outside it, monotone margin law): a coarse
   cover suffices on `>= 99%` of the annulus by area.
2. The corner itself is pinned by the exact endpoint certificates; what
   remains analytic there is a 1-jet/monotonicity certificate along the
   wall into the corner (measured linear approach, slope `~0.029`), plus
   the `mu = -10` ARC INTERIOR (1D; measured range `-0.0688..-0.0602`),
   owned by the minus-ten certificate family.
3. Wall parametrization for the engine: the wall is two endpoint sheets
   over the annulus, glued along the two corner curves of §1; on the
   real slice branch 1 the wall values are convex in `mu` with argmax at
   the `-10` end.
4. Individual arms can carry positive excess (`e_- = +0.6563` at the
   tangent, `+0.0758` at the `-10` wall): certification must bound the
   PAIR, never per-arm.

## Claim boundary

Measured law except the rows marked exact/symbolic (gaps at `-10`, the
cubic `-(mu+10)^3/375` leading term, the propeller fraction
`1/2 + phi_0/pi`, the resultant/discriminant identities, the `mu*` ratio
`2+sqrt3` at numeric precision, the normalizer variant), which the
checker replays.  The annulus shape, polylines, sup location, margin
law, vertex angle `96.379 deg`, and branch values are agent measurements
with stated cross-instrument agreement; none of this proves (EX-W), the
arc interior, (EX-U), or the parent.  Consumes and does not modify
`QuinticChamberWallReduction.md` (the proved reduction),
`QuinticMinusTenEndpointExcessCertificate.md` (the corner certificates),
and `QuinticTraceMaxUniversalChamber.md` (the chamber algebra).
