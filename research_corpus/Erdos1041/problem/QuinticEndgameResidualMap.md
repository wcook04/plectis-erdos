# Erdős 1041: the degree-5 ENDGAME MAP — no counterexample to `min_c L < 2` (adversarial max `1.98529`), the row is EXACTLY tight at the regular pentagon, and the residual is a `|c|`-cusp in the perturbation DIRECTION

Date: 2026-08-30.  Origin: two wave-1 opus campaigns — the endgame agent
(8,722 configurations, adaptive DP45 + independent uniform-RK4 +
inscribed-polyline floors, every corpus anchor reproduced to stated
digits) and the geodesic agent (36 pocket configurations, grid geodesics
+ rigorous neck-cut lower bounds + variational polish) — plus main-loop
replay of the decisive specimens.  Checker:
`scripts/check_erdos1041_endgame_residual_map.py`.  COMPUTATIONAL LAW
note (measured geography; exact rows marked); consumes FRONTIER §§2,
4.4, 5, `MinimalHubArmBudgetRefutation.md`,
`TwoTierStraightStarSelectorLab.md`, `QuinticModelRealTransferLaw.md`.

## 1. Headline: the adversarial maximum and its meaning

Objects: monic quintic, roots in the closed unit disk (MEC-normalised),
`L(c)` the two-arm descent length through critical hub `c` (Newton-flow
lifts of the value segment `[f(c), 0]`), hubs admissible iff
`|f(c)| <= 1` and the segment is clear; the parent-deciding row is
`min_c L(c) < 2` over admissible hubs (FRONTIER §2 wiring).

- **Global adversarial maximum found: `min_c L = 1.985293810`**, margin
  `1.4706e-2`, at a near-gon shell configuration with all four
  `|f(c_k)|` tied at `0.999763408..` (5e-9 tie — the psh tie-locus
  maximum principle reproduced independently), `1-D = 9.4603e-4`,
  `value_gap = 1.0e-9`.  Witness roots (checker E2 replays the
  tie/admissibility/landing structure and bands the value; the final
  `3e-3` of precision is deliberately NOT checker-replayed — at
  `value_gap = 1e-9` checker-grade instruments provably mis-resolve the
  saddle detour, which is §4's law; the certified value rests on the
  campaign's three instruments, spread `<= 1e-5`):
  `+0.9979375665306239+0.0641920034500927i`,
  `+0.2472702143511880+0.9687942950447733i`,
  `-0.8451514944420297+0.5345268481960510i`,
  `-0.7696408194933532-0.6384771013666819i`,
  `+0.3694458748452705-0.9291564011124239i`.
- Every reading above `1.99` in the whole campaign was an instrument
  artifact (§4).  Quantiles of `min_c L`: random closed-disk 3000:
  median `0.368`, q99 `0.891`, max `1.1021`; near-gon 3000
  (`eta in [1e-3, 0.1]`): median `1.732`, q99 `1.875`, max `1.9181`.
  Admissible hubs never numbered zero.

**Exact fact (checker E1): at the regular pentagon `f = z^5 - 1` the
minimal hub is the 4-fold critical point at `0`, each descent arm is a
straight unit radius, and `min_c L = 2` EXACTLY.**  The row is tight at
the on-circle gon (excluded from the open disk, but its limit point):
the entire degree-5 endgame is the approach to that single degenerate
configuration.

## 2. The residual is a `|c|`-cusp; direction, not depth, is adversarial

Over 3,433 resolvable near-gon configurations:

```text
2 - min_c L  ~  kappa * max_k |c_k|,
log-log slope 1.0022, corr 0.99942;
kappa in [1.057, 1.420] (median 1.305) on random shell directions,
kappa = 0.7512 at the adversarial optimum.
```

`|c|` (the critical-splitting scale) is the coercivity invariant — the
SAME invariant `TraceMaxRadialExcessLaw.md` identified for the model
excess, and its measured band matches the real-hub coercivity
`[1.117, 1.384]` of `QuinticModelRealTransferLaw.md` §3 up to the
normalization slack `2 - rho_i - rho_j >= 0`.  Against `1-D` and
`d_gon` the exponent is `1/4` (via `|c| ~ eta^{1/4}` splitting), and
those coordinates predict far worse (`corr 0.969`).  Depth is NOT the
adversarial variable: the global optimum sits at `1-D = 9.5e-4`, four
decades shallower than the deepest sampled shell configs, and random
directions at `eta = 0.1` give `min_c L ~ 1.43` vs `1.97` for the
optimised direction.  Thinness of the residual in invariant
coordinates:

```text
min_c L > 1.9   ==>  |c*| <~ 0.079,  1-D <~ 2.9e-3,  d_gon <~ 4.8e-4
min_c L > 1.95  ==>  |c*| <~ 0.040,  1-D <~ 3.7e-4,  d_gon <~ 5.7e-5.
```

Coverage: of the top-200 near-extremal configs, **0% are covered by any
CLOSING family** (deep-low, MTD4, collinear, concyclic-small, exact-gon
slice — they are concyclic to 1e-7 but at radius 1.0000, outside the
`2^{-1/5}` hypothesis), while **100% satisfy the near-Fekete REDUCTION
hypotheses** — the residual is purely angular, i.e. exactly the
star-kernel program's territory.  Pool-wide any-closing coverage:
65.6%.

**Why the row survives (mechanism).**  Hadamard forces
`prod_k |f(c_k)| = |disc f|/5^5 <= 1` (checker E5), so at least one hub
always sits under the admissibility wall; measured, it is always a
low-`L` one.  At the SPOKE-5 pocket corner a hub with `L = 2.0440`
exists but is excluded by `|f(c)| = 1.0000512`; the admissible hubs
stay at `L <= 1.83`.  The tension between the wall and the arm budget,
not smallness of `L` per se, carries the row.

## 3. Connector slack: the free-hub-in-the-neck family (geodesic agent)

Against true shortest paths in `{|f| < 1}` (36 pocket configs, rigorous
neck-cut lower bounds; anchors matched to the labs to 4+ digits):

- In the MARGIN metric, the true geodesic roughly DOUBLES the budget:
  `(2 - l_geo)/(2 - min_c L) in [1.40, 1.87]` (median `1.67`) across
  the whole pocket.  Pocket laws (n = 27): `2 - l_geo ~ 1.62 (1-t*)^{0.193}`,
  `2 - L ~ 1.02 (1-t*)^{0.197}` — both the natural fifth-root exponent.
- Same throat 36/36 (the geodesic never routes around another saddle;
  the `min_c L` hub IS the first-merge saddle every time), but the
  geodesic hugs the OUTER wall (`max |f| = 1.0` to 10 digits on 30/36),
  not the critical level.
- **The slack lives in the hub's POSITION IN THE THROAT**: slack
  decomposition — arm curvature 22%, sliding the hub to the best neck
  point 107%, bending back −30%.  In 27/27 pocket configs the optimal
  neck point sits at `|p| = 1.19–1.93 x |c|` — strictly OUTSIDE the
  saddle radius, 8–28 deg off-radial.  The corpus's slid-hub family
  `t c, t in (0,1]` slides the WRONG WAY.  A TWO-PARAMETER
  free-hub-in-the-neck straight family (`t > 1` plus one transverse
  offset) captures essentially all recoverable gain: within a median
  `2.1%` of the true geodesic, `1e-5` at the deepest corner (checker E7
  demonstrates the outward-slide gain on a specimen).  A smarter CURVED
  family is not worth inventing; this one is still a finite algebraic
  test.
- Slack vanishes slightly faster than the margin
  (`L - l ~ 0.54 (2-L)^{0.91}`), so no connector rescues a
  configuration whose arms already sit at 2 — consistent with the gon
  exactness of §1.

## 4. Instrument laws (add to the FRONTIER §4.6 family)

1. `value_gap ~ 10^{-0.46} |c*|^{4.71}` (corr 0.963) near the gon, so
   `min_c L > 1.99` lives at `value_gap ~ 5e-11` and `> 1.999` at
   `~1e-15`: **the last `0.015` of the row is below the float64 floor —
   it requires quad precision or an exact certificate, not a bigger
   search.**  Two independent float64 instruments diverge below
   `value_gap ~ 1e-9`.
2. Uniform-grid marching needs step count `~ 8/sqrt(value_gap)`
   (calibrated on the Addendum-2 witness); below that the two arms land
   on the SAME root and the polyline length explodes (a DE run reported
   `min_c L = 3.09` that converges to `1.98877`).  Any adversarial
   search must gate on `value_gap` or it optimises the instrument
   (checker E6 demonstrates the trap and the guard).
3. Grid-based first-merge levels fail near the gon (`t*` within
   `sqrt(eps)`-wide necks; one run reported `t* > 1`): use a grid-free
   merge tree from the descent arms.  float32 storage of `|f|` destroys
   level connectivity within `~6e-8` of level 1.
4. Cluster charts in coefficient form are a precision trap
   (`|f| ~ eps^4` under Horner noise reports "no admissible hub");
   root-product evaluation fixes it (58/60 false vs 0/60).

## 5. What this fixes for the parent program

1. The degree-5 parent theorem is now a LOCAL statement at the gon plus
   a measured-fat middle: prove
   `min_c L <= 2 - kappa_0 max_k|c_k| + O(|c|^2)` uniformly over
   perturbation directions (measured `kappa_0 >= ~0.75`; the star-kernel
   route supplies exactly this — (EX-U) is the model-level
   direction-uniform statement, the real-hub transfer law carries it to
   real scale), with the `O(|c|^2)` explicit so a ball
   `max|c_k| <= sigma_0` closes; then the remainder
   `{d_gon >= delta_0}` has measured `min_c L <= 1.92` with 65.6%
   already family-covered — a bounded certification/coverage problem,
   not an open-ended search.
2. The free-hub-in-the-neck family (§3) is the right finite-certificate
   object for the pocket if extra margin is ever needed: it doubles the
   measured budget at every depth.
3. Any future adversarial claim on this functional that does not gate
   on `value_gap` and dual instruments is void (§4).

## Claim boundary

Measured law throughout except: the gon exactness (E1, exact), the
witness replays (E2–E3), the Hadamard pigeonhole (E5, via the corpus's
fibre-product identity), and the demonstrated instrument trap/guard
(E6).  "No counterexample found" is evidence for, not proof of,
`min_c L < 2`; the `kappa` band, thinness thresholds, coverage
fractions, and geodesic ratios are instrument-strength measurements.
Nothing here proves the parent at degree 5; it fixes the residual's
exact shape, the tight point, the coercivity coordinate, and the two
instrument classes any closing computation must respect.
