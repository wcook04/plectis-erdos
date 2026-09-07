# Erdős 1041: the angular-selector toolkit — sector–ellipse metric, the critical-value trace selector, safe canonical arms, the quintic spine classification, and exact origin-ray criteria

Date: 2026-08-29.  Origin: operator-supplied Type B mathematics (this session's
solve thread), every proof re-derived and verified in the main loop before
landing; nothing here is imported on trust.  Checker:
`scripts/check_erdos1041_angular_selector_toolkit.py`.

All results are POSITIVE infrastructure for the open near-Fekete containment
selector (R1) (`NearFeketeRadialAngularSplit.md`) and for (SPOKE-5)
(`Degree5AssemblyAndSharpenedCuts.md`).  Nothing here refutes anything, and
nothing here claims the parent theorem; the claim boundary is at the end.

Setting for §§2–5: the self-inversive angular blow-up of the on-circle
near-gon (radial deficits are already discharged by
`NearFeketeRadialAngularSplit.md` Theorems 3/3a):

```text
P(w) = w^n + sum_{r=1}^{floor(n/2)} b_r w^r,
```

first-order safe set `{Re P >= 0}`, the `n` roots out along the tract
directions `u_k = e^{2 pi i k/n}`.  At `n = 5`: `P = w^5 + b_2 w^2 + b_1 w`.

## 1. Theorem A (sector–ellipse hub metric; exact, all hubs)

Let `n >= 3`, let `u_1, ..., u_n` be the vertices of a regular `n`-gon on the
unit circle, and let `c` be ANY point of the closed unit disk.  Let
`u_j, u_{j+1}` be the two vertices adjacent to the closed angular sector
containing `c` (bracketing `c`).  Then

```text
|c - u_j| + |c - u_{j+1}|  <=  2,
```

i.e. `c` lies in the closed ellipse with foci `u_j, u_{j+1}` and major axis 2.
Quantitatively, with `r = |c|`:

```text
|c - u_j| + |c - u_{j+1}|  <=  2 - 2 r cos^2(pi/n) + r^2,
```

so the slack is at least `r cos^2(pi/n) >= r/4` whenever `r <= cos^2(pi/n)`.
Stability: if instead `|a_j - u_j| <= eps` and `|a_{j+1} - u_{j+1}| <= eps`,
then `|c - a_j| + |c - a_{j+1}| <= 2 - 2 r cos^2(pi/n) + r^2 + 2 eps`.

Proof.  Rotate so `u_j = e^{-i alpha}`, `u_{j+1} = e^{i alpha}`,
`alpha = pi/n`, and write `c = r e^{i theta}`, `|theta| <= alpha`, `r <= 1`.
The ellipse with foci `e^{+-i alpha}` and focal-distance sum 2 has centre
`(A, 0)`, `A = cos alpha`, vertical semi-major axis 1 and horizontal
semi-minor axis `A`; membership is `Phi <= 1` with
`Phi = (x - A)^2/A^2 + y^2` at `c = x + i y`.  Along the ray of fixed
`theta`, `Phi(r) = (r cos theta - A)^2/A^2 + r^2 sin^2 theta` is a convex
quadratic in `r`, so it suffices to check `r = 0` and `r = 1`.  At `r = 0`:
`Phi = 1`.  At `r = 1`, with `x = cos theta in [A, 1]`: `Phi <= 1` is
equivalent to `(x - A)^2 <= A^2 x^2`, i.e. to
`(x(1-A) - A)(x(1+A) - A) <= 0`; the second factor is `>= A^2 > 0`, and the
first is `<= 0` because `x <= 1 <= A/(1-A)` (using `A = cos(pi/n) >= 1/2` for
`n >= 3`).  Convexity finishes the membership claim.  For the quantitative
form use `sqrt(1 + x) <= 1 + x/2`:
`|u - c| <= 1 - Re(conj(u) c) + r^2/2` for unimodular `u`; summing over the
pair, `u_j + u_{j+1} = 2 cos(pi/n) v` with `v` the unit sector-midpoint
direction, and the angle between `v` and `c` is at most `pi/n`, so
`Re(conj(u_j + u_{j+1}) c) >= 2 r cos^2(pi/n)`.  The stability form is the
triangle inequality.  QED

Equality discussion: `Phi(0) = 1` (the origin lies ON the ellipse: the sum is
exactly 2 there), and for `n = 3` also the far vertex `x = 1, theta = 0`
gives sum exactly 2; for every other `c` in the closed disk the inequality is
strict.

Consequence.  This upgrades the first-order metric discharge recorded in
`NearFeketeRadialAngularSplit.md` ("the length constraint reads
`Re(c conj(a_i + a_j)) >= |c|^2 + O(|c|^3)`") to an EXACT global inequality:
at exact gon vertices, EVERY hub in the closed unit disk is metrically
admissible for its bracketing adjacent pair, with explicit linear-in-`r`
slack; near-gon roots cost only `+2 eps`.  In particular hub-based finite
certificates for (R1)/(SPOKE-5) never need a smallness assumption on the hub
to satisfy the length budget with an adjacent pair.

## 2. Theorem B (critical-value trace identity) and the selector corollary

Let `P(z) = z^n + sum_{r=1}^{floor(n/2)} b_r z^r` (no constraint on the
`b_r`), and let `c_1, ..., c_{n-1}` be the critical points of `P` with
multiplicity.  Then

```text
sum_{nu} P(c_nu) = 0                     (n odd),
sum_{nu} P(c_nu) = -(n/8) b_{n/2}^2      (n even).
```

Proof.  Write `Q = P'/n = z^{n-1} + sum_r (r/n) b_r z^{r-1}` and
`s_m = sum_nu c_nu^m`.  For `n = 2d+1`: the coefficients of `z^{n-2}, ...,
z^{d}` in `Q` all vanish (the perturbation only occupies degrees `<= d - 1`),
so Newton's identities give `s_1 = ... = s_d = 0`.  At a critical point,
multiplying `P'(c) = 0` by `c/n` gives `c^n = -(1/n) sum_r r b_r c^r`, hence
`P(c) = sum_r (1 - r/n) b_r c^r`, and summing kills every term since
`r <= d`.  For `n = 2d`: the same argument gives `s_1 = ... = s_{d-1} = 0`,
while the coefficient of `z^{d-1}` in `Q` is `b_d/2`, so Newton's `d`-th
identity gives `s_d = -d b_d/2`; in `sum_nu P(c_nu) = sum_r (1 - r/n) b_r
s_r` only `r = d` survives, with value `(1/2) b_d (-d b_d/2) = -(n/8)
b_{n/2}^2`.  QED

For the self-inversive blow-up, `b_{n/2}` is purely imaginary, so
`b_{n/2}^2 <= 0` and

```text
sum_nu Re P(c_nu) = 0    (n odd),        sum_nu Re P(c_nu) = (n/8) |b_{n/2}|^2 >= 0    (n even).
```

Corollary B1 (the trace selector).  Every blow-up model has a critical point
with `Re P(c) >= 0`; and EITHER some critical point has `Re P(c) > 0`
STRICTLY — an admissible model hub with first-order margin, transferring to
an actual critical point `c_f` of `f` with `|f(c_f)| < 1` strictly — OR every
critical value of `P` is purely imaginary (`n` odd) / the model is in the
even-`n` tangent set.  The strict case is generic; the exceptional set is the
TANGENT STRATUM, classified at `n = 5` by Theorem D below.

(Machine verification: identity holds to `1e-14` over random models,
`n = 4..9`; see checker.)

## 3. Theorem C (safe canonical arms at a strictly positive hub)

Let `P` be as above, let `c` be a SIMPLE critical point with
`Re P(c) > 0`.  Choose any direction `phi` with `|phi| < pi/2 -
arg-distance` such that the open ray `{P(c) + t e^{i phi} : t > 0}` avoids
the (finitely many) other critical values and stays in `{Re w > 0}`; every
sufficiently small generic `phi` works, and `phi = 0` works whenever the
positive real ray from `P(c)` is critical-value-free.  Then:

1. the fibre continuation of the two local preimage branches of the ray at
   `c` yields two disjoint smooth curves `gamma_+, gamma_-` from `c` to
   infinity;
2. both curves lie entirely in `{Re P > 0}`;
3. `gamma_+` and `gamma_-` tend to infinity in two DISTINCT tracts of the
   `n` asymptotic sectors of `{Re P > 0}` (the sectors around the root
   directions `u_k`).

Hence every NON-TANGENT model possesses a canonical safe connector

```text
tract_i  <- gamma_+ -  c  - gamma_- ->  tract_j     (i != j),
```

running entirely through the strictly safe region; only its LENGTH is not
controlled by this theorem.

Proof.  (1)–(2): along the ray the value is `P(c) + t e^{i phi}` whose real
part is `Re P(c) + t cos phi > 0`; since the ray contains no critical value
for `t > 0` and `c` is a simple critical point (local degree 2, two branch
preimages), each branch continues without obstruction (the continuation can
only fail at a critical point, whose value would lie on the ray) and `|z| ->
infinity` as `t -> infinity` because `|P| -> infinity` forces it; the branches
are disjoint since the fibre over each ray point is finite and the two
branches are distinct germs which can only meet at a critical point of `P`,
excluded on the open ray.  (3): for `t` large the fibre of `P` over
`P(c) + t e^{i phi}` has exactly one point in each of the `n` sectors
(`z ~ w^{1/n} u_k`); two branches ending in the same tract would give two
fibre points in one sector for arbitrarily large `t`, impossible.  QED

Structural supplement (proved): each connected component `V` of
`{Re P > 0}` is unbounded and simply connected (a bounded component or a
bounded complementary hole would force the harmonic function `Re P` to vanish
identically); `P: V -> {Re w > 0}` is proper of degree `d(V) =` the number of
tracts of `V`; `d(V) - 1` equals the number of critical points of `P` in `V`
(Riemann–Hurwitz), so a component containing a strictly positive critical
point reaches at least two tracts; and the tract sets of distinct components
never interlace cyclically (Jordan separation through a path in one component
plus the point at infinity).  NOTE the honest boundary: non-interlacing does
NOT by itself force some component to contain two cyclically ADJACENT tracts
(a degree-2 component with tract set `{k, k+2}` plus singleton components in
the gaps is combinatorially consistent); in every sampled model the positive
component of the best hub did reach two adjacent tracts (checker, flood-fill,
60/60), but adjacency is NOT claimed as proved.  Theorem C deliberately needs
only DISTINCT tracts.

SUPERSEDED IN STRENGTH (same session): `QuinticStarKernelMechanics.md` §1
proves the sharp form — at the TRACE-MAXIMAL critical point the value ray is
automatically critical-value-free (no generic direction needed), the
connector exists at the optimal level `D = max Re H(c)` INCLUDING the
tangent case `D = 0`, no connector exists above level `D`, the result holds
at every degree on the blow-up mode range, and the exact component census
(§2 there) replaces the structural supplement above.

## 4. Theorem D (the quintic tangent stratum is the rotated real spine)

Let `P(w) = w^5 + b w^2 + a w` (`a = b_1`, `b = b_2`) and suppose ALL FOUR
critical values of `P` are purely imaginary.  Then `a b^2 in R` and
`a^5 in R`, and consequently there is `theta` with

```text
e^{-5 i theta} P(e^{i theta} w) = w^5 + B w^2 + A w,     A, B in R.
```

That is: the tangent stratum is contained in the rotation orbit of the real
spine `{(A, B) in R^2}` under `(b_1, b_2) = (e^{4 i theta} A, e^{3 i theta}
B)`.

Proof.  The critical-value polynomial `R(Y) = prod_nu (Y - P(c_nu))`
(monic, degree 4) is, by an exact resultant computation verified symbolically
in the checker,

```text
R(Y) = Y^4 + (18 a b^2 / 25) Y^2
     - (4 b (27 b^4 - 400 a^3) / 3125) Y
     + a^2 (256 a^3 - 27 b^4) / 3125,
```

using `5 c^4 + 2 b c + a = 0` and `P(c) = (3/5) b c^2 + (4/5) a c` at
critical points.  If all roots of `R` are purely imaginary, then the `Y^2`
coefficient (`e_2` of imaginary numbers, real) and the constant coefficient
(product of four imaginary numbers, real) are both real:
`a b^2 in R`, and then `a^2 b^4 = (a b^2)^2 in R` forces `256 a^5 in R`,
i.e. `a^5 in R`.  If `a b = 0` a single rotation makes the surviving
coefficient real.  Otherwise write `alpha = arg a`, `beta = arg b`:
`a^5 in R` gives `5 alpha == 0 (mod pi)`, and `a b^2 in R` gives
`2 beta == -alpha (mod pi)`.  Set `theta = alpha - beta`.  Then
`3 theta == 3 alpha - 3 beta` and `beta - 3 theta == 4 beta - 3 alpha ==
-2 alpha - 3 alpha == -5 alpha == 0 (mod pi)`, so `b e^{-3 i theta} in R`;
and `alpha - 4 theta == 4 beta - 3 alpha == 0 (mod pi)` likewise gives
`a e^{-4 i theta} in R`.  QED

(The output frame matters: the rotation multiplies the safe-set direction by
`e^{5 i theta}`, so the spine family must be treated with its twisted output
phase; the converse inclusion is not claimed — real models need not be
tangent.)

SHARPENED (same session, two independent derivations, main-loop verified):
the containment above is strict and the twist is pinned — the tangent
stratum is EXACTLY ONE gauge orbit, `5 arg b_1 == pi`,
`arg(b_1^2/b_2) == +- pi/2`, `320 |b_1|^3 = 27 |b_2|^4` (so
`|b_1|^3 = 27/320` on the core), with output factor `e^{5 i theta} = +- i`
(an ANTI-real normal form `H = -i G`, `G` real).  Closed-form critical
data, the identification with `QuinticEqualityTetrahedron.md`'s equality
chart, and two explicit connector certificates at the orbit are in
`QuinticStarKernelMechanics.md` §6.

Corollary D1 (campaign dichotomy at `n = 5`).  Every quintic blow-up model
`w^5 + b_2 w^2 + b_1 w` EITHER admits the strict-hub safe two-arm connector
of Theorem C (non-tangent case, via Corollary B1), OR is a rotated real-spine
model.  The open selector problem (R1)/(SK5) therefore splits into (i) a
LENGTH/margin question along canonical arms on the non-tangent bulk and (ii)
a two-real-parameter (plus phase) stratum.

## 5. Theorem E (exact origin-ray criterion at n = 5) and its corollaries

For `P = w^5 + b_2 w^2 + b_1 w` and a tract direction `u` (`u^5 = 1`), write
`a_u = Re(b_1 u)`, `b_u = Re(b_2 u^2)`.  Then
`Re P(t u) = t^5 + b_u t^2 + a_u t`, and the FULL ray `[0, infinity) u` lies
in `{Re P >= 0}` if and only if

```text
a_u >= (3/4^{4/3}) ((-b_u)_+)^{4/3},        3/4^{4/3} = 0.4724703937...
```

Proof.  Positivity of `t^4 + b_u t + a_u` on `t >= 0`: if `b_u >= 0` the
minimum is `a_u` at `t = 0`; if `b_u < 0` the minimum is at
`t_* = (|b_u|/4)^{1/3}` with value `a_u - (3/4^{4/3}) |b_u|^{4/3}`.  QED

Note the balance identities `sum_u a_u = 0`, `sum_u b_u = 0` over the five
tracts.

Corollary E1 (both pure faces close through the origin).  If `b_2 = 0`
(pure first mode), the ray `u` is safe iff `Re(b_1 u) >= 0`, and among five
`72°`-spaced directions at least TWO always satisfy the closed condition (an
arc of `180°` contains at least two of five points spaced `72°`; if only one
point `p` of the closed arc `[-90°, 90°]` were inside, its neighbours
`p ± 72°` would both be outside, forcing `p > 18°` and `p < -18°`
simultaneously).  If `b_1 = 0` (pure second mode), the ray `u` is safe iff
`Re(b_2 u^2) >= 0`, and `u -> u^2` permutes the five directions, so again at
least two rays are safe.  In both cases two full origin rays lie in the safe
set, and the origin two-radii path is metrically free
(`NearFeketeRadialAngularSplit.md` Theorem 1): BOTH PURE FACES OF THE
QUINTIC BLOW-UP ARE CLOSED AT THE MODEL LEVEL BY THE ORIGIN HUB.  (This
supersedes, for `n = 5`, any need for curved-arm analysis on one-mode
models.)

Corollary E2 (mixed dominance cone).  Let `alpha = cos 72° = (sqrt 5 - 1)/4`.
If

```text
|b_2| <= 4 (alpha/3)^{3/4} |b_1|^{3/4} = 0.72729... |b_1|^{3/4},
```

then at least two tract directions have `a_u >= alpha |b_1|` (among five
`72°`-spaced cosines at least two are `>= cos 72°`), and for these
`(3/4^{4/3}) ((-b_u)_+)^{4/3} <= (3/4^{4/3}) |b_2|^{4/3} <= alpha |b_1| <=
a_u`, so two full origin rays are safe and the model closes through the
origin hub.  (Symmetrically, a `b_2`-dominant cone exists via the
`u -> u^2` relabeling with the roles of the criterion's two terms exchanged;
its exact shape is left to the finite-certificate stage.)

Relation to landed closures: the full model core — pure faces included — is
already certified by a DIFFERENT connector (chord + ray tails) in
`QuinticMixedGlobalAtlas.md` (3,834 Bernstein boxes; dictionary
`b_1 = -A`, `b_2 = -B`), the `b_1 = 0` face by
`QuinticSecondModeConnector.md`, and the pure faces globally at
actual-polynomial level by `CyclicTrinomialFiberCase.md` (trinomial origin
spokes).  E1/E2 add the origin-ray mechanism, whose value is that it
applies at REAL scale untransferred (see
`TwoTierStraightStarSelectorLab.md`), not that the model region was open.
The phrase "supersedes ... curved-arm analysis" in E1 is scoped to the
origin-ray route on one-mode MODELS only.

## 6. What this toolkit changes for (R1)/(SPOKE-5)

- The metric side of every hub construction is now EXACT (Theorem A): no
  smallness of the hub, no asymptotics; near-gon perturbation enters linearly.
- Model-level selection is now structured: Corollary B1 + Theorem C give a
  canonical SAFE two-arm connector at a strict critical hub on the entire
  non-tangent bulk; Theorem D reduces the tangent exception at `n = 5` to a
  rotated two-real-parameter spine; Corollary E1 removes both pure faces;
  Corollary E2 removes a `b_1`-dominant mixed cone.
- The surviving open content of (R1)/(SK5) at `n = 5` is thereby localized
  to: (i) the LENGTH (scattering) of the canonical arms — equivalently a
  margin bound along `gamma_+-` — on the genuinely mixed non-tangent region
  outside the origin-closed set, and (ii) the rotated real spine.  Both are
  compact, finitely-parametrized targets.

## Claim boundary

Theorems A, B, C, D, E and Corollaries B1, D1, E1, E2: ordinary proved
mathematics, re-derived in the main loop; the checker verifies each
machine-checkable component (identities to `1e-14`, symbolic resultant,
adversarial metric sup, criterion-vs-numeric agreement, ray counts, cone
sampling, arm containment/distinct-tract spot checks).  The adjacency of the
two arm tracts is NOT claimed (see §3's honest boundary).  NOTHING here
bounds the length of the canonical arms; no parent-theorem claim is made.
The blow-up transfer to actual polynomials at real scale (effective `eta`)
is the separately tracked bookkeeping of the quintic atlas
(`QuinticTransverseFiniteTransfer.md`) and is not re-derived here.
PRIORITY CAVEAT: the trace identity and the ellipse geometry are
classical-flavoured; no literature search has been run; the claim is "new to
this directory" only.
