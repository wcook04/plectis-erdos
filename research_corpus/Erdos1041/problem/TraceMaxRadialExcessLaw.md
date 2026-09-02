# Erdős 1041: the trace-max excess LAW on the quintic core — rightward holds globally with margin `-0.0363` (extremal = certificate (ii)); the radial carrier FAILS in an open pocket; the coercivity invariant is `|c*|`

Date: 2026-08-30.  Origin: subagent computational campaign (three
independent instruments agreeing to `2.2e-16`; 76,252 grid/sweep
points; differential-evolution adversaries; 30-dps polish), main-loop
spot re-verification.  Checker:
`scripts/check_erdos1041_trace_max_radial_excess.py`.  This is a
COMPUTATIONAL LAW note in the sense of `TwoTierStraightStarSelectorLab.md`
— measured geography for the (EX) obligation of FRONTIER §4.3(a), not a
theorem.

## 1. The rightward law ((EX) measured TRUE globally, with a uniform margin)

For `H = w^5 + b_2 w^2 + b_1 w` on the core `max(|b_1|, |b_2|) = 1`,
trace-maximal hub `c*`, and the RIGHTWARD value-ray arms (the Main
Theorem's connector, lifts of `{H(c*) + s : s >= 0}`):

```text
sup_core (e_i + e_j)  =  -0.0362736374,
```

attained EXACTLY at the tangent orbit's skip-pair hub — the corpus's
certificate (ii).  The curved pair at this point is now proved strictly
negative by `QuinticTangentCurvedExcessCertificate.md`; the older
`QuinticTangentOrbitExactCertificate.md` proves the separate straight
skip-pair rescue.
Zero of 76,252 sampled/adversarial configurations had `e_i + e_j >= 0`;
three DE seeds independently converged to the orbit
(`|b_1| = (3/4) 5^{-1/3}`, both `arg(b_1^2/b_2) = -+ pi/2` branches).
The landed stratum table (`QuinticStarKernelMechanics.md` §6: excess
`[0.041, 0.323]`, slack `[0.078, 1.229]`, clearance `1.9x–5.0x`) was
reproduced row by row; interior levels are an exact `1/lambda`
rescaling of the core (verified `5.7e-12`), so the core sup is the
whole-model sup.

**Trace-MAXIMALITY is the load-bearing restriction — not safe-set
membership, not nonnegative level** (final agent correction run;
12,000 random core configs x 4 hubs x 2 rays, blocked/degenerate rows
filtered):

```text
ray        hub restriction              sup E_pair      failures
radial     trace-max hub                -0.0193             0
radial     any hub with Re H(c) >= 0    +0.3520          2.2%
rightward  trace-max hub                -0.0546             0
rightward  any hub with Re H(c) >= 0    +0.3644          2.5%
```

Merely admissible-level hubs fail on BOTH rays; the trace-max hub
never did.  (Unrestricted all-hub suprema, stochastic lower bounds:
rightward `>= +0.6301` — its argmax hub has `Re H(c*) = -0.72`,
outside the safe set, so it is weak evidence on its own; radial
`+0.5034`, on the tangent orbit at level exactly 0.  The random
trace-max radial sample's zero failures at sup `-0.0193` independently
reconfirms that the open radial failure pocket (~0.01% measure) is
reachable only by the targeted orbit approach.)

**Consequence.**  The (EX) inequality `e_i + e_j <= 0` for the Main
Theorem's arms — the metric half of (R1) — now carries a measured
GLOBAL margin `0.0363`, with its unique extremal at the point already proved
exactly.  The analytic obligation is now the compact core with that isolated
tangent point and the centre plus both endpoints of the `mu=-10`
repeated-critical phase arc removed.  The endpoint removal is exact:
`QuinticMinusTenEndpointExcessCertificate.md` proves
`mathcal E(-10,+-arctan(1/(2sqrt(2))))<-1/80`.  The two open subarcs and
the other singular strata still require their natural coordinates; the
measured geography remains: extremal AT the tangent orbit, margin growing
linearly in distance from it.

## 2. The radial carrier fails (do not re-propose globally)

The OUTWARD radial value-ray connector (lifts of `{t H(c*) : t >= 1}`,
the carrier of `OneFaceRadialScatteringTheorem.md`) does NOT extend
from the one-face stratum to the core:

```text
sup_core E_pair(radial) = +0.3582121   (cone-limit fit; open failure set).
```

Mechanism: at the tangent orbit all critical values are collinear
(purely imaginary), and the small hub's radial ray is BLOCKED by the
double foreign value (`V_1 = V_2 = 6.4641 Z*_3` on the same ray,
raygap `1.8e-15`); for `D > 0` the ray is critical-value-free but its
margin degenerates like `(t - 1) D`, and in the open cone of
perturbations keeping the small hub trace-maximal (measure `2.7%` of
the sphere) the excess limit is `+0.357..+0.358`.  Explicit witness
(fully non-degenerate, three instruments to `7e-14`): `eps = 1e-2`
orbit perturbation `b_1 = 0.35882554847972720 + 0.25257115012213690 i`,
`b_2 = -0.95331382807191360 + 0.30198136566164796 i`:
`E_radial = +0.2276426`, `E_rightward = -0.0376871`.  The failure set
is small (`0.011%`–`0.037%` of the core) but OPEN.  Conditional law:
excising a ball of radius `0.30` around the orbit in the
`(|b_1|, arg b_1, arg b_2)` chart leaves `sup E_radial = -0.0029 < 0`
(and `-0.0395` for rightward) — matching the landed conical bound
`D >= 0.30 dist`.  Structural fact: on each one-face line the radial
excess is EXACTLY CONSTANT (the ray direction is carried by `Z*`
itself, so hub, ray and arms rotate rigidly), equal to the rightward
MINIMUM over the line — the one-face theorem's constants
(`-0.8796` at `b_2 = 0`, `-1.0009` at `b_1 = 0`) are those constants.

## 3. The right coercivity invariant

Correlations over the extremal band: `corr(|c*|, E) = -0.99` (both
rays); `corr(Delta_5, E) = -0.64` (rightward).  A Delta_5-coercive
bound `e_i + e_j <= -kappa Delta_5` holds numerically for the
rightward arms with `kappa = 0.0170` but is sup-driven (Delta_5 in
`[2.00, 3.26]` barely varies); for the radial arms it is FALSE.  Any
quantitative `(EX+)` should be posed in the HUB MODULUS (equivalently
the straight-ray slack `Re(h conj(u_i + u_j))`), e.g. the measured
envelope `E_rightward <= -0.163 |c*|` on the sweep (OLS
`E_rad = -0.2195 Delta_5 - 0.3585` recorded for completeness).  The
entropy sum rule (`TraceMaxEntropyAngularBudget.md`) remains the exact
all-sheet currency; its role in a two-sheet allocation must route
through `|c*|`.

## 4. Numerical hygiene (what makes these rows trustworthy)

Three instruments (deflated local branch + Newton march + anchored
graded Gauss–Legendre; adaptive DOP853 `rtol 1e-12`; mpmath 30 dps)
agreeing to `2.2e-16` on ordinary cases; excess-form vs `L - |z|` form
agreement `3.5e-14` across the sweep; cutoff independence
`R = 20/30/50/100` to `5e-12` with tail model `C^2/(10 R^5)`; Newton
residuals `<= 1.3e-15`; `value_gap` guard (raygap `>= 9.2e-4` on the
sweep; near-tie hubs handled by evaluating all four); zero same-tract
arm pairs in ~150k arms (Main Theorem clause 1 confirmed); trace
identity exact (`3.4e-16`); `max |c*| = 0.85828 < t_0`.  Gauge note:
`z -> omega z` is a model gauge only for `omega^5 = 1` (the value
plane rotates otherwise); the core cell used is `arg b_1 in
[0, 2pi/5)`, full `arg b_2`.

## Claim boundary

COMPUTATIONAL LAW throughout (grids + adversaries + high-precision
polish; no interval certificate).  The radial-carrier refutation is a
measured open-set failure with explicit high-precision witnesses — it
retires the global radial route while leaving
`OneFaceRadialScatteringTheorem.md`'s stratum theorem (and its
`dist >= 0.30` conditional extension) intact.  Nothing here proves
(EX); it fixes the extremal, the margin, and the right invariant for
the analytic attempt.  Consumes and does not modify the landed Main
Theorem, certificate (ii), and stratum table.
