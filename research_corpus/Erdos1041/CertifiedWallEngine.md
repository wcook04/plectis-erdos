# Erdős 1041: the certified wall engine — machine-proved enclosures of `mathcal E` on the chamber wall, a proved `O(mu^2/S)` tail theorem, and the (EX-W) closure architecture

Date: 2026-08-30.  Origin: wave-2 opus rigorous-numerics agent
(exact dyadic ball arithmetic; every certified quantity float-free),
main-loop review and landing.  Code:
`scripts/lib_erdos1041_cball.py` (complex ball arithmetic + Krawczyk)
and `scripts/lib_erdos1041_wall_engine.py` (`certified_excess`,
`wall_w`, `tail_bound`, gradient integrals).  Checker:
`scripts/check_erdos1041_certified_wall_engine.py` (fast subset:
re-certifies three of the six demo points, the positive-arm split at
the tangent point, the wall labeling, and the outward-rounding
regression).  Consumes `QuinticChamberWallReduction.md` (whose Theorem
A/Corollary B make wall certification sufficient for (EX-U) away from
the `mu = -10` stratum) and `TraceMaxWallGeographyLaw.md` (margins).

## 1. What is now machine-proved

Six certified enclosures (`k = 60`, i.e. `S = 60^5`; widths `~1e-4`;
30–45 s each), every upper bound strictly negative:

```text
(i)   mu = -10.5,  wall phi = 0.339535553547:  E in [-0.07357191, -0.07344659]
(ii)  mu = -12,    wall phi = 0.335980880332:  E in [-0.10495335, -0.10483254]
(iii) mu = -60,    wall phi = 0.160761632919:  E in [-0.26874768, -0.26863507]
(iv)  mu = -190,   wall phi = 0.004961351323:  E in [-0.27544317, -0.27529910]
(v)   mu = 2-1i,   arc mid  phi = -2.958835315: E in [-1.27925589, -1.27920059]
(vi)  mu = 50+30sqrt3, phi = -pi/2 (w = i):    E in [-0.16951202, -0.16939256]
```

All six contain the independent high-precision references; (vi)
reproduces the corpus tangent value `-0.1694610452` to `7.5e-9`, its
per-arm split is certified `e_- in [+0.656279, +0.656345]` (a PROVED
confirmation that individual arms go positive — only pair bounds can
close (EX-W)), and at (vi) all three gap conditions certify as tight
simultaneously — an independent machine confirmation of the geography
note's conical-vertex picture.  Wall phases are ALGEBRAIC in the
Krawczyk-certified gap enclosures (`w = -+ i g_{j*}/|g_{j*}|`, ball
radius `~3e-19`); no transcendental evaluation enters any certified
quantity.

**Tail theorem (proved, self-contained).**  With `y = 1 + x`,
`y^5 = e^{-i phi} s + P(y)`, `P(y) = -mu y^2 + (2mu+5)y - (mu+4)`:
under explicit checkable hypotheses at `S` (modulus floor, sector
membership of `y(S)/(u S^{1/5})`), for all `s >= S` the arm stays in
its tract with two-sided modulus bounds `lambda s^{1/5} <= |y| <=
Lambda s^{1/5}`, explicit angle bounds, and

```text
0 <= e_a - u_S <= (|y(S)| - Re(bar u y(S))) + Tail_1(S),
Tail_1(S) = O(mu^2 / S)   (leading constant 0.144 mu^2 when
                            lambda = Lambda = 1),
```

with every constant explicit and `S = k^5` keeping all powers rational.
The bound MAJORIZES the measured tail on 20/20 test arms (ratios
7.2–71).  As a by-product `u_S` is nondecreasing and bounded, so the
limit defining the excess exists — independently of the reduction
note's §4.

## 2. The (EX-W) closure architecture (the decisive engineering fact)

**`mathcal E` box-marches catastrophically; its gradient box-marches
almost for free.**  Direct interval certification over a `mu`-ball of
radius `delta` inflates the certified width by `~600x` (`mathcal E` is
a difference of two nearly equal `O(k)` quantities), failing already at
`delta = 1e-3`.  But the certified gradient integrals

```text
|grad_mu E| <= sum_a int |x'| |N_1||y-1|/|N_2|^2 ds,
|d_phi E|   <= sum_a int |x'| |Im(F'' A / B^2)| ds
              (the y^8 terms cancel exactly; the S^{1/5} normalizer
               makes the terminal term phi-independent),
```

are integrals of positive quantities and barely widen over a ball
(`0.105 -> 0.115` at `delta = 0.05`).  So the closure architecture is:
**point-certify `mathcal E` at cell centres; certify the Lipschitz
constant `L_W = |grad_mu E| + |d_phi E| |grad_mu phi_W|` over each cell
with a ball; close by the mean value theorem.**  Measured certified
Lipschitz data and the geography margins give cell radius
`delta(rho) ~ 0.02 rho^{0.70}` (`rho = |mu+10|`) and a projected

```text
N ~ 2.3e5 certified points  (x4 conservative: 9.2e5)
~ 100–190 core-days at current speed (up to ~750 conservative),
```

with a `~10x` speedup available (55% of runtime is CPython `Fraction`
gcd/dispatch; a dyadic mantissa/exponent class removes it) — i.e.
**(EX-W) is now a costed engineering project, not an open problem
shape.**  Two imports are honestly not machine-checked inside the
engine: the `d/d mu <-> lim_S` exchange (follows from holomorphy plus
the locally uniform convergence proved in the reduction note §4) and
the measured phi-evenness used to halve the wall sheets.

## 3. Rigor inventory (read before trusting or extending)

Fully rigorous: Krawczyk fibre enclosures with strict-tube branch
identity (a first-exit argument makes the certified root THE arm
point); two-sided arc bounds via an oriented-box first-order form with
explicit `F'''` remainder (the isotropic-tube cone bound is `~2000x`
weaker — a disc is the wrong enclosure for a nearly straight arm);
explicit head confinement on `[0, s_0]`; the §1 tail theorem; the wall
phase; both gradient integrals.  Fail-safe float: every scout
(Newton, step schedule, tract branch) is followed by an exact
validation that errors or widens, never silently corrupts.  Known
narrow holes, deliberately outside the engine: `wall_w`'s CHOICE of
tight gap and the disjointness of the three gap enclosures are
re-verified externally (`verify_wall.py` pattern; the checker repeats
the labeling check).  Two soundness bugs were found in self-review and
fixed BEFORE the final run (outward rounding of negatives collapsing to
zero; `sqrt_hi` where `sqrt_lo` over-cuts an angular width) — the
checker carries the rounding regression; the post-fix demo run was
bit-identical, so they were numerically inert here, but the first was a
genuine ship-class soundness bug.

## 4. Claim boundary

The six enclosures, the tail theorem, and the gradient bounds are
machine-proved modulo the two named imports.  The coverage projection
(cell counts, core-days) is an estimate from certified per-point costs
and measured margins, not a guarantee.  Nothing here certifies the
whole wall, the `mu = -10` arc interior, (EX-U), or the parent; it
supplies the tool and the plan.  The engine's arm definition is the
corpus's ("the two branches through `x = 0` with
`x_pm ~ +-sqrt(ws/(10+mu))`"), taken as given.
