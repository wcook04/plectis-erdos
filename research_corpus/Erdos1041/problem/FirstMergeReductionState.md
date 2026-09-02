# Erdős 1041: the first-merge reduction, and exactly what is left

Status: release synthesis, current 2026-08-27. Nothing new is proved here.
Every row below is either cited to where it is proved in this directory or
marked open. The point is that the reduction is now sharp and its ingredients
are spread across six files plus five added today, so a reader cannot see the
boundary from any one of them.

## The reduction

Work at `c*`, the critical point of least critical value `mu = min_k |f(c_k)|`,
with all roots in the **open** unit disk.

| ingredient | status | where |
|---|---|---|
| `mu < 1` | **proved** | discriminant identity + Fekete, strict on the open disk ([MinimumCriticalNewtonHubLab.md](MinimumCriticalNewtonHubLab.md)) |
| for `t < mu`, every component of `{|f| < t}` holds exactly one root and `f` is conformal on it | **proved** | properness + unbranched cover, same file |
| at `c*` two **distinct** one-root components meet | **proved** | simply-connectedness of polynomial sublevel components by a maximum-modulus no-hole argument, same file |
| the two lifts of the value ray `f(z) = s f(c*)` continue from `c*` to two **distinct** roots, and satisfy `\|f\| = s mu < 1` away from `c*` | **proved** | no critical value on the open segment, same file |
| `d_1 + d_2 <= 2 mu^{1/n} < 2` for the two **nearest** roots | **proved** | logarithmic balance, `CriticalTwoRootProximity.lean` |
| `d_1 + d_2 <= 2` at **every** critical point, strict on the open disk | **proved** | ["B1 holds globally"](CriticalBudgetLab.md) |
| `L(c*) = (d_a + d_b) + D(c*)`, `D >= 0` | **proved**, elementary | [TurningFloorRefutation.md](TurningFloorRefutation.md) |
| **`L(c*) < 2`** | **OPEN — this is the whole problem** | |

### Current authority anchors

The load-bearing metric row is not a numerical search claim. Its formal
algebraic core is [`two_add_le_two_of_disk_inverse_balance`](CriticalTwoRootProximity.lean#L160-L166),
and the general logarithmic-balance theorem is
[`exists_two_roots_dist_sum_le_two_mul_geomMean`](CriticalTwoRootProximity.lean#L229-L234).
Replay the complete Lean module from the repository root with:

```sh
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py \
  --jobs 2 --project-root formal_math/erdos257_period_noncollapse \
  ErdosProblems.Erdos1041.CriticalTwoRootProximity
```

Those declarations establish a Euclidean budget for a nearest pair selected by
the balance argument. They do **not** identify the endpoints of the descending
inverse branches, and they do not provide a path inside the unit lemniscate.
The latter two facts are the unclosed part of the row `L(c*) < 2`, not hidden
consequences of the Lean metric core.

**Containment is not the difficulty and has not been for some time.** The fourth
row settles it at the first-merge hub. What remains is purely a length statement
about two explicitly described analytic arcs.

Independent check of the fifth row, since it is the load-bearing metric input:
over 120000 minimum-critical hubs at degrees 3 to 8, in uniform, boundary-clustered
and near-polygon families, `(d_1+d_2)/(2 mu^{1/n})` never exceeded 1. Worst
`0.998762` at `n = 3`, falling with degree (`0.987, 0.947, 0.906, 0.837, 0.791`),
with the `n = 3` value tight against the extremal cubic exactly as it should be.

## The two gaps between the proved metric bound and the open length statement

1. **The branch endpoints are not the nearest roots.** `d_1 + d_2 <= 2 mu^{1/n}`
   is about the two nearest roots; `L(c*)` is about the two roots the branches
   actually reach. The merge pair minimises a *weighted* separation rather than a
   Euclidean one — heuristically the components of `a` and `b` are, at level `t`,
   approximately disks of radius `t/|f'(a)|` and `t/|f'(b)|`, so they first touch
   at `t ~ |a-b| / (1/|f'(a)| + 1/|f'(b)|)` — which is why merge pair and nearest
   pair differ. [StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md)
   §5 exhibits a degree-eight configuration where the pair that works is neither.
2. **The arcs curve.** `D(c*) > 0` in general, and the turning is genuinely large:
   [TurningFloorRefutation.md](TurningFloorRefutation.md) proves
   `alpha_A + alpha_B >= pi - phi` at a simple saddle, so where the budget is
   saturated the turning is bounded away from zero.

## What is now known not to work

Recorded so the next reader does not re-enter them.

* Direct root chords; fixed-origin broken lines; metric-selected spokes; spanning-tree
  budgets; the radial-lift angular average — all in `research_packet.json::negative_results`.
* Straight spokes at `c*`, in every selector form. §3 and §5 of
  [StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md): no rule of
  the form "pick the hub by critical value, then take the merging or the nearest
  pair" can work, with exact degree-6 and degree-9 witnesses where **no**
  admissible hub carries two contained spokes.
* The first-merge conditional theorem's spoke claim, refuted at 60 digits on
  those same witnesses ([CriticalBudgetLab.md](CriticalBudgetLab.md), "Claim 3 is false").
* Turning inflation, `L <= chord/cos(alpha/2)`, dead at every `n >= 3` — best
  possible return `2R sec(pi/4 - pi/(2n))`, and the supremum is `+infinity` since
  `alpha` passes `pi`.
* The merge-topology bounds (A), (B), (B\*) and (C)
  ([MergeTopologyBoundRefutation.md](MergeTopologyBoundRefutation.md)); (C) fails
  by the closed form `n^{(n-2)/(n-1)}/2`, unbounded in the degree.
* Any bound whose right-hand side is a **symmetric** function of the root
  positions relative to `c` ([CriticalBudgetLab.md](CriticalBudgetLab.md)).
* Second-order variational arguments at the extremum: the extremum is a **cusp**,
  with fractional-power response
  ([StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md)).

## The two live formulations

Both are restatements of `L(c*) < 2`; neither is proved.

**Chord deficit.** `L(c*) = (d_a + d_b) + D(c*)` with
`D = int (1 - cos theta) ds` over both branches, `theta` the angle between the
tangent and that branch's chord. Since `d_a + d_b < 2` is available at every
critical point, it suffices that `D(c*) < 2 - (d_a + d_b)` at some admissible
hub. Both sides vanish together on the extremal family, which is correct for a
sharp statement and is why no uniform positive margin can exist. Note
`1 - cos theta <= theta^2/2`, so a **weighted `L^2`** turning bound suffices where
the refuted route needed an `L^infinity` one.

**Resolved-branch form.** Setting `P(w) = f(c*+w)/f(c*)` and `xi^2 = 1 - P`, the
two branches become one analytic curve `Z(xi)`, `xi in [-1,1]`, with
`Z'(xi) = -2 xi / P'(Z)` and

```text
L(c*) = int_{-1}^{1} 2 |xi| / |P'(Z(xi))| d xi,
```

where `P(0) = 1`, `P'(0) = 0`, and `|P(d)| >= 1` at every other critical point of
`P`. This is a self-contained analytic question about one polynomial normalised
at a saddle, with no geometry left in it. The obstruction to attacking it by
angular averaging is recorded in
[RadialLiftCoareaGapLab.md](RadialLiftCoareaGapLab.md): the family
`z^n + eps z - r^n` makes all `n-1` critical-value arguments coalesce, so an
average over the value argument sees one spike `n-1` times and misses the
`2(n-1)` scale.

## The healthier route: the two-segment mechanism, and why the origin is load-bearing

Everything above concerns the **descent** construction. There is a second, older
mechanism recorded in [CriticalBudgetLab.md](CriticalBudgetLab.md) under "The
existence half", and on the evidence it is in materially better shape:

> connect two roots by a direct chord, **or** by a broken line through the origin,
> **or** through a critical point, admitting a segment only when the exact maximum
> of `|f|` along it is below 1.

With the spurious-hub fault repaired, 30 restarts and 600 hill-climb steps per
degree, the maximum cheapest certified connection is `1.999999998` at **every**
degree 2 through 10 — exactly `2r` at the modulus cap `r = 1 - 10^-9`, with
nothing above it, and every maximiser the roots-of-unity family. Proved at
`n = 2` and `n = 3`; measured and unrefuted through `n = 10`.

**This is not the straight-spoke route that died.** That route fixed the hub at a
critical point and took the merging or the nearest pair; this one admits the
origin as a hub and admits direct chords, and chooses the pair freely. So
[StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md) §3's
`QC = infinity` witnesses — degree 6 and degree 9, where **no admissible critical
point carries two contained spokes** — say nothing about it.

Measured directly at those two witnesses, at 40 digits:

| degree | cheapest certified two-segment connection | carried by | roots with contained spoke to the origin |
|---|---|---|---|
| 6 | `1.9999997` | **origin hub**, roots 0 and 1 | 3 of 6 |
| 9 | `1.9999997` | **origin hub**, roots 7 and 8 | 4 of 9 |

Both equal `2r` exactly, since the witnesses have max root modulus `0.99999985`.
So at the hardest configurations this directory has stored — the ones that kill
the critical-hub spoke route outright — **the connection is carried by the origin,
and it is carried at exactly the extremal value.**

Two consequences worth stating plainly.

* **Any formulation restricted to critical hubs is strictly weaker than the
  problem.** The origin is not a convenience; at these witnesses it is the only
  thing that works. A proof attempt that only ever selects critical points has
  already given away the configurations that matter most.
* The mechanism is **tight exactly where the problem is tight** — the maximiser at
  every degree is `z^n - r^n`, whose cheapest connection is the two-radius broken
  line through the origin of length `2r`. That is the same family that saturates
  the budget theorem and the same one that makes the constant 2 sharp.

The exact behaviour on that family is worked out rather than measured: the
midpoint of two roots `k` steps apart is `m = r cos(pi k/n) e^{i pi k/n}`, so the
adjacent chord escapes iff `r^n (1 + cos^n(pi/n)) > 1`, which at `n = 3` is
`r^3 > 8/9`. For odd degree **no** chord is interior; for even degree only the
diameter, which is the origin hub with its spokes collinear. Either way the
cheapest connection is `2r`.

### The three families cover each other's failures

The origin alone does **not** suffice, and that is settled exactly, not
numerically: [OriginSpokePairCounterexampleComputationalLab.md](OriginSpokePairCounterexampleComputationalLab.md)
gives a Gaussian-rational quintic at `r = 99999/100000` with directions from the
Pythagorean triples `20^2+99^2=101^2` and `28^2+195^2=197^2`, at which four of the
five origin spokes provably exit, so at most one is safe and no pair can be joined
through the origin.

Measuring the *full* mechanism at each of the recorded hard witnesses, at 40 to 50
digits, shows the families are complementary rather than redundant:

| witness | critical hubs | origin | chords | cheapest certified connection |
|---|---|---|---|---|
| degree 6 (QC, §3) | **all fail** | works, 3 of 6 spokes contained | — | `1.9999997` = `2r` |
| degree 9 (QC, §3) | **all fail** | works, 4 of 9 spokes contained | — | `1.9999997` = `2r` |
| degree 5 (origin lab) | — | **fails completely, 0 of 5 spokes** | works | **`0.0567`**, chord between roots 1 and 3 |

At the quintic the measurement is stronger than the lab's own statement: not "at
most one safe spoke" but **none**. And the connection there is cheap because the
configuration has two roots about `3.2` degrees apart — which is exactly why
[TrueGeodesicLab.md](TrueGeodesicLab.md) records its true geodesic as `0.061` and
calls it "not remotely a hard instance"; the chord value `0.0567` is consistent
with that grid estimate and identifies the responsible pair.

So each family fails somewhere, and at every recorded hard configuration another
family carries the connection at or below the extremal value. That is a coherence
property of the mechanism, not a proof, but it is the reason the measured ceiling
sits at `2r` rather than drifting upward.

### But two of the three can be empty at once, from degree three

The table above shows each family failing *somewhere*. It does **not** show two
of them failing *together*, and that is the question that decides whether the
critical-hub family is needed at all. It is:
[TwoSegmentContainmentReduction.md](TwoSegmentContainmentReduction.md) §2 gives
an exact Gaussian-rational degree-three witness — `L(7 pm 24i)/25` and `-L` with
`L = 999/1000` — at which **no root chord is safe and at most one origin spoke
is safe**. The origin is the minimum-enclosing-disc centre there, certified by
the positive rational barycentric weights `(25/64, 25/64, 7/32)`, so this also
lowers the recorded degree-five `adaptive_mec_chord_or_radial_counterexample` to
the minimal degree: at `n = 2` the chord is always safe, since
`|f| = t(1-t)|a-b|^2 <= 1` on it.

The mechanism is a sign condition, not a thin margin. With all roots on a common
circle of radius `L`, the spoke to `a_j` starts at `|f(0)| = L^n` with initial
log-derivative `-Re(conj(p_1) a_j)/L`, so as `L -> 1` only roots in the closed
half plane `Re(conj(p_1) z) >= 0` can carry a contained spoke — and that half
plane can hold exactly one root even though `sum_j Re(conj(p_1) a_j) = |p_1|^2`.

Two consequences. The critical-hub family is **not** redundant. And random
sampling cannot see this: 4000 draws from six structured families gave zero
failures of the chord-or-origin disjunction that an adversarial searcher broke
within seconds.

**What is missing is the same shape as before**: existence of a good hub-and-pair
in general, proved only at `n = 2, 3`. But the search space is larger and the
measured ceiling has never been exceeded at any degree, which is a better
position than the descent route is in.

And the obligation is a different *kind* of statement. Admitting a free hub `h`
rather than the three named ones, the requirement is

```text
max_{[h,a]} |f| < 1,   max_{[h,b]} |f| < 1,   |h - a| + |h - b| < 2,
```

and the third condition says exactly that `h` lies in the open ellipse with foci
`a, b` and major axis 2. So the length obligation becomes a two-real-dimensional
membership test on one point: straight segments have zero chord deficit, so
`D(c)`, the turning floor, and `int_0^mu ds/|f'|` are all absent. That is the
reduction stated in
[TwoSegmentContainmentReduction.md](TwoSegmentContainmentReduction.md) §1. It is
a sufficient family — its failure would not refute the problem — and it is
feasible at every recorded hard witness. Adversarial search cannot move its
objective off `1` by more than about `5e-7` for degrees 3 through 9, with the
regular polygon as maximiser; the same searcher breaks the neighbouring
chord-or-origin disjunction by `9.7e-3`, four orders of magnitude more.

## Same-day addendum: the near-Fekete half's cone hypothesis is closed

Everything above concerns the two-segment and descent routes on real polynomials.
On the *other* live route — the near-Fekete cusp law, which governs the regime
[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) identifies as the hard one
— the remaining hypothesis is no longer degree-limited.

Two files landed it the same day by different routes.
[MonotoneTurningProof.md](MonotoneTurningProof.md) proves monotone turning on
both branches at every degree by a quadrant-trapping argument, and
[BridgeIdentityProof.md](BridgeIdentityProof.md) proves the bridge (BR) and
assembles `kappa_n = C_n - (D_1+D_2) >= C_n - B_n > 0` from it. Those two own the
result. [ConeBoundMonotoneFunctional.md](ConeBoundMonotoneFunctional.md) is a
second, shorter route to the same hypothesis, and it shows that the
inequality (★) of [ConeBoundBranchGeometry.md](ConeBoundBranchGeometry.md) is the
statement that one explicit harmonic function is monotone along the branch:
with `Xi(zeta) = (n-2) zeta - zeta^{2-n}` on the fixed model `zeta^n + n zeta`,

```text
Xi'(zeta) = ((n-2)/n) g'(zeta)/zeta^{n-1},      Xi(zeta_c) = (n-1) zeta_c,
```

so `d(Im Xi)/d sigma = ((n-2)/n) Im(zeta^{1-n})` carries the sign opposite to
`Im g'`, and sector confinement alone forces `Im Xi` off its hub value `c_n` in
the direction that makes the turning bound hold. Consequences:

* **`kappa_n > 0` at every degree `n >= 3`, on both branches**, where before it
  was a theorem only at `n = 3` on branch 1. The proved bound is `C_n - B_n`,
  which is `0.3860` at the binding degree against the `L^2` route's `0.2119`.
  This is `BridgeIdentityProof.md` §4's assembly, not the `Xi` file's.
* All three of `ConeBoundBranchGeometry.md` §7's open items are closed: the two
  inequalities by both routes, and the `(y-1)^3(y+1)` mystery by
  `MonotoneTurningProof.md`, which shows `sin^2` forces order-3 vanishing at the
  hub. The `Xi` route shows the factorisation was never needed.
* **(★) is *false* on branch 2**, and correctly so: branch 2 needs `dt/d sigma < 0`,
  hence `Phi < 0`. The correct statement is `sign(Phi) = -sign(t(0^+))`, of which
  (★) is the branch-1 half. §7 of that file lists "(★) on branch 2" as a goal;
  the goal as stated cannot hold.
* The descent-ray direction drops out of the algebra but selects the hub: both
  branches are confined **exactly** for `delta in (0, 2 pi/(n-1))`, an interval of
  length exactly the hub spacing, so exactly one of the `n-1` hubs is admissible.
  Necessity comes from the asymptotic directions; sufficiency from Lemma S(δ)
  (the level argument survives for every `delta in [0, pi]`, and the window sits
  inside that) and Lemma W2 (on the outer ray `g'` is real positive, so
  `d(arg zeta)/ds = sin(delta - 2 phi_c)/(r g') < 0` and the wall is a one-way
  barrier).
* **Theorem R closes the last measured link.** `BridgeIdentityProof.md` §4a
  records "that `min_phi kappa_n(phi)` is attained at `phi = 0`" as *measured and
  still load-bearing for the all-`phi` statement*. With confinement proved across
  the window, Lemma T generalised to an arbitrary ray direction, and
  `C_n(delta) > B_n(delta)` proved on the closed window — termwise for `n >= 5`,
  by a Lipschitz-certified grid for `n = 3, 4` — the conclusion is
  `kappa_n(phi) > 0` at **every** degree and **every** direction, and `phi = 0` is
  the worst case **for that lower bound** — not for `kappa_n` itself, which
  `RayDirectionScopeLimit.md` §4 shows the recorded 24-point sweep does not
  resolve. Positivity on the window is positivity everywhere because the window
  is exactly one period of `kappa_n` in the ray direction. So on the limit model
  the near-Fekete half is now proved outright.
* **The two routes agree on the boundary.**
  [RayDirectionScopeLimit.md](RayDirectionScopeLimit.md) proves, independently and
  in the opposite sign convention, that confinement and the cone bound are FALSE
  off-alignment, with `sup|t|/T` up to `5.25` at four `n = 6` directions. Those
  four reproduce in the `Xi` file's own tracer to three digits and all four lie
  outside the window; inside it the ratio is `1.0` to `4e-8`. So the two files are
  the two halves of one statement: the cone bound holds on exactly one
  hub-spacing arc and fails outside it.

Of these, the first two belong to the concurrent files; what the `Xi` route adds
on its own is the second proof, the `Xi_m` family, and all of the ray-direction
work including Theorem R. None of it touches the two-segment mechanism, the
constant 2, the `O(rho^2)` remainder, the degenerate direction `h'(0) = 0`, the
passage from the limit model to a finite perturbation, or the
`D`-bounded-away-from-1 regime — which is now the larger of the two halves left.
Receipt:
[scripts/check_erdos1041_cone_bound_all_degrees.py](scripts/check_erdos1041_cone_bound_all_degrees.py).

**Later update.** [NearFeketeTransverseClosure.md](NearFeketeTransverseClosure.md)
now proves the finite passage and the scale-normalized strict bound on every
fixed transverse cone `|h'(0)| >= eta ||h||`, uniformly in base radii up to one;
its final asymptotic sign transfer is Lean-checked. Accordingly, the
`O(rho^2)`/finite-perturbation item in the preceding paragraph survives only as
`eta -> 0`. The exact near-Fekete residual is the higher tangent family
`zeta^n + (n/j)zeta^j`, `2 <= j <= n-1`, together with its saddle-connection
limits. This update does not affect the still-open `D`-away-from-1 regime or
the unrestricted problem.

## Same-day addendum: the obligation is a capacity bound, and it is scale-free

The row `**L(c*) < 2**` above is stated at the level `1`, where the constant `2`
is a fact about the unit disk. [CapacityGeodesicConjecture.md](CapacityGeodesicConjecture.md)
restates the obligation at the level `μ`, where it becomes

> **(C)** if a component of `K_t = {|f| ≤ t}` holds two roots, two of them are
> joined inside it by a path of length `≤ 2 t^{1/n} = 2 cap(K_t)`,

and proves that (C) implies Erdős #1041 using only `μ ≤ R^n`. Three things
change, and all three matter to the table above.

* **The disk leaves the statement.** `geo / (2 t^{1/n})` is an affine invariant,
  so (C) has no unit-disk hypothesis; the disk is carried entirely by the
  classical Fekete chain in the reduction step.
* **The extremal becomes a family, not a degeneration.** (C) is an *equality*
  for `(z−τ)^n − λ` at every `n ≥ 2` and every `λ ≠ 0`, hence for every
  quadratic. The "no polynomial-independent slack" findings — this file's own
  gap-2 material and `negative_results` entry 0 — describe the `r → 1⁻`
  degeneration of a level-1 statement; they do not bear on a bound whose
  equality case is a two-parameter family at every scale.
* **It survives where the strong completion died.** `geo ≤ L(c*)` always, so
  `L(c*) ≤ 2μ^{1/n}` — refuted at degree four by `negative_results` entry 28 —
  would imply (C). (C) is the same statement with the descent branch replaced by
  the geodesic, and the branch/geodesic gap is exactly what entry 28 spent.

**Effect on the two gaps.** Gap 2 ("the arcs curve") is not removed but is
re-weighted: (C) needs the *geodesic* deficit to fit inside the metric slack,
never the *branch* deficit, and
[CapacityGeodesicConjecture.md](CapacityGeodesicConjecture.md) §7 proves the
slack is first order in the critical radius `ρ_crit` with slope at least
`2cos²(π/n)`, measured exponent `1` at `n = 3,4,5,6`. That is the perturbative
handle [HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) says is missing:
the cusp is a coordinate, and in `ρ_crit` the response is affine.

**Gap 1 is unchanged, and one thing that looked like progress on it is not.** A
degree-four witness there has merging pair ≠ nearest pair at the minimum-critical
hub — but inside a `1.55e−6` critical-value tie, and every tie-guarded search and
all 440 bulk draws put the merging pair *at* the nearest pair. So no tie-free
separation is on file, and gap 1's "the branch endpoints are not the nearest
roots" is still a heuristic claim rather than a witnessed one at the first-merge
hub. *(Superseded 2026-08-28: tie-free separations are now on file at tie
guards `1.001` and `1.05`, found by the gradient-proxy instrument; gap 1 is
witnessed, and the merging-pair metric floor survives at every witness. See
[ClaimLRefutation.md](ClaimLRefutation.md).)* Whoever closes it closes the metric floor of (C) at the same time, because
`exact_results::critical_pair_metric_scale` already covers the nearest pair.

## Same-day addendum: every centred trinomial is closed exactly

[CyclicTrinomialFiberCase.md](CyclicTrinomialFiberCase.md) removes the entire
centred three-term class from the open frontier.  If

```text
f(z)=z^m+a z^r+c,             m>r>=1,
```

and all roots lie in the open unit disk, then **every** root-to-origin spoke is
safe.  For a root `w` and `u in [0,1]`, the root equation gives

```text
f(uw)=(1-u^r)c-(u^r-u^m)w^m,
```

and the two nonnegative coefficients sum to `1-u^m`; since `|c|<1` by Vieta
and `|w|<1`, the whole spoke has `|f|<1`.  Any two roots therefore join through
the origin with length below two.  The same argument, plus the regular-fibre
mean-square identity, settles arbitrary translations
`(z-h)^(qm)+a(z-h)^(qr)+c` whenever `q>=2`.

This is not a reformulation or a perturbative shell.  It is an all-degree,
all-scale exact case theorem with a canonical Lean-checked algebraic kernel.
It strictly subsumes the even-symmetric trinomial row.  Its sparse residual is
precise: translated coprime-exponent trinomials have no nontrivial cyclic fibre,
so displacement from the translation centre is no longer automatically below
one.

## Claim boundary

Before the centred-trinomial addendum, this file contained only synthesis plus
the independent 120000-hub check of `d_1+d_2<=2 mu^{1/n}`.  The addendum now
records one genuine case theorem proved in its linked source and Lean module;
it does not alter the unrestricted first-merge obligation.  Erdős #1041 remains
open, and the honest unrestricted summary is: **containment is proved, the
metric bound for the nearest pair is proved, and what is missing is a length
bound for the pair the branches actually reach.**
