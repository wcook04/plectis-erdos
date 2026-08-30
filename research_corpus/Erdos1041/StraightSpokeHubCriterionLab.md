# Straight-spoke hub criterion — which containment a critical hub can carry

Target (open): if a monic `f(z) = prod_i (z - z_i)` has all roots in the open
unit disk, two roots can be joined by a curve of length below 2 inside
`{|f| < 1}`.

Verifier: `scripts/check_erdos1041_straight_spoke_hub_criterion.py`
Engine: `system/lib/formal_math_lemniscate.py`
Receipt: `source-provenance://private-authoring-project/receipts/erdos1041_straight_spoke_hub_criterion_receipt.json`

## 0. Prior work in this corpus, and what is actually new here

`MinimumCriticalNewtonHubLab.md` already proves, as ordinary mathematics, most
of the frame this note works in, and it must be read first:

* the scale normalisation — dividing by `R = max_j |z_j|` reduces the strict
  open-disk statement to a non-strict closed-disk one;
* `rho = |f(c)|^{1/n} <= R` at a minimum-modulus critical point, from the
  resultant identity `|Disc f| = n^n prod_{f'(d)=0} |f(d)| >= n^n |f(c)|^{n-1}`
  meeting the Fekete/Hadamard bound `|Disc f| <= n^n R^{n(n-1)}`, with equality
  forcing a rotated regular `n`-gon;
* the **strong** completion `L_1 + L_2 <= 2 rho` against the **weak** one
  `L_1 + L_2 <= 2 R`, with the strong one flagged there as possibly false;
* the first-merge proposition: below `mu = min |f(c)|` every component of
  `{|f| < t}` carries exactly one root and is mapped conformally, and the first
  handle joins two *different* one-root components;
* the normalised form `P(0) = 1`, `P'(0) = 0`, `|P(d)| >= 1`;
* an **exact** degree-five counterexample to the straight completion *at the
  minimum-critical hub*, with Gaussian-rational roots on `|z| = r`, all four
  zeros of `f'` isolated in disjoint rational Rouché disks, and dyadic spoke
  parameters giving `|f|^2 > 1` on four of the five spokes
  (`check_minimum_critical_straight_hub.py`).

Two things in this note are not in that record.

**The criterion separation (§1–§2).** The straight elimination there uses
`|f|^2 > 1`, the open-lemniscate test. But the landed degree-three theorem
proves the *hub-sublevel* test `|f| <= |f(c)|`, which is strictly stronger. §2
exhibits a quartic separating the two, so the degree-three inequality is the
wrong generalisation target independently of whether straight spokes survive.

**The elimination is at every hub, not only the minimum one (§3).** The exact
degree-five witness rules out the minimum-critical hub. §3 exhibits degree-six
and degree-nine configurations where *no* admissible critical point at all
carries two contained straight spokes, so the mechanism cannot be repaired by
choosing a different hub either. That closes "another critical point" as a
stand-alone repair, which the earlier record left open.

Everything in §5b and §6b is evidence and structure attached to the corpus's
**strong** statement, not a new reduction. The dedicated falsifier there,
`critical-scale-normalized-minimum-critical-newton-hub`, had reached
0.9495242630078684 on a canonical degree-five run; the multi-seeded pressure
recorded below reaches 0.999994283 at degree three.

## 1. The two criteria are different statements

A two-spoke critical hub joins roots `z_i, z_j` through a critical point `c` by
the broken line `[z_i, c] u [c, z_j]`. Two containment tests have been used for
those segments:

| name | test | what needs it |
|---|---|---|
| `hub_sublevel` | `|f| <= |f(c)|` on the spoke | what the landed degree-three theorem proves |
| `open_lemniscate` | `|f| < 1` on the spoke | what the target statement actually requires |

They are not interchangeable. Since a hub is admissible only when
`|f(c)| < 1`, `hub_sublevel` is strictly stronger.

The degree-three proof lands on the stronger side. Its normalisation
`P_b(w) = w^3 - (3/2) b w^2 + 1` with the identity

```
P_b(t w) = 1 - t^2 - t^2 (1 - t) w^3
```

gives `|P_b(t w)| <= 1 - t^3 <= 1` for a root `w` with `|w| <= 1`, and
`|P_b| <= 1` is exactly `|f| <= |f(c)|`. So the cubic theorem proves
`hub_sublevel` containment, and the packet's standing question — what replaces
that sparsity in higher degree — is a question about the *stronger* criterion.

## 2. Exact witness: the sublevel form dies at degree four

Roots `(a + b i)/10000` for

```
(9999, 4)    (-125, 9998)    (-9999, -14)    (-23, -9999)
```

All four satisfy `a^2 + b^2 < 10^8`, so they lie strictly inside the open unit
disk (an integer inequality, not a floating comparison). The quartic has three
critical points:

| `|f(c)|` | admissible | `hub_sublevel` contained spokes | `open_lemniscate` contained spokes |
|---|---|---|---|
| 1.001223330 | no | — | — |
| 0.998709854 | yes | `{3}` | `{1, 2, 3}`, best pair 1.807638689 |
| 0.998614511 | yes | `{1}` | `{1, 2, 3}`, best pair 1.787689338 |

At every admissible critical point at most **one** root has a sublevel-contained
spoke. The sublevel two-spoke mechanism therefore produces no path at all here —
this is not a length overshoot but a total failure of the mechanism. The same
hubs carry three open-contained spokes, with best pair 1.787689338 < 2.

Re-derived at 60 decimal digits with the critical points relocated by Newton
from the float seeds; the two passes agree. Segment maxima are located from the
real roots of `d|f|^2/dt` along the segment, never sampled — a sampled test can
skip a narrow excursion and report a containment that does not hold.

The failure is not a large-degree accident. It appears in an arbitrarily small
neighbourhood of the extremal family `z^n - r^n`, where the radial spokes satisfy
`|f(t z_k)| = r^n (1 - t^n) <= r^n = |f(c)|` with equality only at `t = 0`: the
sublevel containment is marginal at the extremal family, so a generic
perturbation breaks it. The verifier's deterministic stress family perturbs that
family at four radii and eight perturbation scales and counts the configurations
in which *no* admissible hub retains two sublevel-contained spokes:

| degree | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|
| configurations with no sublevel two-spoke hub | 0 | 9 | 16 | 7 | 3 | 4 |

Degree three never breaks, which is what the landed theorem says; every degree
from four to eight does.

A conjugate-symmetric (real-coefficient) quartic could not be made to separate
the criteria in a 30000-configuration search: the perturbation that breaks
sublevel containment is angular and asymmetric.

## 3. The weaker form dies too, at degree six

Let

```
QC = min over critical points c with |f(c)| < 1
       of  min over root pairs with both spokes inside {|f| < 1}
             of  |z_i - c| + |z_j - c|.
```

Adversarial maximisation of `QC` (evolutionary search seeded from the extremal
family and from uniform configurations, exact segment maxima) gave suprema
1.999999688, 1.999994811, 1.999814422, 1.998833219, 1.996839079, 1.990569039,
1.979972102, 1.970227236, 1.928588184 for degrees 3, 4, 5, 6, 7, 8, 9, 10, 12 —
pinned hard against 2 and never reaching it. **That reading was wrong.**

A second search, maximising the *minimal-critical-value hub* objective instead,
landed in a different basin and found configurations where `QC` is not close to
two but **infinite**: no admissible critical point carries two open-contained
spokes at all.

| degree | admissible hubs | contained spokes per hub | `QC` |
|---|---|---|---|
| 6 | 2, at `|f(c)| = 0.99995098599675816247` and `0.99995927525097869638` | 1, 1 | infinite |
| 9 | 3, at `|f(c)| = 0.99994148349944226776`, `0.99994222113908338804`, `0.99997939186312192797` | 1, 1, 1 | infinite |

All roots lie strictly inside the open unit disk (max modulus `0.99999985`).
Verified at 60 decimal digits with the critical points relocated by Newton
(residuals `|f'(c)| ~ 1e-61`) and every quantity computed from root products
rather than `polyval`. The witnesses are stored as exact IEEE-754 hexadecimal
literals in the verifier, since the margins are near `1e-5` and would not
survive decimal rounding.

**Erdős #1041 is not refuted at those configurations.** The two descending
inverse-ray branches at the same hubs give 1.763942 (degree 6) and 1.545995
(degree 9), and grid geodesics between roots inside `{|f| < 1}` give 1.668784
and 1.395432.

**Routing consequence.** The packet's negative result 4 concluded that a
successful fan-in must use curved descending branches, another critical point,
or global component / Reeb geometry, and `MinimumCriticalNewtonHubLab.md` had
already eliminated straight spokes *at the minimum-critical hub* by an exact
degree-five witness. "Another critical point" is now excluded as a stand-alone
repair too: from degree six there need not be *any* critical point with two
contained straight spokes. Curvature is forced, and negative result 4 is
confirmed rather than relaxed.

**Methodological note, recorded because it nearly landed a false claim.** A
supremum pinned just below a threshold by local adversarial search is not
evidence that the threshold is never crossed. The two searches ranged over the
same space; only the seeding differed. Report which basin a search explored, not
only its record value.

## 4. Mechanisms eliminated on the way

Four candidate routes were tested and killed. Each was a plausible bridge
between the metric theorem and a containment proof.

**(a) Sublevel spokes to the two nearest roots at the minimal-critical-value
hub.** False. Normalising at `c* = argmin |f(c)|` by `alpha^n = f(c*)`,
`u = (z - c*)/alpha`, a degree-12 configuration has the second-nearest root's
spoke reaching `|f| / |f(c*)| = 2.28318003178603` at `t = 0.716` — confirmed at
60 digits. The second-nearest root need not sit in a component adjacent to the
hub, so its straight spoke crosses a wall.

**(b) Two normalised roots inside the closed unit disk.** False. The normalised
polynomial is `P(u) = 1 + u^2 R(u)` with `R` monic of degree `n - 2`, satisfying
`P(0) = 1`, `P'(0) = 0` and `|P(kappa)| >= 1` at every critical point `kappa`.
Adversarial search drove the second-smallest `|u|` to 1.080244757 at degree four
and 1.037279478 at degree five. So the degree-three step "minimality gives two
small roots" does not generalise. The length bound must come from the metric
theorem's *sum* `|u|_(1) + |u|_(2) <= 2`, which held throughout (sup 1.999872 at
degree three), not from bounding each root separately.

**(c) Total inverse-ray tree length `T(v) <= n |v|^{1/n}`.** False. `T(v)` is
the total length of `f^{-1}([0, v])` over all `n` branches; the pure power
`z^n - r^n` attains equality, which made the bound look canonical. A degree-three
edge configuration reaches `T / (n |v|^{1/n}) = 1.065658`.

**(d) The merging pair is below average.** False, and badly. Writing `L(c)` for
the two descending branches that meet at `c`, the share `L(c) / T(v_c)` reaches
0.999066 against an average share of `2/n = 0.25` at degree eight. The two
branches that merge are the *long* ones, not typical ones — they are the pair
that had to travel to meet. Any argument that bounds the total tree and then
takes "two of `n`" is dead.

## 5. Curved branches, and why the hub selection cannot be by critical value

The descending-separatrix version of the same selection rule was measured. With `L(c*)` the total arc length of the two descending inverse-ray
branches at `c* = argmin |f(c)|`:

| degree | sup `L(c*)` | sup over the best hub |
|---|---|---|
| 3 | 1.997269 | 1.971385 |
| 4 | 1.891533 | 1.855019 |
| 5 | 1.773976 | 1.855547 |
| 6 | 1.715879 | 1.445329 |
| 7 | 1.549006 | 1.387942 |

This is a specific selection principle for the packet's priority-one producer —
minimal critical-value modulus — and it is untouched by the
`metric_selected_newton_branch_hub_counterexample`, which selects the hub the
critical-pair metric theorem supplies rather than the hub of least critical
value. On the packet's own balanced quintic the two rules disagree: the metric
hub `0` has `|f(c)| = 0.993907` and branch pair 2.151, whereas the
least-critical-value hubs have `|f(c)| = 0.354167` and branch pair 0.532.

Two further limits on hub selection came out of the same sweeps.

*Minimal critical value is not a sufficient selection rule for straight spokes.*
The objective restricted to `c* = argmin |f(c)|` is infinite — fewer than two
contained spokes at `c*` — at degrees 6, 8, 9 and 12. The degree-six and
degree-nine cases are the section-3 witnesses, where no hub works at all; at the
degree-eight case `c*` has only roots 1 and 4 contained, at distances 0.832414
and 1.155133, so a pair does exist there but it is neither the two nearest roots
nor the merging pair.

*The merging pair is not the right pair either.* At `c*` on that degree-eight
configuration the two descending branches reach roots 1 and 0 (stable under ODE
tolerances down to endpoint error `2.4e-13`), and root 0's straight spoke leaves
the lemniscate, reaching `|f| = 1.000013652510` at `t = 0.1637`. The pair that
works, roots 1 and 4 with total 1.987547, is not the merging pair.

So no rule of the form "pick the hub by critical value, then take the merging or
the nearest pair" can work. Selection has to be by containment, and by section 3
even that is not enough for straight spokes.

## 5b. The square-root resolution, and why its area bound does not reach

Setting `xi^2 = f(c) - w` resolves a simple critical point. The two branches
that merge at `c` become the two halves of **one** analytic curve

```
Z(0) = c,   f(Z(xi)) = f(c) - xi^2,   dZ/dt = -2 t exp(2 i theta) / f'(Z)
```

along `xi = t exp(i theta)`, with `Z - c ~ xi sqrt(-2/f''(c))` near `0` (the
velocity is `0/0` exactly at the critical point, so an integration must start
from that leading behaviour). At `theta_0 = arg f(c)/2` the level runs
monotonically, `f = f(c)(1 - t^2/|f(c)|)`, so the diameter of radius
`rho = |f(c)|^{1/2}` reaches the two roots and its image length **is** `L(c)`.
`resolved_diameter_length` in the engine reproduces `descending_pair` to `1e-10`
on every hub tested, so the reformulation is faithful.

The reason to want it: on a disk where `Z` is univalent, the image area is
bounded. `cap(f^{-1}(K)) = cap(K)^{1/n}` gives
`cap(f^{-1}(D(v, rho^2))) = rho^{2/n}`, and the isocapacitary inequality
`area <= pi cap^2` gives `Area(Z(D(0,rho))) <= pi |f(c)|^{2/n}`. The
angle-average of the squared diameter-image length is then on the metric scale
`2|f(c)|^{1/n} < 2` — exactly the Lean-checked critical-pair scale, arrived at
independently.

**Two measurements kill it.**

*The univalent disk is far too small.* `Z` is univalent only while
`D(v, rho^2)` avoids the other critical values. The fraction of the descent that
the branch-point-free disk covers, `rho_safe^2 / |f(c)|`, has median 0.04–0.12
across degrees 3–8 and reaches 1 only occasionally. So the area bound is a local
statement about a neighbourhood of the saddle, not about the descent.

*The descending direction is not favourable.* The natural hope was that
`theta_0` is better than average, since it runs into the deep part of the
lemniscate while other angles run out toward level `2|f(c)|`. Measured on the
safe disk, `L(c)` exceeds the angular mean in 40–50% of hubs, with ratio up to
1.485. The median ratio is 0.97–1.00: the descending direction is statistically
**average**, not favourable.

So the angle-averaged area bound cannot be specialised to the one direction that
matters, for the same reason the packet's `radial_lift_coarea_critical_ray_sampling_obstruction`
records in the value plane — except here the obstruction is measured rather than
inferred, and it is quantified by the coverage fraction.

## 6. A structural lemma worth formalising

Every component of `{|f| < t}` is simply connected. A bounded complementary
component would carry `|f| = t` on its boundary and `|f| >= t` inside, while
`|f|` is subharmonic and hence bounded by its boundary values; together these
force `|f| == t`, impossible on an open set.

Consequence: a critical point `c` with `f(c) != 0` merges two **distinct**
components of `{|f| < |f(c)|}` rather than closing a loop, so its two descending
branches reach two distinct roots, and the `n - 1` critical points induce a
spanning tree on the `n` roots. This is used implicitly whenever a hub is
assumed to join two different roots; it is an ordinary proof, not yet Lean.
`system.lib.formal_math_lemniscate.merging_pair_tree` checks the spanning-tree
consequence numerically, and `tests/test_formal_math_lemniscate.py` pins it.

## 6b. The corpus's strong statement, in invariant form

`MinimumCriticalNewtonHubLab.md` normalises by `R = max_j |z_j|`. The same
obligation is invariant under the full affine group if `R` is read as the
*circumradius* of the root set rather than the maximum modulus, which also makes
the equality class visible.
Under `z -> a + lambda z` the branch length `L(c)` scales by `|lambda|`, and so
does the circumradius `R` of the root set — the radius of the smallest enclosing
circle. So the natural form of the obligation is

```
        min over critical points c of L(c)   <=   2 R.                    (*)
```

This **implies** the target: roots in the open unit disk give `R < 1`, hence a
path of length below 2. Removing the origin and the scale from the statement
removes two dead directions from any search over configurations, and — more
importantly — it exposes the equality cases.

**Two equality families, and they are the same family.** The lab records
`z^n - r^n`; the quadratics below are a second, and both are affine conjugates of
`z^n - 1`.

*Every quadratic.* With `c = (z1+z2)/2` and `d = (z1-z2)/2`,
`f(c+u) = u^2 - d^2` and `f(c) = -d^2`, so

```
f^{-1}([0, -d^2]) = {c+u : u^2 in [0, d^2]} = {c + t d : t in [-1,1]},
```

which is exactly the segment from `z2` to `z1`. Hence `L(c) = |z1 - z2| = 2R`
for **every** monic quadratic — equality throughout, not just in a limit. This is
an ordinary proof, pinned numerically by
`test_every_quadratic_is_an_equality_case`.

*The extremal family.* For `z^n - r^n` at `c = 0` the branches are the `n` radii,
any two of which give `L = 2r = 2R`.

Both are `f` affinely conjugate to `z^n - 1`, so (\*) is conjecturally sharp with
a single equality class.

**No hub-by-hub argument can prove it.** The per-hub strengthening
`L(c) <= 2 max_k |z_k - c|` at *every* critical point is tight on both equality
families but false in general. A pinned degree-four witness (exact IEEE-754
literals in the verifier) reaches ratio `1.210001551`, with all four roots well
inside the disk — max modulus `0.782955` — and an admissible hub at
`|f(c)| = 0.0318`, so it is neither a boundary nor a level-one degeneracy. At
that same configuration the invariant ratio is only `0.306554`: the per-hub form
fails badly exactly where the invariant form has enormous slack. The selection
over hubs is therefore not a convenience of the proof; it is load-bearing.

**Adversarial evidence for (\*), from three independent min-objectives.**
Normalising to circumcentre `0` and `R = 1` removes the translation and scale
directions, and the search is run three ways: free over all critical points,
restricted to the least-critical-value hub, and restricted to admissible hubs.

| degree | free | least critical value | admissible only |
|---|---|---|---|
| 3 | 0.999999995 | 0.999999996 | 0.999999994 |
| 4 | 0.999998909 | 0.999998909 | 0.999997843 |
| 5 | 0.999934458 | 0.999940557 | 0.999934458 |

All three agree and none crosses. Two things distinguish this from the
straight-spoke near-miss that turned out false. First, the objectives are
independent and concur. Second — and this is the real difference — the supremum
sits at `1` **because an equality family reaches it**. A pinned value with no
equality case is an unexplained near miss; a pinned value with `z^n - 1`
attaining it is a sharp inequality.

The least-critical-value column tracks the free one at every degree, so for the
*branch* version that selection rule appears to attain the minimum — in contrast
to the straight-spoke version, where it fails outright from degree six (§5).

**The packet's priority-one aggregate, same treatment.** Maximising
`sum_c L(c) / (2h)` over admissible hubs, under a free objective, one penalised
toward few hubs, and a coalesced-critical-value seeding, gives 0.999999845,
0.999997627, 0.999912748, 0.999448305, 0.998493771 for degrees 3–7 — never
reaching one. The few-hubs objective drove the admissible hub count down to 1, 2,
4, 5, 6 respectively; at `h = 1` the aggregate is just `L(c)/2` with no averaging
help, and it still came in under (0.997058913 at degree three). The aggregate is
implied by (\*), so (\*) is the better target.

**Why this obligation is better posed than the straight-spoke one it replaces.**
A descending branch pair exists at every admissible critical point and is
automatically contained, since it descends in level — there is no analogue of the
containment failure that killed straight spokes at degree six, and no degenerate
"no admissible pair" mode. Only length can fail.

## 6c. Correction taken from the concurrent line, and the split of labour

The affine-invariant wording in §6b was **insufficient as stated** and has been
corrected in the packet by the concurrent Erdős 1041 line: the minimum must be
taken over *admissible* critical points, those with `|f(c)| < 1`. A short
inverse-ray pair at an inadmissible hub need not lie in the target lemniscate at
all, and rescaling the roots moves critical values, so "min over all critical
points" does not imply the target. See `admissible_branch_length_reformulation`.

That correction does not touch the **strong** completion tested in §6d. At the
minimum-critical hub Fekete gives `|f(c*)| <= R^n < 1` whenever the roots lie in
the open unit disk, so `c*` is automatically admissible and the strong statement
needs no separate qualifier.

The two lines are working different completions and should stay separate:

| | statement | line |
|---|---|---|
| weak | `sum over admissible hubs L(c) <= 2 R m` | `admissible_critical_forest_tangent_support_reduction` — exact endpoint-deficit plus signed-curvature charge, Blaschke/Riemann–Hurwitz component reduction |
| strong | `L(c*) <= 2 rho`, `rho = |f(c*)|^{1/n}` | this note — falsification pressure, complete cubic sweep, cusp structure |

The strong statement implies the weak one pointwise at `c*` but is flagged in
`MinimumCriticalNewtonHubLab.md` as possibly false, so neither supersedes the
other.

## 6d. Evidence on the strong completion

Verifier: `scripts/check_erdos1041_minimal_hub_metric_scale.py`.

The dedicated falsifier `critical-scale-normalized-minimum-critical-newton-hub`
had reached `0.9495242630078684` on a canonical degree-five run. Five
independent seedings — near-extremal, uniform, clustered, near-collision, and a
combined restart — reach `0.999994283` at degree three without crossing one.

The degree-three case is closed by a **complete** parameter sweep rather than
sampling. Normalising gives `P(u) = u^3 + s u^2 + 1` with critical points `0`
and `-2s/3` and `P(-2s/3) = 1 + 4 s^3 / 27`, so minimality is exactly
`|1 + 4 s^3 / 27| >= 1`: 2328 admissible parameters, maximum branch pair length
`1.997967707`, zero violations.

Two structural facts came out of it.

*The extremum is a cusp.* At `z^n - r^n` the critical point at the origin has
multiplicity `n-1`. Splitting it drops the ratio by a fractional power of the
perturbation — at degree five, `1e-9` gives 0.99648, `1e-6` gives 0.98012,
`1e-3` gives 0.88553. A second-order variational argument at the extremum will
not see the right behaviour.

*The cusp exponent is `1/(n-1)`.*
[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) adopts the cusp mechanism
recorded above and states that any perturbative attack on the `D`-near-one side
"must handle a fractional-power response, which is a materially harder object
than a Hessian". It does not give the exponent. Fitting `log(1 - M)` against
`log delta` over eight perturbation scales returns

| degree | 3 | 4 | 5 | 6 |
|---|---|---|---|---|
| fitted | 0.5126 | 0.3267 | 0.2637 | 0.2043 |
| `1/(n-1)` | 0.5000 | 0.3333 | 0.2500 | 0.2000 |

so the response is Hölder of order `1/(n-1)`. That is the spacing exponent of a
multiplicity-`n-1` critical point splitting into `n-1` simple ones, and it is the
*same* exponent as in that file's own `T* <= D^{1/(n-1)}`. So the object a
`D`-split proof needs is not a Hessian but a Hölder-`1/(n-1)` stability estimate
for the Fekete maximiser, with the order now measured rather than described.

*The level condition alone is not the content.* `|f(c)| <= R^n` applied at an
arbitrary critical point fails on about one percent of hubs, reaching 1.0556 at
degree six. What the discriminant/Fekete sandwich supplies is a bound at the
*minimum*-critical hub, and it is minimality — every component of
`{|f| < |f(c*)|}` still holding exactly one root — that the strong completion
depends on.

*Engine boundary, recorded because it bit.* At a degenerate critical point the
substitution `f(z(u)) = (1-u^2) f(c)` is the wrong local model: all `n`
preimages are equidistant from the hub and the field is stiff at the start, so
`descending_pair` under-reports. On `z^n - r^n` it returns 1.7989 against the
true `2r = 1.8` at degree six, and the deficit does not shrink with the start
offset. The direction is conservative for the conjectures, but equality families
must be asserted from their ordinary proofs, not from the integrator.

## 6e. The admissible-forest aggregate, tested where it is tight

[CriticalTreeLengthCharge.md](CriticalTreeLengthCharge.md) states the sufficient
aggregate `sum_{c in A} L(c) <= 2 R m` and reports a deterministic maximum
normalized ratio of `0.988850245227178` over 521 complete admissible-hub sets.
Those sets are bulk-drawn. But (A) is **tight** on `z^n - r^n`, and
[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) shows the hard
configurations are the near-Fekete ones, so the bulk maximum is not the relevant
number: a violation would live in the shell.

Measured inside the shell — roots `r(1+a_k)exp(i(2 pi k/n + t_k))` with `r` just
below one, at eight perturbation scales — (A) holds at every scale and climbs
monotonically toward one:

| degree | worst ratio in the shell |
|---|---|
| 3 | 0.999984770 |
| 4 | 0.999094123 |
| 5 | 0.995004633 |
| 6 | 0.989932789 |

An order of magnitude closer to the boundary than the bulk figure, in the regime
that matters, and still no crossing.

**A measurement risk that had to be ruled out, and was.** Near-Fekete hubs are
near-degenerate, and §6d records that `descending_pair` under-reports at an
*exactly* degenerate hub. An under-reported aggregate would look safe precisely
where it is tightest. Every arc here is therefore integrated twice — once by the
level substitution and once through the square-root resolution
`xi^2 = f(c) - w`, an independent route. They agree to about `1e-15` down to
perturbation `1e-4`, degrading only to `4e-8` at `1e-7`. The under-report does
**not** reach the shell: the split hubs there are simple, and only the exactly
degenerate case suffers. So the shell numbers can be read.

Verifier: `scripts/check_erdos1041_aggregate_near_fekete.py`, which fails if any
shell configuration reaches ratio one, if the two integrators disagree by more
than `1e-6`, or if a shell configuration stops having `n-1` admissible hubs.

## 6f. An exact polynomial representation of the chord deficit

[TurningFloorRefutation.md](TurningFloorRefutation.md) reduces MIN to
`D(c) < 2 - (d1 + d2)` through the chord-deficit identity, and says plainly that
"the content would be an estimate for `D(c)` in terms of the polynomial, and none
is offered". Here is the exact representation, which is where such an estimate
has to start.

Parametrise a descent half-edge by the value radius: `f(z(rho)) = rho e^{i theta}`,
so `dz = e^{i theta} d rho / f'(z)`. Integrating,

```
L_A    = integral_0^{|v|} |1/f'(z(rho))| d rho
c - a  = e^{i theta} integral_0^{|v|} (1/f'(z(rho))) d rho
```

and therefore the chord deficit of that branch is **exactly the
triangle-inequality defect of the complex integral of `1/f'` along the descent
ray**:

> **(TD)**  `D_A = integral |1/f'| d rho  -  | integral (1/f') d rho |`.

Since `f` is monic, `f' = n prod_j (z - c_j)` over the `n-1` critical points, so
both the length and the deficit are integrals of the reciprocal product of
distances to the **critical points** — not the roots:

> **(CP)**  `L(c) = (1/n) sum_{branches} integral_0^{|v|} d rho / prod_j |z(rho) - c_j|`.

Verified against the tracked branches: `(CP)` matches the integrated arc length
and `|c - a|` matches `|integral (1/f') d rho|`, both to `1e-9` — the start
truncation — while `L(c) - (d1 + d2) = D(c)` closes to `1e-16`.

Two things this buys. `D_A` is now a statement about how much `arg(1/f')`
rotates along one ray, and `arg f' = sum_j arg(z - c_j)`, so the deficit is
driven by the angles the branch subtends at the **critical points**, weighted by
`ds`. And the `L^2` form the refutation asks for is immediate: writing
`beta = arg(integral (1/f') d rho)`,

```
D_A = integral |1/f'| (1 - cos(arg(1/f') - beta)) d rho
    <= (1/2) integral |1/f'| (arg(1/f') - beta)^2 d rho,
```

which is a weighted `L^2` turning bound on `sum_j arg(z - c_j)` — exactly the
shape named as sufficient, now written against the polynomial's own critical
divisor. No estimate is claimed; the representation is elementary and the
content is still missing.

## 6g. The start-direction defect, measured rather than assumed

[TurningFloorRefutation.md](TurningFloorRefutation.md) reports that
`descending_pair` returns start *directions* up to 50 degrees wrong and warns
that angular work must not use them. Acting on that, the engine now carries
`branch_start`, which Taylor-expands `f` at the hub by synthetic division and
solves `a_n d^n + ... + a_2 d^2 + u^2 v = 0` in `d = z - c`, so that `a_2 d^2`
cancels against `u^2 v` rather than against `|v|`.

**The conditioning gain does not show up.** Over 778 hubs spanning generic and
near-Fekete configurations down to perturbation scale `1e-7`, the two locators
agree in arc length to `1e-13` and give start directions equal to within `1e-13`.
What the "opposite directions" test actually measures is not locator error: at
finite `u` the two descent directions are opposite only to order `u`, with
correction `O(u a_3 / a_2)`, and `a_2 = f''(c)/2` tends to zero as the hub
approaches a degenerate one. Measured deviation from exactly-opposite at
`u = 1e-6`: `1.6e-6` rad generic, `6.7e-2` rad on a near-Fekete shell at scale
`1e-6`, `1.7e-1` rad at scale `1e-7` — identically for both locators.

So the operative rule is a step-size criterion, not a locator choice: near a
degenerate hub, `u` must be small compared with `|a_2/a_3|` times the angular
accuracy wanted. `descending_pair` keeps its original default, since changing it
would move landed receipts for no measured gain; `branch_start` is exposed and
`start_direction` is now reported. One real bug was found and fixed on the way —
the synthetic-division remainder is the last coefficient plus the final carry,
and taking the last coefficient alone is correct only for a shift of zero, which
no test centred at the origin can see.

## 6h. The hard regime has a universal local model, and MIN survives it

[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) shows the hard
configurations are the near-Fekete ones; §6d measures the response there as a
cusp of order `1/(n-1)`. Together those identify the local model.

Perturb the extremal family, `f = z^n - r^n + eps*g`. Then
`f' = n z^{n-1} + eps g'`, so the `n-1` critical points satisfy
`z^{n-1} = -eps g'(0)/n` to leading order: they sit at radius
`(eps|g'(0)|/n)^{1/(n-1)}` — exactly the measured cusp scale — equally spaced in
angle. Zooming there sends *every* perturbation `g` to the same two-term model,
and the scaling `z -> mu z`, which sends `lambda -> lambda mu^{1-n}` and
`c -> c mu^{-n}`, uses its rotation freedom to normalise `lambda` real and
nonnegative. The hard regime is therefore the three-real-parameter family

```
f(z) = z^n + lambda z - rho e^{i gamma},      lambda >= 0.
```

The corpus already names it, in negative result 8, as the family where all
critical-value arguments coalesce. So the near-extremal case of MIN is a
**complete parameter sweep**, not a sample.

| degree | cells | sup min-hub `L/2R` | sup max-hub `L/2R` | cells with a hub over 1 |
|---|---|---|---|---|
| 3 | 113 | 0.999999996 | 1.0269977 | 23 |
| 4 | 116 | 0.999996778 | 1.0222785 | 46 |
| 5 | 113 | 0.999914693 | 1.0452022 | 87 |
| 6 | 116 | 0.999470405 | 1.0322773 | 52 |

Two readings. MIN holds across the whole family, and its supremum is attained at
`lambda = 0` — the exactly extremal family, where equality is already known, so
the supremum is *explained* rather than pinned. And individual hubs exceed one in
20–77% of cells, so the minimum over hubs is load-bearing, now witnessed by
hundreds of configurations on an exact family instead of one counterexample.

**Claim boundary.** This is the leading-order zoom. Verifying MIN on the model
does not prove MIN near the extremal family; that needs uniform control of the
error between a polynomial and its model, at the scale `1/(n-1)`. What it does is
reduce the regime where every previous mechanism failed to a compact, completely
searchable space, and confirm MIN survives there.

**A closed form that is not there.** At a fixed `lambda = 1e-6` the ratio `D/S`
reads 0.29733, 0.24413, 0.20870, 0.18233 for degrees 3–6; inverting and
subtracting `n log 2` gives 1.2839, 1.3236, 1.3258, 1.3257, which looks
convergent and suggests `D/S = 1/(n log 2 + kappa)`. It is an artifact. Taking
`lambda -> 0` at each degree separately, `kappa` keeps falling — 5.50, 1.51,
1.28, 1.21, 1.16, 1.12, 1.08, 1.05 for degrees 3 to 10 — because different
degrees reach their asymptotic regime at different `lambda`, so comparing them at
one fixed `lambda` compares different stages of the same limit. Recorded so the
detour is not repeated.

## 7. Claim ceiling

Both refutations eliminate *straight two-spoke paths through a single critical
point*. Neither touches curved descending branches, non-critical hubs, or
multi-segment paths, and neither refutes Erdős #1041 — the same witnesses carry
short curved paths.

The sublevel refutation rests on exact integer root data but locates the
quartic's critical points numerically (float64 plus a 60-digit Newton pass), not
by exact rational Rouché disks. The degree-six and degree-nine witnesses are
exact IEEE-754 data rather than rational data, so they are reproducible but not
symbolic; certifying them exactly needs the same Rouché-disk machinery. The separation margins are `1.72e-5` and
`1.96e-5` on the second spoke, and `1.22e-3` on the inadmissible hub, so a
certified enclosure of radius below `1e-7` would close the gap. Everything in
section 3 is finite evidence for an open statement. Erdős #1041 remains open.
