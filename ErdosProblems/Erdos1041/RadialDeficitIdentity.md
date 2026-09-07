# Erdős 1041: the radial deficit identity, and what it refutes

Status: two exact elementary results, two refutations, two instrument defects, and
an independent measurement of a constant that belongs to a concurrent line of
work (§2b). Erdős #1041 remains open. 2026-08-24.

What is claimed here as new: the origin-centred decomposition of `L(c)` with no
indefinite-sign term (§1), its exact representation against `z f'/f` (§1b), the
refutation of the strong form (§1, §7), the refutation of the `L^infinity`
radial turning bound (§2), and the two branch-tracing defects in §5b and §5. Two
numbers from earlier drafts are retracted in §7. The hard-regime
sign statement is **not** claimed here — see §2b.

Verifier: `scripts/check_erdos1041_radial_deficit_identity.py`.

## 1. The identity

Let `f` be monic with all roots in the closed unit disc, `c` a simple critical
point whose two descent branches reach distinct roots `a` and `b`, and let `L(c)`
be the total length of the branch pair. Measure position from the origin.
Traverse each half **outward from `c`** and write `psi` for the angle between the
position vector and the unit tangent, so that `cos psi = d|z|/ds`. Integrating
that over each half gives `int cos psi ds = |a| - |c|` and `|b| - |c|`, hence

```text
L(c) = (|a| + |b|) - 2|c| + D(c),        D(c) = int (1 - cos psi) ds >= 0.
```

That is the whole proof. It is the fundamental theorem of calculus applied to
`|z(s)|`; it needs no properness, no conformality, and no hypothesis on `f`
beyond `c` being a simple critical point with a branch pair reaching two roots.
If a half passes through the origin, `|z(s)|` fails to be differentiable at that
one parameter but stays Lipschitz with `| d|z|/ds | <= 1`, so the integration is
unaffected and `1 - cos psi` remains bounded in `[0, 2]`; the identity is not
disturbed.

**Every term on the right is signed.** `D(c) >= 0`. `2|c| >= 0`. And
`|a| + |b| <= 2R` where `R = max_k |z_k|`. So the target `min_c L(c) <= 2R`
becomes, verbatim and with no inequality spent,

```text
(RD-slack)     D(c)  <=  2|c|  +  ( 2R - |a| - |b| )     at some admissible c.
```

Both terms on the right are nonnegative credits. The obligation is an **upper
bound on a nonnegative quantity** — which is the shape an estimate can have.

**The strong form is false.** Dropping the second credit gives
`(RD): D(c) <= 2|c| at some admissible c`, which would also imply #1041 and is
much cleaner. It does not hold. Adversarial hill-climbing on
`min over admissible c of (D(c) - 2|c|)` breaks it at degree three (`+0.009463`)
and degree four (`+0.011440`), with the target `min_c L(c) - 2R` still strictly
negative at both witnesses (`-0.879`, `-1.316`). So the second credit is
load-bearing: an argument may not discard how much shorter the reached pair is
than the extremal pair.

Read those margins with the discipline `negative_results` entry 19 demands. They
are about `0.01`, which is nine orders above the identity's numerical floor of
`4e-12` on the same traces, and the search runs loose while the winner is
re-scored at `rtol = 1e-12`. But they are not wide, they are not exactified, and
an earlier run of this same search reported `+0.219` — twenty times larger —
before the branch-tracing defect in §5b was found and fixed. **That `+0.219` is
retracted.** The refutation survives the repair; its margin did not.

### Why this is worth having

The directory already carries two exact decompositions of `L`.

* `research_packet.json::exact_results::chord_deficit_polynomial_representation`:
  `L(c) = (d_1 + d_2) + D_chord(c)`, deficit measured against each branch's own
  **chord**. There the budget is `d_1 + d_2`, and the metric theorem gives
  `d_1 + d_2 <= 2 mu^{1/n} <= 2R` only for the two *nearest* roots, not for the
  pair the branches actually reach — gap 1 of
  [FirstMergeReductionState.md](FirstMergeReductionState.md).
* [CriticalTreeLengthCharge.md](CriticalTreeLengthCharge.md):
  `2R - L = (R + <a,U_a>) + (R + <b,U_b>) + K`, with
  `K = int kappa <z,N> ds` a **signed** curvature charge. `research_packet.json`
  entry 21 records `K` reaching `-0.1613` normalised, so the open producer asks
  for nonnegativity of a combined charge whose curvature part has no sign.

The radial identity removes both difficulties at once. The budget is
`|a| + |b|`, which is bounded by `2R` for *whichever* pair the branches reach —
the merge-pair-versus-nearest-pair gap does not arise. And the indefinite `K` is
replaced by an explicit nonnegative credit `2|c|` against a nonnegative deficit.
The obligation becomes an **upper bound on a nonnegative quantity**, which is
the shape an estimate can actually have.

The origin is load-bearing, exactly as it is elsewhere in this problem: `D`,
`|c|` and `R` are all measured from it. The freedom to move it is the same
freedom as the free hub of
[TwoSegmentContainmentReduction.md](TwoSegmentContainmentReduction.md) — any
origin `o` with `|a-o| + |b-o| < 2`, i.e. any point of the same open ellipse,
gives a valid instance.

### The two deficits compare

The directory's chord decomposition and this radial one are two readings of the
same `L(c)`. Equating them,

```text
(d_a + d_b) + D_chord(c)  =  (|a| + |b|) - 2|c| + D_rad(c),
```

and `d_a = |a - c| >= |a| - |c|` on each side gives, with no further work,

```text
D_chord(c) <= D_rad(c).
```

So the radial deficit is the weaker of the two — as it must be, the chord being
the better straight-line reference for each half. The compensation is that the
radial budget is correspondingly larger, by exactly
`2|c| - |a| - |b| + d_a + d_b >= 0`. Neither form dominates; they differ in what
they make estimable. The chord form's deficit is an integral against the
CRITICAL divisor (`exact_results` entry 38); the radial form's is an integral
against `z f'/f`, i.e. the ROOT divisor with a positional weight, and it comes
with the explicit credit `2|c|`.

### The credit that may not be dropped

`2R - |a| - |b|` measures how far the two roots the branches actually reach sit
inside the extremal circle. It vanishes on both equality families and on every
configuration with all roots of equal modulus, so it is invisible to the cases
that make the constant sharp — and exactly for that reason it is easy to drop by
mistake. In the hard regime it is `O(eps)`, negligible beside the `O(rho)`
credit `2|c|`, so §2 below is unaffected; but in the bulk it is what keeps the
statement true.

### Equality class

Both recorded equality families make all three terms vanish together.
For a monic quadratic with the origin at the midpoint, `c = 0`, the branch pair
is the root segment, `D = 0`, `|a| + |b| = 2R`. For `z^n - r^n`, the admissible
hub is the origin, the branches are radii, `D = 0`, `|c| = 0`,
`|a| + |b| = 2r = 2R`. So (RD) holds with equality on the equality class, which
is the correct behaviour for a sharp statement and means no uniform positive
margin can exist — consistent with `negative_results` entries 1 and 28.

## 1b. What the deficit is, against the polynomial

The deficit is not an abstraction; it has an exact representation in the same
coordinates as the length. On a descent branch `f = rho e^{i theta}` with
`theta` fixed, `dz = e^{i theta} drho / f'`, so `ds = drho/|f'|` and
`d|z| = Re(conj(z) e^{i theta}/f') drho/|z|`. Traversing outward from the saddle,
`cos psi = -cos(arg(f/(z f')))`, hence `1 - cos psi = 1 + cos(arg W)` with

```text
W(z) = z f'(z)/f(z) = sum_j z/(z - z_j),

D(c) = int_0^{|f(c)|} 2 cos^2( arg W(z) / 2 ) drho / |f'(z)|,   summed over both halves.
```

Checked against the traced deficit to `5e-12` (`--part deficit-representation`).

Two things follow immediately.

* **`D = 0` exactly when `W` is negative real along the branch**, which is exactly
  when the branch is radial. On `z^n - r^n` every radius has
  `W = n z^n/(z^n - r^n) < 0`, so `D = 0` there — the extremal family is
  characterised, not merely computed.
* The integrand is `2 cos^2(arg W / 2)`, so the deficit is small precisely where
  `arg W` is near `pi`. The estimate the problem needs is therefore an estimate
  of how far `sum_j z/(z - z_j)` stays from the negative reals along a descent
  branch — a statement about the polynomial's logarithmic derivative weighted by
  position, with no curvature and no chord in it.

Compare `research_packet.json::exact_results` entry 38, which writes the CHORD
deficit as the triangle-inequality defect of `int 1/f'` and observes that length
and deficit are integrals against the critical divisor. The radial deficit
instead lands on `z f'/f`, i.e. on the ROOT divisor with a positional weight.

## 2. The hard regime is a one-parameter family

[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) and
[NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) locate the surviving difficulty at
`f = z^n - m + eps h`, whose `n-1` simple critical points sit on a
regular (n-1)-gon of radius `rho = (eps |h'(0)| / n)^{1/(n-1)}`. Since
`1/(n-1) < 1`, `rho >> eps`: the near-field response dominates every `O(eps)`
far-field correction. That is the cusp, and it is what makes the regime hard.

Zoom `z = rho xi`. Then `f(rho xi) = f(0) + rho^n (xi^n + lam xi)` to leading
order, with `lam = f'(0)/rho^{n-1}` normalised to `|lam| = n`; the discarded
coefficients enter at relative order `rho^{j-1}`, `j >= 2`. Descending `|f|` is
descending `Re(sigma H)`, `sigma = 1/f(0)`, `H = xi^n + lam xi`, so the branches
are level curves of `Im(sigma H)`.

Feeding the local model into the identity of §1 gives, per saddle,

```text
|a| + |b| - L(c_k)  =  -rho * kappa_k + o(rho),

kappa_k  =  D_model(k) - 2|xi_k|  =  lim_{Lam -> inf} ( branch length truncated at |xi| = Lam  -  2 Lam ).
```

So `kappa_k` is the **renormalised excess length** of the saddle's separatrix
pair: the amount by which it is longer than the two radii of the same radial
extent. In this regime the second credit `2R - |a| - |b|` is `O(eps)`, negligible
beside `rho`, so (RD-slack) here reduces to the strong form: the hard-regime
obligation is exactly `min_k kappa_k <= 0`.

Two normalisations are available — `xi -> c xi` fixes `|lam|` and one phase, and
the residual `(n-1)`st roots of unity make the remaining phase periodic — so the
model has **one essential real parameter per degree**, of period `2 pi / n`,
with conjugation acting as `beta -> -beta`. The fundamental domain is
`[0, pi/n]`, whose two endpoints are the conjugation-symmetric configurations.

### Why an L-infinity bound cannot work, and what that fixes

The representation invites the obvious estimate: if `|arg W - pi| <= 2 alpha`
along the branch pair then `2 cos^2(arg W/2) = 2 sin^2(alpha) <= 2 alpha^2`, so
`D <= 2 alpha^2 L`, and (RD) would follow from `alpha^2 <= |c|/L`. That dies in
the hard regime, and instructively. There `|c| = rho` and `L -> 2`, so the
criterion would demand `alpha <= sqrt(rho/2) -> 0`; but the branch pair turns by
`O(1)` within `|z| ~ rho` of the origin, so `alpha = O(1)`. The uniform bound is
off by the whole cusp.

What that shows is not that the deficit is large — it is `O(rho)`, the same order
as the credit — but that **all of it is concentrated in the near field**, on the
scale `rho` where the credit lives. So the estimate cannot be uniform along the
branch; it has to be the near-field integral itself. That is exactly what
`kappa` is, and it is why the local model below is the content of the hard
regime rather than a convenience. It is also the radial-coordinate version of
the lesson already recorded for the chord deficit: `negative_results` entry 25
kills turning inflation `L <= (d1+d2)/cos(alpha_max/2)` for the same reason, and
`exact_results` entry 38 notes that a weighted `L^2` bound is what the chord
form needs where the refuted route used `L^infinity`.

## 2b. This constant is not new — attribution, and a 17-digit cross-check

While this note was being written, a concurrent line of work in this same
directory reached the same constant from the other side.
`PerHubChargeSign.md` and `ConeBoundMonotoneFunctional.md` (both dated
2026-08-24, both **uncommitted at the time of writing** and owned by another
session) define `kappa_n = (2R - min_c L(c))/rho` on the same near-field model
and report a *proof* that `kappa_n > 0` at every degree, via a cone bound and a
monotone harmonic functional. That is the same object as the `kappa_k` here:
since `2R - |a| - |b| = O(eps) = o(rho)` in this regime,
`kappa_n = -min_k kappa_k`. **The hard-regime sign statement is therefore
theirs, not this note's**; what follows is an independent measurement of it, and
the claim status of their proof is `reported_prior` — it has not been checked
here.

The two implementations are genuinely independent — different parametrisation,
different integrator, different deficit functional — and they agree. On
`PerHubChargeSign.md`'s degree-three witness
`f = z^3 - (9/10)^3 + eps e^{6i/5} z` at the hub it names:

| eps | branch length, this note | branch length, `PerHubChargeSign.md` |
|---|---|---|
| `1e-6` | `1.8000294939849710296` | `1.8000294939849717352` |
| `1e-8` | `1.8000029373198827010` | `1.8000029373198(83)` |

Seventeen significant digits at `eps = 1e-6`. Both also agree that this hub is a
genuine per-hub violation, and the minimum over hubs at the same configuration
is `(L - 2R)/rho = -0.6496`, i.e. `kappa_n = +0.6496 > 0`, so the target holds
there. One difference worth naming: `PerHubChargeSign.md` takes `R` to be the
circumradius of the root set, this note takes `R = max_k |z_k|`. Theirs is the
smaller and so the stronger claim; the per-hub violation stands under both.

## 3. What the measurement says

`--part local-model`, sweeping that single parameter:

| n | `2\|xi_k\|` | worst (largest) `min_k kappa_k` | at |
|---|---|---|---|
| 3 | 1.154701 | **-0.351041** | symmetric endpoint |
| 4 | 1.259921 | -0.648935 | symmetric endpoint |
| 5 | 1.337481 | -0.841662 | symmetric endpoint |
| 6 | 1.397654 | -0.977598 | symmetric endpoint |
| 7 | 1.446040 | -1.080010 | symmetric endpoint |
| 8 | 1.485994 | -1.160731 | symmetric endpoint |

The margin is **uniformly negative and grows with the degree**, and in the
sampled families the maximiser sits at one of the two conjugation-symmetric
endpoints rather than in the interior. This is a measurement of the constant
attributed in §2b, on the reduced one-parameter family, by an independent
implementation. Individual saddles do cross zero — `max_k kappa_k` reaches
`+0.34` at `n = 3` — so the minimum over hubs is load-bearing here too, in
agreement with `negative_results` entry 20.

At the conjugation-symmetric saddle the separatrix pair is the real algebraic
curve `Im H = 0`, which in polar form is exactly
`u(theta)^{n-1} = -lam sin(theta)/sin(n theta)`, `lam = +-1`. Integrating that
gives a closed-form cross-check; at `n = 4, lam = 1` the curve is
`y^2 = x^2 + 1/(4x)`, `x <= -4^{-1/3}`, and three independent computations —
Cartesian quadrature, polar quadrature, and the arclength ODE — agree:

```text
kappa = -0.7144658694 / -0.7144658699 / -0.7144658820
```

The radial deficit at that saddle behaves like `pi/n` for large `n`
(`n * deficit` = 2.06, 2.18, 2.29, 2.38, 2.51, 2.61, 2.87, 3.10 at
`n = 3,4,5,6,8,10,20,50`), so `kappa -> -2` as `n -> inf`.

**Why the recorded supremum tends to one.** The previous sweep of the
three-parameter local family reported `sup min-hub L/2R` rising to `1` as
`lambda -> 0`, with the supremum attained there. The identity explains it: the
margin is `rho |kappa|`, and `rho -> 0` on that limit while `|kappa|` stays
bounded away from zero. The degeneracy is in the *scale*, not in the shape.

## 4. The matched asymptotic, checked against real polynomials

`--part near-fekete` builds genuine `f = z^n - 0.999^n + eps(...)`, traces every
branch pair, and compares `(|a| + |b| - L(c))/rho` with `-kappa`. The claim is
not "the numbers are close" but "the residual is the `O(rho)` correction", so
that is what is tested: `error/rho` stays below `1.80` at every saddle and every
degree 3 to 5, and shrinking `rho` shrinks the error in proportion — median ratio
`0.997` against each degree's own `rho` shrink factor, which differs by degree
since `rho ~ eps^{1/(n-1)}`. The exact identity of §1 closes to `4e-12` on the
same traces.

## 5b. A second, worse instrument defect — and how it hid

The first defect (§5) is loud once you look for it. This one was silent, it
corrupted every trace in this note's first draft, and it inflated a refutation
margin by a factor of twenty.

Starting off the saddle at `w = +-delta` needs a point on the branch. The obvious
way is to Newton-solve `f(z) = f(c)(1 - delta^2)` from the linearised guess. For
the `delta` this actually needs — small enough that the skipped arc is negligible
beside `rho` in the near-Fekete regime — `1 - delta^2` **rounds to `1` in double
precision**. The target is then exactly `f(c)`, Newton is solving a double root,
and it walks back onto the saddle. The offset silently stops being an offset.

Symptoms, in the order they appeared:

* the identity of §1 held only to `1e-7`, when it is exact;
* two `near-fekete` rows came back with the **wrong sign** against the model;
* one equal-modulus row reported `2|c| - D < 0`, which this note briefly wrote up
  as (RD) failing on a random draw;
* the strong-form search reported `+0.219` where the repaired tracer gives
  `+0.009`.

None of those look like an integrator problem. Three of the four look like
mathematics.

The fix is to stop solving and start inverting. The local expansion gives the
branch point with no cancellation at all:

```text
z = c + s w (1 + alpha w) + O(w^3),   s = sqrt(-2 f(c)/f''(c)),
alpha = f'''(c) s^3 / (12 f(c)).
```

With `delta = 1e-9` the skipped arc is `~1e-7` even at a near-degenerate hub, and
seeding its exact straight-segment contribution
`|z0 - c| - (|z0| - |c|)` into the deficit closes the identity to `4e-12` —
from `1e-7`, a factor of `2.4e4`.

**What should have caught it earlier.** The identity of §1 is exact, so its
residual is a free, always-available instrument check; a `1e-7` gap under an
`rtol = 1e-12` integrator was already telling me the start was wrong, and I read
it as tolerance. The lesson generalises past this problem: when a probe has an
exact identity available, its residual is not a tolerance budget to be widened
until green — it is the instrument's own error bar, and it should be driven to
machine precision before any number the probe produces is quoted.

The `near-fekete` guard was also wrong in a way worth naming. It scored relative
error against `kappa`, which is meaningless at the saddles where `kappa` is near
zero — one such row reported `3080%`. The prediction is that the residual is the
`O(rho)` correction term, so the guard now checks two things instead: that
`error/rho` stays bounded (worst `1.80`), and that halving `rho` halves the error
(median ratio `0.997`). That tests the *order* of the correction, which is what
the reduction actually claims.

## 5. Instrument defect worth recording

The resolved parametrisation `f(z) = f(c)(1 - w^2)` is the right one — it is
regular at the saddle and at both roots — but **it must not be started at
`w = 0`**. The equation is degenerate there, both sign choices relax onto the
same solution, and the two halves silently collapse: the traced pair reaches a
*single* root, with identical geometry on both halves, while the total length
still looks plausible. Worse, the failure is invisible to the obvious
known-answer test: on a monic quadratic the collapsed trace still returns
exactly `2d`, because the two halves of that branch are congruent. The check
script starts at `w = +-delta` with a Newton-refined point of the branch, with
`delta` scaled so the skipped initial segment is below `1e-12` in length, and
reports which root each half reaches.

This is a second member of the instrument class named in
`negative_results` entry 34 — a defect that biases the near-Fekete regime
specifically and passes a symmetric known-answer test.

## 6. Where the difficulty actually sits

The identity localises the problem more sharply than the earlier dichotomy
language suggests, because the second credit is not merely small on the hard
family — it is **identically zero on a whole stratum**.

If every root has the same modulus `R`, then `|a| = |b| = R` for *whichever* pair
the branches reach, so `2R - |a| - |b| = 0` exactly, at every hub, with no
asymptotics. On that stratum

```text
(RD)  D(c) <= 2|c|  at some admissible c      IS      the target,
```

not a strengthening of it. So the strong form is not merely a convenient
simplification that happens to fail; it is exactly the equal-modulus case of the
problem, and the degree-three refutation of §1 necessarily lives off that
stratum.

Measured on the common circle `|z| = 0.99`, at the minimising admissible hub:

| configuration | Fekete defect | `2R - L` | `2\|c\| - D` | `2R - \|a\| - \|b\|` |
|---|---|---|---|---|
| `n=4` arc, spread 0.6 | 0.0585 | 1.051129 | 1.051129 | 0 |
| `n=4` arc, spread 0.3 | 0.0000 | 1.514587 | 1.514587 | 0 |
| `n=4` arc, spread 0.12 | 0.0000 | 1.793469 | 1.793469 | 0 |
| `n=5` arc, spread 0.6 | 0.0078 | 1.216029 | 1.216029 | 0 |
| `n=5` arc, spread 0.3 | 0.0000 | 1.605275 | 1.605275 | 0 |
| `n=6` arc, spread 0.12 | 0.0000 | 1.855441 | 1.855441 | 0 |
| `n=8` arc, spread 0.12 | 0.0000 | 1.886506 | 1.886506 | 0 |

The exact regular polygon is deliberately **not** in that table. For `z^n - R^n`
the only critical point is the origin with multiplicity `n-1`, so there is no
simple hub to measure; `np.roots` splits the multiple root into `n-1` spurious
points at `1e-4` to `1e-3` from the origin and the branch pair through a spurious
hub is not a measurement of anything. Earlier drafts of this note tabulated those
rows as small positive margins; on the repaired tracer two of them come out
*negative*, which is the clearest possible sign that they were never data. The
right statement there is the exact one from §1: the branch pair is two radii,
`D = 0`, `|c| = 0`, `|a| + |b| = 2R`, and (RD) holds with **equality**.

So: equality at the regular polygon, and margins above `1.0` everywhere else on
the circle.

So the difficulty is not "the hard regime" as a fuzzy neighbourhood. It is:

1. the common-modulus stratum, where (RD) is the whole problem; and
2. within that stratum, only the regular polygon, where (RD) holds with equality.

Off the stratum the reached-pair credit is available, and it is substantial.
Six random unequal-modulus draws at degrees 4 to 6, same probe:

| n | `2R - L` | `2\|c\| - D` | `2R - \|a\| - \|b\|` |
|---|---|---|---|
| 4 | 1.241329 | +0.370722 | +0.870607 |
| 4 | 1.465783 | +1.174173 | +0.291610 |
| 5 | 1.875441 | +1.475986 | +0.399456 |
| 5 | 1.674894 | +0.992014 | +0.682881 |
| 6 | 1.493719 | +0.960883 | +0.532836 |
| 6 | 1.559014 | +0.659267 | +0.899747 |

On these draws the reached-pair credit contributes between a fifth and three
quarters of the total margin. **A retraction belongs here.** Before the §5b
repair this table carried a row with `2|c| - D = -0.007420`, and this note read
it as (RD) failing on a *random* draw. It was a tracer artifact; on the repaired
tracer that configuration reads `+0.992014`. Off the stratum (RD) fails only
under adversarial search, not on random draws. That is a much narrower target than "prove an estimate for
`D(c)`", and it is the same place `HardRegimeIsNearFekete.md` puts the difficulty
— reached here from an exact identity rather than from a stability estimate.

## 7. Claim boundary

* §1 is an **ordinary complete proof**, elementary, not Lean-checked. Novelty is
  not claimed for the identity itself; it is the fundamental theorem of calculus
  in polar form. What is claimed is its consequence for this problem — that the
  surviving obligation can be written with no indefinite-sign term, and with the
  merge-pair/nearest-pair gap absent.
* §2's reduction is a **matched asymptotic**, checked numerically in §4, not
  proved. A proof needs uniform control of the discarded coefficients and of the
  far field; both are `O(eps)` against a leading term `O(rho) = O(eps^{1/(n-1)})`,
  so the estimate is plausible but is not supplied here.
* §3 is **finite evidence** on a sampled one-parameter family, degrees 3 to 8. It
  is not a proof that `min_k kappa_k < 0`, and per `negative_results` entry 19 a
  supremum below a threshold is not evidence the threshold is never crossed —
  the difference here is that the observed margin is `0.35`, not `5e-7`, and it
  grows with degree.
* (RD-slack) is **equivalent** to the target at a given hub, not merely
  sufficient: it is `L(c) <= 2R` rearranged. The strong form (RD) is a strictly
  stronger sufficient condition and is **false off the equal-modulus stratum**,
  refuted by adversarial search at degrees three and four with margins `+0.0095`
  and `+0.0114`, the target holding at both witnesses. That is finite evidence
  with a small margin, not an exact witness, and it has not been exactified.
  On the equal-modulus stratum (RD) is not a strengthening at all — it is the
  target — and there it was not broken.
* Two figures in earlier drafts of this note are **retracted**: a strong-form
  margin of `+0.219`, and an equal-modulus row showing (RD) failing on a random
  draw. Both were artifacts of the branch-tracing defect in §5b. The conclusions
  they supported survive the repair; those numbers do not.

Erdős #1041 remains open. What is new is an exact origin-centred decomposition
of `L(c)` with no indefinite-sign term, an exact representation of its deficit
against `z f'/f`, and a reduction of the hard regime to a one-real-parameter
family per degree on which the surviving obligation has a measured margin of at
least `0.35` rather than `5e-7`.
