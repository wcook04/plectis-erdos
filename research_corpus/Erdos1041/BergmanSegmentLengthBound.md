# Erdős 1041: room converts into length through the Bergman kernel, not through Koebe

Status: two proved lemmas, one dropped hypothesis, two proved theorems, one
exact asymptotic calibration on an equality family, a measured reach, and one
new member of the instrument-defect class. Current through 2026-08-27 source
audit. **Erdős #1041 remains open** and nothing below claims otherwise.

Three things this adds. It replaces the Koebe constants of
[AffineNormalisedModuli.md](AffineNormalisedModuli.md) Theorem R by a **sharp**
estimate, which that file's §7 names as the object that would change the
picture. It shows Theorem B never needed the minimality of `mu`, so the
machinery runs at **every** admissible hub. And it proves Conjecture (C) of
[CapacityGeodesicConjecture.md](CapacityGeodesicConjecture.md) outside a
**degree-free level window of relative width 31.3%** (§3b) — that file records
"the whole of (C) is open". The near-Fekete shell is still owned by
[NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) and the extremal family is outside
every hypothesis here, by construction.

## 0. What was open, and what was wrong with the tool

`HardRegimeIsNearFekete.md` splits the problem on the discriminant ratio `D`.
The `D`-away-from-1 half was untouched until `AffineNormalisedModuli.md`
Theorem R converted "the merge component has room" into a length bound. That
conversion is Koebe's: growth for the chord, distortion for the arc, and the
`1/4` theorem plus `diam ≤ 4 cap` for (R2). Its own §4 records the cost —

> The Koebe constants are the reason it is not more. On the same samples
> `L(c*)/bound` never exceeds about `0.55`, so the bound is loose by a factor
> of two or more even where it fires — Koebe distortion is sharp for the Koebe
> function, whose image is a slit plane, and `Omega_t` is nothing like one.

and its §7 names the repair as *"a sharp replacement for the Koebe constants in
Theorem R"*. This is that replacement, and it is not a better distortion
theorem. It is a different estimate.

The object being measured is not a general univalent image. By Theorem B the
descent arc is `psi([-q,q])` — the image of a **diameter**. For the length of
the image of a fixed curve the sharp tool is the reproducing kernel of the
Bergman space, because `Area(Omega) = ||psi'||^2_{A^2}` is exactly a Bergman
norm and length is exactly an `L^1` integral of `psi'` along the curve. Koebe
never enters.

## 1. Lemma A — the Bergman segment inequality

Write `A^2(D)` for holomorphic `h` on the unit disk with
`||h||^2 = int_D |h|^2 dA < oo`, and `K(z,w) = 1/(pi(1 - z conj(w))^2)` for its
reproducing kernel.

> **Lemma A.** For `0 < q < 1` and `h in A^2(D)`,
>
> ```text
> ( int_{-q}^{q} |h(s)| ds )^2   <=   Lambda(q) * ||h||^2 ,
>
>       Lambda(q)  =  int_{-q}^{q} int_{-q}^{q}  ds ds' / ( pi (1 - s s')^2 )
>                  =  (2/pi) log( (1 + q^2) / (1 - q^2) ) ,
> ```
>
> with **equality** for `h(z) = (1 - q^2 z^2)^{-1}`.

*Proof.* Fix a measurable unimodular `u` on `[-q,q]` and put
`Phi_u = int_{-q}^{q} u(s) K_s ds`, where `K_s = K(., s)`. The map
`s -> K_s` is continuous from the compact `[-q,q] subset D` into `A^2`, so
`Phi_u in A^2`, and the reproducing property gives

```text
int_{-q}^{q} h(s) conj(u(s)) ds  =  < h , Phi_u > .
```

Since `< K_s, K_{s'} > = K(s',s)`,

```text
||Phi_u||^2  =  int int u(s) conj(u(s')) K(s',s) ds ds' ,
```

and for **real** `s, s' in (-1,1)` the kernel `K(s',s) = 1/(pi(1-s s')^2)` is
**positive**. Hence `||Phi_u||^2 <= int int K(s',s) ds ds' = ||Phi_1||^2` for
every unimodular `u`. Taking `u = h/|h|` where `h != 0` (its zeros on the
segment are isolated) and `u = 1` elsewhere makes the left side `int |h| ds`,
so Cauchy–Schwarz gives

```text
( int_{-q}^{q}|h| ds )^2  =  |< h, Phi_u >|^2  <=  ||h||^2 ||Phi_u||^2  <=  ||h||^2 ||Phi_1||^2 .
```

The double integral is elementary: `int_{-q}^{q} ds'/(1-s s')^2 = 2q/(1-q^2s^2)`
and then `int_{-q}^{q} 2q ds/(1-q^2 s^2) = 4 artanh(q^2)`. Dividing by `pi`
gives `Lambda(q)`.

For equality, `Phi_1(z) = int_{-q}^{q} ds/(pi(1-zs)^2) = 2q/(pi(1-q^2z^2))`,
which is **positive on `(-q,q)`**; so with `h = Phi_1` the choice `u = 1` is
optimal and Cauchy–Schwarz is an equality. ∎

**The extremal is conformal, so the constant is sharp for domains too.** The
extremal `h` is the derivative of

```text
psi(z)  =  (1/2q) log( (1 + q z)/(1 - q z) ) ,
```

and `z -> (1+qz)/(1-qz)` maps `D` onto a disk whose distance from `0` is
`(1-q)/(1+q) > 0`, hence into a half plane, where `log` is injective. So `psi`
is univalent with bounded derivative, `Omega = psi(D)` has finite area, and
Lemma A is attained by a genuine conformal map. `2/pi` is not an artifact of
enlarging the class from univalent to Bergman.

## 2. Lemma B — the same estimate for an arbitrary curve

Nothing in the proof used that the curve is a segment except the evaluation of
`Lambda`. For a rectifiable `gamma subset D`,

```text
( int_gamma |h| |dz| )^2  <=  ||h||^2 * Lambda(gamma) ,
Lambda(gamma) = int_gamma int_gamma |dz||dz'| / ( pi |1 - z conj(z')|^2 ) ,
```

and the pseudohyperbolic identity
`|1 - conj(z')z|^2 = (1-|z|^2)(1-|z'|^2)/(1-rho(z,z')^2) >= (1-|z|^2)(1-|z'|^2)`
turns that into a conformally natural statement:

> **Lemma B.** Let `Omega` be simply connected with finite area and `Gamma` a
> rectifiable curve in it. Then
>
> ```text
> length(Gamma)  <=  (1/2) * len_hyp(Gamma) * sqrt( Area(Omega)/pi ) ,
> ```
>
> `len_hyp` the hyperbolic length for the metric `2|dz|/(1-|z|^2)`.

Both sides are natural: hyperbolic length is a conformal invariant of the pair
`(Omega, Gamma)`, and the Euclidean length and area are not conformal but are
what the problem asks about. Lemma B is asymptotically sharp for short curves
near the centre (`Omega = D`, `Gamma = [0,r]`, `r -> 0`) and is what covers
curves that are not diameters.

**How much Lemma B loses on the case at hand,** i.e. `Lambda(q)` against the
majorant `(1/pi) log^2((1+q)/(1-q))`, checked in arm `KERN`:

| `q` | `0.1` | `0.35` | `0.6` | `0.8` | `0.93` | `0.99` |
|---|---|---|---|---|---|---|
| sharp / Lemma B | `0.993` | `0.922` | `0.784` | `0.628` | `0.477` | `0.328` |

so on a diameter Lemma A is worth a factor of three where it matters. Lemma B
is the general tool; Lemma A is the one used below.

**Novelty is not claimed for either.** Lemma A is Cauchy–Schwarz against the
Bergman kernel plus the positivity of that kernel on the real segment; Lemma B
is one line more. Both should be assumed known until a priority search on
Bergman-space and conformal-length literature says otherwise. What is new here
is only the *use*: that this, not distortion, is the estimate the two-segment
merge component wants.

## 3. Theorem C — and Theorem B holds at every admissible hub

First, a hypothesis of `AffineNormalisedModuli.md` Theorem B can be dropped.

> **Observation.** Theorem B never uses the minimality of `mu`. Let `c` be
> **any** critical point, `v = |f(c)| > 0`, and `t > v` a level whose component
> `Omega` of `{|f| < t}` containing `c` holds exactly two roots. Then (B1)–(B5)
> hold verbatim with `mu` replaced by `v` and `q = sqrt(v/t)`.

*Why.* (B1) is the maximum principle (no holes) plus properness plus
Riemann–Hurwitz: `chi(Omega) = 1 = 2 chi(D_t) - b = 2 - b`, so a two-root
component has **exactly one** branch point, which must be `c`. (B2) needs only
`B'(0) = f'(psi(0)) psi'(0)/t = 0`, i.e. `f'(c) = 0`. Then `|B(0)| = q^2` reads
`v = t q^2`, and (B3)–(B5) are unchanged.

That matters because `admissible_branch_length_reformulation` records that *the
minimum over admissible hubs is load-bearing* and that the per-hub form is
false (`negative_results` 20). Restricting to `c*` threw away most of the hubs
the obligation is allowed to use.

> **Theorem C.** Let `f` be monic of degree `n >= 2` with distinct roots, `c` a
> critical point, `v = |f(c)| > 0`, and `t > v` a level whose component `Omega`
> at `c` holds exactly two roots `a, b`. Then the descent arc `Gamma` at `c`
> joins `a` to `b`, lies in `{|f| <= v}`, and
>
> ```text
> L(c)  =  length(Gamma)  <=  sqrt( (2 Area(Omega)/pi) * log( (t+v)/(t-v) ) )
>                         <=  t^{1/n} sqrt( 2 log( (t+v)/(t-v) ) ) .
> ```

*Proof.* By the Observation, `psi : D -> Omega` is conformal with `psi(0) = c`,
`psi(+-q) = a, b`, `q = sqrt(v/t)`, and `Gamma = psi([-q,q])`. Apply Lemma A to
`h = psi'`, using `||psi'||^2_{A^2} = Area(Omega)` and
`(1+q^2)/(1-q^2) = (t+v)/(t-v)`. The last step is Pólya's
`Area{|f| <= t} <= pi t^{2/n}`, recorded as (A) of
[LemniscateCapacityBudget.md](LemniscateCapacityBudget.md). ∎

> **Corollary D.** Let `f` be monic with all roots in the **open** unit disk and
> circumradius `R`. Suppose some critical point `c` with `v = |f(c)| <= R^n`
> admits a level `t in (v, R^n]` whose component at `c` holds exactly two roots
> and
>
> ```text
> 2 Area(Omega) log( (t+v)/(t-v) )  <  4 pi R^2 .
> ```
>
> Then Erdős #1041 holds for `f`. Using only Pólya it suffices that
>
> ```text
> v / t  <  tanh(1)  =  0.7615941559... .
> ```

*Proof.* The arc lies in `{|f| <= v}` and `v <= R^n < 1`, so it is contained in
the target lemniscate, and Theorem C gives `L(c) < 2R < 2`. For the second
form, `t <= R^n` gives `t^{2/n} <= R^2`, so `2 t^{2/n} log((t+v)/(t-v)) < 4R^2`
reduces to `log((t+v)/(t-v)) < 2`. ∎

Both statements are scale-covariant and need no normalisation: under
`z = tau + sigma zeta` lengths scale by `sigma`, areas by `sigma^2`, levels by
`sigma^n`, and `log((t+v)/(t-v))` is invariant — so Theorem C is an affine
statement in the sense `CapacityGeodesicConjecture.md` §1 asks for, and the
minimum enclosing circle enters only through the admissibility threshold `R^n`.

**A general form, with no two-root hypothesis.** Lemma B applied to the
hyperbolic geodesic gives, for any simply connected `Omega` of area `A`
containing two roots `a, b` and contained in `{|f| < t}` with `t <= R^n`:

```text
a and b are joined inside Omega by a curve of length
      <=  (1/2) * d_hyp,Omega(a,b) * sqrt(A/pi) ,
```

which settles Erdős #1041 for `f` whenever that is below `2R`. This has no
hypothesis on the number of roots — but it is only useful when
`d_hyp,Omega(a,b)` can be bounded, and for a `k`-root component that is exactly
what is missing: writing `B` for the degree-`k` Blaschke product and `zeta_j`
for its zeros, `prod_j rho(zeta_c, zeta_j) = |f(c)|/t` bounds the **smallest**
pseudohyperbolic distance and says nothing about the second. The two-root case
is the one where the antipodality of (B2) forces `rho_1 = rho_2 = q` and closes
that gap. So Theorem C is not the general statement; it is the case where the
general statement has a computable right-hand side.

**An explicit area bound, when the other roots are far.** Write
`f = (z-a)(z-b) Q` and `q_Omega = min_{closure Omega} |Q|`. On `Omega`,
`|(z-a)(z-b)| <= t/q_Omega`, so `Omega` sits inside a Cassini oval,
`cap(Omega) <= sqrt(t/q_Omega)`, and `Area <= pi cap^2` gives
`Area(Omega) <= pi t / q_Omega`. Corollary D then reads

```text
v / t  <  tanh( q_Omega / t ) ,
```

which beats the Pólya form exactly when `q_Omega > t` — that is, when the other
`n-2` roots stay far from the merge component. This is where the practical
margin of §5 comes from, stated in the polynomial rather than in a measured
area.

**Against Corollary R.** Corollary R fires when
`t/mu > coth^2(1/8) = 64.68`, i.e. `mu/t < tanh^2(1/8) = 0.0154637`.
Corollary D fires when `v/t < tanh(1) = 0.7615942`. That is a factor of

```text
tanh(1) / tanh^2(1/8)  =  49.25
```

in the admissible level ratio, **before** the true area is used in place of the
Pólya cap — which is where most of the practical gain lives (§5).

**Why this is exactly a quantitative form of the `D`-split.** Normalise the
minimum enclosing circle to the unit circle. Then Fekete reads `mu <= 1` with
equality **iff** the roots are the `n`-th roots of unity, so the level interval
`(mu, 1]` that Theorem C draws its room from is non-empty precisely when
`D < 1`. The hypothesis of Corollary D is therefore empty exactly on the
Fekete-equality family — which is exactly where `L(c) = 2R` and no bound may
fire. What Corollary D adds to `HardRegimeIsNearFekete.md`'s split is that the
room is spent against **area**, not against the level ratio alone: the crude
`mu <= D^{1/(n-1)}` route would need `D < tanh(1)^{n-1}`, which degrades with
degree, while the measured criterion still fires at `mu = 0.9958` (§6).

## 3b. What this proves of the capacity conjecture (C)

[CapacityGeodesicConjecture.md](CapacityGeodesicConjecture.md), landed
concurrently in this directory, moves the target off level `1` and onto level
`μ`:

> **Conjecture (C).** If a connected component of `K_t = {|f| ≤ t}` contains two
> roots of `f`, then two of them are joined **inside that component** by a path
> of length at most `2 t^{1/n} = 2 cap(K_t)`.

Its §8 records "the whole of (C) is open" and lists (C) itself as the third and
strongest open item. Theorem C bears on it directly, and the fit is exact
because of a reduction that file already makes.

**For a Morse polynomial the binding case of (C) is a two-root component —
Theorem C's hypothesis.** Every component of `{|f| < t}` contains a root (else
`1/f` violates the maximum principle there), so below the first merge level
every component holds exactly one. (C) at a level `τ` implies (C) at every
`t > τ` for the component containing `C_τ`, so only the level at which a
component *first* holds two roots binds; there a critical point `c` of
multiplicity `m` joins `m+1` one-root lobes, and the merged component holds
`m+1` roots. So:

> if every critical point of `f` is simple, every first-merge component holds
> **exactly two** roots, and (C) for `f` reduces to the two-root case.

The exception is exactly the degenerate stratum — and that is not a technicality
to be waved through, because it is where the problem lives: on `z^n - r^n` the
hub has multiplicity `n-1`, all `n` lobes merge at one level, and the first
component to hold two roots holds all `n`. That family is (C)'s equality case
(that file's Theorem 2), so the stratum the reduction misses is precisely the
one no bound may touch.

> **Theorem E.** Let `C` be a component of `K_t` holding exactly two roots, `c`
> its unique critical point (Riemann–Hurwitz), `v = |f(c)|`. If
>
> ```text
> t  >=  coth(1) * v  =  1.3130352... * v ,
> ```
>
> then (C) holds for `C`. More sharply it holds as soon as
> `2 Area(C) log((t+v)/(t-v)) <= 4 pi t^{2/n}`.

*Proof.* Theorem C bounds the descent arc, which is one contained path joining
the two roots, by `t^{1/n} sqrt(2 log((t+v)/(t-v)))`. That is at most
`2 t^{1/n}` iff `log((t+v)/(t-v)) <= 2` iff `v/t <= tanh(1)`. ∎

> **Corollary.** Let `f` be Morse. Then (C) holds for `f` at every level except
> inside the windows `[v_i, coth(1) v_i)`, one per critical point `c_i` that
> creates a two-root component. Each window has relative width `31.3%`, and
> outside their union (C) is a theorem.

**The window is degree-free, and that is the point.** At `t = coth(1) v` the
factor `t^{1/n}` appears on both sides and cancels, so the threshold
`t/v >= coth(1)` carries no `n`. Every other route to this half degrades with
degree: `mu <= D^{1/(n-1)}` turns "`D` bounded away from `1`" into a level ratio
that tends to `1` as `n` grows, so the `D`-split alone gives a window that
closes. Theorem E's does not. That is a consequence of measuring the room
against capacity — which is exactly the move (C) makes — rather than against
the unit disk.

Two things this does **not** do. It says nothing at the merge level `t = v`
itself, where `q = 1` and the bound diverges; that endpoint is the tightest case
of (C) and it stays open. And it bounds the *descent arc*, not the geodesic, so
it does not touch the gain that file identifies as the point of the geodesic
formulation — that the geodesic is strictly shorter than the arc that
`negative_results` 29 refutes at `1.0042`. Theorem E is an upper bound on a
particular path, which is all (C) asks for, but it inherits none of that slack.

*Concurrency.* Conjecture (C) is quoted from that file as read on
2026-08-24; its Theorems 1–3 are **not** re-derived here and nothing above
depends on them. Theorem E is an implication from Theorem C to (C)'s statement,
so it survives even if that note's own proofs move. This directory has retracted
a same-day sibling result before.

## 4. The calibration: exact on the quadratic equality family

`admissible_branch_length_reformulation` records two equality families. One of
them, every monic quadratic, is inside Theorem C's hypotheses at every level,
and there the theorem is asymptotically **exact**.

Take `f = z^2 - 1`, so `R = 1`, `c = 0`, `v = mu = 1`, and `L(c) = |a-b| = 2R = 2`
exactly. For `t > 1` the Cassini oval `{|z^2-1| < t}` is connected, so `Omega`
is all of it and holds both roots. Substituting `w = z^2`,

```text
Area  =  (1/2) int_{|w-1|<t} dA(w)/|w|  =  (1/2) int_0^{2pi} rho(phi) dphi ,
rho(phi) = cos phi + sqrt(t^2 - sin^2 phi) ,
```

so `Area(t) = 2 t E(k = 1/t)` with `E` the complete elliptic integral of the
second kind, written in the modulus convention (`mpmath` and `scipy` take the
parameter `m = k^2`, so the receipt calls `ellipe(1/t^2)`). With
`E(k) = (pi/2)(1 - k^2/4 - 3k^4/64 - ...)` and
`log((t+1)/(t-1)) = (2/t)(1 + 1/(3t^2) + ...)`,

```text
(2 Area/pi) log((t+1)/(t-1))  =  4 ( 1 + (1/3 - 1/4)/t^2 + O(t^-4) )
                              =  4 ( 1 + 1/(12 t^2) + O(t^-4) ) ,
```

> **so the bound is `2 sqrt(1 + 1/(12 t^2) + O(t^-4))`: strictly above the true
> `L = 2R` at every finite level, and converging to it.**

At 40 digits (arm `QUAD`; float64 cannot do this — at `t = 1e4` the quantity
`bound^2/4 - 1` is `8.3e-10` and the Richardson coefficient loses five digits
to cancellation, which is why the arm runs in `mpmath`):

| `t` | `1.5` | `3` | `10` | `100` | `1000` | `1e4` |
|---|---|---|---|---|---|---|
| bound `- 2` | `5.816e-2` | `1.018e-2` | `8.402e-4` | `8.334e-6` | `8.333e-8` | `8.333e-10` |
| `t^2 (bound^2/4 - 1)` | `0.13276` | `0.09187` | `0.08404` | `0.083340` | `0.0833334` | `0.08333333` |

against `1/12 = 0.08333333`.

This is the property `StraightSpokeHubCriterionLab.md` §7 asks of any candidate
bound and the reason to prefer this estimate on grounds other than the measured
reach: **it reproduces an equality family of the problem instead of losing a
constant factor there.** (R2) cannot — on the same family it returns
`8 t^{1/2} log((1+q)/(1-q))`, which at `t = 1e4` is about `1.6e2`, off by a
factor of eighty.

**And the family is not an isolated coincidence: it is the local shape of a
merge component.** Whenever the two merging roots are well separated from the
rest, `f = (z-a)(z-b) Q` with `Q` nearly constant on the component, so the
component is nearly a Cassini oval of the pair — the family of this section, at
a large effective `t`. That is why the sampled worst ratio sits where it does:
the guarded sweep of §5 reaches `L(c)/bound = 0.981` over `1085` pairs, so the
estimate is within `2%` of tight on real configurations and the constant `2/pi`
is not what limits the reach.

## 5. Reach, measured on the same hypotheses

Comparing estimates, not hypothesis sets: for every configuration, every
Fekete-admissible hub `c` (`|f(c)| <= R^n`) and every level inside the bisected
two-root window at `c`, all four bounds are evaluated and each is credited with
its own best `(c, t)`. `L(c)` comes from this directory's accurate tracker at
closing depth 10.

**The area instrument, and the three guards it needed.** Areas come from an
`801 x 801` grid over `|z| <= 2.02`, `|f|` evaluated once per configuration and
the component taken by connected-component labelling from `c`. That is a
one-sided instrument in the dangerous direction — area is a **numerator** in
Theorem C, so an under-reported area produces a bound that is too small — and
the first unguarded run duly produced eleven violations of the theorem, worst
`L/bound = 1.1209`, all at degree `>= 6`. All eleven were the instrument, and
each has an identifiable cause now guarded:

* **The root count is not a safe witness for the two-root hypothesis.** Nine of
  the eleven had **two** critical points inside the labelled component, so by
  Riemann–Hurwitz (`b = k-1`) it held three roots, not two — the root count had
  miscounted. Roots sit inside lobes joined by a neck that goes sub-grid as
  `t -> v`; critical points are interior and far from the level set. Both
  counts are now required to agree, and the critical-point count is the
  reliable one.
* **A hub whose own cell is above the level.** The original code fell back to an
  arbitrary neighbouring label, which at a sub-grid neck is one lobe. Such
  levels are now refused outright.
* **Percent-level discretisation.** The area is now **bracketed** by eroding
  and dilating the mask by one cell, and a component whose bracket is wider
  than `10%` is re-gridded once on its own bounding box rather than refused —
  small components are exactly the tight ones, so refusing them would bias both
  the reach and the sharpness downwards. A component touching the frame is
  refused outright, since a truncated mask under-reports. Arm `AREA` calibrates
  the bracket against the one area this file knows exactly — the Cassini oval
  `2 t E(1/t^2)` of §4 — and it contains the exact value at every tested
  resolution and level, with the ends at `-1.53%` and `+1.57%`.

The bracket then does two different jobs, and the distinction matters for
reading the numbers below. `area_hi` gives the **verdict**: `L > bound(area_hi)`
means the theorem fails even granting the largest area the instrument admits,
and only that fails the arm. `area_lo` gives a **strict statistic**: it makes
the bound as small as the instrument allows, so values slightly above one are
the bracket's own width and are not violations. Settlement claims use
`area_hi`, which is the conservative end for them.

108 configurations over degrees `3..8` and six families, `1085` admissible
`(hub, level)` pairs:

| estimate | settles `min_c L(c) < 2R` |
|---|---|
| Theorem C with the measured area | **`104 / 108`  (96.3%)** |
| Theorem C with Pólya only | `76 / 108`  (70.4%) |
| Theorem R (R1), the chord form | `30 / 108`  (27.8%) |
| Theorem R (R2), the capacity form | `8 / 108`  (7.4%) |
| Theorem R, either | `30 / 108`  (27.8%) |
| settled **only** by Theorem C | `74` |
| settled **only** by Theorem R | `0` |

with `min_c L(c) < 2R` true in all `108`, and no violation of Theorem C at any
of the `1085` pairs (`THMA` verdict `0.98102`).

Three readings. **The comparison is calibrated**: (R1) here returns `27.8%`,
independently reproducing the `15-27%` that `AffineNormalisedModuli.md` §4
records for it, so the two measurements are of the same thing. **The two
estimates are nested, not complementary** — Theorem R settles nothing Theorem C
misses, which is what "same hypotheses, sharper estimate" should look like, and
`74` of the `108` are settled by Theorem C alone. And **the constant is not what
limits the reach**: the worst verdict ratio `L(c)/bound` over `1085` pairs is
`0.981`, so the estimate is within `2%` of tight on real configurations, while
the four it misses fail by the area, not by `2/pi`.

Two caveats stay attached. The reach counts are counts on a sample, not a
statement about proportions, and they are a **lower** bound on the true reach
because levels the area instrument cannot resolve are refused rather than
guessed. And `L(c)` inherits the tracker's error bar from `negative_results` 24
and 34, which biases towards the conjecture.

## 6. Where it stops, and why that is correct

The hypothesis is **empty on the extremal family**. For `f = z^n - r^n` and any
`t > mu = r^n`, the component of `{|f| < t}` at the degenerate hub contains all
`n` roots, so no level has a two-root component and Theorem C says nothing.
That is the required behaviour: there `L(c) = 2r = 2R` exactly, so a bound that
fired would be false.

On the **near-Fekete shell** it must eventually stop, and the mechanism is
clear: splitting the multiplicity-`(n-1)` hub puts the `n-1` critical values
within `O(rho^n)` of each other (`NearFeketeCuspLaw.md` §2), so the level at
which a third root joins approaches `v` while `Area(Omega)` tends to the area of
two petals of `{|f| < mu}`, which does not shrink. The logarithm diverges
against a fixed area.

What it does **not** do is stop early. Perturbing the regular `n`-gon along a
fixed angular direction with the roots kept exactly on the unit circle, so
`R = 1` throughout (arm `SHELL`, every row computed at two resolutions):

| `n` | last firing `eps` | there `mu` is | `rho` | bound | true `min_c L(c)` |
|---|---|---|---|---|---|
| 4 | `0.04` | `0.996955` | `0.153` | `1.953` | `1.737` |
| 5 | `0.01` (fine grid: `0.005`) | `0.999146` | `0.164` | `1.908` | `1.714` |
| 6 | `0.002` — the bottom of the ladder | `0.999823` | `0.172` | `1.913` | `1.714` |

Two things to read off, and the second is the load-bearing one. The criterion
still fires at `mu = 0.9998`, where the Pólya form (`mu < tanh(1) = 0.762`) gave
up long before — so on this stratum essentially all of the work is done by the
**true area** rather than by the level ratio. And the reach **improves with
degree**: at `n = 6` it has not switched off at the smallest perturbation
tested, while at `n = 4` it stops at `eps = 0.04`. That is the opposite of every
route through `mu <= D^{1/(n-1)}`, whose window closes as `n` grows, and it is
the same degree-freeness Theorem E's window has.

The one verdict that differs between the two resolutions is `n = 5`,
`eps = 0.005`, where the coarse and fine bounds straddle `2` by `0.5%`. That is
the cut-off being located, not a disagreement: the arm requires any such flip to
straddle the threshold and to be unique per degree.

So Theorem C and the cusp law still do **not** meet. The cusp law is a
first-order statement as `rho -> 0` with an unquantified `O(rho^2)` remainder;
Theorem C is an explicit criterion that switches off at some finite `rho` which
this table brackets but does not compute. The gap between them is a
**one-parameter** gap in `rho` at each degree, not a gap in configuration
space — and at `n = 6` this measurement does not reach far enough to show that
there is one.

## 7. Claim boundary

**Primary-source boundary (read 2026-08-27).** The Pólya attribution used for
the global area input is bound to the downloaded primary scan recorded in
[`erdos1041_constant_factor_polya_primary_text_read_20260827d.json`](../../../../docs/formal_math/observatory_source_reaudit/erdos1041_constant_factor_polya_primary_text_read_20260827d.json).
The source is George Pólya, *Beitrag zur Verallgemeinerung des Verzerrungssatzes
auf mehrfach zusammenhängende Gebiete*, Sitzungsberichte der Preussischen
Akademie der Wissenschaften (1928), printed pp. 280--282 (scan pp. 312--314),
PDF SHA-256
`2de0cd74d07f02ff08be81e1eaac35b5529e1c60e35e1c5c9b4c4ca0602fd205`,
[`official archive PDF`](https://archive.org/download/sitzungsbericht1928preu/sitzungsbericht1928preu.pdf).
Those pages support the global area--capacity inequality for polynomial
sublevel sets. They do **not** state Lemma A's local Bergman estimate, the
componentwise coarea--perimeter synthesis, or the assembled Erdős #1041 path
claim. The local arguments remain ordinary repository-authored mathematics;
no priority or novelty claim is made.

**Proved, by ordinary mathematics:** Lemma A including the equality case and
the univalence of its extremal; Lemma B; the Observation that Theorem B needs
no minimality; Theorem C; Corollary D; the asymptotic expansion of §4 and hence
that the bound exceeds `2R` at every finite `t` on the quadratic family and
converges to it.

**Not first here:** Theorem B and Theorem N
([AffineNormalisedModuli.md](AffineNormalisedModuli.md)); Pólya's
`Area{|f| <= t} <= pi t^{2/n}` and `cap = t^{1/n}`
([LemniscateCapacityBudget.md](LemniscateCapacityBudget.md)); the corrected
obligation and its equality families (`admissible_branch_length_reformulation`);
the reproducing kernel of the Bergman space, and the Bergman-space
Cauchy–Schwarz that Lemma A is an instance of.

**Measured, not proved:** every count in §5 and every row in §6's table. Areas
are bracketed rather than exact, with the bracket calibrated in arm `AREA`
against the closed-form Cassini area to `-1.53% / +1.57%`; verdicts use the
conservative end and the strict statistic uses the other, so a strict ratio
slightly above one (`1.0093` here) is the bracket's width and not a violation.
The reach counts are counts on a sample, not a theorem about proportions, and
they under-state the reach because unresolvable levels are refused. `L(c)`
inherits the tracker's error bar from `negative_results` 24 and 34, which
biases **towards** the conjecture — so the honest reading of the worst verdict
ratio is that no violation was found at this instrument resolution, not that
the margin is certified.

**Retracted within this note, twice, and both in the unsafe direction.**

*One.* An earlier float64 form of §4's calibration reported the bound falling
`4.9e-4` **below** `2` at `t = 1e4` and the Richardson coefficient missing
`1/12` by `2.8e-5`. Both were quadrature and cancellation — a `1/|w|`
singularity sampled on a uniform polar grid, then a difference of near-equal
float64 quantities — not a violation. Fixed by the closed form `2 t E(1/t)` and
40-digit arithmetic.

*Two, and it is the useful one.* The first unguarded configuration sweep
reported **eleven violations of Theorem C**, worst `L/bound = 1.1209`. Every one
was the area instrument, and the diagnosis generalises past this file:

> **A component's root count is not a safe witness for the two-root
> hypothesis; its critical-point count is.** Riemann–Hurwitz makes them the same
> statement — a `k`-root component of a lemniscate sublevel set carries exactly
> `k-1` critical points — but they are not equally observable on a grid. The
> roots live in lobes joined by a neck whose width vanishes as the level
> approaches the critical value, so a sampled component splits or merges there
> and miscounts; the critical points are interior and far from the level set,
> so they are counted correctly by the same grid. Nine of the eleven violations
> read "two roots" while holding two critical points, i.e. three roots.

This is a new member of the class `negative_results` 24 and 34 record, with a
third cause. Its two predecessors under-report **branch length** and **level**;
this one under-reports **the area of a sublevel component**, and like them it
errs towards the conjecture. The general rule the three share: whenever a
sampled quantity enters a bound as a numerator, calibrate it against a case
with a closed form before reading any near-miss — which is why arm `AREA`
exists and why §4's Cassini area is worth having in closed form twice over.

**Not established: novelty.** See §2.

**Erdős #1041 remains open.** Theorem C settles a slice of configurations, not
a case of the theorem; it is silent on the extremal family by construction, and
it does not reach the near-Fekete shell.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_bergman_segment_bound.py --part all --trials 3 --grid 701
```

Arms, each fail-closed:

| arm | what fails it |
|---|---|
| `KERN` | the closed form for `Lambda(q)` misses an independent 40-digit double quadrature, or exceeds the Lemma B majorant |
| `EXTR` | `h = (1-q^2z^2)^{-1}` does not attain `Lambda(q)`, or its primitive is not injective on a sampled grid |
| `QUAD` | the bound drops to or below `2` on `z^2 - 1`, or the Richardson coefficient misses `1/12` |
| `AREA` | the erode/dilate bracket fails to contain the exact Cassini area `2 t E(1/t^2)` |
| `THMA` | `L(c) > bound(area_hi)` at any admissible pair |
| `POLYA` | `Area(Omega_t) > pi t^{2/n}` |
| `REACH` | Theorem C does not settle strictly more than Theorem R, or settles less than their union |
| `SHELL` | the criterion never fires on the shell, a resolution flip is not a threshold straddle, or two flips occur at one degree |
| `THRESH` | the `tanh(1)` / `tanh^2(1/8)` ratio drops below `40`, or the `coth(1)` edge of Theorem E is not exact |

Receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1041_bergman_segment_bound_receipt.json`.
