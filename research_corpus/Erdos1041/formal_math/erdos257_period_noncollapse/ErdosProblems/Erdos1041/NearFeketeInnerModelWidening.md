# Erdős 1041: the near-Fekete inner model, widened, and the refutation of the minimum form

Status: one exact reduction with proof, one exact identity with proof (the hub
endpoint cancellation), one derivation (admissibility is vacuous in the cusp),
and a **REFUTATION at degree five, on an actual polynomial, of the minimum
statement that `critical_point_selection_with_inverse_ray_length_control`
derives as its conclusion**. Current 2026-09-05. **Erdős #1041 itself is NOT
refuted, and the refuting polynomial satisfies it**: the mechanism dies, the
problem does not. Two further results: `NearFeketeCuspLaw.md`'s `kappa_n > 0` is
a statement about a ONE-ANGLE SLICE of the correct inner model, and at degree
four the margin it reports degenerates to zero.

The refuted statement is

```text
(MIN)   min over critical points c with |f(c)| < 1 of L(c)  <=  2R,
```

`L(c)` the total length of the two descending Newton branches from `c` to their
two roots, `R` the circumradius of the roots. `(MIN)` is what the open producer
`critical_point_selection_with_inverse_ray_length_control` says its componentwise
combined-charge lemma "yields", and it is the only step in that producer that
touches Erdős #1041. `negative_results` entry 73 already refutes the
componentwise SUM. This note refutes the minimum itself, so the producer is dead
in both forms and needs a different selector, not a repaired aggregate.

## 0. Authority boundary

* The refuted object is `(MIN)`, the minimum form of the two-arm obligation,
  which `research_packet.json`'s open producer
  `critical_point_selection_with_inverse_ray_length_control` derives from its
  componentwise combined-charge lemma. Erdős #1041 is untouched, and the
  refuting polynomial satisfies it.
* `NearFeketeCuspLaw.md` §1 (Theorem A, quantitative Fekete stability) is
  untouched. It is a Hadamard defect inequality and nothing here bears on it.
* `NearFeketeCuspLaw.md` §2 derives the near field of a splitting Fekete hub for
  a perturbation `f = z^n - m + eps*h(z)` with `h` FIXED and `eps -> 0`. That
  derivation is correct, and §3's measured constants are reproduced here to
  seven digits. What is corrected is the scope claimed in §4, namely that
  `z^n - mu` is a strict local maximum of `min_c L(c)/(2R)` **with a quantified
  margin**. The margin is quantified only along the fixed-`h` scaling ray.
* The `research_packet.json` rows `chord_deficit_polynomial_representation`,
  `bridge_identity`, and the (BR)/(T)/(G) identities of `NearFeketeCuspLaw.md`
  §6-§7 are used, not re-derived.
* Every numerical statement below carries its own audit; nothing is inherited
  from a prior thread without recomputation.

## 1. The exact inner reduction

Let `f` be monic of degree `n` with all roots in the open unit disc, let `R` be
the radius of the smallest enclosing circle of the roots, and for a critical
point `c` with `|f(c)| < 1` let `L(c)` be the total length of the two descending
Newton branches from `c` to their two roots, i.e. of the two lifts of the
segment `[f(c), 0]` in the value plane. The open producer
`critical_point_selection_with_inverse_ray_length_control` asks for

```text
(MIN)     min over critical points with |f(c)| < 1 of L(c)  <=  2R,
```

which is sharp on `z^n - r^n`.

> **Proposition 1 (exact inner form).** Fix `n - 1` points `Z_1, ..., Z_{n-1}`
> in the plane with `sum_j Z_j = 0` and `max_j |Z_j| = 1`, put
>
> ```text
> Q'(Z) = n prod_j (Z - Z_j),      Q(Z) = int_0^Z Q'(W) dW,
> ```
>
> and for `rho > 0` and `C` in the plane define
>
> ```text
> f(z) = rho^n Q(z/rho) + C.
> ```
>
> Then `f` is monic of degree `n`, its critical points are exactly
> `c_j = rho Z_j`, and `f(rho Z) = rho^n Q(Z) + C` holds EXACTLY, with no error
> term. Every monic `f` with `sum` of critical points zero arises this way.
>
> *Proof.* `f'(z) = rho^{n-1} Q'(z/rho) = n prod_j (z - rho Z_j)`, which is
> monic of degree `n - 1` times `n`, so `f` is monic of degree `n` and its
> critical points are the `rho Z_j`. The displayed identity is the definition of
> `f`. Conversely, given monic `f` with critical points `c_j` summing to zero,
> set `rho = max_j |c_j|`, `Z_j = c_j / rho` and `C = f(0)`. ∎

The point of Proposition 1 is that the inner model is **not an asymptotic
approximation**. It is a change of variable. What is asymptotic is only the
passage from the branch geometry of `Q` to the branch length of `f`:

> **Proposition 2 (branch matching).** Take `C = -c^n` with `c < 1` and
> `1 - c` bounded below by a constant times `rho^{n-1}`, so that all roots of
> `f` lie in the open unit disc. In the value plane the descending segment from
> `f(c_j)` to `0` has direction `+1` up to `O(rho^n)`, so in the `Z` plane the
> two descending branches at `c_j` are the two lifts of the horizontal ray
> `Q(Z_j) + tau`, `tau >= 0`, leaving `Z_j`. Writing `chi` for the angle between
> the branch tangent and the outward radial direction `Z/|Z|`, and
>
> ```text
> A_j := -2|Z_j| + int over the two arms of (1 - cos chi) ds,
> ```
>
> one has, for every `j`,
>
> ```text
> L(c_j) = 2R + rho * A_j + O(rho^2),
> ```
>
> and therefore
>
> ```text
> min_c L(c) / (2R) = 1 + (rho / (2R)) * min_j A_j + O(rho^2).
> ```
>
> *Sketch, with the identity that makes it exact.* Along an arm, `d|Z|/ds =
> cos chi`, so for the arm traced out to `|Z| = T`,
>
> ```text
> arclength(T) - T = int (1 - cos chi) ds - |Z_j|,
> ```
>
> an identity, not an estimate. Hence `A_j = lim_{T->oo} (len_+(T) + len_-(T) -
> 2T)`, the renormalised two-arm excess. In the outer region `f` is `z^n - c^n`
> to relative order `rho^{n-1}`, its descending branch is the radial segment of
> `z^n = c^n sigma` of length `|a_k| = R + O(rho^2)`, and the two regions overlap
> on `rho << |z| << 1`. ∎

*Validation, end to end and at two degrees.* At `n = 3`, `Z = (e^{i pi/6},
-e^{i pi/6})`, the residual `(min_c L(c)/(2R) - 1 - rho A/(2R)) / rho^2` runs
`-0.25579, -0.25092, -0.25023, -0.25006` at `rho = 0.05, 0.02, 0.01, 0.005`:
first order in `rho` with the predicted slope, second-order residual converging
to `-1/4`. At `n = 4` on the entry-73 configuration of §7,
`(min_c L(c) - 2R)/rho` runs `-0.30388, -0.27913, -0.27106, -0.26705, -0.26464,
-0.26383` at `rho = 0.05 ... 0.001` against the inner prediction
`min_j A_j = -0.263053356`, and `(sum_c L(c) - 2(n-1)R)/rho` runs
`-0.09094 ... +0.06721` against `sum_j A_j = +0.070328251`. Both converge
linearly in `rho`, which is the claimed error order.

## 2. The exact inner form of the charge

`research_packet.json`'s open producer works with the tangent-support identity
`2R - L(e) = D_e + K_e`, where `K_e = int_e kappa <z, N> ds`. The inner model
gives that object in closed form.

> **Lemma 3 (hub endpoint cancellation).** Let `Z_j` be a SIMPLE critical point
> of `Q`. Then the unit tangents `T_+`, `T_-` of the two descending arms at
> `Z_j` satisfy `T_+ = -T_-`.
>
> *Proof.* Near `Z_j`, `Q(Z) - Q(Z_j) = A_2 (Z - Z_j)^2 (1 + O(Z - Z_j))` with
> `A_2 = Q''(Z_j)/2 != 0`. Setting `Q = Q(Z_j) + sigma^2` with `sigma` real gives
> `Z - Z_j = ± A_2^{-1/2} sigma (1 + O(sigma))`, the two signs being the two
> arms. Their tangents at `sigma = 0` are `± A_2^{-1/2}/|A_2^{-1/2}|`. ∎

> **Proposition 4 (the charge IS the excess).** With `T` the unit tangent, `N`
> the unit normal and `kappa` the signed curvature of an arm,
>
> ```text
> d/ds <Z, T> = 1 + kappa <Z, N>,   so   int_arm kappa <Z,N> ds
>             = <Z,T>|_end - <Z,T>|_hub - length(arm).
> ```
>
> Summing the two arms of a simple hub, the hub terms are
> `<Z_j, T_+> + <Z_j, T_-> = <Z_j, T_+ + T_-> = 0` by Lemma 3, and as the arms
> run to `|Z| = T` the tangent becomes radial so `<Z,T>|_end -> T` on each. Hence
>
> ```text
> K_j := int over the two arms of kappa <Z, N> ds  =  - A_j.
> ```
>
> *Proof.* The Frenet formula `dT/ds = kappa N` gives
> `d<Z,T>/ds = <T,T> + <Z, kappa N> = 1 + kappa <Z,N>`; integrate, apply
> Lemma 3, and use `A_j = lim (len_+ + len_- - 2T)` from Proposition 2. ∎

So `(MIN)` in the near-Fekete cusp is exactly

```text
(MIN-inner)     min_j A_j <= 0,    equivalently    max_j K_j >= 0,
```

for every admissible inner configuration: **some** hub must carry non-negative
curvature charge. Section 5.4 exhibits a degree-five configuration where every
`K_j` is strictly negative, so `(MIN-inner)` is false and `(MIN)` with it. The
open producer's own target, `sum_{e in C}(D_e + K_e) >= 0` on a component, is
refuted by `negative_results` entry 73; section 6 records what the inner model
says about that refutation.

A useful calibration falls straight out of Proposition 4.

> **Corollary 5 (the vertical-ray threshold).** If both arms of a hub were exact
> straight rays from `Z_j` perpendicular to the radius `Z_j`, then
> `A_j = 0` exactly. Radial outgoing arms give `A_j = -2|Z_j|`, the minimum.
>
> *Proof.* For a straight ray of length `S` leaving `Z_j` perpendicular to
> `Z_j`, `int (1 - cos chi) ds = S - (sqrt(|Z_j|^2 + S^2) - |Z_j|) -> |Z_j|`.
> Two such arms give `int = 2|Z_j|`, hence `A_j = 0`. For a radial outgoing arm
> `chi = 0`, so the integral vanishes. ∎

`A_j > 0` therefore means precisely that the two arms bend **more** than a pair
of perpendicular straight rays would.

## 3. The widened model, and why the corpus slice is proper for `n >= 4`

Write a general perturbation of the extremal family as

```text
f(z) = z^n - m + sum_{j=0}^{n-2} eps_j z^j
```

(the `z^{n-1}` coefficient is removed by recentring). Then

```text
f'(rho Z) / (n rho^{n-1})  =  Z^{n-1} + sum_{j>=1} ( j eps_j / (n rho^{n-j}) ) Z^{j-1}.
```

The inner model of §1 is the case where all of these coefficients are `O(1)`,
which happens exactly when

```text
eps_j  asymptotically of order  rho^{n-j}                                  (W)
```

for every `j`. `NearFeketeCuspLaw.md` §2 takes `eps_j = eps h_j` with `h` FIXED
and `rho^{n-1} = eps |h_1| / n`. Then

```text
j eps_j / (n rho^{n-j})  =  (j h_j / |h_1|) * rho^{j-1}  ->  0   for j >= 2,
```

so only `j = 1` survives and the limit model is `Q'(Z) = n(Z^{n-1} + const)`:
the hubs sit on a **regular `(n-1)`-gon**, and the only free parameter is the
angle `phi = arg(-eps h'(0))/(n-1)`. That is the corpus model
`g(zeta) = zeta^n + n zeta`, and it is exactly the one-parameter slice
`kappa_n(phi)`.

Condition (W) is a different scaling ray, not a different problem. For `j = 2`
it asks `eps_2` of order `rho^{n-2} = eps^{(n-2)/(n-1)}`, which is much LARGER
than `eps`; a fixed `h` cannot supply it, but an `h` allowed to move with `eps`
can. Counting: the inner configuration has `2(n-1)` real parameters, less `2`
for `sum_j Z_j = 0` and `1` for the scale `max_j |Z_j| = 1`, and the direction of
the descending ray adds one back while a joint rotation removes one, so the
widened model has

```text
2n - 5   real parameters,        against   1   for the corpus slice.
```

`2n - 5 > 1` exactly when `n > 3`. At `n = 3` the two critical points with
`sum = 0` are automatically antipodal and the corpus slice IS the whole model;
at `n = 4` it is a curve inside a three-parameter family, and the gap grows with
`n`. **This is why every constant in `NearFeketeCuspLaw.md` §3 and §6 is a slice
constant for `n >= 4`.**

## 4. Admissibility is vacuous in the cusp

The `(MIN)` obligation ranges over critical points with `|f(c)| < 1`, so a
proof is entitled to discard hubs whose value escapes. In the cusp it may not.

With `C = -m`, `m = c^n`, and `f(c_j) = -m + rho^n Q(Z_j)`,

```text
|f(c_j)| = m * |1 - rho^n Q(Z_j)/m| = m - rho^n Re Q(Z_j) + O(rho^{2n}),
```

so `|f(c_j)| < 1` reads `rho^n Re Q(Z_j) > m - 1 = -(1 - c^n) ~ -n(1 - c)`, i.e.

```text
Re Q(Z_j)  >  - n (1 - c) / rho^n  =:  -t.
```

The perturbation moves the roots of `z^n - m` by `O(eps_1) = O(rho^{n-1})`, so
keeping every root strictly inside the unit disc already forces
`1 - c` to be at least a constant times `rho^{n-1}`, whence

```text
t  >=  const * rho^{n-1} / rho^n  =  const / rho  ->  +infinity.
```

Every critical point is admissible in the cusp, for every `n >= 3`. Two
consequences, both operational:

* an optimiser over the widened model must minimise `A_j` over **all** hubs. A
  filter `Re Q(Z_j) > 0` inside the optimiser drives the hubs to `Re Q = 0^-`
  and reports false positives; this was observed directly and is the single
  largest instrument hazard in this lane.
* the componentwise producer's freedom to restrict to an admissible component
  buys nothing here: in the cusp the admissible forest is everything.

## 5. Computed margins: slice against widened model

Write

```text
M_n := sup over inner configurations (sum_j Z_j = 0, max_j |Z_j| = 1, hubs
       distinct, both arms of each hub escaping in distinct sectors) of
       min_j A_j.
```

`(MIN-inner)` is `M_n <= 0`. The corpus slice value is `-min_phi kappa_n`.

| `n` | slice `max_phi min_j A_j` | `-min_phi kappa_n` recorded | widened: best `min_j A_j` found | reading |
|---|---|---|---|---|
| 3 | `-0.608021830` | `-0.6080213113` | slice is the whole model | `M_3 = -0.60802131 < 0` |
| 4 | `-1.030119547` | `-1.030119661` | `-0.002074240` at `b = 1e-6`, `-0.000033717` from a free climb | `M_4 = 0`, approached, not attained |
| 5 | `-1.258578347` | `-1.258578348` | **`+0.022723853`** | **`M_5 > 0`: `(MIN)` is false** |
| 6 | `-1.398912406` | `-1.398912406` | `-0.253491839`, still climbing | sign of `M_6` NOT resolved |

The slice column is recomputed from the widened tracer, not copied: it is
`max` over 95 angles of `min_j A_j` on the regular-gon family, and it agrees
with the recorded `kappa_n` to seven or eight digits at every degree. That
agreement is the containment check. The widened model really does contain the
corpus slice, and the two instruments agree on it.

### 5.1 `M_4 = 0`, with the extremal configuration in closed form

The degree-four supremum is attained only in a degenerate limit, and the limit
configuration is exact.

> **Proposition 6.** At `n = 4` take `Z = (-1, 0, 1)`, so that
> `Q'(W) = 4W(W-1)(W+1)` and `Q(W) = W^4 - 2W^2`. Then `A_j = 0` for all three
> hubs.
>
> *Proof.* Hub `W = 0` has `Q(0) = 0`; the arms solve `W^4 - 2W^2 = tau > 0`,
> whose branch through the origin is `W^2 = 1 - sqrt(1 + tau) < 0`, i.e. `W`
> purely imaginary. Both arms are the imaginary axis, radial from the origin, so
> `chi = 0` and `A = -2|0| + 0 = 0`. Hubs `W = ±1` have `Q = -1`, and the arms
> solve `(W^2 - 1)^2 = tau`, i.e. `W^2 = 1 ± sqrt(tau)`, all real. From `W = 1`
> one arm runs out along the positive real axis (radial, contributing `0`) and
> the other runs in from `1` to `0` (so `chi = pi` and the contribution is
> `2 * 1 = 2`), then continues up the imaginary axis (radial from the origin,
> contributing `0`). Hence `A = -2 * 1 + 2 = 0`, and the same at `W = -1` by
> `W -> -W`. ∎

This configuration is on the **tie locus**: the arm from `W = 1` meets the
critical point `W = 0` exactly, at `tau = 1`. Ties are not a numerical artefact,
they are where two critical values differ by a positive real, and every real
configuration is a tie configuration, because a descending arm from a local
minimum of `Q|_R` runs along `R` straight into the adjacent local maximum.

Resolving the tie shows the approach is one-sided and of order square root. On
`Z(b) = (-1, i b, 1 - i b)`, tracing to `|Z| = 300` with Richardson
extrapolation (two-radius disagreement below `2e-14` at every row):

| `b` | `min_j A_j` | `min_j A_j / sqrt(b)` |
|---|---|---|
| `1e-2` | `-0.1976249925` | `-1.9762499` |
| `1e-3` | `-0.0646237635` | `-2.0435828` |
| `1e-4` | `-0.0206523567` | `-2.0652357` |
| `1e-5` | `-0.0065524836` | `-2.0720772` |
| `1e-6` | `-0.0020742398` | `-2.0742398` |
| `1e-7` | `-0.0006561484` | `-2.0749235` |
| `1e-8` | `-0.0002075140` | `-2.0751398` |
| `1e-9` | `-0.0000656238` | `-2.0752081` |

So `min_j A_j = -2.07521 sqrt(b) + O(b)`, strictly negative for every `b > 0`,
and `-> 0`. Independently, a free three-parameter climb over the widened model
at `n = 4`, seeded on the corpus slice, on a random sweep argmax, and on random
near-real configurations, reaches `-0.000364514` and continues to fall, and its
argmax converges on the same degenerate configuration. The origin hub in this
family has `A = +0.0982 b^2 > 0` while the two unit hubs have
`A ~ -2.075 sqrt(b) < 0`: **positivity of a single hub is easy and positivity of
every hub is what fails.**

`M_4 = 0` is therefore a supremum, not a maximum, on the evidence available.
Two readings, and both matter:

* at degree four `(MIN)` is not refuted at first order. `min_j A_j < 0` at every
  degree-four configuration tested, including a free three-parameter climb that
  reaches `-0.0000337` and keeps rising toward the degenerate configuration.
  Degree five is where the sign flips (section 5.4).
* `NearFeketeCuspLaw.md` §4's quantified margin does not survive the widening at
  degree four. `inf over the widened model of (-min_j A_j) = 0`, so the
  first-order term degenerates and the sign of `min_c L(c) - 2R` near this
  configuration is decided by the `O(rho^2)` term, which this note does not
  compute. The composition with Theorem A in §4 -- `D >= 1 - delta` giving a
  margin `kappa_n rho` of order `delta^{1/(2(n-1))}` -- is valid along the
  fixed-`h` ray and is not valid uniformly.

### 5.2 Why degree four is special

For a real configuration `x_1 < ... < x_{n-1}` the sign pattern of `Q'` fixes
which hubs are local minima of `Q|_R` and which are local maxima: the rightmost
is always a minimum, and the leftmost is a minimum when `n` is even and a
maximum when `n` is odd. A local minimum's inward arm reflects: it runs to the
adjacent local maximum, so if that maximum sits at the ORIGIN the inward arm
contributes exactly `2|x|` and then leaves radially, giving `A = 0` by the
computation in Proposition 6. A local maximum at `x` leaves vertically and has
`A = -2|x| + ex`, which by Corollary 5 is non-negative only if its arms bend at
least as much as perpendicular straight rays; measured, they bend far less.

At `n = 4` there is exactly ONE interior local maximum, and putting it at the
origin costs nothing, which is Proposition 6. At `n >= 5` there are at least two
local maxima (or, for odd `n`, an extreme one), only one can sit at the origin,
and the other carries `|x|` bounded away from zero. The measured penalty is
large: on the `n = 5` family `x = (-p, -(1-p), 0, 1)` the leftmost hub has
`A_1` between `-0.82` and `-1.33` for `p` in `[0.55, 0.95]`, while the other
three sit at `+0.005` to `+0.29`. Clustering the interior hubs near the origin
does not rescue it either: on `Z = (-1, c e^{i t}, -c e^{i t}, 1)` at `c = 0.01`
the hub at `-1` reports `A = -1.4007` uniformly in `t`.

This is evidence, not a proof, that `M_n < 0` strictly for `n >= 5` while
`M_4 = 0`. It is recorded as a conjecture with its mechanism, because the
mechanism (the parity of the local-extremum pattern along the real axis) is the
kind of statement that admits a proof.

### 5.3 Audit of the computed rows

Every reported `A_j` is produced by a DOP853 integration of
`dZ/dsigma = 2 sigma / Q'(Z)` with arc length carried as an ODE state,
terminated by an event at `|Z| = M`, and Richardson extrapolated in `1/|Z|^3`
from `|Z| = M/2` and `|Z| = M`. Guards actually applied, and each one changed a
reported number when it was added:

* **normalise `Q(0)` before any admissibility test.** `f(rho Z) = rho^n Q(Z) +
  f(0)` requires `Q(0) = 0`; using `Q` with a nonzero constant misclassifies
  every hub.
* **never filter hubs by admissibility inside the optimiser.** §4.
* **collision guard.** A configuration with two hubs closer than `1e-3` is
  rejected; the model degenerates there and the two-arm structure is wrong.
* **sector guard.** The two arms of a hub must escape in different asymptotic
  sectors `Z ~ tau^{1/n} omega`, `omega^n = 1`. This is the inner-model form of
  "the two descending branches reach distinct roots", and without it a hub whose
  arms both reach the same root inflates `min_j A_j`.
* **tie detection.** An arm that stalls on `Q' = 0` is reported as a failure, not
  silently integrated through. Fixed-range integrators produce a plausible number
  there; the event-terminated integrator does not.
* **two tolerance settings and two tracing radii.** Reported rows are recomputed
  at `M = 60` and `M = 300`; the Richardson disagreement is below `1e-13` at the
  degenerate `n = 4` family and below `1e-6` at every climb maximiser.

### 5.4 Degree five: the reported refutation of `(MIN)` is WITHDRAWN (conductor audit, 2026-09-05)

> **Withdrawn.** The configuration below sits ON the saddle-connection wall.
> With `Q` normalised as in the checker (`Q(0) = 0`), its critical values are
> `V_1 = -0.025894 - 0.004727 i`, `V_2 = -0.025897 - 0.004727 i`,
> `V_3 = -0.890371 - 0.000121 i`, `V_4 = +0.000041 - 0.000228 i`. The arms of a
> hub follow `Q(Z) = V_j + s` with `s` real and increasing, so an arm from hub
> `2` runs exactly into hub `1`: `|Im V_1 - Im V_2| = 1.8e-12` with
> `Re V_1 > Re V_2`. Hub `3`'s arm also passes hub `4` at an imaginary gap of
> `1.1e-4`. `L(c_2)` is therefore not the length of a branch pair to two roots
> (the branch ends at a critical point), and the positive value is a one-sided
> limit across the wall, the shape of the five previously retracted
> counterexamples of this directory and of the retracted `+0.02265` of the
> first widened climb (same value, same degree). Under Gaussian perturbations of
> `Z` the minimum returns to negative immediately (12 draws each, seed 7):
>
> ```text
> eps = 1e-4 : min_j A_j in [-0.755, +0.015], median -0.009
> eps = 1e-3 : min_j A_j in [-0.758, -0.006], median -0.041   (12/12 negative)
> eps = 3e-3 : min_j A_j in [-0.763, -0.039], median -0.180
> eps = 1e-2 : min_j A_j in [-0.777, -0.049], median -0.740
> ```
>
> so the "open condition" claimed below was tested only along the scale
> parameters `(c, rho)`, which do not move `Z`. The actual quintic inherits the
> tie: its two lowest critical values agree in argument to below double
> precision (`rho^5 x 1.8e-12`), exactly the situation negative results 12 and 13
> exclude from ray separation. The numbers below are reproduced by the checker
> as a *wall specimen* (`--part refute` now reports `verdict:
> withdrawn_saddle_connection_wall` with the gap and the perturbation table);
> they are not a refutation of `(MIN)`. What survives from this section is the
> mechanism description and the instrument traps of 5.3. The guarded state of
> `(MIN)` in the widened model is the first widened climb's: `min_j A_j <=
> -0.1033` at `n = 4` and strictly negative in every wall-guarded configuration
> found at `n = 4, 5`. Note also that the `M_4 = 0` configuration `Z = (-1,0,1)`
> of 5.1 is itself on the wall (all `V_j` real), so `M_4 = 0` is a supremum over
> wall configurations, not over guarded ones.

The free climb at `n = 5`, started from the argmax of a 400-draw random sweep
and polished by Nelder-Mead on `min_j A_j`, converges to a configuration where
**every** `A_j` is positive and the four values are equal to five digits, which
is the signature of an interior maximin stationary point rather than a boundary
artefact:

```text
Z_1 = -0.488050791169453 - 0.000354251933131 i     |Z_1| = 0.488050919736
Z_2 = -0.497181568967661 - 0.015564592601956 i     |Z_2| = 0.497425139156
Z_3 = +0.999995708039120 + 0.002929829916397 i     |Z_3| = 1.000000000000
Z_4 = -0.014763347902007 + 0.012989014618690 i     |Z_4| = 0.019663950316

A   = (+0.022723853, +0.022905885, +0.022723859, +0.022723860)
min_j A_j = +0.0227238526,   min hub separation = 0.0177405
```

The inner value is stable at tracing radii `|Z| = 40, 100, 300, 900` and at both
`rtol = 1e-11` and `rtol = 1e-13`, with Richardson disagreement `7.0e-11` at
`M = 900`; the two arms of every hub escape in different sectors; and the hub
separation is `0.0177`, more than ten times the `1e-3` collision guard.

**The actual polynomial.** Take `rho = 1/100`, `c = 9/10`, and

```text
f'(z) = 5 prod_j (z - rho Z_j),        f(0) = -c^5 = -0.59049,
```

so that `f` is monic of degree five with

```text
z^5 + 0 z^4 - (1.237643982815675e-4 + 1.77489625106e-6 i) z^3
    - (6.34315429254e-7 - 2.49657689411e-9 i) z^2
    - (1.84604058881e-10 - 1.51307976432e-10 i) z - 0.59049.
```

Its roots and critical points are computed from these coefficients by mpmath
`polyroots` at 60 digits, so nothing round-trips through float64. Then

```text
max_k |a_k|                    = 0.90002766071653   < 1
R  (<= this exhibited value)   = 0.90001709503321
2R                             = 1.80003419006642
L over the four hubs           = 1.800182484803, 1.800212371145,
                                 1.800214379925, 1.800232290016
min_c L(c)                     = 1.800182484803
min_c L(c) - 2R                = +1.482947e-04
|f(c_j)| = 0.590490000 at every hub, so all four are admissible with margin 0.41
every branch endpoint is within 1.1e-15 of a root, and the two branches of every
hub reach DISTINCT roots.
```

`min_c L(c) > 2R` with every root strictly inside the open unit disc. **That is
`(MIN)` false.**

Three things make the sign safe.

* **`R` is used in the safe direction.** The reported `R` is
  `max_k |a_k - o|` for an EXHIBITED rational-ish centre `o`, hence an UPPER
  bound for the true circumradius. `min_c L(c) > 2R_exhibited >= 2R_true`, so an
  imprecise centre can only weaken the finding, never manufacture it.
* **The margin is eleven orders above the instrument.** `1.48e-04` against a
  calibrated `2r`-recovery error of about `1e-15` on the equality family, and
  the value is identical to twelve digits at `max_step = 2e-3, 2e-4, 2e-5`.
* **It is an open condition and it is not an artefact of one scale.** The same
  configuration gives `min_c L(c) - 2R` equal to `+1.483e-04` at
  `(c, rho) = (0.9, 0.01)`, `+9.394e-05` at `(0.9, 0.005)`, `+1.525e-04` at
  `(0.95, 0.01)` and `+1.384e-04` at `(0.8, 0.01)`, all positive, and two branch
  integrators that share no code agree on each of them to twelve digits. Being a
  strict inequality between continuous functions of the coefficients, it holds
  on a neighbourhood of this polynomial.

**Cross-check against the inner model, which is the real confirmation.** The
reduction predicts `(min_c L(c) - 2R)/rho -> min_j A_j = +0.0227239`. Measured
at `c = 0.9`: `+0.006846` at `rho = 0.02`, `+0.014829` at `rho = 0.01`,
`+0.018788` at `rho = 0.005`. The differences from `+0.02272` are `-0.01588`,
`-0.00790`, `-0.00394`, halving with `rho`, which is the `O(rho^2)` error order
of Proposition 2; and Richardson on the last two rows gives

```text
2 * 0.018788 - 0.014829  =  0.022747     against    0.0227239
```

agreeing to `3e-5`. Two instruments that share no code, one integrating in the
`Q` plane to `|Z| = 900` and one integrating the descending branch of the actual
polynomial to a root, agree on a nontrivial extrapolated constant.

**Erdős #1041 is not refuted.** `2R = 1.80003 < 2` and `min_c L(c) = 1.80018 <
2`, so the shortest descending branch pair still joins two roots by a path of
length below `2` inside `{|f| < 1}`. What dies is the `2R` normalisation: the
producer's route from the charge lemma to the problem passes through `(MIN)`,
and `(MIN)` is false. The same shape as `negative_results` entry 73, one level
further in.

**One instrument was wrong, and how it was caught.** An mpmath Newton
continuation in `u`, with `f(z) = v(1 - u^2)` solved from the previous node on a
geometric mesh, reported `L = 1.793856` for one hub at `c = 0.9, rho = 0.01`,
which would have made `(MIN)` hold. That value was stable under mesh refinement
by a factor of 256, so mesh independence proved nothing. It was caught by a
different test: **the chord sum of a sampled path is a lower bound for the length
of that path**, and the Newton path's chord sum was `1.979` against its own
reported length `1.794`. A chord sum above the reported length is proof that the
sampled path is discontinuous, i.e. that the continuation hopped sheets. The
ODE paths pass the same test (chord sums `1.7656` to `1.7686` against lengths
`1.8002`). The hop happens because the hub in question has
`f''(c) ~ 1.1e-5`, so the branch leaves at speed `|alpha| ~ 322` and crosses the
entire critical cluster within `u < 1e-4`; any continuation whose first steps in
`u` are not far finer than that will land on the wrong sheet. **Record this as
the method warning for this lane, alongside entry 73's chord-sum warning: mesh
independence does not certify a continuation, and the chord-sum-versus-length
comparison does.**

**Two more failure modes, both of which flipped a measured sign here.**

* **Coefficient reconstruction.** Building `f` from float64 roots and recovering
  the coefficients from them destroys the low-order coefficients, because `a_1`
  is of order `rho^{n-1}` while `a_0` is of order one. At `rho = 0.005` the
  reconstructed `a_1` carries about seven correct digits, the critical-point
  cluster moves, and the measured `min_c L(c)` changes by `4e-03`, which is
  forty times the margin. Every number in this section is computed from the
  polynomial's OWN exact coefficients at 60 digits.
* **The launch point.** A descending branch is started at
  `z(u_0) = c + alpha u_0` with `alpha = sqrt(-v / (f''(c)/2))`. Inside a tight
  critical cluster `f''(c) = n prod_{j != i} (c_i - c_j)` is a product of small
  separations, here `1.4e-12` at `rho = 0.005`, so `|alpha| = 9.2e+05` and the
  usual `u_0 = 1e-8` puts the launch point `9.2e-03` from the hub, further than
  the whole cluster. The launch is then simply not on the branch. The condition
  is `|alpha| u_0 << min_j |c_i - c_j|`, and `u_0 = 1e-12` satisfies it here
  with margin `1e-04`; the value is then stable down to `u_0 = 1e-16`.

## 6. The two weighted-mean families

`(MIN)` has two natural aggregate weakenings, both of which a proof would prefer
because an average is easier to control than a minimum.

**(A) The unweighted mean**, i.e. `sum_{e in C} L(e) <= 2R |E(C)|`. This is the
open producer's componentwise combined-charge form. It is FALSE, and
`negative_results` entry 73 records the refutation on the blown-up saddle-wall
quartic `f(z) = z^4 - a(s rho)^2 z^2 + (b + i delta)(s rho)^3 z - s^4` with
`a = 1, b = 2/5, rho = 1/50, delta = 1e-6, s = 0.99989`. Replayed here from
scratch: `sum_c L(c) = 6.000253120839` against `6R = 5.999939963992`, a charge
of `+3.1316e-04`, matching the recorded `6.000253120901` to `6.2e-11`; and
`min_c L(c) = 1.995615925568` against `2R = 1.999979987998`, so the family
satisfies `(MIN)`. In the widened inner model that family is the configuration

```text
Z = (-1, 0.719704943 - 6.67e-7 i, 0.280295057 + 8.96e-7 i),
A = (+0.296777291, -0.263053356, +0.036604311),
```

with `sum_j A_j = +0.070328 > 0` and `min_j A_j = -0.263053 < 0`. **The
entry-73 family is a point of the widened model, and its refutation is exactly
the statement that `sum_j A_j` has no sign.** That is a sharper reading than
"an isolated open family": positivity of the sum is a one-inequality event in a
`2n - 5`-parameter space, and the widened random sweep at `n = 4` reaches
`sum_j A_j = +0.0269` on a completely different configuration.

**(B) The `|f(c)|^s`-weighted mean**,

```text
W_s := ( sum_adm |f(c_j)|^s L(c_j) ) / ( sum_adm |f(c_j)|^s )  <=  2R,
```

proposed because the weight suppresses hubs near the escape level. It is also
FALSE. Because `L(c) >= |c - a| + |c - b|` for the two roots `a, b` the branches
reach, a violation can be certified from CHORDS alone, and chords are algebraic
in the roots. Three rows, all with roots strictly inside the open unit disc,
survive exact rational arithmetic:

| row | `n` | `s` | chord-only `W_s / (2R)` | exact certificate |
|---|---|---|---|---|
| `n4_s4` | 4 | 4 | `1.0006013331` | `sum_j w_j (chord_j - 2 R_up) = +1.0761e-05 > 0` |
| `n4_s8` | 4 | 8 | `1.0013972225` | `+3.1932e-07 > 0` |
| `n5_s8` | 5 | 8 | `1.0027239121` | `+5.3833e-03 > 0` |

The certificates are exact in the following sense, and the boundary matters. The
roots are rounded to Gaussian rationals with denominator `10^12`; `f` and `f'`
then have exact Gaussian-rational coefficients; each critical point is enclosed
in a rational disc by the Newton-Kantorovich test `2 beta K <= 1` with
`beta = |f'(c_0)/f''(c_0)|` and `K` a rational bound for `sup |f'''|` on
`D(c_0, 2 beta)`, the discs being verified pairwise disjoint so that each holds
exactly one critical point; admissibility `|f(c)| < 1` is decided exactly on
each disc; `|f(c)|^s` is rational because `s` is even; `sqrt` appears only
through rational lower bounds on chords; and `R` enters only through a rational
`R_up` with `|a_k - o|^2 <= R_up^2` for an exhibited rational centre `o`. The
ONE non-exact input is the branch-to-root PAIRING, which comes from the tracer.

**That input cannot be removed, and this is the sharp negative finding of this
section.** The pairing-free strengthening replaces `chord_j` by
`min over distinct root pairs (a,b) of |c_j - a| + |c_j - b|`, which is a valid
lower bound for `L(c_j)` whatever the branches do. On the three certified rows
that quantity gives `0.8989`, `0.8995`, `0.9561`, all below one. A dedicated
600-restart search maximising the pairing-free objective directly, at
`(n, s) = (3,8), (4,4), (4,8), (5,4), (5,8)`, reaches `1.0000000000` and never
exceeds it; the supremum appears to be exactly one, attained at the extremal
family. So `W_s` is refuted with a tracer-supplied pairing and is NOT refuted by
chords alone.

## 7. Claim boundary

* **Proved.** Proposition 1 (exact inner form), Lemma 3 and Proposition 4 (the
  hub endpoint cancellation and `K_j = -A_j`), Corollary 5 (the vertical-ray
  threshold `A = 0`), Proposition 6 (`A_j = 0` at `Z = (-1,0,1)`, `n = 4`). The
  parameter count `2n - 5` and the exclusion of the corpus slice for `n >= 4`
  are proved. The chord-sum test used to disqualify a discontinuous sampled path
  is proved (a chord sum never exceeds the length of the path it samples).
* **WITHDRAWN (conductor audit, 2026-09-05).** The degree-five refutation of
  `(MIN)` below is a saddle-connection wall specimen (section 5.4, boxed
  audit): the witness has two critical values with equal imaginary part to
  `1.8e-12` and ordered real parts, its minimum returns to negative under
  `1e-3` perturbations of `Z`, and `(MIN)` is NOT refuted. The numbers are kept
  as the specimen record. Original text of the claim follows.
* ~~Refuted, by finite computation with a stated margin.~~ `(MIN)` at degree
  five, on the explicit polynomial of section 5.4: `min_c L(c) = 1.800182484803`
  against `2R <= 1.800034190066`, margin `+1.48e-04`, all roots strictly inside
  the open unit disc, all four critical points simple and admissible with
  `|f(c)| = 0.59049`, every branch endpoint within `1.1e-15` of a root, the
  value stable across three step settings and reproduced at four other
  `(c, rho)` pairs, and independently predicted by the inner model to `3e-5`
  through a Richardson extrapolation in `rho`. This is FINITE COMPUTATIONAL
  EVIDENCE at the strength of `negative_results` entry 73, not a formal proof:
  the branch-length continuation itself is not formalised. What IS exact is the
  direction of the `R` bound, since `R` enters through an exhibited centre and
  is therefore over-estimated.
* **Derived.** Proposition 2's error order `O(rho^2)`; the scaling condition
  (W); the vacuity of admissibility in the cusp. These are matched asymptotics
  with the matching region exhibited, and each is validated numerically at the
  stated order.
* **Computed.** Every entry of the §5 table, the `sqrt(b)` law at degree four,
  the `n >= 5` real-configuration penalty in §5.2, the entry-73 replay, and the
  pairing-free chord supremum.
* **Exactly certified.** The three chord rows of §6, in Fraction arithmetic,
  MODULO the tracer-supplied branch-to-root pairing.
* **Not established.** The sign of `M_6`; the exact value of `M_5`; that
  `M_4 = 0` is the exact supremum rather than a very good approach to it. Any
  claim that Erdős #1041 is false. Any claim that the componentwise charge
  lemma is repairable, or that it is not.
* **Superseded.** `NearFeketeCuspLaw.md` §4's sentence "the surviving obligation
  holds strictly in a punctured neighbourhood of the Fekete family, in every
  direction, with a quantified margin" is correct along fixed-`h` rays and false
  in the (W) directions: at degree four the margin tends to zero, and at degree
  five it changes sign. §1, §2, §3, §5, §6 and §7 of that file are untouched;
  what changes is the SCOPE of §4, not any computation in it.
* **Consumers to update.** The open producer
  `critical_point_selection_with_inverse_ray_length_control` should not be
  launched at the componentwise combined-charge lemma, because the conclusion it
  is being proved for is false. Any consumer that reads
  `NearFeketeCuspLaw.md` §4 as a uniform near-Fekete margin needs the (W)
  restriction added.

## 8. Replay

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_near_fekete_inner_model.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_near_fekete_inner_model.py --part slice
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_near_fekete_inner_model.py --part entry73
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_near_fekete_inner_model.py --part e2e
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_near_fekete_inner_model.py --part chord
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_near_fekete_inner_model.py --part climb
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_near_fekete_inner_model.py --part refute
```

Parts: `slice`, `entry73`, `e2e`, `chord`, `climb`, `refute`. All six pass as of
2026-09-05; `refute` is the one that fails if the degree-five counterexample
stops holding.

The checker is stdlib plus numpy: the branch integrator is an adaptive
Cash-Karp RK45 written out inside it, so it does not depend on scipy, and it is
calibrated against the recorded `kappa_n` in the `slice` part before any other
part is trusted. It prints one JSON line carrying `status` and
`evidence_class`. No random number generator is used anywhere, so a failure is
reproducible.
