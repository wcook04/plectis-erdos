# Erdős 1041: the radial resultant sweep, and the near-field model of the origin-spoke route

Status: two exact identities, one exact entry-radius law for the first-order
model, one near-field model with an exactly critical optimum, and an explanation
of why two earlier searches pinned at the threshold. Current through 2026-08-27;
the exact replay below passes all A1--G checks. Erdős #1041 remains open;
nothing below claims otherwise.

The corpus's near-Fekete work is all about the **descent-branch** route:
[NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) rescales `z^n - m + eps h` to the
`eps`-free model `g(zeta) = zeta^n + n zeta` and reads `L(c) = 2R - kappa_n rho`
off it. This note does the same job for the **origin-spoke** route — the family
[TruncatedSpokeReduction.md](TruncatedSpokeReduction.md) and
[TwoSegmentContainmentReduction.md](TwoSegmentContainmentReduction.md) reduce the
problem to — and gets a different, simpler model with a different verdict.

The directional formulas below assume every root is nonzero, so that
`ahat_j = a_j / |a_j|` is defined. A configuration with a zero root needs a
separate zero-root treatment and is not silently included in the directional
identities.

## 1. The radial sweep identity

Write `f* (z) = prod_k (1 - conj(a_k) z)` for the reciprocal adjoint,
`p_m = sum_k a_k^m`, and `ahat_j = a_j / |a_j|`.

> **(RS-t).** For `|z| < 1/max_k|a_k|`,
> `-log|f*(z)| = sum_{m>=1} (1/m) Re(conj(p_m) z^m)`. Summing over the `n` root
> **directions** at radius `t`,
>
> ```text
> sum_j -log|f*(t ahat_j)|  =  sum_{m>=1} (t^m/m) Re(conj(p_m) sigma_m),
>                                                      sigma_m = sum_j ahat_j^m,
> ```
>
> and if all `|a_k| = r` then `p_m = r^m sigma_m`, so
>
> ```text
> sum_j -log|f*(t ahat_j)|  =  sum_{m>=1} ((t r)^m / m) |sigma_m|^2   >=  0,
> ```
>
> i.e. `prod_j |f*(t ahat_j)| = exp(- sum_m ((tr)^m/m)|sigma_m|^2) <= 1`,
> **decreasing in `t`**, for every `t` in `[0, 1/r)`.

*Proof.* `log f*(z) = sum_k log(1 - conj(a_k) z) = - sum_{m>=1} (z^m/m) conj(p_m)`
by the principal branch; take real parts and sum at `z = t ahat_j`. For equal
moduli the bracket is `conj(sigma_m) sigma_m`. ∎

**This is the whole radius, not only its endpoint.** At `t = r` the left side is
`- sum_{j,k} log|1 - conj(a_k) a_j| = -log|Res(f, f*)|` and the right side is
`sum_m |p_m|^2 / m`, so **(RS-t) at `t = r` is exactly Theorem RS** of
[RootCentredReciprocalSweep.md](RootCentredReciprocalSweep.md), i.e.
`research_packet.json::exact_results::reciprocal_adjoint_resultant_power_sum_identity`.
The identity above is the one-parameter family that interpolates it from the
trivial value `1` at `t = 0`.

Checked to `2.1e-13` over 72 (degree, radius, radial point) triples in degrees
2–9, with the truncation controlled by the **tail bound**
`n^2 x^{M+1}/((M+1)(1-x))`, not by a small term — the trap that file records as
having produced spurious errors up to `5.3`.

## 2. What it buys, and the exact reason it does not close

Two facts pair with it.

* **Blaschke majorant.** For roots in the closed unit disk, `f = B f*` with
  `B = prod_k (z-a_k)/(1-conj(a_k)z)` and `|B| <= 1` on the closed disk, so
  `|f| <= |f*|` there. Hence `|f*| <= 1` on `[0, a_j]` **implies** the origin
  spoke to `a_j` lies in `{|f| <= 1}`.
* **`log|f*|` is harmonic** on `|z| < 1/max|a_k|` — `f*` has no zeros there — so
  the log singularities that make `sum_j log|f(t a_j)|` useless pointwise are
  absent.

Together with (RS-t): for equal moduli and **every** radius `t`, at least one
root direction has `|f*(t ahat_j)| <= 1`, hence `|f(t ahat_j)| <= 1`, with an
explicit deficit `(1/n) sum_m ((tr)^m/m)|sigma_m|^2`.

> **This is an `L^1`-in-`t` statement and the index `j` moves with `t`.** So
> (RS-t) locates the failure exactly: it is not that no direction is ever good,
> it is that the good direction is not the same one throughout.

**The `L^infinity` upgrade is refuted, exactly, and not here.** Even the weakest
form — *some single* `j` good at *every* `t`, for `n` points on the unit circle —
is `(ONE-SPOKE)` of
[VisibilityOverlapReduction.md](VisibilityOverlapReduction.md), and that file
records it **FALSE at `n = 5`**, on an exact Gaussian-rational countermodel from
a concurrent line (`codex_root`, commit `9fede2b363`, checker
`formal_math/probes/erdos1041_one_spoke_countermodel.py`), re-verified there in
`Fraction` arithmetic: the five unit-modulus points `1`, `(-20 +/- 99i)/101`,
`(-28 +/- 195i)/197` have **every** one of the five products
`prod_k |t w_j - w_k|` above one somewhere on `[0,1]`. That is the sharp form of
what §3a below only measures, it is theirs, and it should be cited rather than
this note's shell counts. The general-position statement was already
`negative_results` 8/16 (Form A′).

## 3. The near-Fekete spoke law, and an exact balance identity

Put `a_k = omega^k (1 + e_k)`, `omega = exp(2 pi i / n)`, `eta = sum_k |e_k|`.
Differentiating `log|f|` in the roots,

```text
log|f(z)|  =  log|1 - z^n|  +  Re Lambda(z)  +  O(eta^2),
Lambda(z)  =  sum_k e_k / (1 - z omega^{-k})  =  sum_{m>=0} Ehat_m z^m,
Ehat_m     =  sum_k e_k omega^{-km}.
```

> **(BAL).** For every `t` and every `e`, exactly:
> `sum_{j=0}^{n-1} Lambda(t omega^j) = n Lambda(0) / (1 - t^n)`.

*Proof.* `sum_j Lambda(t omega^j) = sum_k e_k sum_l 1/(1 - t omega^l)` after
re-indexing `l = j-k`, and `sum_{l=0}^{n-1} 1/(1 - t omega^l) = n/(1 - t^n)`. ∎

Since `Re Lambda(0) = Re sum_k e_k = -Delta` with `Delta >= 0` the total radial
deficit, (BAL) gives `sum_j [log(1-t^n) + Re Lambda(t omega^j)] = n log(1-t^n) -
n Delta/(1-t^n) < 0`: the first-order form of the `L^1` statement of §2, now with
both terms separately nonpositive. Every harmonic `m` **not** divisible by `n`
cancels across the `n` spokes; only `Delta` and the `z^n` term survive.

Checked: (BAL) to `1.2e-13`; the `O(eta^2)` claim by its convergence rate — the
residual falls by `101.0` and `100.1` per decade of `eta`, i.e. quadratically.

## 3a. The spoke functional in closed form: positive kernels on the antisymmetric part

For a **pure angular** perturbation — `a_k = exp(i(2 pi k/n + theta_k))`, all
moduli exactly one, `Delta = 0`, which is the hardest case — the first-order form
collapses to something completely explicit. Since
`Lambda_0(z) := Lambda(z) - Lambda(0) = sum_k e_k z/(omega^k - z)`, evaluating at
`z = t omega^j` and re-indexing `l = k - j` gives
`Lambda_0(t omega^j) = sum_l e_{j+l} t/(omega^l - t)`, and with `e_k = i theta_k`,
`Re(i theta K) = -theta Im K`, `Im(t/(omega^l - t)) = -t sin(2 pi l/n)/|omega^l - t|^2`:

> **(SPOKE-KERNEL).** To first order,
> `log|f(t omega^j)| = log(1 - t^n) + P_j(t)` with
>
> ```text
> P_j(t) = sum_{l=1}^{floor((n-1)/2)} ( theta_{j+l} - theta_{j-l} ) * g_l(t),
>
> g_l(t) = t sin(2 pi l/n) / ( 1 - 2 t cos(2 pi l/n) + t^2 )   >  0   on (0,1).
> ```
>
> So the origin spoke to root `j` is contained iff
> `P_j(t) <= -log(1 - t^n)` for every `t` in `[0,1)`.

Four consequences, all immediate:

* **Every kernel is positive.** `g_l` is the conjugate Poisson kernel at angle
  `2 pi l / n`, and `sin(2 pi l/n) > 0` on the whole index range, so the sign of
  each contribution is the sign of its angular difference.
* **The functional sees only the antisymmetric part of `theta` about `j`.** The
  pairing `g_{n-l} = -g_l` is what collapses the `n-1` terms to
  `floor((n-1)/2)` differences.
* **A perturbation symmetric about root `j` leaves that spoke exactly
  contained**: `theta_{j+l} = theta_{j-l}` for all `l` gives `P_j == 0`, and
  `-log(1-t^n) > 0`.
* **`sum_j P_j == 0` identically**, which is (BAL) at `Delta = 0` — so the `L^1`
  statement of §2 is here the trivial one that `n` numbers summing to zero cannot
  all be positive.

Checked at degrees 3–9 against `log|f(t omega^j)| - log(1-t^n)` computed directly
from the coefficients, at four radii per ray: the relative error falls from
`3.6e-2` at `eta = 1e-3` to `9.3e-6` at `eta = 1e-7`, i.e. the residual is
`O(eta^2)` as a first-order law requires.

**This is the object `TruncatedSpokeReduction.md` needs and does not have.** The
entry radius of §4 is exactly the largest root of `P_j(t) = -log(1-t^n)`, and the
question "how many spokes are contained" is exactly "how many of the `n` numbers
`P_j`, which sum to zero, stay under the positive budget `-log(1-t^n)`
*uniformly in `t`*". Measured here: at `n = 3, 5, 7` that count drops to **one**
at angular perturbations as small as `1e-5`, so Form A′ fails arbitrarily close
to the extremal family at those degrees; at `n = 4, 6` the minimum observed is
two. **The count can reach zero**, which is stronger than anything measured here
and is not this note's: see the `(ONE-SPOKE)` countermodel cited in §2.

What this section adds to that refutation is the **mechanism**: the count is
governed by `floor((n-1)/2)` positive conjugate-Poisson kernels acting on the
antisymmetric part of the angular perturbation, so it is decided by the
*symmetry defect* of the configuration about each root, not by the size of the
perturbation.

## 4. The entry radius is a fractional power of the perturbation

On the ray `z = t omega^j` the first-order form is exactly
`t cos(psi_j) - t^n + (-Delta) + O(t^2 eta)` after the rescaling of §5, where
`psi_j = psi + 2 pi j/n` and `psi = arg Ehat_1`. Hence, at `Delta = 0`:

> **(TAU).** `tau_j = (cos psi_j)_+^{1/(n-1)}` — zero when `cos psi_j <= 0`, and
> otherwise the `(n-1)`-th root of the perturbation.

So the spoke to `a_j` fails on a **middle** interval `(0, tau_j)` and is
contained from `tau_j` outward. Measured against `tau` computed in root
coordinates by exact segment maxima at `n = 3`:

| `eta` | `1e-2` | `1e-3` | `1e-4` | `1e-5` |
|---|---|---|---|---|
| `tau` predicted | `9.3057e-2` | `2.9430e-2` | `9.3057e-3` | `2.9428e-3` |
| `tau` measured | `8.8693e-2` | `2.8992e-2` | `9.2453e-3` | `2.9383e-3` |
| ratio | `0.9531` | `0.9851` | `0.9935` | `0.9985` |

converging to 1, as a first-order law must. The same first-order sign test
predicts **which** spoke fails: at `n = 3` with angular perturbation
`(eta, 0, 0)` it predicts rays `0, 1` good and ray `2` bad, and that is measured
at every scale.

This is the law behind the numbers `TruncatedSpokeReduction.md` §3 reports
without one (`tau/|a| = 0.542751, 0.047854, 0.047854, 0.032779, 0.032779`): the
entry radius is small because it is a **fractional power** of the perturbation,
not because the perturbation is small.

**Consequence for `Delta > 0`.** The spoke survives in full iff
`max_t (t cos psi_j - t^n) <= Delta`, i.e. iff

```text
cos psi_j <= 0    or    (1 - 1/n) n^{-1/(n-1)} (cos psi_j)^{n/(n-1)}  <=  Delta.
```

So the origin-spoke route survives an angular perturbation of size `eta` exactly
when the radial deficit dominates `eta^{n/(n-1)}` — the same fractional-power
family as the descent route's cusp, with exponent `n/(n-1)` in place of
`1/(n-1)`.

## 5. The near-field model, and why it is exactly critical

Rescale `z = s zeta` with `s^{n-1} = |Ehat_1|`, so the linear and the `z^n` terms
balance. Dividing by `s|Ehat_1|`, the containment condition
`log|f| <= 0` becomes `W(zeta) <= delta` for the **`eta`-free, `R`-free model**

```text
W(zeta) = Re( e^{i psi} zeta )  -  Re( zeta^n )  =  Re H(zeta),
H(zeta) = e^{i psi} zeta - zeta^n,        delta = Delta / (s |Ehat_1|) >= 0.
```

`W` is harmonic — `{W <= 0}` is the preimage of a half plane under an analytic
map — and `W(0) = 0`, so the origin sits **on** the boundary of the good set, and
near the origin the good set is a genuine half plane, hence convex. That
convexity is the mechanism of Form A-cut at leading order: on a chord the linear
term attains its maximum at an endpoint, and both endpoints are on good rays by
construction.

The hardest rotation is `psi = pi/n`, where the `n` rays are anti-aligned. At
`n = 3`, `psi = pi/3`: rays `0` and `2` have `cos psi_j = 1/2` (so
`tau = 2^{-1/2}`) and only ray `1` is fully good. Taking the pair `(1,2)`, the
chord at radius `s` is the vertical segment through `-s/2`, and writing
`zeta = -s/2 + iy`,

```text
W = -s/4 - (sqrt3/2) y + s^3/8 - (3s/2) y^2,
```

a downward parabola, interior maximum at `y* = -sqrt3/(6s)` whenever
`s >= 1/sqrt3`, with value

```text
g(s) = s^3/8 - s/4 + 1/(8 s),      g'(s) = 0  <=>  3 s^4 - 2 s^2 - 1 = 0  <=>  s = 1,
```

and **`g(1) = 1/8 - 1/4 + 1/8 = 0` exactly.** The optimum is attained at
`zeta* = -1/2 - i sqrt3/6 = 3^{-1/2} e^{7 i pi/6}`, where *both* harmonics vanish
separately: `arg(e^{i psi} zeta*) = 3 pi/2` and `3 arg zeta* = 3 pi/2 (mod 2 pi)`.

> **The near-field model of the origin-spoke route is exactly critical: its
> optimum is `0` at the worst rotation, strictly negative elsewhere.**

At `psi = 0` the same pair gives `W = -s/2 + s^3/8 < 0` for `s < 2`, so
`model_V(0) <= -3/8`. The supremum over `psi` is therefore `0`, attained on the
measure-zero set `psi = pi/n (mod 2 pi/n)`.

## 6. Why every recorded search pins at exactly `1.0000000`

`TruncatedSpokeReduction.md` §6 reports `sup V = 1.00000000` with residual below
`1e-8`, and `TwoSegmentContainmentReduction.md` §5 reports `1.0000005438` and
calls it inner-search truncation. Both attach `negative_results` entry 19 — *a
supremum pinned just under a threshold is one basin* — and answer it with a
negative control.

§5 supplies a stronger answer than a control. **The objective's leading-order
model is identically critical at the worst direction**, so a searcher that pins
at `1.0000000` is not failing to find a violation; it is measuring a quantity
whose first-order variation about the extremal family is zero. Any margin is
second order in the perturbation, exactly as `NearFeketeCuspLaw.md`'s `O(rho^2)`
remainder is on the descent side.

Two consequences. A first-order (Hessian-free) argument cannot prove Form A-cut,
and equally cannot refute it. And a search residual of `5e-7` at `n = 3` is the
expected size of a second-order effect at that search's step scale, not evidence
either way.

Independent confirmation from a search run **in the shell** rather than in bulk
root coordinates — the coordinates `HardRegimeIsNearFekete.md` prescribes and
which no recorded Form A-cut search uses — parametrising
`z_k = (1+a_k) exp(i(2 pi k/n + t_k))` rescaled to `max|z_k| = 1`, with the
perturbation scale annealed over `1e-1 … 1e-7`:

| `n` | 3 | 4 | 5 | 6 |
|---|---|---|---|---|
| `sup V`, shell coordinates | `1.0000000000000` | `1.0000000000000` | `1.0000000000000` | `1.0000000000000` |
| `sup V`, bulk coordinates, 5 restarts | `1.0000000064` | `1.0000000055` | `1.0000000000` | `1.0000000000` |
| control (chord-or-origin, **known false**) | `1.0097379` | `1.0000000` | `1.0000000` | `1.0000000` |

The shell searcher returns to the extremal family **exactly** at every degree —
moduli `1.0` to the last bit, angular deviation `0` — and cannot leave it. That
is the signature §5 predicts. The control column fires only at `n = 3` at this
budget, so only that column carries information, exactly as
`TruncatedSpokeReduction.md` §6 records; where it fires, the known-false
statement breaks by `9.7e-3` against a Form A-cut residual of `6.4e-9`, six
orders of magnitude apart.

## 6a. The extremum is a cusp of exponent `n/(n-1)`, and it is strict

§5 says the leading model is critical, so the margin is decided below leading
order. Here is what it is. Keeping all roots **exactly** on the unit circle
(`Delta = 0`, the hardest case) and perturbing the regular `n`-gon along a random
unit angular direction `theta` at scale `eps`:

| `n` | 3 | 4 |
|---|---|---|
| `n/(n-1)` | `1.5` | `1.3333` |
| median measured exponent, 9 directions | `1.504` | `1.333` |
| spread | `1.501 … 1.540` | `1.311 … 1.386` |
| directions with `V > 1` | `0/9` | `0/9` |

> **`V - 1  ~  - c_n  eps^{n/(n-1)}`, with `c_n > 0` in every direction sampled.**

**An instrument correction belongs here, because it bit this measurement.** A
**uniform** grid in the hub radius `s` cannot resolve the optimum, which sits at
`s ~ eta^{1/(n-1)}` — a fractional power. On `[tau, 1]` with 200 points the step
is `5e-3` while the optimum at `eta = 1e-4`, `n = 3` is near `1e-2`, so the
reported `V` is inflated and the exponent came out as `1.08` in one direction
instead of `1.5`. This is the recorded scale-truncation defect class
(`negative_results` 34) in a new place, and it fails the same way: **upward in
`V`, i.e. against the mechanism**. The receipt uses a logarithmic `s` grid plus
the endpoint `s = tau`; with it the nine `n = 3` directions land in
`[1.501, 1.540]`. A first table computed on the uniform grid read `1.519 /
1.337 / 1.260 / 1.20 / 1.17` at `n = 3 … 7`; those numbers are withdrawn in
favour of the log-grid ones above.

Three things follow.

* **The regular `n`-gon on the unit circle is a strict local maximum of `V`, with
  value exactly `1`.** So Form A-cut holds in a neighbourhood of the extremal
  family at every degree measured. Measured, not proved — 52 directions across
  five degrees, none of them positive.
* **The exponent is `n/(n-1) < 2`, so `V` has an infinite second derivative
  there.** It is a cusp, not a smooth maximum, and a Hessian argument sees
  nothing — the same lesson `StraightSpokeHubCriterionLab.md` records for the
  descent side, now with an exponent attached for this route.
* **`n/(n-1)` is the exponent §4 derives independently**, as the threshold at
  which the radial deficit `Delta` covers the spoke's excess
  `(1-1/n) n^{-1/(n-1)} (cos psi_j)^{n/(n-1)}`. Two routes — a perturbation of
  the objective and an explicit one-ray calculation — give the same power, which
  is the check that the scaling `z = s zeta`, `s^{n-1} = |Ehat_1|`, is the right
  one.

### Degree three is the only degree where the model is critical

The exponent `n/(n-1)` is the *generic* rate, valid wherever
`model_V(psi) < 0`; at a rotation where the model is critical the leading term
vanishes and the margin drops to the next order. §5 exhibits exactly one such
rotation, `psi = pi/3` at `n = 3`. **It is the only one at any degree**, and the
reason is a counting argument:

> The number of fully good rays is `#{ j : cos(psi + 2 pi j/n) <= 0 }`, i.e. the
> number of `n`-th roots of unity in a closed half plane, which is at least
> `floor(n/2)`. That is `>= 2` exactly when `n >= 4`, and equals `1` only at
> `n = 3`.

With two fully good rays the hub radius may be taken small: both ray maxima are
`s cos psi_j - s^n <= -s^n < 0`, and on the chord the linear term attains its
maximum at an endpoint (it is linear) while the `-Re(zeta^n)` term is `O(s^n)`,
so the whole staple is strictly negative for small `s`. Hence
`model_V(psi) < 0` for every `psi` as soon as `n >= 4`, and the margin is
`Theta(eps^{n/(n-1)})` uniformly in the direction.

**So the one degree at which this route's leading model degenerates is the one
degree at which Erdős #1041 is already proved**
([CubicCriticalHub.md](CubicCriticalHub.md)). At `n = 3` the next order can still
be signed by hand, because a pure angular perturbation forces
`Ehat_2 = -conj(Ehat_1)` (the DFT of a real vector satisfies
`Ehat_{n-m} = -conj(Ehat_m)`, and `n - 1 = 2` there); with
`zeta*^2 = (1/3) e^{i pi/3}` and `arg Ehat_1 = pi/3` this gives
`Re(Ehat_2 zeta*^2) = -|Ehat_1|/3 < 0`, a strictly negative correction. For
`n >= 4` that pairing does not tie `Ehat_2` to `Ehat_1`, but the counting
argument means nothing has to be signed there.

The measured exponents converge from above as `eps` shrinks, which is what a
leading fractional power plus a higher correction must do; the widest outliers
(`1.540` at `n = 3`, `1.386` at `n = 4`) are the directions nearest the
critical rotation, where the crossover toward the next order has begun.

## 7. Two corroborations on the descent side

Recorded here because they were produced by the same instrument pass and bear on
the standing obligation, not because they are this note's subject.

* **Independent reproduction of the degree-four obligation failure.** A hill
  climb in `beta`-space seeded independently of
  [ComponentDepthRefutation.md](ComponentDepthRefutation.md) §8 finds a
  *different* degree-four admissible `beta` with `L(c*)/(2 Rt) = 1.0000893`
  (slack `1.3e-9`, `Rt = 1.000420`). The same engine reproduces that note's
  stored witness at `Rt = 1.00091105331882` (14 digits against its
  `1.00091105331881554`) and `L/(2 mu^{1/4}) = 1.0010746` against its
  `1.00107324`, the difference being a finer inscribed polygon. So the failure of
  `L(c*) <= 2R` at the minimal hub is not one corner: it has at least two
  basins at degree four.
* **The `beta`-space table past degree five.** `HubModuliReduction.md` records
  `sup L/2` over admissible `beta` as `0.99988 / 1.00107 / 1.00438` at
  `n = 3,4,5` and states degrees six and above were not reached. A hill climb at
  `n = 6` reaches `L/2 = 1.0125` (slack `6.9e-7`) — so the strong form's
  violation **grows** with degree — while the obligation survives there at
  `L/(2Rt) = 0.98471`, because `Rt = 1.02826` grows faster. These are basin
  records, not suprema.

## 8. Claim boundary

**Not first here.** The failure of the `L^infinity` upgrade of §2 — the sharp,
exact, on-the-circle form — is `(ONE-SPOKE)` of
[VisibilityOverlapReduction.md](VisibilityOverlapReduction.md), refuted at
`n = 5` by a concurrent line the same day (`codex_root`, commit `9fede2b363`).
Cite that, not §3a's shell counts, for "the origin-spoke route fails". §3a's
contribution is the mechanism, not the refutation.

Proved here, by ordinary mathematics: (RS-t) and its specialisation to Theorem RS
at `t = r`; the Blaschke majorant consequence of §2; the balance identity (BAL);
the entry-radius law (TAU) as a statement about the first-order model; the
`n = 3` model computation of §5, which is exact algebra (`3s^4 - 2s^2 - 1 = 0`,
`g(1) = 0`).

Computed and reproducible from the receipt: the `2.1e-13` identity check with
tail-bounded truncation, the `1.2e-13` balance check, the quadratic residual
rates `101.0 / 100.1`, the `tau` convergence table of §4, and the two
fail-closed controls (a pinned `n = 3` witness where one spoke always exits, and
the recorded five-root witness where **no** full spoke is contained, reproducing
`tau/|a| = 0.542751, 0.047854, 0.047854, 0.032779, 0.032779` to six digits).

Measured, not proved: the shell suprema of §6, the cusp exponent and its
strictness in §6a (52 perturbation directions across five degrees, none
positive), the `L^infinity` failure counts of §3a, and the two `beta`-space
records of §7. Basin records, per `negative_results` entry 19.

**Not established.** The **constant** `c_n` in §6a, and any proof that it is
positive in every direction rather than in the sampled ones: that is exactly what
would give Form A-cut, hence Erdős #1041, in a quantified neighbourhood of the
extremal family, and it is the obvious next object. The counting argument of §6a
proves `model_V(psi) < 0` for `n >= 4` *at leading order in the model*; carrying
that to the polynomial itself needs the `O(eta^2)` remainder controlled
uniformly, which is not done here — the same gap as
`NearFeketeCuspLaw.md`'s `O(rho^2)`. Anything about configurations far from the regular polygon, where `D` is
small and the Fekete deficit is large — untouched here, and the other half of
`HardRegimeIsNearFekete.md`'s split. And no novelty claim against the literature:
(RS-t) is an elementary Schur–Cohn-type expansion and a priority check must
precede any such claim. **Erdős #1041 remains open.**

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_radial_resultant_sweep.py
```

The 2026-08-27 replay reports A1--A3, B1--B2, C, D1--D2, E, F, and G as
`[PASS]`, ending with `all checks passed`. Those checks are numerical or
instrument controls for the quantities labelled as such above; they do not
turn the ordinary proofs into Lean theorems or close the remaining transfer
obligation.
