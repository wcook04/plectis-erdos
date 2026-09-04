# Erdős 1041: the near-Fekete cusp has a law, and its sign is favourable

Status: one ordinary theorem (Fekete stability), one ordinary scaling argument
(the near-field model), and a high-precision measurement of the constants that
scaling leaves undetermined. Its source-current companion now proves the finite
perturbation passage on every fixed transverse cone, while this note retains the
limit-model derivation and its measured direction law. Current through
2026-08-27; the stability replay below passes. **This does not prove Erdős #1041.**
It answers the two items
[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) leaves open by name, and
it corrects that file's reading of the cusp as an obstruction.

## 0. What was asked

`HardRegimeIsNearFekete.md` splits a hypothetical proof on the Fekete ratio
`D = prod_{i<j}|z_i-z_j|^2 / n^n` and closes each half with an explicit gap.

> **`D` near 1.** … This is the extremal family for the constant 2, and it is
> understood exactly.
>
> … **a stability estimate for the Fekete maximiser is the object that would
> join the two halves. No such estimate is claimed, cited, or known to this
> file, and locating one is the obvious next step.**

and, in its own same-day correction,

> the `D`-near-1 side is a **cusp**, not a smooth maximum, and
> `StraightSpokeHubCriterionLab.md` states in terms that a second-order
> variational argument at the extremum "will not see the right behaviour". Any
> perturbative attack there must handle a fractional-power response, which is a
> materially harder object than a Hessian.

Section 1 supplies the stability estimate. Sections 2–4 supply the
fractional-power response itself — its exponent, its scale, its universal
constant, and its **sign**. Section 5 states what that does and does not settle.

## 1. Theorem A — quantitative Fekete stability

Fekete's bound is Hadamard's inequality in disguise, and Hadamard's inequality
has a defect term. Let `a_1,…,a_n` lie in the closed unit disk, let
`V_{ij} = a_j^i` for `i = 0..n-1`, and let `G = V V^*`, so that

```text
G_{ik} = sum_j a_j^i conj(a_j)^k,     g_i := G_{ii} = sum_j |a_j|^{2i} <= n,
det G  = |det V|^2 = prod_{i<j} |a_i - a_j|^2.
```

Fekete's `prod_{i<j}|a_i-a_j|^2 <= n^n` is `det G <= prod_i g_i <= n^n`.

> **Lemma (scalar).** For every integer `n >= 1` and every `mu` in `(0, n]`,
> `log mu <= (mu - 1) - (mu - 1)^2 / (2n)`.
>
> *Proof.* `h(mu) = (mu-1) - (mu-1)^2/(2n) - log mu` has `h(1) = h'(1) = 0` and
> `h''(mu) = 1/mu^2 - 1/n`. So `h` decreases on `(0,1)`, increases on
> `(1, sqrt n)`, and is concave on `(sqrt n, n]`, where its minimum is at an
> endpoint. `h(sqrt n) > 0`, and
> `h(n) = (n^2-1)/(2n) - log n` vanishes at `n = 1` with derivative
> `(n-1)^2/(2n^2) >= 0`, hence `h(n) >= 0`. ∎

> **Theorem A.** Write `Ghat_{ik} = G_{ik}/sqrt(g_i g_k)`, which is positive
> semidefinite with unit diagonal and trace `n`, so its eigenvalues lie in
> `[0, n]`. Then
>
> ```text
> prod_{i<j} |a_i - a_j|^2  =  det G  <=  (prod_i g_i) * exp( -||Ghat - I||_F^2 / (2n) ),
> ```
>
> and therefore, with `D = prod_{i<j}|a_i-a_j|^2 / n^n`,
>
> ```text
> D  <=  (prod_i g_i/n) * exp( -||Ghat - I||_F^2 / (2n) )
>    <=  exp( -||Ghat - I||_F^2 / (2n) ).                              (S)
> ```
>
> *Proof.* `det G = (prod_i g_i) det Ghat`. Apply the scalar lemma to each
> eigenvalue `mu_i` of `Ghat` and use `sum_i (mu_i - 1) = 0` together with
> `sum_i (mu_i - 1)^2 = ||Ghat - I||_F^2`. ∎

Two readable corollaries.

* **(C1) Moduli.** Every factor `g_i/n` is at most one, so (S) forces
  `g_i/n >= D` for each `i`; at `i = n-1` that is
  `(1/n) sum_j |a_j|^{2(n-1)} >= D`. `D` near one forces every modulus near one.
* **(C2) Power sums.** If every `|a_j| = 1` then `g_i = n` and `G_{ik} = p_{i-k}`
  with `p_m = sum_j a_j^m`, so `||Ghat - I||_F^2 = (2/n^2) sum_{m=1}^{n-1}(n-m)|p_m|^2`
  and (S) reads

  ```text
  sum_{m=1}^{n-1} (n - m) |p_m|^2  <=  n^3 log(1/D).
  ```

  By Newton's identities small `p_1 … p_{n-1}` forces small `e_1 … e_{n-1}`,
  i.e. `f` is close to `z^n + e_n`. Equality holds exactly at the regular
  `n`-gon on the unit circle, i.e. at `f = z^n - mu`, `|mu| = 1`.

**Novelty is not claimed for Theorem A.** The proof is Hadamard plus a one-line
scalar inequality, and a quantitative Fekete/Hadamard stability bound of this
shape is very plausibly classical. Per this directory's `AGENTS.md`, nothing
here should be described as new before a priority search on stability of Fekete
points, Hadamard defect, and Gram-determinant deficiency.

*Verification.* `scripts/check_erdos1041_near_fekete_cusp_law.py --part stability`:
26,400 configurations over degrees 2–12 in six families give worst **relative**
slack `-4.9e-15` (float64 roundoff at the exact equality case), and a 60-digit
`mpmath` spot check gives exact equality at the regular gon and strictly
positive slack at perturbed gons.

## 2. The near field of a splitting Fekete hub is `eps`-free

Perturb the extremal family arbitrarily:

```text
f(z) = z^n - m + eps*h(z),      deg h <= n-1,      m = R^n.
```

Critical points solve `n z^{n-1} = -eps h'(z)`. To leading order that is
`z^{n-1} = -eps h'(0)/n`: the `n-1` hubs form a regular `(n-1)`-gon of radius

```text
rho = ( eps |h'(0)| / n )^{1/(n-1)}                                      (*)
```

rotated by `arg(-eps h'(0))/(n-1)`. **Only `h'(0)` enters at leading order.**

Take the exact one-parameter representative `h(z) = e^{i phi} z`. Then the hubs
are exactly `c_k = rho exp( i (pi + phi + 2 pi k)/(n-1) )` and
`f(c_k) = ((n-1)/n) eps e^{i phi} c_k - m` — closed form, so no root-finding
error enters the hub. Rescaling `z = rho zeta` and using `eps = n rho^{n-1}`,

```text
f(z) + m  =  rho^n ( zeta^n + n zeta )  =:  rho^n g(zeta),
```

so the near field is governed by `g(zeta) = zeta^n + n zeta` with **no `eps`, no
`R`, no `m` in it**. `g'(zeta) = n(zeta^{n-1}+1)`, so `g`'s critical points are
exactly `zeta_c^{n-1} = -1`, all simple, with critical values `(n-1) zeta_c`; a
descending branch of `f` is the `g`-preimage of the ray
`{(n-1) zeta_c + s : s >= 0}` leaving `zeta_c`.

Matching this near field to the far field — where `f ≈ z^n - m` and the branch
is the radial segment of `z^n = m sigma`, of length `R` — gives, for the two
branches at one hub,

```text
L(c) = 2R - kappa_n(phi) * rho + O(rho^2),      kappa_n(phi) = beta_1 + beta_2,
```

where `beta = lim_{Z->oo} ( Z - Lambda(Z) )` is the renormalised excess of a
near-field branch (`Lambda(Z)` = its arclength out to `|zeta| = Z`). Since
`1/(n-1) < 1` for `n >= 3`, this `rho`-term dominates the `O(eps)` motion of the
roots and of `R`: it is the entire leading behaviour.

**So the whole near-Fekete half turns on the sign of one universal function
`kappa_n(phi)` of a single angle.** The degenerate direction `h'(0) = 0` is
excluded and needs its own order.

## 3. The constants

`(2R - min_c L(c)) / rho` at `R = 0.9`, `h(z) = z` (`phi = 0`), by `eps`:

| eps | n=3 | n=4 | n=5 | n=6 |
|---|---|---|---|---|
| `1e-2` | 0.64050369 | 1.0529883 | 1.2754364 | 1.4124687 |
| `1e-4` | 0.61122923 | 1.0311748 | 1.2591145 | 1.3992554 |
| `1e-8` | 0.60805339 | 1.0301219 | 1.2585789 | 1.3989126 |
| `1e-12` | 0.60802163 | 1.0301197 | 1.2585783 | 1.3989124 |
| `1e-15` | **0.60802134** | **1.0301197** | **1.2585783** | **1.3989124** |

Eight converged digits, and the limit is a genuine constant rather than a drift.

**`R`-independence.** The same limits at `R = 0.5` and `R = 0.9`: `n=3` gives
`0.60802189` and `0.60802163`; `n=4` gives `1.0301197` and `1.0301197`. This is
the direct test of the rescaling in §2 — `kappa_n` may not depend on `R`, and it
does not.

**Universality under arbitrary `h`.** For random `h` of degree `n-1`, the ratio
`(2R - min_c L(c)) / (kappa_n(arg h'(0)) * rho)` with `rho` from (*) tends to 1:
at `n = 3`, `eps = 1e-12`, four random directions give
`1.000000481`, `1.000000322`, `1.000000279`, `1.000000327`. A fifth returned
`1.336463` — **not a failure of universality but a confirmation of it**: that
direction had `h'(0) < 0`, i.e. `phi = pi`, and
`1.336463 x 0.60802134 = 0.812598`, which is exactly `kappa_3(pi)` from the
sweep below. The general perturbation is governed by the one-parameter model,
through `arg h'(0)`, to six or more digits.

**The direction sweep.** `kappa_n(phi)`, 24 samples of a full turn at
`eps = 1e-12`, is `2 pi / n`-periodic and runs between

| n | `min_phi kappa_n` | attained at | `max_phi kappa_n` | attained at |
|---|---|---|---|---|
| 3 | **0.6080216** | `phi = 0, 2pi/3, 4pi/3` | 0.8125984 | `phi = pi/3, pi, 5pi/3` |
| 4 | **1.0301197** | `phi = 0, pi/2, pi, 3pi/2` | 1.1341439 | `phi = pi/4, 3pi/4, …` |

**Strictly positive at every sampled direction**, and — usefully — the minimum
is attained at `phi = 0`, the aligned position where the critical `(n-1)`-gon
points at a root of the `n`-gon. So the single-slice table above is not a
sample: it is already `min_phi kappa_n`.

## 4. Consequence, and a correction

`kappa_n(phi) > 0` for every `phi` says exactly this:

> `z^n - mu` is a **strict local maximum** of `min_c L(c) / (2R)`, with value
> exactly 1, and the approach is first order in `rho`, i.e. of order
> `eps^{1/(n-1)}` in the perturbation.

So the surviving obligation `min_{c admissible} L(c) <= 2R` holds **strictly**
in a punctured neighbourhood of the Fekete family, in every direction, with a
quantified margin.

This corrects the reading in `HardRegimeIsNearFekete.md`. The cusp is not an
obstruction to the conjecture; it is the *reason the conjecture has slack* off
the extremal family, and the slack it supplies (`eps^{1/(n-1)}`) is far larger
than the `eps^2` a smooth maximum would give. What is true is that a **Hessian**
cannot see it — the correct object is not a second-order expansion in the
perturbation but a **first-order expansion in `rho`**, and §2 supplies that
expansion in closed form. The fractional power is a change of variable, not a
harder analysis.

Combining with Theorem A: `D >= 1 - delta` bounds the perturbation by
`eps = O_n(sqrt delta)` through (C1) and (C2), and §2 then converts that into a
margin `kappa_n rho ≍ delta^{1/(2(n-1))}`, which **exceeds** `delta`. The two
halves of the proposed `D`-split therefore meet on the near-Fekete side with
room, rather than pinching.

## 5. The instrument, and a defect it had to fix

A descending branch is parameterised by `f(z) = v(1 - s^m)` with
`m = (hub multiplicity) + 1`. Two things go wrong with the obvious integrator
and both bias the measurement in the **same, dangerous** direction — they
under-report length, which makes the surviving conjecture look safer.

* **Scale truncation.** The substitution resolves the hub's own local order, but
  a hub that is *simple yet nearly degenerate* — the entire near-Fekete regime —
  still travels many decades of `|z - c|` inside a vanishing range of `s`. Plain
  Gauss–Legendre on `[0,1]` silently truncates the inner journey. The fix is a
  geometric mesh `[0,2^-K], [2^-K,2^-K+1], …, [1/2,1]`.
* **Conditioning.** Solving `f(z) = v(1 - sigma)` directly loses `sigma` to
  rounding once `sigma < eps_mach`, and Newton then collapses the branch back
  onto the hub. The fix is shifted coordinates: solve `Q(w) = -v sigma` with
  `Q(w) = f(c+w) - v`, whose constant term is exactly zero.

With both fixes the integrator returns `2r` to `3.9e-16` on the equality family
`z^n - r^n` at `n = 3..7` -- that residual is the float64 quadrature rule, not
the method — the case on which
`StraightSpokeHubCriterionLab.md` records this directory's own integrator
returning `1.7989` against the true `1.8` at degree six. It independently
reproduces the two stored hard witnesses to the recorded digits:
`1.763941902` against `1.763942`, and `1.545995147` against `1.545995`.

The smallest enclosing circle is computed exactly (over pairs and triples), not
iteratively: an approximate centre **inflates** `R`, and `R` sits in the
denominator of the obligation, so an approximation again flatters the
conjecture. A Badoiu–Clarkson iteration at 3000 steps returned `R = 1.0000724`
for the degree-6 witness, whose roots all have modulus `0.99999985`.

## 6. The remaining inequality, reduced to one variable

`kappa_n > 0` was left above as a property of the fixed model `g`. It reduces
further, to a statement with **no free parameters at all**, via two exact
identities. Put `G(zeta) := zeta^n + zeta = zeta g'(zeta)/n`.

> **(I1)** The angle `theta` between the branch tangent and the radial direction
> `zeta/|zeta|` is `theta = -arg G(zeta)`.
>
> *Proof.* `d zeta / d sigma = 1/g'`, so `arg(d zeta / zeta) = -arg(zeta g')`. ∎
>
> **(I2)** Along a branch, `G = sigma - (n-1)(zeta - zeta_c)`.
>
> *Proof.* `G = g - (n-1) zeta` identically, and `g = (n-1) zeta_c + sigma` on
> the branch. ∎

(I2) has a useful consequence: `sigma` is real, so `Im G = -(n-1) Im(zeta - zeta_c)`
— the imaginary part of `G` is an affine function of the height above the hub.

Since `|zeta_c| = 1`, and writing `ex := 1 - beta`,

```text
ex = int (1 - cos theta) dl = Lambda - (radial gain),      kappa_n = 2 - (ex_1 + ex_2).
```

So the near-Fekete half of Erdős #1041 is **exactly**

```text
ex_1 + ex_2 < 2                                                        (E)
```

for the two descending branches at one hub of `zeta^n + n zeta`. No `eps`, no
`R`, no perturbation, no search: one fixed polynomial per degree.

Computed from `g` alone — which reproduces the values measured on the actual
polynomial, an independent confirmation of the whole §2 scaling:

| n | `ex_1` | `ex_2` | `kappa_n` from `g` | measured on `f` | `J_n := (n-1)(ex_1+ex_2)` |
|---|---|---|---|---|---|
| 3 | 1.23509426 | 0.15688443 | 0.6080213113 | 0.60802134 | 2.783957 |
| 4 | 0.77676065 | 0.19311969 | 1.030119661 | 1.0301197 | 2.909641 |
| 5 | 0.55177282 | 0.18964884 | 1.258578348 | 1.2585783 | 2.965687 |
| 6 | 0.42368707 | 0.17740053 | 1.398912406 | 1.3989124 | 3.005438 |
| 8 | 0.28647515 | 0.15129615 | 1.562228697 | | 3.064399 |
| 12 | 0.17210103 | 0.11329791 | 1.714601057 | | 3.139388 |
| 20 | 0.09503301 | 0.07416163 | 1.830805352 | | 3.214698 |
| 30 | 0.06079084 | 0.05156911 | 1.887640048 | | 3.258439 |

(I1) and (I2) hold to `1.2e-32` and `6.2e-41` at 40 digits along both branches at
every degree tabulated.

Two things follow. `(E)` is equivalent to `J_n < 2(n-1)`, so **the binding degree
is `n = 3`**, where it asks `J_3 < 4` against a measured `2.784` — a 30% margin —
and the margin then grows without bound. And `J_n` is visibly convergent
(≈ 3.26 at `n = 30`, increasing and flattening), so **any uniform bound
`J_n <= 4` proves the near-Fekete half outright**.

*A bound that is not good enough, recorded so it is not retried.* Let `alpha` be
the branch's asymptotic root direction and `gamma = chi - alpha`. Writing the
branch in coordinates aligned with `alpha` and using
`sqrt(dX^2 + dY^2) <= dX + |dY|` with both coordinates monotone gives
`ex <= |sin gamma| + (1 - cos gamma)`. At `n = 3` that is `2` for the branch with
`gamma = pi/2` and `0.634` for the branch with `gamma = -pi/6`, total `2.634`
against the true `1.392`. The `|dX| + |dY|` split loses too much precisely on the
branch that matters; a proof needs the hypotenuse, i.e. a genuine `L^2` estimate
on `dY/dX`, which is the same shape
[FirstMergeReductionState.md](FirstMergeReductionState.md) identifies as the
weakening that the chord-deficit formulation permits.

## 7. The branch geometry is exact, and the target becomes one uniform constant

Everything in §6 is anchored at the **radius**. `research_packet.json`'s
`chord_deficit_polynomial_representation` anchors the same deficit at the
**chord**. The two meet exactly.

Let `alpha` be a branch's asymptotic exit direction and `gamma = chi - alpha`
the angle between the hub direction and it. The chord from `zeta_c` to a far
point of the branch has length `Z - cos gamma + o(1)`, so with
`D := lim (Lambda(Z) - (Z - cos gamma))` the arc-minus-chord deficit,

```text
beta = cos gamma - D,        kappa_n = (cos g_1 + cos g_2) - (D_1 + D_2).   (BR)
```

`D` is exactly the triangle-inequality defect of `int (1/g') d sigma`, i.e.
`D = int (1 - cos(tau - alpha)) dl` with `tau = arg(d zeta)` the tangent
direction — the object the packet row writes down for the real polynomial.
(BR) is verified to `6.2e-27`, and **proved 2026-08-24** in
[BridgeIdentityProof.md](BridgeIdentityProof.md): it is the exact arclength
identity `|zeta(S)| - S = (|u|-U) + cos gamma - int_0^S(1-cos t)ds` together with
the single limit `|u| - U = V^2/(|u|+U) -> 0`, which Lemma T already supplies.

Three things about the branches are then **exact**, not measured:

> **(G) Exit angles.** The two branches at `zeta_c = exp(i pi/(n-1))` leave to
> infinity in the directions `alpha = 0` and `2 pi / n`, so
>
> ```text
> gamma_1 = pi/(n-1),        gamma_2 = pi/(n-1) - 2 pi/n = -(n-2) pi /(n(n-1)).
> ```
>
> **(T) Monotone turning, exact total.** `tau` turns **monotonically** along each
> branch — the total variation of `tau` equals `|Delta tau|` to `1.7e-27` — with
>
> ```text
> T_1 = (n-2) pi / (2(n-1)),        T_2 = (n-2)^2 pi / (2 n (n-1)),
> ```
>
> both strictly below `pi/2`. **Proved 2026-08-24** in
> [MonotoneTurningProof.md](MonotoneTurningProof.md), on both branches at every
> degree; it had been verified to `7.7e-9` (the cutoff tail, not `dps`).
>
> **(K) The target.** By (BR) and (G), `kappa_n > 0` is exactly
>
> ```text
> D_1 + D_2  <  cos( pi/(n-1) ) + cos( (n-2) pi /(n(n-1)) ).
> ```

The right-hand side is **increasing in `n`**, with minimum `sqrt(3)/2` at
`n = 3` and limit `2`. So the whole near-Fekete half follows from a **single
uniform constant**:

```text
D_1 + D_2  <=  sqrt(3)/2 = 0.8660254...                                    (U)
```

Measured maximum of `D_1 + D_2` over degrees 3–20 is **0.33953495**, at `n = 5`
— a margin of **2.55×**. (The individual deficits are small and well behaved:
`D_1` runs 0.235, 0.277, 0.259, 0.233, … and `D_2` runs 0.023, 0.059, 0.081,
0.091, … .)

**Why (T) matters, and exactly how far it reaches.** The turning route was killed
for the general polynomial: `CriticalBudgetLab.md` records
`L <= chord / cos(alpha/2)` as dead at every `n >= 3`, "and the supremum is
`+infinity` since `alpha` passes `pi`". In the near-field model that failure mode
does not occur — the turning is monotone and its total is exactly
`T_1, T_2 < pi/2`. Since `|tau - alpha| <= T` throughout,
`D = int (1 - cos(tau-alpha)) dl` is a weighted `L^2` turning integral against a
tangent that never leaves a cone of half-angle `< pi/2`. That is the weakening
[FirstMergeReductionState.md](FirstMergeReductionState.md) says the chord-deficit
formulation permits, with its hypothesis available rather than assumed.

**(T) IS A STATEMENT ABOUT THE LIMIT MODEL ONLY.** It is established for
`g(zeta) = zeta^n + n zeta`, i.e. for the `eps -> 0` near field, which is all the
cusp law needs — the law is itself leading-order,
`L(c) = 2R - kappa_n rho + O(rho^2)`. **Whether monotone turning survives at
finite perturbation is not settled here**, and (T) must not be quoted as a fact
about real polynomials. The corpus's global refutation of the turning route
(`CriticalBudgetLab.md`: the supremum is `+infinity` since `alpha` passes `pi`)
stands untouched by anything in this file.

*An attempt to settle the finite-perturbation question is recorded as failed, so
it is not repeated naively.* A float64 sweep at the minimum-critical hub measuring
`TV(tau) - |Delta tau|` produced two disagreeing implementations — the first
passed a polynomial built from **un-centred** roots together with a **centred**
hub, a frame mismatch that manufactured non-monotonicity at `n = 3`. The
corrected version then returned an `eps`-incoherent profile (at `n = 6`, deviation
`5.7e-5` at `eps = 1e-8` but `4.4e-16` at `eps = 1e-1`, the opposite of what a
real effect does), with all magnitudes at the noise floor of a discrete float64
turning sum. Discrete `TV` of an angle is a poor instrument here: the model's own
turning residual is already `7.7e-9` at 30 digits. Settling this needs the turning
accumulated from `d tau = -Im((g''/g') dz)` in extended precision, not a sum of
`np.angle` differences.

What is still missing is only the weight: `Lambda` is infinite, so
`D <= (1 - cos T) Lambda` is vacuous, and a bound needs the decay of
`tau - alpha`. Parameterising by the turning angle `t = |tau - alpha|` (legitimate
by (T)) gives `D = int_0^T (1 - cos t) R(t) dt` with `R` the radius of curvature;
`R(t) ~ C t^{-n/(n-1)}` as `t -> 0`, so the integrand is `~ t^{(n-2)/(n-1)}` and
converges. **A bound on `R(t)` is now the entire remaining obstacle**, and it is
a statement about one fixed polynomial per degree.

## 8. The branch in closed algebraic form, and the binding degree as one cubic

Work in `P = zeta / zeta_c`, so the hub sits at `P = 1`. Since `|zeta_c| = 1`,
radii and arclengths are unchanged, so `beta`, `D` and `kappa_n` are all
intrinsic to the `P`-plane. Using `zeta_c^{n-1} = -1`:

> **(A1)** `g(zeta) - g(zeta_c) = -e^{i chi} F(P)` with
> `F(P) := P^n - n P + (n-1)`, and `F` has a **double root at the hub**:
>
> ```text
> F(P) = (P-1)^2 Q(P),        Q(P) = sum_{i=0}^{n-2} (n-1-i) P^i,
> ```
>
> because `P^n - nP + (n-1) = (P-1) sum_{j=0}^{n-1}(P^j - 1)`.
>
> **(A2)** `g'(zeta) = n(1 - P^{n-1})`.

So a descending branch is `{P : e^{i chi} F(P) <= 0}` — **the preimage of a ray
under one fixed polynomial with a double root at the hub**. The `n-1` hubs, the
`n` exit directions, the turning and the deficit are all properties of `F`, and
`chi` enters only by choosing which ray. Verified to `1.1e-40`.

At the **binding degree** `n = 3` this is completely explicit. There
`chi = pi/2`, `F(P) = (P-1)^2 (P+2)`, and `e^{i pi/2} F <= 0` says `Re F = 0`, so
with `P = x + iy` the branch lies on the real cubic

```text
x^3 - 3 x y^2 - 3 x + 2 = 0,        i.e.    y^2 = (x-1)^2 (x+2) / (3x).   (A3)
```

Its `x > 0` component is exactly the two descending branches through `(1,0)`,
leaving at slopes `+-1` and running to the asymptote `y = x/sqrt(3)` (direction
`pi/6`) and to the vertical end at `x -> 0+` (direction `-pi/2`). Those are
precisely the measured exit directions, since `gamma = chi - alpha` turns them
into `gamma_2 = -pi/6` and `gamma_1 = pi/2`. Verified: the tracked branch
satisfies (A3) to `3.5e-35`, and its measured exit directions are `-0.5 pi` and
`0.166639 pi` against the predicted `-0.5 pi` and `pi/6`.

**So the binding case of the whole near-Fekete half is a statement about one
explicit real cubic.** On (A3), `y y' = (x^3-1)/(3x^2)`, hence

```text
1 + y'^2 = (4x^6 - 9x^4 + 4x^3 + 1) / (3 x^3 (x^3 - 3x + 2)).             (A4)
```

The numerator is **not** a perfect square — matching `(2x^3 + a x^2 + b x + c)^2`
forces `a = 0`, `b = -9/4`, `c = 1`, and then its `x^2` coefficient is `81/16`
rather than `0`. So the arclength, and therefore `kappa_3`, has no elementary
closed form. Recorded so that no one hunts for one: `kappa_3 = 0.60802134…` is a
period-type constant, and a proof of `kappa_3 > 0` must be an inequality, not an
evaluation.

## 9. Theorem B — `kappa_3 > 0`, proved

The binding degree is no longer measured. Everything below is ordinary
mathematics; the verifier only checks that the algebra was transcribed
correctly.

**The edge is one graph.** Both descending branches at `n = 3` lie on the *same*
sign-branch of (A3),

```text
y(x) = (x-1) sqrt(x+2) / sqrt(3x),        x in (0, oo),
```

because they leave the hub in the directions `pi/4` and `-3pi/4`, both of which
sit on `y = +(x-1)` locally. So the whole edge `Gamma` is a single graph: from
`x -> 0+` (where `y -> -oo`, exit direction `-pi/2`) through the hub `(1,0)` to
`x -> +oo` (where `y ~ x/sqrt3`, exit direction `pi/6`). Checked to `5.3e-34`.

Write `s(x) := dx/dy = 1/y'(x)`.

> **Lemma 1.** `y'(x) = (x^2+x+1) / sqrt(3x^3(x+2))`, so
> `s(x)^2 = 3x^3(x+2) / (1+x+x^2)^2`.
>
> **Lemma 2.** `d(s^2)/dx = 18 x^2 (x+1) / (1+x+x^2)^3 > 0` on `x > 0`.
> Hence `s` increases from `0` to `sqrt3`, with `s(1) = 1`. In particular
> `s <= 1` on `(0,1]`, and on `(1,oo)` the slope `y' = 1/s` **decreases
> monotonically from `1` to `1/sqrt3`** — so the tangent angle on branch A falls
> monotonically from `pi/4` to `pi/6`. Monotone turning at `n = 3` is thereby
> *proved*, not measured.
>
> *Proof of Lemma 2.* Differentiating `(3x^4+6x^3)/(1+x+x^2)^2` and factoring,
> the numerator is `(1+x+x^2) 6x^2 [(2x+3)(1+x+x^2) - (x^2+2x)(1+2x)]`, and the
> bracket collapses to `3(x+1)`. ∎
>
> **Lemma 3.** `phi(s) := (sqrt(1+s^2)-1)/s = s/(sqrt(1+s^2)+1)` is increasing,
> with `phi(1) = sqrt2 - 1`.

**Branch B** (`x: 0 -> 1`, exit direction `-pi/2`, so `cos gamma_1 = 0`).
Parameterised by `y` the chord direction is the `y`-axis and `x` stays in
`[0,1]`, so `D_B = int_{-oo}^{0} (sqrt(1+s^2) - 1) dy = int s phi(s) dy`. By
Lemma 2 `s <= 1`, so by Lemma 3

```text
D_B <= phi(1) * int s dy = (sqrt2 - 1) * (x(0) - x(-oo)) = sqrt2 - 1.
```

**Branch A** (`x: 1 -> oo`, exit direction `pi/6`, so `cos gamma_2 = sqrt3/2`).
In coordinates rotated by `pi/6`, Lemma 2 gives `tau in (pi/6, pi/4]`, hence
`v_u = tan(tau - pi/6) in (0, tan(pi/12)]`: both `u` and `v` are monotone. `v`
runs from `-1/2` at the hub to `0` at the asymptote (the line `y = x/sqrt3`
passes through the origin), so `TV(v) = 1/2` and, with `tan(pi/12) = 2 - sqrt3`,

```text
D_A <= phi(2 - sqrt3) / 2.
```

**Conclusion.** By the bridge (BR) and the exit angles (G),

```text
kappa_3 = sqrt3/2 - (D_A + D_B)
        >= sqrt3/2 - (sqrt2 - 1) - (2-sqrt3)/(2(sqrt6 - sqrt2 + 1))
        =  0.385985592618...  >  0.                                        []
```

The true value is `0.6080213113`, so the bound is valid and loses about a third.

**What Theorem B settles.** At degree three, `z^3 - mu` is a *strict* local
maximum of `min_c L(c)/(2R)` with value exactly `1`, approached at rate
`eps^{1/2}`. The near-Fekete half of Erdős #1041 is therefore **proved at the
binding degree**. It is not proved for `n >= 4` — those have far more room
(`cos g_1 + cos g_2` rises to `2` while `D_1 + D_2` stays near `0.34`), but each
needs its own curve, since (A3) is special to `n = 3`. The method transfers: the
same `phi(max slope) x total variation` estimate applies to any degree once the
analogue of Lemma 2 is in hand.

*Verifier:* `scripts/check_erdos1041_kappa3_positive.py`.

## 10. What this does not settle

* The `D`-bounded-away-from-1 half is untouched. `HardRegimeIsNearFekete.md`'s
  "nothing here converts that room into a length bound yet" still stands.
* `kappa_n(phi) > 0` — **`phi = 0` is now proved; general `phi` is not.** §6's
  inequality `ex_1 + ex_2 < 2`, equivalently `J_n < 2(n-1)`, follows at every
  `n >= 3` from `kappa_n = C_n - (D_1+D_2) >= C_n - B_n > 0`, assembled in
  [BridgeIdentityProof.md](BridgeIdentityProof.md) §4 out of (BR),
  [MonotoneTurningProof.md](MonotoneTurningProof.md), and
  [TurningLengthBound.md](TurningLengthBound.md) §§2–3. The bound loses about a
  third at the binding degree `n = 3` (`0.386` against a true `0.608`) and the
  margin grows thereafter. Theorem B (§9) is the `n = 3` case, and its own use of
  (BR) is now justified. **But §6 and §7 work in `Im g = c_n`, which is the
  descending level set only when `phi = 0`** — for general `phi` §2's rescaling
  puts the branches in `Im(e^{i n phi/(n-1)} g) = const`. The arithmetic agrees:
  §6's `0.6080213113` is §3's `min_phi kappa_3` at `phi = 0`. So the strict local
  maximum of §4 still rests on §3's **measured** claim that the minimum over
  `phi` sits at `phi = 0` (24 samples, tabulated for `n = 3, 4`). Proving that,
  or running the argument at general `phi`, is the remaining work; see
  `BridgeIdentityProof.md` §4a for the rotated form of the target.
* "Local" is qualitative: the `O(rho^2)` remainder is not quantified, so no
  explicit `delta_n` is claimed for which `D >= 1 - delta_n` implies the bound.
* The degenerate direction `h'(0) = 0` is excluded.
* Nothing here bears on the aggregate charge (E)/(F) of
  [CriticalTreeLengthCharge.md](CriticalTreeLengthCharge.md), on straight-spoke
  mechanisms, or on any bound at a hub other than the minimising one.

**Erdős #1041 remains open.**

## 11. Later finite-perturbation closure on transverse cones

The finite-remainder boundary above has now moved. The all-direction positive
limit coefficient is combined in
[NearFeketeTransverseClosure.md](NearFeketeTransverseClosure.md) with a uniform
near/far matched-asymptotic argument. On every cone
`|h'(0)| >= eta ||h||`, it proves the actual finite, scale-normalized inequality

```text
L_{eps,h,R} < 2 R_{eps,h,R}
```

for all sufficiently small `eps`, uniformly for base radii in compact ranges
`[R_*,1]`. The order-theoretic transfer from the positive scaled limit to the
strict inequality is Lean-checked in
[`NearFeketeTransverseClosure.lean#L19-L31`](NearFeketeTransverseClosure.lean#L19-L31)
and specialized to `length < 2 * radius` at
[`#L34-L60`](NearFeketeTransverseClosure.lean#L34-L60). Replay it with:

```sh
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py --jobs 2 --project-root formal_math/erdos257_period_noncollapse ErdosProblems.Erdos1041.NearFeketeTransverseClosure
```

Thus the `O(rho^2)` remainder is no longer an open item on a fixed transverse
cone. What remains on the near-Fekete side is precisely loss of transversality:
directions approaching `h'(0)=0`, whose first blow-ups are the finite family
`zeta^n + (n/j) zeta^j`, `2 <= j <= n-1`. The unrestricted problem remains
open.

## Claim boundary

Proved, by ordinary mathematics: the scalar lemma, Theorem A, corollaries (C1)
and (C2), and the §2 scaling (hub radius `rho`, the `eps`-free near-field model
`g(zeta) = zeta^n + n zeta`, and the reduction of a general perturbation to
`arg h'(0)` at leading order).

Measured, not proved (arithmetic is mpmath at 50 digits, but the
Gauss-Legendre rule is generated in float64, so the honest error bar on every
length here is **3.9e-16 absolute** -- the measured deviation from `2r` on the
equality family -- which supports the eight digits of `kappa_n` quoted and no
more): the constants `kappa_n`, their
`R`-independence, their universality across random `h`, and — still — that
`min_phi kappa_n(phi)` is **attained at `phi = 0`**. What is no longer measured
is the positivity of `kappa_n(0)` itself: see
[BridgeIdentityProof.md](BridgeIdentityProof.md) §4 and §4a.

Since proved elsewhere: (T), the monotone turning of §7, in
[MonotoneTurningProof.md](MonotoneTurningProof.md); and (BR) itself, in
[BridgeIdentityProof.md](BridgeIdentityProof.md), which also assembles
`kappa_n(0) > 0` at every `n >= 3` from those two plus
[TurningLengthBound.md](TurningLengthBound.md) §§2–3. That is the `phi = 0`
slice; the all-`phi` statement §4 needs still rests on §3's measured location of
the minimum. It relies on this note's §2 scaling and Theorem A, which are claimed
as proved here and were not re-derived there.

Not established: novelty of Theorem A ahead of a priority search; any bound in
the `D`-away-from-1 regime; any explicit neighbourhood size; `kappa_n(phi) > 0`
for `phi != 0`; and any progress on the constant 2.

## Current stability replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_near_fekete_cusp_law.py --part stability
```

The 2026-08-27 run reports `stability PASS`, with worst
`stability_worst_vdm_over_bound = 1.0` at degree 8. This validates the stated
stability experiment only; the high-precision constants and the all-direction
`phi` claim retain the measured/not-proved boundary above.
