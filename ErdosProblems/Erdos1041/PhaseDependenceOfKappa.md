# Erdős 1041: where the split direction actually enters `kappa_n(phi)`

Status: one symmetry (proved), one structural identity (derived modulo §2's
modelling assumption, and confirmed against the cusp law's own sweep at `n = 3`
and `n = 4`), and one refuted reading — mine, from earlier today. 2026-08-24.
**This does not prove Erdős #1041**, and it does not prove `kappa_n(phi) > 0` for
`phi != 0`. It says exactly what would.

## 0. The discrepancy

[NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) §2 states

```text
L(c) = 2R - kappa_n(phi) * rho + O(rho^2),      kappa_n(phi) = beta_1 + beta_2,
```

with `beta` a property of a near-field branch. But §2's own rescaling
`z = rho e^{i psi} zeta`, `psi = phi/(n-1)`, gives

```text
f(z) + m  =  rho^n e^{i n psi} g(zeta),        g(zeta) = zeta^n + n zeta,
```

in which **`g` is `phi`-free** — and so are its critical points, its level set
`Im g = c_n`, its branches, and therefore `beta_1 + beta_2`. Yet §3 measures a
genuine `phi`-dependence: `kappa_3` runs `0.608022` to `0.812598`, `kappa_4` runs
`1.030120` to `1.122912`, and `rho = (eps|h'(0)|/n)^{1/(n-1)}` is `phi`-free too.
A `phi`-free right-hand side cannot equal a `phi`-varying left-hand side. Something
in the statement is compressed.

## 1. Where `phi` enters: the descending direction rotates

The far field wants `f + m` real positive (the branch is the radial segment of
`z^n = m sigma`). Through `f + m = rho^n e^{i n psi} g`, that is the ray leaving
the critical value in the **`g`-plane** direction `e^{-i delta}`,

```text
delta := n psi = n phi/(n-1),
```

so a descending branch lies in `Im(e^{i delta} g) = const`, not in `Im g = c_n`.
The two agree exactly when `phi = 0`. Write

```text
cand(delta) := C(delta) - ( D_1(delta) + D_2(delta) )
```

for the two-branch deficit at hub `0` in direction `e^{-i delta}`, with the exit
directions `alpha_k(delta) = (2 k pi - delta)/n` and
`gamma_k = pi/(n-1) - alpha_k`. Then `cand(0)` is the `kappa_n` of §6/§7.

## 2. Lemma — hub `j` in direction `delta` is hub `0` in direction `delta + 2 pi j/(n-1)`

> **Lemma.** Let `omega = e^{2 pi i/(n-1)}`. Then `g(omega zeta) = omega g(zeta)`,
> and the hubs are `omega^j zeta_c`. Consequently the branch geometry at hub `j`
> in direction `e^{-i delta}` is the image under `zeta -> omega^j zeta` of the
> geometry at hub `0` in direction `e^{-i(delta + 2 pi j/(n-1))}`.

*Proof.* `(omega zeta)^n = omega^{n-1} omega zeta^n = omega zeta^n` since
`omega^{n-1} = 1`, so `g(omega zeta) = omega(zeta^n + n zeta)`. Hence
`Im(e^{i delta} g(omega eta)) = Im(e^{i(delta + 2 pi j/(n-1))} g(eta))` for
`zeta = omega^j eta`, and `zeta -> omega^j zeta` is an isometry, so every radius,
arclength and angle used in `beta` is preserved. ∎

## 3. The structural identity

`min_c L(c)` is a **minimum over curves**, hence `kappa_n = (2R - min_c L)/rho`
is a **maximum over candidates**. Taking §2's modelling assumption that the
minimiser is a two-branch curve at one hub, the Lemma turns the choice of hub
into a shift of `delta`:

> **(H)**  `kappa_n(phi) = max_{j = 0..n-2}  cand( n phi/(n-1) + 2 pi j/(n-1) )`.

The `n-1` arguments are equally spaced by `2 pi/(n-1)` on the circle.

*Confirmation.* Against the cusp law's own verifier
(`--part phase`, 12 samples, 40 digits):

| n | `phi/(2 pi/n)` | `max_j cand` | sweep |
|---|---|---|---|
| 3 | `0` | `0.607915` | `0.608022` (its **minimum**) |
| 3 | `1/2` | `0.812492` | `0.812598` (its **maximum**) |
| 4 | `0` | `1.030031` | `1.030120` (its **minimum**) |
| 4 | `1/3` | `1.122823` | `1.122912` (its **maximum**) |

to the tracer's `~1e-4` quadrature bar
([BridgeIdentityProof.md](BridgeIdentityProof.md) §5). (H) reproduces the whole
sweep curve, its minimum at `phi = 0`, and its shape — and at `n = 4` it finds
`1.134055` at `phi/(2 pi/n) = 1/2`, a value the 12-sample sweep steps over.

## 4. What this refutes — including my own earlier reading

`BridgeIdentityProof.md` §4a said that for general `phi` the branches simply live
in `Im(e^{i n phi/(n-1)} g) = const`, as if that single rotated pair *were*
`kappa_n(phi)`. **It is not.** A single candidate goes badly negative:

| n | worst `cand(delta)` | at `delta` | true `kappa_n(phi)` there |
|---|---|---|---|
| 3 | `-0.552869` | `pi/2` | `0.812598` |
| 4 | `-0.068125` | `~1.745` | `1.088667` |

A negative `cand` is not a counterexample to anything — it says that candidate
curve is longer than `2R`, so the minimiser picks a different hub. Reading one
candidate as `kappa_n(phi)` would have manufactured a contradiction with the
conjecture out of nothing. The rescaling algebra of §1 is right; the identification
was wrong.

## 5. The machinery does rotate

Both master identities of [MonotoneTurningProof.md](MonotoneTurningProof.md)
survive at every `delta`. Put

```text
a~ = (1-lambda)theta/2 - delta/2,     b~ = (1+lambda)theta/2 + delta/2,
```

so `a~ + b~ = theta` is unchanged and `b~ - a~ = lambda theta + delta`. The zero
sets keep their shape — `{Y_delta = 0}` is `r^{n-1} sin b~ = sin a~` and
`{X_delta = 0}` is `r^{n-1} cos b~ = -cos a~` — and with
`W_pm = lambda^{-1} sin(b~ - a~) +/- sin theta`,

```text
d/d theta log K_+^delta = (1-lambda^2) sin^2(theta) / ( 2 sin a~ sin b~ W_+ )
d/d theta log K_-^delta = (1-lambda^2) sin^2(theta) / ( 2 cos a~ cos b~ W_- )
```

exactly as before (sympy: difference `0`), and at the hub `theta = pi` we still
have `a~ + b~ = pi`, hence `sin a~ = sin b~`, `-cos a~/cos b~ = 1`, and

```text
K_+^delta(pi) = K_-^delta(pi) = lambda^{-1} sin(pi lambda + delta) = c_n(delta),
```

the rotated critical value. The proof at `delta = 0` is cleaner in this general
form: `d a~/d theta = (1-lambda)/2` and `d b~/d theta = (1+lambda)/2` are
constants, so the `a/theta` substitution used at `delta = 0` is unnecessary.

## 6. `C - B` in closed form, and it is positive

By (H), `kappa_n(phi) > 0` for every `phi` is equivalent to

> **(P)** for every `delta`, at least one of the `n-1` points
> `delta + 2 pi j/(n-1)` has `cand > 0`.

The turning-length bound gives `cand(delta) >= C(delta) - B(delta)`. That right
side turns out to be elementary. Reparametrise by the exit angle rather than by
`delta`: the two branches leave along the two `n`-th-root directions **bracketing**
`arg zeta_c`, so with

```text
u := gamma_1 in [0, 2 pi/n),      v := 2 pi/n - u = -gamma_2,
```

the whole configuration is a function of `u` alone, and — the step that makes
everything collapse —

> **Lemma C.** `T_k = (n-2) |gamma_k| / 2` for both branches.

*(At `delta = 0`, `u = pi/(n-1)` and this returns `T_1 = (n-2)pi/(2(n-1))`,
`T_2 = (n-2)^2 pi/(2n(n-1))`, the closed forms already recorded.)*

Hence `B = tan((n-2)u/4) sin u + tan((n-2)v/4) sin v`, and since
`cos x - tan(qx) sin x = cos((q+1)x)/cos(qx)`,

```text
C - B  =  psi(u) + psi(v),        psi(x) = cos((n+2)x/4) / cos((n-2)x/4).
```

> **Theorem.** With `q = (n-2)/4` and `u + v = 2 pi/n`, `u, v >= 0`,
>
> ```text
> ( C - B ) cos(q u) cos(q v)  =  cos(pi/n) * cos( n(u-v)/4 ).
> ```
>
> Consequently `C - B > 0` for `u in (0, 2 pi/n)`, and `C - B = 0` exactly at
> `u = 0` and `u = 2 pi/n`.

*Proof.* `psi(x) cos(qx) = cos(px)` with `p = q + 1`, so the left side is
`cos(pu)cos(qv) + cos(pv)cos(qu)`, which by product-to-sum is

```text
(1/2)[ cos(pu+qv) + cos(pv+qu) ] + (1/2)[ cos(pu-qv) + cos(pv-qu) ].
```

Since `p - q = 1` and `p + q = n/2`, the four arguments are `u + qw`, `v + qw`,
`nu/2 - qw`, `nv/2 - qw` with `w = 2 pi/n`. Summing each pair to a product,

```text
(1/2)[cos(u+qw) + cos(v+qw)]         = cos(w/2 + qw) cos((u-v)/2),
(1/2)[cos(nu/2-qw) + cos(nv/2-qw)]   = cos(nw/4 - qw) cos(n(u-v)/4),
```

and `w/2 + qw = pi/2` exactly, killing the first term, while
`nw/4 - qw = pi/n`. That is the identity. For the sign: `qu <= q w = pi(n-2)/(2n) < pi/2`
so `cos(qu) > 0`, likewise `cos(qv) > 0`; `cos(pi/n) > 0` for `n >= 3`; and
`|n(u-v)/4| <= n w/4 = pi/2` with equality only when `{u,v} = {0, w}`. ∎

This **subsumes** [TurningLengthBound.md](TurningLengthBound.md) §3's Proposition,
which proved `C_n > B_n` only at the single point `u = pi/(n-1)` and needed
separate closed-form checks at `n = 3` and `n = 4`.

So the bad set for the bound is not an arc at all — it is the single point
`u = 0`, where a branch exits exactly along the hub direction. The `n-1`
candidates are distinct mod `2 pi/n` (they are spaced `2 pi/(n(n-1)) < 2 pi/n`),
so at most one of them can sit there, and for `n >= 3` at least one of the others
has `C - B > 0`. **(P) follows.**

## 6a. The last link, closed concurrently — and the two routes agree

The link `cand(delta) >= C(delta) - B(delta)` needs monotone turning on the
**rotated** branches, i.e. the sector confinement of
[MonotoneTurningProof.md](MonotoneTurningProof.md) §§6–7 redone at general
`delta`. **That was proved concurrently**, in
[ConeBoundMonotoneFunctional.md](ConeBoundMonotoneFunctional.md) §7a — Lemma S(δ)
for the inner wall and Lemma W2 for the outer one, the latter by showing the flow
`d(arg zeta)/ds = sin(delta - 2 phi_c)/(r g')` points strictly inward on the outer
ray. That note's Theorem R then carries `C_n > B_n` across the window. So the
all-`phi` conclusion is **not** blocked here; this section previously said it was,
and that was written before `336adb2b33` was read.

**The two routes reach the same structure from opposite sides, and they agree.**
Its Proposition W confines both branches exactly on a window of length
`2 pi/(n-1)` — the hub spacing — so **exactly one hub is admissible**. §3 above
instead computes every hub and takes the maximum. Mind the convention: that note
writes the descent as `g = (n-1) zeta_c + s e^{i delta}` while §1 here uses
`e^{-i delta}`, so its `delta` is minus this one, and its window `(0, 2 pi/(n-1))`
is `delta in (2 pi - 2 pi/(n-1), 2 pi)` here. With that translation:

> at every degree `3, 4, 5` and every sampled `phi`, `argmax_j cand` lands in
> Proposition W's admissible window — 15 of 15.

So the maximum in (H) *is* the admissible hub, and the negative candidates of §4
are exactly the inadmissible ones, whose traced "branches" have left their
sectors and whose deficit therefore means nothing. Two independent derivations,
one selection rule.

What §6 adds on top is sharpness: Theorem R carries `C_n > B_n` across the
window, while the closed form above gives `C - B` **exactly**, positive on the
whole open exit-angle range with its two zeros located.

## Claim boundary

Proved: the Lemma of §2; the rotated identities of §5 (symbolically exact for
both `K_pm^delta`, and `K_pm^delta(pi) = c_n(delta)`); Lemma C and the Theorem of
§6, hence `C - B > 0` on `(0, 2 pi/n)` at every `n >= 3`, hence (P) — every step
of the §6 proof is checked symbolically in `n` by the probe.

Derived, given §2's modelling assumption that the minimiser is a two-branch curve
at one hub: the structural identity (H).

Measured: that (H) reproduces the cusp law's sweep at `n = 3, 4` to `~1e-4`, and
the negative candidate values of §4. Both come from the float64 tracer, whose
error bar is the quadrature bound of `BridgeIdentityProof.md` §5. Lemma C is
checked against the recorded `T_1`, `T_2` at `delta = 0` and against the traced
`|t|` at `delta != 0`; it is stated as proved because it is forced by
`t(hub) = -delta/2 - n pi/(2(n-1)) + gamma_k - p_k pi` reduced mod `2 pi`, but
that reduction is a short calculation this note does not write out.

Reported by a concurrent session, read but not re-derived here: Lemma S(δ),
Lemma W2, Proposition W and Theorem R of
[ConeBoundMonotoneFunctional.md](ConeBoundMonotoneFunctional.md) §7–§7a, which
close the rotated-confinement link §6a used to name as open. What this note
checked against them is the 15-of-15 agreement of §6a, not their internal proofs.

Not established: any novelty claim. `kappa_n(0) > 0` at every degree stands,
proved in `BridgeIdentityProof.md` §4.

**Erdős #1041 remains open.**

## Replay

```sh
./repo-python formal_math/probes/erdos1041_phase_dependence.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_near_fekete_cusp_law.py --part phase
```
