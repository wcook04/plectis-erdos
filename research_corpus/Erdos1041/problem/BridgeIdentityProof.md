# Erdős 1041: the bridge (BR) is a two-line limit, and `kappa_n > 0` follows at every degree

Status: one exact identity and one limit, from which the last measured link in
the near-Fekete chain becomes a theorem. 2026-08-24. **This does not prove
Erdős #1041.** It does not touch the `D`-away-from-1 half, the `O(rho^2)`
remainder, the degenerate direction `h'(0) = 0`, or the constant 2. Everything
lives on the limit model, per the scope boundary in `ade3b6ac08`.

## 0. What was open

[NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) §7 introduced the bridge between
the two anchorings of a branch's renormalised excess and recorded it as measured:

> ```text
> beta = cos gamma - D,   kappa_n = (cos g_1 + cos g_2) - (D_1 + D_2).   (BR)
> ```
> (BR) is verified to `6.2e-27`.

Both [TurningLengthBound.md](TurningLengthBound.md) §3 and the cusp law's own
Theorem B (§9, `kappa_3 > 0`) **use** (BR) inside a proof, so it was carrying
weight it had not earned. It turns out to be elementary.

## 1. The finite-arclength identity

Let `Gamma` be a descending branch at the hub `zeta_c` (so `|zeta_c| = 1`), with
asymptotic direction `alpha`, `e^{i n alpha} = 1`, and
`gamma = arg(zeta_c) - alpha`. Parametrise by arclength `s`, so `Lambda(S) = S`.
Put

```text
u(s) = e^{-i alpha} zeta(s) = U(s) + i V(s),      t = tau - alpha .
```

Because `d zeta/ds = e^{i tau}`, we have `cos t = Re(e^{-i alpha} d zeta/ds)`, so

```text
int_0^S cos t  ds  =  Re( e^{-i alpha}( zeta(S) - zeta_c ) )  =  U(S) - cos gamma,
```

using `Re(e^{-i alpha} zeta_c) = cos(arg zeta_c - alpha) = cos gamma`. Hence, for
**every** finite `S`,

> ```text
> |zeta(S)| - S  =  ( |u(S)| - U(S) )  +  cos gamma  -  int_0^S (1 - cos t) ds .   (*)
> ```

No limits, no asymptotics: `(*)` is bookkeeping.

## 2. The one limit

> **Lemma.** Along a descending branch, `|u| - U -> 0`.

*Proof.* `|u| - U = (|u|^2 - U^2)/(|u| + U) = V^2/(|u| + U)`. Lemma T of
[TurningLengthBound.md](TurningLengthBound.md) §1 shows `V = O(U^{-(n-2)})`, so
`V` is bounded; and `|u| = |zeta| -> infinity` because `Re g = Re g(zeta_c) + sigma`
is unbounded on the branch. Then `U >= |u| - |V| -> infinity`, so the quotient
tends to `0`. ∎

Only *boundedness* of `V` is used. Lemma T gives far more — `V -> 0` at an
explicit rate — but the bridge does not need it.

## 3. Theorem — (BR)

> **Theorem.** With `beta := lim_{S -> infinity} ( |zeta(S)| - S )` and
> `D := int_Gamma (1 - cos t) dl`,
>
> ```text
> beta = cos gamma - D ,
> ```
>
> either side existing iff the other does. Summing the two branches at a hub and
> using `kappa_n = beta_1 + beta_2` gives
> `kappa_n = (cos gamma_1 + cos gamma_2) - (D_1 + D_2)`.

*Proof.* Let `S -> infinity` in `(*)`: the first bracket tends to `0` by the
Lemma, and the integral increases to `D`. ∎

The chord form of §7 — "the chord from `zeta_c` to a far point has length
`Z - cos gamma + o(1)`" — is the same statement seen through
`|zeta(S) - zeta_c| = (U - cos gamma) + O(1/U)`; going through `U` directly
avoids the chord entirely.

## 4. Consequence — `kappa_n > 0` at every degree

Four links, now all proved:

| # | statement | source |
|---|---|---|
| 1 | `kappa_n(phi) = beta_1 + beta_2` | cusp law §2 scaling |
| 2 | `beta_i = cos gamma_i - D_i` | **(BR), §3 above** |
| 3 | `D_i <= tan(T_i/2)|sin gamma_i|` | `TurningLengthBound.md` §2 Theorem |
| 4 | `B_n < C_n` for every `n >= 3` | `TurningLengthBound.md` §3 Proposition |

Link 3's two hypotheses — constant sign of `t`, and `|t| <= T_i` — were the open
ones; they are proved on both branches at every degree in
[MonotoneTurningProof.md](MonotoneTurningProof.md). Its other input, Lemma T, is
proved in `TurningLengthBound.md` §1, and `gamma_i`, `T_i` are closed forms.
Link 4 is proved in closed form. Therefore

> ```text
> kappa_n  =  C_n - (D_1 + D_2)  >=  C_n - B_n  >  0        for every n >= 3,
> ```

equivalently `ex_1 + ex_2 < 2`, equivalently `J_n < 2(n-1)`. The cusp law's §10
names exactly this as the remaining work:

> `kappa_n(phi) > 0` is **measured**, not proved. §6 reduces it to the
> parameter-free inequality `ex_1 + ex_2 < 2` … that inequality is where the
> remaining work is.

so `kappa_n > 0` at every degree, not only at `n = 3` (Theorem B), whose own use
of (BR) is also now justified. The margin is the closed-form `C_n - B_n`, which
runs `0.386` at `n = 3` up to `1.44` at `n = 10` against true values `0.608` to
`1.655` — valid, losing about a third at the binding degree.

## 4a. Which `kappa_n` — the `phi = 0` slice, and what is still measured

**This is `kappa_n(0)`, not `kappa_n(phi)` for every `phi`.** §2 of the cusp law
takes `h(z) = e^{i phi} z` and rescales by `z = rho e^{i psi} zeta`,
`psi = phi/(n-1)`, giving

```text
f(z) + m  =  rho^n e^{i n psi} g(zeta),        g(zeta) = zeta^n + n zeta .
```

The *model* `g` is therefore `phi`-free, and so are the hub positions and every
arclength — which is why `beta_1 + beta_2` looks parameter-free. But the far
field wants `f + m` real positive, so in the `g`-plane the descending ray leaves
the critical value in direction `e^{-i n psi}`, and a descending branch lies in

```text
Im( e^{i n psi} g )  =  const ,        n psi = n phi/(n-1),
```

not in `Im g = c_n`. Those coincide exactly when `phi = 0`. The arithmetic
confirms it: §6's value `0.6080213113` is §3's sweep minimum
`min_phi kappa_3 = 0.6080216` **attained at `phi = 0`**, while the sweep maximum
is `0.8125984` at `phi = pi/3`. So §6 and §7 — and hence everything above —
compute the `phi = 0` slice.

Consequently:

* `kappa_n(0) > 0` for every `n >= 3` is **proved**.
* `kappa_n(phi) > 0` for every `phi` — what §4 of the cusp law needs for the
  strict local maximum — was, when this was written, resting on its §3 **measured**
  claim that the minimum over `phi` sits at `phi = 0`. **That is no longer the
  route.** A concurrent session proved the rotated confinement directly
  ([ConeBoundMonotoneFunctional.md](ConeBoundMonotoneFunctional.md) §7a, Lemma S(δ)
  and Lemma W2) and carried `C_n > B_n` across the resulting window (Theorem R),
  so the all-`phi` statement no longer needs the sweep at all. See
  [PhaseDependenceOfKappa.md](PhaseDependenceOfKappa.md) §6a for how that window
  and the max-over-hubs picture here are the same selection rule.

Closing that last gap means running the argument at general `psi`. The sign law
survives the rotation: with `d zeta/d sigma = e^{-i n psi}/g'` one gets
`dt/d sigma = -((n-1)/n) Im( e^{-i n psi}/N^2 )`, so the requirement becomes
that `N` stays in a quadrant **rotated by `n psi / 2`**, and the two separating
curves become `{Im(e^{i n psi/2} N) = 0}` and `{Re(e^{i n psi/2} N) = 0}`. The
master identity does survive that rotation — see
[PhaseDependenceOfKappa.md](PhaseDependenceOfKappa.md) §5.

**Correction, same day.** An earlier version of this section read as though that
one rotated branch pair *is* `kappa_n(phi)`. It is not: it is one candidate, and
it goes negative (`-0.553` at `n = 3`, `delta = pi/2`, where the true
`kappa_3(phi)` is `0.813`). `min_c L(c)` is a minimum over curves, so `kappa_n` is
a **maximum** over the `n-1` hubs, which the symmetry `g(omega zeta) = omega g(zeta)`
turns into a maximum over `delta + 2 pi j/(n-1)`. That structure, its agreement
with the cusp law's sweep, and the exact remaining target are in
[PhaseDependenceOfKappa.md](PhaseDependenceOfKappa.md).

**What this does not upgrade.** Everything the cusp law §10 lists besides that
bullet still stands: the `D`-away-from-1 half is untouched; "local" stays
qualitative because the `O(rho^2)` remainder is unquantified, so no explicit
`delta_n` is claimed; the degenerate direction `h'(0) = 0` is excluded; and
nothing here bears on the constant 2. **Erdős #1041 remains open.**

## 5. Instrument note

The `kappa_n` this directory's float64 tracer returns differs from the cusp
law's 40-digit value by about `5e-5` at `n = 3` (`0.607971` against
`0.6080213113`), a gap the existing probes already publish. It is **quadrature,
not truncation**: widening the traced range at a fixed sample count makes the
gap *grow* — `-5.0e-5`, `-2.7e-4`, `-1.4e-3`, `-7.2e-3` as `smax` goes
`1e3.5 -> 1e6.5` — because the geometric `s`-grid thins out where the arclength
integrand still matters. The truncation tail is separately visible and tiny:
`|u| - U` is already `4.8e-13` at `U ~ 215`. Refining instead of widening
settles it: at fixed range `smax = 1e3.5` the gap falls `-8.1e-4`, `-5.0e-5`,
`-3.1e-6`, `-7.8e-7` for `npts = 5000, 20000, 80000, 160000` — clean `O(h^2)`
trapezoid convergence **onto the stored 40-digit value**. That is an independent
confirmation of (BR) itself, since the traced `kappa_3` is assembled from
`cos gamma - D` while `0.6080213113` was computed from the branch geometry at 40
digits. So the tracer's `kappa_n` should be read at the *smallest* adequate
range, and the 40-digit value is the authority. The bridge check is immune
either way — `(*)` holds identically, to `5e-17`.

The probe also confirms Lemma T's two decay rates directly: `|V| U^{n-1}` on
branch 1 and `|V| U^{n-2}` on branch 2 stay between `0.38` and `0.99` at every
degree `3..12`, so the boundedness the §2 Lemma needs is not marginal.

## Claim boundary

Proved, by ordinary mathematics: the identity `(*)`, the Lemma of §2, and the
Theorem of §3, hence (BR). Given the four links tabulated in §4,
`kappa_n(0) > 0` at every `n >= 3`.

Measured: that `min_phi kappa_n(phi)` is attained at `phi = 0` (cusp law §3,
tabulated for `n = 3, 4` only). It was load-bearing for the all-`phi` statement
when this note was written; it no longer is, since
[ConeBoundMonotoneFunctional.md](ConeBoundMonotoneFunctional.md) §7a proves the
rotated confinement outright. The `phi != 0` branches live in
`Im(e^{i n phi/(n-1)} g) = const`, not in `Im g = c_n`, so they are still **not**
covered by anything proved *here*, and the right object there is a maximum over
hubs, not a single pair.

Inherited, not re-derived here: the cusp law's §2 scaling
(`kappa_n(phi) = beta_1 + beta_2`), its Theorem A, and Lemma T. All three are
listed as proved in their own claim boundaries; this note takes them at their
word rather than checking them again.

Measured: nothing this note relies on. The probe's section A checks `(*)` and the
decay of `|u| - U`; section B compares the traced `kappa_n` against the stored
40-digit values within the quadrature error bar of §5.

Not established: novelty — `(*)` is the definition of arclength written out, and
the Lemma is one line, so both should be assumed known until a priority search
says otherwise. Also untouched: everything in §4's closing paragraph.

## Replay

```sh
./repo-python formal_math/probes/erdos1041_bridge_identity.py --max-n 12
```
