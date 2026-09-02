# Erdős 1041: the cone hypothesis, proved at the binding degree

Status: four ordinary lemmas, one exact symbolic factorisation, and three
refuted routes. 2026-08-23. **This does not prove Erdős #1041**, and it does not
prove the near-Fekete half at every degree. It closes the hypothesis of
[TurningLengthBound.md](TurningLengthBound.md) for `n = 3`, branch 1, and proves
two of its three ingredients at every degree.

**Superseded in part, 2026-08-24.** (★) is now proved at every degree on **both**
branches by [MonotoneTurningProof.md](MonotoneTurningProof.md), which also
explains the `n = 3` cubic of §5 and closes §7's open list. Read this note for
Lemmas S and B (still the sector and sign inputs) and for §6's three refutations;
read the proof note for (★) itself.

Everything here is on the limit model `g(zeta) = zeta^n + n zeta`, per the scope
boundary in `ade3b6ac08`. Write `zeta = r e^{i phi}`, `y = Im zeta`,
`phi_c = pi/(n-1)`, `zeta_c = e^{i phi_c}`, `c_n = (n-1) sin(phi_c)`,
`P = zeta^{n-1}`, `G = zeta^n + zeta = zeta g'(zeta)/n`. Branch 1 is the
descending branch at `zeta_c` with asymptotic direction `alpha = 0`; it lies in
the level set `Im g = c_n`.

## 1. Lemma S — branch 1 stays in the open sector

> **Lemma S.** Branch 1 satisfies `0 < arg zeta < phi_c` at every point after the
> hub.

*Proof.* The branch cannot meet either boundary ray.

*The ray `arg zeta = 0`.* There `zeta` is real, so `g(zeta)` is real and
`Im g = 0`. But `Im g = c_n > 0` on the branch. So the level set misses the
positive real axis entirely, and `y > 0` throughout.

*The ray `arg zeta = phi_c`.* There `P = r^{n-1}e^{i pi} = -r^{n-1}`, so
`zeta^n = zeta P = -r^n e^{i phi_c}` and

```text
Im g = Im(zeta^n) + n Im(zeta) = sin(phi_c) ( n r - r^n ).
```

Now `h(r) = n r - r^n` has `h'(r) = n(1 - r^{n-1})`, vanishing on `r > 0` only at
`r = 1`, with `h''(1) = n(1-n) < 0`; so `h` has a strict global maximum
`h(1) = n - 1`. Hence `Im g <= (n-1) sin(phi_c) = c_n` on that ray, **with
equality only at `r = 1`, i.e. only at `zeta_c` itself.** So the branch meets
that ray only at its own starting point. ∎

Lemma S is what every later step needs, and it was previously carried as a
verified-not-proved hypothesis.

## 2. Lemma B — `Im zeta` is strictly decreasing, so `Im G > 0`

> **Lemma B.** Along branch 1, `dy/d sigma < 0`. Hence `y < sin(phi_c)`, i.e.
> `Im zeta < Im zeta_c`, i.e. `Im G > 0`.

*Proof.* `d zeta / d sigma = 1/g'`, so `dy/d sigma = Im(1/g') = -Im(g')/|g'|^2`.
With `g' = n(P+1)`,

```text
Im g' = n Im P = n r^{n-1} sin((n-1) phi),
```

which is strictly positive for `0 < phi < phi_c` by Lemma S, since then
`(n-1)phi in (0, pi)`. So `dy/d sigma < 0` strictly. The branch starts at
`y = sin(phi_c)`, so `y < sin(phi_c)` after. Finally `G = g - (n-1) zeta` gives
`Im G = c_n - (n-1) y = (n-1)(sin(phi_c) - y) > 0`. ∎

## 3. Corollary — the tangent has constant sign

By Lemma S, `arg P = (n-1)phi in (0,pi)`, so `P` lies in the open upper
half-plane, so `Im(P+1) > 0` and `psi := arg(P+1) in (0,pi)`. Since
`t = -arg(e^{i alpha}(P+1)) = -psi` on branch 1, the tangent offset `t` is
**strictly negative throughout**. That is the constant-sign hypothesis of
`TurningLengthBound.md` §2, now proved. Equivalently, under the conformal map
`P = zeta^{n-1}` of the sector onto `H`, `|t| = pi * omega(P,(-inf,-1),H)`.

## 4. The remaining hypothesis collapses to one inequality

`|t| <= T_1` follows from `|t|` being decreasing, i.e. from `dt/d sigma >= 0`.
Since `dt/d sigma = -Im(g''/(g')^2)` and `g''/(g')^2 = (n-1) zeta^n/(n G^2)`,
this is `Im(zeta^n/G^2) <= 0`. Writing `P + 1 = rho e^{i psi}` this is
`sin(phi + 2 psi) <= rho sin(phi + psi)`; multiplying by `r` and using
`r rho sin(phi+psi) = Im G = c_n - (n-1) y` turns it into
`r sin(phi + 2 psi) + (n-1) y <= c_n`, and expanding `sin(phi+2psi)` through
`rho cos psi = 1 + q cos theta`, `rho sin psi = q sin theta`
(`q = r^{n-1}`, `theta = (n-1)phi`) gives, after using the level set once,

> **(★)**  `Phi := c_n r^{n-2} - (n-2) r^{n-1} sin(phi) - sin((n-2) phi) >= 0`,
>
> equivalently `Phi = q^2 sin(n phi) + 2 q sin(phi) - sin((n-2) phi) >= 0`.

Both forms vanish at the hub. `Phi` (the first form) is the numerically stable
one; the second loses to cancellation in `r^{2n-2}` beyond `n ~ 10`.

*Verification.* `min Phi` runs `-5.6e-16` to `-7.3e-15` — machine zero — at every
degree `3..12`, and `sign(Phi)` matches `sign(dt/d sigma)` pointwise.

*Instrument reach.* The float64 root-continuation is only trusted where the
level-set residual `|Im g - c_n|` is below `1e-6`; the probe reports that
fraction (`0.92`–`1.00`). Past `|zeta|^n ~ 1e12` the residual swamps everything —
at `n = 12`, `r ~ 1e3` gives residual `30`, and those points are not on the curve
at all. Every assertion is restricted to resolved points.

## 5. Theorem — (★) is exactly `y <= 1` at `n = 3`

At `n = 3`, `phi_c = pi/2`, `c_3 = 2`, and (★) reads `2r >= sin(phi)(r^2+1)`. The
level set is `y(3x^2 - y^2 + 3) = 2`, so `3x^2 = 2/y + y^2 - 3`. Eliminating `x`:

```text
3 r y * [ 2r - sin(phi)(r^2+1) ]  =  -4 (y-1)^3 (y+1)      identically on the curve.
```

Verified symbolically (sympy, difference exactly `0`). Since `y > 0` by Lemma S,
the right side is `>= 0` iff `y <= 1`. So

> **(★) at `n = 3` is equivalent to `Im zeta <= Im zeta_c`, which is Lemma B.**

Hence at `n = 3` branch 1: turning is monotone, `|t| <= T_1 = pi/4`, and by the
Theorem of `TurningLengthBound.md`, `D_1 <= tan(pi/8) = sqrt2 - 1 = 0.414214`
against a measured `0.235101`. **Degree 3, branch 1 is closed unconditionally.**

## 6. Three refuted routes, recorded so they are not retried

* **A sufficient split that fails.** (★) follows from `y <= sin(phi_c)` together
  with `sin((n-2)phi) <= r^{n-2} sin(phi_c)`. The second is **false**: the
  quantity `sin((n-2)phi) - r^{n-2}sin(phi_c)` reaches `+0.140` at `n = 3` and
  `+0.671` at `n = 12`. Both halves are tight at the hub, which is what made the
  split look plausible.
* **`Re G >= 0` is false on the branch.** `min Re G` is `-0.189` at `n = 3`,
  `-0.0129` at `n = 12`. Any argument routing `arg G <= pi/2` is dead.
* **`r >= 1` is a minority of the branch.** `min r` is `0.766` at `n = 3` and
  `0.998` at `n = 12`, and the fraction with `r < 1` runs `0.76` at `n = 3` to
  `0.64` at `n = 12`. A case split assuming `r >= 1` covers a third at best.

The third kills the natural attack on the general case: writing
`q Phi = (1/r)[(n-1)(sin phi_c - y)(q^2 - cos 2phi) + Re G sin 2phi] + sin(phi)(q^2-1)`
makes all three terms nonnegative when `r >= 1` and `Re G >= 0`, and **both
hypotheses fail on most of the branch.**

## 7. What is left

*All three were closed on 2026-08-24 by
[MonotoneTurningProof.md](MonotoneTurningProof.md); kept as written so the order
of discovery stays legible.*

* ~~(★) for `n >= 4`, and (★) on branch 2 at every `n`.~~ Both proved. Branch 2's
  sector is proved too (Lemma 5 there), and its sign argument is the *reverse*
  quadrant, not the one in §3.
* ~~Whether the `n = 3` factorisation `(y-1)^3(y+1)` has a general-`n` analogue.~~
  It does: the cubic is the order-3 vanishing forced by the `sin^2 theta` in that
  note's master identity, with constant `(1-lambda^2)/(6 cos^2(lambda pi/2))`,
  equal to `1/4` at `n = 3`.
* Everything outside the limit model, per `ade3b6ac08`.

**Erdős #1041 remains open**, and degree 3 of the problem itself was already
proved by other means (`CubicCriticalHub.lean`); what is new here is that the
*near-field model's* cone hypothesis at `n = 3` is no longer an assumption.

## Claim boundary

Proved: Lemma S, Lemma B, the constant-sign corollary, the collapse to (★), and
the `n = 3` equivalence (★) `<=>` `y <= 1` (symbolic, exact).

Measured: `min Phi >= -7.3e-15` at degrees `3..12` on resolved points, the sign
agreement of `Phi` with `dt/d sigma`, and the three refutations in §6. Lemma B is
checked through `Im g' = n r^{n-1} sin((n-1)phi)`, not through `Im(1/g')`: the
latter underflows (`|g'|^2` reaches `1e56` at `n = 12`, so the sign of a `1e-28`
quotient is float64 noise, not mathematics).

Not established *here*: (★) for `n >= 4` and (★) on branch 2 — both since proved
in [MonotoneTurningProof.md](MonotoneTurningProof.md). Novelty of any of it —
Lemma S is a one-line calculus fact and Lemma B is elementary, so both should be
assumed known until a priority search says otherwise.

## Replay

```sh
./repo-python formal_math/probes/erdos1041_turning_length_bound.py --max-n 10
./repo-python formal_math/probes/erdos1041_cone_branch_geometry.py
```
