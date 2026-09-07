# Erdős 1041: monotone turning is a theorem, on both branches, at every degree

Status: one identity, proved symbolically and by hand, from which statement (T)
of [NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) §7 and hypothesis (C1) of
[TurningLengthBound.md](TurningLengthBound.md) §4 both follow at every degree.
2026-08-24. **This does not prove Erdős #1041.** It does not touch the bridge
(BR), the `D`-away-from-1 half, the `O(rho^2)` remainder, or the constant 2.
Everything lives on the limit model, per the scope boundary in `ade3b6ac08`.

## 0. What was open

`TurningLengthBound.md` §6 recorded three gaps. Two of them:

> * (C1) is **not proved**. It is a sharp pointwise inequality on one explicit
>   algebraic curve per degree, with equality at one point.
> * … branch 2's sign needs its own argument (its sector is the rotate by
>   `2 pi/n`).

and `NearFeketeCuspLaw.md` §7 carried the parent statement as measured:

> **(T) Monotone turning, exact total.** `tau` turns **monotonically** along each
> branch … Verified to `7.7e-9` (the cutoff tail, not `dps`).

All three are closed below. The mechanism is a single derivative identity, and
it does not care which branch it is on.

## 1. Notation

`n >= 3`, `g(zeta) = zeta^n + n zeta`, `g' = n(zeta^{n-1}+1)`, hub
`zeta_c = e^{i phi_c}` with `phi_c = pi/(n-1)`, `c_n = (n-1) sin(phi_c) = Im g(zeta_c)`.
Write `zeta = r e^{i phi}` and

```text
lambda = 1/(n-1),   theta = (n-1) phi,   a = (n-2)phi/2 = (1-lambda)theta/2,
                                         b = n phi/2     = (1+lambda)theta/2,
```

so `a + b = theta`, `b - a = phi`, and `c_n = sin(pi lambda)/lambda`. `Gamma_1`
and `Gamma_2` are the two descending branches at `zeta_c`, with asymptotic
directions `alpha_1 = 0` and `alpha_2 = 2 pi/n`; `sigma = Re g - Re g(zeta_c)`
is the parameter, `t = tau - alpha` the tangent offset. Set

> **`N(zeta) := g'(zeta) / (n zeta^{(n-2)/2}) = zeta^{n/2} + zeta^{-(n-2)/2}`**,
>
> ```text
> X := r^{(n-2)/2} Re N = r^{n-1} cos b + cos a,
> Y := r^{(n-2)/2} Im N = r^{n-1} sin b - sin a.
> ```

## 2. Lemma 1 — the sign of the turning is the sign of `X Y`

> **Lemma 1.** Off the hub, `dt/d sigma = ((n-1)/n) Im(N^2)/|N|^4`, and hence
> `sign(dt/d sigma) = sign(X Y)`.

*Proof.* `tau = arg(d zeta/d sigma) = -arg g'`, so
`dt/d sigma = -Im(g''/(g')^2)`. Now
`g''/(g')^2 = (n-1) zeta^{n-2}/(n (zeta^{n-1}+1)^2) = (n-1)/(n N^2)`, so
`dt/d sigma = -((n-1)/n) Im(1/N^2) = ((n-1)/n) Im(N^2)/|N|^4`. Finally
`Im(N^2) = 2 Re N Im N = 2 X Y / r^{n-2}`. ∎

So the whole question is the *quadrant* of `N`. At the hub `N = 0`; the limiting
argument there is `arg g''(zeta_c) + arg(zeta - zeta_c) - (n-2)phi_c/2`, which is
`0` on `Gamma_1` and `pi` on `Gamma_2`. The claim to prove is that each branch
stays in the quadrant it starts on the boundary of:

```text
Gamma_1:  X > 0, Y > 0   (first quadrant)   =>  dt/d sigma > 0
Gamma_2:  X < 0, Y > 0   (second quadrant)  =>  dt/d sigma < 0
```

`Y > 0` is required on **both**. That shared half is where the identity lives.

## 3. Lemma 2 — `Im g` on the two zero sets, in closed form

`{Y = 0}` and `{X = 0}` are graphs over `phi`:

```text
C_Y :  r^{n-1} =   sin a / sin b        C_X :  r^{n-1} = - cos a / cos b
```

(`C_X` is nonempty only where `cos a cos b < 0`.)

> **Lemma 2.** On `C_Y`, `Im g = K_+(theta)`; on `C_X`, `Im g = K_-(theta)`, where
>
> ```text
> W_pm(theta) = lambda^{-1} sin(lambda theta) +/- sin(theta)
> K_+ = ( sin a / sin b )^lambda  W_+ ,      K_- = ( -cos a / cos b )^lambda  W_- .
> ```

*Proof.* `Im g = r[ r^{n-1} sin 2b + n sin phi ]`. On `C_Y`,
`r^{n-1} sin 2b = 2 sin a cos b = sin(a+b) - sin(b-a) = sin theta - sin phi`, so
`Im g = r[ sin theta + (n-1) sin phi ] = r W_+`. On `C_X`,
`r^{n-1} sin 2b = -2 cos a sin b = -(sin theta + sin phi)`, so
`Im g = r[ (n-1) sin phi - sin theta ] = r W_-`. In both cases `r` is the
displayed radius, and `(n-1) sin phi = lambda^{-1} sin(lambda theta)`. ∎

Both pass through the hub: at `theta = pi`, `sin a = cos(lambda pi/2) = sin b`
and `-cos a/cos b = 1`, so both radii are `1`, and `W_+ = W_- = c_n`. Hence

```text
K_+(pi) = K_-(pi) = c_n .                                              (H)
```

## 4. Lemma 3 — the master identity

> **Lemma 3.** Wherever the expressions are defined and positive,
>
> ```text
> d/d theta  log K_+  =  (1 - lambda^2) sin^2(theta) / ( 2 sin a sin b W_+ )
> d/d theta  log K_-  =  (1 - lambda^2) sin^2(theta) / ( 2 cos a cos b W_- )
> ```

*Proof.* Write `S = sin(lambda theta)`, `T = sin(theta)`; note `da/d theta = a/theta`
and `db/d theta = b/theta`. For `K_+`,

```text
d/d theta log K_+ = (lambda/theta)(a cot a - b cot b) + (cos(lambda theta)+cos theta)/W_+,
```

and `cos(lambda theta) + cos theta = 2 cos a cos b`. Multiply by
`theta sin a sin b W_+`:

```text
Q_+ = lambda W_+ (a cos a sin b - b cos b sin a) + 2 theta sin a sin b cos a cos b .
```

Using `cos a sin b = (T+S)/2` and `cos b sin a = (T-S)/2`,

```text
lambda(a cos a sin b - b cos b sin a)
   = (lambda theta/2)[ (1-lambda)(T+S)/2 - (1+lambda)(T-S)/2 ]
   = (lambda theta/2)( S - lambda T ),
```

so the first term is `(lambda theta/2)(S - lambda T)(S/lambda + T) = (theta/2)(S^2 - lambda^2 T^2)`.
The second is `(theta/2) sin 2a sin 2b = (theta/2) sin((1-lambda)theta) sin((1+lambda)theta)
= (theta/2)(T^2 - S^2)`. They add to

```text
Q_+ = (theta/2)(1 - lambda^2) T^2 ,
```

which is the claim. For `K_-` the same computation with `2 sin a sin b` in place
of `2 cos a cos b` gives
`lambda(b sin b cos a - a sin a cos b) = (lambda theta/2)(S + lambda T)`, hence
`(theta/2)(S + lambda T)(S/lambda - T) = (theta/2)(S^2 - lambda^2 T^2)`, and the
same total `Q_- = (theta/2)(1-lambda^2)T^2`. ∎

**Everything cancels but `sin^2 theta`.** That single fact is the proof.

## 5. Lemma 4 — the weights are positive

> **Lemma 4.** `W_pm > 0` for `phi in (0, pi)`, hence on the whole range
> `theta in (0, 2 pi/(1+lambda))` used below.

*Proof.* `|sin(k phi)| <= k sin(phi)` for `phi in [0,pi]` and integer `k >= 1`, by
induction (`|sin((k+1)phi)| <= |sin k phi| + sin phi`), strictly for `k >= 2` and
`phi in (0,pi)`. Apply with `k = n-1 >= 2`. Here `phi = lambda theta < 2 pi/n < pi`. ∎

## 6. Corollary — the four sign regimes

`a in (0, pi)` and `b in (0, pi)` throughout `theta in (0, 2 pi/(1+lambda))`, so
`sin a, sin b > 0` there; `cos b > 0` exactly for `theta < pi/(1+lambda)`, i.e.
`phi < pi/n`; `cos a > 0` exactly for `theta < pi/(1-lambda)`. With (H) and
Lemma 3:

| range | `K_+` | `K_-` |
|---|---|---|
| `theta in (0, pi)` | increasing, so `< c_n` | on `(pi/(1+lambda), pi)`: decreasing, so `> c_n` |
| `theta in (pi, 2 pi/(1+lambda))` | increasing, so `> c_n` | decreasing, so `< c_n` |

In particular `Im g = c_n` holds **nowhere** on `C_Y` or `C_X` except at the hub.
Since `Gamma_1` and `Gamma_2` lie in `{Im g = c_n}`, neither branch meets either
zero set after the hub, so `X` and `Y` have constant sign along each.

## 7. Lemma 5 — branch 2 stays in its sector

`Gamma_1 subset {0 < phi < phi_c}` is Lemma S of
[ConeBoundBranchGeometry.md](ConeBoundBranchGeometry.md).

> **Lemma 5.** `Gamma_2 subset {phi_c < phi < 2 pi/n}`.

*Proof.* The initial direction at the hub is `arg sqrt(2/g''(zeta_c)) + pi`,
whose argument minus `phi_c` is `pi n/(2(n-1)) - pi/(n-1) in (0, pi)`, so
`Gamma_2` leaves into `phi > phi_c`.

*Lower wall.* By Lemma S the ray `phi = phi_c` meets `{Im g = c_n}` only at
`zeta_c`.

*Upper wall.* On `phi = 2 pi/n`, `zeta^n = r^n > 0`, so `Im g = n r sin(2pi/n)`,
strictly increasing in `r`: the ray meets `{Im g = c_n}` at the single point
`Z_0 = r_0 e^{2 pi i/n}`, `r_0 = c_n/(n sin(2 pi/n))`. Along any descending
branch `Re g = Re g(zeta_c) + sigma` is strictly increasing, so it suffices that

```text
Re g(Z_0) = r_0^n + c_n cot(2 pi/n)  <  (n-1) cos(phi_c) = Re g(zeta_c),
```

which rearranges to `r_0^n < (n-1) sin(2pi/n - phi_c)/sin(2 pi/n)`, i.e. to
`r_0^n < (n-1) sin(pi(n-2)/(n(n-1)))/sin(2 pi/n) =: M_n`.

`r_0 < 1`: with `f(x) = sin x/x` decreasing on `[0,pi]`, `r_0 < 1` says
`f(phi_c) < 2 f(2 pi/n)`, and `f(phi_c) <= f(pi/2) = 2/pi = 0.6366` while
`2 f(2 pi/n) >= 2 f(2 pi/3) = 0.8270`.

`M_n >= 1`: direct for `n = 3, 4, 5` (`1.1547`, `1.5`, `1.9097`); for `n >= 6`,
`sin x >= 2x/pi` on `[0,pi/2]` and `sin y <= y` give
`M_n >= (n-1) * (2/pi)(n-2)/(2(n-1)) = (n-2)/pi >= 4/pi > 1`.

So `r_0^n < 1 <= M_n`, and `Z_0` is not on `Gamma_2`. Finally `r -> 0` is
impossible (`Im g -> 0 != c_n`), so `Gamma_2` is trapped. ∎

## 8. Theorem

> **Theorem.** Along `Gamma_1`, `X > 0` and `Y > 0`; along `Gamma_2`, `X < 0`
> and `Y > 0`. Consequently `dt/d sigma > 0` on `Gamma_1` and `dt/d sigma < 0`
> on `Gamma_2`, everywhere after the hub.

*Proof.* By §6 each of `X`, `Y` has constant sign on `Gamma_i \ {zeta_c}`, so it
is enough to name the sign at one point of each branch.

*`Y` on `Gamma_1`.* For `theta < pi` we have `a < b` and `a + b < pi`, so
`sin a < sin b` and `C_Y` lies strictly inside the unit circle. Any point of
`Gamma_1` with `r >= 1` therefore has `Y > 0`, and `Gamma_1` is unbounded because
`Re g = Re g(zeta_c) + sigma -> infinity` forces `|zeta| -> infinity`.

*`X` on `Gamma_1`.* Where `phi <= pi/n` both `cos a > 0` and `cos b >= 0`, so
`X > 0` outright; `Gamma_1` reaches that region since `phi -> 0`.

*`X` on `Gamma_2`.* By Lemma 5, `phi -> 2 pi/n`, so `b -> pi` and `cos b -> -1`;
for `r` large `X = r^{n-1} cos b + cos a < 0`.

*`Y` on `Gamma_2`.* On the same far field, `Im g = c_n` reads
`2 r^n sin b cos b = c_n - n r sin phi`, so

```text
r^{n-1} sin b = ( c_n/r - n sin phi ) / (2 cos b)  ->  n sin(2 pi/n)/2 ,
```

while `sin a -> sin((n-2)pi/n) = sin(2 pi/n)`. Hence
`Y -> (n-2) sin(2 pi/n)/2 > 0`. (The probe confirms the sharper
`Y(R) = (n-2)sin(2pi/n)/2 - c_n/(2R) + O(R^{-2})`.)

Lemma 1 converts the quadrants into the sign of `dt/d sigma`. ∎

## 9. What this closes

`t` is continuous on each branch with `t -> 0` at infinity (`arg zeta -> alpha`
and `e^{i n alpha} = 1`), and `t(zeta_c^+) = -T_1` on `Gamma_1`, `= +T_2` on
`Gamma_2`, both read off `arg g''(zeta_c) = (n-2)pi/(n-1)` in closed form. With
the Theorem:

* **(T) is proved.** `t` increases from `-T_1` to `0` on `Gamma_1` and decreases
  from `+T_2` to `0` on `Gamma_2`. Monotone, so total variation `= |Delta tau| = T_i`,
  and the totals are the closed forms `T_1 = (n-2)pi/(2(n-1))`,
  `T_2 = (n-2)^2 pi/(2n(n-1))` already recorded.
* **Constant sign is proved** on both branches — `t < 0` throughout `Gamma_1`,
  `t > 0` throughout `Gamma_2` — which is hypothesis (i) of `TurningLengthBound.md` §5.
* **`|t| <= T_i` is proved**, which is hypothesis (ii), i.e. **(C1) and its
  branch-2 analogue**, the sharp inequalities §6 of that note left open.
* **Branch 2's sector** is proved (Lemma 5).

By §2 of `TurningLengthBound.md` this gives `D_i <= tan(T_i/2)|sin gamma_i|`
unconditionally, and by its §3 Proposition `C_n - B_n > 0` at every `n >= 3`. So

> On the limit model, **`kappa_n > 0` now follows from the bridge (BR) alone.**

(BR) is itself still *measured* — `NearFeketeCuspLaw.md` §7 verifies it to
`6.2e-27` and its claim boundary does not list it as proved. So the near-Fekete
half is not finished; what is finished is everything downstream of the bridge.

## 10. Why `n = 3` produced a cubic

`ConeBoundBranchGeometry.md` §5 found the exact factorisation
`3 r y (2r - sin(phi)(r^2+1)) = -4(y-1)^3(y+1)` and called the cubic vanishing
"the striking feature … unexplained". It is Lemma 3: the derivative of
`log K_pm` carries `sin^2 theta`, which vanishes to order two at `theta = pi`, so
`K_pm - c_n` vanishes to order **three** at the hub, with

```text
(K_+ - c_n)/(theta-pi)^3 -> +(1-lambda^2)/(6 cos^2(lambda pi/2)),
(K_- - c_n)/(theta-pi)^3 -> -(1-lambda^2)/(6 sin^2(lambda pi/2)).
```

At `n = 3` the first constant is `1/4`. The cubic is general, not a degree-three
accident, and it is why `theta = pi` is a stationary point of `log K_+` that is
nevertheless **not** a maximum — `K_+` increases straight through it. That sign
flip either side of the hub is exactly what lets one lemma serve both branches:
`C_Y` sits inside `{Im g < c_n}` on `Gamma_1`'s side and outside it on
`Gamma_2`'s.

## 11. Three things that stayed dead

The routes `ConeBoundBranchGeometry.md` §6 refuted are untouched by this and
should not be retried: the sufficient split through
`sin((n-2)phi) <= r^{n-2} sin(phi_c)` is false; `Re G >= 0` is false on the
branch; and `r >= 1` covers a minority of it. The present proof avoids all three
because it never estimates the branch — it estimates the *zero sets it must not
cross*, which are explicit graphs with no level-set constraint on them.

## Claim boundary

Proved, by ordinary mathematics: Lemma 1 (sign law), Lemma 2 (`Im g` on `C_Y`,
`C_X`), Lemma 3 (the master identity — also checked symbolically by sympy),
Lemma 4, the §6 sign regimes, Lemma 5, and the Theorem of §8, hence (T),
constant sign, `|t| <= T_i`, and (C1) on both branches, at every `n >= 3`.

Measured, not proved: nothing this note *relies* on. The probe's sections B–F
are confirmations of proved statements at 50 digits, and section D is a float64
root-continuation cross-check whose resolved fraction (`0.875`–`1.000`) is
reported. `dt/d sigma` blows up at the hub, where `N -> 0`, so its sign is read
off `X Y`, which stays well conditioned.

Inherited, still measured: the bridge (BR) (`6.2e-27`), the values of `D_i` and
`kappa_n`, and everything in `NearFeketeCuspLaw.md`'s own claim boundary.

Not established: novelty. Lemma 3 is one page of elementary trigonometry and the
quadrant argument is a standard separation; both should be assumed known until a
priority search on Newton-flow trajectories and lemniscate geometry says
otherwise. Also untouched: the `D`-away-from-1 half, the `O(rho^2)` remainder,
the degenerate direction `h'(0) = 0`, anything at finite perturbation, and the
constant 2.

**Erdős #1041 remains open.**

## Replay

```sh
./repo-python formal_math/probes/erdos1041_monotone_turning.py --max-n 12
```
