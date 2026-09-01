# Erdős 1041: the cone bound is one monotone harmonic functional

Status: a second, shorter proof of a theorem that was proved concurrently by
another route, plus three things that route does not carry — a family of monotone
functionals, an exact window that selects the hub, and Theorem R, which closes the
last measured link in the near-Fekete chain by proving `kappa_n(phi) > 0` at every
perturbation direction and not only at `phi = 0`. 2026-08-24.
**This does not prove Erdős #1041.**

Scope, per `ade3b6ac08` and `TurningLengthBound.md` §4a: everything below lives
on the fixed near-field model `g(zeta) = zeta^n + n zeta`, one polynomial per
degree. Nothing here is a statement about a perturbed polynomial.

## 0. Concurrent derivation — what is and is not first here

**The main conclusion is not first here.** While this file was being written,
commit `1783f08f31` landed
[MonotoneTurningProof.md](MonotoneTurningProof.md), which proves monotone
turning on both branches at every degree by a different mechanism: the turning
has the sign of `X Y` where `X + iY = r^{(n-2)/2} g'/(n zeta^{(n-2)/2})`, and a
master identity for `Im g` on the two zero sets `{X=0}`, `{Y=0}` shows neither
meets the level set off the hub, so each branch is trapped in its starting
quadrant. That file closes (T), (C1) and its branch-2 analogue, branch 2's
sector, and (★) for `n >= 4` and on branch 2. [BridgeIdentityProof.md](BridgeIdentityProof.md),
landed the same day, then proves the bridge (BR) and assembles

```text
kappa_n = C_n - (D_1 + D_2) >= C_n - B_n > 0        at every n >= 3.
```

So **`kappa_n > 0` at every degree is theirs, not this file's**, and §5 below is
a restatement of it rather than a new corollary. The quadrant argument is also
strictly stronger in one respect: it *proves* the confinement that the argument
below *assumes*.

What this file adds:

1. **A shorter proof of the same theorem**, once confinement is granted. (★) is
   not a trigonometric inequality at all — it is the statement that one explicit
   harmonic function is monotone along the branch. Three one-line facts about
   `Xi(zeta) = (n-2) zeta - zeta^{2-n}` and the fundamental theorem of calculus
   replace the master identity. It needs no factorisation, and the `r >= 1` and
   `Re G >= 0` obstructions of `ConeBoundBranchGeometry.md` §6 do not arise.
2. **The family** (§6). `Xi` is the `m = n-1` member of `n-1` monotone
   functionals `Xi_m`, one for each `m = 1..n-1`, and the family stops exactly at
   `m = n`. Lemma B is the shadow of the same sign fact.
3. **The whole descent-ray direction question** (§7, §7a, §7b), which is in
   neither concurrent file. The `Xi` identities are direction-free; confinement is
   not, and the asymptotic directions pin its window to `(0, 2 pi/(n-1))` — an
   interval whose length is exactly the hub spacing, so exactly one of the `n-1`
   hubs is admissible (Proposition W). Sufficiency on that window is then proved
   too (Lemma S(δ), Lemma W2), and Theorem R carries `C_n > B_n` across it. The
   result is `kappa_n(phi) > 0` at **every** direction, which is exactly the link
   [BridgeIdentityProof.md](BridgeIdentityProof.md) §4a records as *measured and
   still load-bearing*, and the one
   `NearFeketeCuspPositivityProof.md` §4 leaves open as "other ray directions".

## 0a. What was open when this started

`ConeBoundBranchGeometry.md` reduces the cone hypothesis `|t| <= T` to the
pointwise inequality

> **(★)**  `Phi := c_n r^{n-2} - (n-2) r^{n-1} sin(phi) - sin((n-2) phi) >= 0`

on the level set `Im g = c_n`, proves it at `n = 3` on branch 1 by an exact
factorisation `(y-1)^3 (y+1)`, and records that the factorisation is special to
degree three: *"Whether the `n = 3` factorisation has a general-`n` analogue.
The cubic vanishing at the hub is the striking feature and is unexplained."*
(`MonotoneTurningProof.md` explains it: `sin^2` forces order-3 vanishing at the
hub.)

## 1. The functional

Notation as in `ConeBoundBranchGeometry.md`: `zeta = r e^{i phi}`,
`phi_c = pi/(n-1)`, `zeta_c = e^{i phi_c}`, `c_n = (n-1) sin(phi_c)`,
`P = zeta^{n-1}`, `G = zeta^n + zeta = zeta g'(zeta)/n`. Both descending branches
at `zeta_c` are the `g`-preimages of the ray `{(n-1) zeta_c + sigma : sigma >= 0}`,
parametrised so that `g(zeta(sigma)) = (n-1) zeta_c + sigma`; both lie in
`Im g = c_n`.

> **Definition.** For `n >= 3` put
>
> ```text
> Xi(zeta) := (n-2) zeta - zeta^{2-n}.
> ```

`Im Xi` is harmonic on `C \ {0}`. Three facts, each one line.

> **(X1)** `Xi'(zeta) = (n-2)(1 + zeta^{1-n}) = ((n-2)/n) * g'(zeta) / zeta^{n-1}`.
>
> **(X2)** `Xi(zeta_c) = (n-1) zeta_c`, so `Im Xi(zeta_c) = c_n`.
>
> **(X3)** On the level set `Im g = c_n`,
>
> ```text
> Im( G^2 / zeta^n )  =  c_n - Im Xi(zeta)  =  Phi / r^{n-2}.
> ```

*Proofs.* (X1) is `d(-zeta^{2-n})/d zeta = (n-2) zeta^{1-n}`, and
`g' = n(zeta^{n-1}+1)`. (X2): `zeta_c^{n-1} = -1` gives
`zeta_c^{2-n} = zeta_c * zeta_c^{1-n} = -zeta_c`, so
`Xi(zeta_c) = (n-2)zeta_c + zeta_c`. (X3): expand
`G^2/zeta^n = zeta^{2-n}(zeta^{n-1}+1)^2 = zeta^n + 2 zeta + zeta^{2-n}`, take
imaginary parts, and substitute `Im(zeta^n) = c_n - n Im(zeta)` from the level
set; what is left is `c_n - (n-2)Im(zeta) + Im(zeta^{2-n}) = c_n - Im Xi`. The
second equality is the definition of `Phi` divided by `r^{n-2}`, using
`Im(zeta^{2-n}) = -r^{2-n} sin((n-2)phi)`. ∎

So (★) is exactly `Im Xi <= Im Xi(zeta_c)` — the same shape as Lemma B's
`Im zeta <= Im zeta_c`, with `zeta` replaced by `Xi`.

## 2. Lemma M — `Im Xi` is monotone along a branch, with the sign of `Im g'`

> **Lemma M.** Along a descending branch,
>
> ```text
> d(Im Xi)/d sigma  =  ((n-2)/n) Im( zeta^{1-n} )  =  -((n-2)/n) sin((n-1)phi) / r^{n-1},
> ```
>
> which is strictly negative wherever `Im g' > 0` and strictly positive wherever
> `Im g' < 0`.

*Proof.* `d zeta/d sigma = 1/g'`, so by (X1)
`d Xi/d sigma = Xi'/g' = ((n-2)/n) zeta^{1-n}`, and
`Im(zeta^{1-n}) = -r^{1-n} sin((n-1)phi)`. Since
`Im g' = n Im(zeta^{n-1}) = n r^{n-1} sin((n-1)phi)`, the two have opposite
signs. ∎

This is the same one-line computation as Lemma B, which is
`dy/d sigma = Im(1/g') = -Im(g')/|g'|^2`. **Lemma B and (★) are the same fact
applied to two members of one family** — see §6.

> **Corollary (the sign of the turning derivative).** With
> `t = arg(d zeta) - alpha` the tangent offset,
>
> ```text
> dt/d sigma  =  -Im( g''/(g')^2 )  =  ((n-1)/n) * Im(G^2/zeta^n) / |G^2/zeta^n|^2,
> ```
>
> so `sign(dt/d sigma) = sign(c_n - Im Xi) = sign(Phi)` by (X3).

*Proof.* `g''/(g')^2 = ((n-1)/n) zeta^n/G^2` and `Im(1/w) = -Im(w)/|w|^2`. ∎

## 3. Confinement: `Im g'` has constant sign on each branch

Branch 1 (asymptotic direction `alpha_1 = 0`) is confined to the sector
`0 < phi < phi_c` — this is **Lemma S of
[ConeBoundBranchGeometry.md](ConeBoundBranchGeometry.md) §1**, proved there, and
it is used here as given. Then `(n-1)phi in (0, pi)` and `Im g' > 0`.

Branch 2 has asymptotic direction `alpha_2 = 2 pi / n`, and
`phi_c < alpha_2 < 2 phi_c` for every `n >= 3`.

> **Lemma S2.** Branch 2 is confined to the sector `phi_c < phi < 2 phi_c`.
> Hence `(n-1) phi in (pi, 2 pi)` and `Im g' < 0` on it.

*(Not first: this is Lemma 5 of [MonotoneTurningProof.md](MonotoneTurningProof.md).
The proof below is independent — it uses only the level set and the asymptotic
direction — so it is kept as a second route, not as a claim of priority.)*

*Proof.* The initial directions at the simple hub solve
`g''(zeta_c)(d zeta)^2 > 0`; since `arg g''(zeta_c) = (n-2)phi_c = pi - phi_c`
they are `-(pi - phi_c)/2` and `(pi + phi_c)/2`. Branch 2 is the second, which
increases `phi`, so it enters `phi > phi_c` immediately.

*The wall `phi = phi_c`.* Lemma S's own computation gives
`Im g = sin(phi_c)(n r - r^n) <= (n-1) sin(phi_c) = c_n` on that ray, with
equality only at `r = 1`. So the level set meets the ray only at `zeta_c`, and
`g` is injective along the branch (`g = (n-1)zeta_c + sigma`), so the branch
never returns to it.

*The wall `phi = 2 phi_c`.* There `zeta^{n-1} = r^{n-1}` is positive real, so
`zeta^n = r^n e^{2 i phi_c}` and

```text
Im g = sin(2 phi_c) ( r^n + n r ).
```

For `n = 3`, `2 phi_c = pi` and this is `0 != c_3`: the level set misses the ray
entirely. For `n >= 4`, `0 < 2 phi_c < pi`, so `sin(2 phi_c) > 0` and the right
side is **strictly increasing in `r > 0`** from `0` to `+infinity`. Hence the
level set meets this ray in exactly one point.

Now suppose branch 2 left the sector. It can only do so through the outer wall,
at that single point, and — `g` being injective along the branch — it can never
cross back. But branch 2 tends to infinity with `arg zeta -> alpha_2`, and
`phi_c < alpha_2 < 2 phi_c`, so its argument is eventually strictly inside the
sector, forcing a second crossing. Contradiction. ∎

*(Measured, for calibration rather than proof: branch 2's argument rises
monotonically from `phi_c` and accumulates at `alpha_2` from below, never
reaching the outer wall at all — at `n = 10`, `phi` runs `0.3490658 …
0.6283165` against `alpha_2 = 0.6283185` and `2 phi_c = 0.6981317`.)*

## 4. Theorem — the cone bound, both branches, every degree

> **Theorem C.** For every `n >= 3`, on each of the two descending branches at a
> hub of `g(zeta) = zeta^n + n zeta`:
>
> * **(★) holds with strict inequality after the hub.** On branch 1,
>   `Im Xi < c_n`, i.e. `Phi > 0`; on branch 2, `Im Xi > c_n`, i.e. `Phi < 0`.
> * `t` is strictly monotone, has constant sign, and satisfies
>
>   ```text
>   |t| <= T_i,     T_1 = (n-2)pi/(2(n-1)),     T_2 = (n-2)^2 pi/(2 n (n-1)),
>   ```
>
>   with equality only at the hub.

*Proof.* By (X2) the function `u := c_n - Im Xi` vanishes at the hub. By §3 and
Lemma M, `u' > 0` on branch 1 and `u' < 0` on branch 2, throughout. Hence
`u > 0` on branch 1 and `u < 0` on branch 2 after the hub, which is the first
claim; and by the Corollary of §2, `t' > 0` on branch 1 and `t' < 0` on
branch 2, so `t` is strictly monotone.

For the bound, `t` is monotone and takes values in a bounded interval, so it has
a limit at infinity; the branch is asymptotic to a ray of direction `alpha` with
`e^{i n alpha} = 1` and `g' ~ n zeta^{n-1}`, so `arg(d zeta) = -arg g' ->
-(n-1)alpha = alpha (mod 2 pi)`, i.e. the limit of `t` is `0 mod 2 pi`. Section 3
pins which representative: on branch 1, `P` lies in the open upper half-plane so
`t = -arg(1+P) in (-pi, 0)`; on branch 2, `P` lies in the open lower half-plane
so `t = -arg(1+P) - alpha_2 in (-alpha_2, pi - alpha_2)`, and
`alpha_2 <= 2 pi/3`. In both cases `0` is the only admissible limit. So `t`
increases from `t(0^+)` to `0` on branch 1 and decreases from `t(0^+)` to `0` on
branch 2, giving constant sign and `|t| <= |t(0^+)|`.

Finally `t(0^+)` is the initial tangent offset, computed from
`arg g''(zeta_c) = pi - phi_c` exactly as in §3:

```text
branch 1:  t(0^+) = -(pi - phi_c)/2 - 0      = -(n-2)pi/(2(n-1))          = -T_1,
branch 2:  t(0^+) =  (pi + phi_c)/2 - 2pi/n  =  (n-2)^2 pi/(2 n (n-1))    =  T_2.
```

∎

The sign pattern is worth stating plainly, because it is the reason a single
argument covers both branches: **(★) is false on branch 2 as stated** — `Phi`
is negative there — and that is exactly right, because branch 2 needs
`|t|` decreasing from a *positive* start, hence `dt/d sigma < 0`, hence
`Phi < 0`. The corpus's (★) is the branch-1 specialisation of the correct
statement, which is `sign(Phi) = -sign(t(0^+))`.

## 5. Consequence — `kappa_n > 0` at every degree (not first here; see §0)

`TurningLengthBound.md` §2 proves `D <= tan(T/2)|sin gamma|` whenever `|t| <= T`
with constant sign, and §3 proves in closed form, for every `n >= 3`, that

```text
C_n := sum_i cos gamma_i   >   B_n := sum_i tan(T_i/2)|sin gamma_i|.
```

Theorem C supplies the hypothesis of §2 at every degree on both branches, so:

> **Corollary K.** `kappa_n >= C_n - B_n > 0` for every `n >= 3`.

This is the assembly carried out in [BridgeIdentityProof.md](BridgeIdentityProof.md)
§4 out of (BR), [MonotoneTurningProof.md](MonotoneTurningProof.md), and
`TurningLengthBound.md` §§2–3, and it is recorded here only because Theorem C
supplies the same hypothesis by a different route. The bridge (BR), which turns
`kappa_n` into `C_n - (D_1+D_2)`, was itself measured until the same day and is
now proved in that file; without it this consequence would be conditional.

| n | `kappa_n` (measured) | `C_n - B_n` (proved lower bound) |
|---|---|---|
| 3 | `0.6080213` | **`0.3859856`** |
| 4 | `1.0300780` | `0.7320508` |
| 5 | `1.2585430` | `0.9581537` |
| 6 | `1.3988800` | `1.1144207` |
| 8 | `1.5622000` | `1.3163027` |
| 10 | `1.6547390` | `1.4417280` |

Before 2026-08-24 `kappa_n > 0` was a theorem only at `n = 3`, via the `L^2`
route of [NearFeketeCuspPositivityProof.md](NearFeketeCuspPositivityProof.md),
which returns `15 sqrt3/32 - 3/5 = 0.2119`. The turning route returns `0.3860` at
`n = 3` — 82% more — and does not stop at degree three.

## 6. The whole family, and why Lemma B is the `m = n-1` member

Nothing above used `Xi` specifically. For any integer `m` let `Xi_m` be an
antiderivative of `g'(zeta) zeta^{-m}`; then along a branch
`d Xi_m / d sigma = zeta^{-m}`, so

```text
d(Im Xi_m)/d sigma  =  -sin(m phi)/r^m.
```

By Lemma S this is strictly negative on branch 1 for **every** `m` in
`1..n-1`, since then `m phi < m pi/(n-1) <= pi`. So branch 1 carries `n-1`
independent monotone functionals, explicitly

```text
Xi_m(zeta) = n zeta^{n-m}/(n-m) + n zeta^{1-m}/(1-m)     (m != 1, n),
Xi_1(zeta) = n zeta^{n-1}/(n-1) + n log zeta.
```

`m = n-1` gives `Xi_{n-1} = n zeta - n zeta^{2-n}/(n-2) = (n/(n-2)) Xi`, which is
Theorem C. The `m` that reproduces Lemma B is the degenerate direction: Lemma B
is `d(Im zeta)/d sigma = Im(1/g') < 0`, the same sign fact routed through `1/g'`
rather than through `g' zeta^{-m}`. The family stops at `m = n-1` because
`sin(n phi)` changes sign inside the sector.

Two of the members are worth recording as facts about the branch rather than as
machinery. `m = 1` gives that `((n/(n-1)) r^{n-1} sin((n-1)phi) + n phi)` is
strictly decreasing, and `m = n-2` gives a second sharp inequality of exactly
(★)'s shape one step down. Neither is used above.

## 7. The ray direction drops out of the algebra, and selects the hub

`NearFeketeCuspPositivityProof.md` §4 restricts its theorem to the aligned
direction: *"The model is `zeta^n + n e^{i phi} zeta` … `phi` survives as the
ray angle, and only `phi = 0` is treated here."* Under the rotation recorded
there the descent ray in the standard model `g(zeta) = zeta^n + n zeta` has
direction `e^{-i delta}` with `delta = n phi/(n-1)`, and the branch satisfies
`g(zeta(s)) = (n-1)zeta_c + s e^{i delta}` after absorbing the sign.

**The algebra is direction-free.** Everything in §1, §2 and §4 survives verbatim,
because the phase cancels:

```text
d Xi/ds  =  Xi'(zeta) e^{i delta}/g'  =  ((n-2)/n) e^{i delta} zeta^{1-n},
```

so `d/ds Im( e^{-i delta} Xi ) = ((n-2)/n) Im(zeta^{1-n})` — **the same expression,
with no `delta` in it**. The level set becomes `Im(e^{-i delta} g) = c` with
`c := Im(e^{-i delta}(n-1)zeta_c)`, (X2) becomes `Im(e^{-i delta}Xi(zeta_c)) = c`,
and (X3) becomes `Im(e^{-i delta} G^2/zeta^n) = c - Im(e^{-i delta} Xi)`, which is
again the sign of `dt/ds`. Only §3 — confinement — is direction-dependent.

**And confinement selects exactly one hub.** The asymptotic directions pin the
window exactly. As `s -> oo`, `zeta^n ~ s e^{i delta}`, so branch `i` escapes along
`arg zeta -> (delta + 2 pi k_i)/n` with `k_1 = 0` and `k_2 = 1`; that direction must
lie in the branch's own sector, `(0, phi_c)` for branch 1 and `(phi_c, 2 phi_c)` for
branch 2. Solving:

```text
branch 1 confined  ==>  delta in ( 0 , n pi/(n-1) ),
branch 2 confined  ==>  delta in ( -(n-2) pi/(n-1) , 2 pi/(n-1) ),
both               ==>  delta in ( 0 , 2 pi/(n-1) ).
```

> **Proposition W.** The both-branches window has length exactly `2 pi/(n-1)`,
> which is exactly the spacing of the hub orbit under the symmetry
> `g(omega zeta) = omega g(zeta)`, `omega = e^{2 pi i/(n-1)}`. Hence for every
> configuration **exactly one of the `n-1` hubs has both branches confined**, and
> the cusp law, which minimises over hubs, always has that one available.

*Proof of the length claim.* The two intervals above intersect in `(0, 2 pi/(n-1))`
since `2 pi/(n-1) < n pi/(n-1)` for `n > 2` and `-(n-2)pi/(n-1) < 0`. The symmetry
rotates hub `zeta_c` to `omega zeta_c` and the ray direction by the same `omega`,
so hub `k` at direction `delta` is hub `0` at direction `delta - 2 pi k/(n-1)`; the
`n-1` translates of any `delta` by the hub spacing meet an interval of exactly that
length in exactly one point, off the lattice. ∎

### 7a. Sufficiency on the window is also proved

Necessity above is a statement about asymptotic directions. Sufficiency needs the
two walls, and both arguments survive the change of direction.

> **Lemma S(δ).** For every `delta in [0, pi]`, the level argument of Lemma S
> holds verbatim, so **neither branch meets the ray `arg zeta = phi_c` except at
> the hub, and neither meets `arg zeta = 0` at all**. In particular branch 1 is
> confined to `(0, phi_c)`.

*Proof.* Along the branch `Im g = c_n + s sin(delta) >= c_n`, with equality only
at `s = 0` when `sin delta > 0`. On the ray `arg zeta = 0` the value `g` is real,
so `Im g = 0 < c_n`: the branch misses it. On the ray `arg zeta = phi_c`,
Lemma S's own computation gives `Im g = sin(phi_c)(n r - r^n) <= c_n` with
equality only at `r = 1`; so a meeting forces `zeta = zeta_c` **and**
`s sin delta = 0`, and `g` is injective along the branch, so `s = 0`. The two
rays disconnect `C \ {0}`, and the initial direction
`(delta - pi + phi_c)/2` decreases `arg zeta` for `delta < pi + phi_c`, so
branch 1 starts inside `(0, phi_c)` and stays. ∎

Since `2 pi/(n-1) <= pi` for every `n >= 3`, **the whole window lies in
`[0, pi]`** and Lemma S(δ) covers all of it.

> **Lemma W2 (the outer wall is a one-way barrier).** For `delta in (0, 2 phi_c)`
> branch 2 is confined to `(phi_c, 2 phi_c)`.

*Proof.* The inner wall is Lemma S(δ), and the initial direction
`(delta - pi + phi_c)/2 + pi` increases `arg zeta`, so branch 2 starts inside.
On the outer ray `arg zeta = 2 phi_c` we have `zeta^{n-1} = r^{n-1} > 0`, so
`g' = n(r^{n-1} + 1)` is **real and positive**; since
`d zeta/ds = e^{i delta}/g'` and `d(arg zeta)/ds = Im( (d zeta/ds)/zeta )`,

```text
d(arg zeta)/ds  =  Im( e^{i delta} / (zeta g') )  =  sin(delta - 2 phi_c) / (r g')
```

at **every** point of that ray. For `delta in (0, 2 phi_c)` the angle
`delta - 2 phi_c` lies in `(-2 phi_c, 0) subset (-pi, 0)`, because
`2 phi_c <= pi`; so the right side is strictly negative and the flow points
strictly inward everywhere on the wall. A first contact at `s_1` would force
`d(arg zeta)/ds >= 0` there. Contradiction. (At `delta = 0` the same sign holds
for `n >= 4`; at `n = 3`, `2 phi_c = pi` and `Im g = 0` on that ray, so Lemma S(δ)
excludes it.) ∎

*Verification.* The wall identity holds to `1.1e-25` at 30 digits, and a sweep of
degrees 3–12 x 15 interior directions x both branches — 240 traces — reports no
excursion and no sign change of `Im g'`.

### 7b. Theorem R — the near-Fekete half closes at every ray direction

The remaining direction-dependent object is the pair `(gamma_i, T_i)`, which the
asymptotic directions give in closed form:

```text
alpha_1 = delta/n,   alpha_2 = (delta + 2 pi)/n,   gamma_i = phi_c - alpha_i,
tau_0   = (delta - pi + phi_c)/2,   T_1 = |tau_0 - alpha_1|,  T_2 = |tau_0 + pi - alpha_2|.
```

`T_1` and `T_2` are affine in `delta` with the same slope `(n-2)/(2n)`, and at the
two ends of the window they **swap**: `T_1(2 phi_c) = T_2(0)` and
`T_2(2 phi_c) = T_1(0)`, both `< pi/2`. So `tan(T_i/2) < 1` throughout.

> **Theorem R.** `C_n(delta) > B_n(delta)` for every `n >= 3` and every `delta` in
> the closed window `[0, 2 pi/(n-1)]`. Hence, with Lemma S(δ), Lemma W2 and
> Theorem C, `kappa_n(phi) > 0` for **every** perturbation direction `phi`.

*Proof.* For `n >= 5`: `gamma_1 = phi_c - delta/n in [phi_c(1 - 2/n), phi_c]` and
`gamma_2 = phi_c - (delta + 2 pi)/n in (-phi_c, -(n-2)pi/(n(n-1)))`, so
`|gamma_i| <= phi_c = pi/(n-1) <= pi/4` for both. Then
`|sin gamma_i| < cos gamma_i` termwise, and with `tan(T_i/2) < 1`,
`B_n <= |sin gamma_1| + |sin gamma_2| < cos gamma_1 + cos gamma_2 = C_n`.

For `n = 3, 4` the bound `|gamma_i| <= pi/4` fails and the check is a
one-variable Lipschitz certificate. `|C_n'| <= 2/n`; and since `T_i' = (n-2)/(2n)`,
`T_i < pi/2` gives `|d tan(T_i/2)/d delta| <= (n-2)/(2n) <= 1/2`, so
`|B_n'| <= 2(1/2 + 1/n) = 1 + 2/n` and `L := 1 + 4/n` is a Lipschitz constant.
On a grid of `20000` points the minima are `0.385985592618` at `n = 3` and
`0.732050807569` at `n = 4`, against half-step penalties `1.8e-4` and `1.1e-4`,
leaving certified lower bounds `0.3858` and `0.7319`. ∎

The minimum of `C_n - B_n` over the window is attained at `delta = 0` at every
degree tested, so the aligned direction — the only one previously proved — is the
worst case **for this lower bound**. That is a statement about `C_n - B_n`, not
about `kappa_n` itself: [RayDirectionScopeLimit.md](RayDirectionScopeLimit.md) §4
shows the recorded 24-point sweep of `kappa_n(phi)` samples a singular direction
at its maximum and the antipode at its minimum, so `phi = 0` must **not** be
quoted as `argmin_phi kappa_n`. That clause is withdrawn from this file.

Why positivity on one window is positivity everywhere: `kappa_n` has period
`2 pi/(n-1)` in `delta` — `RayDirectionScopeLimit.md` §4 records exactly this at
`n = 3` ("`kappa_3` has period `pi` in `delta`"), and `pi = 2 pi/(n-1)` there.
That period is the hub spacing, because rotating the hub by `omega` and the ray
by `omega` is a symmetry of `g`. **So the window is exactly one full period**, and
Theorem R covers every direction.

**What this closes.** [BridgeIdentityProof.md](BridgeIdentityProof.md) §4a records
the remaining gap in its own terms:

> **This is `kappa_n(0)`, not `kappa_n(phi)` for every `phi`.** … the `phi != 0`
> branches live in `Im(e^{i n phi/(n-1)} g) = const`, not in `Im g = c_n`, so they
> are **not** covered by anything proved here.

and lists "that `min_phi kappa_n(phi)` is attained at `phi = 0`" as *measured and
still load-bearing*. Theorem R replaces that measurement. Its four links all
survive the change of direction:

| # | link | why it is direction-free |
|---|---|---|
| 1 | `kappa_n(phi) = beta_1 + beta_2` | the cusp law's §2 scaling is stated for general `phi` |
| 2 | (BR), `beta_i = cos gamma_i - D_i` | its identity `(*)` uses only `\|zeta_c\| = 1` and `d zeta/ds = e^{i tau}`; its Lemma needs only that `V` is bounded |
| 3 | `D_i <= tan(T_i/2)\|sin gamma_i\|` | needs Lemma T (below), constant sign, and `\|t\| <= T_i` — the last two from Theorem C plus §7a |
| 4 | `C_n > B_n` | Theorem R |

Link 2's hypothesis is Lemma T, which also generalises. With
`e^{i n alpha} = e^{i delta}` and `u = e^{-i alpha} zeta`, the branch equation
becomes

```text
u^n + n u e^{i(alpha - delta)}  =  (n-1) zeta_c e^{-i delta} + s,
```

whose right side again has `s`-independent imaginary part `c`. Taking imaginary
parts,

```text
V ( n U^{n-1} + n cos(alpha - delta) )  =  c - n U sin(alpha - delta) + O(V^2),
```

so `V = O(U^{-(n-2)})` when `sin(alpha - delta) != 0` and `O(U^{-(n-1)})` when it
vanishes — the same conclusion as at `delta = 0`, and in particular `V -> 0`. So
Lemma T holds at every direction, with `-sin gamma` the value of the integral.

**Consequence.** On the limit model the near-Fekete half is proved at every degree
**and every perturbation direction**. What remains on that side is the `O(rho^2)`
remainder, the degenerate direction `h'(0) = 0`, and the passage from the limit
model to a finite perturbation.

### 7c. Reconciliation with `RayDirectionScopeLimit.md`

[RayDirectionScopeLimit.md](RayDirectionScopeLimit.md) (`c6d3a5465b`) reports, by
an independent route, that **confinement and the cone bound are false off the
aligned direction**, with the cone bound failing at four `n = 6` directions with
`sup|t|/T` up to `5.25`. Read at face value that would refute Theorem R. It does
not, and the reason is a sign convention: that file traces
`g = w_c + s e^{-i delta}`, this one traces `g = w_c + s e^{+i delta}`, so its
`delta` is the negative of this file's.

Checked rather than assumed, with this file's own tracer at 40 digits, `alpha`
from the traced asymptote and `T = |t(0^+)|` from the closed form at the saddle —
exactly the protocol its §3 prescribes:

| its `delta` | mapped `delta` here | in this window? | `sup\|t\|/T` branch 1 | branch 2 |
|---|---|---|---|---|
| `1.6008` | `4.682385` | no | `1.0` | **`1.304697`** |
| `2.3862` | `3.896985` | no | `1.0` | **`5.217632`** |
| `2.648` | `3.635185` | no | `1.0` | **`5.249495`** |
| `3.4334` | `2.849785` | no | `1.0` | **`1.359275`** |

Its four failures reproduce here to three digits — `1.30, 5.22, 5.25, 1.36`
against its `1.31, 5.22, 5.25, 1.36` — so the refutation is real and now has two
independent instruments behind it. **And all four lie outside `(0, 2 pi/5)`.**
Read without the sign flip, as a control, every one of the same four numbers
returns ratio `1.0`. Inside the window, sampled at seven interior points,
`sup|t|/T` is `1.0` to `4e-8` on both branches — the residual being the
`sigma = 1e-14` start offset, not a violation.

So the two files agree: **the cone bound holds exactly on one hub-spacing arc and
fails outside it.** Its §2 wall-crossing formulas say the same thing in closed
form — its `s_1` crossing needs `sin(delta) > 0`, which under the sign map is
`sin(delta) < 0` here, disjoint from `[0, pi]`, and its `s_2` crossing needs
`sin(delta + 2 phi_c) < 0`, which under the map is disjoint from `(0, 2 phi_c)`.
Its §2 is therefore the converse half of Proposition W, derived independently.

Two further points from that file, both accepted here. Its §3 observes that the
failures cluster at the *singular* directions, where the descent ray from the hub
value passes through another critical value; mapped into this convention those
are `{4.712, 4.084, 3.456, 2.827}` at `n = 6` and `3 pi/2` at `n = 3`, none of
them in the window — measured at two degrees, not proved in general, and worth
proving. And its §5 corrects this file's receipt for reporting 92 violations in
96 traces; that was the `dps = 20`, `300`-step version, and its diagnosis — the
supremum of `|t|` sits at the hub, which is where `arg g'` is worst conditioned —
is the same one reached here independently and recorded under *Instrument reach*.
The shipped receipt now starts the ray sweep at `sigma = 1e-14` at 40 digits and
passes; the withdrawn "97 directions" line is already gone.

## 8. What this does not settle

* **The `O(rho^2)` remainder** of the cusp law is still unquantified, so nothing
  here gives an explicit neighbourhood of the Fekete family on which
  `min_c L(c) < 2R`. The near-Fekete half is proved *for the limit model*, and the
  passage from that model to a finite perturbation is untouched.
* **The degenerate direction** `h'(0) = 0` is excluded throughout, as in the cusp
  law.
* **The `D`-bounded-away-from-1 half** of
  [HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) is untouched.
* **Nothing here bears on the constant 2**, on finite perturbations, or on the
  two-segment mechanism of
  [TwoSegmentContainmentReduction.md](TwoSegmentContainmentReduction.md).

**Erdős #1041 remains open**, and so does everything outside the limit model.

## Claim boundary

Proved, by ordinary mathematics, at every `n >= 3`: (X1), (X2), (X3), Lemma M
and its Corollary, Lemma S2, Theorem C on both branches, Proposition W,
Lemma S(δ), Lemma W2, the generalisation of Lemma T to an arbitrary descent-ray
direction, and Theorem R — the last by the termwise argument for `n >= 5` and by
a Lipschitz-certified grid for `n = 3, 4`, which is a proof rather than a
measurement. The
inputs from elsewhere are Lemma S ([ConeBoundBranchGeometry.md](ConeBoundBranchGeometry.md) §1),
the Theorem and Proposition of [TurningLengthBound.md](TurningLengthBound.md)
§§2–3, and — for §5 — the bridge (BR) of
[BridgeIdentityProof.md](BridgeIdentityProof.md).

**Not first here, and this is the important row.** The theorem of §4 — monotone
turning on both branches at every degree, hence (★) and its branch-2 mirror — was
proved the same day and landed first in
[MonotoneTurningProof.md](MonotoneTurningProof.md) (`1783f08f31`), by the
quadrant argument described in §0; Lemma S2 is its Lemma 5; and `kappa_n > 0` at
every degree is assembled in [BridgeIdentityProof.md](BridgeIdentityProof.md) §4,
not here. The reduction of the cone hypothesis to (★), and (★) at `n = 3` on
branch 1, are `ConeBoundBranchGeometry.md`'s. The `n = 3` route through the `L^2`
chord-deficit estimate is
[NearFeketeCuspPositivityProof.md](NearFeketeCuspPositivityProof.md)'s and remains
the sharper instrument for `D` itself. What is first here is the `Xi` mechanism as
a route, the `Xi_m` family of §6, and everything in §7 — Proposition W,
Lemma S(δ), Lemma W2 and Theorem R.

Measured, not proved: the tabulated `kappa_n` and `D_i` (trapezoid quadrature on
a geometric mesh in `sigma`, agreeing with the recorded `kappa_3 = 0.6080213113`
to 6 digits); that no *singular* direction — one whose descent ray passes through
another critical value — lies inside the window, checked at `n = 3` and `n = 6`
only; and the reconciliation table of §7c. The generalised Lemma T is checked by quadrature at `n = 3, 4` and
three directions each, residual `3.6e-6` to `9.5e-5` — the tail-truncation bar the
`delta = 0` case already carries, not an error in the identity.

Instrument reach, and it is sharper than it looks. `u = c_n - Im Xi` vanishes at
the hub to order `sigma^{3/2}`, not linearly: `Im(zeta_c^{1-n}) = Im(-1) = 0`, so
`u'` vanishes there as well, and `u' ~ sqrt(sigma)` gives `u ~ sigma^{3/2}`. At a
`1e-20` start that is `u ~ 1e-30`, ten digits above a 40-digit floor and fine —
but at 30 digits it *is* the floor, and the seed sign is then read off roundoff.
Two runs of this receipt were failed by exactly that: the first reported ten
spurious branch failures at `sigma < 1e-24` with `|d t| < 1e-15`, the second two
spurious ray-direction failures whose `u` values were `0.0` and `+-4e-31`. Both
were instrument, not mathematics; the current receipt starts the branch traces at
`sigma = 1e-20` and the ray sweep at `sigma = 1e-14`, both at 40 digits. The proof
itself needs no cutoff.

Not established: novelty. `Xi` is an antiderivative of `g' zeta^{1-n}` and the
argument is one application of the fundamental theorem of calculus, so a
priority search on Newton-flow / lemniscate-trajectory monotone functionals
should precede any claim that it is new.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_cone_bound_all_degrees.py
```
