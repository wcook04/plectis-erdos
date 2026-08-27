# Erdős 1041: the turning bound alone gives the length bound — no curvature estimate

Status: one exact identity (Lemma T), one elementary inequality, and an
arithmetic check that is closed-form at every degree. 2026-08-23.
**This does not prove Erdős #1041**, and it does not by itself prove the
near-Fekete half. It removes the obstacle
[NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) §7 names as the remaining one, and
replaces it with a strictly weaker hypothesis that §7 already verifies.

## 0. What was asked

`NearFeketeCuspLaw.md` reduces the near-Fekete half to `kappa_n > 0` on the
fixed model `g(zeta) = zeta^n + n zeta`, in the chord form (BR)/(K), and closes
with:

> What is still missing is only the weight: `Lambda` is infinite, so
> `D <= (1 - cos T) Lambda` is vacuous, and a bound needs the decay of
> `tau - alpha`. … **A bound on `R(t)` is now the entire remaining obstacle.**

It is not. `Lambda` being infinite is not the difficulty, because the divergence
lives entirely in the *longitudinal* direction. The *transverse* displacement of
a branch is finite and **exactly computable**, and that single fact converts the
turning bound straight into a length bound with no radius-of-curvature estimate
anywhere.

## 1. Lemma T — the transverse displacement is exactly `-sin(gamma)`

> **Lemma T.** Let `Gamma` be a descending branch at the hub `zeta_c`, with
> asymptotic direction `alpha` and `gamma = arg(zeta_c) - alpha`. Then
>
> ```text
> int_Gamma sin(tau - alpha) dl  =  -sin(gamma),
> ```
>
> where `tau = arg(d zeta)` is the tangent direction.

*Proof.* `d zeta = e^{i tau} dl`, so
`int e^{i(tau - alpha)} dl = e^{-i alpha} int_Gamma d zeta
 = e^{-i alpha}(zeta_infty - zeta_c)`, and the claim is the imaginary part
together with `Im(e^{-i alpha} zeta) -> 0` along `Gamma`.

For that limit: `alpha` is an `n`-th root direction, so `e^{i n alpha} = 1`.
Put `u = e^{-i alpha} zeta = U + iV`. Taking imaginary parts in
`u^n + n u e^{i alpha} = sigma + (n-1) zeta_c` (whose right side has imaginary
part `c_n := (n-1) sin(pi/(n-1))`, independent of `sigma`) gives

```text
V ( n U^{n-1} + n cos alpha ) = c_n - n U sin alpha + O(V^2),
```

so `V = O(U^{-(n-2)})` when `sin alpha != 0` and `V = O(U^{-(n-1)})` when
`alpha = 0`. Both tend to `0` for `n >= 3`. Hence `Im(e^{-i alpha}zeta_infty) = 0`
and the integral equals `-Im(e^{-i alpha} zeta_c) = -sin(gamma)`. ∎

Geometrically: **a descending branch is asymptotic to the ray through the
origin in direction `alpha`, not merely to a parallel of it.** That is the whole
content, and it is what the chord computation in §7 of the cusp law — which
takes only the real part, `Z - cos gamma + o(1)` — leaves on the table.

*Verification.* `formal_math/probes/erdos1041_turning_length_bound.py` reports
the residual `|int sin(tau-alpha) dl + sin gamma|` falling from `1.4e-5` at
`n = 3` to `8.2e-14` at `n = 10`, matching the predicted `O(Z^{-(n-2)})` tail.

## 2. The bound

Write `t = tau - alpha`.

> **Theorem.** Suppose along `Gamma` the tangent satisfies `|t| <= T` and `t`
> has constant sign. Then
>
> ```text
> D  :=  int_Gamma (1 - cos t) dl  <=  tan(T/2) * |sin gamma|.
> ```

*Proof.* `1 - cos t = 2 sin^2(t/2)` and `|sin t| = 2|sin(t/2)cos(t/2)|`, so
`1 - cos t = |sin t| tan(|t|/2) <= tan(T/2)|sin t|` for `|t| <= T < pi`.
Constant sign gives `int |sin t| dl = |int sin t dl|`, which is `|sin gamma|`
by Lemma T. ∎

No curvature, no `R(t)`, no decay rate. If the turning is monotone the same
statement reads: `D / |sin gamma|` is a weighted average of `tan(|t|/2)` against
the measure `sin|t| dl`, hence at most `tan(T/2)`.

## 3. Consequence: the near-Fekete half, given the cone hypothesis

*The cone hypothesis is no longer a hypothesis (see §6), and (BR) is proved in
[BridgeIdentityProof.md](BridgeIdentityProof.md), so this section's `kappa_n >= C_n - B_n`
is now unconditional at every degree.*

By (BR)/(K) of the cusp law, `kappa_n = (cos gamma_1 + cos gamma_2) - (D_1 + D_2)`
with the exact exit angles and turning totals (G), (T) recorded there:

```text
gamma_1 = pi/(n-1),                 T_1 = (n-2) pi / (2(n-1)),
gamma_2 = -(n-2) pi /(n(n-1)),      T_2 = (n-2)^2 pi / (2 n (n-1)).
```

`T_1` and `T_2` are not measured: they are the initial tangent-versus-asymptote
angles, and follow in closed form from `arg g''(zeta_c) = (n-2)pi/(n-1)` at the
simple hub. So with

```text
B_n := sum_i tan(T_i/2) |sin gamma_i|,       C_n := sum_i cos gamma_i,
```

the Theorem gives `kappa_n >= C_n - B_n`.

> **Proposition.** `C_n > B_n` for every `n >= 3`.

*Superseded 2026-08-24 by a stronger closed form.* With `u = gamma_1`,
`v = -gamma_2`, `u + v = 2 pi/n` and `q = (n-2)/4`,
`(C-B) cos(qu) cos(qv) = cos(pi/n) cos(n(u-v)/4)`, so `C - B > 0` for **every**
`u in (0, 2 pi/n)` — not just at `u = pi/(n-1)` — and the `n = 3, 4` cases below
stop needing their own arithmetic. See
[PhaseDependenceOfKappa.md](PhaseDependenceOfKappa.md) §6. The proof below is kept
as the record of how the bound was first cleared.

*Proof.* For `n >= 5` the crude bound `tan(T_i/2) <= tan(pi/4) = 1` already
suffices, i.e. it is enough that the tangent stays in a half-plane. The claim
`sin gamma_1 + |sin gamma_2| < cos gamma_1 + cos gamma_2` rearranges to
`sin(gamma_1 - pi/4) < sin(pi/4 - |gamma_2|)`. Now `|gamma_2| < gamma_1` always,
since `(n-2)/n < 1`, and `n >= 5` gives `gamma_1 = pi/(n-1) <= pi/4`. So the
left side is `<= 0` and the right side is `> 0`.

`n = 4`: `B_4 = tan(pi/6)sin(pi/3) + tan(pi/12)sin(pi/6) = 1/2 + (2-sqrt3)/2
 = (3-sqrt3)/2` and `C_4 = (1+sqrt3)/2`; `3 - sqrt3 < 1 + sqrt3` iff `1 < sqrt3`.

`n = 3`: `B_3 = tan(pi/8) + tan(pi/24)/2 = (sqrt2 - 1) + (sqrt6-sqrt3+sqrt2-2)/2`
and `C_3 = sqrt3/2`; `2 B_3 < 2 C_3` is `3 sqrt2 + sqrt6 - 4 < 2 sqrt3`, i.e.
`2.6921… < 3.4641…`. ∎

Measured, for comparison (`--max-n 10`):

| n | `kappa_n` measured | `B_n` | `C_n` | `C_n - B_n` |
|---|---|---|---|---|
| 3 | 0.607971 | 0.4800398 | 0.8660254 | **0.385986** |
| 4 | 1.030078 | 0.6339746 | 1.3660254 | 0.732051 |
| 5 | 1.258543 | 0.6399596 | 1.5981133 | 0.958154 |
| 6 | 1.398880 | 0.6081418 | 1.7225625 | 1.114421 |
| 8 | 1.562200 | 0.5285495 | 1.8448522 | 1.316303 |
| 10 | 1.654739 | 0.4592263 | 1.9009543 | 1.441728 |

The binding degree is `n = 3`, exactly as the cusp law's `J_n` form predicts,
and the bound clears it by 45%.

## 4. What the hypothesis reduces to

Because `d zeta / d sigma = 1/g'`, the tangent angle is exactly

```text
t  =  -arg( e^{i alpha} ( zeta^{n-1} + 1 ) )                            (Q)
```

— an explicit function of position, with no integration. So:

* **constant sign of `t`** and
* **`|t| <= T`**

are pointwise statements about the level set `Im g = c_n`. Two reductions.

**(i) Constant sign.** `t = -Im log(zeta^{n-1}+1)` is harmonic off the critical
points. Under the conformal map `P = zeta^{n-1}`, the sector
`S = {0 < arg zeta < pi/(n-1)}` goes to the upper half-plane, `zeta_c` goes to
`-1`, and

```text
|t|  =  arg(P + 1)  =  pi * omega( P, (-inf,-1), H ),
```

the harmonic measure of `(-inf,-1)`. So `0 <= |t| <= pi` free, and *provided the
branch stays in `S`* — verified for branch 1 at every degree tested — `P` lies
in the closed upper half-plane and `t <= 0` throughout. Constant sign holds.

**(ii) The cone.** With `mu := e^{i pi/(2(n-1))} = sqrt(zeta_c)`, the branch-1
cone bound `arg(P+1) <= T_1` is *equivalent* to

```text
Re( mu ( zeta^{n-1} + 1 ) )  >=  0                                       (C1)
```

since `T_1 = pi/2 - pi/(2(n-1))`. In polar coordinates `zeta = r e^{i phi}`,
using `G = sigma - (n-1)(zeta - zeta_c)`, (C1) is

```text
sigma cos(phi_c/2 - phi) + (n-1)[ cos(3 phi_c/2 - phi) - r cos(phi_c/2) ] >= 0,
```

`phi_c = pi/(n-1)`, on the curve `r^n sin(n phi) + n r sin phi = (n-1) sin phi_c`.
At the hub (`r=1`, `phi=phi_c`, `sigma=0`) both sides vanish: the bound is sharp
there and, measured, nowhere else.

*Measured.* `sup |arg Q|` equals `T` to nine decimals at every degree `3..14` on
both branches, attained only at the hub, and `min Re Q/|Q| = cos T` exactly.
`min Re(mu(P+1))` along branch 1 is `0` to `4e-9`.

**(C1) is not a sector fact.** It fails badly on `S` off the level set — at
`n = 5`, `r = 50` the left side reaches `-6.2e6`. Any proof must use the level
set `Im g = c_n`, not just the sector.

## 4a. Scope: everything here lives on the limit model

`ade3b6ac08` bounds (T) to the `eps -> 0` near field and warns it must not be
quoted as a fact about real polynomials, since `CriticalBudgetLab.md` refutes the
turning route globally (`the supremum is +infinity since alpha passes pi`). That
boundary applies verbatim here and costs nothing: **every object in this note --
`Gamma`, `tau`, `alpha`, `gamma`, `T`, `D`, Lemma T, (Q), (C1) -- is defined on
the fixed model `g(zeta) = zeta^n + n zeta`, one polynomial per degree.** Lemma
T's asymptotics use `g` and only `g`. Nothing here is a statement about a
perturbed polynomial, and the leading-order law
`L(c) = 2R - kappa_n rho + O(rho^2)` is what carries it back. Whether monotone
turning survives at finite perturbation is open, and this note does not need it.

## 5. Net effect

The near-Fekete half now rests on (i) + (ii): the branch stays in its sector,
and the tangent stays in the cone of half-angle `T` — the statement
`NearFeketeCuspLaw.md` §7 records as (T) and verifies to `1.7e-27`. **Both are
now proved** ([MonotoneTurningProof.md](MonotoneTurningProof.md), 2026-08-24), so
on the limit model the half rests on the bridge (BR) alone. It no longer
rests on any estimate for the radius of curvature `R(t)`, on the decay of
`tau - alpha`, or on a weighted `L^2` turning integral. For `n >= 5` even the
sharp cone is unnecessary: the half-plane statement `Re(e^{i alpha}g'(zeta)) > 0`,
i.e. the branch is a graph over its own asymptote, is enough.

## 6. What this does not settle

*The first two bullets were closed on 2026-08-24 by
[MonotoneTurningProof.md](MonotoneTurningProof.md); kept as written so the order
of discovery stays legible.*

* ~~(C1) is **not proved**.~~ Proved at every degree, on both branches, together
  with the branch-2 analogue `Re(mu' (zeta^{n-1}+1)) <= 0`. It is still a sharp
  pointwise inequality on one explicit algebraic curve per degree with equality
  at one point; what changed is that the proof never estimates the curve, only
  the two zero sets it must not cross.
* ~~That branch 1 stays in `S` is verified, not proved; branch 2's sign needs its
  own argument.~~ Branch 1's sector is Lemma S of
  [ConeBoundBranchGeometry.md](ConeBoundBranchGeometry.md); branch 2's is Lemma 5
  of the proof note, and its sign argument is the reverse quadrant.
* The `D`-bounded-away-from-1 half is untouched, as is the `O(rho^2)` remainder,
  the degenerate direction `h'(0) = 0`, and everything in
  [CriticalTreeLengthCharge.md](CriticalTreeLengthCharge.md).
* Nothing here bears on the constant 2.

**Erdős #1041 remains open.**

## Claim boundary

Proved, by ordinary mathematics: Lemma T (including the asymptotic-ray limit),
the Theorem of §2, the identity (Q), the equivalence of the cone bound with
(C1), the harmonic-measure identity `|t| = pi omega(P,(-inf,-1),H)`, and the
Proposition of §3 in closed form at every `n >= 3`.

Also proved, 2026-08-24, in [MonotoneTurningProof.md](MonotoneTurningProof.md):
(C1) and its branch-2 analogue, monotone turning on both branches, and that each
branch stays in its sector — i.e. hypotheses (i) and (ii) of §5.

Measured, not proved (float64 root-continuation; the identity residual is the
honest error bar and runs `1.4e-5` at `n=3` to `8.2e-14` at `n=10`): the values
of `D_i` and `kappa_n`, and the sharpness of `sup|arg Q| = T`.

Not established: any novelty claim — Lemma T is an elementary
asymptotic computation and the `tan(T/2)` inequality is standard, so both should
be checked against the literature on lemniscate arclength and Newton-flow
trajectories before either is described as new.

## Replay

```sh
./repo-python formal_math/probes/erdos1041_turning_length_bound.py --max-n 10
```
