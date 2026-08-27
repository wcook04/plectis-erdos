# Erdős 1041: the near-field cusp is one polynomial at every degree

Status: six ordinary propositions plus one guarded measurement, reconciled with
the source-current near-field theorem stack on 2026-08-24. **This does not prove
Erdős #1041.** This note supplies an alternate polynomial normalisation and
radial-deficit identities. It does not own the later all-degree, all-direction
proof of `kappa_n(phi) > 0` on the limit model; that proof is assembled in
[`MonotoneTurningProof.md`](MonotoneTurningProof.md),
[`BridgeIdentityProof.md`](BridgeIdentityProof.md), and
[`ConeBoundMonotoneFunctional.md`](ConeBoundMonotoneFunctional.md).

Receipt: [`scripts/check_erdos1041_near_field_cusp_polynomial.py`](scripts/check_erdos1041_near_field_cusp_polynomial.py),
checker commit `700b90e473`, gates G1--G12. The checker is finite numerical and
symbolic evidence; the all-degree theorem remains ordinary mathematics in the
three sources below.

## 0. Provenance, first

`kappa_n > 0` at every degree and every ray direction is **already a theorem**
in this directory, landed 2026-08-24 in
[MonotoneTurningProof.md](MonotoneTurningProof.md) (monotone turning),
[BridgeIdentityProof.md](BridgeIdentityProof.md) (the bridge, and the assembly),
and [ConeBoundMonotoneFunctional.md](ConeBoundMonotoneFunctional.md)
(Theorem R, all directions). None of that is this note's.

This note was written without opening those three files: `research_packet.json`
does not carry them among its 51 exact results, and the session read the packet
instead of the directory. The consequence is that §5 re-derives `C_n - B_n` and
§4.5's sign condition restates their monotone-turning theorem. Both are recorded
as second routes, with attribution, not as results. The AGENTS.md warning in this
directory — *"List the `.md` files in this directory rather than following only
the cross-references"* — describes exactly what went wrong, and it went wrong
again here.

What is not a duplicate, as far as the files above show: the polynomial normal
form `Ghat` of §1, the geometric-mean form of `omega` in Proposition 4, the
large-degree limit `Ghat(1+x/n) -> e^x - x - 1`, and the two instrument defects
described in §6. The corrected diagnostics are now pinned by gates G8--G9 of the
landed checker.

## 0a. What the n = 3 route could not do

[NearFeketeCuspPositivityProof.md](NearFeketeCuspPositivityProof.md) proves
`kappa_3 > 0` and states exactly where the method stops:

> Lemma 1 is special to `n = 3`, since `Im(zeta^n) = const` is not solvable for
> `X` in radicals over `Y`.

and

> A general proof needs an explicit majorant for `int tan^2(tau - alpha) dP` on
> `zeta^n + n zeta`, not a better inequality.

Its own table records the `L^2` bound running `3.03x` to `5.34x` below target
for `n = 3 … 12`, so the obstruction was never the strength of the estimate —
it was that above degree three there was no closed form to estimate *on*.

The normal form below is one such closed form, available at every degree. It is
a change of coordinates, not a theorem, and the theorem it would have supported
was proved independently the same day by the files named in section 0.

## 1. The reduction (exact)

`NearFeketeCuspLaw.md` §4 gives the near field of `f = z^n - m + eps h` as

```text
g_phi(zeta) = zeta^n + n e^{i phi} zeta,     phi = arg h'(0),
```

with hubs `zeta_c^{n-1} = -e^{i phi}` (so `|zeta_c| = 1`), critical values
`(n-1) e^{i phi} zeta_c`, and the descent branches the `g_phi`-preimages of the
ray leaving the critical value in the direction of the far-field value `+m`.

> **Proposition 1 (hub normalisation).** Put `zeta = zeta_c w`. Then
>
> ```text
> g_phi(zeta_c w) - g_phi(zeta_c)  =  - e^{i phi} zeta_c * Ghat(w),
> Ghat(w) := w^n - n w + (n-1) = (w-1)^2 q(w),   q(w) = sum_{j=0}^{n-2}(n-1-j) w^j.
> ```

*Proof.* `zeta_c^n = zeta_c · zeta_c^{n-1} = -e^{i phi} zeta_c`, so

```text
g_phi(zeta_c w) - g_phi(zeta_c)
  = zeta_c^n w^n + n e^{i phi} zeta_c w - (n-1) e^{i phi} zeta_c
  = -e^{i phi} zeta_c ( w^n - n w + (n-1) ).
```

The factorisation is `w^n - 1 - n(w-1) = (w-1) sum_{k=0}^{n-1}(w^k - 1)`,
and each `w^k - 1` carries another factor `w-1`; `q(1) = n(n-1)/2`. ∎

Three consequences, all immediate and all degree-free.

* **The hub is `w = 1`, a double root of `Ghat`.** The two descent branches
  leave it in the opposite directions the simple saddle demands.
* **`phi` survives only as the direction of one ray.** Normalising `arg m = 0`,
  the descent condition becomes `Ghat(w) in rho e^{-i n nu}`, `rho >= 0`, with
  `nu = arg zeta_c` — **the angular position of the hub**, nothing else. The
  normalized polynomial no longer depends on `phi` or the perturbation; it
  remains the explicit degree-indexed family `Ghat_n(w) = w^n - nw + (n-1)`.
* **The exit directions are the far-field root directions.** `arg w -> -nu +
  2 pi k/n`, i.e. `arg zeta -> 2 pi k/n`.

Degree three is now not special. `Ghat = w^3 - 3w + 2 = (w-1)^2(w+2)`, and
`NearFeketeCuspPositivityProof.md`'s cubic `x^3 - 3xy^2 - 3x + 2 = 0` is the
real form of `Im(e^{3 i nu} Ghat) = 0` at `nu = pi/2`.

## 2. The excess is a radial deficit (exact)

Write `v := Ghat(w)^{1/n}`, so `v` runs along a straight ray `s e^{i alpha}`,
`s >= 0`, and `w = w(v)` with `w(0) = 1`. Then `w'(v) = v^{n-1}/(w^{n-1}-1)`.

> **Proposition 2.** With `omega(s) := |dw/dv|`, the renormalised excess is
>
> ```text
> ex = 1 + int_0^oo ( omega(s) - 1 ) ds  =  int_Gamma ( |dw| - d|w| ) ,
> ```
>
> a radial deficit; and `kappa_n = 2 - ex_+ - ex_-`. Equivalently
>
> ```text
> kappa_n  =  lim_{S -> oo} [ |w_+(S)| + |w_-(S)| - length(Gamma up to S) ] :
> ```
>
> `kappa_n > 0` says exactly that **the descent curve joining the two far
> endpoints is shorter than the broken line through the origin**.

That is the original problem in miniature, which is why the constant is `2`.

> **Proposition 3 (the identity).** Along either branch,
>
> ```text
> ex = 1 - cos(alpha) + int_0^oo (Im w')^2 / ( |w'| + Re w' ) ds .
> ```

*Proof.* `|w'| - Re w' = (Im w')^2/(|w'| + Re w')` identically, and
`int_0^oo (Re w' - 1) ds = Re[ e^{-i alpha}(h(oo) - h(0)) ] = -cos alpha` for
`h(v) := w(v) - v`, since `h(0) = 1` and `h(v) = O(v^{2-n}) -> 0`. ∎

This is an **equality**, not an estimate, and it needs no monotonicity
hypothesis; Lemma 2 of `NearFeketeCuspPositivityProof.md` is its Cauchy–Schwarz
consequence when `Re w' > 0` (which does hold here — checked on every branch
below, minimum `+4.7e-3` at `n = 3` and positive at every degree tested).

> **Proposition 4 (why the extremal family is the constant function).**
> `omega = (B/A)^{n-1}` where `B` is the geometric mean of the distances from
> `w` to the `n` roots of `Ghat` and `A` the geometric mean of the distances to
> its `n-1` critical points.

*Proof.* `|Ghat| = B^n` and `|Ghat'| = n A^{n-1}`, and
`omega = n|Ghat|^{(n-1)/n}/|Ghat'|`. ∎

So `omega ≡ 1` exactly for `Ghat = w^n`, which is the descent of `z^n - lambda`:
the equality family is the *constant* integrand, not an extremal curve. The same
normalisation works for the true polynomial — with `F(z) := f(c) - f(z)` and
`zeta := F(z)^{1/n}`, the strong completion `L(c) <= 2|f(c)|^{1/n}` is exactly
"`n|F|^{(n-1)/n}/|F'|` averages to at most one over the two rays", and it is
identically one on both recorded equality families.

## 3. The far-field target direction, in closed form (exact)

`NearFeketeCuspLaw.md` records an older finite sweep and
`NearFeketeCuspPositivityProof.md` §4 lists a numeric far-field "target" row.
Proposition 1 makes the target row arithmetic. The later reconciliation in
`ConeBoundMonotoneFunctional.md` and `RayDirectionScopeLimit.md` withdraws the
inference that `phi=0` is `argmin_phi kappa_n`; nothing below reinstates it.

The hubs are `zeta_c = exp(i(phi + pi + 2 pi k)/(n-1))`, `k = 0 … n-2`, so
`nu_k = arg zeta_c` are spaced by `2 pi/(n-1)`, hence by

```text
2 pi/(n-1) - 2 pi/n = 2 pi / (n(n-1))     (mod 2 pi/n),
```

and the `n-1` of them **tile `[0, 2 pi/n)` exactly**. The two branches of a hub
exit at the two root directions straddling `nu`, so with `psi := nu mod 2 pi/n`,

```text
T(psi) := cos gamma_1 + cos gamma_2 = cos psi + cos(2 pi/n - psi)
        = 2 cos(pi/n) cos(psi - pi/n),
```

peaking at `psi = pi/n`. Since `min_c L(c) = 2R - rho max_k kappa(nu_k)`, the
worst ray direction is the one whose tiling straddles `pi/n` symmetrically, at
distance `pi/(n(n-1))`:

> **Proposition 5.** `min over phi of max over hubs of T = 2 cos(pi/n) cos(pi/(n(n-1)))`,
> attained at `phi = 0` for this far-field target `T`.

| `n` | 3 | 4 | 5 | 6 | 8 | 10 | 12 |
|---|---|---|---|---|---|---|---|
| closed form | `0.86603` | `1.36603` | `1.59811` | `1.72256` | `1.84485` | `1.90095` | `1.93130` |
| recorded row | `0.8660` | `1.3660` | `1.5981` | `1.7226` | `1.8449` | `1.9010` | `1.9313` |

Every entry of the recorded target row is reproduced. Note `2 pi/n - nu* =
pi/(n-1)`, so the binding direction for `T` is `phi = 0` at every degree. This
does **not** identify an extremum of `kappa_n`; the later ray-direction analysis
shows why that stronger reading of the old sweep is unsafe.

## 4. What the model measures

At the far-field target direction `nu* = pi/n - pi/(n(n-1))`, exit directions
`alpha_+ = -pi(n-2)/(n(n-1))` and `alpha_- = pi/(n-1)` (measured, not assumed;
gate G4):

| `n` | `ex_+` | `ex_-` | `kappa_n` | recorded | `max abs(dw/dv)` | two-resolution spread |
|---|---|---|---|---|---|---|
| 3 | `0.156884` | `1.235094` | `0.6080215` | `0.60802134` | `1.2003` | `0` |
| 4 | `0.193120` | `0.776761` | `1.0301197` | `1.0301197` | `1.2167` | `0` |
| 5 | `0.189649` | `0.551773` | `1.2585784` | `1.2585783` | `1.2168` | `6.7e-16` |
| 6 | `0.177401` | `0.423687` | `1.3989124` | `1.3989124` | `1.2143` | `0` |
| 7 | `0.163939` | `0.342312` | `1.4937486` | — | `1.2115` | `0` |
| 8 | `0.151296` | `0.286475` | `1.5622287` | — | `1.2089` | `2.2e-16` |
| 10 | `0.129933` | `0.215301` | `1.6547662` | — | `1.2048` | `7.8e-15` |
| 12 | `0.113298` | `0.172101` | `1.7146011` | — | `1.2018` | `2.1e-12` |

All four recorded `kappa` constants are reproduced, and so are the two recorded
per-branch excesses at `n = 3` (`1.2350942612` against `1.2350942613`,
`0.1568842833` against `0.156884427`). The spread is the two-resolution guard
required by `negative_results` entry 43; it is at least `10^11` below the
claimed margin at every row, so these are not values whose grid error is the
size of the claim.

Three observations that a proof should use.

* **The measured binding-direction values of `kappa_n` increase with degree**
  over the displayed finite range. This is calibration, not a monotonicity
  theorem. Positivity on the full limit model is proved elsewhere by the
  source-current turning/bridge/window stack cited at the top of this note.
* **`|dw/dv| <= 1.2168` at every degree tested**, occurring at `|w| ≈ 1.1 … 1.37`.
  `omega` blows up only at the other critical points `eta_k = exp(2 pi i k/(n-1))`,
  `k != 0`, so a distance bound from `Gamma` to those points is the whole of the
  pointwise control. Gate G7 records that distance (`1.63` at `n = 3` down to
  `0.38` at `n = 12`).
* **`ex_+ + ex_- ≈ 3.4/n`.** The deficit lives at scale `|w - 1| ~ 1/n`, and
  `Ghat(1 + x/n) = (1 + x/n)^n - x - 1 -> e^x - x - 1`, so the large-degree
  model is the transcendental `E(x) = e^x - x - 1` with the branch
  `E(x) in R_{<0}` leaving `x = 0` along the imaginary axis.

## 4.5. An exact conditional reduction, and how the current corpus discharges it

The polynomial normal form gives two further identities. They are elementary,
but they must be visible because they show how a turning-sign theorem becomes a
metric bound.

> **Proposition 6 (imaginary variation and angular deficit).** Along a branch
> `v=s e^{i alpha}`, with `w'=dw/dv` and `beta=arg w'`,
>
> ```text
> int_0^oo Im(w') ds = sin(alpha),
> D := ex-(1-cos(alpha))
>    = int_0^oo |tan(beta/2)| |Im(w')| ds.
> ```
>
> Consequently, if `Im(w')` has one sign along the branch and `beta` has a
> continuous choice with finite `sup_Gamma |tan(beta/2)|`, then
>
> ```text
> D <= |sin(alpha)| sup_Gamma |tan(beta/2)|.
> ```

*Proof.* Put `h(v)=w(v)-v`. As in Proposition 3, `h(0)=1`, `h(v)->0`, and
`d(e^{-i alpha}h)/ds=h'(v)=w'-1`. Hence
`int_0^oo(1-w')ds=e^{-i alpha}`; taking imaginary parts gives the first
identity. Pointwise away from the negative real axis,
`|w'|-Re(w')=|w'|(1-cos beta)=|tan(beta/2)| |Im(w')|`; the improper endpoint
value is understood by continuity. This gives the second identity under the
stated finite-angle condition.
If `Im(w')` has one sign, the first identity yields
`int|Im(w')|ds=|sin(alpha)|`, and taking the supremum proves the bound. ∎

The corresponding proof route makes `Im(w')` single-signed and places the
maximum of `|beta|` at the hub by expressing monotone turning through the sign of

```text
S(w) := Ghat(w) Ghat''(w) / Ghat'(w)^2.
```

That sign is measured by this note's gate G10 but is **not proved by the
checker**. It is no longer an open corpus-level gate: `MonotoneTurningProof.md`
proves monotone turning on both aligned branches at every degree,
`BridgeIdentityProof.md` proves the bridge to `kappa_n`, and
`ConeBoundMonotoneFunctional.md` selects the unique admissible hub and proves the
all-direction window theorem. Proposition 6 is therefore a proved alternate
metric interface to that source-current theorem stack, not an independent proof
of its conclusion and not an open-problem statement.

## 5. The bound this route produces is the corpus's `C_n - B_n`

Carrying Proposition 6 through with `sup|tan(beta/2)|` attained at the hub, where
`beta(0) = ((n-2)/2) alpha` exactly, gives the closed-form lower bound

```text
kappa_n >= Phi(n, psi) := sum_pm [ cos a_pm - sin|a_pm| tan( (n-2)|a_pm| / 4 ) ],
a_+ = psi,   a_- = 2 pi/n - psi .
```

**This is not a new bound.** With `a_- = pi/(n-1)` and `a_+ = pi(n-2)/(n(n-1))`
the two hub angles are exactly `T_1 = (n-2)pi/(2(n-1))` and
`T_2 = (n-2)^2 pi/(2n(n-1))` of [TurningLengthBound.md](TurningLengthBound.md),
`Phi` is exactly its `C_n - B_n`, and the agreement is numerical as well as
symbolic:

| `n` | 3 | 4 | 5 | 6 | 8 | 10 |
|---|---|---|---|---|---|---|
| `Phi(n)` here | `0.3859856` | `0.7320508` | `0.9581537` | `1.1144207` | `1.3163027` | `1.4417280` |
| `C_n - B_n` recorded | `0.3859856` | `0.7320508` | `0.9581537` | `1.1144207` | `1.3163027` | `1.4417280` |

Likewise the sign condition this route needs — that
`Im( Ghat Ghat''/Ghat'^2 )` keeps the sign of `alpha` along the branch, so that
`Im w'` is single-signed and `|beta|` peaks at the hub — is the same statement as
monotone turning with constant sign, which
[MonotoneTurningProof.md](MonotoneTurningProof.md) proves at every degree by the
quadrant argument, and which
[ConeBoundMonotoneFunctional.md](ConeBoundMonotoneFunctional.md) proves again by
the `Xi` functional and extends to every ray direction (Theorem R). Proposition 6
above is the `s`-parametrised form of the identity `(*)` that
[BridgeIdentityProof.md](BridgeIdentityProof.md) §1 proves as the bridge (BR).

So the whole of §5 is a **second derivation of a landed theorem**, reached in
this session without opening those three files. It is recorded because a second
independent route to `C_n - B_n` is worth having and because the polynomial
normal form makes the route short, not because anything here is first.

## 6. Claim boundary

**Proved here, by ordinary mathematics, and not found in the sibling files:**
Proposition 1 (the `Ghat(w) = w^n - nw + (n-1)` normal form, hub at `w = 1`);
Proposition 2 (the radial-deficit reading, `kappa_n > 0` iff the descent curve
beats the broken line through the origin); Proposition 4
(`omega = (root-GM / critical-GM)^{n-1}`, so the extremal family is the constant
integrand); the closed form `2 cos(pi/n) cos(pi/(n(n-1)))` for the recorded
target row; and the large-degree limit `Ghat(1+x/n) -> e^x - x - 1`.

**Proved here but NOT first:** Proposition 3 and Proposition 6 (these are the
bridge `(*)` of [BridgeIdentityProof.md](BridgeIdentityProof.md) §1 in a
different parametrisation), and the bound `Phi = C_n - B_n` of §5, which is
[TurningLengthBound.md](TurningLengthBound.md) §§2-3.

**Withdrawn.** An earlier revision of this note read Proposition 5 as showing
`phi = 0` is `argmin_phi kappa_n`. It is not. Proposition 5 is a statement about
the far-field target `T` only; `RayDirectionScopeLimit.md` §4 shows the recorded
sweep samples a singular direction at its maximum, so that reading is unsafe and
is retracted. The commit message that landed this note's first revision claims it
"removes the n=3-only obstruction"; that claim is superseded — the obstruction
was removed the same day by the three files in section 0.

**Two instrument defects caught and pinned by gates G8--G9**, both of the class
`negative_results` entry 43 names. These are instrument diagnostics, not
mathematical proof.

1. A naive `sup |beta|` reads **exactly `pi/2` at every degree** — a clean-looking
   constant that is pure underflow: near the hub `|w'|` falls to `1e-54` at
   `n = 10` and `Re w'` cancels to `1e-69`. The sup is now taken only where
   `|w - 1| > 1e-7`, with `beta(0)` supplied analytically.
2. Reading the ray direction off the traced endpoint instead of its closed form
   injects an error `~ S^{1-n}`, which is the **size of `Im w'` itself** in the
   far field. That manufactured a resolution-independent sign flip in `Im w'`
   over the last 30% of the trace at `n = 3, 4, 5` — stable under mesh
   refinement, and therefore easy to mistake for a real feature. `alpha` is now
   exact and the endpoint angle is only a convergence check.

**Not touched:** the `O(rho^2)` remainder, so no explicit neighbourhood size; the
`D`-away-from-1 half of [HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md);
finite perturbations; and the constant 2.

**Erdős #1041 remains open.**
