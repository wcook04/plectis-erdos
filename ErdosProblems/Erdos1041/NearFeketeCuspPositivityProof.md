# Erdős 1041: `kappa_3 > 0` is now a theorem

Status: one proof. 2026-08-23. **This does not prove Erdős #1041**, and it does
not prove the near-Fekete half. It closes the binding instance of the one
inequality [NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) leaves as measured.

## 0. What was open

`NearFeketeCuspLaw.md` §8 lists, under "What this does not settle":

> `kappa_n(phi) > 0` is **measured**, not proved. §6 reduces it to the
> parameter-free inequality `ex_1 + ex_2 < 2`, equivalently `J_n < 2(n-1)`, on
> the fixed model `zeta^n + n zeta`; that inequality is where the remaining work
> is.

and, in §6, names the tool the reduction needs:

> a proof needs the hypotenuse, i.e. a genuine `L^2` estimate on `dY/dX`

together with the reason the obvious `|dX| + |dY|` split fails: at `n = 3` it
returns `2.634` against the true `1.392`.

That `L^2` estimate is supplied below, and at `n = 3` it is strong enough. The
same file records `n = 3` as the binding degree — `(E)` is `J_n < 2(n-1)`, so
the requirement is weakest there — and `phi = 0` as `min_phi kappa_n`.

## 1. The degree-three branch is an explicit algebraic graph

Work in the near-field model `g(zeta) = zeta^3 + 3 zeta`, hub `zeta_c = i`,
critical value `2i`. A descending branch is the `g`-preimage of the ray
`{2i + s : s >= 0}`, so it satisfies `Im g = 2` identically. Writing
`zeta = X + iY`,

```text
Im(zeta^3 + 3 zeta) = 3 X^2 Y - Y^3 + 3 Y = 2,
```

hence `3 X^2 Y = Y^3 - 3Y + 2 = (Y-1)^2 (Y+2)` and

> **Lemma 1.** Both descending branches at `zeta_c = i` lie on the single graph
>
> ```text
> X(Y) = (1 - Y) sqrt( (Y + 2) / (3 Y) ),        Y > 0,
> ```
>
> branch 1 being `Y: 1 -> 0` and branch 2 being `Y: 1 -> oo`. Moreover
>
> ```text
> X'(Y) = - (Y^2 + Y + 1) / ( sqrt(3) Y^{3/2} sqrt(Y + 2) )   <  0.
> ```

*Proof.* The displayed factorisation is exact, and `Re g = X(X^2 - 3Y^2 + 3) >= 0`
selects the two arcs. At `Y = 1` the graph passes through `zeta_c = i`. As
`Y -> 0+`, `X -> +oo` with `Y/X -> 0`, the exit direction `alpha = 0`; as
`Y -> oo`, `X ~ -Y/sqrt(3)`, the exit direction `alpha = 2 pi / 3`. These are the
two exit directions `(G)` of `NearFeketeCuspLaw.md` at `n = 3`. The derivative is
the quotient rule on `(1-Y) phi(Y)` with `phi = sqrt((Y+2)/(3Y))`, using
`phi' = -1/(3 Y^2 phi)` and `3 Y^2 phi^2 = Y(Y+2)`. ∎

This is the whole reason degree three is tractable: `Y^3 - 3Y + 2` factors, so
the branch is a graph over `Y` with a closed-form derivative. No other degree
has it, since `Im(zeta^n) = const` is not solvable for `X` in radicals over `Y`.

**Concurrent independent derivation, and what it adds.** Commit `909de7b7d1`
("the near-field branch in closed algebraic form; n=3 is one real cubic"), landed
by another actor in this directory minutes before this file, records the same
curve as the implicit real cubic `x^3 - 3xy^2 - 3x + 2 = 0`; under
`(x, y) = (Y, X)` that is exactly the equation above. Lemma 1 is therefore not
claimed as first here. What that commit adds is a negative result this proof
depends on: it shows the arclength integrand is **not** a perfect square, so
`kappa_3 = 0.60802134…` is a period-type constant with no elementary closed
form, and concludes that "a proof of `kappa_3 > 0` must be an inequality, not an
evaluation". Lemma 2 is that inequality. The step this file contributes beyond
the shared curve is solving it as a graph with the closed-form `X'`, which is
what makes the two integral bounds of §3 computable.

Verification that the graph is the branch set, rather than merely a curve
through the hub: `Im g - 2` vanishes to `1e-38` at 400 sampled points, and the
closed-form `X'` matches a 20-digit central difference to `1e-19`
([scripts/check_erdos1041_cusp_positivity_n3.py](scripts/check_erdos1041_cusp_positivity_n3.py)).
Integrating `ex = int (dl - dr)` on this graph reproduces the recorded constants
to every digit they were quoted at:

| quantity | from the graph | recorded in `NearFeketeCuspLaw.md` |
|---|---|---|
| `ex_1` | `1.2350942613` | `1.23509426` |
| `ex_2` | `0.156884427` | `0.15688443` |
| `kappa_3` | `0.608021311212` | `0.6080213113` |
| `D_1`, `D_2` | `0.2350942613`, `0.02290983` | `0.235`, `0.023` |

## 2. The `L^2` chord-deficit estimate

> **Lemma 2.** Let a branch leave the hub with exit direction `alpha`, and write
> `eta = e^{-i alpha} zeta = P + iQ`. If `P` is monotone along the branch, then
>
> ```text
> D  <=  (1/2) int (dQ)^2 / dP.
> ```

*Proof.* `P` starts at `Re(e^{-i alpha} zeta_c) = cos(gamma)` and increases to
`+oo`, while `Q` has a finite limit. From `sqrt(a^2 + b^2) <= a + b^2/(2a)` for
`a > 0`,

```text
Lambda  =  int sqrt(dP^2 + dQ^2)  <=  (P_end - cos gamma) + (1/2) int (dQ)^2/dP,
```

and `r = |eta| = sqrt(P^2 + Q^2) >= P`, so
`Lambda - r <= -cos gamma + (1/2) int (dQ)^2/dP`. Adding one and using
`ex = 1 + lim(Lambda - r)` gives `ex <= 1 - cos gamma + (1/2) int (dQ)^2/dP`.
Since `ex = 1 - cos gamma + D` exactly — this is `(BR)` of
`NearFeketeCuspLaw.md` §7 — the claim follows. ∎

The integrand is `(dQ)^2/dP = tan^2(tau - alpha) dP`, so Lemma 2 *is* the `L^2`
estimate on the turning that §6 asks for, and it is exactly the hypotenuse the
`|dX| + |dY|` split throws away.

## 3. Two elementary bounds close it at `n = 3`

**Branch 1** (`alpha = 0`, so `P = X`, `Q = Y`). `P` is monotone because
`X' < 0` while `Y` decreases. Parametrising by `Y`,

```text
I_1 := int (dQ)^2/dP = int_0^1 dY / |X'(Y)|
     = int_0^1  sqrt(3) Y^{3/2} sqrt(Y+2) / (Y^2 + Y + 1)  dY.
```

On `[0,1]`, `sqrt(Y+2) <= sqrt(3)` and `Y^2 + Y + 1 >= 1`, so the integrand is at
most `3 Y^{3/2}` and

```text
I_1  <=  int_0^1 3 Y^{3/2} dY  =  6/5,        hence   D_1 <= 3/5.
```

**Branch 2** (`alpha = 2 pi / 3`). Here `P = -X/2 + sqrt(3) Y/2` and
`Q = -Y/2 - sqrt(3) X/2`, so with `X' = -|X'|`,

```text
dP/dY = ( sqrt(3) + |X'| ) / 2  >=  sqrt(3)/2,
dQ/dY = ( sqrt(3)|X'| - 1 ) / 2.
```

The first gives monotone `P`. For the second, rationalising,

```text
sqrt(3)|X'| - 1 = ( Y^2+Y+1 - sqrt(Y^4 + 2Y^3) ) / ( Y^{3/2} sqrt(Y+2) )
                = N(Y) / ( Y^{3/2} sqrt(Y+2) ),
N(Y) := (3Y^2 + 2Y + 1) / ( Y^2 + Y + 1 + sqrt(Y^4 + 2Y^3) ),
```

using `(Y^2+Y+1)^2 - (Y^4 + 2Y^3) = 3Y^2 + 2Y + 1`.

> **Lemma 3.** `N(Y) <= 3/2` for `Y >= 1`.
>
> *Proof.* The claim is `3Y^2 + Y - 1 <= 3 Y^{3/2} sqrt(Y+2)`; both sides are
> positive for `Y >= 1`, and squaring gives
> `9Y^4 + 6Y^3 - 5Y^2 - 2Y + 1 <= 9Y^4 + 18Y^3`, i.e.
> `12 Y^3 + 5 Y^2 + 2 Y - 1 >= 0`, which holds termwise for `Y >= 1`. ∎

Hence, using `Y + 2 >= 3`,

```text
(dQ/dY)^2 / (dP/dY)  <=  (2/sqrt 3) * (sqrt(3)|X'| - 1)^2 / 4
                     =   N^2 / ( 2 sqrt(3) Y^3 (Y+2) )
                     <=  3 / ( 8 sqrt(3) Y^3 ),
I_2  <=  (3/(8 sqrt 3)) int_1^oo Y^{-3} dY  =  sqrt(3)/16,
```

so `D_2 <= sqrt(3)/32`.

> **Theorem.** For the near-field model `g(zeta) = zeta^3 + 3 zeta`,
>
> ```text
> kappa_3  =  ( cos gamma_1 + cos gamma_2 ) - ( D_1 + D_2 )
>          >=  sqrt(3)/2 - 3/5 - sqrt(3)/32
>          =   15 sqrt(3)/32 - 3/5
>          =   0.211898...  >  0.
> ```
>
> Equivalently `ex_1 + ex_2 <= 2 - 0.2118 < 2`, and `J_3 <= 3.576 < 4`.

The true value is `kappa_3 = 0.6080213`, so the chain recovers 35% of it; the
sharp form of Lemma 2 alone gives `D_1 + D_2 <= (I_1 + I_2)/2 = 0.28583` against
the true `0.25800`, within 11%.

Consequence, in the language of `NearFeketeCuspLaw.md` §4: `z^3 - mu` is a
**strict** local maximum of `min_c L(c) / (2R)` in the aligned direction, with
value exactly 1 and first-order approach in `rho`. That statement is no longer a
measurement.

## 4. Exactly how far this reaches

Proved: Lemmas 1–3 and the Theorem, all by ordinary elementary mathematics —
one factorisation, one quotient rule, one scalar inequality
`sqrt(a^2+b^2) <= a + b^2/(2a)`, and two integral estimates. The only numerics
are confirmations, and the closed-form lower bound needs none.

Not proved, and not to be quoted as proved:

* **Other ray directions.** The model is `zeta^n + n e^{i phi} zeta`, which a
  rotation `zeta -> e^{i phi/(n-1)} zeta` sends to `zeta^n + n zeta` at the cost
  of a global phase `e^{i n phi/(n-1)}` on `g`. That phase is the direction of
  the descent ray, so `phi` survives as the ray angle, and only `phi = 0` is
  treated here. `NearFeketeCuspLaw.md` measures `phi = 0` as `min_phi kappa_3`;
  that minimality is a measurement.
* **Other degrees.** Lemma 1 is special to `n = 3`. Lemma 2 is not — and it does
  not run out of strength. Tracing the branches of `zeta^n + n zeta` by Newton
  continuation in `s`, an implementation sharing nothing with the algebraic
  graph, and comparing `(I_1 + I_2)/2` against `cos gamma_1 + cos gamma_2`:

  | `n` | 3 | 4 | 5 | 6 | 8 | 10 | 12 |
  |---|---|---|---|---|---|---|---|
  | target | `0.8660` | `1.3660` | `1.5981` | `1.7226` | `1.8449` | `1.9010` | `1.9313` |
  | `L^2` bound | `0.2859` | `0.4062` | `0.4382` | `0.4404` | `0.4183` | `0.3894` | `0.3620` |
  | margin | `3.03x` | `3.36x` | `3.65x` | `3.91x` | `4.41x` | `4.88x` | `5.34x` |

  The bound peaks near `n = 6` and then falls while the target rises toward `2`,
  so the margin **grows** with degree and `n = 3` is the tight case for the
  method as well as for the inequality. (At `n = 3` this independent tracer
  returns `0.2859256` against the algebraic graph's `0.2858285` — the difference
  is the geometric mesh, and it is a cross-check on Lemma 1.)

  So the obstruction at general `n` is not that the `L^2` estimate is too weak.
  What is missing is only the explicit evaluation: at `n = 3` the two integrals
  were bounded in closed form because Lemma 1 makes the branch a graph with a
  closed-form derivative, and no such form is available above degree three. A
  general proof needs an explicit majorant for `int tan^2(tau - alpha) dP` on
  `zeta^n + n zeta`, not a better inequality.
* **The `D`-bounded-away-from-1 half.** Untouched, exactly as
  [HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) leaves it.
* **Any neighbourhood size.** The `O(rho^2)` remainder in the cusp law is still
  unquantified, so no explicit `delta` is claimed for which `D >= 1 - delta`
  implies the bound.

**Erdős #1041 remains open.**
