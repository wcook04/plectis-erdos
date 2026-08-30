# Erdős #1041: an explicit finite near-Fekete remainder

Status: exact factorisation, origin-anchored quantitative logarithmic expansion,
ordinary proof, Lean-checked analytic kernels, and a deterministic
numerical replay. 2026-08-25. **This is not the unrestricted solution of Erdős
#1041.** It replaces the informal `O(eta^2)` in the current Form A-cut frontier
by a usable inequality and isolates the remaining multiscale selection problem.

## 1. Exact coordinates

Let

```text
omega = exp(2 pi i/n),        a_k = omega^k (1+e_k),
eta = max_k |e_k|,            f(z) = product_k (z-a_k),
E_m = sum_k e_k omega^(-km).
```

For every `k`, direct algebra gives

```text
z-a_k = (z-omega^k) (1 + e_k/(1-z omega^(-k))).             (F1)
```

Consequently, whenever `|z|<1-eta`,

```text
f(z) = (z^n-1) product_k (1+w_k(z)),
w_k(z) = e_k/(1-z omega^(-k)).                              (F2)
```

This identity has no asymptotic error. The condition `|z|<1-eta` makes every
denominator and every factor nonzero.

## 2. The logarithmic error, with constants

For `|w|<1`, the Taylor tail of the principal complex logarithm satisfies

```text
| log|1+w| - Re w | <= |w|^2 / (2(1-|w|)).                 (L)
```

Indeed, this is the real-part consequence of

```text
|Log(1+w)-w| <= |w|^2 / (2(1-|w|)).
```

Fix `0<=r<1` and suppose `eta<1-r`. Put `alpha=eta/(1-r)`. For
`|z|<=r`, (F2), (L), and `|w_k(z)|<=alpha` give

```text
| log|f(z)| - log|1-z^n| - Re sum_k w_k(z) |
    <= n alpha^2 / (2(1-alpha)).                            (R1)
```

The two remaining expansions are geometric series. First,

```text
sum_k w_k(z) = sum_{m>=0} E_m z^m,
```

and `|E_m|<=n eta`, so for every integer `M>=0`,

```text
| sum_{m>M} E_m z^m |
    <= n eta r^(M+1)/(1-r).                                (R2)
```

Second, apply (L) to `w=-z^n`:

```text
| log|1-z^n| + Re(z^n) |
    <= r^(2n)/(2(1-r^n)).                                  (R3)
```

Combining (R1)--(R3) proves the quantitative expansion theorem.

> **Theorem (finite near-Fekete expansion).** If `0<=r<1`, `eta<1-r`,
> `|z|<=r`, and `M>=0`, then
>
> ```text
> | log|f(z)| - [sum_{m=0}^M Re(E_m z^m) - Re(z^n)] | <= B_M(r,eta),
> ```
>
> where
>
> ```text
> B_M(r,eta)
>   = n eta r^(M+1)/(1-r)
>     + n alpha^2/(2(1-alpha))
>     + r^(2n)/(2(1-r^n)),       alpha=eta/(1-r).           (B)
> ```

In the especially convenient collar `eta<=(1-r)/2`, the middle term is at
most `n alpha^2`. No unnamed constant remains. The next section gives a
strictly stronger origin-anchored form in which this quadratic error acquires
an additional factor `r`.

## 3. The origin-anchored theorem: the missing factor of `|z|`

The unanchored expansion throws away useful information at the origin. Since

```text
log|f(0)| = sum_k log|1+e_k| < 0,
```

keep this constant exact. Put

```text
Phi(w) = log|1+w| - Re w.
```

On `|v|,|w|<=alpha<1`, differentiation or the logarithmic power series gives

```text
|Phi(w)-Phi(v)| <= alpha/(1-alpha) |w-v|.                  (A1)
```

For `w_k(z)=e_k/(1-z omega^(-k))`,

```text
|w_k(z)-e_k| <= eta r/(1-r).
```

Therefore the nonlinear error **after anchoring at zero** obeys

```text
|R_anchor(z)|
  <= n eta^2 r / ((1-r)^2 (1-alpha)),     alpha=eta/(1-r). (A2)
```

This is `O(eta^2 |z|)`, not merely `O(eta^2)`.

There is also no infinite Fourier tail. Since `E_(m+n)=E_m`, geometric
resummation gives exactly

```text
sum_k (w_k(z)-e_k)
  = [sum_(m=1)^(n-1) E_m z^m + E_0 z^n] / (1-z^n).        (A3)
```

Combining (F2), (A1)--(A3) proves the stronger theorem.

> **Theorem (origin-anchored finite-mode expansion).** Under `0<=r<1`,
> `eta<1-r`, and `|z|<=r`, let
>
> ```text
> P(z) = [sum_(m=1)^(n-1) E_m z^m + E_0 z^n] / (1-z^n).
> ```
>
> Then
>
> ```text
> |log|f(z)| - [log|f(0)| + log|1-z^n| + Re P(z)]|
>   <= n eta^2 r / ((1-r)^2 (1-alpha)).                   (A)
> ```

This is the useful stability theorem. It retains the strictly negative exact
constant `log|f(0)|`, turns the nonlinear error into a term vanishing at the
hub, and represents every transition regime by one finite numerator.

**The nonlinear error is an exact coefficient in other coordinates.**
[ReciprocalNewtonExpansion.md](ReciprocalNewtonExpansion.md) Theorem R3 shows
that `-p_m/m = E_m - ((m+1)/2) E_m^(2) + ...` for `1 <= m <= n-1`, where
`p_m = sum_j a_j^(-m)`, so `R_anchor` is term by term the second and higher
terms of the exact reciprocal coefficient. That form is controlled in `C^2` and
can be truncated past any prescribed contact order; this one keeps the
degree-`n` baseline in closed form with no infinite tail. Use this one when the
baseline must be exhibited exactly, and that one when the contact order binds —
which is what a tied face or a face switch produces.

The disk constraint supplies another exact piece of slack. From
`|1+e_k|<=1`,

```text
2 Re(e_k) + |e_k|^2 <= 0,
-Re E_0 >= (1/2) sum_k |e_k|^2.                            (D)
```

Thus the radial deficit controls the entire quadratic perturbation energy.
The Lean module proves both (A1) and (D), as well as the finite geometric
identity underlying (A3).

## 4. The exact stability implication

Write

```text
Q_M(z) = sum_{m=0}^M Re(E_m z^m) - Re(z^n).
```

Either quantitative theorem immediately gives the certificate

```text
Q_M(z) + B_M(r,eta) < 0   ==>   log|f(z)| < 0   ==>   |f(z)| < 1.       (S)
```

Thus the dangerous arrow in the current programme is now precise: a model
margin does not merely have to be `o(1)`; it must beat the explicit three-part
budget (B), pointwise on the proposed arms and connector.

The Lean module [FormACutQuantitativeExpansion.lean](FormACutQuantitativeExpansion.lean)
checks (F1), the sharp one-factor inequality (L), its half-radius finite-sum
corollary, the anchored Lipschitz estimate (A1), the finite geometric
resummation, the radial-energy inequality (D), and the real stability
implication (S). The finite Fourier reindexing and root-of-unity product are
proved above by geometric series and elementary factorisation; the replay
checks their exact coordinates.

## 5. What the bound says about transition regimes

Suppose `E_1=...=E_(m-1)=0` and `E_m` is the first nonzero coefficient. At the
formal balance radius

```text
rho_m = |E_m|^(1/(n-m)),
```

the `m`-mode and `z^n` terms have the same size. Formula (B) proves stability
there only when the Fourier tail and the quadratic logarithmic error are
smaller than that common size.

This need not follow merely from `E_m != 0`. For example, one may have
`E_1=epsilon^4` and `E_2=epsilon`: mode one is literally first, but

```text
rho_1 = epsilon^(4/(n-1)),       rho_2 = epsilon^(1/(n-2)),
```

and `rho_2/rho_1 -> infinity` for `n>=4`. The useful outer scale is then mode
two, not the lexicographically first nonzero coefficient. The deterministic
replay includes this negative control.

So a uniform proof cannot divide by the first nonzero coefficient. It must use
the upper envelope of the finitely many mode scales, or an equivalent finite
Newton-polygon/stratified argument. This is a real reduction in the open
problem: infinitely many apparent degeneracies have become a finite competition
among `n-1` explicit scales, with the stronger anchored budget (A) attached.

There is nevertheless a decisive restriction on the dangerous high modes.
Write `e_k=x_k+i y_k` and `Delta=-Re E_0`. The disk condition makes every
`x_k<=0`, so `sum|x_k|=Delta`. If `R_m` and `Theta_m` are the Fourier
transforms of the real sequences `x` and `y`, then

```text
E_m       = R_m + i Theta_m,
E_(n-m)   = conj(R_m) + i conj(Theta_m),
|E_(n-m) + conj(E_m)| = 2|R_m| <= 2 Delta.                 (P)
```

Hence either the radial deficit is already comparable with a high mode and
supplies negative constant slack, or that high mode is paired, up to `2 Delta`,
with the low mode `n-m`. In the tangent limit `Delta=o(eta)`, every dominant
frequency therefore reduces to one with `m<=n/2`. At its balance radius the
anchored error (A2) is of strictly higher order:

```text
eta^2 rho_m = o(rho_m^n)       for m<=n/2.
```

This is why anchoring and pairing together repair the apparent high-mode
failure of the crude `O(eta^2)` expansion.

## 6. Claim boundary and next handoff

Closed here:

* the exact perturbed-root factorisation (F1)--(F2);
* the explicit finite expansion and its constants (B);
* the stronger origin-anchored finite-mode expansion (A), including the
  `O(eta^2|z|)` remainder;
* the radial-energy and approximate tangent-pairing inequalities (D), (P);
* the strict stability certificate (S);
* the reason a coefficient-only first-mode normalization is not uniform.

Still open:

* selecting two complete or truncated spokes compatibly through every change
  of dominant Fourier scale;
* proving a connector remains in the strict sublevel during those switches;
* overlapping the resulting explicit near-Fekete neighbourhood with the
  existing non-near-Fekete/Bergman regime.

The next mathematical object should therefore be a **finite mode-envelope
selector**, not another unquantified remainder expansion.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_form_a_cut_quantitative_expansion.py
```
