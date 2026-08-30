# Erdős #1041: the anchored nonlinear error is an exact reciprocal coefficient

Status: complete ordinary proof, exact rational checker, focused Lean kernel.
Current through 2026-08-27; the replay below passes. **This does not prove
Erdős #1041**, and it does not close any open
producer. It is a coordinate theorem: the `O(eta^2 |z|)` remainder that
`FormACutQuantitativeExpansion.md` carries as an error is, in the reciprocal
power-sum coordinates, part of an exact coefficient.

## 1. The exact expansion

Let `f(z) = prod_{j=1}^n (z - a_j)` with every `a_j != 0`, and put

```text
r(a) = min_j |a_j|,        p_m = sum_j a_j^{-m}   (m >= 1).
```

> **Theorem R1.** For `|z| < r(a)`,
>
> ```text
> log|f(z)| = log|f(0)| - Re sum_{m>=1} (p_m/m) z^m,
> ```
>
> the series converging absolutely. With `q = |z|/r(a) < 1` and `N >= 0`,
>
> ```text
> | log|f(z)| - log|f(0)| + Re sum_{m=1}^{N} (p_m/m) z^m |
>       <= n q^{N+1} / ((N+1)(1-q)).                       (T0)
> ```
>
> Writing `T_N` for the corresponding holomorphic tail,
>
> ```text
> |T_N'(z)|  <= (n/r) q^N / (1-q),                          (T1)
> |T_N''(z)| <= (n/r^2) q^{N-1} ( N/(1-q) + q/(1-q)^2 ).    (T2)
> ```

*Proof.* `f(z) = f(0) prod_j (1 - z/a_j)` and `|z/a_j| <= q < 1`, so

```text
log(f(z)/f(0)) = sum_j log(1 - z/a_j)
               = - sum_j sum_{m>=1} (z/a_j)^m / m
               = - sum_{m>=1} (p_m/m) z^m,
```

the double series converging absolutely because `|z/a_j| <= q`. Taking real
parts gives the identity. Since `|p_m| <= n r^{-m}`, the tail of the last
series is bounded by `sum_{m>N} n q^m/m <= n q^{N+1}/((N+1)(1-q))`, which is
(T0). Differentiating termwise gives (T1) and (T2) from
`sum_{m>N} q^{m-1} <= q^N/(1-q)` and
`sum_{m>N} (m-1) q^{m-2} <= q^{N-1}(N/(1-q) + q/(1-q)^2)`. ∎

The point of (T2) is that the discarded part is controlled in `C^2`, which is
what a moving quadratic contact needs. `FormACutQuantitativeExpansion.md`
bounds its remainder in `C^0` only.

**This is a Taylor expansion, not an asymptotic one.** `p_m` is an exact
function of the roots; no perturbation parameter appears, and nothing has been
linearised. `-sum_m (p_m/m) z^m` is simply the Taylor series of
`log(f(z)/f(0))` at the origin.

## 2. The coefficients are rational in the coefficients of `f`

Write `f(z) = sum_{k=0}^n c_k z^k` with `c_n = 1` and `c_0 = f(0) != 0`, and
put `chat_k = c_k/c_0`, with `chat_k = 0` for `k > n`.

> **Theorem R2.** `chat_0 = 1` and for every `m >= 1`
>
> ```text
> sum_{j=0}^{m-1} chat_j p_{m-j} + m chat_m = 0,
> ```
>
> that is `p_m = -m chat_m - sum_{j=1}^{m-1} chat_j p_{m-j}`.

*Proof.* The reciprocals `1/a_j` are the roots of the reversed polynomial, so
`e_k(1/a) = e_{n-k}(a)/e_n(a)`. From `c_k = (-1)^{n-k} e_{n-k}(a)` and
`c_0 = (-1)^n e_n(a)` we get `e_k(1/a) = (-1)^k chat_k`. Newton's identity for
the `1/a_j`,

```text
sum_{j=0}^{m-1} (-1)^j e_j(1/a) p_{m-j} + (-1)^m m e_m(1/a) = 0,
```

becomes the displayed recursion because `(-1)^j e_j(1/a) = chat_j`. ∎

Equivalently, `f'(z) = -f(z) sum_{m>=0} p_{m+1} z^m` as formal power series;
the recursion is that identity coefficient by coefficient.

**What R2 buys.** Every reciprocal Newton coordinate is a rational function of
the coefficients of `f` with denominator a power of `f(0)`. So the whole
normalisation of §4 is rational, hence semialgebraic in the real and imaginary
parts of the coefficients, and a curve-selection or Puiseux argument over that
normalisation is legitimate without any further argument. That is not true of
the root-error coordinates `e_k`, which require a root labelling.

## 3. The bridge: what this says about the `E_m` coordinates already on file

Take the near-Fekete parametrisation of this directory,

```text
a_k = omega^k (1 + e_k),   omega = exp(2 pi i/n),   eta = max_k |e_k| < 1,
E_m^{(j)} = sum_k e_k^j omega^{-km},   E_m = E_m^{(1)}.
```

> **Theorem R3.** For `1 <= m <= n-1`,
>
> ```text
> -p_m/m = E_m - ((m+1)/2) E_m^{(2)} + ((m+1)(m+2)/6) E_m^{(3)} - ... ,
> ```
>
> the general term being `(-1)^{j-1} (1/m) binom(m+j-1, j) E_m^{(j)}`, and
>
> ```text
> | -p_m/m - E_m |  <=  n (m+1) eta^2 / ( 2 (1-eta)^{m+2} ).      (R3)
> ```

*Proof.* `a_k^{-m} = omega^{-km}(1+e_k)^{-m}` and
`(1+e)^{-m} = sum_{j>=0} (-1)^j binom(m+j-1,j) e^j`. For `1 <= m <= n-1` the
`j = 0` term contributes `sum_k omega^{-km} = 0`, so
`p_m = sum_{j>=1} (-1)^j binom(m+j-1,j) E_m^{(j)}`; dividing by `-m` gives the
display. For the estimate, Taylor with integral remainder applied to
`h(e) = (1+e)^{-m}` gives
`|h(e) - 1 + m e| <= (eta^2/2) m(m+1)(1-eta)^{-m-2}`, and summing over the `n`
roots and dividing by `m` gives (R3). ∎

So the quantity that `FormACutQuantitativeExpansion.md` carries as the anchored
nonlinear remainder `R_anchor = O(eta^2 |z|)` is, term by term, the second and
higher terms of the exact coefficient `-p_m/m`. **It is not an error.** The
practical consequence is the one that matters for transfer: when a quadratic
correction happens to carry the same Newton weight as a nominally active linear
mode — which is exactly the situation a face switch or a tied face produces —
the reciprocal coordinates keep it, whereas the anchored expansion has to
budget it against the active margin.

`FormACutQuantitativeExpansion.md` keeps one thing this does not: its resummed
form `log|1-z^n| + Re P(z)` with `P = [sum_m E_m z^m + E_0 z^n]/(1-z^n)`
exhibits the degree-`n` baseline in closed form and has no infinite tail at
all, because `E_{m+n} = E_m`. The two forms are complementary; R1 is the one to
use when the contact order is the binding constraint, and the anchored form is
the one to use when the baseline must be exhibited exactly.

## 4. The reciprocal Newton normalisation

Near the regular `n`-gon `p_n(a)/n != 0`. Choose the continuous branch
`lambda(a)^n = p_n(a)/n` with `lambda -> 1` at the regular polygon, and put

```text
b_m(a) = (p_m(a)/m) lambda(a)^{-m},        so b_n(a) = 1,
d(a)   = -log|f(0)| = -sum_j log|a_j| > 0,
rho(a) = max( d^{1/n}, max_{1<=m<n} |b_m|^{1/(n-m)} ),
A_0    = d/rho^n,     A_m = b_m/rho^{n-m}   (1 <= m < n).
```

Then `0 <= A_0 <= 1`, `|A_m| <= 1`, and at least one of these is an equality,
so the coefficient section is compact. With `z = rho lambda^{-1} zeta`,
Theorem R1 becomes

```text
rho^{-n} log|f(rho lambda^{-1} zeta)|
   = -A_0 - Re( zeta^n + sum_{m=1}^{n-1} A_m zeta^m ) + E_N(zeta),
```

and by (T0)–(T2), for every fixed `M` and every `N >= n`,

```text
||E_N||_{C^2(|zeta| <= M)}  <=  C(n,N,M) rho^{N+1-n}.
```

Retaining more reciprocal terms therefore pushes the unmodelled error beyond
any prescribed finite Newton or contact order. This is the same compactification
as `AffineNormalisedModuli.md` Theorem N, in different coordinates: Theorem N
normalises at a critical point by `lambda^n = f(c)`, this one normalises at the
origin by the top reciprocal coefficient.

## 5. The staple length identity

For distinct `i, j` put `u_k = a_k/|a_k|` and, for
`0 <= s <= min(|a_i|,|a_j|)`, let the equal-radius staple be
`[a_i, s u_i] + [s u_i, s u_j] + [s u_j, a_j]`.

> **Theorem R4.** Its length is exactly
>
> ```text
> L = |a_i| + |a_j| - s (2 - |u_i - u_j|),
> ```
>
> and since `|u_i - u_j| <= 2`, `L <= |a_i| + |a_j| < 2` whenever both roots
> lie in the open unit disk, for **every** admissible `s` including `s = 0`.

*Proof.* The two arms have lengths `|a_i| - s` and `|a_j| - s`; the chord has
length `s|u_i - u_j|`. ∎

The content is that moving root directions cost nothing in the length budget:
no polynomial-independent margin is spent, which is required by
`negative_results` entry 3. `TruncatedSpokeReduction.md` records the special
case `|a_i| = |a_j| = 1`, where the identity reads `2(1-s) + 2 s sin(theta/2)`.

## 6. Contact absorption is a discriminant, not a limit

Uniform convergence to a non-positive model does not survive perturbation:
`-x^2 + eps` converges uniformly to `-x^2` and has a positive maximum for every
`eps > 0`. The correct local invariant is the completed square.

> **Theorem R5.** If `F(x) <= -kappa x^2 + B|x| + V + eps` with `kappa > 0`,
> then `F(x) <= V + eps + B^2/(4 kappa)` for all `x`; so the contact survives
> exactly when
>
> ```text
> V + eps + B^2/(4 kappa) < 0.
> ```

*Proof.* `-kappa x^2 + B|x| <= B^2/(4 kappa)`. ∎

This is the algebra behind the sextic first-order transverse selector already
on file: curvature `-x^2/20` against transverse slope `3 delta |x|` costs
exactly `(3 delta)^2/(4/20) = 45 delta^2`. Any transfer theorem that assumes
only uniform convergence to a non-positive atlas is false; the curvature and
the first nonzero transverse jet must both be retained.

## 7. What this does and does not deliver

**Delivers.** An exact, coefficient-rational, `C^2`-controlled expansion whose
truncation error can be pushed past any finite contact order; the identification
of the anchored nonlinear remainder as an exact coefficient; a length identity
that spends no margin; and the completed-square criterion that makes a
zero-margin contact decidable.

**Does not deliver.** No open producer is closed. In particular
`sextic_second_mode_mixed_neighborhood_transfer` is a statement about the
compact homogeneous mixed band `|E_1|/|E_2| < 3/4`, not about transfer, and
nothing here touches it. The general "resolved atlas transfers to actual
polynomials" statement needs, beyond §1–§6, a finite stratification with
strict leaves and a curve-selection argument; `NearFeketeUniqueNewtonFaceClosure.md`
supplies that for a unique outer Newton face, and only there.

## 8. What is not first here

* The origin-anchored finite-mode expansion with exact constant `log|f(0)|`,
  its `O(eta^2|z|)` remainder, and the geometric resummation `E_{m+n} = E_m`:
  `FormACutQuantitativeExpansion.md` §3. Theorem R3 is the statement that its
  remainder is an exact coefficient in other coordinates, not a replacement.
* The compactifying normalisation by a single scale with the top coefficient
  pinned: `AffineNormalisedModuli.md` Theorem N.
* The integral weight gap `q_k(n-m) - q_m(n-k) >= 1` and the unique-outer-face
  transfer: `NearFeketeUniqueNewtonFaceClosure.md`.
* The `s = 1` staple length: `TruncatedSpokeReduction.md`.
* The `6075 < 78^2 = 6084` outer-or-child overlap and the sextic null-branch
  leaves: the `SexticNullBranch*` modules.
* Newton's identities, the logarithmic series, and Taylor with integral
  remainder are classical.

## 9. Claim boundary

**Proved, by ordinary mathematics:** Theorems R1 (including (T0)–(T2)), R2, R3
(including (R3)), R4, R5, and the normalisation of §4.

**Verified formally:** the tail geometric bound behind (T0), the Newton
recursion of R2 at the first orders, the staple length identity R4, and the
completed-square bound R5, in
[`ReciprocalNewtonExpansion.lean#L49-L111`](ReciprocalNewtonExpansion.lean#L49-L111).
The load-bearing declarations are `tsum_geometric_tail` (`#L49-L56`),
`newton_solve` (`#L60-L73`), `staple_length_eq`/`staple_length_lt_two`
(`#L77-L88`), and `quadratic_contact_absorbs`/`contact_survives`
(`#L92-L111`).

**Verified exactly by replay:** R2 against `sum_j a_j^{-m}` on exact
Gaussian-rational configurations; the coefficient bound `|p_m| <= n r^{-m}`;
(R3) at `n = 4`, where `omega = i` makes both sides exactly Gaussian rational;
R4's inequality `|u_i - u_j|^2 <= 4` and `|a_i| + |a_j| < 2` on exact rational
moduli; and R5 including the sextic instance `45 delta^2`.

**Not proved:** Erdős #1041, and no producer of this directory. §7 states the
gap between §1–§6 and a general transfer theorem.

**Not established: novelty.** The expansion is the Taylor series of
`log(f/f(0))` and R2 is Newton's identity for the reversed polynomial. Both
should be assumed classical. What is claimed is the identification in R3 and
the resulting choice of coordinates.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_reciprocal_newton_expansion.py
lake env lean research_corpus/Erdos1041/ReciprocalNewtonExpansion.lean
```

The 2026-08-27 exact replay reports `NEWTON`, `COEFFBOUND`, `BRIDGE`,
`STAPLE`, `CONTACT`, and `COUNTERMODEL` as `PASS`, with 14,400 Newton rows,
15,000 coefficient-bound rows, and 2,000 contact rows. The replay validates
the exact-data arms and their claim boundary; the ordinary convergence proof
and the remaining transfer gap are not promoted to Lean by this receipt.
