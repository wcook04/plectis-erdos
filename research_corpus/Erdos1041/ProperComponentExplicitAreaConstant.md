# Erdős 1041: the two-root quintic area gap is now EXPLICIT — `A_{5,2} <= 4^{-2/5}(1 - 6.76e-8)`, closing the FRONTIER gap-5 remainder

Date: 2026-08-30.  Origin: main-loop proof completed from the Schur-tail
seed of `ProperComponentUniformAreaGap.md`, chain audited and sharpened
by a subagent (certified 50-dps arithmetic with directed rounding; the
final inequality re-verified in EXACT rational arithmetic by the
checker).  Checker: `scripts/check_erdos1041_explicit_area_constant.py`.

## Theorem (explicit uniform area gap, `n = 5`, `k = 2`)

Every monic quintic `P`, regular `t > 0`, and component `U` of
`{|P| < t}` containing exactly two roots satisfy

```text
Area(U)  <  pi * 4^{-2/5} * (1 - eps_5) * t^{2/5},
eps_5 := (13/50000)^2 = 6.76e-8,
```

STRICT even at the constant (the chain saturates at `6.780e-8`; the
stated `eps_5` is the checker's exact-rational test point).  Critical
`t` inherit `<=` by the landed monotone approximation.

Corollary (merge threshold): the `k = 2` dichotomy threshold improves
from `Theta_{5,2} = tanh(4^{2/5}) = 0.940354210173506...` to

```text
Theta_{5,2}  >=  tanh( 4^{2/5} / (1 - eps_5) )  =  0.940354223795...,
```

an explicit `+1.362e-8` (the elementary fallback constant of §4 gives
`+1.67e-11`).  This turns FRONTIER §4.5's "awaits an explicit constant"
into a number; the LOGICAL gap is closed, while the measured `0.482`
shows the true constant is far larger — sharpening remains open, not
existence.

## Inputs (all landed in `ProperComponentUniformAreaGap.md`)

Exterior normalisation `Psi(zeta) = zeta + sum b_l zeta^{-l}`,
`p = C^5/t`, `E = sum l |b_l|^2 < 1`, identity
`Area/(pi t^{2/5}) = p^{2/5}(1 - E)` (`(*)`); the factorisation
`Q(Psi(zeta)) = zeta^5 g(1/zeta)` (`(**)`), `g` a degree-3 Blaschke
product with `g(0) = p > 0`, `Q` of degree 5; the STRICT capacity bound
`p < p* = 1/4`; and the Schur-tail lemma
`sum_{nu > N} |hat g_nu|^2 >= (1 - p^2) p^{2N}`.  One completion the
proof needs and the landed note asserts only on `|zeta| > 1`: `(**)`
holds a.e. on the unit circle — at a regular value `partial U` is an
analytic Jordan curve, so `Psi` extends across `T` by Schwarz
reflection (alternatively: both sides are bounded analytic with
nontangential limits, and agreement on `|zeta| > 1` forces boundary
agreement a.e.).  With that, `|Q(Psi)| = |g(1/zeta)| = 1` a.e. on `T`,
so `||Q o Psi||_{L^2(T)} = 1`.

## Proof

Write `eta = sqrt E`, `delta = delta_5(p) = (1 - p^2) p^{10}` and
`h = Psi - zeta = sum_{l >= 1} b_l zeta^{-l}`.

**Step 1 (tail forces negative modes).**  `Q(Psi) = sum_{nu >= 0}
hat g_nu zeta^{5 - nu}` on `T`; the modes with `nu > 5` are the
negative frequencies, and `Q(zeta)` (a polynomial) has none.  Schur
tail with `N = 5`:

```text
sqrt(delta)  <=  || Proj_{<0} (Q o Psi) ||_2
             =   || Proj_{<0} (Q o Psi - Q) ||_2.
```

**Step 2 (linear term, sharp).**  For the linear part `Q' h`:
`Proj_{<0}(Q' h)` has frequency-`(-nu)` coefficient
`sum_j j q_j b_{j-1+nu}` (`nu >= 1`).  The tail-decay lemma
`sum_{l >= j} |b_l|^2 <= E/j` (immediate from `sum l |b_l|^2 = E`)
gives, per `j`, an `l^2` norm `<= j |q_j| (E/j)^{1/2}
= sqrt j |q_j| eta`, so

```text
|| Proj_{<0}(Q' h) ||_2  <=  eta * sum_{j=1}^5 sqrt j |q_j|
    <=  eta * [ sqrt 10 (B_Q^2 - p^2)^{1/2} + sqrt 5 p ],
```

using Cauchy–Schwarz over `j <= 4` (`sum_{j<=4} j = 10`) and the EXACT
leading coefficient `q_5 = p`.  Here `B_Q := (sum_j |q_j|^2)^{1/2}`.

**Step 3 (higher order, regrouped).**  `Q o Psi - Q - Q' h
= sum_j q_j sum_{q'=2}^{j} C(j,q') zeta^{j-q'} h^{q'}`; by
Hausdorff–Young + weighted Hölder (`||h||_{2q} <= C_q eta`,
`C_q = zeta(q/(q-1))^{(q-1)/(2q)}`, `A_q := C_q^q`), `||h^{q'}||_2 <=
A_{q'} eta^{q'}`, and regrouping BY POWER with Cauchy–Schwarz over `j`:

```text
|| Q o Psi - Q - Q' h ||_2  <=  B_Q * sum_{q'=2}^{5} A_{q'} G_{q'} eta^{q'},
G_q := ( sum_{j=q}^{5} C(j,q)^2 )^{1/2}
     (G_1^2..G_5^2 = 55, 146, 117, 26, 1).
```

**Step 4 (self-bound).**  `||Q o Psi||_2 = 1` and Steps 2–3 give
`B_Q <= 1 + B_Q W(eta)`, `W(eta) := sum_{q=1}^{5} A_q G_q eta^q`, so
`B_Q <= Bbar := 1/(1 - W(eta))` whenever `W(eta) < 1`.

**Step 5 (the explicit bound).**  Combining,

```text
sqrt(delta_5(p))  <=  L(eta) :=
   [ sqrt 10 (Bbar^2 - p^2)^{1/2} + sqrt 5 p ] eta
   + Bbar * sum_{q=2}^{5} A_q G_q eta^q .
```

`L` is strictly increasing, so `eta >= L^{-1}(sqrt delta)`.  At
`p = 1/4`: `delta = 15/16777216` exactly, and the checker verifies IN
EXACT RATIONAL ARITHMETIC (rational upper bounds for `A_q`, `G_q`, the
square roots, with every rounding upward) that

```text
L(13/50000)  <=  sqrt(15)/4096,
```

hence `eta >= 13/50000` and `E >= eps_5 = (13/50000)^2` whenever
`p = 1/4`.  For `p < 1/4` the same chain runs with `delta_5(p)`;
`delta_5` is increasing on `(0, 1/4]` (`delta' = 2p^9(5 - 6p^2) > 0`),
and the map `p -> p^{2/5}(1 - eps(p))` is strictly increasing (rigorous
guard: `d eps/dp <= delta'(p)/L'(0)^2` with `L'(0) >= 3`, and
`(5/2) p delta'(p)/9 <= 2.5e-6 < 1 - eps`), so for every `p < 1/4`,

```text
Area/(pi t^{2/5}) = p^{2/5}(1 - E) <= p^{2/5}(1 - eps(p))
                  <  4^{-2/5} (1 - eps_5).
```

QED

## 4. Elementary fallback (no Step-2/3 sharpening)

The crude one-line chain — `||Q o Psi - Q||_2 <= B_Q C_5 eta` with
`C_5 = (sum_{j=1}^5 D_j^2)^{1/2}`, `D_j = sum_{q<=j} C(j,q) A_q` —
gives `eps >= delta/(C_5^2 (1 + sqrt delta)^2)`; with the certified
`C_5 <= 103.8636` this is `eps >= 8.27e-11` (crude integral-test zeta
bounds alone: `C_5 <= 110.28`, `eps >= 7.3e-11`).  Recorded because it
is fully self-contained on one page.

## 5. General `(n, k)` (same chain, computed values)

`p* = k/(2n-k)`, `delta_n(p) = (1-p^2) p^{2n}`, `G_q^{(n)} =
(sum_{j=q}^n C(j,q)^2)^{1/2}`; `delta_n` increasing on `(0, p*]` for
every `n, k` since `p* <= (n-1)/(n+1) < sqrt(n/(n+1))`.  Sharp-chain
values (subagent, certified arithmetic; checker re-certifies `(5,2)`):

```text
(5,2): 6.78e-8    (5,1): 2.46e-11    (5,3): 1.09e-5    (6,2): 2.14e-10
```

## Claim boundary

Ordinary proved mathematics; the ONLY numerical content of the theorem
is the exact-rational verification `L(13/50000) <= sqrt(15)/4096` and
the rational-ceiling constants feeding it, both done in exact
arithmetic by the checker (floats appear only in cross-checks).  The
subagent's audit found the route capped near `eps_5 ~ 1.1e-7`
(numerically-located operator norm `Lambda_5 = 2.835` vs the certified
`sqrt 10` surrogate) — sharpening toward the measured `0.482` needs a
different mechanism, not better roundings; that remains open.  The
landed seed figure `5.7e-10` at `p >= 1/8` in the parent note is TRUE
but understated (exact value `9.17e-10`).  Nothing here is a parent
claim.  PRIORITY CAVEAT: no literature search; claim "new to this
directory" only.
