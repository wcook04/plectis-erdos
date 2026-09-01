# Erdős 1041: the m=3 endpoint Poisson reduction and the selector domain

## Status

This note works the two obligations of `ThreeExteriorGreenPolarization.md` from
the complementary, computation-first side.  It (1) proves the exact
identification of the `q -> 1` endpoint of the derivative inequality (8) with
a weighted Poisson-kernel inequality and eliminates the angles exactly, (2)
records a certified witness that the literal `q in [s, 1]` barrier domain of
the selector obligation is false, and (3) verifies the corrected-domain
barrier statement under global adversarial search.  The final
piecewise-rational radius residual is not yet proved.  Unrestricted Erdős
1041 remains open.

## 1. Exact endpoint identification for (8)

The corpus's derivative inequality (8) is

```text
sum_(j,k) r_j H(q, r_k, cos(theta_j-theta_k))
  >= (sum_j r_j) [3q^2/(q^3-p) + 3p q^2/(1-p q^3)],
```

with `p = r_1 r_2 r_3` and

```text
H(q,r,c) = (1-r^2)(q(1+r^2)-rc(1+q^2))
           /[(q^2+r^2-2qrc)(1-2qrc+q^2r^2)].
```

Substituting `q = 1` collapses the two denominator factors identically, so
**at `q = 1` inequality (8) is exactly** the weighted Poisson inequality

```text
sum_(j,k) r_j P_(r_k)(c_jk) >= (r_1+r_2+r_3) T(p),
P_r(c) = (1-r^2)/(1+r^2-2r c),   c_jk = cos(theta_j-theta_k),
T(p)   = 3(1+p)/(1-p).                                  (E1)
```

Both sides are continuous at `q = 1`, so (E1) is the endpoint value of the
residual of (8).  Nothing here is a limit argument: `H(1,r,c) = P_r(c)` is a
direct substitution, verified exactly by the replay checker.

## 2. Exact angle elimination at the endpoint

`P_r` is strictly convex in `c` (exact checker identity), with

```text
P_r(-1/2)  = psi(r) = (1-r^2)/(1+r+r^2),
P_r'(-1/2) = phi(r) = 2r(1-r^2)/(1+r+r^2)^2,
```

so the tangent bound gives, exactly,

```text
sum_(j,k) r_j P_(r_k)(c_jk)
  >= D(r) + sum_(j<k) G_jk (c_jk + 1/2),                  (E2)
D(r)    = sum_j r_j(1+r_j)/(1-r_j)
          + sum_(j<k) [r_j psi(r_k) + r_k psi(r_j)],
G_jk    = 2 r_j r_k (phi(r_j) + phi(r_k)).
```

The remaining angle problem is exactly the corpus's weighted cosine problem

```text
min_(A+B+C=0) G_12 cos A + G_23 cos B + G_31 cos C,
```

whose minimum is explicit: the stationary value
`-(G_12^2 G_23^2 + G_12^2 G_31^2 + G_23^2 G_31^2)/(2 G_12 G_23 G_31)` when
`1/G_12, 1/G_23, 1/G_31` form a triangle, and the endpoint value
`min(G_31 - G_12 - G_23, -G_31 - |G_12 - G_23|)` otherwise.  The replay
checker validates this formula against brute-force angle minimization (exact
agreement to machine precision on both branches, 24 endpoint-branch and
stationary-branch samples).

Consequently the endpoint residual of (8) reduces **exactly** to an explicit
piecewise-rational function of the radii alone:

```text
E(r_1,r_2,r_3) = D(r) + M(G) + (G_12+G_23+G_31)/2
                 - (r_1+r_2+r_3) T(p).                   (E3)
```

Computationally (200000-sample deterministic scan over the radius cube):
`E >= 0` everywhere, with minimum `+1.6e-6` attained near the equal-radius
slice; the equal-radius slice satisfies `E = 0` identically (floating zero
`4.4e-16`), and near-equal perturbations `(0.3+eps, 0.3, 0.3-eps)` scale as
`E ~ 1.406 eps^2` — the same quadratic equality-locus behaviour as the
corpus's isosceles `(x-z)^2` factor.  On the endpoint branch of the cosine
minimum (24 forced samples) the residual minimum is `+5.8e-2`.

**Open remainder:** prove `E >= 0` as a rational inequality.  The
stationary-branch numerator has 52083 operations with mixed signs and the
endpoint-branch numerators have 417 terms; both are in the same
reduced-quotient-sign class as the corpus's isosceles quotient, and no
factorization was found.  The endpoint branch of (8) is now, however, a
three-variable rational inequality rather than a coupled angle/radius
problem.

## 3. Boundary-layer corollary for GP3

Let `c_j = sum_k (1-r_k^2)/|e^{i theta_j} - a_k|^2` be the Poisson slope of
`log|B|` at the boundary point `omega_j = e^{i theta_j}`.  Near `q = 1`,

```text
log|B(q omega_j)| = -c_j (1-q) + O((1-q)^2),
d/dq log T_p(q)|_(q=1) = 3(1+p)/(1-p) = T(p),
```

so the pointwise GP3 margin in the boundary layer is governed by

```text
max_j c_j >= T(p)                                        (BL)
```

with first-order margin `(max_j c_j - T(p))(1-q)`.  Since (E1)-(E2) sum with
positive weights `r_j`,

```text
sum_j r_j c_j >= (sum_j r_j) T(p)  ==>  max_j c_j >= T(p),
```

so proving the endpoint inequality (E3) `>= 0` also closes the GP3 boundary
layer.  Numerically (8-seed differential evolution plus Nelder-Mead polish),
the unweighted margin `max_j c_j - T(p)` never went below `+1.3e-8`, and its
minimizer ran to the degenerate corner `r -> 0`; the weighted margin attained
floating zero exactly at the regular triangle.  Equality holds iff the
configuration is regular (equal radii, 120-degree spacing), matching the
Dubinin symmetrization evidence recorded in `ThreeExteriorGreenPolarization.md`.

## 4. Certified witness: the literal `[s,1]` barrier domain is false

The selector obligation is stated with ray barriers on `q in [s, 1]`
(`x in [1, 1/s]`).  For unequal radii this overshoots the attached root: the
ray `q e^{i theta_j}` passes through its own zero `a_j` at `q = r_j`, and the
segment beyond `r_j` is not part of a curve "from the component boundary to
the excluded root".

Witness (rational data, 60-digit evaluation):

```text
(r_1, r_2, r_3) = (99/100, 1/10^6, 99/100),
(theta_1, theta_2, theta_3) = (0, 1/100, 2/100),
s = (r_1 r_2 r_3)^(1/3) = 0.0099332217...
```

At `q = s`, all three ray values satisfy

```text
|B(s e^{i theta_j})| / s^3 = 9928.217... > 1  (each j),
```

so `min_j max_(q in [s,1)) |B(q e^{i theta_j})|/q^3 >= 9928 >> 1 = M_sym`.
The literal-domain reading of the selector/interval lemma is false.  This is
a domain defect, not a bridge defect: on the geometrically correct domains —
per-ray `[r_j, 1]`, or the conservative common domain
`[max_k r_k, 1)` consistent with GP3's own domain — the statement revives.

## 5. Corrected-domain barrier statement

On the corrected common domain `q in [max_k r_k, 1)`, define

```text
b_j = max_q (log|B(q e^{i theta_j})| - 3 log q).
```

**Conjecture (selector, corrected domain).** `min_j b_j <= 1`, with the
regular triangle as the tight equality family (`T_p(q) <= q^3` with equality
only at `q = 1`).

Global adversarial search (7-seed differential evolution plus Nelder-Mead
polish over all radii and angles, 500-point q-grids) returned a maximum of
`min_j b_j` of `1.1e-16` — floating zero, attained only in the degenerate
corner `r -> 0` where `|B| -> q^3` identically.  No violation was found.
Note this does **not** follow from pointwise GP3 (the minimizing ray may
depend on `q`); it is the genuine selector content.

The first-order angular statistic `C_j = sum_k r_k cos(theta_j - theta_k)`
(max provably nonnegative since `sum_j r_j C_j = |sum_k r_k e^{i theta_k}|^2
>= 0`, and it controls the boundary layer of the best ray) selects the
barrier minimizer on the corrected domain in only 61 percent of 600 random
trials (mean log-barrier penalty `2.8e-3`, worst `2.7e-1`).  It is evidence
bearing, not a selector; the search for the selecting weighted angular
statistic asked for by `ThreeExteriorEqualRadiusAngularEnvelope.md` remains
open.

## Claim boundary

Exact in this note: the `q = 1` identification `H(1,r,c) = P_r(c)`, the
convexity and tangent constants, the exact reduction of the endpoint residual
to (E3), and the falsity witness of Section 4 (60-digit evaluation of
rational data).  Numerical evidence only: `E >= 0`, (BL), and the
corrected-domain selector conjecture.  GP3, the radius-weighted certificate,
the selector lemma, the symmetric envelope, and unrestricted Erdős 1041
remain open.  Packet rebuilding is out of scope for this cycle; the note is
standalone corpus material for absorption by the active proof lane.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_three_exterior_endpoint_and_selector.py
```
