# Erdős 1041: a uniform finite-scale collar off the stationary collapse face

## Status

This note thickens the exact `u=0` theorem from
`ThreeExteriorStationaryCollapsedFace.md` on a nontrivial finite-scale slab.
In the ordered chart

```text
u=r s w,  v=s w,  0<=r,s<=1,                           (1)
```

the stationary surplus is strictly positive whenever

```text
0<=r<=10^-22,
1/25000<=w<=1/2,
0<=s,t<=1.                                             (2)
```

The width is deliberately crude but fully uniform and exact.  Combined with
the all-collapse collars in `ThreeExteriorStationaryCollapsedFaceCollar.md`,
it is the first overlap that carries positivity from the scale-zero corner to
a genuine finite-scale interval while moving off the face `r=0`.

It does not cover `w>1/2`, a practical-width collar, GP3, or unrestricted
Erdős 1041.

## 1. Quantitative lower bound on the face

On `r=0`, write the continuous stationary residual as

```text
S_0(t;s,w)=w^3 P_ord(t,s,w)/C(t,s,w),                  (3)
```

where `P_ord` and the positive denominator `C` are exactly those in
`ThreeExteriorStationaryCollapsedFace.md`.  The tensor Bernstein degree of
`P_ord` on `[0,1]^3` is `(28,28,50)`.

Restrict the `w` direction exactly to `[1/25000,1/2]` by two de Casteljau
splits.  All 42,891 resulting controls are strictly positive.  Their exact
minimum is

```text
m =
12279771987308302586472053335247680637483798058378066075156428194742975182708104138949979874250363701733625111973
 /1412807648648595204576849937438964843750000000000000000000000000000000000000000000000000000000000000000000000000.
                                                                  (4)
```

The control stream has SHA-256 digest

```text
77cb56827c008300bac187950f580f08d4cb466b72e8d9fc3608d2f86a8c22a1.
```

For real `0<=t,s<=1` and `w<=1/2`,

```text
A(w),D_t(w),A(sw),D_t(sw) <= 7/4.
```

Hence, with the notation `Q=A^2D^2`, `K=(1+t)Q+N` from the face theorem,

```text
Q <= Q_max=2401/256,
K <= K_max=3185/128,
C <= Q_max^4 K_max^2
  =337122325107410704225/70368744177664.                (5)
```

Equations (3)--(5) and `w>=1/25000` give the exact positive face lower bound

```text
S_0 >= L_0 := (1/25000)^3 m/(Q_max^4K_max^2)>0.         (6)
```

The checker emits `L_0` as a reduced rational.

## 2. A complex-r Cauchy bound

Fix real `t,s,w` in the slab and treat `S_stat` as a rational function of the
complex projective variable `r`.  On

```text
|r|=1/8,                                               (7)
```

one has `|u|=|rsw|<=1/16`, while `v,w<=1/2`.  Put

```text
U=1/16,
a_U=1-U-U^2=239/256.                                   (8)
```

For `f(x)=(1-x^2)/(1+x+x^2)^2`, the same subtraction used in the
all-collapse collar gives

```text
|L_t(u)-(1+t)| <= 2*9249/57121,
|L_t(u)| <= 131584/57121.                              (9)
```

For real `0<=x<=1/2`, monotonicity of `L_t` gives

```text
L_t(x) >= f(1/2)=12/49,
L_t(x) <= 2.                                           (10)
```

Therefore every denominator `L_i+L_j` in the cancelled stationary quotient
form is bounded below by

```text
ell=24/49,                                             (11)
```

and every numerator pair sum is bounded above by

```text
B=245826/57121.                                        (12)
```

Bounding the self, directed-pair, comparator, alpha, and quotient terms on
the circle yields

```text
|S_stat(r)| <= M_r
 =152259770097409/5481518516880.                       (13)
```

All denominators are nonzero in the closed disc, so Cauchy's estimate applies.
For real `0<=r<1/8`,

```text
|S_stat(r)-S_0|
 <= M_r (r/(1/8))/(1-r/(1/8)).                        (14)
```

At `r=10^-22`, the right side of (14) is strictly smaller than `L_0`.
The exact difference is

```text
121494909091889509246860522269724224673483288272769421012253910219803809161936043759770886726364780589102555718998923054848522343913199709123921
 /1293998127809641900215802214217038998357901387808778070829113210352755721418319424516167603922411899475264362990856170654296875000000000000000000000000000000000000
 >0.                                                    (15)
```

Equations (6), (14), and (15) prove (2).

## 3. Replay and exact boundary

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_finite_scale_face_collar.py
```

The replay reconstructs the cleared face numerator from the primitive
rational terms, performs the exact de Casteljau restriction, checks all 42,891
control signs and the digest, then recomputes every denominator, circle, and
Cauchy bound as rational arithmetic.

The theorem covers only the first finite slab `w<=1/2`.  Extending the collar
through `1/2<w<1` requires a separate high-radius chart because the self-term
denominators approach the boundary and the uniform circle majorant (13) is no
longer effective.  That is now the smallest uncovered part of the `r=0`
boundary; no point on the slab in (2) remains open.
