# Erdős 1041: phase-moment repair of the reciprocal-weight spoke majorant

## Status

This note proves an exact hybrid straight-spoke certificate at an arbitrary
nonroot critical point.  It combines:

1. the inverse-square, phase-free AM--GM majorant; and
2. a new phase-sensitive Newton-coefficient majorant which is exact on the
   regular radial family.

It also gives the exact obstruction to using the inverse-square statistic
alone: that proposed universal certificate fails on every sufficiently
large regular radial polygon, and persists under small simple-critical-point
perturbations.

The hybrid removes the regular-family blind spot, but no theorem here proves
that every polynomial has a critical point satisfying the hybrid test.

## 1. The normalized spoke polynomial

Let

```text
P(z)=product_(k=1)^n(z-a_k),
P'(c)=0,             P(c)!=0.
```

For a selected root `a_i`, put

```text
u_k=(a_i-c)/(a_k-c),       u_i=1.                      (1)
```

Criticality gives

```text
sum_k u_k=(a_i-c) sum_k 1/(a_k-c)=0.                  (2)
```

Along `z=c+t(a_i-c)`, `0<=t<=1`, the exact normalized value is

```text
P(z)/P(c)=C_i(t):=product_k(1-tu_k)
                   =sum_(k=0)^n c_(i,k)t^k,           (3)
c_(i,0)=1,        c_(i,1)=0.                          (4)
```

Thus containment is a one-variable polynomial question carrying all phases.

## 2. The phase-free energy majorant

Let

```text
p_k=|c-a_k|^-2 / sum_j |c-a_j|^-2,
S_i=(1-p_i)/p_i=sum_(k!=i)|u_k|^2.                    (5)
```

AM--GM on the `n-1` spectator factors gives

```text
|C_i(t)|
 <=F_(n,S_i)(t)
 :=(1-t)[1+(2t+S_i t^2)/(n-1)]^((n-1)/2).             (6)
```

Indeed `sum_(k!=i)u_k=-1`, so the arithmetic mean of
`|1-tu_k|^2` is exactly the bracket in (6).  Put

```text
Phi_n(S)=max_(0<=t<=1)F_(n,S)(t).                     (7)
```

This is useful in diffuse configurations but discards every phase.

## 3. Exact phase-moment repair

The regular normalized spoke polynomial is `1-t^n`.  Subtract it in (3) and
use the triangle inequality:

```text
|C_i(t)| <= H_i(t),                                   (8)

H_i(t)=1-t^n
       +sum_(k=2)^(n-1)|c_(i,k)|t^k
       +|c_(i,n)+1|t^n.                               (9)
```

Define

```text
Psi_i=max_(0<=t<=1) H_i(t).                           (10)
```

This is not another phase-free norm.  If

```text
U_m=sum_k u_k^m,
```

Newton's identities give, for example,

```text
c_(i,2)=-U_2/2,
c_(i,3)=-U_3/3,
c_(i,4)=U_2^2/8-U_4/4.                               (11)
```

Thus (9) retains the signed complex low moments that (6) erased.  Keeping all
coefficients is a finite exact moment closure, not a series remainder.

Combining (6) and (8) proves the pointwise hybrid bound

```text
|C_i(t)|<=min(F_(n,S_i)(t),H_i(t)),
max_t |C_i(t)|<=B_i:=min(Phi_n(S_i),Psi_i).            (12)
```

One may sharpen `B_i` further to `max_t min(F,H)`.  The separated minimum in
(12) is retained because it gives two independently checkable scalar
certificates.

## 4. Two-root consumer

Order the roots so that `r_1=|c-a_1|<=r_2<=...`, and set

```text
mu=|P(c)|,          rho=mu^(1/n).                      (13)
```

> **Theorem (phase-moment two-spoke certificate).**  If
>
> ```text
> mu B_1<=1,              mu B_2<=1,                  (14)
> ```
>
> then the two straight segments from `c` to `a_1,a_2` lie in
> `{|P|<=1}` and their total length is at most `2`.

### Proof

Containment is (3), (12), and (14).  Since `B_i>=1`, (14) also gives
`mu<=1`.  The sharp critical ellipse theorem gives

```text
r_1+r_2<=2rho<=2.                                     (15)
```

Concatenating the two spokes proves the theorem.  Strict inequalities in
(14) give an open-sublevel path away from its root endpoints.  For roots in
the open unit disk, the usual dilation/limit argument supplies the strict
`<2` form.  ∎

The same theorem can be used with any critical point.  It does not require
selection by least critical value.

## 5. Exact failure of the weight-only proposal

For equal reciprocal weights, `S=n-1`.  Exact differentiation of (6) gives

```text
t_*=(n-3)/(n-1),
Phi_n(n-1)
 =2/(n-1) [2(n-2)/(n-1)]^((n-1)/2).                  (16)
```

This exceeds one for every `n>=4`.  Now take

```text
P_r(z)=z^n-r^n,             0<r<1.                    (17)
```

Its critical point is `c=0`, all weights are `1/n`, and `mu=r^n`.  Hence the
weight-only proposal fails whenever

```text
r^n Phi_n(n-1)>1.                                     (18)
```

For example, at `n=5`, `Phi_5(4)=9/8`; with `r=99/100`,

```text
(99/100)^5(9/8)>1                                    (19)
```

by exact integer arithmetic.  This is a falsifier of the proposed
**certificate**, not of Erdős 1041: the actual spoke polynomial is
`C_i(t)=1-t^n` and is safe.

The obstruction is not an artefact of a multiple critical point.  Fix any
`r` satisfying (18) strictly and consider

```text
P_(r,epsilon)(z)=z^n+epsilon z-r^n.                   (20)
```

If `0<epsilon<1-r^n`, Rouché on the unit circle puts every root strictly in
the disk, while

```text
P'_(r,epsilon)(z)=nz^(n-1)+epsilon
```

has `n-1` simple critical points.  Their configurations converge to the
equal-weight object as `epsilon` tends to zero.  Continuity and the strict
margin in (18) show that **every** critical point still fails the weight-only
test for all sufficiently small positive `epsilon`.

The phase-moment side repairs the exact lost family: for (17),

```text
c_(i,2)=...=c_(i,n-1)=0,       c_(i,n)=-1,
Psi_i=1.                                             (21)
```

Thus the hybrid theorem certifies both nearest spokes for every `r<1`, even
when (18) makes the inverse-square half fail.

## 6. Computed scope and exact open boundary

The companion checker replays (2), (6), (11), (16), (19), and (21), then
falsifies the two majorants against direct spoke products on deterministic
complex samples.  A near-regular perturbation probe confirms the predicted
behaviour: `Psi_i-1` follows the first nonzero complex Newton moment, whereas
`Phi_n(S_i)-1` stays bounded away from zero at the regular limit.  Those
samples are intuition only.

The exact remaining question is global selection:

```text
does some critical point make (14) hold for its two nearest roots?          (22)
```

The old weight-only version of (22) is false by (17)--(20).  The hybrid
version survives, is exact on the regular boundary, and uses precisely the
phase data absent from the falsified proposal.  No unrestricted Erdős 1041
conclusion is claimed.
