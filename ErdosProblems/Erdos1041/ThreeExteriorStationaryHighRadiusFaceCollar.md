# Erdős 1041: compact high-radius collars off the stationary collapse face

## Status

In the ordered chart

```text
u=r s w,  v=s w,  0<=r,s<=1,
```

the continuous stationary surplus satisfies two new exact conclusions.

1. On the concrete slab

   ```text
   0<=r<=10^-12,  1/2<=w<=3/4,  0<=s,t<=1,
   ```

   one has `S_stat(t;u,v,w)>0`.

2. For every real `R` with `1/2<=R<1`, there is an explicit
   `epsilon(R)>0` such that

   ```text
   0<=r<epsilon(R),  1/2<=w<=R,  0<=s,t<=1
   ```

   implies `S_stat(t;u,v,w)>0`.

Together with the already proved all-collapse and finite-scale collars, the
second statement gives an open neighborhood of every point of the face
`r=0` in the physical range `0<w<1`.  This is local boundary removal, not a
proof of the full stationary inequality: no uniform positive width as
`R` tends to `1` is asserted, and the compact off-face interior remains open.

## 1. A parameterized face lower bound

On `r=0`, the exact face theorem writes

```text
S_0(t;s,w)=w^3 P_ord(t,s,w)/C(t,s,w),
```

with `C>0`.  Restrict the tensor Bernstein form of `P_ord`, of degree
`(28,28,50)`, to `w in [1/2,1]`.  All 42,891 controls are nonnegative (62
high-`w` controls vanish).  Crucially, all 841 controls with `w`-index zero
are positive, with exact minimum

```text
m_0=944707/8192.
```

The full restricted stream has digest

```text
c3bef1c70d3e9317aa6c711811c87bf1076b3ba46f2201d8aa2e49cc69a789c5.
```

Fix `1/2<=R<1` and put `theta=2R-1`.  A left de Casteljau subdivision at
`theta` sends a degree-50 control row `(b_0,...,b_50)` to controls whose
`k`-th entry is a convex combination containing
`b_0(1-theta)^k`.  Since every original control is nonnegative and every
`b_0>=m_0`, each new control is at least

```text
m(R)=m_0 [2(1-R)]^50 >0.                         (1)
```

For `0<=x<=R`, put `A_R=1+R+R^2`.  The positive cleared denominator obeys

```text
Q<=A_R^4,
K<=(1+t)Q+N<=2A_R^4+2A_R^2.
```

The omitted sign factors are at most one.  Since `w>=1/2`, (1) gives

```text
S_0 >= L(R)
 := (1/8) m(R) /
    ((A_R^4)^4 (2A_R^4+2A_R^2)^2) >0.             (2)
```

## 2. An explicit compact-radius Cauchy collar

Treat `S_stat` as a rational function of complex `r` on `|r|=1/8`.  Then
`|u|<=1/8`, while the two real radii are at most `R`.  Let

```text
a=1-1/8-(1/8)^2=55/64,
d=(2U+4U^2+2U^3+U^4)/a^2=1297/3025,  U=1/8,
c=1-2d=431/3025,
f_R=(1-R^2)/(1+R+R^2)^2.
```

The subtraction estimate for the phase kernel gives a mixed pair-sum lower
bound `c`; two real kernels give `2f_R`.  Thus the harmonic-mean quantity

```text
ell(R)=c(2f_R)/(c+2f_R)                              (3)
```

is a positive lower bound for every stationary quotient denominator.  Also

```text
B=2(1+U^2)/a^2+2=2874/605
```

bounds every numerator pair sum.  With

```text
p=U R^2,  q=U+2R,
```

termwise absolute values give the exact rational majorant

```text
M(R) = (U+U^2)/(1-U)
     + 2(R+R^2)/(1-R)
     + 6[R(1+R/2)+R^2(R+1/2)]/a
     + 3q/(1-p) + 3qp/(1-p)
     + (3/2)R^2 B + (3/2)R^2 B^2/ell(R).            (4)
```

All terms in (4) are finite and positive for `R<1`.  Cauchy's estimate yields

```text
|S_stat(r)-S_0|
 <= M(R) (r/U)/(1-r/U).
```

Consequently the explicit choice

```text
epsilon(R)=U L(R)/(M(R)+L(R))>0                     (5)
```

proves the parameterized theorem.

## 3. Strong concrete slab

For `R=3/4`, direct exact subdivision on `[1/2,3/4]` improves (1): every
control is at least `944707/8192`.  Using the corresponding local denominator
bound and the same circle calculation gives

```text
M(3/4)=1357159489278069/4805902393600.
```

At `r=10^-12`, the exact lower bound minus the Cauchy variation is

```text
3546303003385585440289099771072474285183122678111523
/1467189338451516912195382886511687343920025203557636476000000
>0.
```

This proves the concrete collar.

## 4. Replay and boundary

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_high_radius_face_collar.py
```

The checker reconstructs the cleared face numerator, performs the exact
Bernstein restrictions, hashes the control stream, and recomputes the
concrete and parameterized rational bounds.  There are no floating-point or
sampling claims.

The theorem removes the entire physical `r=0`, `0<w<1` face only locally
after composition with the lower-scale collars.  It does not cover a compact
off-face interior, provide a width uniform at `w=1`, prove GP3, or prove
Erdős 1041.
