# Erdős 1041: an explicit ordered collar off the three-exterior collapse corner

## Status

This note proves a nonzero exact collar for the stationary radial surplus from
`ThreeExteriorGreenPolarization.md`.  Order the scale-free radii and use the
multiplicative chart

```text
0 <= u <= v <= w,
u=r s w,  v=s w,  0<=r,s<=1.                            (1)
```

Then

```text
S_stat(t;u,v,w)>0                                       (2)
```

throughout the explicit wedge

```text
0<=r<=1/2,  0<w<=1/25000,  0<=s<=1,  0<=t<=1,           (3)
```

using the continuous extension on coordinate faces.  The proof is exact:
formal power-series algebra identifies the cubic, a 16-control Bernstein
certificate gives a uniform lower bound, and a rational Cauchy majorant bounds
the complete infinite tail.

There is also an adaptive exact family: for every `3/4<=h<1`, the same proof
gives a positive scale collar on the whole projective interval `0<=r<=h`,
with an explicit scale bound tending to zero only as `h` tends to `1`.  Thus
every projective direction except the isosceles face `r=1` has a proved
all-collapse neighbourhood; that face is already covered by the isosceles
theorem.

This does not cover arbitrary positive `w`, the full ordered cone, GP3, or
unrestricted Erdős 1041.

## 1. Exact cubic in the ordered chart

Use the scale-free definitions

```text
A(x)=1+x+x^2,
D_t(x)=1+t x+t^2x^2,
L_t(x)=(1-x^2)/A(x)^2+t(1-t^2x^2)/D_t(x)^2.             (4)
```

The tangent weights are

```text
alpha_ij=u_i u_j(L_t(u_i)+L_t(u_j)).                    (5)
```

For formal expansion it is important to cancel the removable coordinate-face
singularities before dividing.  For example,

```text
alpha_12 alpha_13/alpha_23
 =u^2 (L_t(u)+L_t(v))(L_t(u)+L_t(w))/(L_t(v)+L_t(w)).   (6)
```

The other two quotient terms are cyclic.  Truncated-series arithmetic applied
directly to the rational operations in (4)--(6) gives

```text
S_stat(t;rsw,sw,w)=c_3(t,r,s)w^3+O(w^4),                (7)
```

with the coefficients of `w^0,w^1,w^2` exactly zero and

```text
c_3=3/2(1+t^2)F(r,s),                                   (8)

F(r,s)=2r^3s^3-r^2s^3-r^2s^2-rs^3-rs
       +2s^3-s^2-s+2.                                  (9)
```

On the full square, the degree `(3,3)` tensor Bernstein controls of `F` are

```text
[[2,5/3,1,2],
 [2,14/9,7/9,4/3],
 [2,13/9,4/9,0],
 [2,4/3,0,0]].                                         (10)
```

They are all nonnegative.  The zeros lie on the already-visible diagonal
boundary; indeed

```text
F(r,1)=2(1-r)^2(1+r).                                  (11)
```

For the concrete wedge (3), put `r=R/2`.  Its 16 controls are positive and
the least is

```text
7/12.                                                   (12)
```

Consequently, throughout (3),

```text
c_3 >= 3/2 * 7/12 = 7/8.                               (13)
```

More generally put `r=hR`, where `3/4<=h<1`.  Exact one-variable Bernstein
comparison of all 16 controls proves that their least is

```text
m(h)=2(1-h)^2(1+h).                                    (14)
```

Hence the adaptive cubic lower bound is

```text
c_3 >= c(h):=3(1-h)^2(1+h).                            (15)
```

## 2. One Cauchy bound controls the complete tail

Fix real `t,r,s` in (3) and regard the surplus as a rational function of the
complex variable `w`.  On the circle

```text
|w|=rho=5/42                                            (16)
```

all three radii have modulus at most `rho`.  Put

```text
delta=1-rho,
a_0=1-rho-rho^2=1529/1764.                             (17)
```

Thus the self denominators have modulus at least `delta`, while both `A` and
`D_t` have modulus at least `a_0`.

For `f(x)=(1-x^2)/(1+x+x^2)^2`, direct subtraction from `1` gives

```text
|f(x)-1|
 <=(2rho+4rho^2+2rho^3+rho^4)/a_0^2
 =928405/2337841=:E.                                   (18)
```

Since `L_t(x)=f(x)+t f(tx)`, every pair sum in a quotient such as (6)
satisfies

```text
|L_t(x)+L_t(y)| >= 2-4E = 962062/2337841=:ell>0.        (19)
```

In particular all removable quotient expressions are analytic on and inside
the circle.  Also

```text
|L_t(x)| <= 2(1+rho^2)/a_0^2 = 6311592/2337841=:L.      (20)
```

Bounding the three self terms, six directed pair terms, two comparator terms,
three positive alpha terms, and three reciprocal-variance quotient terms gives

```text
|S_stat(w)| <= M:=
 3(rho+rho^2)/delta
 +6[rho(1+rho/2)+rho^2(rho+1/2)]/a_0
 +9rho/(1-rho^3)+9rho^4/(1-rho^3)
 +3rho^2L+6rho^2L^2/ell
 =2377539521421837945/582238064264313611.               (21)
```

Cauchy's estimate therefore gives `|a_n|<=M/rho^n` for every Taylor
coefficient.  Using the exact cubic cancellation from §1,

```text
|sum_(n>=4) a_n w^n|/w^3
 <= M (w/rho^4)/(1-w/rho).                              (22)
```

At `w=1/25000`, the right side is exactly

```text
105688288837860677801496/129920185775607321791675.     (23)
```

Subtracting (19) from (11) leaves the strictly positive rational margin

```text
63934989726365830129757/1039361486204858574333400.     (24)
```

The right side of (18) increases with `w`, so (20) proves (2) on the whole
wedge (3).

The same argument with (15) proves the adaptive family

```text
0<=r<=h,  0<w<W(h),
W(h)=c(h)rho^4/(M+c(h)rho^3),  3/4<=h<1.               (25)
```

For each fixed `h<1`, `W(h)>0`.  This is the promised projective coverage of
every direction short of `r=1`.

## 3. Replay and surviving boundary

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_collapsed_face_collar.py
```

The checker independently performs the formal rational-series calculation,
verifies the cubic identity, converts (9) to the exact Bernstein basis, and
replays every rational majorant and the final strict margin.  The 16 cubic
controls have SHA-256 digest

```text
886924c3472c28538d3bd2627cb4b9d87fd38fe2755f5e578ff76e85640e516c.
```

Together with `ThreeExteriorStationaryCollapsedFace.md`, this proves the
stationary expression on the entire one-radius-collapse face and on a
nontrivial projective wedge at the all-collapse corner.  In fact (25) reaches
every fixed projective ratio `r<1`, while the face `r=1` is an already-proved
isosceles slice.  The surviving boundary is now quantitative: the certified
scale shrinks as `r` approaches `1`, and no arbitrary-`w` collar has been
proved away from `r=0` or the isosceles faces.  No claim about the endpoint
angular branch is made here.
