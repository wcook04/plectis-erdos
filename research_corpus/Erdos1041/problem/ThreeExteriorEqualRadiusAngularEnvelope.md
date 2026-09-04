# Erdős 1041: regular angular spacing maximizes the equal-radius three-exterior radial barrier

## Status

This note proves two global slices of the symmetric-envelope conjecture for
three exterior roots and the full local result at the regular triangle.
When their moduli are equal, one of the three actual root-attached radial
curves has barrier no larger than the regular-triangle model.  Under every
product-preserving infinitesimal radius perturbation, the minimum ray barrier
has nonpositive first variation.  Moreover, when the angles are regularly
spaced, arbitrary unequal radii are globally dominated by equal radii.  The
remaining `m=3` problem is the coupled irregular-angle/irregular-radius case.

## Theorem

Let the exterior Blaschke zeros be

```text
a_j=s*exp(i theta_j),  j=1,2,3,  0<s<1,
```

and let `W(z)=unit*t*z^n/B(z)`.  For the radial segment from the component
boundary to the excluded root corresponding to `a_j`, write `F_j(x)` for
`|W(x exp(i theta_j))|/t`, where `1<=x<=1/s`.

> **Theorem.** There is one index `j`, independent of `x`, such that for every
> `1<=x<=1/s`,
>
> ```text
> F_j(x) <= x^n (1-sx)/(x-s) * Q_x(-1/2),               (1)
> Q_x(c)=(1-2sx c+s^2x^2)/(x^2-2sx c+s^2).
> ```
>
> The right side is exactly the radial profile of the equal-radius regular
> triangle.  Consequently the first exterior merge height is no larger than
> the regular-triangle radial barrier.

## Proof

For `x>=1`, direct differentiation gives

```text
d/dc log Q_x(c)
 = 2sx(1-x^2)(1-s^2)
   /[(1-2sx c+s^2x^2)(x^2-2sx c+s^2)] <= 0,             (2)
```

and

```text
d^2/dc^2 log Q_x(c)
 = (2sx)^2[(x^2-2sx c+s^2)^(-2)
           -(1-2sx c+s^2x^2)^(-2)] <= 0.                (3)
```

Thus `log Q_x` is decreasing and concave.

Put `c_12=cos(theta_1-theta_2)` and cyclically.  The elementary identity

```text
c_12+c_23+c_31=(|sum_j exp(i theta_j)|^2-3)/2 >= -3/2   (4)
```

and Jensen's inequality imply

```text
[Q_x(c_12)Q_x(c_23)Q_x(c_31)]^(1/3) <= Q_x(-1/2).       (5)
```

The spectator multiplier on ray `j` is

```text
S_j(x)=sqrt(Q_x(c_jk)Q_x(c_jl)).                         (6)
```

Moreover

```text
S_1S_2S_3=Q_x(c_12)Q_x(c_23)Q_x(c_31).                  (7)
```

Choose the pair with smallest cosine and let `j` be the remaining index.
Because `Q_x` is decreasing, the omitted pair has the largest `Q_x` value;
hence (6) makes `S_j(x)=min_i S_i(x)`.  The ordering depends only on the
cosines, not on `x`.  Equations (5)-(7) therefore give, for this single index,

```text
S_j(x) <= (S_1S_2S_3)^(1/3) <= Q_x(-1/2)
```

for every `x`.  Multiplying by the common selected-zero factor
`x^n(1-sx)/(x-s)` proves (1). ∎

## Local radial polarization theorem

Keep the regular angles and perturb the radii as

```text
r_j(epsilon)=s*exp(epsilon*u_j),    u_1+u_2+u_3=0.
```

At a fixed interior point `1<x<1/s`, differentiate the logarithm of the ray
profile at `epsilon=0`.  The selected-zero factor contributes `A u_j`, while
each of the two spectator factors contributes `L u_k`.  Hence

```text
d/depsilon log F_j(x)|_0
 = A u_j+L(u_k+u_l)=(A-L)u_j,                            (8)
```

where exact simplification gives

```text
A-L = 3sx(x^2-1)
      * (s^4x+s^3x^2+s^3+sx^2+s+x)
      / [2(x-s)(sx-1)(s^2+sx+x^2)(s^2x^2+sx+1)] < 0.   (9)
```

All factors except `sx-1` are positive, and `sx-1<0` in the interior.  Since
the `u_j` sum to zero, some `u_j` is maximal and nonnegative; (8)-(9) show that
this ray has nonpositive first variation.  At a nonzero radial tangent the
maximum `u_j` is positive, so the pointwise min-ray profile decreases strictly.

At the regular profile's unique interior maximizer the same calculation,
together with the envelope theorem, gives the one-sided directional derivative
of the min of the three optimized ray barriers.  Thus the regular triangle is
a strict local maximizer in every nonzero product-preserving radial direction.
Combined with the preceding angular theorem, all pure angular directions and
all pure radial directions are now controlled exactly.

## Global radial polarization at regular angles

Now fix the three angles at `120`-degree spacing, but allow radii `r_1,r_2,r_3`
with product `p=s^3`.  Let `r_1=r` be the largest radius and follow its radial
attachment curve.  At fixed `x` put

```text
g(log rho)=1/2 log Q_x(rho,-1/2).
```

Exact differentiation gives

```text
d^2/d(log rho)^2 g
 = -rho*x(rho-1)(rho+1)(x^2-1) P
   /[2(rho^2+rho*x+x^2)^2(rho^2*x^2+rho*x+1)^2] >= 0,  (10)
```

where

```text
P=rho^4x^2+4rho^3x^3+4rho^3x+rho^2x^4+7rho^2x^2+rho^2
  +4rho*x^3+4rho*x+x^2 > 0.
```

Thus `g` is convex.  Since `r_2,r_3<=r` and
`log r_2+log r_3=3log s-log r`, convexity on this interval puts the maximum of
`g(log r_2)+g(log r_3)` at an endpoint.  Hence it is at most

```text
g(log r)+g(log(s^3/r^2)).                               (11)
```

It remains to compare this endpoint family with equality.  Let `A(r)` be the
logarithmic derivative, with respect to `log r`, of the selected-zero factor,
and let `L(r)=d g(log r)/d log r`.  Direct factorization gives `L(r)>0` and

```text
A(r)+L(r)
 = r(x^2-1) R
   /[2(x-r)(rx-1)(r^2+rx+x^2)(r^2x^2+rx+1)] < 0,       (12)
```

where

```text
R=r^4x^2+r^3x^3+r^3x+4r^2x^4+4r^2x^2+4r^2
  +r*x^3+r*x+x^2 > 0.
```

The endpoint profile in (11) therefore has derivative

```text
A(r)+L(r)-2L(s^3/r^2) < 0                               (13)
```

with respect to `log r`.  Because `r>=s`, it is bounded by its value at `r=s`,
which is exactly the regular equal-radius profile.  Thus the ray attached to a
largest-radius zero proves the symmetric envelope whenever the three angles
are regularly spaced.

## Frontier effect

Together with `TwoExteriorSymmetricEnvelope.md`, this identifies a reusable
polarization hierarchy:

1. two exterior zeros: angular and radial polarization are both exact;
2. three equal-radius exterior zeros: regular angular spacing is exact;
3. arbitrary radii with regular angles: globally closed by convex endpoint
   reduction and the decreasing boundary family;
4. coupled irregular angles and irregular radii: still open.  Prove that some
   ray admits both the angular Jensen gain and the radial endpoint reduction,
   or find the additional weighted angular statistic needed to select it.

## Exact no-go for the three-ray product shortcut

A tempting way to avoid selecting one ray is to prove that the product of all
three radial profiles is at most the cube of the regular profile.  This is
false, even pointwise and with rational data.

Take radii

```text
r_1=r_2=1/1600,   r_3=1/25,   s=(r_1r_2r_3)^(1/3)=1/400,
```

put the first two zeros at angle `0` and the third at angle `pi`, and evaluate
at `x=8` (which lies in every radial domain).  Substitution into the exact
rational formulas gives

```text
F_1(8)F_2(8)F_3(8)
 / [8^n A_s(8)Q_s(-1/2)]^3 > 1.1673.                   (14)
```

The checker proves the squared rational inequality before converting the
displayed ratio to a decimal.  This does **not** refute the min-ray envelope:
the ray attached to the `1/25` zero is extremely cheap.  It refutes only the
geometric-mean shortcut and forces a selector-based proof in the coupled case.

The third line is now the first unsupported implication.  It is narrower than
the original all-`m` mountain-pass conjecture and retains actual attachment
curves throughout.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_angular_envelope.py
```
