# Erdős 1041: the regular-row log tangent fails on every two-positive collapse face

## Status

This note gives an exact obstruction to one proposed proof of the three-exterior
endpoint inequality.  The proposed logarithmic inequality itself is **not**
refuted.  What fails is the further replacement of each convex angular pair by
its tangent at the regular angle `cos(theta_i-theta_j)=-1/2`.

## The proposed reduction

Write

```text
P_r(c)=(1-r^2)/(1+r^2-2rc),
A(r)=P_r(1)=(1+r)/(1-r),
B(r)=P_r(-1/2)=(1-r^2)/(1+r+r^2),
p=r_1r_2r_3,  s=p^(1/3),  T=3(1+p)/(1-p).
```

The regular-row weights

```text
alpha=A(s)/T,   beta=B(s)/T
```

satisfy `alpha+2 beta=1`.  Weighted AM--GM in each Poisson sum gives

```text
sum_j r_j log(c_j/T)
 >= alpha sum_i r_i log(A(r_i)/A(s))
    + beta sum_(i<j) [
        r_i log(P_(r_j)(c_ij)/B(s))
       +r_j log(P_(r_i)(c_ij)/B(s))].                  (1)
```

For a pair put

```text
Q_ij(c)=r_i log P_(r_j)(c)+r_j log P_(r_i)(c),
d_i=1+r_i+r_i^2,
g_ij=Q_ij'(-1/2)=2r_ir_j(1/d_i+1/d_j).
```

Each `Q_ij` is strictly convex.  Replacing it in (1) by its tangent at
`-1/2`, and minimizing the resulting weighted cosine sum, produces the
radii-only residual

```text
Psi(r)=alpha sum_i r_i log(A(r_i)/A(s))
 + beta [sum_i (R-r_i)log(B(r_i)/B(s))
         +M(g)+(g_12+g_23+g_31)/2],                   (2)
R=r_1+r_2+r_3,
M(g)=min sum_(i<j) g_ij cos(theta_i-theta_j).
```

The hoped-for assertion was `Psi>=0`.

## Exact collapse-face obstruction

Set `r_1=r_2=x` and let `r_3` tend to zero, where `0<x<1`.  Then

```text
s -> 0,  alpha,beta -> 1/3,
g_12 -> 4x^2/(1+x+x^2),  g_23,g_31 -> 0,
M(g) -> -g_12.
```

Consequently (2) has the exact limit

```text
Psi_0(x)
 = (2x/3) log(A(x)B(x)) - 2x^2/[3(1+x+x^2)]
 = (2x/3) [log(1+u)-u],
u=x/(1+x+x^2).                                         (3)
```

Since `u>0` and `log(1+u)<u`, equation (3) is strictly negative for every
`0<x<1`.  Continuity therefore gives positive radii with `Psi<0` in every
sufficiently thin neighborhood of each such collapse point.  The proposed
radii residual is not globally nonnegative.

This is not merely an asymptotic floating-point effect.  The checker gives a
fully rational positive-radius witness

```text
(r_1,r_2,r_3)=(1/8,1/8,1/64000),   s=1/160,
```

uses the exact stationary weighted-cosine formula, and bounds every logarithm
by rational truncations of

```text
log q = 2 atanh((q-1)/(q+1)).
```

Its exact rational upper bound is less than `-7.8924e-5`.

## What survives

The failure belongs to the pair-tangent relaxation, not to (1) and not to the
original logarithmic conjecture.  Indeed, on the limiting face above the
untangented expression is nonnegative.  At the angular minimum the two
positive equal radii are antipodal and

```text
P_x(1)+P_x(-1)+P_0 = A(x)+A(x)^(-1)+1 >= 3.
```

Thus the original weighted logarithmic sum has nonnegative limiting value,
whereas (2) is strictly negative.  Any continuation of the geometric route
must retain finite pair curvature (or minimize the pair logarithms directly);
the regular-angle first tangent alone cannot close the endpoint.

This note proves no GP3 selector, no finite radial inequality, and no case of
unrestricted Erdős 1041.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_endpoint_log_geometric.py
```
