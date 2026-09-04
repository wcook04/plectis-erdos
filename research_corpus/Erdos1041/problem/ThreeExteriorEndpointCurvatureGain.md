# Erdős 1041: a quantitative curvature gain on the GP3 endpoint branch

This note upgrades the endpoint switch-square reduction from an algebraic
identity to a strict branch-aware lower bound.

For `0<r<=q<1`, recall

```text
H(q,r,c)=(q-rc)/(q^2+r^2-2qrc)
         -(qr^2-rc)/(1+q^2r^2-2qrc).
```

For a pair of radii `r_i,r_j`, put

```text
K_ij(c)=r_i H(q,r_j,c)+r_j H(q,r_i,c),
alpha_ij=K_ij'(-1/2),
mu_ij=K_ij''(-1).
```

The source tangent reduction supplies `alpha_ij>0`. The new conclusion is the
following.

## Theorem (endpoint curvature gain)

Let `a,b,c>0` be the three tangent weights, and suppose the endpoint branch is
active at `a`, so

```text
F=bc-a(b+c)>=0,   kappa=F/(b+c).
```

Let `mu>0` be `K_a''(-1)` for the pair kernel belonging to the active angle.
If `S_true` is the surplus obtained from the unlinearized convex pair kernels
and `S_end` is its tangent endpoint residual, then

```text
S_true >= S_end + Psi(kappa,mu),

Psi(kappa,mu) = 3kappa/2-kappa^2/(2mu),  0<=kappa<=3mu/2,
                9mu/8,                   kappa>=3mu/2.
```

In particular `Psi>=0`, with equality exactly on the switching surface
`F=0`. Away from that surface the endpoint tangent estimate gains a strict,
explicit amount.

## Proof

Direct differentiation gives

```text
H_cc=4qr^2[(q^2-r^2)/(q^2+r^2-2qrc)^3
           +(1-q^2r^2)/(1+q^2r^2-2qrc)^3].
```

Both summands are nonnegative and the second is strictly positive. A further
derivative is

```text
H_ccc=24q^2r^3[(q^2-r^2)/(q^2+r^2-2qrc)^4
               +(1-q^2r^2)/(1+q^2r^2-2qrc)^4] > 0.
```

Thus `K_a''` increases on `[-1,1]`, `mu=K_a''(-1)>0`, and strong convexity at
the tangent point gives

```text
K_a(x)>=K_a(-1/2)+K_a'(-1/2)(x+1/2)+mu(x+1/2)^2/2.   (1)
```

Fix the active angle `A` and write `x=cos A`. Minimizing the other two tangent
angles subject to `A+B+C=0` gives

```text
f(x)=a x-sqrt(b^2+c^2+2bcx).
```

Since

```text
f'(x)=a-bc/sqrt(b^2+c^2+2bcx)
     <=a-bc/(b+c)=-kappa,
```

we have `f(x)-f(1)>=kappa(1-x)`. The endpoint tangent minimum is `f(1)`.
Keeping only the active-kernel curvature term in (1), therefore,

```text
S_true-S_end
 >= min_(-1<=x<=1) [kappa(1-x)+mu(x+1/2)^2/2].        (2)
```

The quadratic in (2) has stationary point `x=kappa/mu-1/2`. It lies in the
interval exactly when `kappa<=3mu/2`, giving
`3kappa/2-kappa^2/(2mu)`; otherwise the minimum is at `x=1`, giving `9mu/8`.
Both branches agree at `kappa=3mu/2`, and the stated equality condition is
immediate.

Replay the derivative identities, switch algebra, quadratic minimization, and
an exact positive rational kernel specimen with

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_endpoint_curvature_gain.py
```

This theorem does not by itself prove the endpoint residual nonnegative: one
must still control the tangent stationary value on or near `F=0`. Its value is
that the remainder is now localized to the switch surface; all strict endpoint
points carry an explicit positive curvature payment. It does not prove GP3 or
Erdős 1041.
