# Erdős 1041: a strict curvature gain on the GP3 endpoint switch

The endpoint-curvature theorem can be sharpened by retaining the curvature of
the optimized two-angle envelope, not only the active pair kernel.  This
removes the previous vanishing of the curvature payment on the
reciprocal-triangle switch.

## Theorem (strong endpoint curvature gain)

Let `a,b,c>0`, and suppose the endpoint branch is active at `a`.  Put

```text
kappa=bc/(b+c)-a >= 0,
nu=b^2 c^2/(b+c)^3 > 0.
```

Let `mu>0` be the lower curvature `K_a''(-1)` of the pair kernel belonging to
the active angle.  With `S_true` denoting the unlinearized surplus and
`S_end` its tangent endpoint residual,

```text
S_true >= S_end + G(kappa,mu,nu),

G = 9mu/8-(3mu/2-kappa)^2/[2(mu+nu)],  0<=kappa<=3mu/2,
    9mu/8,                              kappa>=3mu/2.       (1)
```

The gain is strictly positive throughout the active cone.  In particular, on
the switch `kappa=0`,

```text
G(0,mu,nu)=9mu nu/[8(mu+nu)] > 0.                       (2)
```

## Proof

Fix the active angle and write `x=cos A`.  After minimizing the other two
tangent angles, their contribution is

```text
f(x)=a x-sqrt(b^2+c^2+2bcx).
```

Direct differentiation gives

```text
f'(1)=a-bc/(b+c)=-kappa,
f''(x)=b^2 c^2/(b^2+c^2+2bcx)^(3/2) >= nu              (3)
```

for `-1<=x<=1`.  Taylor's integral remainder from the endpoint therefore
gives

```text
f(x)-f(1) >= kappa(1-x)+nu(1-x)^2/2.                   (4)
```

The active pair kernel independently contributes
`mu(x+1/2)^2/2`.  Setting `y=1-x` reduces the extra payment to

```text
min_(0<=y<=2)
  [kappa y+nu y^2/2+mu(3/2-y)^2/2].                   (5)
```

The stationary point is

```text
y_*=(3mu/2-kappa)/(mu+nu).
```

It belongs to `[0,2]` exactly when `kappa<=3mu/2`; the lower endpoint is
active otherwise.  Substitution gives (1).  On the first branch,

```text
G = [9mu nu/4+3mu kappa-kappa^2]/[2(mu+nu)] > 0,
```

because the numerator is concave in `kappa` and positive at both endpoints
of `[0,3mu/2]`.  Formula (2) follows immediately.

Replay all derivative and minimization identities exactly with

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_endpoint_strong_curvature_gain.py
```

This theorem supplies a strict payment on the switch surface, but it does not
by itself compare that payment with a possibly negative tangent residual.
That quantitative switch comparison remains the GP3 obligation.  No claim of
GP3 or Erdős 1041 is made here.
