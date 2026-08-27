# Radial-lift coarea identity and its sampling obstruction

## The exact identity

For a monic polynomial `f`, put `U={z:|f(z)|<1}`.  Away from the finitely
many critical-value arguments, define the total length of all inverse lifts of
the value-plane radius at angle `theta` by

`R(theta)=integral_0^1 sum_{f(z)=s exp(i theta)} 1/|f'(z)| ds`.

This is exactly an arc-length integral: on any inverse branch `z(s)`,
`|z'(s)|=1/|f'(z(s))|`.  Polar coordinates in the value plane followed by the
area formula give

`integral_0^(2 pi) R(theta) dtheta
 = integral_U |f'(z)|/|f(z)| dA(z)`.

Thus the familiar coarea currency controls an angular `L1` average of the
complete radial inverse image.  This is a useful exact bridge between the
computation and the analysis, but it is not yet the desired discrete critical-
edge estimate.

## Why direct sampling at the critical rays fails

Consider

`f_epsilon(z)=z^n+epsilon*z-r^n`, with `0<r<1` and `epsilon>0` small.

When `r^n+epsilon<1`, Rouché's theorem on the unit circle puts all `n`
roots strictly inside the disk: `|epsilon*z-r^n|<|z^n|` there.  For sufficiently
small epsilon the critical values below also remain strictly inside the value
disk, so the family lies in the actual admissible initial state.

Its critical points obey `c^(n-1)=-epsilon/n`, so there are `n-1` distinct
simple critical points.  At each one,

`f_epsilon(c)=-r^n-(n-1)c^n`.

Consequently all `n-1` critical-value arguments converge to `pi` as epsilon
tends to zero.  Distinctness and genericity therefore provide no uniform
angular separation with which to sample the `L1` identity.

The limit polynomial `f_0(z)=z^n-r^n` makes the loss explicit.  On the negative
value ray the `n` lifts first run from the `n` roots to zero and then out again.
Their exact total length is

`R(pi)=n*(r+(1-r^n)^(1/n))`,

while the descending part alone is `n*r`.  Charging this same complete-lift
pointwise majorant once for each of the `n-1` coalescing critical rays produces

`(n-1)R(pi)>n(n-1)r`.

At `r=9/10` and every `n>=3`, this already exceeds the desired aggregate scale
`2(n-1)`.  Therefore the chain

`L_c <= R(arg f(c))`, then sum over critical points, then invoke the angular
average

cannot prove the candidate `sum_c L_c<2h`.  The problem is not merely a missing
constant: a single angular spike is being counted with critical multiplicity.

## What remains live

This result does **not** refute the all-critical aggregate conjecture.  The
boundary regular family remains its sharp positive model: after splitting the
multiple saddle, its descending critical edges approach the radial two-root
paths of length `2r`, and their normalized average approaches `r<1`.

The analytic consumer must therefore charge the descending Reeb edge itself
before angular integration, or cancel overlap/multiplicity among nearby
critical rays.  A viable proof may use an edge-disjoint Reeb measure, an
attachment interval with multiplicity divided out, or a telescoping charge
between consecutive saddle levels.  An unweighted point evaluation of the
complete radial-lift `L1` function is eliminated.

Replay:

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_radial_lift_coarea_gap.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_radial_lift_coarea_gap.py --check
```
