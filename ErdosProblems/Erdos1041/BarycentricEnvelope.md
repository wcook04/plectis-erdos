# Barycentric disc envelope and sharp critical ellipse

## Status

This note gives an exact disc-envelope representation, an inverse-square
descent disc, and one sharp sufficient containment regime for Erdős #1041.  It
does not prove the unrestricted problem.  Its value is that it represents
containment by a correlated finite-dimensional family of discs.

The sharp critical ellipse in section 3 is **not a new result of this note**.
It is the already-landed geometric-mean scale theorem
`exists_two_roots_dist_sum_le_two_mul_geomMean` in
`CriticalTwoRootProximity.lean`, ordinarily exposed by
`GlobalCriticalTwoNearestBudget.md`.  It is repeated here only because the new
disc envelope supplies a new potential containment consumer for that metric
theorem.

## 1. Exact quadratic envelope

Let `f(z)=prod_j (z-a_j)` and `K_T={z: |f(z)|<=T}`.  For positive weights
`lambda_j` with `prod_j lambda_j=1`, set

```
Q_lambda(z) = (1/n) sum_j lambda_j |z-a_j|^2.
```

Then

```
K_T = union_lambda {z: Q_lambda(z) <= T^(2/n)}.              (A)
```

Indeed, weighted AM--GM gives `|f(z)|^(2/n) <= Q_lambda(z)`, so
every quadratic sublevel lies in `K_T`.  Conversely, away from the roots take

```
u=|f(z)|^(1/n),       lambda_j=u^2/|z-a_j|^2.
```

Their product is one and every summand is `u^2`, giving equality.  A root is
obtained by a limiting choice with its weight large and all other weights
small.

Writing `p_j=lambda_j/sum lambda`, `G(p)=(prod p_j)^(1/n)`,
`h(p)=sum p_j a_j`, and `V(p)=sum p_j|a_j-h(p)|^2`, (A) becomes

```
D_T(p) = closedDisc(h(p), sqrt(n T^(2/n) G(p)-V(p))) subset K_T,
K_T = union_p D_T(p).                                       (B)
```

For fixed `z`, `nG(p)-sum p_j|z-a_j|^2` is concave.  Thus a common disc
attachment remains present while its weight vectors are linearly
interpolated.  This correlation is absent from the already-refuted
independent-strip allocation.

## 2. Inverse-square descent disc

For a non-root `z`, put

```
P(z)=sum_j 1/(z-a_j),       S(z)=sum_j 1/|z-a_j|^2,
B(z)=sum_j a_j |z-a_j|^-2 / S(z) = z-conj(P(z))/S(z).
```

Then

```
closedDisc(B(z), |z-B(z)|) subset {y: |f(y)|<=|f(z)|}.       (C)
```

Apply AM--GM to the ratios `|1-(z-y)/(z-a_j)|^2`.  Their sum is

```
n - |P|^2/S + S |y-B|^2.
```

It is at most `n` on the disc in (C).  The completed-square identity is
formalized in `BarycentricEnvelope.lean`.  Harmonic mean below geometric mean
also yields the Pythagorean descent inequality

```
|z-B(z)|^2 + |f(B(z))|^(2/n) <= |f(z)|^(2/n).                (D)
```

At a non-root critical point `c`, write
`rho=|f(c)|^(1/n)` and `S_c=sum |c-a_j|^-2`.  The weights
`lambda_j=rho^2/|c-a_j|^2` in (A) give the explicit unit-level hub disc

```
closedDisc(c, delta_c) subset K_1,
delta_c^2 = n(1-rho^2)/(S_c rho^2).                          (E)
```

## 3. Existing sharp critical ellipse interface

Order `r_j=|c-a_j|` increasingly at a non-root critical point and let
`rho=(prod r_j)^(1/n)`.  Then

```
r_1+r_2 <= 2 rho.                                            (F)
```

Criticality gives

```
1/r_1 <= sum_{j>=2} 1/r_j <= (n-1)/r_2,
```

so `r_1>=r_2/(n-1)` and `r_2<=rho (n-1)^(1/n)`.  Also
`rho^n>=r_1 r_2^(n-1)`, hence `r_1<=rho^n/r_2^(n-1)`.  If
`r_2<=rho`, (F) is immediate.  Otherwise `x=r_2/rho` lies in
`[1,(n-1)^(1/n)]` and

```
(r_1+r_2)/rho <= x+x^(-(n-1)) <= 2,
```

because the last function is decreasing on that interval.  Equality forces
all `r_j=rho`.  Thus the exact length constant is already available; the hard
part is keeping the spokes inside the lemniscate.

## 4. A sharp contained-spoke regime

At `c`, let `p_j=1/(S_c r_j^2)` and `x_i=S_c r_i^2`.  Interpolate in the
simplex from `p` to the vertex `e_i`.  The barycentre traces the straight spoke
from `c` to `a_i`, while direct calculation of `G` and `V` in (B) shows that
the spoke is safe if

```
rho^2 <= inf_{0<=t<1} Phi_(n,x_i)(t),
Phi_(n,x)(t) = (((1+(x-1)t)/(1-t))^(1/n))/(1+xt/n).           (G)
```

The logarithmic derivative of `Phi` has the sign of

```
t (2n-(n-1)x+n(x-1)t).
```

Therefore `x_i<=2n/(n-1)` makes `Phi>=1`, and the entire spoke is safe whenever
`rho<=1`.

Consequently, if `c` is a least-critical-value point and

```
S_c r_2^2 <= 2n/(n-1),                                      (H)
```

the two nearest spokes lie in `K_1` and have total length at most `2rho<=2`.
After scaling roots in the open unit disc by their maximum modulus `R<1`, the
path has length at most `2R<2` and lies in `|f|<=R^n<1`.

The unrestricted residual is the diffuse regime where (H) fails.  In the disc
model it asks for a feasible weight path between two root vertices whose
barycentre path has length at most `2rho`.  This is a correlated disc-chain
problem, not the previously falsified independent attachment budget.

## 5. Exact guardrail

Arbitrary critical-to-root spokes are not always safe.  For

```
f_r(z)=(z^2-r^2)(z^4+(6/5)r^2z^2+r^4)
```

all six roots are distinct and have modulus `r`, and zero is critical, but

```
|f_r(r/2)| = (327/320) r^6.
```

Thus for `r^6>320/327` the spoke from zero to `r` leaves `K_1`.  This does not
contradict (G), and zero is not least-critical in this example; it prevents an
unsupported jump from the sharp ellipse theorem to spoke containment.
