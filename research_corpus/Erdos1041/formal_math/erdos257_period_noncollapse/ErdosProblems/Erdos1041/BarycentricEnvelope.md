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

## 1a. Power-mean convex-cover lattice

The quadratic representation is one member of a full exact family.  For
`1 <= p < infinity`, positive `lambda_j` with `prod_j lambda_j=1`, and
`G_T=T^(1/n)`, put

```text
C_(p,lambda)(T)
  = {z : (1/n) sum_j (lambda_j |z-a_j|)^p <= G_T^p}.
```

Also put

```text
C_(infinity,lambda)(T)
  = intersection_j closedDisc(a_j, G_T/lambda_j).
```

Then, for every `p in [1,infinity]`,

```text
K_T = union_(prod lambda=1) C_(p,lambda)(T).             (Bp)
```

For finite `p`, AM--GM applied to the `n` nonnegative numbers
`(lambda_j|z-a_j|)^p` proves that every carrier lies in `K_T`.  Conversely,
if `f(z) != 0`, set `G=|f(z)|^(1/n)` and
`lambda_j=G/|z-a_j|`.  Their product is one and every normalized distance is
exactly `G`, so `z` lies in the carrier whenever `G<=G_T`.  At a root `a_i`,
take `lambda_j=epsilon` for `j!=i` and
`lambda_i=epsilon^(-(n-1))`; a sufficiently small positive `epsilon` puts
`a_i` in the carrier.  The same canonical weights prove the `p=infinity`
case directly.

Each carrier is convex.  For fixed weights the power-mean inequality gives

```text
C_(q,lambda)(T) subset C_(p,lambda)(T)   (1 <= p <= q <= infinity).
```

Thus the returned weighted-distance carrier (`p=1`), the disc carrier in
(A) (`p=2`, after replacing its weights by `lambda_j^2`), and the new
intersection-of-root-discs carrier (`p=infinity`) are not competing
representations but a nested lattice with the same exact union.  The result
does not supply a length bound: changing `lambda` along a chain can still
destroy attachment to a fixed root, which is precisely the quantifier kept
open by COVER.

### 1b. Exact attachment no-go at the regular quartic

The largest fixed-weight member `p=1` still cannot prove COVER.  For two
points `x,y`, define

```text
M(x,y) = inf_(prod lambda=1)
           max(sum_j lambda_j|x-a_j|, sum_j lambda_j|y-a_j|).
```

Convex duality and AM--GM give the exact minimax formula

```text
M(x,y)/n
 = max_(0<=t<=1)
     (product_j (t|x-a_j|+(1-t)|y-a_j|))^(1/n).       (Bdual)
```

Indeed `max(A,B)=max_t(tA+(1-t)B)`, strong convex duality exchanges the
infimum and maximum, and the product-one minimum of `sum lambda_j c_j` is
`n(product c_j)^(1/n)`.  Endpoint zero factors follow by a limit.

Now take the roots `r,ir,-r,-ir`, with `r=99/100`, let `x=0`, and let `y=r`.
At `t=1/2` the four affine distances are

```text
r/2,  r(1+sqrt(2))/2,  3r/2,  r(1+sqrt(2))/2,
```

whose product is

```text
r^4 * 3(3+2sqrt(2))/16 > r^4 * 87/80 > 1.            (Bno)
```

The first strict inequality uses `sqrt(2)>7/5`; the second is exact integer
arithmetic.  Hence no `p=1` carrier in `K_1` contains both the origin and any
root.  Nevertheless every radial arm is genuinely safe:

```text
|f(sr)| = r^4(1-s^4) < 1  for 0<=s<1,
```

and has length `r<1`.  Thus the common-carrier certificate fails on the
parent problem's equality family while COVER itself holds sharply.  Optimizing
the fixed-weight power-mean lattice cannot close the attachment quantifier;
future convex-cover work must allow carrier switching with a separately
controlled path, or leave this coordinate.

The two scalar inequalities in `(Bno)` and the radial strictness are formalized
in `PowerMeanCarrierAttachmentNoGo.lean` and replayed independently by
`scripts/check_erdos1041_power_mean_carrier_attachment_no_go.py`.

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
