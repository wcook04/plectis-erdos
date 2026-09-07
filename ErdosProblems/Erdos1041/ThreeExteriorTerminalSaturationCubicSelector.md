# Erdős 1041: terminal saturation cubic selector for three exterior zeros

## Status

This note closes the speed-saturation endpoint left by the finite
three-exterior continuation argument.  For `n=5,6`, every speed-admissible
degree-three exterior Blaschke configuration with product sufficiently close
to the sharp endpoint has an attached radial barrier no larger than the
regular comparator.

The endpoint is cubic, not quadratic: the regular ray profile has vanishing
first and second radial derivatives.  The proof combines the quantitative
Clark-fibre stability theorem with an exact scaled selector calculation.  A
companion symbolic checker replays all endpoint jets, the speed-kernel
elimination, and the positive quadratic loss.

The resulting terminal collar is non-explicit.  It removes saturation as an
open escape route; nonregular contacts in the remaining compact middle
capacity interval are not addressed here.

## 1. The cubic regular scale

Fix `n in {5,6}`, put

```text
p_0=(n-3)/(n+3),       delta=p_0-p,       tau=sqrt(delta).
```

For the regular triangle the log radial profile is

```text
L_n(q,p)=-n log q+log(q^3-p)-log(1-pq^3).             (1)
```

At `(q,p)=(1,p_0)` exact differentiation gives

```text
L_q=L_qq=0,
L_qqq=n(n-3)(n+3)/2=:C_n>0,
L_qqqq=-3n(n-3)(n+3),
partial_p L_q=(n+3)^2/6=:A_n.                         (2)
```

Thus, with `q=1-tau X`,

```text
tau^(-3)L_n(1-tau X,p_0-tau^2)
  -> A_n X-(C_n/6)X^3.                                (3)
```

The limiting maximizer and maximum are

```text
X_n=sqrt(2A_n/C_n)
   =sqrt(2(n+3)/(3n(n-3))),
K_n=(2/3)A_n X_n=(n+3)^2 X_n/9.                       (4)
```

In particular

```text
n=5: X_5=4/sqrt(30),   K_5=256/(9sqrt(30)),
n=6: X_6=1/sqrt(3),    K_6=3sqrt(3),                  (5)
```

and

```text
log R_n(p)=K_n delta^(3/2)+O(delta^2).                 (6)
```

## 2. The speed constraint selects an exact kernel

Write `s=p_0^(1/3)`.  A square-root-scale perturbation of the endpoint
triangle has, after rotation,

```text
a_j=s exp(tau x_j+O(tau^2))
      exp(i[2pi j/3+tau phi_j+O(tau^2)]),
sum x_j=sum phi_j=0.                                  (7)
```

At the boundary direction of `a_j`, the Blaschke speed is

```text
g_j=sum_k (1-r_k^2)
              /[1-2r_k cos(theta_k-theta_j)+r_k^2].   (8)
```

Let `ell_j` be its first variation in `tau` at the regular endpoint.
Direct differentiation gives

```text
ell_0+ell_1+ell_2=0.                                  (9)
```

Speed admissibility says `ell_j<=0`.  Hence all three vanish.  With
`x_2=-x_0-x_1` and `phi_2=-phi_0-phi_1`, their unique simultaneous kernel is

```text
phi_0= sqrt(3)(x_0+2x_1)T(s)/[3(s-1)^3(s+1)],
phi_1=-sqrt(3)(2x_0+x_1)T(s)/[3(s-1)^3(s+1)],          (10)

T(s)=s^4+2s^3+2s+1.
```

Thus every nonzero admissible square-root tangent is encoded by the two
radial variables `x_0,x_1`; there is no separate angular escape.

## 3. Exact second-order speed loss

Write the attached speed deficits as

```text
n-g_j=tau^2 sigma_j+o(tau^2),       sigma_j>=0.        (11)
```

The fixed-product condition contributes

```text
sum_j (log r_j-log s)=-tau^2/p_0+o(tau^2).             (12)
```

Substitute (10)--(12) in the second variation of the sum of (8).  Exact
simplification gives

```text
sigma_0+sigma_1+sigma_2=3A_n-Q_s(x_0,x_1),            (13)

Q_s(x_0,x_1)=D(s)(x_0^2+x_0x_1+x_1^2),               (14)

D(s)=18s^2(s^2-s+1)(s^2+4s+1)(4s^4+5s^3+5s+4)
     /[(1-s)^5(1+s)(s^2+s+1)^3] >0.                  (15)
```

Consequently

```text
min_j sigma_j <= A_n-Q_s(x_0,x_1)/3 <=A_n,            (16)
```

strictly for every nonzero square-root tangent.

There is one further potentially dangerous scaled jet.  If `L_j(q)` is the
log barrier on the ray attached to `a_j`, then `L_j,qq(1)=0` at the endpoint.
Its first configuration variation could have produced a term proportional
to `tau^3 X^2`.  On the exact speed kernel (10), however,

```text
partial_tau L_j,qq(1)|_(tau=0)=0,       j=0,1,2.       (17)
```

The checker verifies this cancellation identically.  It is the reason the
Clark square-root rate is exactly strong enough.

## 4. The limiting cubic selector

Taylor expansion of the general attached profile, using (11), (17), and
(2), now gives uniformly for bounded `X>=0`

```text
tau^(-3)L_j(1-tau X)
 -> sigma_j X-(C_n/6)X^3.                             (18)
```

For `sigma>=0`, the maximum of the right side is

```text
M_n(sigma)=(2/3)sigma sqrt(2sigma/C_n),                (19)
```

a strictly increasing function of `sigma`.  Therefore (16) implies

```text
min_j M_n(sigma_j)
 <= M_n(A_n-Q_s/3)
 <= M_n(A_n)=K_n,                                     (20)
```

with strict inequality for every nonzero square-root tangent.

This is the complete endpoint cubic atlas: the three selector chambers are
simply the three choices of the smallest `sigma_j`, and their common upper
envelope is controlled by the positive form (14).

## 5. From the limiting atlas to a genuine terminal collar

We use the following standard scaled version of the robust min-kernel lemma.

> **Scaled cubic lemma.**  Suppose an analytic family of three attached
> profiles has: (i) the common cubic endpoint jet (2); (ii) a speed-admissible
> first-order kernel of constant rank; (iii) the cancellation (17); and (iv)
> a positive-definite loss (13)--(15).  Suppose also that, at every positive
> parameter, the regular orbit has the strict finite mixed-kernel stability
> property.  Then the limiting inequality (20) persists in a full
> neighbourhood of the endpoint, with equality only on the regular orbit.

### Proof of the lemma

Work in fixed-product log-radius and angle coordinates `z`, centred at the
regular triangle of the **same** product, and quotient the common rotation.
The three endpoint zeros are simple and separated.  Hence the Clark bound
`distance=O(tau)`, after its unique matching and one rotation, is equivalent
to

```text
|z|<=C tau                                                   (21a)
```

in these analytic coordinates.  Relabelling is fixed by the three disjoint
endpoint zero disks; there is no hidden orbit direction.

Put the ray displacement and `z` on the common `tau` scale, `z=tau x`.
The endpoint cubic jet confines every competing ray optimizer to a fixed
compact `X` interval.  On each closed scaled annulus
`epsilon<=|x|<=C`, speed admissibility forces the limiting first variation
onto (10), and (20) has a uniform strict gap.  Analytic convergence of the
scaled profiles preserves it.

It remains to rule out the multiscale regime `x=o(1)`.  Here the exact finite
regular first-variation formulas have a single factor `1-q_reg`, with
`(1-q_reg)/tau ->X_n`; after division by `tau` their simultaneous kernel has
constant rank.  If `K_tau` denotes that kernel, compactness of the unit
sphere gives

```text
min_j DG_j(tau,0)[z]
 <=-c tau dist(z,K_tau).                                (21b)
```

On `K_tau`, the summed optimized Hessian has exactly one factor `1-q_reg`.
The endpoint sign audit (22a) below therefore gives

```text
sum_j D^2G_j(tau,0)[w,w] <=-c tau |w|^2,
                                  w in K_tau.           (21c)
```

The weighted Taylor expansion behind (18) is uniform.  After regular
equality and the first-order identities are removed, its scaled remainders
are

```text
O(tau^4|x|^2+tau^3|x|^3),                              (21)
```

against the main `-c tau^3|x|^2` kernel gap.  Thus they are absorbed by first
choosing the scaled ball and then `tau` small.

Equivalently, a contradiction sequence with `z=o(tau)` may be normalized by
its actual norm `rho=|z|`.  If the limiting direction is off `K_tau`, (21b)
gives a negative term of order `tau rho`, dominating the higher terms.  If
it lies in `K_tau`, (21c) gives a negative summed term of order
`tau rho^2`; the cubic remainder is `O(rho^3)=o(tau rho^2)`.  In either case
at least one barrier is strictly below the regular one.  This explicit
second normalization rules out an arbitrarily thin `o(tau)` escape and also
excludes a second equality orbit.  The lemma follows.  ∎

For completeness, the strict finite kernel does not lose an extra order at
the endpoint.  In the notation of that theorem its Hessian has one explicit
factor `1-q`, and all remaining denominators have nonzero endpoint limits.
The only sign factor reduces, at `q=1` and `s^3=p_0`, to

```text
n=5: -9(1748s^2+113s-43)/64,
n=6: -2(3810s^2+193s-81)/27,                          (22a)
```

times the positive factor `s^2+s+1`.  Both expressions are strictly
negative already from `s>1/2`.  Thus the kernel Hessian divided by `tau`
has a negative-definite endpoint limit.  Similarly, the exact first-order
selector formulas have one factor `1-q`, and after division by `tau` retain
constant rank.  These observations justify the two uniform absorptions in
(21), rather than merely invoking pointwise strictness.

The hypotheses are exact source-current theorems: (2), (9)--(17) are proved
here; strict positive-parameter stability is
`ThreeExteriorFiniteRegularMixedKernelStability.md`.
`ThreeExteriorQuantitativeSaturationStability.md` supplies

```text
distance(configuration,endpoint regular orbit)=O(tau), (22)
```

so every speed-admissible terminal configuration enters the scaled compact
set to which the lemma applies.  We obtain:

> **Theorem (terminal saturation selector).**  For `n=5,6` there exists
>
> ```text
> eta_n>0                                                    (23)
> ```
>
> such that, whenever
>
> ```text
> p_0-eta_n<p<p_0,       max_T |B'|<=n,                (24)
> ```
>
> at least one actual zero-attached radial barrier satisfies
>
> ```text
> V_j<=R_n(p).                                          (25)
> ```
>
> Equality occurs only for the regular triangle modulo rotation and
> relabelling.

The endpoint `p=p_0` itself is the regular rigidity theorem and has barrier
one, so the closed terminal interval is covered as well.

## 6. Exact remaining boundary

The saturation branch in
`ThreeExteriorFiniteCapacityContinuationReduction.md` is now closed.  The
three-exterior selector is proved at low capacity and in a terminal interval
below `p_0`.  What remains is a compact middle-capacity contact problem:
exclude a nonregular interior KKT contact or a contact on the closed speed
boundary.  No numerical value of `eta_n`, no complete middle-capacity atlas,
and no unrestricted Erdős 1041 theorem are claimed here.
