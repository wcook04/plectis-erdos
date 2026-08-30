# Erdős 1041: the three-exterior gap is a Green-potential polarization problem

## Status

This note replaces the coupled `m=3` radial formula by its intrinsic unit-disc
form and records the sharp remaining inequality.  The change of variables is
exact.  The proposed radius-weighted logarithmic certificate and its
monotonicity are computational conjectures, not theorems.  The unrestricted
Erdős 1041 problem remains open.

## Exact intrinsic reformulation

Let

```text
B(z)=unit*product_(k=1)^3 (z-a_k)/(1-conj(a_k)z),
a_k=r_k exp(i theta_k),   p=r_1r_2r_3,
```

and put `q=1/x`.  On the root-attached exterior ray used in
`ThreeExteriorEqualRadiusAngularEnvelope.md`, direct inversion gives

```text
F_j(x)/x^n = |B(q exp(i theta_j))|.                       (1)
```

Indeed every factor is the pseudohyperbolic distance

```text
rho_D(q exp(i theta_j),a_k)
 = |q exp(i theta_j)-a_k|/|1-conj(a_k)q exp(i theta_j)|. (2)
```

For the regular triangle, `s=p^(1/3)`, the product collapses to

```text
T_p(q)=(q^3-p)/(1-pq^3).                                 (3)
```

Thus the pointwise coupled conjecture is the following clean statement.

> **GP3.** If `max r_k <= q < 1`, then
>
> ```text
> min_j |B(q exp(i theta_j))| <= T_p(q).                 (4)
> ```

The regular equal-radius triangle is an equality case.  Equation (4) is
independent of the ambient polynomial degree `n`.

## Radius-weighted certificate

The equal-weight product of the three ray values is false.  The numerically
rigid replacement is

```text
D(q)=sum_j r_j log|B(q exp(i theta_j))|
     -(r_1+r_2+r_3)log T_p(q) <= 0.                      (5)
```

Because all weights are positive, (5) implies (4).  Fixed-seed global searches
over all three radii, `q`, and two independent angles find no positive value of
`D`.  Replacing the weights `r_j` by `r_j^alpha` produces counterexamples for
at least `alpha=1/4` and `alpha=1/2`; the linear radius weight is structural,
not cosmetic.

There is a sharper one-variable reduction.  One has `D(1)=0`, and

```text
d/dq log rho_D(q exp(i theta),r exp(i phi))
 = (1-r^2)[q(1+r^2)-r cos(theta-phi)(1+q^2)]
   /[(q^2-2qr cos(theta-phi)+r^2)
     (1-2qr cos(theta-phi)+q^2r^2)].                    (6)
```

Also

```text
d/dq log T_p(q)=3q^2/(q^3-p)+3pq^2/(1-pq^3).            (7)
```

Therefore (5) follows from the explicit rational inequality

```text
sum_(j,k) r_j H(q,r_k,cos(theta_j-theta_k))
 >= (sum_j r_j)[3q^2/(q^3-p)+3pq^2/(1-pq^3)],           (8)
```

where `H` is the right side of (6).  Deterministic differential evolution
again minimizes (8) at the regular triangle to numerical precision.  The next
angular step is now exact.  The kernel can be written

```text
H(q,r,c)=(q-rc)/(q^2+r^2-2qrc)
         -(qr^2-rc)/(1+q^2r^2-2qrc),                   (9)
```

and therefore

```text
d^2H/dc^2=4qr^2[(q^2-r^2)/(q^2+r^2-2qrc)^3
                +(1-q^2r^2)/(1+q^2r^2-2qrc)^3] > 0.  (10)
```

Thus every pair kernel

```text
K_ij(c)=r_i H(q,r_j,c)+r_j H(q,r_i,c)
```

is strictly convex and lies above its tangent at `c=-1/2`.  Minimizing the
three tangent terms is the exact weighted cosine problem

```text
min_[A+B+C=0] alpha*cos(A)+beta*cos(B)+gamma*cos(C).
```

Its minimum is the least of the two endpoint values

```text
gamma-alpha-beta,   -gamma-|alpha-beta|,
```

and, when its stationary cosine lies in `[-1,1]`,

```text
-(alpha^2 beta^2+alpha^2 gamma^2+beta^2 gamma^2)
 /(2 alpha beta gamma).                                (11)
```

The stationary value in (11) is admissible exactly when

```text
1/alpha, 1/beta, 1/gamma
```

are the side lengths of a (possibly degenerate) triangle.  This follows from
the stationary equations

```text
alpha sin(A)=beta sin(B)=gamma sin(C)
```

and the sine law.  Outside this reciprocal-triangle region the minimum is an
endpoint value.  Thus the radial problem is genuinely piecewise, with a
fully explicit semialgebraic branch condition.

There are two useful exact checks on the stationary branch.  First, on the
regular radial locus `r_1=r_2=r_3` its residual is identically zero for every
`r_1<q<1`.  Second, on the isosceles slice `(r_1,r_2,r_3)=(x,x,z)`, the reduced
numerator of the stationary residual has the exact factor

```text
(x-z)^2.                                                (12)
```

The replay checker verifies (12) without expanding its large quotient: both
the residual and its first `z` derivative vanish identically at `z=x`.
The quotient after (12) has mixed monomial signs, so (12) is an equality-locus
and local-structure theorem, not by itself a global positivity proof.

The sign of its leading transverse coefficient can nevertheless be proved
exactly.  Put `x=q u` and `t=q^2`, so `0<u,t<1`.  If `E(x,x,z;q)` denotes the
stationary radial residual, termwise differentiation and exact reduction give

```text
(1/2) partial_z^2 E(x,x,z;q)|_(z=x) = u P(t,u)/Q(q,u), (13)
```

where `P` has bidegree `(15,25)`.  The denominator `Q` is strictly negative:
its sign-bearing factors are

```text
(u-1)^3 (qu-1) (q^2u-1)^3,
```

and its remaining nontrivial factor has the manifestly positive decomposition

```text
(1-u^2)+q^2(1-q^4u^2)+q^6u^4+q^4u^4
 +4q^4u^3+4q^4u^2+4q^2u^2+4q^2u.
```

For the numerator, the replay converts `P` exactly to the tensor Bernstein
basis on `[0,1]^2`.  All `16*26=416` coefficients are nonpositive and `405`
are strictly negative.  Bernstein basis functions are positive in the open
square, hence `P(t,u)<0`; together with `Q(q,u)<0`, (13) is strictly positive.
Thus the regular radial locus is a strict transverse local minimum of the
stationary tangent residual throughout the full domain `0<x<q<1`.

### Tangent (simplex) curvature certificate

The transverse certificate above moves `z` at fixed `x`, so it proves the
second variation only in the direction `(0,0,1)`, which is not tangent to the
product-preserving simplex `r_1r_2r_3=p`.  The missing tangent direction is
now closed by an exact certificate of the same shape.  Along the exactly
product-preserving isosceles path

```text
r_1=r_2=s*w,   r_3=s/w^2,   p=s^3 for every w,
```

the stationary residual satisfies, with `u=s/q` and `t=q^2`,

```text
(w d/dw) S|_(w=1)      = 0,                       (14)
(w d/dw)^2 S|_(w=1)    = 18 u^3 Nhat(t,u)/D(q,u) > 0,   (15)
```

where

```text
D=(u-1)^3(qu-1)(qu+1)(q^2u-1)^3(u^2+u+1)^4(q^4u^2+q^2u+1)^4 E(q,u),
E=(1-u^2)+q^2(1-q^4u^2)+q^4u^4(1+q^2)+4q^4u^3+4q^2u^2(1+q^2)+4q^2u,
```

is strictly negative on the open unit square (three sign-bearing factors are
negative and the tail `E` is a sum of nonnegative terms), and `Nhat` has
bidegree `(15,25)`: all `416` tensor Bernstein coefficients of `Nhat` on
`[0,1]^2` are nonpositive with `405` strictly negative, so `Nhat<0` and (15)
is strictly positive.  Equation (14) is the exact infinitesimal form of the
S_3 symmetry: the surplus vanishes on the whole regular diagonal.

Together the two certificates give the full local picture at the regular
triangle.  The surplus is S_3-invariant in the radii, so its Hessian at the
diagonal has the form `aJ+bI`; it vanishes along the diagonal (the surplus is
identically zero there), hence `3a+b=0` and `a+b=2b/3`.  The transverse
certificate proves `a+b>0` and the tangent certificate proves `b>0`; each is
equivalent to the other given the diagonal vanishing, and together they show
the Hessian is positive semidefinite with kernel exactly the diagonal
direction.  The regular triangle is therefore a strict local minimizer of the
stationary surplus on every product-preserving simplex, in every direction.

### Isosceles slice: the surplus inequality is proved

The full isosceles slice is now an exact theorem, not evidence.  With
`u=x/q`, `w=z/q`, `t=q^2`, the stationary surplus factors exactly as

```text
S(q;x,x,z) = q^2 (u-w)^2 Num(t,u,w)/Den(q,u,w),                 (16)
```

where `Den` is strictly negative on the open unit box (seven strictly
negative sign-bearing factors `(1-u),(1-w),(1-qu),(1-q^2u),(1-q^2w),
(1-u^2w),(1-q^6u^2w)` and a manifestly positive remaining part with the same
positive tail `E` as above), and `-Num` has bidegree `(21,20,20)` in
`(t,u,w)`: all `22*21*21 = 9702` tensor Bernstein coefficients on `[0,1]^3`
are nonnegative, `9569` strictly positive and `133` exactly zero.  Hence

```text
S(q;x,x,z) >= 0   for all   0 < x, z <= q < 1,                  (17)
```

with equality only on the diagonal `z=x`.  By S_3 symmetry this covers every
isosceles configuration.  Together with the two local certificates, the
radial surplus is proved on the whole diagonal neighbourhood and on all
isosceles slices; the remaining gap is strictly the fully coupled case of
three distinct radii.

### Evidence base for the remaining coupled case

Three computation families back the coupled inequality, and three shortcuts
are eliminated.

1. Angular-layer validation.  Direct two-angle minimization of the weighted
   cosine sum confirms the closed-form minimum in both branches: the
   stationary value (11) where the reciprocals form a triangle, and the
   endpoint value `- (alpha+beta+gamma) + 2*min(alpha,beta,gamma)` outside it
   (the violating weight carries the `+1` cosine).  No mismatch at grid
   precision in randomized trials.
2. In-domain global search.  A 60-digit randomized search over
   `0<q<1`, `0<r_k<=q` with the branch condition enforced (4000
   configurations, 1047 on the endpoint branch), plus 60 adversarial
   hill-climbs on the operative surplus, found no negative value; the search
   converges to the two equality regimes (the diagonal and the collapse
   corner) and nowhere else.
3. Scale structure.  At the collapse corner the surplus is exactly quadratic
   on the endpoint branch, `S_end = (1+q^2)(r_1+r_2-r_3)^2/q^2 + O(r^3)`
   with a perfect-square leading form, and exactly cubic on the stationary
   branch with leading form `3(1+q^4)/(2q^3)[2sum r^3 - sum_sym r^2 r']`,
   which is `Schur(r) + (sum r^3 - 3r_1r_2r_3) >= 0` by Schur and AM-GM.
4. Schur-convexity fails.  In log-radius coordinates on the
   product-preserving simplex the operative surplus is not Schur-convex:
   randomized in-domain probes found negative values of
   `(v_i-v_j)(dS/dv_i-dS/dv_j)` and negative diagonal second derivatives.
   No radius-smoothing (equalization) reduction of the global inequality to
   the isosceles slice is therefore available, and attempts along that route
   should not be retried without a new idea.
5. Scale monotonicity fails.  The ratio `S_stat(erho)/e^3` is not
   nondecreasing in the overall scale: 181 violations in 6000 randomized
   checks, all at two-scale corners (two roots collapsed, the third at a
   finite fraction of `q`), and the exact cubic lift `S_stat >= e^3 C_3`
   fails by a small margin at the same corners although the surplus itself
   stays positive there.  Monotonicity-based lift arguments are eliminated.
6. Coefficientwise positivity fails.  In the scale expansion
   `S_stat(erho) = sum_k e^k C_k` the forms `C_4` and `C_6` are positive on
   randomized samples but `C_5` and `C_7` are negative at extreme ratios, so
   no all-coefficients-positive certificate of the scale expansion exists.
7. The isosceles slices are not global transverse minima.  The splitting
   curvature `d^2/du^2 S(q; x+u, x-u, z)|_(u=0)` is negative in a thin
   small-pair corner: all randomized negatives have `x/q <~ 0.02` and
   `z/x >~ 10` (worst `-20.4` at `q=0.197`, `x/q=0.0057`, `z/q=0.32`), while
   near the diagonal the certified curvature is positive.  Tube arguments
   that would extend the slice theorem by transverse monotonicity are
   therefore unavailable; the coupled positivity is a genuinely global
   coupling.
8. Endpoint-cone certificate state.  The endpoint-branch operative surplus
   `S_end` on the dominant-radius cone has a fully verified cleared
   numerator `N_end = S_end * D_0` (exact rational identity, 54336 terms,
   degree 54; `D_0 > 0` on the domain).  After the simplex-to-box
   parametrization its tensor Bernstein form on `[0,1]^4` (degrees
   `(27,36,36,13)`, 536648 coefficients) has exactly `590` negative
   coefficients (`0.11%`), all confined to the high-`t` (q near 1), tiny-`b`
   corner, worst `-0.0163`.  Targeted subdivision improves the bounds but
   re-exposes negativity along the branch-boundary surface
   `alpha_12(alpha_13+alpha_23) = alpha_13 alpha_23` (equivalently
   `b ~ x`), where the endpoint and stationary bounds coincide and the
   surplus is only of order `e^3`.  The residual of the endpoint branch is
   therefore exactly a neighbourhood of the branch-boundary layer; away from
   it the numerator's Bernstein form is within targeted subdivision of a
   complete certificate.

Near `q=r_1=r_2=r_3` the self terms and the regular comparator separately
diverge while their difference remains exactly zero.  Ordinary double
precision can consequently fabricate large negative residuals (values near
`-3e5` were observed).  The checker now re-evaluates two such witnesses at
100 decimal digits and recovers zero below `1e-75`.  Future falsification of
the radial surplus must use arbitrary precision or a cancellation-free
normal form in this boundary layer.

Consequently the only unproved part of (8) is the radial surplus inequality
in the fully coupled case of three distinct radii, after subtracting (11) in
the reciprocal-triangle region or the active endpoint outside it.  The local
structure at the equality locus is certified in every direction, the full
isosceles slices are proved by (16)-(17), and the Schur-smoothing,
scale-monotonicity, and coefficientwise shortcuts are all eliminated.
Computation with the branch condition enforced finds no negative value;
endpoint minima approach a boundary equality regime, while apparent interior
negatives collapse to regular equality under high precision.  This is
evidence, not a proof.  No angular search and no maximization in the ambient
polynomial degree remains.

## Relation to sharp Blaschke symmetrization literature

Dubinin proved that among degree-`d` finite Blaschke products with `C(0)=0`
and fixed `|C'(0)|`, the rotationally symmetric product

```text
C_c(z)=z(z^(d-1)-c)/(1-cz^(d-1))
```

maximizes the least modulus of a critical value (V. N. Dubinin, *An upper
bound for the least critical values of finite Blaschke products*, Sbornik:
Mathematics 213:6 (2022), 744--751, DOI `10.1070/SM9679`).  Its proof uses
dissymmetrization of the inverse Riemann surface and is strong evidence that
the regular object in (3) is the correct extremal object.

There is, however, an exact applicability firewall.  The merge function here
is the meromorphic inner quotient

```text
z^n/B(z),
```

not an analytic finite Blaschke product normalized by a nonzero derivative at
the origin.  Dubinin's theorem does not directly imply GP3 or the merge
envelope.  A valid use requires either proving (8) or extending the
dissymmetrization theorem to this prescribed zero/pole quotient.

## Effect on the full envelope

GP3 would prove the pointwise minimum envelope on the common radial domain.
It does not by itself prove that one fixed attached ray has optimized barrier
at most the regular barrier: the minimizing index may depend on `q`.  The
remaining `m=3` bridge therefore has two named obligations:

1. prove the rational derivative inequality (8), hence GP3;
2. prove a selector/interval lemma converting pointwise GP3 into
   `min_j max_q q^(-n)|B(q exp(i theta_j))| <= M_sym`.

This is strictly narrower than the previous coupled-angle/coupled-radius
statement and prevents the already-refuted equal-product and static-selector
shortcuts from being retried.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_three_exterior_green_polarization.py
python3 research_corpus/Erdos1041/scripts/check_erdos1041_gp3_simplex_curvature.py
python3 research_corpus/Erdos1041/scripts/check_erdos1041_gp3_isosceles_slice.py
```

The second checker proves the tangent (simplex) curvature certificate (14)-(15);
the third proves the full isosceles slice (16)-(17).  The disposable evidence
probe behind the evidence base above is
`scripts/explore_erdos1041_radial_surplus.py` (validation, isosceles scan,
Schur probe, global search); it is evidence, not a proof surface.
