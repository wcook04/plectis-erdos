# Erdős 1041: full finite regular mixed-kernel stability in degrees five and six

## Theorem

Fix `n in {5,6}` and put `d=n-3`.  Let three finite exterior zeros form a
regular triangle of radius `s`, with

```text
0 < p=s^3 < d/(n+3).
```

The strict upper bound is exactly the regular degree-three Blaschke speed
condition.  Let `R_n(p)` be the optimized common root-attached radial barrier.
On the fixed-product configuration manifold, the regular triangle is a
strict local maximizer of the **minimum** of the three optimized attached-ray
barriers.  More precisely:

1. every nonzero tangent outside the simultaneous first-order kernel makes
   at least one attached barrier descend to first order;
2. on the simultaneous kernel, the sum of the three optimized log barriers
   has strictly negative second variation.

Consequently every speed-admissible finite regular equality point has an
attachment-compatible neighborhood in which

```text
min_j V_j <= R_n(p),
```

with equality only at the regular triangle modulo rotation and relabeling.
This holds along the **entire** open regular equality curve, not merely at
small capacity or near the finite/homogeneous limit.

The neighborhood radius supplied here is pointwise in `p`; no uniform collar
as `p` tends to zero or to the speed-saturation endpoint is claimed.  Thus
this theorem removes the finite regular mixed tangent as a source of a local
counterexample, but does not by itself close the full compact near-equal
selector problem, GP3, the terminal block, or unrestricted Erdős 1041.

## 1. Regular ray and its stationary point

After rotation and inversion, the common regular profile is

```text
S_n(q)=q^(-n)(q^3-p)/(1-pq^3),       s<q<1.
```

The speed inequality makes its unique maximizer `q=q_n(s)` interior.  Its
stationary equation is

```text
n = 3q^3/(q^3-s^3) + 3s^3q^3/(1-s^3q^3).             (1)
```

Write a fixed-product radial tangent as

```text
r_j(epsilon)=s exp(epsilon x_j+O(epsilon^2)),
x_0+x_1+x_2=0,                                        (2)
```

and the pairwise cosine tangents as

```text
c_jk(epsilon)=-1/2+epsilon y_jk+O(epsilon^2),
y_01+y_02+y_12=0.                                     (3)
```

The last identity is the tangent equation for the planar Gram determinant

```text
G(c)=1+2c_01c_02c_12-c_01^2-c_02^2-c_12^2=0.         (4)
```

By symmetry, the sum of the three first variations vanishes.  Direct
differentiation shows that all three first variations vanish simultaneously
exactly when

```text
y_01=K(q,s)x_2,   y_02=K(q,s)x_1,   y_12=K(q,s)x_0,   (5)

K(q,s)=
  3(q^2s^3+q^2s+qs^4+q+s^3+s)
  /[2(q-s)(s-1)(s+1)(qs-1)].                          (6)
```

The coefficient `K` is positive on `0<s<q<1`.  If (5) fails, three real
first variations with zero sum cannot all be nonnegative, proving the
first-order part of the theorem.

## 2. Exact optimized Hessian on the kernel

For the second-order calculation, first use affine log-radius and cosine
coordinates and eliminate the optimizing-ray displacement by the envelope
identity

```text
L_env,ee = L_ee - L_eq^2/L_qq.                         (7)
```

For ray zero, after (1), (2), and (5), exact differentiation gives

```text
L_env,ee =
 [-qs(q-1)(q+1)] [A x_0^2+B x_0x_1+C x_1^2] / D,     (8)

D=2(q-s)^2(s-1)(s+1)(qs-1)^2
   (q^2+qs+s^2)^2(q^2s^2+qs+1)^2.                    (9)
```

The prefactor in square brackets is positive and `D<0`.  The coefficient
polynomials, replayed in the checker, satisfy

```text
B=C=-2H(q,s),                                         (10)

4AC-B^2 =
 -12(q^2+qs+s^2)(q^2s^2+qs+1)J(q,s)H(q,s),           (11)
```

where every coefficient of `J` is strictly positive.  Therefore the
quadratic form in (8) is positive definite as soon as

```text
H(q,s)<0.                                             (12)
```

The other two ray forms are relabelings.  Thus (12) makes every affine-chart
kernel variation strictly negative before the planar curvature correction.

## 3. The two stationary algebraic arcs

Put

```text
z=q/s,       t=s^2,       Y=z^3.
```

Equation (1) becomes

```text
t^3 = ((n-3)Y-n)/[Y(nY-n-3)],                         (13)
```

on

```text
n=5:  5/2 < Y < 4,
n=6:    2 < Y < 3.                                   (14)
```

Reducing `H(sz,s)/s^4` by (13) gives the exact identities

```text
n=5:
 H = -3(z^2+z+1)^2 P_5(t,z) / [z^2(5z^3-8)^2],       (15)

n=6:
 H =   -(z^2+z+1)^2 P_6(t,z) / [z^2(2z^3-3)^2].      (16)
```

Here `P_5` and `P_6` are the explicit degree `(2,10)` integer polynomials in
the replay script.  Their signs are certified **only on the stationary
curves**; they are not asserted positive on the surrounding rectangles.

The ordinate in (13) is increasing.  Exact differentiation gives

```text
n=5: (t^3)'=-10(Y-4)(Y-1)/[Y^2(5Y-8)^2] >0,
n=6: (t^3)'= -2(Y-3)(Y-1)/[Y^2(2Y-3)^2] >0.          (17)
```

Dyadic subdivision of the intervals (14), with 100-step exact rational
cube-root enclosures at every endpoint, proves

```text
P_5(t,z) > 0:   86 rational arc boxes, depth at most 23,
                 weakest recorded rational lower bound > 37/100;

P_6(t,z) > 0:  193 rational arc boxes, depth at most 27,
                 weakest recorded rational lower bound > 1/20.             (18)
```

Every interval operation in (18) uses `fractions.Fraction`; no floating-point
sign decision is made.  Equations (15)--(18) prove (12), hence positive
definiteness of the quadratic form in (8) throughout both complete arcs.

## 4. Returning from cosine coordinates to actual planar angles

The affine cosine calculation is not silently identified with an arbitrary
planar curve.  Differentiating (4) twice at the regular triangle gives

```text
sum_(j<k) c_jk'' = (2/3) sum_(j<k) y_jk^2.            (19)
```

For one off-diagonal factor, the common first derivative with respect to its
cosine is

```text
g = -qs(1-q^2)(1-s^2)
    /[(q^2+s^2+qs)(1+q^2s^2+qs)] < 0.                (20)
```

Each pair occurs in two of the three ray barriers.  Hence the total curvature
correction to their summed second variation is

```text
2g sum c_jk'' = (4g/3) sum y_jk^2 <= 0,               (21)
```

and is strict for a nonzero angular tangent.  The radial acceleration terms
cancel in the sum because each radius has the same summed coefficient and
fixed product gives `sum (log r_j)''=0`.  Thus actual planar curvature can
only strengthen the negative summed kernel variation.  At least one of the
three attached barriers therefore descends to second order.

The first-order alternative plus this negative kernel calculation is the
standard finite-dimensional second-order sufficient condition for a strict
local maximum of the minimum.  This proves the theorem.

## Replay and boundary

Run

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_finite_regular_mixed_kernel.py
```

The replay checks the Hessian determinant factorization, positivity of `J`,
both stationary reduction identities, both monotonicity identities, and all
279 exact rational arc boxes.  The proof applies for

```text
0<p<(n-3)/(n+3).
```

At `p=0` the finite chart degenerates; at the upper endpoint the optimizing
ray reaches `q=1` and the strict interior-envelope argument degenerates.
Those endpoint regimes require the existing low-capacity/homogeneous and
speed-saturation producers.  No unrestricted three-exterior selector or
parent theorem is claimed here.

## Research receipt

```text
tao_pipeline_receipt:
  input_stage: generation
  output_stage: verification
  artifact: ThreeExteriorFiniteRegularMixedKernelStability.md plus exact symbolic/rational checker
  human_understanding_delta: the entire finite regular equality curve is locally selector-stable; a putative counterexample cannot bifurcate through a first-order-flat mixed radial/angular mode
  verification_state: ordinary exact derivation plus bit-independent rational replay
  publication_or_review_state: source-level research result, not independently reviewed
  canonicalization_state: finite regular local-stability producer in the three-exterior selector family
  unresolved_downstream_bottleneck: turn pointwise regular collars and the outer-radial cone into a global compact near-equal selector certificate
  next_stage_owner: active Erdős 1041 exterior-selector proof lane

paper_assimilation:
  paper: erdos-1041-lemniscate-newton-flow
  section: exterior finite-Blaschke adaptive selector
  canonical_mechanism_family: finite_regular_mixed_kernel_stability
  relation: exact local producer supporting, not closing, the parent
  understanding_delta: all non-kernel directions switch linearly; the only simultaneous kernel has a strictly negative optimized Hessian on the full finite regular arc
  evidence_boundary: degrees five and six, fixed-product configurations, pointwise neighborhoods along the open regular curve
  hard_step: stationary-curve elimination of the mixed Hessian sign followed by exact rational arc subdivision
  meaningful_failed_route: a two-dimensional rectangular sign claim is false and unnecessary; the sign holds on the one-dimensional stationary algebraic curve
  open_remainder: quantitative globalization of the compact near-equal branch, GP3 complement, or another terminal-block producer
```
