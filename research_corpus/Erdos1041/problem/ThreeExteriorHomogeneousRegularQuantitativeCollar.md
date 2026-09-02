# Erdős 1041: an exact `1/50` joint collar at the homogeneous regular three-ray equality

## Status

This note replaces the qualitative equality excision in
`ThreeExteriorLowCapacityRegularKernelSecondVariation.md` by a fully explicit
rational neighbourhood in degrees five and six.  It treats the two radial
shape variables, all three angular cosine perturbations, and the displacement
of the ray parameter from its regular maximizer simultaneously.  On each of
the three first-variation selector cones, the corresponding actual
root-attached ray is no larger than the regular homogeneous comparator
throughout that joint collar.

This is a local theorem for the leading homogeneous three-exterior model.  It
does not certify the compact complement, perform the finite-capacity transfer,
or prove Erdős #1041.

## Coordinates

Fix `n in {5,6}`, put `d=n-3`, and let

```text
t^3=d/n,                 C_n=t^d(1-t^3).
```

Use the exact product-one radial chart

```text
b_0=1+X,    b_1=1+Y,    b_2=1/((1+X)(1+Y)).             (1)
```

Write the three cosine perturbations as

```text
c_01=-1/2+alpha,  c_02=-1/2+beta,  c_12=-1/2+gamma.     (2)
```

Set `A=3(1+t)` and `B=2(1-t)`.  The normalized first variations of the
three squared ray profiles at the regular maximizing point are

```text
L_0=A X+B(alpha+beta),
L_1=A Y+B(alpha+gamma),
L_2=-A(X+Y)+B(beta+gamma).                              (3)
```

For the selector cone of ray zero put

```text
M=(L_0+L_1+L_2)/3,
U=L_0-L_1,
V=L_0-L_2.                                             (4)
```

Conversely, define

```text
L_0=M+(U+V)/3,
L_1=M+(-2U+V)/3,
L_2=M+(U-2V)/3,                                        (5)

N_0=L_0-A X,   N_1=L_1-A Y,   N_2=L_2+A(X+Y),
B alpha=(N_0+N_1-N_2)/2,
B beta =(N_0+N_2-N_1)/2,
B gamma=(N_1+N_2-N_0)/2.                              (6)
```

Thus `M,U,V>=0` says exactly that ray zero has the largest nonnegative
first-order gap.  Genuine angle triples satisfy
`alpha+beta+gamma>=0`, hence `M>=0`; the theorem is proved on the larger
relaxed cosine chart and does not use the Gram determinant.

## Quantitative collar theorem

Put

```text
delta=1/50,                 q=t+Z.                      (7)
```

> **Theorem.**  Suppose
>
> ```text
> 0<=M,U,V<=delta,        |X|,|Y|,|Z|<=delta.           (8)
> ```
>
> Define the radii and cosines by (1), (2), and (5)--(6).  Then the
> homogeneous squared profile on the ray attached to root zero satisfies
>
> ```text
> q^(2d) product_(k=0)^2
>   (1-2q b_k c_0k+q^2 b_k^2) <= C_n^2,                (9)
> ```
>
> where `c_00=1`.  The two cyclic versions hold on the selector cones of
> rays one and two.

The statement includes the ray-radius displacement `Z`; it is not merely a
certificate at the regular maximizing sample.

## Exact proof

Let `R=(1+X)(1+Y)`.  Clear the positive denominators in (9) and define

```text
P_n=9 B^2 R^2 (C_n^2-H_0(q)^2).                        (10)
```

After substituting (5)--(6), this is a polynomial over `Q(t)` in
`M,U,V,X,Y,Z`.  The exact checker proves two uniform facts on the whole box
(8), using tensor-product Bernstein coefficients on rational boxes enclosing
the real roots

```text
7368/10000 < (2/5)^(1/3) < 7369/10000,
7937/10000 < (1/2)^(1/3) < 7938/10000.                 (11)
```

First,

```text
partial_M P_n>0,   partial_U P_n>0,   partial_V P_n>0. (12)
```

Therefore `P_n(M,U,V,X,Y,Z)>=P_n(0,0,0,X,Y,Z)`.

Second, on the kernel slice `M=U=V=0`, the Hessian of `P_n` in
`(X,Y,Z)` is positive definite throughout the cube.  The checker verifies
strict positivity of all three leading principal minors by exact Bernstein
coefficients.  At the origin,

```text
P_n=partial_X P_n=partial_Y P_n=partial_Z P_n=0,        (13)
```

with (13) checked exactly modulo `t^3-d/n`.  Strict convexity now gives
`P_n(0,0,0,X,Y,Z)>=0`; (12) gives the same conclusion on the full selector
box.  Since every factor cleared in (10) is positive for `delta=1/50`, this
is exactly (9).  Cyclic symmetry proves the other two cones.  ∎

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_homogeneous_regular_quantitative_collar.py
```

The replay constructs the full joint polynomial rather than reading stored
coefficients.  In each degree it checks three seven-variable monotonicity
certificates and three four-variable Hessian-pivot certificates, all with
exact rational arithmetic.

## Exact boundary

The collar removes a genuine singularity from a future compact branch-and-
bound proof: the regular equality is now surrounded by a proved open region,
so the complement has strict margin.  What remains is the finite exact cover
of the compact homogeneous domain outside the three cyclic `1/50` collars,
followed by the separate finite-capacity transfer.  No claim about either
remainder is made here.

```text
tao_pipeline_receipt:
  input_stage: qualitative local generation
  output_stage: exact quantitative verification
  artifact: ThreeExteriorHomogeneousRegularQuantitativeCollar.md plus exact Bernstein checker
  human_understanding_delta: the regular equality is no longer a puncture requiring an asymptotic argument; each selector cone has an explicit 1/50 joint radial-angular-ray-parameter neighborhood
  verification_state: ordinary exact proof with a bit-replayable rational Bernstein certificate
  publication_or_review_state: source-level research result, not independently reviewed
  canonicalization_state: quantitative replacement for the earlier regular-kernel second-variation lemma in the homogeneous adaptive-minray family
  unresolved_downstream_bottleneck: exact branch-and-bound cover of the compact homogeneous complement, then finite-capacity transfer
  next_stage_owner: active Erdős 1041 exterior-selector proof lane

paper_assimilation:
  paper: erdos-1041-lemniscate-newton-flow
  section: exterior finite-Blaschke adaptive selector
  canonical_mechanism_family: low_capacity_adaptive_minray
  relation: exact local input to the homogeneous three-exterior compact closure, not a parent closure
  understanding_delta: the three linear selector cones plus uniform kernel convexity resolve the coupled equality geometry quantitatively
  evidence_boundary: degrees five and six, homogeneous leading model, joint 1/50 coordinate collar
  hard_step: strict seven-variable selector monotonicity and uniform three-variable Hessian positivity by exact Bernstein coefficients
  meaningful_failed_route: a qualitative Taylor argument could not be consumed by a finite box atlas
  open_remainder: compact homogeneous complement and finite-capacity transfer
```
