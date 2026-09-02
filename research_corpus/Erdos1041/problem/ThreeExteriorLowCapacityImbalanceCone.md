# Erdős 1041: the homogeneous low-capacity three-ray envelope outside a compact radial cone

## Status

This note proves an angle-free part of the homogeneous low-capacity
three-exterior selector problem in **every ambient degree `n>=4`**.  It gives
one actual root-attached ray whose full leading-order barrier is no larger
than the regular-triangle leading barrier whenever the normalized radii are
sufficiently unequal.  Consequently the only unresolved part of the
homogeneous `m=3` min-ray inequality is a compact near-equal radial box.

It is an abstract exterior finite-Blaschke statement.  It does not prove the
finite-capacity envelope, a polynomial realization, or Erdős #1041.

## The homogeneous barrier

Let `b_1,b_2,b_3>0` satisfy

```text
b_1 b_2 b_3=1,
```

and let `u_1,u_2,u_3` be unit complex numbers.  In the small-capacity scaling
`a_j=epsilon b_j u_j`, the leading barrier on the ray attached to `j` is

```text
H_(j,n)(y)=y^(-n) product_k |y u_j-b_k u_k|,
                    y>=b_j,       n>=4.                 (1)
```

Put `d=n-3`.  The regular-triangle leading barrier is

```text
C_n=(3/d)(d/n)^(n/3).                                    (2)
```

Indeed, for a regular triangle with product one, the leading profile is
`y^(-n)(y^3-1)`, whose unique maximum has `y^3=n/d` and is (2).

## Imbalance-cone theorem

Put `B=max_j b_j`, choose `j` with `b_j=B`, and define

```text
z_n=(sqrt(1+4dn)-1)/(2d),
M_n=(z_n-1)(z_n+1)^2/z_n^n,
T_n=(M_n/C_n)^(1/d).                                     (3)
```

> **Theorem.**  If
>
> ```text
> B^d C_n >= M_n,                                        (4)
> ```
>
> then `sup_(y>=b_j) H_(j,n)(y)<=C_n`.  The selected curve is the
> actual ray attached to a largest-radius zero.

Numerically, the hypotheses are respectively

```text
B >= T_5=1.150373553830...,
B >= T_6=1.099043672131...,                              (5)
```

For orientation, `M_5=(822+82 sqrt(41))/3125` and
`M_6=(12881+2117 sqrt(73))/93312`.

### Proof

For `y>=B`, the own-root factor is exactly `y-B`, while both spectator
factors obey the triangle inequality.  Thus, on writing `y=Bz`,

```text
H_(j,n)(Bz)
 <=(Bz)^(-n)(Bz-B)(Bz+B)^2
 =B^(3-n) f_n(z),

f_n(z)=(z-1)(z+1)^2/z^n,             z>=1.              (6)
```

Its logarithmic derivative has the exact sign identity

```text
d/dz log f_n(z)=-(d z^2+z-n)/(z(z^2-1)).                (7)
```

The quadratic in (7) is strictly increasing on `[1,infinity)`, is `-2` at
one, and has its unique zero at `z_n`; hence `max f_n=M_n`.  Equation (6),
followed by (4), is the claim. ∎

## Consequence: the hard normalized region is compact

For an attempted counterexample in either degree, (4) must fail.  Therefore

```text
max_j b_j<T_n.
```

Since the product is one, every radius simultaneously obeys

```text
T_n^(-2)<b_j<T_n.                                       (9)
```

So the remaining homogeneous min-ray problem is not a large-radius or
vanishing-radius problem: it is a compact, product-normalized,
near-equal-radii problem with two angular variables.  This sharpens the
target for a finite selector-region certificate.

## Exact replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_low_capacity_imbalance_cone.py
```

The checker verifies the symbolic all-degree derivative identity and the two
original degree-five/six radical specializations using exact real algebra.

## Research receipt

```text
tao_pipeline_receipt:
  input_stage: generation
  output_stage: verification
  artifact: ThreeExteriorLowCapacityImbalanceCone.md plus exact symbolic checker
  human_understanding_delta: arbitrary angular data are harmless outside an explicit compact near-equal radial cone in every ambient degree; the largest-radius actual attachment ray already wins there
  verification_state: ordinary exact proof with symbolic real-algebra replay
  publication_or_review_state: source-level research result, not independently reviewed
  canonicalization_state: one cone theorem in the low-capacity adaptive-selector family
  unresolved_downstream_bottleneck: certify the compact box T_n^(-2)<b_j<T_n by an adaptive selector or min-ray argument
  next_stage_owner: active Erdős 1041 exterior-selector proof lane

paper_assimilation:
  paper: erdos-1041-lemniscate-newton-flow
  section: exterior finite-Blaschke adaptive selector
  canonical_mechanism_family: low_capacity_adaptive_minray
  relation: exact global reduction for the homogeneous m=3 model, not a parent closure
  understanding_delta: radial imbalance is not the source of the low-capacity difficulty; only a compact coupled angular/radial core survives
  evidence_boundary: leading small-capacity profile only, for every n>=4
  hard_step: the largest-root ray plus an exact one-variable extremum
  meaningful_failed_route: closest-root selection fails inside the surviving compact cone
  open_remainder: prove the compact min-ray or curved mountain-pass inequality
```
