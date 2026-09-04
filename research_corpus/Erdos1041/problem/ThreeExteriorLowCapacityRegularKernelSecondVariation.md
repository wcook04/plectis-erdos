# Erdős 1041: the regular low-capacity selector kernel is strictly second-order stable

## Status

This note gives the exact equality excision for the homogeneous three-exterior
min-ray problem at the regular triangle in **every ambient degree `n>=4`**.
It applies on a relaxed cosine domain, so it also applies to genuine angle
triples.  Every first-order-flat, product-preserving deformation makes all
three optimized log barriers strictly descend at second order.

This is a local homogeneous theorem.  It does not by itself certify the
compact complement, finite capacity, or the parent problem.

## Setup

Write `d=n-3`, let `t` be the regular maximizing reciprocal radius,

```text
t^3=d/n,                  n>=4,
```

and use logarithmic radii

```text
b_0=exp(epsilon p),
b_1=exp(epsilon r),
b_2=exp(-epsilon(p+r)).                                  (1)
```

Relax the angular Gram domain to cosine variables
`c_jk=-1/2+epsilon s_jk`; genuine unit directions are a subset of this local
relaxed domain.  Put

```text
L_j(q,epsilon)
 =d log q + (1/2) sum_k log(1-2q b_k c_jk+q^2 b_k^2).   (2)
```

Thus the leading barrier on ray `j` is `exp L_j`, and at the regular point
`epsilon=0`, `q=t`, all three equal the regular constant `C_n`.

## First-order-flat kernel

The first derivatives of the three optimized barriers vanish simultaneously
exactly on the two-parameter kernel

```text
s_01=3(p+r)(t+1)/(2(t-1)),
s_02=-3r(t+1)/(2(t-1)),
s_12=-3p(t+1)/(2(t-1)).                                 (3)
```

In particular `s_01+s_02+s_12=0`: this is tangent to the sharp angular
constraint `sum c_jk>=-3/2`.

For sufficiently small `epsilon`, the critical point near `t` is unique by
the implicit-function theorem; write `ell_j(epsilon)` for the optimized
log-barrier minus `log C_n`.  On (3),

```text
ell_j(0)=ell_j'(0)=0.                                    (4)
```

## Exact second-order separation

Let `Q=p^2+pr+r^2`, which is positive unless `(p,r)=(0,0)`.  The exact
envelope calculation is stronger than a summed descent: each of the three
optimized log barriers has strictly negative second derivative on every
nonzero kernel direction.  Here is an all-degree sign certificate.  Up to the
common positive denominator

```text
2(1-t)^2(1+t+t^2)^2/t,
```

each envelope Hessian is one of the quadratic forms

```text
A p^2+Bpr+B r^2,
B p^2+Bpr+A r^2,
A(p^2+r^2)+Cpr,                                        (5)
```

where

```text
A=t^4-7t^3-24t^2-7t+1,
B=14t^4-14t^3-72t^2-14t+14,
C=-12(1-t^2)^2.                                       (6)
```

For `n>=4`, one has `t>=4^(-1/3)>1/2`.  Thus `A,B<0`,
`B-4A=10t^4+14t^3+24t^2+14t+10>0`, and `C-2A=-B>0`.
These are exactly the leading-minor conditions proving every form in (5) is
strictly negative definite.  Their sum is

```text
sum_j ell_j''(0)
 =2t Q(4t^4-7t^3-30t^2-7t+4)
   / [2(1-t)^2(1+t+t^2)^2] <0.                           (7)
```

The individual negative-definiteness check gives `ell_j''(0)<0` for every `j` when
`(p,r)!=(0,0)`.  Taylor expansion and (4) therefore imply

```text
ell_j(epsilon)<0 for every j
```

for all sufficiently small nonzero `epsilon` on that direction.  Thus no
sample-versus-full selector comparison is needed inside the equality excision.

## Role in the compact selector problem

The imbalance-cone theorem reduces the global homogeneous problem to a compact
near-equal radial box.  Away from the regular equality point, a finite
selector-box certificate has strict margin.  At the point itself, all
transverse directions have a negative first variation; (3)--(5) dispose of
the only residual two-dimensional kernel, with all three rays descending.
This removes the equality singularity from such a certificate.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_low_capacity_regular_kernel_second_variation.py
```

The checker differentiates (2) symbolically, solves the first-order kernel,
applies the exact envelope-Hessian formula, and checks the all-degree sign
forms at exact representative degrees, including the original `n=5,6`
specializations.

## Research receipt

```text
tao_pipeline_receipt:
  input_stage: generation
  output_stage: verification
  artifact: ThreeExteriorLowCapacityRegularKernelSecondVariation.md plus exact symbolic checker
  human_understanding_delta: the regular equality does not conceal a coupled flat escape; its only first-order kernel is strictly second-order descending for the min-ray objective
  verification_state: ordinary exact local calculus with symbolic algebra replay
  publication_or_review_state: source-level research result, not independently reviewed
  canonicalization_state: equality-excision lemma inside the low-capacity adaptive-minray family
  unresolved_downstream_bottleneck: finite certificate for the compact complement of the regular equality neighborhood
  next_stage_owner: active Erdős 1041 exterior-selector proof lane

paper_assimilation:
  paper: erdos-1041-lemniscate-newton-flow
  section: exterior finite-Blaschke adaptive selector
  canonical_mechanism_family: low_capacity_adaptive_minray
  relation: local equality stability supporting the compact homogeneous closure
  understanding_delta: all non-kernel directions descend linearly, and the exact kernel descends quadratically
  evidence_boundary: homogeneous relaxed-cosine local model for every n>=4
  hard_step: implicit optimization followed by the envelope Hessian on the two-dimensional kernel
  meaningful_failed_route: treating the regular equality as an ordinary strict box
  open_remainder: certify the finite compact selector cover
```
