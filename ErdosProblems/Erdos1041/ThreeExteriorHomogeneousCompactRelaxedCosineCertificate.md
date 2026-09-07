# Erdős 1041: exact angle elimination and the compact homogeneous vertex atlas

## Status

This note eliminates one angular variable from the compact homogeneous
three-exterior selector problem and closes every vertex branch of a still
larger relaxed cosine polytope in degrees five and six.  The original
five-variable angular/radial/ray-parameter box is reduced to two explicit
active-line stationary families in three variables.  Those two families meet
at the regular equality and are the only surviving compact homogeneous
obligation.

The theorem is about the leading homogeneous model.  It does not yet close the
two active-line families, make the finite-capacity transfer, or prove Erdős
#1041.

## 1. Exact projection of the selector cell

Fix the ray attached to root zero.  Put

```text
t^3=(n-3)/n,                 k=3(1+t)/(2(1-t)),
b_0=1+x,  b_1=1+y,  b_2=1/((1+x)(1+y)),                (1)
c_01=-1/2+alpha,  c_02=-1/2+beta,  c_12=-1/2+gamma.
```

The normalized first variations from the regular point are

```text
L_0=3(1+t)x+2(1-t)(alpha+beta),
L_1=3(1+t)y+2(1-t)(alpha+gamma),
L_2=-3(1+t)(x+y)+2(1-t)(beta+gamma).                   (2)
```

Work first on the relaxed cosine polytope

```text
-1/2<=alpha,beta,gamma<=3/2,
alpha+beta+gamma>=0.                                   (3)
```

Every genuine triple of unit directions lies in (3), because the last
inequality is exactly
`c_01+c_02+c_12>=-3/2`.  The planar Gram determinant is not used.

The conditions `L_0>=L_1,L_2` say

```text
gamma<=beta+k(x-y),
gamma<=alpha+k(2x+y).                                  (4)
```

There exists a `gamma` satisfying (3)--(4) if and only if

```text
beta+k(x-y)>=-1/2,
alpha+k(2x+y)>=-1/2,
alpha+2beta+k(x-y)>=0,
2alpha+beta+k(2x+y)>=0.                                (5)
```

Indeed, the allowed interval is

```text
max(-1/2,-alpha-beta)
 <= gamma <=
min(3/2,beta+k(x-y),alpha+k(2x+y)),                    (6)
```

and comparing the two lower entries with the last two upper entries gives
exactly (5).  The ray-zero barrier contains `alpha,beta` but not `gamma`, so
(5) is an exact dimension reduction, not a bound.

## 2. A stronger two-inequality relaxation

For an upper bound, drop the first two inequalities in (5).  Write

```text
R=-k(x-y),             S=-k(2x+y).                     (7)
```

The remaining angular polygon is

```text
-1/2<=alpha,beta<=3/2,
alpha+2beta>=R,        2alpha+beta>=S.                 (8)
```

At fixed `x,y,q`, the two spectator factors on ray zero are positive and
strictly decreasing in `alpha` and `beta`.  Hence their product is maximized
on the lower Pareto frontier of (8).  That frontier has only four types.

The vertical vertex is

```text
alpha=-1/2,
beta=max(-1/2,(R+1/2)/2,S+1),                         (9)
```

and the horizontal vertex is

```text
beta=-1/2,
alpha=max(-1/2,R+1,(S+1/2)/2).                        (10)
```

The remaining pieces lie on

```text
alpha+2beta=R                                           (11)
```

with

```text
max(-1/2,(2S-R)/3,R-3) <= alpha <= min(3/2,R+1),       (12)
```

or on

```text
2alpha+beta=S                                          (13)
```

with

```text
max(-1/2,(S-3/2)/2)
 <= alpha <= min(3/2,(S+1/2)/2,(2S-R)/3).              (14)
```

On either line the spectator product is a concave quadratic in `alpha`.
Consequently its exact maximum is the value at the stationary point clipped
to (12) or (14).  Thus the entire compact angular problem is exactly reduced
to the two vertices (9)--(10) and two explicit active-line stationary
profiles.

## 3. Vertex atlas theorem

Let

```text
C_n=t^(n-3)(1-t^3).
```

The homogeneous squared barrier on ray zero is

```text
H_0(q)^2=q^(2(n-3)) product_(j=0)^2
 (1-2q b_j c_0j+q^2 b_j^2),       0<=q<=1/b_0.         (15)
```

> **Theorem.**  For `n=5,6`, throughout the compact normalized radial region
>
> ```text
> T_n^(-2)<b_j<T_n,
> ```
>
> every vertical or horizontal vertex in (9)--(10) satisfies
>
> ```text
> H_0(q)^2<=C_n^2.                                     (16)
> ```
>
> This remains true on the enlarged rational radial boxes used by the
> checker:
>
> ```text
> n=5:  3/4<=b_j<=29/25,
> n=6:  4/5<=b_j<=11/10.                               (17)
> ```

### Proof

Each maximum in (9) and (10) has three linear cells.  This gives twelve
degree/cell combinations.  On every cell, substitute the corresponding
linear value of `alpha` or `beta` into (15).  The checker subdivides the
rational `(x,y,q)` box dyadically, discards boxes which miss (17), the ray
domain, or the relevant linear cell, and proves (16) on every remaining box
by an exact rational interval upper bound.

The only algebraic quantities are `t` and `k`.  They are enclosed by

```text
7368/10000 < (2/5)^(1/3) < 7369/10000,
7937/10000 < (1/2)^(1/3) < 7938/10000,                 (18)
```

and monotonicity gives exact rational intervals for `k`.  The comparison uses
the smaller of the two rational endpoint values of
`t^(2(n-3))(1-t^3)^2`, so every rounding is in the adversarial direction.
The twelve finite trees close at depth at most 28.  No floating-point number
enters the replay.  ∎

## 4. First surviving boxes

The vertex atlas removes every box on which one angular coordinate reaches
its lower wall.  The only survivors are the interiors of (11) and (13), where
the clipped stationary point is active.  Numerical probes locate their sole
zero at

```text
x=y=0,       q=t,       R=S=0,                         (19)
```

and the two line formulas approach one only through this point.  The exact
`1/50` joint collar in
`ThreeExteriorHomogeneousRegularQuantitativeCollar.md` already surrounds
(19).  Therefore the next exact computation is a three-variable atlas for
the two active-line profiles outside that collar, not the original
five-variable angular box.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_homogeneous_compact_relaxed_cosine.py
```

```text
tao_pipeline_receipt:
  input_stage: five-variable compact homogeneous selector
  output_stage: exact angular elimination plus verified vertex cover
  artifact: ThreeExteriorHomogeneousCompactRelaxedCosineCertificate.md plus exact rational box checker
  human_understanding_delta: gamma disappears exactly and the angular maximum has four Pareto branches; every vertex branch is closed, leaving only two active selector lines
  verification_state: ordinary exact reduction and bit-replayable rational interval atlas for all twelve vertex cells
  publication_or_review_state: source-level research result, not independently reviewed
  canonicalization_state: compact-complement reduction in the homogeneous adaptive-minray family
  unresolved_downstream_bottleneck: certify the two three-variable active-line stationary profiles outside the landed 1/50 collar
  next_stage_owner: active Erdős 1041 exterior-selector proof lane

paper_assimilation:
  paper: erdos-1041-lemniscate-newton-flow
  section: exterior finite-Blaschke adaptive selector
  canonical_mechanism_family: low_capacity_adaptive_minray
  relation: exact compact homogeneous reduction and partial cover, not a parent closure
  understanding_delta: the apparent three-angle selector is a two-angle polygon whose only difficult faces are the two equalizing active lines
  evidence_boundary: homogeneous leading model, degrees five and six; vertex branches closed, active lines open
  hard_step: exact gamma projection followed by twelve rational three-variable cell atlases
  meaningful_failed_route: direct five-variable natural-interval subdivision produced millions of selector-boundary artefacts
  open_remainder: two active-line atlases and finite-capacity transfer
```
