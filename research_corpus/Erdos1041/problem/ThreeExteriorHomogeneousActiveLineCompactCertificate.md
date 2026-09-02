# Erdős 1041: complete compact homogeneous three-exterior selector certificate

## Status

This note closes the two active-line families left by
`ThreeExteriorHomogeneousCompactRelaxedCosineCertificate.md`.  Together with
that note and the exact `1/50` regular collar, it proves the homogeneous
adaptive three-ray barrier throughout the compact normalized radial region in
degrees five and six.  The proof is made on the relaxed cosine polygon, so it
contains every genuine angular triple.

This removes the compact homogeneous obligation.  It does not by itself lift
the result from the leading homogeneous model to finite capacity, and it does
not prove Erdős #1041.

## 1. The exact clipped-stationary decomposition

Retain the coordinates

```text
t^3=(n-3)/n,                    k=3(1+t)/(2(1-t)),
b_0=1+x,  b_1=1+y,  b_2=1/((1+x)(1+y)),
R=-k(x-y),                       S=-k(2x+y).            (1)
```

After eliminating the spectator angle `gamma`, the relaxed ray-zero selector
polygon is

```text
-1/2<=alpha,beta<=3/2,
alpha+2beta>=R,                 2alpha+beta>=S.        (2)
```

The preceding vertex atlas handles the vertical and horizontal lower-cosine
walls.  On the remaining line

```text
alpha+2beta=R,                                           (3)
```

the allowed interval is

```text
max(-1/2,(2S-R)/3,R-3) <= alpha <= min(3/2,R+1).       (4)
```

On

```text
2alpha+beta=S,                                           (5)
```

it is

```text
max(-1/2,(S-3/2)/2)
 <= alpha <= min(3/2,(S+1/2)/2,(2S-R)/3).              (6)
```

The spectator product is a concave quadratic on either interval.  Therefore
the clipped maximum is exhausted by the following seven candidates:

```text
R*: the stationary point on (3),
S*: the stationary point on (5),
I : alpha=(2S-R)/3, beta=(2R-S)/3,
RA: alpha=3/2 on (3),       RB: beta=3/2 on (3),
SA: alpha=3/2 on (5),       SB: beta=3/2 on (5).       (7)
```

The other clip endpoints are exactly the vertical or horizontal candidates
already certified by the vertex atlas.  Thus (7), together with that atlas,
is exhaustive; there is no unclassified endpoint.

## 2. Closed forms for the stationary candidates

Put

```text
P=1+q b_1+q^2 b_1^2,        Q=1+q b_2+q^2 b_2^2,
C_n=t^(n-3)(1-t^3).                                      (8)
```

On (3) the unrestricted stationary point is

```text
alpha_R^*=
 [b_2 P-2b_1(Q-qb_2R)]/(4q b_1b_2),                    (9)
```

and its exact spectator maximum is

```text
[b_2P+2b_1Q-2q b_1b_2R]^2/(8b_1b_2).                  (10)
```

On (5), respectively,

```text
alpha_S^*=
 [2b_2P-b_1(Q-2qb_2S)]/(8q b_1b_2),                   (11)

[2b_2P+b_1Q-2q b_1b_2S]^2/(8b_1b_2).                  (12)
```

The checker uses (9)--(12) only on boxes which can meet the corresponding
applicability intervals (4) or (6).  A box which cannot meet the interval is
discarded; no unrestricted stationary value is substituted for a clipped
endpoint.

## 3. The double-active equality profile

At candidate `I`, the formulas collapse to

```text
alpha=-k(x+y),                    beta=ky.              (13)
```

Choosing `gamma=kx` makes all three first variations equal.  Hence in the
collar coordinates of
`ThreeExteriorHomogeneousRegularQuantitativeCollar.md` one has

```text
M=U=V=0.                                                (14)
```

This is the branch which carries the regular equality `x=y=0,q=t`.  Boxes
contained in

```text
|x|,|y|,|q-t|<=1/50                                    (15)
```

are therefore removed by the already-proved collar, uniformly for the
algebraic `t`.

Outside (15), the checker forms the full cleared polynomial gap on (13):

```text
B=2(1-t), A=3(1+t), D=(1+x)(1+y),

G_n=B^2 C_n^2 D^2
 -q^(2(n-3))(1-q(1+x))^2
  [B(1+q(1+y)+q^2(1+y)^2)+2q(1+y)A(x+y)]
  [B(D^2+qD+q^2)-2qDAY].                               (16)
```

Here the final `Y` is the radial coordinate `y`.  Formula (16) is exactly a
positive-denominator multiple of `C_n^2-H_0(q)^2`.  Its tensor-product
Bernstein coefficients are constructed once on the rational root box and
then subdivided exactly by midpoint de Casteljau steps.  Every surviving box
outside (15) has nonnegative Bernstein coefficients.

## 4. Compact homogeneous closure theorem

> **Theorem.**  Let `n=5` or `n=6`, and suppose the normalized product-one
> radii lie in the compact region
>
> ```text
> T_n^(-2)<b_j<T_n.
> ```
>
> Fix the root-attached ray selected by the largest first variation.  For
> every genuine angular triple and every `0<=q<=1/b_0`, its homogeneous
> squared profile satisfies
>
> ```text
> H_0(q)^2<=C_n^2.                                     (17)
> ```
>
> The same assertion holds on the larger rational radial boxes
>
> ```text
> n=5: 3/4<=b_j<=29/25,
> n=6: 4/5<=b_j<=11/10.                                (18)
> ```

### Proof

The exact gamma projection and monotonicity reduce the angular maximum to the
Pareto frontier (3)--(6).  The prior vertex atlas proves the vertical and
horizontal endpoints.  Concavity reduces everything else to (7).

For `R*` and `S*`, substitute (10) and (12), respectively.  For `RA`, `RB`,
`SA`, and `SB`, substitute the displayed linear endpoint.  Exact rational
interval subdivision proves (17) on every box which can meet the relevant
candidate cell.  Candidate `I` is proved by (15)--(16).  These candidates
exhaust the clipped maxima, proving (17).  Cyclic symmetry handles the other
selected rays.  ∎

The largest trees have 29,921 nodes in degree five and 28,987 nodes in degree
six for the natural-interval stationary profiles.  The Bernstein trees for
the double-active profile have only 561 and 759 nodes, and reach depths 18
and 20.  All arithmetic is rational; the only algebraic inputs are enclosed
by

```text
7368/10000 < (2/5)^(1/3) < 7369/10000,
7937/10000 < (1/2)^(1/3) < 7938/10000.                 (19)
```

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_homogeneous_active_line_compact.py
```

```text
tao_pipeline_receipt:
  input_stage: compact homogeneous active-line remainder
  output_stage: complete compact homogeneous selector certificate
  artifact: ThreeExteriorHomogeneousActiveLineCompactCertificate.md plus exact rational interval/Bernstein checker
  human_understanding_delta: clipping produces seven exact candidates; regular equality belongs to the shared double-active kernel, while the unrestricted stationary points are separate easy branches
  verification_state: ordinary exact reduction and bit-replayable rational trees in degrees five and six
  publication_or_review_state: source-level research result, not independently reviewed
  canonicalization_state: compact homogeneous closure in the low-capacity adaptive-minray family
  unresolved_downstream_bottleneck: finite-capacity lift from the homogeneous selector theorem
  next_stage_owner: active Erdős 1041 exterior-selector proof lane

paper_assimilation:
  paper: erdos-1041-lemniscate-newton-flow
  section: exterior finite-Blaschke adaptive selector
  canonical_mechanism_family: low_capacity_adaptive_minray
  relation: closes the compact homogeneous producer, not the finite-capacity parent
  understanding_delta: all angular/radial homogeneous cases are now certified after exact selector projection and clipping
  evidence_boundary: degrees five and six, leading homogeneous model; finite-capacity error remains open
  hard_step: exact double-active kernel Bernstein cover outside the quantitative equality collar
  meaningful_failed_route: treating the two unrestricted stationary formulas as if they carried equality misses the shared clipped intersection branch
  open_remainder: quantitative finite-capacity transfer on the compact region
```
