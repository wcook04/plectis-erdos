# Erdős 1041: smooth unique-active three-ray contacts are impossible

## Theorem

Fix a capacity below saturation in the finite three-exterior problem and
write

```text
V_j(C)=max_(r_j<=q<=1) q^(-n)|B_C(q u_j)|,
H(C)=min_j V_j(C)/R_n(p).                              (1)
```

Work in a smooth interior configuration cell: the boundary-speed inequality,
the radial compactness bounds, and all collision constraints are strict, and
the active ray has a unique nondegenerate interior optimizing radius.

> **Unique-active exclusion.**  A nonregular local maximum of `H` at level
> `H=1` cannot have a unique active ray.

Equivalently, every finite nonregular first contact in a smooth optimizer cell
must lie on a selector switch where at least two attached rays satisfy

```text
V_j=R_n(p).                                             (2)
```

The only other surviving contact locations are the already explicit
boundaries: an optimizer switch, the closed speed boundary, a collision or
radial chart boundary, or the regular equality orbit.  This removes the full
open cell with one cheapest ray from the compact contact atlas.

## Proof

Assume ray `j` is uniquely active.  It remains uniquely active in a
neighbourhood, so a local maximum of `H` is a local maximum of `V_j`; the
regular comparator is constant on the fixed-product configuration slice.
The envelope theorem permits differentiation at its unique optimizing radius
`q`.  Rotate so `u_j=1`, and write every exterior zero as

```text
a_k=r_k exp(i alpha_k),       alpha_j=0.               (3)
```

For a spectator zero put

```text
N=q^2+r_k^2-2q r_k cos(alpha_k),
D=1+q^2r_k^2-2q r_k cos(alpha_k).                      (4)
```

Its angular derivative in the optimized log barrier is

```text
partial_(alpha_k) log rho(q,a_k)
 =q r_k(1-q^2)(1-r_k^2) sin(alpha_k)/(N D).            (5)
```

Every factor outside the sine is strictly positive.  The two spectator
angles are independent coordinates after quotienting common rotation, so
stationarity forces

```text
alpha_k in {0,pi}       for both k !=j.                (6)
```

Now vary the logarithmic radii subject to fixed product.  The scale derivative
contributed by one zero is

```text
S_k=1/2[P_(q a_k)(1)-P_(a_k/q)(1)].                   (7)
```

On the two collinear directions, exact simplification gives

```text
S_+(r)=-r(1-q^2)/[(1-qr)(q-r)] <0,                    (8)
S_-(r)= r(1-q^2)/[(1+qr)(q+r)] >0.                    (9)
```

Fixed-product stationarity says all three `S_k` are equal: the derivative
along every vector whose logarithmic-radius coordinates sum to zero must
vanish.  The active zero itself lies on the plus direction and has negative
`S_j`.  Equations (8)--(9) therefore exclude every spectator on the opposite
direction.  All three zeros lie on the selected ray.

For fixed `q`, the positive factor

```text
r/[(1-qr)(q-r)]                                       (10)
```

has strictly positive logarithmic derivative

```text
1/r+q/(1-qr)+1/(q-r).                                 (11)
```

Thus `S_+(r)` is strictly decreasing and hence injective.  Equality of the
three radius derivatives forces

```text
r_1=r_2=r_3=:r.                                        (12)
```

The putative stationary configuration is therefore the triple coincident
zero on one ray.  But its pointwise Blaschke profile is strictly below the
regular-triangle profile with the same product.  Indeed, for `r<q<1`,

```text
((q-r)/(1-rq))^3 < (q^3-r^3)/(1-r^3q^3),              (13)
```

because after cancelling one factor the positive cross-multiplied difference
is

```text
3 q r(q-1)(q+1)(r-1)(r+1)>0.                          (14)
```

At the assumed contact `V_j=R_n(r^3)>1`, so the maximizing `q` is interior.
Evaluating (13) there gives

```text
V_j < regular_profile(q) <= R_n(r^3),                 (15)
```

contradicting `V_j=R_n(r^3)`.  Hence the unique-active smooth contact does
not exist.  ∎

## Frontier effect

The previous continuation theorem allowed an arbitrary nonregular equality
contact with nonsmooth KKT weights.  The scale-contact theorem added the
contracted-speed condition.  The present theorem removes the generic
one-active-ray cell entirely.  A surviving interior contact must have two or
three equal cheapest barriers, so the selector-switch equalities can be used
as elimination equations before any interval subdivision.

This is not just a dimension count: the proof identifies the only formal
single-ray stationary object and defeats it by the strict pointwise
polarization gap (13).

## Exact boundary

Proved here: exclusion of every unique-active local equality maximum in a
smooth interior optimizer cell.  Still open: multi-active selector switches,
optimizer-switch cells, the closed speed boundary, and the remaining compact
finite selector.  No unrestricted Erdős 1041 closure is claimed.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_unique_active_contact.py
```

```text
tao_pipeline_receipt:
  input_stage: true-selector first-contact system
  output_stage: exclusion of the smooth unique-active contact cell
  artifact: ThreeExteriorUniqueActiveContactExclusion.md plus symbolic checker
  human_understanding_delta: angular stationarity makes a unique cheapest ray collinear, fixed-product radial stationarity collapses it to a triple coincident zero, and strict pointwise polarization defeats that object
  verification_state: ordinary exact proof plus symbolic identity replay
  publication_or_review_state: source-level research theorem, not independently reviewed
  canonicalization_state: subordinate contact-cell theorem in the existing adaptive-minray family
  unresolved_downstream_bottleneck: multi-active selector switches and constraint-boundary contacts
  next_stage_owner: switch-surface elimination or certified compact atlas
```
