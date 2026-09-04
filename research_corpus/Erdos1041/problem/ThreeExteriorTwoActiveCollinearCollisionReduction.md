# Erdős 1041: collinear two-active contacts force a collision

## Theorem

Fix an ambient degree `n>3` and a strict-speed three-exterior configuration

```text
a_k=r_k exp(i theta_k),       0<r_k<1,
max_(|u|=1) sum_k P_(a_k)(u)<n.                        (1)
```

Suppose exactly two root-attached rays are active at a smooth interior KKT
contact, their optimizing radii are unique and interior, and the KKT weight
is mixed.  If the contact is collinear, then two root occurrences coincide.

Consequently there is no collision-free smooth collinear two-active contact.
Together with `ThreeExteriorTwoActiveVirialExclusion.md`, this removes every
collision-free smooth two-active contact, in every ambient degree.

## Proof

For a source radius `q` and a root radius `r`, the radial Poisson-difference
coefficient on the same and opposite rays is

```text
S_-(q,r)=-r(1-q^2)/[(q-r)(1-qr)],
S_+(q,r)= r(1-q^2)/[(q+r)(1+qr)].                     (2)
```

As in the virial exclusion, fixed-product radial KKT gives one common
coefficient

```text
T_0=T_1=T_2=tau,                                      (3)
```

and optimizer stationarity plus strict boundary speed gives

```text
3 tau=lambda(C_0-n)+(1-lambda)(C_1-n)<0.              (4)
```

Thus every root occurrence has weighted coefficient `tau<0`.

Rotate the first active ray to the positive real axis.  The collinear branch
of the angular KKT reduction has two cases.

### Coincident active directions

If the two active directions coincide, their optimized profiles are the same
one-variable function.  Uniqueness of the optimizer gives `q_0=q_1=q`, so
the weighted coefficient is just (2).  A root on the opposite ray has
coefficient `S_+(q,r)>0`, contradicting (3)--(4).  Hence all three roots lie
on the active ray.  There `S_-(q,r)=tau<0` forces `r<q`, and

```text
d/dr S_-(q,r)
 =-q(1-q^2)(1-r^2)/[(q-r)^2(1-qr)^2]<0.              (5)
```

Therefore `S_-(q,.)` is injective on `(0,q)`.  Equation (3) makes all three
radii equal, hence all three root occurrences coincide.

### Antipodal active directions

Now put the active sources at `q_0` and `-q_1`.  For a root of radius `r` on
the positive ray its weighted coefficient is

```text
T_+(r)=lambda S_-(q_0,r)+(1-lambda)S_+(q_1,r).        (6)
```

If `r>q_0`, both terms in (6) are positive; equality to `tau<0` is
impossible.  Thus every positive-ray root satisfying (3) lies in
`0<r<q_0`.  On this interval exact differentiation gives

```text
T_+'(r)/(1-r^2)
 =-lambda q_0(1-q_0^2)/[(q_0-r)^2(1-q_0r)^2]
  +(1-lambda)q_1(1-q_1^2)/[(q_1+r)^2(1+q_1r)^2].     (7)
```

The magnitude of the negative term in (7) is strictly increasing in `r`,
because `(q_0-r)(1-q_0r)` is strictly decreasing.  The positive term is
strictly decreasing, because `(q_1+r)(1+q_1r)` is strictly increasing.
Hence the right side of (7) is strictly decreasing and changes sign at most
once, from positive to negative.  Since

```text
T_+(0)=0,                                             (8)
```

the graph is either strictly decreasing, or first increases above zero and
then strictly decreases.  In either case every fixed negative level is met
at most once.  In particular `T_+(r)=tau<0` has at most one solution.

The same argument with the signs interchanged applies on the negative ray:

```text
T_-(r)=lambda S_+(q_0,r)+(1-lambda)S_-(q_1,r),        (9)
```

and `T_-(r)=tau<0` also has at most one solution.

All three root occurrences lie on two antipodal rays.  By the pigeonhole
principle two occurrences lie on the same ray; the negative-level uniqueness
just proved forces their radii to agree.  They are the same point, so the
configuration lies on the collision boundary.  ∎

## Frontier effect and exact boundary

The genuinely angular branch is empty by the positive-spectator virial
theorem.  The present theorem pushes its collinear complement entirely onto
the collision boundary.  Therefore the collision-free smooth two-active
atlas is empty; no two-active interval subdivision remains in the open
configuration cell.

Still open inside the finite selector are collision-face contacts,
three-active contacts, optimizer switches, the closed speed boundary, the
named radial chart boundaries, and the regular equality orbit.  This theorem
does not by itself prove the finite selector or unrestricted Erdős 1041.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_two_active_collinear_collision.py
```

```text
tao_pipeline_receipt:
  input_stage: collinear smooth two-active KKT contact plus strict boundary speed
  output_stage: reduction of the entire collinear branch to the collision boundary
  artifact: ThreeExteriorTwoActiveCollinearCollisionReduction.md plus symbolic checker
  human_understanding_delta: the common virial is negative, while each antipodal ray can realize a negative radial level at only one radius
  verification_state: ordinary exact proof plus symbolic identity replay
  publication_or_review_state: source-level research theorem, not independently reviewed
  canonicalization_state: decisive subordinate exclusion in the adaptive-minray family
  unresolved_downstream_bottleneck: collision faces, three-active contacts, optimizer switches, speed boundary, and radial chart boundaries
  next_stage_owner: collision-face reduction and three-active virial analysis
```
