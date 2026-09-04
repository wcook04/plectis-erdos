# Erdős 1041: virial exclusion of genuinely angular two-active contacts

## Theorem

Fix an ambient degree `n>3` and a strict-speed three-exterior configuration

```text
a_k=r_k exp(i theta_k),       0<r_k<1,
max_(|u|=1) sum_k P_(a_k)(u)<n.                        (1)
```

Suppose two optimized attached rays are active at a smooth interior KKT
contact, their optimizing radii `q_0,q_1` are interior, and the KKT weight is
mixed.  Then the contact cannot lie in the genuinely angular branch of
`ThreeExteriorTwoActiveAngularKktReduction.md`.

Consequently, in degrees five and six every smooth two-active first contact
is collinear.  The entire noncollinear canonical chamber is empty; no value
equation, scale-contact inequality, or interval atlas is needed to exclude
it.

## Proof

Use the canonical chamber of the angular reduction:

```text
theta_0=0,       theta_1=A,       theta_2=pi+C,
0<C<A<pi.                                             (2)
```

Put `D=A-C`, so `C,D>0` and `C+D=A<pi`.  For one source radius `q`, root
radius `r`, and relative angle `x`, abbreviate

```text
K(q,r,x)=q r(1-q^2)(1-r^2)
          /[(q^2+r^2-2qr cos x)(1+q^2r^2-2qr cos x)],

S(q,r,x)=1/2[P_(q r exp(ix))(1)-P_(r exp(ix)/q)(1)].  (3)
```

The exact radial factorization is

```text
S(q,r,x)
 =r(1-q^2)[r(1+q^2)-q(1+r^2)cos x]
   /[(q^2+r^2-2qr cos x)(1+q^2r^2-2qr cos x)].        (4)
```

Let `lambda in (0,1)` be the mixed KKT weight.  The positive tension law
from the angular reduction gives one number `W>0` such that

```text
W=lambda K(q_0,r_2,pi+C) sin C
 =(1-lambda)K(q_1,r_2,pi-D) sin D.                    (5)
```

Consider the weighted radial coefficient of the spectator root:

```text
T_2=lambda S(q_0,r_2,pi+C)
    +(1-lambda)S(q_1,r_2,pi-D).                       (6)
```

Equations (4)--(5) give

```text
T_2/W
 = r_2/(1-r_2^2)
    [(q_0+q_0^(-1))/sin C+(q_1+q_1^(-1))/sin D]
   +(1+r_2^2)/(1-r_2^2)(cot C+cot D).                 (7)
```

Every term in the square bracket is positive.  The remaining cotangent sum
is also strictly positive because

```text
cot C+cot D=sin(C+D)/(sin C sin D)=sin A/(sin C sin D)>0. (8)
```

Thus

```text
T_2>0.                                                (9)
```

The radial KKT equations say that all three weighted root coefficients are
equal:

```text
T_0=T_1=T_2=tau.                                      (10)
```

On active ray `j`, one-variable optimizer stationarity gives

```text
sum_k [P_(q_j a_k)(u_j)+P_(a_k/q_j)(u_j)]=2n.         (11)
```

Therefore, writing `C_j=sum_k P_(q_j a_k)(u_j)`, summing (3) over the three
roots yields the virial identity

```text
sum_k S_jk=C_j-n.                                     (12)
```

The Poisson semigroup identity and the strict boundary-speed hypothesis (1)
give

```text
C_j=P_(q_j)*[sum_k P_(a_k)](u_j)<n,                   (13)
```

because `0<q_j<1`.  Sum (10) over the root index and use (12):

```text
3 tau=lambda(C_0-n)+(1-lambda)(C_1-n)<0.              (14)
```

Hence `tau<0`, contradicting (9)--(10).  The genuinely angular branch is
impossible.  ∎

## Frontier effect and exact boundary

This removes all collision-free and collision-bearing noncollinear smooth
two-active contacts at once.  The seven-equation canonical contact atlas is
unnecessary on that branch.  The mechanism is structural: angular force
balance makes the third root radially expansive, while the boundary-speed
condition makes the total optimized virial contractive.

Still open inside the finite selector are the collinear two-active branch,
three-active contacts, optimizer switches, the closed speed boundary, and
the named radial/collision constraint faces.  The theorem does not prove the
full finite selector or unrestricted Erdős 1041.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_two_active_virial.py
```

```text
tao_pipeline_receipt:
  input_stage: canonical smooth two-active KKT chamber plus strict boundary speed
  output_stage: complete exclusion of the genuinely angular branch
  artifact: ThreeExteriorTwoActiveVirialExclusion.md plus symbolic checker
  human_understanding_delta: positive angular tension forces the spectator radial coefficient positive, but optimizer stationarity and Poisson contraction force the common radial virial negative
  verification_state: ordinary exact proof plus symbolic identity replay
  publication_or_review_state: source-level research theorem, not independently reviewed
  canonicalization_state: decisive subordinate exclusion in the adaptive-minray family
  unresolved_downstream_bottleneck: collinear two-active, three-active, optimizer-switch, speed-boundary, and constraint-face contacts
  next_stage_owner: collinear multiplicity reduction and three-active virial analysis
```
