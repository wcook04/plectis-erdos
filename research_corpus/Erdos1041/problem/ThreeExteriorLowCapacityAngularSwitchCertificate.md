# Erdős 1041: an exact angular selector switch in the low-capacity three-exterior model

## Status

This note is the positive companion to
`ThreeExteriorClosestRayLowCapacityNoGo.md`.  On the same exact rational
one-parameter family, a root-indexed first angular moment rejects the closest
excluded root and selects a different actual root ray.  The selected ray has
its **entire optimized barrier strictly below the regular-triangle
comparator** for both ambient degrees `n=5` and `n=6`, uniformly for

```text
0 < epsilon <= 1/600.
```

The theorem is attachment-compatible: the curve is the actual radial segment
from the component boundary to the selected reciprocal zero.  It proves a
genuine adaptive-selector family, not the unrestricted three-exterior
envelope.  The first-moment rule is known not to select the optimum on every
configuration, so only the exact family stated here is claimed.

## 1. Family and angular statistic

Retain the rational unit vectors and normalized radii

```text
u_0=(1,0),
u_1=(21/221,-220/221),
u_2=(-91/109,60/109),

b_0=1,       b_1=24/25,       b_2=51/50,
P=b_0b_1b_2=612/625,
a_j=epsilon b_j u_j.
```

For each root direction define the scale-free first angular moment

```text
C_j=Re(conj(u_j) sum_k b_k u_k).                        (1)
```

Exact arithmetic gives

```text
C_0= 288661/1204450,
C_1= 500061/1204450,
C_2=-502339/1204450.                                   (2)
```

Hence (1) uniquely selects `j=1`.  The same index also maximizes the cubic
root charge

```text
A_j=b_j(C_j-b_j),
```

whose three exact values are

```text
A_0=-915789/1204450,
A_1=-7874532/15055625,
A_2=-2596317/1771250.                                  (3)
```

This is a genuine switch: `b_2` is largest, so `j=2` is the closest excluded
root, while `b_1` is smallest and `j=1` is the farthest excluded root in the
exterior radial coordinate.  The closest ray is too expensive by the exact
companion no-go, but the first-moment ray will now be proved cheap.

## 2. A uniform upper bound for the selected full ray

Put `q=epsilon y` on the ray in direction `u_1`.  Its geometric domain is

```text
b_1 <= y <= 1/epsilon.
```

For ambient degree `n=3+d`, inversion gives

```text
G_(1,n)(epsilon y)
 =epsilon^(-d) H_(1,n)(y)
  / product_k |1-epsilon^2 y b_k conj(u_k)u_1|,         (4)

H_(1,n)(y)^2
 =y^(-2n) product_k |y u_1-b_k u_k|^2.                 (5)
```

Since `q<=1` and every `b_k<=b_2`,

```text
|1-epsilon^2 y b_k conj(u_k)u_1|
 >=1-epsilon b_2.
```

Therefore

```text
G_(1,n)(epsilon y)
 <=epsilon^(-d) H_(1,n)(y)/(1-epsilon b_2)^3.          (6)
```

The remaining maximization is an exact univariate polynomial problem.  Put

```text
U_5=31/100,       U_6=6/25,

Q_n(y)=U_n^2 y^(2n)-product_k |y u_1-b_k u_k|^2.       (7)
```

The exact Sturm sequence has no root in `[24/25,infinity)` for either
`n=5` or `n=6`, and

```text
Q_5(24/25)=3808165569232896/59604644775390625>0,
Q_6(24/25)=1314732507698036736/37252902984619140625>0. (8)
```

Thus

```text
H_(1,5)(y)<31/100,
H_(1,6)(y)<6/25                                  (9)
```

throughout the complete selected-ray domain.  Notice that (9) controls the
full maximum; it is not a sampled-radius inequality.

## 3. Exact comparison with the regular maximum

The regular-triangle profile with the same product
`p=epsilon^3P` is

```text
S_n(q)=q^(-n)(q^3-p)/(1-pq^3).
```

Evaluate it at the rational scale

```text
y_5=27/20,       y_6=5/4,       q=epsilon y_n.
```

Both points lie in the regular radial domain.  Dropping the denominator in
the favorable direction gives

```text
M_sym(5,p) >=epsilon^(-2) L_5,
L_5=(y_5^3-P)/y_5^5=526640/1594323,

M_sym(6,p) >=epsilon^(-3) L_6,
L_6=(y_6^3-P)/y_6^6=2493248/9765625.                  (10)
```

The correction in (6) is worst at `epsilon=1/600`.  Exact rational
comparison gives

```text
(31/100)/(1-(51/50)/600)^3 < L_5,
( 6/25 )/(1-(51/50)/600)^3 < L_6.                     (11)
```

The positive differences in (11) are respectively

```text
29718569381417680/1586205767647501101,
136804039410832576/9715904932490234375.
```

Combining (6), (9), (10), and (11) proves

```text
max_(q in [epsilon b_1,1])
  q^(-n)|B_epsilon(q u_1)|
  < M_sym(n,epsilon^3P),       n=5,6.                  (12)
```

Thus the angular moment (1) selects one actual excluded root whose complete
radial attachment barrier satisfies the conjectured sharp comparator on this
low-capacity family.

## Frontier effect and exact boundary

Together with the companion no-go, (12) isolates the correct qualitative
mechanism:

```text
radius order alone fails;
an angularly informed switch between actual roots can recover the comparator.
```

The statistic `C_j` is the first Fourier moment of the radius-weighted
direction measure.  Its weighted average obeys
`sum_j b_j C_j=|sum_j b_j u_j|^2>=0`, which explains why it is structurally
available, but this note does not claim it is the global optimum selector.
The general three-exterior problem still requires either a stronger
multi-scale angular statistic, a proof for the optimized minimum over all
three rays, or a curved mountain-pass theorem.

The result is an abstract exterior finite-Blaschke theorem.  It does not
assert polynomial realization of this particular model, a general
low-capacity neighborhood theorem, or unrestricted Erdős 1041.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_low_capacity_angular_switch.py
```

The checker uses exact rational arithmetic and SymPy's exact Sturm root count.

## Research receipt

```text
tao_pipeline_receipt:
  input_stage: generation
  output_stage: verification
  artifact: ThreeExteriorLowCapacityAngularSwitchCertificate.md plus exact rational/Sturm checker
  human_understanding_delta: the low-capacity failure is selector-specific; a first angular moment switches to a non-closest root and restores the sharp comparator on the exact family
  verification_state: ordinary exact proof with exact rational and Sturm replay
  publication_or_review_state: source-level research result, not independently reviewed
  canonicalization_state: positive companion in the same low-capacity selector mechanism family
  unresolved_downstream_bottleneck: turn the family-specific first moment into a global adaptive statistic or optimize all three rays directly
  next_stage_owner: active Erdős 1041 exterior-selector proof lane

paper_assimilation:
  paper: erdos-1041-lemniscate-newton-flow
  section: exterior finite-Blaschke adaptive selector
  canonical_mechanism_family: low_capacity_angular_selector_switch
  relation: exact positive family supporting, not closing, the parent
  understanding_delta: angular first-moment data can repair a radius-order selector failure while retaining one actual attachment ray
  evidence_boundary: one exact rational one-parameter family in n=5,6
  hard_step: uniform full-ray Sturm bound followed by a global regular-maximum comparison
  meaningful_failed_route: always attach the closest excluded root
  open_remainder: global min-ray or curved mountain-pass selector
```
