# Erdős 1041: exact three-active contact chamber and value-splitting target

## Theorem

Fix `n in {5,6}` and a collision-free, strict-speed, smooth interior
three-exterior first contact.  Suppose all three optimized root-attached rays
are active, with unique interior optimizing radii `q_j`.

Then every KKT weight is strictly positive.  If the three root directions
are distinct and noncollinear, they occur in one positive cyclic chamber:
after rotation and relabelling,

```text
theta_0=0,       theta_1=A,       theta_2=B,
0<A<pi,          0<B-A<pi,        0<2pi-B<pi.         (1)
```

The complete angular system is a positive three-edge equilibrium.  The
complete radial system has a common virial `tau` satisfying the sharp strip

```text
tau_* <= tau < 0,       tau_*=(C_*-n)/3.              (2)
```

Here `C_*` is the regular contracted speed at the same product.  Thus the
remaining smooth three-active obstruction is exactly a stationary
**value-splitting rigidity** problem: show that, away from the regular
triangle, at least one of the three stationary optimized values is strictly
below the regular comparator.

This is the only collision-free smooth interior contact type left after
`ThreeExteriorUniqueActiveContactExclusion.md`,
`ThreeExteriorTwoActiveVirialExclusion.md`, and
`ThreeExteriorTwoActiveCollinearCollisionReduction.md`.

## 1. Positive support and angular chamber

Put

```text
a_k=r_k exp(i theta_k),
K_jk=q_j r_k(1-q_j^2)(1-r_k^2)
     /[(q_j^2+r_k^2-2q_jr_k cos(theta_k-theta_j))
       (1+q_j^2r_k^2-2q_jr_k cos(theta_k-theta_j))].  (3)
```

Every `K_jk` is positive away from a zero of the evaluated Blaschke product.
Let `lambda_j>=0`, `sum lambda_j=1`, be a KKT multiplier.  A multiplier
supported at one ray is excluded by the unique-active theorem.  A multiplier
supported at two rays is excluded in the collision-free cell by the
noncollinear virial theorem and the collinear collision reduction.  Those
proofs use only the supported gradients; a third equality ray with zero
weight does not alter them.  Hence

```text
lambda_0,lambda_1,lambda_2>0.                          (4)
```

For an unordered pair define the positive symmetric edge weight

```text
w_jk=lambda_j K_jk+lambda_k K_kj.                     (5)
```

Angular stationarity is exactly

```text
sum_(j != k) w_jk sin(theta_k-theta_j)=0,   k=0,1,2. (6)
```

Order three distinct directions as `0<A<B<2pi`.  The first two independent
equations in (6) give one common signed tension

```text
w_01 sin A=w_12 sin(B-A)=-w_02 sin B.                 (7)
```

Since `0<B-A<2pi` and the three directions are noncollinear, the common
sign cannot be negative: if `A>pi`, then `0<B-A<pi`, a contradiction.
It is therefore positive.  Equation (7) gives `A<pi`, `B-A<pi`, and
`B>pi`, which is precisely (1).  Thus every cyclic gap is strictly less
than a semicircle, and there are no free angular sign choices.

## 2. Common radial virial

For one source/root pair put

```text
S_jk=1/2[P_(q_j a_k)(u_j)-P_(a_k/q_j)(u_j)]

    =r_k(1-q_j^2)
      [r_k(1+q_j^2)-q_j(1+r_k^2)cos(theta_k-theta_j)]
      /[(q_j^2+r_k^2-2q_jr_k cos(theta_k-theta_j))
        (1+q_j^2r_k^2-2q_jr_k cos(theta_k-theta_j))]. (8)
```

The fixed-product radial KKT equations say

```text
T_k:=sum_j lambda_j S_jk=tau,       k=0,1,2.          (9)
```

At the ray optimizer, logarithmic `q_j` stationarity gives

```text
sum_k [P_(q_j a_k)(u_j)+P_(a_k/q_j)(u_j)]=2n.        (10)
```

Writing

```text
C_j=sum_k P_(q_j a_k)(u_j),                          (11)
```

equations (8)--(10) yield the row identity

```text
sum_k S_jk=C_j-n.                                     (12)
```

Sum (9) over `k` and use (12):

```text
3tau=sum_j lambda_j(C_j-n).                           (13)
```

The strict boundary-speed hypothesis and the Poisson semigroup identity give
`C_j<n` for every `j`; hence `tau<0`.  At a first upward scale contact, the
true-selector scale theorem gives `C_j>=C_*` on every active ray.  Therefore

```text
3tau>=C_*-n,
```

which is the lower half of (2).  The regular triangle has equality
`tau=tau_*`.

## 3. Exact residual system

Let

```text
L_j=-n log q_j+sum_k log rho_D(q_j exp(i theta_j),a_k),
L_*=log R_n(r_0r_1r_2).                               (14)
```

At a three-active first contact one has

```text
L_0=L_1=L_2=L_*,                                      (15)
C_0,C_1,C_2>=C_*,                                     (16)
```

together with (6), (9), and the three optimizer equations (10).  At fixed
product the unknowns are two radial shapes, two angles, three optimizing
radii, and two independent KKT weights.  Allowing the product to vary gives
ten variables and the ten equality equations (6), (9)--(10), and (15), plus
the signed inequalities (1)--(2), (4), and (16).

Equivalently, the single contact-level theorem still needed in the smooth
three-active cell is

```text
(6), (9), (10), tau>=tau_*, nonregular
   ==> min_j (L_j-L_*)<0.                              (17)
```

The regular orbit is already covered by
`ThreeExteriorFiniteRegularMixedKernelStability.md`; its terminal limit is
covered by `ThreeExteriorTerminalSaturationCubicSelector.md`.

## Computational falsifier and exact boundary

A deterministic ten-equation least-squares probe in both degrees used 360
random starts.  All 61 converged roots were regular triangles, with equal
radii, `120`-degree spacing, equal optimizing radii, and weights `1/3`.
This is evidence only.

Removing the value equations reveals genuine nonregular stationary branches,
so the stronger shortcut `tau<=tau_*` is false.  On a reflection-symmetric
continuation with radii proportional to

```text
(exp(t),exp(-t/2),exp(-t/2)),       t>0,               (18)
```

the computed signs in both degrees are

```text
L_0-L_*<0<L_1-L_*=L_2-L_*,
C_0-C_*>0>C_1-C_*=C_2-C_*,
tau-tau_*>0.                                          (19)
```

Thus stationary branches must not be discarded; the exact target is their
value split (17).  Statements (18)--(19) are computational guidance, not a
proved sign theorem.

Still outside this reduction are optimizer-switch cells, the closed speed
boundary, radial chart boundaries, and collision faces of the finite
selector.  Repeated polynomial roots already close the parent problem by a
constant path, but that does not prove the selector inequality on its
collision boundary.  No finite-selector or unrestricted parent theorem is
claimed here.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_three_active_contact.py
```

```text
tao_pipeline_receipt:
  input_stage: collision-free smooth three-active first-contact KKT system
  output_stage: positive cyclic chamber, sharp virial strip, and exact value-splitting residual
  artifact: ThreeExteriorThreeActiveContactReduction.md plus symbolic checker
  human_understanding_delta: nonregular stationary branches are real, but a first contact additionally requires simultaneous equality of three values; the latter is the exact rigidity target
  verification_state: ordinary exact reduction plus symbolic identity replay; branch value signs are computational evidence only
  publication_or_review_state: source-level research reduction, not independently reviewed
  canonicalization_state: subordinate contact reduction in the adaptive-minray family
  unresolved_downstream_bottleneck: prove stationary value splitting, then handle optimizer/speed/radial boundary cells
  next_stage_owner: reflection-stationary value split and global three-active rigidity
```
