# Erdős #1041: the equality tetrahedron absorbs the paired cubic mode

Status: complete analytic extended-contact theorem, exact symbolic replay, and
focused Lean formalization, 2026-08-25. This removes the last first-order
obstruction at the unique equality orbit of the normalized quintic atlas. It
does not by itself finish the transverse finite-polynomial transfer or
unrestricted Erdős #1041.

## 1. The missing direction

At the canonical equality chart the leading mixed model is

```text
H(z)=Re(u_* z+i z^2-z^5),          u_*^3=27/320.          (1)
```

The disk-tangent pairing forces the first omitted mode to be

```text
rho Re(i z^3),                    rho>=0.                 (2)
```

Previous work checked its signs at two axis contacts. The decisive fact is
what it does on **all four** contacts simultaneously.

## 2. Exact cubic values

Write the four contacts as

```text
z_L=y(sqrt(5)+i),
z_+=iy(sqrt(3)-1),
z_R=y(-sqrt(5)+i),
z_-=-iy(sqrt(3)+1),                y>0.                   (3)
```

Since `Re(i z^3)=-Im(z^3)`, division by `y^3` gives

```text
q_L=-14,
q_+=(sqrt(3)-1)^3,
q_R=-14,
q_-=-(sqrt(3)+1)^3.                                      (4)
```

Their sum is not zero:

```text
q_L+q_++q_R+q_-
 =-28+(sqrt(3)-1)^3-(sqrt(3)+1)^3
 =-48.                                                    (5)
```

Thus the paired cubic has a strictly negative barycentre on the active
contact set.

## 3. The extended selector

Let `g_j dot v` be the three-parameter first variations from
`QuinticEqualityTetrahedron`. They satisfy

```text
sum_j g_j dot v=0.                                        (6)
```

The extended first variations are

```text
X_j(v,rho)=g_j dot v+rho y^3 q_j.                         (7)
```

By (5)--(6),

```text
sum_j X_j(v,rho)=-48 rho y^3.                             (8)
```

Therefore some contact always obeys the quantitative average bound

```text
X_j(v,rho)<=-12 rho y^3.                                  (9)
```

If `rho>0`, this is strict for **every** coefficient perturbation `v`, however
large its tangent component is. If `rho=0` and `v!=0`, the original centred
tetrahedron supplies strict negativity. Hence

> For every `rho>=0` and every nonzero extended direction `(v,rho)`, at least
> one of the four contact variations is strictly negative.

This is stronger than selecting between the two simultaneous zeros: the same
four equal barycentric weights that killed the coefficient perturbation now
turn the paired cubic into a uniform negative drift.

## 4. Remainder absorption

Suppose each contact calculation has an upper remainder `epsilon`. If

```text
epsilon<12 rho y^3,                                      (10)
```

then the contact from (9) remains strictly negative. When (10) is not the
dominant comparison because `rho` is tiny relative to the coefficient
displacement, the existing tetrahedral support `59/1000` and quadratic
remainder bound `8 delta^2` apply. These two estimates cover the full corner:

```text
rho dominates delta^2  ->  cubic average (9),
delta^2 dominates rho  ->  tetrahedral linear support.  (11)
```

There is no transition wedge left between them.

## 5. Verification and downstream handoff

The exact checker derives (4) directly from (3), reduces (5) modulo
`s_3^2-3`, and tests one million extended directions. Lean proves the exact
cubic sum, the average selector, the robust remainder form, and the combined
`rho=0`/`rho>0` strict selector by reusing the original tetrahedron theorem.

Closed here: the first-order and paired-cubic stability of the unique quintic
equality orbit in every admissible extended direction. The next proof owner
must insert this selector into the exact anchored expansion and the finite
atlas boxes; away from equality, the atlas already has strict margin. That is
now glue with explicit constants, not a missing geometric mechanism.
