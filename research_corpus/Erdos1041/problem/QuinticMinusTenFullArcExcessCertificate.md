# Erdős 1041: uniform negative curved excess on the full `mu=-10` phase arc

Date: 2026-08-30. Exact checker:
`scripts/check_erdos1041_quintic_minus_ten_full_arc_excess.py`.

## 1. Result

Let

```text
F(x)=F_{-10}(x)=x^3(x^2+5x+10),
q_0=1/(2sqrt(2)),
phi_0=arctan(q_0).
```

For every allowed phase on the repeated-critical stratum,

```text
|tan(phi)| <= q_0,
```

the canonical pair of limiting curved inverse-ray arms born at the triple
hub has uniformly negative excess:

```text
mathcal E(-10,phi) < -1/100 < 0.                       (F0)
```

This is an exact all-phase statement.  It strictly contains the earlier
centre theorem and the two endpoint theorems.  In the model chamber
reduction it closes the complete canonical singular obligation `EX-10`.
`QuinticWallSheetSubharmonicReduction.md` subsequently reduces regular
`EX-W` sheets to one-real-dimensional double-tight branches and explicit
puncture limits.  Model-to-real transfer, degree five, and unrestricted
Erdős 1041 remain separate open obligations.

## 2. One fixed box for every signed arm

For a signed parameter `zeta=tan(phi)`, write an upper-half-plane arm as

```text
x=b(t+i),  b>0.
```

The ray equation is the quadratic curve

```text
Q_zeta(t,b)=A_zeta(t)b^2+B_zeta(t)b+C_zeta(t)=0,
A_zeta(t)=zeta(t^5-10t^3+5t)+5t^4-10t^2+1,
B_zeta(t)=5zeta t^4-30zeta t^2+5zeta+20t^3-20t,
C_zeta(t)=10zeta t^3-30zeta t+30t^2-10.              (F1)
```

Let `r(zeta)` be the selected negative zero of `C_zeta`, let `k(zeta)` be
the selected positive zero of `A_zeta`, and set

```text
d=k-r,
t=r+dy,
w=b(k-t),
0<=y<=1.                                              (F2)
```

The checker isolates these roots uniformly on every rational phase slab.
Exact endpoint signs and nonzero `C_t,A_t` prove uniqueness and smooth
dependence.  Throughout the full signed interval they stay in

```text
-3/4 < r < -2/5,
 1/5 < k <  1/2.                                     (F3)
```

In particular every certified arm remains in `t>-1`.  The nonzero upper
zero and critical point of `F` have slopes `-sqrt(5/3)` and `-sqrt(2)`, both
below `-1`; hence the glued branch meets neither.  Its entrance scalar is
positive, and the exact orientation sign below identifies it with the
outward physical inverse-ray lift.

Write

```text
D_zeta(k,t)=(A_zeta(t)-A_zeta(k))/(t-k).
```

Because `C_zeta(r)=0`, the cleared equation can be evaluated in the
dependency-reduced form

```text
S=-D_zeta(k,t)w^2+B_zeta(t)w
  +(t-r)(k-t) E_zeta(r,t)=0,                          (F4)
E_zeta(r,t)=10(zeta(r^2+rt+t^2-3)+3(r+t)).
```

The selected solution satisfies `w(0)=0` and `w(1)=1`.

## 3. The square-integrand cancellation

Put

```text
Y=wS_w-(k-t)S_t,
X=tY+w(k-t)S_w.                                      (F5)
```

The checker proves `S_w>0`, `Y>0`, and

```text
Delta=sqrt(X^2+Y^2)sqrt(1+k^2)+Y+kX>0.               (F6)
```

These signs give implicit regularity and the positive-ray orientation.  The
physical tangent has coordinates `(X,Y)`, while its determinant with the
terminal direction satisfies the exact identity

```text
kY-X=-(k-t)^2 S_t.                                   (F7)
```

Also

```text
w_y=-d S_t/S_w.                                      (F8)
```

Multiplying the quotient-free tangent half-angle by `|w_y|` cancels both
absolute values and prices every turn automatically:

```text
tan(|theta|/2)|w_y|
  = d(k-t)^2 S_t^2/(S_w Delta)
  = d^3(1-y)^2 S_t^2/(S_w Delta).                    (F9)
```

Thus the transverse budget is the smooth fixed-box integral

```text
J(zeta)=integral_0^1
  d^3(1-y)^2 S_t^2/(S_w Delta) dy.                   (F10)
```

Projection on the terminal direction and the transverse endpoint identity
then give the support--oscillation bound

```text
e(zeta) <= (J(zeta)-k(zeta))/sqrt(1+k(zeta)^2).       (F11)
```

At phase `phi`, the two physical arms are the signed upper arms `zeta=q`
and `zeta=-q`, where `q=|tan(phi)|`.  It is therefore enough to bound

```text
B(q)=e(q)+e(-q),  0<=q<=q_0.                         (F12)
```

## 4. Tight exact anchors

The checker covers `[0,q_0]` by 64 rational slabs, using an outward rational
enclosure slightly larger than `q_0`.  At the midpoint of each slab it
isolates `r,k` and the selected `w` root on 640 rational `y` cells.  Floating
point proposes boxes only.  A cell is accepted only when exact endpoint
signs and `S_w>0` isolate one root for the whole cell, both adjacent node
boxes lie inside it, and the exact `Y,Delta` lower bounds are positive.

On a cell where (F8) has a fixed exact sign, the checker uses the two very
narrow node boxes to bound the variation of `w`.  On a sign-uncertain cell
it instead integrates the nonnegative exact expression (F9) directly.
This hybrid is rigorous without a stationary resultant: the variation form
is sharp away from a turn, while the square form is sharp at a genuine turn
and at the quadratically vanishing terminal tail.

The resulting anchor bounds contain neither repeated phase uncertainty nor
floating-point acceptance.

## 5. Paying phase uncertainty once

Natural two-dimensional interval quadrature is sound but wasteful: treating
`zeta,r(zeta),k(zeta),w(zeta,y)` as independent repeats the same phase width
in every `y` cell.  The checker removes that dependency with exact
first-order interval jets.

The algebraic root derivatives are

```text
r'=-C_zeta/C_t,
k'=-A_zeta/A_t.                                      (F13)
```

Differentiating (F4) at fixed `y` gives

```text
w'=-(d/dzeta S at fixed w)/S_w.                      (F14)
```

Forward interval differentiation is then applied to (F5)--(F11), including
the outward square roots.  On 128 rational `y` cells per phase slab this
produces a rigorous number `L_sigma` with

```text
|e'(zeta)| <= L_sigma                                (F15)
```

for every signed `zeta` in that slab.  If `q_c` and `rho` are its midpoint
and half-width, the mean-value theorem yields

```text
B(q) <= B_anchor(q_c)+rho(L_+ + L_-).                (F16)
```

The crucial point is that `rho` occurs once in (F16), not once for every
quadrature cell.

All interval endpoints are integer multiples of `2^-80`.  Addition,
multiplication, division, powers, and square roots use integer floor or
ceiling operations, so this speed optimization remains exact outward
rational arithmetic.

## 6. Checker result

The default run checks 64 phase anchors, 640 point cells per signed arm, and
128 derivative cells per signed arm.  Every branch box, regularity sign,
orientation sign, dual derivative bound, and mean-value fan-in is checked
before the final comparison

```text
max_slab [B_anchor+rho(L_++L_-)] < -1/100.            (F17)
```

The per-slab decimal lines are readable projections of exact dyadic
rational inequalities.  They are not floating-point proof inputs.

On the default run the weakest slab is the endpoint-adjacent slab 64.  Its
exact dyadic comparison is displayed readably as

```text
B_anchor < -0.037351392,
L_+ + L_- < 6.856366,
B_uniform < -0.018413178614 < -0.01.                 (F18)
```

Across the atlas the anchor checks give `S_w>5.56`, `Y>5.50`, and
`Delta>11.84`.  The hybrid falls back to (F9) on 11035 sign-uncertain cells;
the remaining cells use exact node variation.  These decimals summarize
strict exact dyadic inequalities recorded by the checker.

## Claim boundary

The Python checker is the authority for the finite exact interval atlas,
including branch isolation, the hybrid point budgets, dual phase
derivatives, and the final rational comparison.  The symbolic identities
(F1), (F4), and (F7) are also checked exactly before the atlas starts.

This theorem closes exactly the canonical pair on the full `mu=-10` singular
phase arc in the universal quintic model.  Direction-dependent simple-hub
resolutions approaching the triple hub can select a different pair among the
three limiting arms; those wall-sheet puncture limits require an explicit
tract match or an additional side-arm certificate.  It does not prove the
remaining one-dimensional `EX-W` boundary and puncture obligations, the
model-to-real consumption law, the degree-five real theorem, or unrestricted
Erdős 1041.
