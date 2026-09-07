# Erdős 1041: gap-normalized wall sheets are subharmonic

Date: 2026-08-30. Exact algebra checker:
`scripts/check_erdos1041_quintic_wall_sheet_subharmonic_reduction.py`.
Consumes `QuinticChamberWallReduction.md` and
`QuinticMinusTenFullArcExcessCertificate.md`.

## 1. Result

The chamber-wall obligation `EX-W` in
`QuinticChamberWallReduction.md` is nominally two-real-dimensional: one
chooses `mu in C`, and the phase is pinned by one tight critical gap.  This
note proves a further exact dimension drop.

Let `u` be the selected tight critical root, let

```text
mu(u)=-(5/2)(u+2)(u^2+2u+2),
lambda(u)=g(u)=(1/2)u^3(3u^2+10u+10),                (W1)
```

and choose the wall orientation `eps in {+1,-1}` by

```text
e^{i phi} lambda = -eps i |lambda|.                  (W2)
```

On every lifted open wall-sheet component on which `lambda != 0` and
`mu != -10`, define

```text
U_{u,eps}=mathcal E(mu(u),phi(u))/|lambda(u)|^(1/5). (W3)
```

> **Theorem W (weighted wall-sheet maximum principle).**  `U_{u,eps}` is
> subharmonic in the complex coordinate `u`.  Consequently, on each
> regular lifted wall-sheet component `D`,
>
> ```text
> sup_D U <= max(
>     sup_{partial_dt D} U,
>     limsup_{lambda -> 0 in D} U,
>     limsup_{mu -> -10 in D} U),                    (W4)
> ```
>
> where `partial_dt D` is the double-tight boundary: a second critical gap
> has zero rotated real part.

Since `|lambda|^(1/5)>0`, `U` and `mathcal E` have exactly the same sign.
Thus (W4), not subharmonicity of `mathcal E` itself, reduces the sign problem
on every regular two-dimensional wall sheet to one-dimensional
double-tight branches and explicit puncture-limit obligations.

This is a proved analytic reduction.  It does **not** yet prove `EX-W`: the
double-tight branches and the puncture limits still have to be certified.

## 2. A global coordinate on the critical-root cover

Recall

```text
F_mu(x)=x^2(x^3+5x^2+10x+10+mu),
C_mu(x)=5x^3+20x^2+30x+20+2mu,
g(x)=(1/2)x^3(3x^2+10x+10),
F_mu(x_j)=-g(x_j) when C_mu(x_j)=0.                  (W5)
```

Solving `C_mu(u)=0` for `mu` gives (W1), and exact division gives

```text
C_{mu(u)}(x)
 =5(x-u)(x^2+(u+4)x+(u^2+4u+6)).                    (W6)
```

Hence the normalization of the critical-root cover is simply the `u`-plane;
the other two critical roots are quadratic over it.  Critical-root
collisions cause no label singularity on this cover.

The exceptional values are also explicit:

```text
lambda(u)=0
  iff u=0 or 3u^2+10u+10=0,

mu(u)+10=-(5/2)u(u^2+4u+6),                         (W7)

3u^2+10u+10=0
  implies 27mu(u)^2+140mu(u)+200=0.
```

Thus the active-gap-zero images are `mu=-10` and

```text
mu_* = (-70 +- 10 i sqrt(5))/27.                    (W8)
```

At a root of `3u^2+10u+10`, the polynomial itself factors exactly as

```text
F_{mu(u)}(x)=x^2(x-u)^2(x+5+2u).                    (W9)
```

The two `mu_*` values are regular double-hub parameters but carry a zero
foreign gap.  In contrast, `mu=-10` makes the hub at `x=0` triple, including
on the two lifts `u=-2+-i sqrt(2)` where the selected foreign gap is nonzero.

## 3. Fifth-root gap normalization freezes the ray

Work locally where `lambda != 0`.  Choose a holomorphic fifth root
`alpha^5=lambda`, put

```text
c=alpha^{-1},  x=alpha y,  s=|lambda| tau,
P_{u,alpha}(y)=alpha^{-5}F_{mu(u)}(alpha y).          (W10)
```

Then

```text
P_{u,alpha}(y)
 =y^5+5cy^4+10c^2y^3+(10+mu)c^3y^2,                (W11)

P_{u,alpha}(y)-(y+c)^5
 =mu c^3y^2-5c^4y-c^5.                              (W12)
```

The wall relation (W2) gives

```text
e^{-i phi}=eps i lambda/|lambda|,
F_mu(x)=e^{-i phi}s
  iff P_{u,alpha}(y)=eps i tau.                      (W13)
```

The moving physical ray is therefore the fixed ray `eps i[0,infinity)`.
For any other critical gap `h`, the chamber inequality becomes

```text
Re(e^{i phi}h)>=0
  iff eps Im(conj(lambda)h)>=0.                      (W14)
```

The strict inequalities in (W14) define the interior of a lifted sheet;
equality for another gap is exactly its double-tight boundary.  The active
critical value is `-lambda`, hence the normalized value `-1`, and no
critical value lies on the fixed ray for positive `tau` anywhere in a
regular sheet neighborhood.

Euclidean quantities scale by `|alpha|`:

```text
length_x=|alpha| length_y,
|1+x|=|1+alpha y|=|alpha| |c+y|.                    (W15)
```

Since `|alpha|=|lambda|^(1/5)`, the normalized pair excess in `y` is exactly
the function `U` in (W3).  Changing the local fifth root rotates `y` by a
fifth root of unity and changes neither `U` nor its pair of arms.

## 4. Proof of Theorem W

Let `y_+(tau;u),y_-(tau;u)` be the two inverse branches of (W13) born at
the double hub `y=0`.  On a regular sheet `mu != -10`; the coefficient of
`y^2` in (W11) is nonzero.  For `tau>0` the fixed ray meets no critical
value, so the implicit function theorem gives locally holomorphic branches
in `u`, with

```text
partial_tau y_a = eps i / partial_y P(y_a).          (W16)
```

For fixed `tau`, the right side is a nonzero holomorphic function of `u`.
Therefore its modulus is subharmonic.  Near `tau=0` it is
`O(tau^{-1/2})`, locally uniformly, and hence integrable.  It follows that
for every finite `T`, the pair sum

```text
V_T(u)=sum_{a in {+,-}}[
    integral_0^T |partial_tau y_a| d tau - T^(1/5)] (W17)
```

is subharmonic.

Identity (W12) supplies the terminal comparison without a moving
parameter-dependent normalizer.  On either monic tract, `|y|=O(T^(1/5))`;
the defect on the right of (W12) is only quadratic in `y`.  Consequently,
locally uniformly in `u`,

```text
|c+y_a(T)|-T^(1/5)=O(T^(-2/5)) -> 0.                (W18)
```

Using (W15), the locally uniform limit of (W17) is exactly

```text
lim_{T->infinity} V_T(u)=U_{u,eps}.                  (W19)
```

A locally uniform limit of subharmonic functions is subharmonic.  Arm swaps
under continuation disappear in the pair sum, so the locally proved
functions glue.  This proves the first assertion of Theorem W.

The universal chamber is compact, and the finite critical-root cover over
it is compact.  Excise small neighborhoods of `lambda=0` and `mu=-10` from
a lifted sheet component.  The ordinary maximum principle puts the maximum
of `U` on the resulting boundary.  Every nonexceptional sheet boundary has
equality in one of the two remaining inequalities (W14), hence is
double-tight.  Shrinking the excisions gives (W4).  This proves the second
assertion.  Notice that multiplying `U` by the varying positive function
`|lambda|^(1/5)` would not preserve subharmonicity; only equality of signs is
used.

## 5. The double-tight boundary has a degree-ten one-parameter cover

Let `x` and `v` be two critical roots over the same `mu`, with `g(x)!=0`.
After dividing `C_mu(v)-C_mu(x)` by `v-x`, distinct roots satisfy

```text
q_x(v)=v^2+(x+4)v+(x^2+4x+6)=0.                    (W20)
```

They are simultaneously tight exactly when their gap ratio is real.  Order
the pair so that

```text
t=g(v)/g(x) is real,  |t|<=1.                       (W21)
```

Eliminating `v` from (W20) and `g(v)=t g(x)` gives the exact implicit carrier

```text
P_t(x)=Res_v(q_x(v),2(g(v)-t g(x)))

 =9(t^2+t+1)x^10
 +(60t^2+60t+150)x^9
 +(160t^2+100t+1180)x^8
 +(200t^2-240t+5700)x^7
 +(100t^2-1260t+18600)x^6
 +(42616-2144t)x^5
 +(69120-1680t)x^4
 +(78000-480t)x^3
 +58320x^2+25920x+5184.                             (W22)
```

This is an implicit algebraic cover, not a single-valued rational
parametrization.  Generically its second root is nevertheless recovered by
one rational formula.  Reduction modulo `q_x` gives

```text
2(g(v)-t g(x)) == -M(x)v-N_t(x) mod q_x,             (W23)

M=(x^2+6x+6)(3x^2+8x+8),

N_t=3tx^5+10tx^4+10tx^3
    +3x^5+24x^4+84x^3+156x^2+156x+72,

v=-N_t/M.                                           (W24)
```

Moreover,

```text
P_t=N_t^2-(x+4)N_tM+(x^2+4x+6)M^2.                 (W25)
```

So when `M=0`, `P_t=0` forces `N_t=0` and the reduced gap equation vanishes
identically; this is a genuine finite exceptional fibre, not an extraneous
resultant root.  Its ratio values satisfy

```text
Res_x(M,P_t)
 =15850845241344(2t^2-2t-1)^2(32t^2-32t+9)^2.       (W26)
```

On `[-1,1]` only

```text
t_*=(1-sqrt(3))/2                                   (W27)
```

is real; its sole `M=0` branch is the already isolated tangent orbit, while
the remaining branches are generic.

The complete branch-event calculation is even smaller:

```text
Res_x(P_t,partial_x P_t)=const *
 t^4(t-1)^4(t^2+t+1)(2t^2-2t-1)^2
 (9t^2-32t+32)(9t^2+14t+9)(32t^2-32t+9)^3.         (W28)
```

The four displayed quadratics other than `2t^2-2t-1` have negative real
discriminant, and the leading coefficient `9(t^2+t+1)` never vanishes on
the real line.  Hence the only real branch events on the ordered compact
interval are

```text
t=t_*,  t=0,  t=1.                                  (W29)
```

The endpoint fibres factor as

```text
P_0=(x^2+4x+6)^3
    (9x^4+42x^3+82x^2+72x+24),

P_1=(3x^2+8x+6)^3
    (x^4+2x^3+10x^2+24x+24).                        (W30)
```

The powers in (W30) are elimination multiplicities; each displayed factor
is squarefree and the two factors in each line are coprime.  The `t=0`
fibre contains the gap-zero endpoints over `mu=-10` and `mu_*`; the `t=1`
fibre contains collision/equal-gap cases and duplicate ordered pairs.

Thus the ordinary boundary is a finite family of analytic complex-root
branches over the three regular real intervals

```text
(-1,t_*), (t_*,0), (0,1),                            (W31)
```

plus the four finite endpoint/event fibres `-1,t_*,0,1`.  Exact complex
root isolation and interval-Newton continuation on (W31), followed by the
third-gap chamber filter and a one-dimensional arm certificate, is a
complete finite route for the double-tight part of `EX-W`.

The later theorem `QuinticDoubleTightCriticalValueCarrier.md` compresses
this route further.  It eliminates the critical-root labels in favor of the
unordered invariant `kappa=t/(1+t^2)`, proves a complete five-event carrier
with exactly five upper-half-plane `mu` branches on four regular intervals,
recovers the pair direction rationally, and puts both hub arms on one compact
parameter interval regular at the hub and infinity.  The degree-ten
root-cover algebra above remains a valid independent derivation, but is no
longer the smallest exact atlas target.

## 6. Exact residual after this reduction

The model wall problem now has exactly one honest residual.  The former
direction-dependent triple-hub limits over `mu=-10` have been closed exactly
by `QuinticMinusTenWallLimitSideArmCertificate.md`, and the former active
gap-zero fibres over `mu_*` have been closed exactly by the endpoint theorem
plus angular interpolation described below.

1. **Regular double-tight branches.**  Execute the finite compact atlas of
   `QuinticDoubleTightCriticalValueCarrier.md`: four `kappa` intervals, five
   conjugacy-reduced `mu` branches, two arms, and one compact arm parameter.
   This replaces both the former two-real-dimensional wall atlas and the
   larger ordered-root cover (W22)--(W31).  The event-excision theorem
   `QuinticDoubleTightCompactAtlas.md` already proves negativity on relative
   neighborhoods of `kappa_-,0,kappa_+`, so only disjoint compact regular
   branch truncations remain to certify.

The active gap-zero fibres are no longer residuals.  At each `mu_*` in (W8),
the zero gap is tight for every allowed phase.  The exact theorem
`QuinticMuStarEndpointExcessCertificate.md` proves the two representative
endpoint pairs below `-47/125` and `-2/5`; the short-sector maximum principle
of `QuinticMuStarAngularFiberReduction.md` propagates the common bound
`-3/8` across the full half-circle, and conjugation handles the other `mu_*`.
The global phase-Sturm theorem `PhiConvexitySturmBound.md` supplies an
independent propagation proof.  Continuity of the regular arm system then
forces `U->-infinity` on adjacent normalized sheets, closing both punctures.

For completeness, the triple-hub theorem classifies the three approach-lobe
pairings as `{T_0,T_1}`, `{T_1,T_4}`, and `{T_0,T_4}`.  Its new shallow arm
has excess below `-13/15`; combined with the two earlier endpoint-arm bounds,
the three pair ceilings are `-23/30`, `-1/80`, and `-47/48`.  Hence every
nonzero-active `mu=-10` puncture limsup in (W4) is strictly negative.

Critical-root collisions introduce no additional analytic singularity on
the normalized `u`-cover.  Active collisions already occur in the
double-tight carrier, and inactive collisions are handled without choosing
an ordering of the remaining quadratic roots.

Once the single compact-atlas residual above is negative, Theorem W proves
`EX-W`; `QuinticChamberWallReduction.md` then proves `EX-U`.  The
model-to-real transfer, degree-five theorem, and unrestricted Erdős 1041
remain separate later obligations.

## 7. Claim boundary

The subharmonicity theorem and maximum-principle reduction are ordinary
proved mathematics.  The checker replays exactly the active-root cover,
gap normalization, fixed-ray convention, Euclidean scaling, exceptional
fibres, degree-ten boundary carrier, reconstruction formula, denominator
exceptions, full discriminant, and endpoint factorizations.  The later
critical-value carrier has its own exact checker for the smaller unordered
cover and compact arm chart.

The checker does not replace the analytic proof of subharmonicity, and this
note does not claim that the remaining compact double-tight atlas has already
been certified.  The `mu=-10` and `mu_*` exceptional inputs are now closed by
their separate exact certificates.  In particular this note does not prove
`EX-W`, `EX-U`,
model-to-real transfer, the degree-five theorem, or unrestricted Erdős
1041.
