# Erdős 1041: support--Stieltjes and weighted-cusp reduction on the double-tight carrier

Date: 2026-08-30. Exact replay:
`scripts/check_erdos1041_quintic_double_tight_support_stieltjes.py`.
Consumes `QuinticDoubleTightCriticalValueCarrier.md` and
`QuinticDoubleTightCompactAtlas.md`.

## 1. Result

The compact double-tight atlas need not be certified by subtracting two
large arclength quantities.  After rotating an inverse-ray arm into its
terminal direction, its excess is exactly a nonnegative Stieltjes integral
minus one endpoint support.  Turns, angle extrema, and curvature changes of
the Stieltjes density are finite algebraic sets.

> **Theorem SS (finite support--Stieltjes reduction).**  On every regular
> double-tight arm, split first at the zeros of `Im H'` and then at the
> inflections of the half-angle density defined below.  On each resulting
> interval the bending integral has a Hermite--Hadamard upper bound using
> only two endpoint values, or one midpoint value.  Every splitting point
> is an isolated solution of an explicit polynomial system.  The generic
> turn eliminant has only fifteen residual roots after removal of its two
> endpoint factors.

Near the only weak event, `kappa=0, mu=-10`, the weighted coordinate

```text
kappa=sigma u^3,   mu=-10+sigma u z,   sigma in {+1,-1}               (SS1)
```

makes the carrier regular and turns the apparent parameter-gradient
singularity into a compact polynomial/rational integral.  Consequently the
entire residual, including the cusp, is a finite exact root-isolation and
sign calculation; no limiting continuity radius or improper arclength
subtraction remains.

This note proves the reduction, not the final finite sign calculation.

## 2. Exact rotated arm identity

Let `eta^5=d`, where `eta` is the terminal fifth root reached by the arm,
and set

```text
alpha=conj(eta),   z=alpha x,
nu=(10+mu) alpha^3,
H(z)=z^5+5 alpha z^4+10 alpha^2 z^3+nu z^2.          (SS2)
```

Along the arm `H(z)=s>0`.  Write `z=u+iv` and

```text
H'(z)=A+iB,   R=sqrt(A^2+B^2)>0.                    (SS3)
```

Since `z_s=1/H'=(A-iB)/R^2`,

```text
u_s=A/R^2,   v_s=-B/R^2.                            (SS4)
```

On a cell on which `R+A>0`, put

```text
f=|tan(arg(z_s)/2)|=|B|/(R+A).                      (SS5)
```

Rationalizing with `R^2=A^2+B^2` gives the pointwise identity

```text
|z_s|-u_s = B^2/[R^2(R+A)] = f |v_s|.               (SS6)
```

The compact excess identity (CV25) therefore becomes

```text
e_arm = integral_Gamma f |dv| - Re(alpha).           (SS7)
```

If a cell contains `B=0,A<0`, formula (SS5) is not used there: the original
nonnegative density `|z_s|-u_s` is retained.  Thus the reduction makes no
unproved global forward-projection assumption.

## 3. The finite algebraic event sets

The level curve itself is

```text
Y(u,v):=Im H(u+iv)=0.                               (SS8)
```

The `v`-turns satisfy `Y=B=0`.  If
`alpha=a+ib` and `nu=c+id`, exact elimination gives

```text
Res_u(Y,B)=400 v^2(v+b)^2 R_15(v),                  (SS9)
deg R_15=15.                                        (SS10)
```

The factors `v=0` and `v=-b` are respectively the hub and terminal
endpoint levels.  Thus each ordinary arm has only finitely many interior
monotonicity pieces, with a uniform generic degree bound.

For angle events define

```text
J=Im(H'' conj(H')^2),
Delta=B partial_v-A partial_u.                      (SS11)
```

Along `Y=0`, direct logarithmic differentiation gives

```text
d(arg z_s)/dv = J/(B R^2),
df/dv = sign(-B) J/[B R(R+A)].                     (SS12)
```

Hence angle extrema satisfy `Y=J=0`.  Inflections of `f` on a
`v`-monotone cell satisfy the algebraic system

```text
Y=0,
R^2-A^2-B^2=0,
Delta( J/[B R(R+A)] )=0,                            (SS13)
```

after clearing the displayed nonzero denominator and imposing
`R>0,R+A>0`.  This is a polynomial system in `(u,v,R)`; interval isolation
can reject denominator and sign impostors exactly.

## 4. Quadrature-free upper bounds

Let `[v_0,v_1]` be one monotone piece further split at every solution of
(SS13), and put `h=|v_1-v_0|`.  The sign of the cleared derivative in
(SS13) decides the curvature of `f`.  Hermite--Hadamard gives

```text
f convex:  integral f |dv| <= h [f(v_0)+f(v_1)]/2,
f concave: integral f |dv| <= h f((v_0+v_1)/2).     (SS14)
```

Endpoint and midpoint values are obtained by interval Newton on `(SS8)` at
fixed `v`.  Summing (SS14), adding any exceptional original-density cells,
and subtracting `Re(alpha)` gives a one-sided exact certificate for
(SS7).  Unlike direct arclength quadrature, every term is nonnegative and
there is no subtraction of two divergent quantities.

## 5. Exact resolution of the weak cusp

Let `K_kappa(mu)` be (CV8), choose `sigma=+-1`, and define

```text
H_sigma(u,z)=u^-6 K_{sigma u^3}(-10+sigma u z).      (SS15)
```

Exact expansion proves that `H_sigma` is a polynomial (degree at most
thirteen in `u` and ten in `z`) and

```text
H_sigma(0,z)
 =(2304/625)(z^6+16200z^3+590490000).               (SS16)
```

Its six roots are simple.  The implicit branch derivative is

```text
z'=-H_u/H_z,   mu'=sigma(z+u z').                   (SS17)
```

The reconstructed active-pair sum `P` also has a regular nonzero limit,
and the wall direction satisfies

```text
phi'=-Im[(P_u+P_z z')/P].                           (SS18)
```

For the inverse arms put `x=uX`.  The three model derivatives factor as

```text
A_model=u a,   C_model=u c,   F''=u b,
a=sigma z+10X+5uX^2+u^2X^3,
c=2sigma z+30X+20uX^2+5u^2X^3,
b=2sigma z+60X+60uX^2+20u^2X^3.                   (SS19)
```

Since `dx=u dX`, the apparent singularity in the `mu`-gradient cancels:

```text
|2/C_model-F''/C_model^2| |dx|
   = |2/c-b/c^2| |dX|,                              (SS20)

|Im(F'' A_model/C_model^2)| |dx|
   =u |Im(ba/c^2)| |dX|.                            (SS21)
```

An inner `x=uX` chart and the reciprocal outer chart `u=xv`, followed by
the compact terminal chart (CV20), therefore turn the cusp gradients into
finite interval integrals on compact boxes.

For example, the following four rational inequalities form a sufficient
exact cusp certificate on `0<=u<=10^-4`:

```text
|mu'|<=30,   |phi'|<=6,
G_mu<=2,     G_phi<=8.                              (SS22)
```

Indeed the chain-rule constant is then at most `108`.  The already proved
worst limiting ceiling is `-1/80`, so

```text
mathcal E(u) <= -1/80+108u <= -17/10000 <0.          (SS23)
```

Thus (SS22), once replayed on the displayed compact charts, closes the
explicit punctured neighborhood `0<|kappa|<=10^-12`.

## 6. Exact remaining boundary

Theorem SS replaces the former two-dimensional arclength atlas by:

1. isolation of finitely many roots of (SS9) and (SS13);
2. rational interval evaluation of the finite sum (SS14);
3. the four compact cusp inequalities (SS22).

No assertion is made here that those final interval signs have already
been replayed.  In particular this note alone does not prove the compact
double-tight sign theorem, `EX-W`, `EX-U`, degree five, or unrestricted
Erdős 1041.
