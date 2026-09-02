# Erdős 1041: the stationary three-exterior surplus is positive on every one-radius collapse face

## Status

This note proves an exact boundary theorem for the stationary radial surplus in
`ThreeExteriorGreenPolarization.md`.  In the scale-free variables

```text
r_1=q u,  r_2=q v,  r_3=q w,  t=q^2,
```

the continuous stationary expression on the face `u=0` is strictly positive
for `0<t<1` and `0<v,w<1`.  The proof is a bit-replayable rational identity
and tensor-Bernstein certificate.  It removes all three one-radius-collapse
faces from the possible zero or negative locus of the compactified stationary
problem.

It does **not** prove a positive-width collar `u>0`, the fully distinct
positive-radius interior, GP3, or unrestricted Erdős 1041.

## 1. Scale-free kernel and the variance identity

Put

```text
A(x)=1+x+x^2,
D_t(x)=1+t x+t^2 x^2,
L_t(x)=(1-x^2)/A(x)^2+t(1-t^2x^2)/D_t(x)^2.             (1)
```

If `a,b,c>0` are the three tangent weights, their entire stationary angular
correction is

```text
T(a,b,c)
 =1/2(a+b+c-ab/c-ac/b-bc/a)
 =-1/4[c(a-b)^2/(ab)+b(a-c)^2/(ac)+a(b-c)^2/(bc)].     (2)
```

Equivalently, for `x=1/a,y=1/b,z=1/c`,

```text
T=-((x-y)^2+(y-z)^2+(z-x)^2)/(4xyz).                   (3)
```

Thus the correction is an exact reciprocal-variance penalty, rather than a
six-term rational expression with hidden cancellation.

There is also a useful monotonicity built into (1).  For

```text
f(x)=(1-x^2)/(1+x+x^2)^2
```

one has

```text
f'(x)=2(x^3-3x-1)/(1+x+x^2)^3<0   (0<x<1),             (4)
L_t(x)=f(x)+t f(tx),
L_t'(x)=f'(x)+t^2 f'(tx)<0         (0<t,x<1).           (5)
```

In particular `L_t` is positive and strictly decreasing.  The pair weights
in the scale-free stationary formula are

```text
alpha_ij=u_i u_j(L_t(u_i)+L_t(u_j)).                    (6)
```

## 2. The exact collapsed-face formula

Let

```text
Q_x=A(x)^2D_t(x)^2,
N_x=(1-x^2)D_t(x)^2+t(1-t^2x^2)A(x)^2,
K_x=(1+t)Q_x+N_x,
M_vw=N_vQ_w+N_wQ_v.                                    (7)
```

Then `L_t(x)=N_x/Q_x`, `L_t(0)+L_t(x)=K_x/Q_x`, and
`L_t(v)+L_t(w)=M_vw/(Q_vQ_w)`.

Before the stationary correction, the scale-free residual on `u=0` collapses
without expansion to

```text
R_0(t;v,w)
 = h(v)+h(w)+p(v,w)+p(w,v)-2(v+w),                     (8)

h(x)=x/(1-x)+t x^2/(1-tx),
p(a,b)=a(1+b/2)/A(b)-t a b(tb+1/2)/D_t(b).
```

Indeed the two pairs involving the zero radius contribute `v+w`, while the
regular comparator contributes `-3(v+w)`; its product-dependent second term
vanishes.  Taking the stationary correction continuously to `u=0` gives

```text
S_0(t;v,w)=R_0(t;v,w)+vw M_vw/(2Q_vQ_w)
 -v^2 K_v M_vw/(2Q_v^2K_w)
 -w^2 K_w M_vw/(2Q_w^2K_v).                            (9)
```

All apparent `0/0` terms have disappeared in (9).

## 3. Exact positivity certificate

Clear (9) by

```text
C=(1-v)(1-tv)(1-w)(1-tw)Q_v^2Q_w^2K_vK_w.             (10)
```

Every factor in `C` is strictly positive on the open unit cube.  Write
`P=C S_0`.  Exact sparse arithmetic gives

```text
deg_(t,v,w) P=(28,28,28),
number of monomials=13206.                              (11)
```

The polynomial is symmetric in `v,w`, and its first nonzero homogeneous part
at `v=w=0` is the positive cubic

```text
[P]_(deg(v,w)=3)
 =6(1+t)^2(1+t^2)(v+w)(2v^2-3vw+2w^2).                (12)
```

The quadratic in the last factor is positive definite.

By symmetry it is enough to take `0<v<=w` and write `v=s w`, `0<s<=1`.
Equation (12) shows, and exact division verifies, that

```text
P(t,sw,w)=w^3 P_ord(t,s,w).                             (13)
```

The quotient has degrees

```text
deg_(t,s,w) P_ord=(28,28,50).                           (14)
```

Its exact tensor Bernstein expansion on `[0,1]^3` has

```text
29*29*51 = 42891 coefficients,
42829 strictly positive,
62 zero,
0 negative.                                            (15)
```

The `s=1` Bernstein face contains strictly positive coefficients as well, so
the ordered chart includes the isosceles boundary.  Since every Bernstein
basis function is positive in the open cube, (15) proves
`P_ord(t,s,w)>0` for `0<t,w<1`, `0<s<=1`.  Equations (10) and (13), followed
by symmetry, yield the theorem.

> **Collapsed-face theorem.** For every `0<t<1` and `0<v,w<1`,
>
> ```text
> S_0(t;v,w)>0.                                         (16)
> ```

The coefficient stream has SHA-256 digest

```text
f8ebe74d98bf3ef8ff3ced244af64de6e972d6667ba62e50e79f621c3bf731a1.
```

## 4. Replay and exact boundary

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_collapsed_face.py
```

The replay verifies (2), (4), the hand-cleared formula at three independent
exact rational points, symmetry, the cubic identity (12), the ordered chart,
two independent exact Bernstein evaluations, all coefficient signs, and the
coefficient digest.

The theorem is a compactification result.  It proves that a fully distinct
stationary counterexample cannot converge to a face where exactly one scaled
radius vanishes while the other two stay positive.  It does not supply the
uniform transverse derivative bound needed to thicken the face into a collar;
the remaining boundary consists of the two-scale corner where at least two
radii collapse, together with the genuinely interior fully distinct region.
