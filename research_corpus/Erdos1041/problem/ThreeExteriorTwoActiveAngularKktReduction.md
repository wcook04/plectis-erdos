# Erdős 1041: canonical chamber for a smooth two-active selector contact

## Theorem

Fix `n in {5,6}` and a strict-speed three-exterior configuration

```text
a_k=r_k exp(i theta_k),       0<r_k<1,
```

in a smooth interior chart.  Suppose exactly the rays `0,1` are active at a
nonregular first contact of the true selector, and that their optimized
barriers have unique nondegenerate interior maximizers `q_0,q_1`.  Rotate so
that

```text
theta_0=0,       theta_1=A,       theta_2=B.             (1)
```

Then the nonsmooth KKT multiplier is genuinely mixed: there are
`lambda in (0,1)` and `t=lambda/(1-lambda)>0`.  Put

```text
K(q,r,x)=q r(1-q^2)(1-r^2)
          /[(q^2+r^2-2qr cos x)(1+q^2r^2-2qr cos x)]>0, (2)

a=K(q_0,r_1,A) sin A,
b=K(q_0,r_2,B) sin B,
c=K(q_1,r_0,A) sin A,
d=K(q_1,r_2,B-A) sin(B-A).                             (3)
```

The complete angular KKT system is

```text
d=-t b,             c=-t(a+b),                         (4)
d(a+b)=bc.                                               (5)
```

It has precisely two geometric branches.

1. **Collinear branch:** `sin A=sin B=sin(B-A)=0`.
2. **Genuinely angular branch:** after reflection, relabelling the two active
   rays, and choosing representatives modulo `2pi`,

   ```text
   0<A<pi<B<A+pi<2pi,                                  (6)
   b/a<-1,       sign d=sign c=sign a=-sign b.          (7)
   ```

The signed chamber has a positive **three-edge tension law**.  Write
`C=B-pi`, so `0<C<A`, abbreviate

```text
K_01=K(q_0,r_1,A),       K_10=K(q_1,r_0,A),
K_02=K(q_0,r_2,B),       K_12=K(q_1,r_2,B-A),

w_01=lambda K_01+(1-lambda)K_10,
w_02=lambda K_02,        w_12=(1-lambda)K_12.
```

Then angular stationarity is equivalently

```text
w_01 sin A=w_12 sin(A-C)=w_02 sin C.                  (7a)
```

In particular the multiplier and the remaining angular equation are

```text
t=K_12 sin(A-C)/(K_02 sin C),

K_10 sin A
 =K_12 sin(A-C)[1-K_01 sin A/(K_02 sin C)]>0.         (7b)
```

Thus the bracket in (7b) is strictly positive.  This is a positive-coordinate
replacement for the determinant (5), and is the sharper form for interval
elimination.

Thus a noncollinear two-active contact cannot occur in an arbitrary angular
box.  The third root lies in the unique frustrated sector between the
antipodes of the two active rays, and its angular pull on ray `0` strictly
dominates the active-root pull there.

There is a simultaneous radial reduction.  For an active ray `j` define

```text
S_jk=1/2[P_(q_j a_k)(u_j)-P_(a_k/q_j)(u_j)],
T_k=lambda S_0k+(1-lambda)S_1k.                        (8)
```

Fixed-product radial stationarity is exactly

```text
T_0=T_1=T_2.                                            (9)
```

Consequently the whole smooth two-active contact has been reduced to the
canonical chamber (6), the angular determinant (5), two independent radial
equalities from (9), the two one-variable optimizer equations

```text
sum_k[P_(q_j a_k)(u_j)+P_(a_k/q_j)(u_j)]=2n, j=0,1,   (10)
```

and the two contact equations

```text
V_0=V_1=R_n(r_0r_1r_2).                                (11)
```

At a first upward scale contact the source-current true-selector theorem adds

```text
sum_k P_(q_j a_k)(u_j)>=C_*,       j=0,1.              (12)
```

No free angular sign choices or endpoint KKT weights remain.

## Proof

For one spectator zero at relative angle `x`, write

```text
N=q^2+r^2-2qr cos x,
D=1+q^2r^2-2qr cos x.
```

Differentiating `log rho=(log N-log D)/2` gives

```text
partial_x log rho
 =qr sin x(D-N)/(ND)
 =K(q,r,x) sin x,                                      (13)
```

because `D-N=(1-q^2)(1-r^2)`.  Therefore the angular
gradients of the two optimized log barriers in the coordinates `(A,B)` are

```text
g_0=(a,b),             g_1=(c-d,d).                    (14)
```

The envelope theorem removes the `q_j` derivatives.  Nonsmooth stationarity
gives `lambda g_0+(1-lambda)g_1=0`.  An endpoint multiplier would make one
active optimized barrier stationary by itself.  The algebra in
`ThreeExteriorUniqueActiveContactExclusion.md` uses only that stationarity,
not uniqueness of the active set: it forces all three zeros to be coincident
on the selected ray and then contradicts the strict polarization inequality
at `V_j=R_n`.  Hence `0<lambda<1`.

Divide the two coordinates of the KKT equation by `1-lambda`.  They become

```text
t a+c-d=0,             t b+d=0,
```

which are exactly (4).  Taking the determinant of the two gradients gives
(5).

If `sin A=0`, then `a=c=0`; (4) successively gives `b=d=0`.  Positivity of
the kernels in a smooth contact chart yields the collinear branch.  Otherwise
`a` and `c` have the same nonzero sign.  The second equation in (4) makes
`d` opposite to `b`, while the first gives

```text
(a+b)/a<0.
```

Thus `b/a<-1`, and `c,d` have the sign of `a`.  Reflect if necessary so
`sin A>0`, and take `0<A<pi`, `0<=B<2pi`.  The sign conditions say

```text
sin B<0,        sin(B-A)>0.
```

The first puts `B` in `(pi,2pi)`.  Since then `0<B-A<2pi`, the second puts
`B-A` in `(0,pi)`, proving (6)--(7).

In this chamber `sin B=-sin C` and `sin(B-A)=sin(A-C)`.  Group the two
contributions on the active edge `01`.  The two coordinates of the weighted
KKT equation become exactly the two equalities in (7a).  The second gives the
formula for `t`; substituting it into the first and isolating the `K_10` term
gives (7b).  Positivity of every factor on the left forces the bracket to be
positive.

Finally, direct logarithmic-radius differentiation of one pseudohyperbolic
factor gives

```text
r partial_r log rho(q u,r exp(i theta))
 =1/2[P_(q r exp(i theta))(u)-P_(r exp(i theta)/q)(u)]. (15)
```

The fixed-product tangent space consists of log-radius variations whose
coordinates sum to zero.  A linear form vanishes on that plane exactly when
its three coefficients agree.  Applied to the weighted KKT gradient, (15)
is (8)--(9).  Equations (10)--(12) are respectively the optimizer equation,
active equality, and the already proved true-selector scale-contact
inequality.  ∎

## Frontier effect and exact boundary

This removes endpoint multiplier faces and five of the six noncollinear
angular order chambers from the smooth two-active contact atlas.  It also
replaces four unconstrained configuration-gradient equations by one positive
tension equation and two radial coefficient equalities.  The reduction is
particularly suited to interval/Krawczyk exclusion because every sine and
every displayed factor in (7b) has a fixed sign.

Still open are exclusion of solutions of (5), (9)--(12) in the canonical
chamber, the collinear two-active branch, three-active switches,
optimizer-switch cells, and the named speed/collision/radial boundaries.  No
finite-selector theorem or unrestricted Erdős 1041 theorem is claimed.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_two_active_angular_kkt.py
```

```text
tao_pipeline_receipt:
  input_stage: true-selector contact plus smooth two-active KKT system
  output_stage: canonical angular chamber and radial coefficient reduction
  artifact: ThreeExteriorTwoActiveAngularKktReduction.md plus symbolic checker
  human_understanding_delta: a noncollinear two-active contact is a frustrated three-direction equilibrium in one fixed angular chamber, not an arbitrary five-variable contact
  verification_state: ordinary exact proof plus symbolic identity replay
  publication_or_review_state: source-level research reduction, not independently reviewed
  canonicalization_state: subordinate switch-cell reduction in the adaptive-minray family
  unresolved_downstream_bottleneck: exclude the canonical chamber, collinear branch, and named constraint boundaries
  next_stage_owner: signed interval elimination or a value-speed tradeoff theorem
```
