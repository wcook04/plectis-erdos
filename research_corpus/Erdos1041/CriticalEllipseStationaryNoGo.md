# Exact no-go for universal critical-ellipse KKT elimination

## Result

The finite-contact reduction in `CriticalEllipseMinimaxStationarity.md` is a
necessary description of a minimizer.  It is **not** an upper-bound certificate
for every stationary system.  The exact quartic below has an interior
one-contact critical KKT point whose level is strictly above `Gcrit`.

This is not a counterexample to CE--GM or Erdős #1041.  The same selected root
pair has a lower feasible critical hub.  The result kills only the proposed
elimination

```text
every finite-contact stationary system has level <= Gcrit.
```

The corrected stationary target is existential: at least one KKT branch must
have level at most `Gcrit`.

## Exact witness

Put

```text
c* = -7/10 - 9i/20,       h = -3/10 - i/5,
a  = -13/20 - 3i/4,       b = -9/10 - i/5,
c2 = 4831/9700 + 623i/2425.
```

Let

```text
f(z) = z^4 + (1623+1271i)z^3/2425
       + (-40944-59293i)z^2/97000
       + (21116-325513i)z/485000
       + (-38470+229487i)/1940000.
```

Exact expansion gives

```text
f'(z) = 4(z-c*)(z-h)(z-c2).
```

The polynomial factors as `(z-a)(z-b)(z^2+q1 z+q0)`, with

```text
q1 = (-8543-4131i)/9700,
q0 = (10033+7811i)/97000.
```

The two displayed roots satisfy `1-|a|^2=3/200` and
`1-|b|^2=3/20`.  The strict quadratic Schur--Cohn gaps for the other
factor are

```text
9533327/9700000,
22223888608029/94090000000000,
```

so all four roots lie in the open unit disc.  Applying the same reciprocal
quadratic test after translating by `c*` shows the two unlabelled roots are
more than `1/2` from `c*`; the exact gaps are

```text
199970789/204820789,
20189808506749521/41951555606582521.
```

Since

```text
|c*-a|^2=37/400,          |c*-b|^2=41/400,
```

`a,b` are exactly the two nearest roots to `c*`.

## Critical-value and ellipse certificates

Writing `V*=|f(c*)|^2`, `H=|f(h)|^2`, and `V2=|f(c2)|^2`, exact evaluation
gives

```text
V* = 310713136913/12416000000000,
H  = 27084213/485000000,
V2 = 87929920831854142093/1416468496000000000000.
```

The strict ordering gaps are

```text
H-V*  = 382642715887/12416000000000,
V2-V* = 1640077640035291749/44264640500000000000.
```

Thus `c*` uniquely minimizes the critical-value modulus.  If
`rho=|f(c*)|^(1/4)`, then `V*>(63/100)^8`, while

```text
|h-a| < 33/50,            |h-b| = 3/5.
```

Therefore `|h-a|+|h-b|<63/50<2 rho`: the bad stationary hub is strictly
inside the sharp critical ellipse.

On either arm `r=a,b`, convert

```text
H - |f(h+t(r-h))|^2
```

after division by `t^2` to degree-six Bernstein form.  All fourteen controls
are strictly positive; their minimum is `H` itself.  Hence the common hub is
the unique maximum on both arms.  Since `f'(h)=0`, the single active gradient
is zero, so this is an interior one-contact KKT point.

For a quartic, `|f(h)|>Gcrit` is equivalent to `H^2>V*V2`.  The exact gap is

```text
27524087520828329414378574621091
---------------------------------------------------  > 0.
17586872846336000000000000000000000
```

Thus a stationary branch can lie comfortably above the target level.

## Why CE--GM still succeeds

At `c*`, both analogous arm gaps have all-positive degree-six Bernstein
controls, with minimum `V*`.  Moreover

```text
|c*-a|<31/100,            |c*-b|<33/100,
```

so the broken line through `c*` has length below `16/25`.  Because the other
two critical values are larger, `|f(c*)|<Gcrit`.  This exact witness therefore
satisfies CE--GM with a large margin.

## The missing second-order filter

At a nonroot simple critical hub let

```text
C = conjugate(f(h)) f''(h),
Q(w) = Re(C w^2),
B(u,v) = Re(C u v).
```

For `u_a=a-h` and `u_b=b-h`, the witness has

```text
Q(u_a)    = -7748379/97000000,
Q(u_b)    = -546719301/6062500000,
B(u_a,u_b)= -7986141/50000000.
```

The two arms occupy the same negative saddle cone.  With `D=u_a+u_b`,

```text
Q(D)<0,   B(D,u_a)<0,   B(D,u_b)<0.
```

Taylor expansion near the hub and the strict arm gap away from it show that
moving a small positive distance in direction `D` lowers the entire two-arm
maximum.  The exact rational point

```text
h_down = h + (u_a+u_b)/1000
       = -6019/20000 - 4011i/20000
```

already gives a finite certificate: all degree-eight Bernstein controls of
`H-|f|^2` on both moved arms are positive.  Consequently the bad KKT point is
a saddle, not a minimizer.

In particular, a generic critical-contact local minimizer with strict hub
maxima must satisfy the necessary sign

```text
Re(conjugate(f(h)) f''(h) (a-h)(b-h)) >= 0.
```

This filter removes the exact false positive, but it does not by itself prove
that some surviving branch lies below `Gcrit`.

## Corrected stationary formulation and scope

Let `M(h)` be the maximum of `|f|` on the two selected arms over the closed
critical ellipse, and let `S` be the full finite-contact KKT set, including the
ellipse normal cone.  Compactness and the finite-contact theorem give only

```text
min_{h in E} M(h) = inf_{h in S} M(h).
```

Therefore the exact KKT formulation of CE--GM is

```text
inf_{h in S} M(h) <= Gcrit,
```

not a pointwise upper bound on `S`.

The companion standard-library checker reconstructs every rational identity,
Schur gap, Bernstein certificate, threshold comparison, and descent witness.
`CriticalEllipseStationaryNoGo.lean` checks the derivative factorization,
critical-value scalars, threshold gap, second-order signs, and the generic
same-cone descent-sign kernel.  Schur--Cohn, the Bernstein-to-segment
interpretation, KKT/Danskin, and the analytic Taylor compactness step remain
ordinary mathematics.

This exact no-go retires one CE--GM elimination strategy.  It does not refute
CE--GM, the tied-Newton-face joint selector, or unrestricted Erdős #1041.

