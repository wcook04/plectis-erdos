# Erdős 1041: the tight-gap wall-sheet maximum principle is degree-uniform

Date: 2026-08-30. Exact algebra replay:
`scripts/check_erdos1041_all_degree_wall_sheet_subharmonic.py`.
Consumes `AllDegreePhaseSturmReduction.md` and generalizes the analytic core of
`QuinticWallSheetSubharmonicReduction.md`.

## 1. Setting

Let `M` be a complex parameter manifold carrying a holomorphic family of
centred monic polynomials

```text
H_a(z)=z^n+R_a(z),             deg R_a<=n-2,          n>=2.       (W1)
```

On a regular critical-root cover suppose that `c(a)` and `u(a)` are distinct
holomorphic critical points, `c` is simple, and

```text
lambda(a)=H_a(u(a))-H_a(c(a)) != 0.                              (W2)
```

Choose one of the two wall orientations `epsilon in {+1,-1}` and put

```text
d(a)=epsilon i lambda(a)/|lambda(a)|.                            (W3)
```

Thus the selected foreign critical gap is perpendicular to the outward value
ray.  Work on an open regular wall-sheet domain `D` on which the two inverse
arms born at `c` along

```text
H_a(z)=H_a(c)+d(a)s,             s>0,                            (W4)
```

meet no further critical value and keep fixed continuation combinatorics.  If
`z_+` and `z_-` are those arms, define their outward pair excess by

```text
E(a)=sum_{q in {+,-}} lim_{S->infinity}
       [ integral_0^S |partial_s z_q| ds - |z_q(S)| ].          (W5)
```

This is the scale-free metric appearing in the near-Fekete model problem.  It
is not the finite descending-arm functional of an arbitrary polynomial.

> **All-degree wall-sheet theorem.**  On every such regular sheet,
>
> ```text
>             U(a)=E(a)/|lambda(a)|^(1/n)                       (W6)
> ```
>
> is plurisubharmonic.  It is independent of the local choice of an `n`-th
> root of `lambda` and glues across permutations of the two arms.

Consequently, on every relatively compact regular wall-sheet subdomain on
which `U` extends continuously to the boundary,

```text
sup_D U <= sup_(partial D) U.                                  (W7)
```

For a trace-max chamber, its ordinary boundary consists of additional tight
critical gaps together with critical collisions, a vanishing normalizing gap,
and whatever boundary belongs to the chosen coefficient compactification.
Thus a regular one-tight wall has no strict interior maximum.  This is a
degree-uniform reduction; it is not a proof of the signs on the surviving
multiple-tight or degenerate strata.

## 2. The tight-gap normalization freezes the ray

Work locally on `D` and choose a holomorphic root

```text
alpha^n=lambda.
```

Put

```text
x=z-c,        x=alpha y,        s=|lambda| tau,
P_a(y)=lambda^-1 [H_a(c+alpha y)-H_a(c)].                       (W8)
```

Then (W3)--(W4) become

```text
P_a(y)=epsilon i tau.                                           (W9)
```

The moving physical ray is therefore the fixed ray
`epsilon i (0,infinity)` in every local parameter chart.  Moreover, with
`C=c/alpha`, the missing `z^(n-1)` coefficient in (W1) gives

```text
P_a(y)=(y+C)^n+Q_a(y),              deg Q_a<=n-2.               (W10)
```

Indeed the difference is

```text
lambda^-1 [R_a(c+alpha y)-H_a(c)],
```

which has the asserted degree.  This two-degree terminal gap is the only
algebraic input needed below.

Let `y_+(tau;a),y_-(tau;a)` be the two branches in (W9).  For `tau>0`,
implicit differentiation gives

```text
partial_tau y_q=epsilon i/(partial_y P_a)(y_q).                 (W11)
```

It is a nonzero holomorphic function of `a` on the regular sheet.

## 3. Proof of plurisubharmonicity

For finite `T`, define

```text
V_T(a)=sum_q integral_0^T |partial_tau y_q| d tau
       -2 T^(1/n).                                             (W12)
```

For fixed positive `tau`, the modulus in (W12) is plurisubharmonic in `a`.
At the simple critical hub, the two branches have the uniform local form

```text
y_q(tau)=+-A(a) tau^(1/2)+O(tau),
partial_tau y_q=O(tau^(-1/2)),                                 (W13)
```

on compact parameter subdomains, so the lower endpoint is locally uniformly
integrable.  Hence each `V_T` is plurisubharmonic.

Let `eta^n=epsilon i` be the terminal direction of one arm.  Equation (W10)
and ordinary inversion at infinity give, locally uniformly in `a`,

```text
y_q(tau)+C=eta tau^(1/n)+O(tau^(-1/n)),
partial_tau y_q=(eta/n)tau^(1/n-1)+O(tau^(-1-1/n)).             (W14)
```

It follows both that the support-defect tail is integrable and that

```text
|y_q(T)+C|-T^(1/n) -> 0.                                      (W15)
```

Lengths and terminal moduli scale by `|alpha|=|lambda|^(1/n)`:

```text
integral |dz|=|alpha| integral |dy|,
|z|=|alpha| |y+C|.                                            (W16)
```

Using (W15)--(W16) in (W5) shows

```text
lim_(T->infinity) V_T(a)=E(a)/|lambda(a)|^(1/n)=U(a),          (W17)
```

locally uniformly on `D`.  A locally uniform limit of plurisubharmonic
functions is plurisubharmonic.  Replacing `alpha` by another `n`-th root of
`lambda` only rotates `y`, while an arm permutation leaves their sum fixed;
therefore the local functions glue.  This proves the theorem.

## 4. Composition with the phase theorem

For the low-mode near-Fekete models

```text
H(z)=z^n+sum_(1<=k<=floor((n-1)/2)) b_k z^k,                   (W18)
```

the trace identity gives `sum H(c_j)=0`.  The phase-Sturm theorem first moves
the pair-excess maximum, for fixed coefficients, to a phase at which one
foreign critical gap is tight.  The present theorem then moves any strict
maximum inside a regular complex wall sheet to its boundary.  If every
foreign gap is tight at a trace-maximal hub, all rotated critical values have
the same real part; the trace identity forces that real part to be zero.
Thus the terminal nondegenerate skeleton consists of critical values on the
supporting line, together with the lower-dimensional partially tight strata
created when the complex wall sheet itself has a real residual.

For `n=5`, the first wall sheet has one complex coordinate and its boundary is
the one-real-dimensional double-tight carrier already isolated in
`QuinticDoubleTightCriticalValueCarrier.md`.  The theorem explains why the
same reduction mechanism is not quintic-specific.  It does **not** make the
remaining real carrier subharmonic; small interior bumps on that carrier are
known and must still be certified or controlled by a different inequality.

## 5. Exact boundary

Proved here: (W6)--(W7) on every regular labelled wall sheet, in every degree,
for centred monic families with the degree-two terminal gap.  The proof is
ordinary several-complex-variable analysis; the checker replays the exact
normalization and terminal-degree identities through degree twelve.

Not proved: extension through `lambda=0`, multiple hubs, or critical-value
collisions; negativity on any multiple-tight real skeleton; compactness of an
arbitrary chosen coefficient normalization; the all-degree model excess
theorem; the actual-polynomial transfer outside already proved regimes; or
unrestricted Erdős 1041.

## 6. Replay

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_all_degree_wall_sheet_subharmonic.py
```
