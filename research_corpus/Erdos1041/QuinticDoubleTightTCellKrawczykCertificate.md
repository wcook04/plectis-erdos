# Erdős 1041: first exact regular double-tight parameter cell

Date: 2026-08-30. Exact replay:
`scripts/check_erdos1041_quintic_double_tight_tcell_krawczyk.py`.
Consumes `QuinticDoubleTightCriticalValueCarrier.md` and
`QuinticSupportDefectEngine.md`.

## 1. Result

Write the two selected critical gaps as `a` and `b=t a`, with real
`-1<=t<=1`.  On the complete interval

```text
4999/5000000 <= t <= 5001/5000000,                  (TC1)
```

the checker proves that the weak upper-half-plane branch through

```text
a  = 6.8103735129... - 56.0253967665... i,
mu = -13.1212730489... + 1.7637781695... i           (TC2)
```

is a unique regular analytic carrier branch, remains in one strict wall
chamber, and its paired inverse-ray excess satisfies the uniform exact bound

```text
mathcal E < -1/10.                                   (TC3)
```

The checker supplies two independent exact sign proofs on the whole
parameter tube: direct support gives `mathcal E<-1/200`, while an exact
centre value plus exact positive-gradient integrals strengthens this to
(TC3).  No gradient bound is imported or inferred from floating data.

## 2. Two-equation carrier

For

```text
A=4(mu+4),
B=-(12/25)(3mu^3-5mu^2-100mu-200),
C=(4/3125)(mu+10)^3(27mu^2+140mu+200),
```

Vieta gives the exact system

```text
E1=(1+t+t^2)a^2+(1+t)A a+B=0,
E2=t(1+t)a^3+t A a^2-C=0.                            (TC4)
```

The checker evaluates a two-complex-variable parametric Krawczyk map for
`(a,mu)` over the full real interval (TC1).  With radii

```text
rad(a)=4*10^-3,  rad(mu)=5*10^-4,
```

the exact outward bounds are

```text
rad K_a  < 3.219153*10^-3,
rad K_mu < 4.805575*10^-4,
|det d(E1,E2)/d(a,mu)| > 13382.78.                   (TC5)
```

Thus the Krawczyk map is a strict self-map and the interval Jacobian is
nonsingular.  Exact implicit differentiation also gives

```text
|a_t|<9763.19,  |mu_t|<1466.62.                     (TC6)
```

These derivative bounds are diagnostics for atlas sizing, not premises of
the excess sign.

## 3. Wall reconstruction and direct sign

Put `p=(1+t)a` and `h=-A-p`.  The whole Krawczyk tube satisfies

```text
Im(conj(p)h)>1997.46,  |p|>56.49.                   (TC7)
```

Hence the chamber sign is fixed and

```text
d=e^{-i phi}=i p/|p|.
```

The resulting exact balls for `mu` and `d` are passed to the compact
support--Stieltjes engine.  Both hub arms are isolated on 2048 exact rational
cells; monotone pieces use the half-angle support bound and possible turns
use the original nonnegative defect density.  The paired outward endpoint is

```text
mathcal E < -0.007378912... < -1/200.               (TC8)
```

All floating values in the checker are scouts only.  Krawczyk inclusion,
wall separation, root tubes, support sums, tail bounds, and the final
comparison use exact rational complex balls.

## 4. Exact gradient transport

At the centre `t=1/1000`, the corresponding unordered parameter is exactly

```text
kappa=t/(1+t^2)=1000/1000001.
```

The point engine isolates that exact carrier root and proves

```text
mathcal E(t_0)<-0.1169876625.                        (TC9)
```

For the whole Krawczyk tube, a gradient-only wall march uses its validated
arc tubes and the a-priori length bound `length<=Lip Delta s`; it never asks
two widened endpoint balls for a chord lower bound.  The resulting exact
positive-integral ceilings are

```text
G_mu<0.289497,  G_phi<7.031465.                     (TC10)
```

Combining (TC6), the exact wall-angle derivative bound `|phi_t|<82.609`,
and `|t-t_0|<=1/5000000` gives

```text
mathcal E(t)<-0.116786575<-1/10                     (TC11)
```

throughout (TC1).  Parameter uncertainty is paid once in (TC11), rather
than once per arm-integration cell.

## 5. Boundary

This proves one nonzero-width regular carrier cell and, more importantly,
the sound reusable cell mechanism.  It does not yet cover the other four
branches at this `t`, extend the cell to an event, close the cusp collar, or
prove the complete double-tight atlas, `EX-W`, `EX-U`, degree five, or
unrestricted Erdős 1041.
