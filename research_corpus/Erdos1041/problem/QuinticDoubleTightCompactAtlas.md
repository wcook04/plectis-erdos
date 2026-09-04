# Erdős 1041: exact event excision from the compact double-tight atlas

Date: 2026-08-30. Replay checker:
`scripts/check_erdos1041_quintic_double_tight_compact_atlas.py`.
Consumes `QuinticDoubleTightCriticalValueCarrier.md`,
`QuinticMinusTenWallLimitSideArmCertificate.md`,
`QuinticMuStarAngularFiberReduction.md`, and `CertifiedWallEngine.md`.

## 1. Result

Let `C_phys` be the physical part of the compact unordered double-tight
carrier of Theorem CV, and put

```text
kappa_-=(1-3sqrt(3))/13,
kappa_+=(1+3sqrt(3))/13.
```

> **Theorem DTE (event excision).**  There are relative open neighborhoods
> `N_-`, `N_0`, and `N_+` in `C_phys` of the complete fibres over
> `kappa_-`, `0`, and `kappa_+`, respectively, such that
>
> ```text
> mathcal E < 0 on N_- union N_0 union N_+ .          (DTE1)
> ```
>
> At the two triple-tight centres themselves the stronger exact bounds are
>
> ```text
> mathcal E(50+30sqrt(3), +-pi/2) < -1/6,
> mathcal E(50-30sqrt(3), +-pi/2) < -1.              (DTE2)
> ```

Thus the final compact atlas no longer has to certify across any of its
three interior event fibres.  It is enough to cover compact truncations of
the twenty regular upper-half-plane carrier branches after deleting these
already-negative event neighborhoods.  This is a genuine open-subatlas
closure, but the radii supplied by the continuity argument are not made
numerical here.

## 2. The two triple-tight fibres

The exact carrier calculation gives

```text
(kappa_-,mu_-) = ((1-3sqrt(3))/13, 50+30sqrt(3)),
(kappa_+,mu_+) = ((1+3sqrt(3))/13, 50-30sqrt(3)).    (DTE3)
```

At either point all three critical gaps are collinear, so the two chamber
wall directions are `w=e^{-i phi}=+-i`.  Since `mu_+-` is real, complex
conjugation interchanges the two inverse rays and preserves arclength and
terminal modulus.  The two orientations consequently have the same paired
excess.

The certified wall engine, run with exact dyadic ball arithmetic at
`k=20`, proves

```text
mu=50+30sqrt(3), w=i:
  -0.169562 < mathcal E < -0.168324 < -1/6,

mu=50-30sqrt(3), w=i:
  -1.144720 < mathcal E < -1.144643 < -1.           (DTE4)
```

The displayed decimals are only readable outward roundings of the exact
rational intervals returned by the checker.  Acceptance is the rational
comparison of its upper endpoint with `-1/6` or `-1`.

The projected double roots are ordinary conjugate crossings.  If
`mu=mu_0+z(kappa-kappa_0)+O((kappa-kappa_0)^2)`, their exact tangent cones
are

```text
z^2+(388+228sqrt(3))z+459744+265392sqrt(3)=0,
z^2+(388-228sqrt(3))z+459744-265392sqrt(3)=0,        (DTE5)
```

whose discriminants are strictly negative.  Hence the upper-half-plane
carrier representative has a finite one-sided linear chart at both
crossings (switching between conjugate slopes across the real fibre).
The reconstruction denominator `D` is nonzero there.  Therefore `mu`, the
reconstructed pair direction `p`, and the two limiting wall phases vary
continuously along every incident physical branch.  Local uniform
continuity of the regular inverse-ray excess, together with the strict
margins (DTE4), gives `N_-` and `N_+`.

This argument is deliberately topological after the exact point margins:
it proves the existence of event neighborhoods without pretending that an
effective covering radius has been computed.

## 3. The complete `kappa=0` fibre

The exact event factorization is

```text
Khat(0,mu)=16(mu+10)^6(27mu^2+140mu+200)^2.          (DTE6)
```

Thus every upper carrier branch approaching `kappa=0` tends either to
`mu=-10` or to

```text
mu_*=(-70+10i sqrt(5))/27
```

or its conjugate.  There are no hidden limiting parameters.  The Newton
leading forms are squarefree:

```text
q=(mu+10)^3/kappa:
  q^2+16200q+590490000=0,
  q=-8100+-16200i sqrt(2),

mu-mu_*=q kappa:
  q^2+[(-28+4i sqrt(5))/15]q
     +(352-112i sqrt(5))/675=0,                     (DTE7)
```

and the second quadratic has discriminant
`(704-224i sqrt(5))/675 != 0`.  Hence finitely many regular Newton charts
exhaust the punctured carrier near this fibre.

The already-proved `mu=-10` wall-limit theorem gives the three possible
directional pair ceilings

```text
-1/80, -23/30, -47/48,
```

all strictly negative.  The `mu_*` endpoint theorem plus angular
interpolation gives the uniform full-fibre ceiling `-3/8`, and conjugation
does the same at `conj(mu_*)`.  These are precisely the limiting charts in
(DTE7).  Taking the minimum of finitely many local neighborhoods proves
`N_0`.

## 4. What failed, and what remains

A tempting shortcut would restrict the wall-sheet subharmonic function to
the real `kappa` carrier and claim endpoint domination.  That is invalid:
the restriction of a subharmonic function to a curved real trace need not
be subharmonic or even lack an interior maximum.  Numerical branch tracking
also finds small interior bumps.  The event excision above uses strict
local margins and continuity only; it makes no monotonicity assertion.

The exact residual is now the disjoint compact regular atlas obtained by
removing `N_- union N_0 union N_+` from the twenty upper-half-plane branch
traces (with the two hub arms paired at each point).  Its sign still needs
an effective interval-Newton/DT-Lip cover, or a new analytic inequality.
This note does not prove that residual, `EX-W`, `EX-U`, the model-to-real
transfer, degree five, or unrestricted Erdős 1041.
