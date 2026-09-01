# Erdős 1041: complete hub-orbit cancellation is not pointwise

## Result

The Lean-checked identities in `NearFeketeHubOrbit.lean` cancel the
frequency-two term in

```text
Im(nu a) Im(nu b)
```

when `a`, `b`, and the positive weight are common across a complete cyclic
orbit.  The actual near-Fekete branches do not have that form: at common value
increment `s`, each hub direction `nu` selects different solutions of

```text
nu Phi(t) = s,      Phi(t) = t^n - n t + (n-1).
```

It is tempting to hope that summing the *actual* charge densities at fixed `s`
restores pointwise positivity.  That strengthening is false.

Take degree `n=4`, the exact unit seed

```text
nu_0 = (12+5i)/13,
nu_j = exp(2 pi i j/3) nu_0,     j=0,1,2,
```

and `s=5`.  For each `nu_j`, follow both solutions born at the double root
`t=1`.  If `Phi'` and `Phi''` are evaluated at one such solution, its signed
support-charge density with respect to `s` is

```text
q(nu,t)
 = [Im(nu t Phi'(t))/|Phi'(t)|]
   [-Im(conj(nu) Phi''(t)/Phi'(t)^2)].               (Q)
```

The six densities sum to

```text
-0.1222436935974366584643845342402620067610... < -0.12.   (N)
```

The source-current guarded homotopy tracer selects the six branches.  Their
endpoints are then independently refined at 80 and 120 decimal digits.  The
two totals agree beyond 60 digits, every polynomial residual is below
`10^-70`, and the closest selected endpoint remains more than `0.35` from any
other saddle.  Thus this witness is separated from the branch-collision region
that invalidates coarse continuation.

## Derivation of the density

Writing `s=tau^2`, branch differentiation gives

```text
dt/ds = conj(nu)/Phi'(t).
```

The tangent-support factor is

```text
p = Im(nu t Phi'(t))/|Phi'(t)|,
```

and the turning rate is

```text
d vartheta/ds = -Im(conj(nu) Phi''(t)/Phi'(t)^2).
```

Their product is `(Q)`.  This is the same signed curvature-support currency as
`CriticalTreeLengthCharge.md` and `PerHubChargeSign.md`, now evaluated after
the complete hub fan-in at a common value parameter.

## Consequence and claim boundary

The pointwise route is eliminated: the cyclic correlation kernel cannot be
inserted under the integral by simply summing the actual branches at each
`s`.  Any successful near-Fekete combined-charge proof must establish an
**integrated** compensation, construct a genuinely invariant measure or
reparametrization, or use endpoint/global component information before taking
the sign.

This is a deterministic high-precision mechanism falsifier, not an exact
algebraic counterexample.  It does **not** refute the integrated complete-orbit
charge, the componentwise combined-charge conjecture, COVER, or Erdős 1041.
The parent theorem remains open.

Replay:

```text
python3 research_corpus/Erdos1041/scripts/check_erdos1041_near_fekete_orbit_pointwise_no_go.py
```
