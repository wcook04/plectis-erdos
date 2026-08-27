# Erdős #1041: the sharp quintic mixed-mode transition and its paired correction

Status: exact transition chart, analytic derivation, symbolic replay, and
Lean-checked lexicographic tie-break, 2026-08-25. **This identifies and resolves
one sharp equality chart; it does not yet prove the full mixed-mode connector
theorem or unrestricted Erdős #1041.**

## 1. The computation finally hit the boundary

Normalize the degree-five mixed Newton model as

```text
H(z)=Re(Az+Bz^2-z^5),             max(|A|,|B|)=1.          (1)
```

An adversarial search minimized, over every root-ray pair and truncation
radius, the maximum of `H` on both outward ray tails and the joining chord,
while an outer search maximized that best certificate over `(A,B)`. Random
configurations had comfortable negative margins. The adversarial maximum did
not: it converged to zero at the recognisable phase chart

```text
arg A = 2 pi/5,      arg B = 13 pi/10,
|B|=1,               |A|=u_*,
u_*^3 = 27/320,      u_*=0.4386026607319299... .           (2)
```

This is not floating-point bad luck. It is an exact equality stratum.

## 2. Why the leading model vanishes twice

Write `A=u omega`, `B=exp(13 pi i/10)`, with
`omega=exp(2 pi i/5)`, and put `z=r exp(i alpha)`. Then

```text
H(z)=r u cos(2 pi/5+alpha)
     +r^2 cos(13 pi/10+2 alpha)-r^5 cos(5 alpha).          (3)
```

At each of the antipodal angles

```text
alpha_+ = pi/10,              alpha_- = -9 pi/10,          (4)
```

all three cosines vanish separately. Thus `H=0` there for every `r` and every
`u`; no leading-order estimate can manufacture strict slack at those points.
Geometrically these directions occur on the relevant fifth-root chords. The
checker derives the chord intersections exactly; the Lean theorems
`mixedLeadingValue_at_positive_zero` and
`mixedLeadingValue_at_negative_zero` verify the trigonometric core.

The amplitude in (2) is where the remaining adjacent chart becomes tangent to
zero. If `w(t)=(1-t)+t omega^4`, write

```text
Re(A r w+B r^2 w^2-r^5 w^5)=r[u L(t)+r B_2(t)-r^4 C(t)].  (5)
```

At an interior tangency, eliminating `u` and `r` from the value, `t`-derivative,
and `r`-derivative gives

```text
4 L C B_2' - 3 B_2 C L' - B_2 L C' = 0.                 (6)
```

Its relevant root is

```text
t_* = sqrt(5)(3+sqrt(5)-sqrt(10-2sqrt(5)))/10.
```

Substitution into

```text
r_*^3 = B_2(t_*)/(4C(t_*)),
u_*   = -3r_*B_2(t_*)/(4L(t_*))
```

reduces exactly to `u_*^3=27/320`. This explains the seemingly arbitrary
numerical amplitude and makes the equality reproducible rather than fitted.

## 3. The next Fourier mode breaks the tie

The disk constraint pairs tangent Fourier modes. To leading tangent order,

```text
E_3 = -conj(E_2).                                        (7)
```

The Lean theorem `tangentFourier_pair` proves this conjugate-sign identity for
an arbitrary finite purely imaginary perturbation sequence; the fifth-root
specialization is exactly (7).

For the phase of `B` in (2), the paired cubic correction is

```text
K(r,alpha)=r^3 cos(17 pi/10+3 alpha).                     (8)
```

At the two leading zeros it has opposite signs:

```text
K(r,alpha_+) =  r^3,
K(r,alpha_-) = -r^3.                                     (9)
```

So the equality does **not** force the two tied directions to have the same
next-order sign. At the simultaneous-zero point `alpha_-`, the first omitted
paired mode supplies a strict negative margin; at `alpha_+` it supplies the
opposite sign. This is a pointwise lexicographic tie-break, not by itself a
certificate that an entire chord through `alpha_-` is nonpositive. The Lean theorems
`pairedThirdCorrection_at_positive_zero` and
`pairedThirdCorrection_at_negative_zero` check (9), while
`pairedCorrection_resolves_tie` proves the quantitative implication

```text
L <= 0,  epsilon>0,  |R| <= epsilon r^3/2
    ==> L-epsilon r^3+R < 0.                              (10)
```

This is the correct refinement of “the first nonzero mode wins”: on a leading
equality stratum, inspect the first mode that is nonzero **on the equality
set**, and select between the tied connectors by its sign.

## 4. Exact boundary

Closed here:

* the adversarial near-zero is recognized as the algebraic amplitude
  `u_*^3=27/320`;
* the simultaneous leading zeros are derived exactly;
* tangent Fourier pairing has opposite signs at the two tied zero directions;
* at the negative simultaneous-zero point, the correction absorbs any
  remainder smaller than half its cubic margin.

Still required for a complete degree-five near-Fekete theorem:

* prove that every normalized mixed model (1) has a nonpositive truncated
  connector and classify all equality charts up to fifth-root symmetry;
* prove that the chart above and its symmetries are the complete equality set,
  rather than merely the maximizer found by the bounded search;
* transfer the resulting stratified margin through the exact finite expansion
  uniformly, then overlap it with the non-near-Fekete regime.

The computation has therefore done what it was supposed to do: it did not
stand in for a proof, and it did not merely report another almost-one. It found
the exact place where strict leading-order negativity fails and exposed the
analytic term that repairs that failure.
