# Erdős #1041: an exact connector on the canonical sextic mixed slice

Status, 2026-08-25: complete analytic theorem, exact symbolic replay, and a
Lean-checked square-times-Bernstein certificate. This closes one complete
degree-six homogeneous mixed-mode slice. It does **not** prove the full
degree-six near-Fekete model, the finite perturbation transfer, or unrestricted
Erdős #1041.

## The theorem

Let

```text
H_u(z) = Re(-i u z - z^2 - z^6),                 u >= 0,
omega = exp(i pi/3).
```

Put

```text
q = (7+4 sqrt(3))/27,             r=q^(1/4).
```

For every `u>=0`, the outward radial tails from `r` to the sixth-root
directions `1` and `omega^(-1)`, together with the chord joining
`r` to `r omega^(-1)`, lie in `{H_u<=0}`. The same pair and the same radius
work for the entire half-line of amplitudes.

This is the canonical hard slice located by the degree-six finite-mode
adversary: after sixth-root rotation its near-zero configurations converge to
`A=-iu`, `B=-1`, `C=0` in

```text
Re(Az+Bz^2+Cz^3-z^6).
```

## The two rays

On the upper ray `z=x`,

```text
H_u(x)=-x^2-x^6<=0.
```

On the lower ray `z=x omega^(-1)`,

```text
H_u(z)=-u sqrt(3)x/2+x^2/2-x^6.
```

Since

```text
q=(7+4sqrt(3))/27 > 1/2,
```

every `x>=r` has `x^4>=q>1/2`, so the last two terms are nonpositive; the
linear term is nonpositive as well.

## The exact chord factorization

Write

```text
w(t)=(1-t)+t omega^(-1),                  0<=t<=1.
```

Direct expansion gives

```text
Re(w^2)=-(t^2+2t-2)/2,

Re(w^6)=
 (t^2-4t+1)(t^2+2t-2)(2t^2-2t-1)/2.
```

At the selected radius, the carrier factors as

```text
Re(w^2)+q Re(w^6)
 = q (t+1+sqrt(3)) (t+1-sqrt(3))^2 C(t),
```

where

```text
C(t)=t^3+(-6+sqrt(3))t^2+(27/2-7sqrt(3))t
     -67/2+41sqrt(3)/2.
```

The square is the exact double contact discovered computationally at
`t=sqrt(3)-1`. It is an equality of the first two modes separately, not a
numerical near-miss.

The degree-three Bernstein coefficients of `C` are

```text
-67/2+41sqrt(3)/2,
-29+109sqrt(3)/6,
-53/2+97sqrt(3)/6,
-25+29sqrt(3)/2.
```

Every coefficient is strictly positive; the single rational bound
`sqrt(3)>50/29` proves all four inequalities. Hence `C(t)>0` on `[0,1]` and
the carrier is nonnegative. Therefore

```text
H_0(rw(t))=-r^2[Re(w(t)^2)+q Re(w(t)^6)]<=0.
```

Finally `Im(rw(t))=-r sqrt(3)t/2<=0`, so

```text
H_u(rw(t))=H_0(rw(t))+u Im(rw(t))<=H_0(rw(t))<=0
```

for every `u>=0`. This monotonicity is why one equality certificate covers the
whole amplitude half-line.

## Path length and boundary

The two radial tails plus their chord have normalized length

```text
2(1-r)+r |1-omega^(-1)| = 2-r < 2,
```

because the two directions are adjacent and their chord has unit length. Thus
the model connector has strict metric slack even though its value inequality
has one double contact.

Lean verifies the algebraic radius, all Bernstein coefficients, the exact
factorization, chord positivity, both ray inequalities, and the uniform
`u>=0` assembly in the
[canonical connector theorem](./SexticCanonicalMixedSlice.lean#L202-L217).

What remains open is genuinely higher-dimensional: allow the phases and
relative amplitudes of the first three low sextic modes to vary, classify the
other equality faces, and transfer a finite connector atlas through the
origin-anchored actual-polynomial remainder. This theorem removes the
canonical pure-second-mode boundary face from that future atlas.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_sextic_canonical_mixed_slice.py
./repo-python source-provenance://private-authoring-project/scripts/lean_fast_build.py --jobs 2 \
  ErdosProblems/Erdos1041/SexticCanonicalMixedSlice.lean
```

The exact replay terminates with `PASS: one exact connector works for every
amplitude u >= 0`. The result identity is
`sextic_canonical_mixed_slice_connector`; the checked source snapshot is
`5cbc0fa0aec288a1d19fb1abf12dc85a00b2c447`. The source hashes are:

```text
analytic note  e375c24be79495aa05446efecd2055729f083187db5ea92d2c68202e4f714e61
Lean core      dafeba3aaab3cdf4661a9dd8d4ff59dead77353c67ca40c46220b5d585560b42
exact replay   7aa52f875121d6e2262f3ecdb5d82c549924bc0c667885c29705ddc91ea47849
```

This is a source-specific ordinary theorem with an exact symbolic certificate
and a Lean-checked core. It makes no priority or novelty claim and does not
establish the full sextic model, a perturbation transfer, peer review, or a
solution of Erdős #1041.
