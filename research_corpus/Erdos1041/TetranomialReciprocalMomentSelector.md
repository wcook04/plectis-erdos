# Erdős #1041: the reciprocal-moment radius selector

Status: analytic theorem proved on 2026-08-24.  Its scalar radius-product
kernel, monotone tail bound, and end-to-end two-spoke consumer are formalized
in `TetranomialReciprocalMomentSelector.lean`; its exact canonical shared-cache
Lean build passed on 2026-08-24.  This is a second coefficient-only tetranomial class, not an
unrestricted solution of Erdős #1041.

## The theorem

Let

```text
g(w)=w^m+a w^r+b w^s+c,        m>r>s>=2,
```

have all `m` roots in the open unit disk and `c!=0`.  Put `k=s-1` and

```text
rho = ((m-1)|c|^k)^(1/(mk)).
```

If

```text
rho < 1,
rho^r (rho^(m-r)+|a|) < 1,                         (RM)
```

then two distinct roots have complete origin spokes in `{|g|<1}` and hence
are connected there by a broken line of length below two.  As before, the
conclusion survives every translated cyclic lift covered by the companion
theorem.

## Proof

Let the root radii in increasing order be
`rho_1<=rho_2<=...<=rho_m`.  Because the coefficients of
`w,w^2,...,w^(s-1)` vanish, the reciprocal polynomial has its first `s-1`
nonleading coefficients zero.  Newton's identities therefore give

```text
sum_i w_i^(-ell)=0            for 1<=ell<s.          (1)
```

Use `ell=k=s-1`.  Isolating the term of largest reciprocal modulus and using
the triangle inequality gives

```text
rho_1^(-k) <= (m-1)rho_2^(-k),
rho_2^k <= (m-1)rho_1^k.                              (2)
```

Vieta and the ordering of the remaining radii give

```text
|c| = product_i rho_i >= rho_1 rho_2^(m-1).          (3)
```

Raise (3) to the `k`th power and combine it with (2):

```text
rho_2^(mk) <= (m-1)|c|^k.                            (4)
```

Thus `rho_2<=rho`, so at least two roots have modulus at most `rho`.  At any
such root, the root equation identifies the Abel tail and the triangle
inequality yields

```text
|c+bw^s|=|w^m+aw^r|
          <= |w|^r(|w|^(m-r)+|a|)
          <= rho^r(rho^(m-r)+|a|)<1.                (5)
```

The tetranomial Abel theorem now makes both complete spokes safe.  Strictness
is automatic even if the second inequality in (RM) is weakened to `<=1`,
because the two selected roots lie strictly below any coefficient cap chosen
strictly above the right side of (4).

The case `c=0` is deliberately excluded from this reciprocal formulation;
it has a zero root and should be handled by factoring the zero multiplicity
before applying the selector.

## Computational pressure

On the same deterministic 3,204 accepted open-disk tetranomials used by the
two preceding audits, (RM) certifies 1,683 configurations.  Its union with the
tail-resultant selector certifies 3,203, including two of that theorem's three
residuals.  Every certified sample has at least two numerically safe tails.
The single remaining sample has four safe tails but is outside both sufficient
conditions.  Its closest-pair squared distance is `0.1130296...`, so the
already-proved elementary chord budget is
`2^(7-2)d^2=3.6169479...<4`.  Thus the three-selector union certifies all
3,204 samples.  This is evidence for a covering conjecture, not a proof that
the three cases exhaust every tetranomial.  The counts measure coverage and
falsification pressure; the analytic proofs and Lean kernels are authority.

A broader adversarial replay immediately falsified that covering conjecture.
Its first witness had exponent pattern `(12,8,4)`, hence was actually the
fourfold cyclic lift of a cubic and was already closed by the unconditional
cubic quotient theorem.  After restricting to primitive exponent triples, a
genuine selector-union survivor appeared at `(m,r,s)=(5,4,1)`: all roots had
modulus below `0.997762`, three tails were numerically safe, but all three
sufficient tests failed.  Thus the individual theorems survive exactly as
stated, while their proposed exhaustiveness is retired.

## Boundary and handoff

This theorem consumes information orthogonal to total tail energy: missing
low coefficients become reciprocal cancellation and force a second small
root.  The next primitive boundary is the sparse quintic pattern `(5,4,1)`,
where reciprocal cancellation is unavailable and total tail energy is too
coarse despite three safe tails.  Its useful next mechanism is a root-count or
moment argument consuming the two missing middle coefficients, not another
claim that the current selectors are exhaustive.  The Refinery should present
this selector beside, not underneath, the tail-resultant selector and preserve
the no-priority boundary.
