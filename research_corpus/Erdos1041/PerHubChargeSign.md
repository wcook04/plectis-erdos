# Erdős 1041: the near-Fekete residue is a curvature charge, and it is negative at some hubs

Status: one exact counterexample, two exact identities, and one measured
selection mechanism. 2026-08-24. **This does not prove Erdős #1041** and it does
not weaken the surviving obligation. It removes a class of attacks on the
near-Fekete half, and supplies the algebraic form the remaining work needs.

Receipt: [`scripts/check_erdos1041_per_hub_charge_sign.py`](scripts/check_erdos1041_per_hub_charge_sign.py),
three parts (`witness`, `charge`, `sign`), all deterministic.

## 1. The per-hub obligation is false, arbitrarily close to the Fekete family

[NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) writes its constant as
`kappa_n(phi) = (2R - min_c L(c))/rho`. The `min_c` is load-bearing and has not
been read as such: `kappa_n > 0` is a statement about the **best** hub, not
about a hub. The distinction is not academic.

Take `f(z) = z^n - R^n + eps e^{i phi} z` with `R = 9/10`, so every root lies in
the open unit disk. At `n = 3`, `phi = 6/5`, `eps = 10^-6`, the hub
`c = rho e^{i(pi + phi)/2}` is admissible (`|f(c)| = 0.729`), and

```text
     L(c) = 1.8000294939849717352
       2R = 1.8000000000001524157        (exact circumradius of the root set)
   L - 2R = +2.9493985e-5   > 0
```

The same configuration at `eps = 10^-8` gives `L - 2R = +2.9373199e-6`, and a
degree-five case (`phi = 2`, `eps = 10^-6`) gives `L - 2R = +5.7575077e-4`. The
deficit scales like `rho`, as §2 of the cusp law predicts, but **with the wrong
sign at this hub**: the per-hub charge is `-0.0509` at `n = 3` and `-0.0272` at
`n = 5`, against `+0.8084` and `+1.0059 … +1.3135` at the sibling hubs. The
minimum over hubs is comfortably below `2R` in every case, so the conjecture is
untouched; what fails is the per-hub reading of it.

Two guards, because both available errors flatter this claim rather than the
conjecture. `R` is the circumradius of the **perturbed** root set, computed
exactly over pairs and triples — an iterative centre inflates `R`, and `R` sits
on the safe side of the inequality being violated. And the branch integrator
uses shifted coordinates with a geometric mesh, since both defects recorded in
[NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) §5 **under**-report length.

**Consequence, and it is a stop condition.** No hub-by-hub argument can prove
the near-Fekete half. An estimate that establishes `L(c) <= 2R` at an arbitrary
admissible hub of a near-Fekete polynomial is proving something false. Every
proof must either select the hub or aggregate over hubs. This is the same shape
as [CriticalTreeLengthCharge.md](CriticalTreeLengthCharge.md)'s recorded failure
of `sum_e K_e >= 0` termwise, and it localises that failure: it happens in the
near-Fekete regime, at leading order in `rho`, with a computable constant.

## 2. In the model the residue is pure curvature charge

Let `Gamma` be the two-branch arc at one hub of the near-field model
`g(zeta) = zeta^n + n lambda zeta`, `|lambda| = 1`, truncated at `|zeta| = Z`.
Write `p = <zeta, N>` for the signed distance from the origin to the tangent
line (`N = iT` the left normal) and `dvartheta` for the turning. Then

```text
        kappa_n  =  int_Gamma  p dvartheta.                            (P)
```

*Proof.* The tangent-support identity (B) of `CriticalTreeLengthCharge.md` gives
`Lambda(Z) = <zeta,T>|_ends - int kappa <zeta,N> dl`. Both ends are radial in
the limit, so the endpoint term is exactly `2Z`, and
`kappa_n = lim (2Z - Lambda(Z))` is the remaining integral. ∎

So the endpoint deficit `D_e` of (D) vanishes identically in the model: **the
near-Fekete residue is entirely the signed curvature support**, which is why the
geometric slack `D_e` supplies nothing there and why the sign question is
irreducible. Verified against `2 - (ex_1 + ex_2)` to `2e-15` at
`n = 3,4,5,6,8,12`, reproducing the recorded `kappa_n` to `5e-9`.

## 3. The charge integrand in closed algebraic form

With `G = zeta^n + lambda zeta = zeta g'(zeta)/n` and `X = zeta^n`, so that
`X = G - lambda zeta`,

```text
   p dvartheta  =  ((n-1)|zeta| / n) * Im(G) * Im(G^2 conj(X)) / |G|^5  ds.   (C)
```

The substitution `zeta = zeta_c t` removes the hub and the perturbation
direction together, leaving **one fixed polynomial per degree and one unit
parameter**:

```text
   Phi(t) = t^n - n t + (n-1),      Phi(1) = Phi'(1) = 0,
   branch:  nu Phi(t) = s >= 0  leaving the double root t = 1,   |nu| = 1.
```

Here `nu = zeta_c^n`, and `nu` ranges over the whole circle as the split
direction does. This is sharper than the `zeta^n + n zeta` plus `phi`
formulation of the cusp law: the hub is normalised to `t = 1` and the only datum
left is the ray direction. Writing `h = t - 1` and `E_1 = t^{n-1} - 1`,

```text
   Im G = (n-1) F1,      Im(G^2 conj(X)) = |t|^{2n} F2,
        F1 = Im(nu h),        F2 = Im( nu E_1^2 / t^{n-2} ),
```

both cancellation-free, so (C) becomes

```text
   p dvartheta / d tau  =  2 tau (n-1)^2 F1 F2 |t|^{2n-4} / ( n |E_1|^5 ),     (C')
```

and in particular

```text
        sign( p dvartheta )  =  sign( F1 * F2 ).                        (S)
```

Verified against the geometric product to `8e-7` relative at `n = 3 … 30`.

Equivalently, with `A_k = Im(nu t^k)` and the branch relation
`A_n = n A_1 - (n-1) A_0`, (S) reads `(A_n - A_1)(A_n - 2 A_1 + A_{2-n}) >= 0`.
At `n = 2` the second factor vanishes identically, which is the quadratic case:
straight branches, zero curvature, zero residue.

**For a general polynomial** the same computation gives, along any descent
branch, `p dvartheta` proportional to `-Im(N conj(z)) Im(N')` with `N = f/f'`
the Newton step — the "correct residual currency" of
`CriticalTreeLengthCharge.md` written out. That form is *not* sign-definite in
general; §1 is the near-Fekete instance of its failure.

## 4. Numerical hygiene: two opposite cancellation regimes

Recorded because both cost a false reading here before being caught, and both
are invisible in a spot check.

* `Im(conj(Phi) E)` with `E = t^n - t` — the natural algebraic form — cancels in
  the **far field**: both factors grow like `|t|^n` while the imaginary part
  stays `O(|t|)`, so beyond `|t| ~ 10^3` the sign is pure noise. A sweep built
  on it reported violations on 3–4% of the plane that are not there.
* `F2` written as `(n-1) F1 - Im(nu (t - t^{2-n}))` cancels at the **hub**: the
  two terms agree to leading order in `h`, so at `|h| ~ 3e-6` the difference is
  `1e-17` against terms of size `4e-6`. Computing `E_1` from its binomial
  expansion removes it.

Every sign decision in the receipt is taken on the geometric product
`p * dvartheta`, which has neither defect; the algebraic forms are cross-checked
against it, never used to decide.

Separately, the branch tracer caps its step by a quarter of the distance to any
**other** critical point of `Phi` (the nontrivial `(n-1)`-th roots of unity) and
rejects a step whose Newton correction exceeds 35% of it. Without that guard the
tracer jumps sheets near the directions `arg nu = -arg(1 - omega^j)`, where the
branch genuinely runs into a second saddle, and returns smooth, plausible,
wrong lengths — this directory's recorded artifact class.

## 5. What selects the hub — measured, not proved

At the aligned hub (`nu = e^{i n pi/(n-1)}`, the `phi = 0` slice, the direction
where the cusp law's minimum is attained) the integrand is pointwise
nonnegative: negative charge mass fraction below `1e-28` at every degree
`3 … 30`. So (S) holds there termwise and `kappa > 0` follows with no
cancellation at all. That is the same slice
[ConeBoundBranchGeometry.md](ConeBoundBranchGeometry.md) proves Lemma S and
Lemma B for, and its Lemma B (`Im zeta` strictly decreasing, hence `Im G > 0`)
is exactly the constant sign of `F1` in (S) — the first of the two factors.

Off that slice the second factor changes sign somewhere on the branch, so (S)
fails termwise and the set `S_n` of directions for which it holds pointwise is a
proper subset of the circle. **The shape of `S_n` is not settled here.** A sweep
on the unguarded tracer returned `S_n` as essentially one arc, longer than the
hub spacing `2 pi/(n-1)` at `n = 3 … 13`, which would make every hub orbit
`{nu omega^k}` meet it; that reading is **not** carried by the receipt. The
guarded tracer, which is the only one whose branch identification is trusted
here, is too slow near the saddle-collision directions
`arg nu = -arg(1 - omega^j)` to have confirmed it — and those directions are
precisely where the arc endpoints sit, so the unguarded figure is suspect
exactly where it matters. Treat the arc claim as an open measurement.

What the shape of `S_n` is worth is stated plainly: if `S_n` contains an arc
longer than `2 pi/(n-1)`, then some hub of every near-Fekete polynomial has a
termwise-positive charge, and a proof of (S) on that arc closes the near-Fekete
half with no cancellation argument anywhere. That is the natural next target,
and settling the arc — with a tracer that does not stall at the collisions — is
the prerequisite.

## 6. Claim boundary

Exact: the witness of §1 (mpmath at 60 digits, exact circumradius, admissibility
checked), the identity (P), and the algebraic forms (C), (C'), (S), which are
ordinary calculus and algebra.

Measured, not proved: pointwise nonnegativity at the aligned hub; the arc length
of the good set and its comparison with `2 pi/(n-1)`; the per-hub charge values.
The float64 quadrature carries the same `3.9e-16` absolute error bar the cusp
law records, which supports the digits quoted here and no more.

Not established: any bound in the `D`-away-from-1 regime; positivity of
`kappa_n(phi)` at every direction as a theorem for `n >= 4`; and any progress on
the constant 2. **Erdős #1041 remains open.**
