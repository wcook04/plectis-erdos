# Erdős 1041: finite near-Fekete closure on every transverse cone

Status: an analytic scale-normalized finite-perturbation theorem, conditional only on the
source-current all-direction cusp theorem already proved in this directory.
Current 2026-08-27. **This is a genuine new case of Erdős #1041, not a proof
of the unrestricted problem.** It closes the passage from the limit model to
finite perturbations whenever the linear perturbation is quantitatively
nonzero. The tangent strata `h'(0)=0` and the `D`-away-from-1 bulk remain
outside its scope.

The formal sign-transfer consumer is
[`eventually_pos_of_scaled_deficit_tendsto_pos`](NearFeketeTransverseClosure.lean#L19-L31),
with the comparison-radius and constant-two conclusions in
[`eventually_length_lt_twice_radius`](NearFeketeTransverseClosure.lean#L34-L46)
and [`eventually_length_lt_two`](NearFeketeTransverseClosure.lean#L48-L60).
Replay the complete Lean module from the repository root with:

```sh
lake env lean research_corpus/Erdos1041/NearFeketeTransverseClosure.lean
```

These declarations formalize only the eventual sign inference.  The uniform
complex matched-asymptotic statement and its branch construction remain the
ordinary analytic proof given below.

## 1. The theorem

Fix `n >= 3`, a lower radius `R_* > 0`, and a norm on the finite-dimensional space
`P_{n-1}` of complex polynomials of degree at most `n-1`. For `eta > 0` let

```text
H_eta = { h in P_{n-1} : ||h|| = 1 and h(0) = 0 and |h'(0)| >= eta }.
```

We impose h(0)=0 in this theorem. A constant perturbation translates the
value plane but does not preserve the target sublevel set {|f|<1}; extending
the theorem to nonzero h(0) therefore requires a separate critical-value and
sublevel argument. Put

```text
f_{eps,h,R}(z) = z^n - R^n + eps h(z),
R in [R_*,1],                               h in H_eta.
```

For sufficiently small positive `eps`, let `R_{eps,h,R}` be the radius of the
minimum enclosing circle of the roots. The source-current cusp construction
selects one of the `n-1` critical points born from the multiple critical point
at zero and joins the two roots reached by its two descending Newton branches.
Write `L_{eps,h,R}` for their total arclength.

> **Transverse finite-perturbation theorem.** For every `n >= 3`, `R_*>0`
> and `eta > 0`, there is `eps_0 > 0`, **uniform in `R in [R_*,1]`**, such that,
> for every `h in H_eta` and `0 < eps < eps_0`, the selected two-root path
> satisfies the scale-normalized inequality
>
> ```text
> L_{eps,h,R} < 2 R_{eps,h,R}.
> ```
>
> Whenever the roots lie in the open unit disk, `R_{eps,h,R}<1`; the same path
> then has length `<2` and lies in `{|f_{eps,h,R}|<1}`. Consequently Erdős
> #1041 holds for every such polynomial in the punctured transverse shell.

The normalization `||h||=1` loses nothing: absorb any other size into `eps`.
The condition `|h'(0)| >= eta` is the exact transversality condition. It says
that the first splitting of the `(n-1)`-fold critical point is the ordinary
`z^n+n zeta` cusp already solved by
`MonotoneTurningProof.md`, `BridgeIdentityProof.md`, and
`ConeBoundMonotoneFunctional.md`.

## 2. Uniform blow-up

Set

```text
rho = (eps |h'(0)| / n)^(1/(n-1)),
e^(i phi) = h'(0)/|h'(0)|,
z = rho zeta.
```

After a harmless positive rescaling of the value coordinate,

```text
rho^(-n) (f_{eps,h}(rho zeta) + R^n)
  = zeta^n + n e^(i phi) zeta
      + sum_{k=2}^{n-1} b_k(h) rho^(k-1) zeta^k.                 (1)
```

Because `H_eta` is compact and `|h'(0)| >= eta`, all `b_k(h)` are uniformly
bounded. Thus (1), together with every fixed number of derivatives, converges
uniformly on compact `zeta`-sets to

```text
g_phi(zeta) = zeta^n + n e^(i phi) zeta,                         (2)
```

uniformly in `h in H_eta`. The critical points of (2) are simple. The implicit
function theorem therefore continues the selected critical point and both
descending inverse branches uniformly on every compact segment of their value
rays. Their rescaled arclengths converge uniformly there.

The only possible loss of uniformity is at infinity, where near and far fields
are matched. It is removed by a two-cutoff argument. Fix a large `M`.

* On `|zeta| <= M`, compact inverse-branch convergence gives the limit-model
  length with error `o_H(rho)`, uniform on `H_eta`.
* On `M rho <= |z| <= R/2`, solve the inverse branch from
  `z^n = R^n sigma + O(eps |z|)` by the implicit function theorem. Its tangent
  differs uniformly from the appropriate radial tangent by
  `O(M^{1-n}) + O_H(rho)`. After integration, the error divided by `rho` is
  `O(M^{2-n}) + o_H(1)` (with the usual logarithmic estimate at `n=3`, still
  tending to zero after the near-field subtraction).
* On `R/2 <= |z| <= 2R`, roots and inverse branches depend smoothly on the
  coefficients, so their contribution differs from the radial segment and
  the endpoint displacement by `O_H(eps)=o_H(rho)`.

All constants in this split are uniform for `R in [R_*,1]`: the outer annulus
stays away from zero, while the blown-up equation is independent of `R`.
First let `eps -> 0` with `M` fixed, then let `M -> infinity`. This proves the
uniform matched asymptotic, jointly in `h` and `R`,

```text
(2 R_{eps,h,R} - L_{eps,h,R}) / rho
       -> kappa_n(phi(h))                                      (3)
```

on `H_eta`. This is the finite-perturbation passage that the earlier cusp notes
left unproved. Notice that no explicit `O(rho^2)` constant is needed; uniform
`o(rho)` is exactly the necessary statement.

For the exact linear family `h(z)=e^(i phi)z`, the same conclusion needs no
stability argument: after scaling, (1) is exactly (2), and (3) is the definition
of the two renormalized branch excesses assembled by the bridge identity. Thus
the finite all-direction linear-perturbation family is already a direct
corollary; the cutoff argument is what upgrades it to the whole transverse cone.

**Later exact strengthening.**
[CyclicTrinomialFiberCase.md](CyclicTrinomialFiberCase.md) now removes the
small-perturbation restriction from that exact linear family altogether.  More
generally, every centred trinomial `z^n+a z^j+c`, for every `1<=j<n` and every
coefficient scale whose roots lie in the open unit disk, has every root-to-origin
spoke inside `{|f|<1}`.  Thus the present cusp analysis remains load-bearing for
general perturbing polynomials, but no longer owns any exact three-term tangent
model: all of them are closed globally by the coefficient-partition identity.

## 3. The sign closes the theorem

`ConeBoundMonotoneFunctional.md`, using the bridge and monotone-turning results,
proves `kappa_n(phi)>0` for every direction. Its proof gives the uniform lower
bound

```text
kappa_n(phi) >= min_{delta in [0, 2pi/(n-1)]}
                   (C_n(delta)-B_n(delta)) =: kappaBar_n > 0.   (4)
```

The lower bound is termwise for `n>=5`; the files give certified positive
Lipschitz bounds `0.3858` and `0.7319` for `n=3,4`. Combine uniform convergence
(3) with (4). For all sufficiently small `eps`, uniformly over `H_eta`,

```text
2 R_{eps,h,R} - L_{eps,h,R} >= (kappaBar_n/2) rho > 0.
```

Hence `L_{eps,h,R}<2R_{eps,h,R}`. For any member whose roots lie in the open
unit disk, its minimum enclosing radius is `<1`, so `L_{eps,h,R}<2`.

Along each descending branch the argument of `f` is fixed and `|f|` decreases
from the selected critical value to zero. In the open-disk application,
rescale by the actual enclosing radius: the selected value is
`R_{eps,h,R}^n+o(1)` with the proved negative cusp correction, hence is `<1`
throughout the same sufficiently small transverse shell. The joined path lies
in `{|f|<1}`. This proves the stated case of Erdős #1041.

## 4. What computation contributed

The earlier 50-digit cusp sweeps found the `eps^(1/(n-1))` scale, recovered the
same coefficient for arbitrary perturbing polynomials, and showed positivity
in every sampled direction. The later analytic stack proved that sign for all
degrees and directions. The present argument uses those computations only to
identify the correct blow-up and matching scale; the conclusion follows from
uniform compact convergence and the analytic lower bound (4).

## 5. Exact claim boundary and next obstruction

Proved here: the finite, strict and scale-normalized bound `L<2R_MEC` on every
fixed constant-free transverse cone `h(0)=0` and `|h'(0)|>=eta||h||`, with
`eps_0` uniform for the base radius in `[R_*,1]`. This uniform comparison, not
the elementary openness of a strict path at one fixed `R<1`, is the substantive
assertion.

Inherited and used: the all-degree, all-direction positivity of the cusp
coefficient and its explicit positive lower bound.

Lean-verified in `NearFeketeTransverseClosure.lean`: the load-bearing final
inference from a positive scaled deficit limit to eventual strict length
bounds, including the final `<2` implication when the enclosing radius is `<1`.
The complex matched-asymptotic statement (3) remains an ordinary analytic
proof, not a Lean theorem.

Not proved: a neighborhood uniform over directions approaching `h'(0)=0` for a
general perturbing polynomial; the bulk regime bounded away from the Fekete
stratum; or unrestricted Erdős #1041.  The formerly listed exact higher-tangent
models `zeta^n+A zeta^j` are now closed globally by
`CyclicTrinomialFiberCase.md`; what survives is control of the higher-order
terms accompanying those tangent models in a genuinely non-trinomial
perturbation.
