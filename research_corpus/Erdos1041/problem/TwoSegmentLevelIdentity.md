# Erdős 1041: the two-segment mechanism is level-optimal, and its threshold is Fekete's

Status: one normalisation, two proved theorems, one **refuted** measured
identity, one exact extremal computation, one adversarial extension, and one
new member of the instrument-defect class. 2026-08-24. **Erdős #1041 remains
open** and nothing below claims otherwise. The later exact degree-seven
refutation is [TwoSegmentLevelIdentityRefutation.md](TwoSegmentLevelIdentityRefutation.md).

What this adds to [TwoSegmentContainmentReduction.md](TwoSegmentContainmentReduction.md)
is not more evidence for its conjecture. It is an explanation of *why the number
in that conjecture is one*, and a normalisation under which the conjecture becomes
scale-invariant, non-strict, and posed over a compact set — the three properties
its open-disk form lacks, and the three a variational proof would need.

## 1. The closed-disk normalisation

`research_packet.json::exact_results::two_segment_containment_reduction` (E39) is
stated on the **open** disk with three **strict** inequalities. That form has no
equality case and no compactness, so no extremal argument can start from it. The
following restatement has both.

> **Theorem 1 (normalisation).** Suppose that for every `n ≥ 2` and every monic `g`
> of degree `n` with all roots in the **closed** unit disk there are distinct roots
> `α, β` and a point `η` with
>
> ```text
> (i')  max_{[η,α]} |g| ≤ 1,   (ii')  max_{[η,β]} |g| ≤ 1,   (iii')  |η−α| + |η−β| ≤ 2.
> ```
>
> Then Erdős #1041 holds.

*Proof.* Let `f` be monic with all roots in the open unit disk. If `f` has a repeated
root the problem is trivial (two roots coincide; the constant path has length `0` and
`|f| = 0 < 1` there), so assume the roots are distinct. Let `D(z_c, R)` be their
minimum enclosing disk; `R ≤ max_i |z_i| < 1` and `R > 0`. Put

```text
g(w) := R^{-n} f(z_c + R w),
```

monic of degree `n` with all roots `(z_i − z_c)/R` in the closed unit disk. Apply the
hypothesis to `g` and pull back along the affine map `w ↦ z_c + Rw`, which carries
segments to segments and scales lengths by `R`:

```text
|f| = R^n |g| ≤ R^n < 1   on both segments,      |h−a| + |h−b| ≤ 2R < 2.
```

Both strict inequalities Erdős #1041 asks for are produced by the normalisation
itself, from `R < 1`, and not by the hypothesis. ∎

So the mechanism's real content is a **non-strict** statement over the compact
configuration space `D̄^n`, and it has an equality case, computed exactly in §5.

## 2. The level floor is a theorem

Write, for monic squarefree `f` of degree `n ≥ 2`,

```text
μ  :=  min { |f(c)| : f'(c) = 0 },
V_E :=  inf over distinct roots a,b and hubs h with |h−a|+|h−b| ≤ 2
             of   max( max_{[h,a]}|f| , max_{[h,b]}|f| ).
```

`V_E` is the ellipse-restricted best achievable level of the two-segment mechanism.
Conditions (i')/(ii') of Theorem 1 say exactly `V_E ≤ 1`.

> **Theorem 2 (level floor).** `V_E ≥ μ`. More strongly, for **any** distinct roots
> `a, b` and **any** `h ∈ ℂ`, `max_{[h,a] ∪ [h,b]} |f| ≥ μ`.

*Proof.* Let `M` be that maximum and suppose `M < μ`. Put `Ω = {|f| < μ}`. Every
critical point `c` has `|f(c)| ≥ μ`, so `Ω` contains no critical point. Let `U` be a
connected component of `Ω`. Then `f|_U : U → D_μ` is proper: a preimage of a compact
`K ⊂ D_μ` is bounded, and if `z_k ∈ U` converges then the limit lies in `Ω` and in
`Ū`, and `Ū ∩ Ω = U` because `U` is relatively closed in `Ω`. A proper holomorphic
map onto a disk is a branched covering; here it is unbranched, and `D_μ` is simply
connected, so a **connected** covering of it is a homeomorphism. Hence `f|_U` has
degree `1` and `U` contains exactly one root.

Now `[h,a] ∪ [h,b]` is connected (the two segments meet at `h`) and is contained in
`{|f| ≤ M} ⊂ Ω`, so the distinct roots `a` and `b` lie in one component of `Ω` —
contradicting the previous paragraph. ∎

Theorem 2 is the reason the mechanism cannot be cheap: no two-segment path can
undercut the level at which the first merge happens. What is remarkable is that it
appears never to pay more.

## 3. The measured identity `V_E = μ`

Sixty configurations, four families (uniform in the disk, boundary-clustered,
perturbed regular polygon, three-cluster), degrees `3, 4, 5, 6, 8`, hub restricted to
the closed ellipse `|h-a|+|h-b| <= 2` throughout. The residual **shrinks with the inner
search budget**, which is what distinguishes truncation from a real gap:

| inner budget (grid `m`, refine rounds, samples `K`) | worst `V_E / mu` |
|---|---|
| `29 / 45 / 56` (receipt default) | `1.0000224` |
| `41 / 70 / 64` | `1.0000031` |

At the finer budget all but four of the sixty rows sit inside `1 + 1e-7`; the largest
residuals are `3.1e-6` (a three-cluster degree-6 configuration with `mu = 1.7e-4`), then
`2.6e-7`, `1.7e-7`, `1.1e-7`. `V_E` is an infimum approached on the feasibility
boundary and the hub comes from a finite grid plus local refinement, so **every reported
`V_E` is an upper bound on the true infimum** -- the search error runs in the safe
direction for the identity and the dangerous direction for the floor, and the floor is
the half that is proved. The companion arm confirms it: `worst mu / V_E = 0.9999999997`
over the same families, never above one.

The measurement is not sampled. `max_{t in [0,1]} |f(h + t(a-h))|^2` is the maximum of an
explicit **real polynomial of degree `2n`**, taken over the real roots of its derivative
together with the two endpoints; no grid enters the verdict.

> **Retracted conjecture (level identity).** `V_E = μ` for every monic
> squarefree `f`.

This is false. The exact dyadic degree-seven witness of
[TwoSegmentLevelIdentityRefutation.md](TwoSegmentLevelIdentityRefutation.md)
has a unique least critical point and no root spoke contained at level `μ`,
forcing `V_E>μ`. The table above remains a faithful report of the original
measurement and is retained as a warning about threshold-pinned searches.

### 3b. The identity's sharpest necessary condition is false

At level `mu` the two lobes meet only at `c*`, so a two-segment path realising the
identity must cross there: one of its two segments contains `c*`, and the sub-segment
from that segment's root to `c*` is a **sublevel-contained straight spoke**. Hence

> **(SPOKE>=1).** At the minimum-critical-value hub `c*`, at least one of the straight
> spokes `[c*, z_k]` satisfies `max |f| <= mu` on it.

is necessary for `V_E = mu`. It is the exact complement of what the corpus already
refutes: `negative_results` entry 14 exhibits a quartic with **at most one** contained
spoke at every admissible critical point. Over 144 random configurations at degrees
`3..10` the contained-spoke count is `2` in 132 cases and `1` in 2 -- entry 14's witness
is a special configuration, not the generic picture.

Testing (SPOKE>=1) needs care, because **the naive objective is degenerate**. A contained
spoke attains its maximum `mu` *at the endpoint* `c*`, so `max_{[c*,z_k]}|f| / mu` is
identically `1` whenever the spoke is contained and an adversarial search has nothing to
move; a first pass at tolerance `1e-11` duly reported "zero contained spokes" in 10 of
144 cases, all of them float noise on an exact equality. Excising the endpoint fixes it:
the informative objective is `max_{t <= 1-delta} |f| / mu` along `[z_k, c*]` with
`delta = 1e-3`, which is `< 1` **iff** the spoke is contained. Adversarial hill-climbing
on `min_k` of that quantity, three restarts per degree, roots capped at modulus one:

| `n` | 3 | 4 | 5 | 6 | 8 |
|---|---|---|---|---|---|
| `sup min_k` (interior ratio) | `0.99999987` | `0.99999989` | `0.99999995` | `0.99999995` | `0.99999997` |

pinned at `1` **from below** at every degree, with an independent second searcher
agreeing to `1e-7`. That search missed a real violation. The exact degree-seven
witness in [TwoSegmentLevelIdentityRefutation.md](TwoSegmentLevelIdentityRefutation.md)
has **zero** sublevel-contained spokes at its unique least critical point, with
the smallest excess ratio `1.0000212851940088...`. Thus `SPOKE>=1` and the
identity it was meant to protect are both retired.

## 4. Why the threshold is one

The corpus records the free-hub conjecture as `sup V ≤ 1` and observes that the
maximiser is the regular polygon at every degree. The identity of §3 cannot be
used to prove it. What survives from the same calculation is a different exact
scale. Writing `R` for the circumradius of the roots, the
discriminant/Fekete sandwich already recorded in `negative_results` entry 23 gives

```text
prod_{c} |f(c)|  =  prod_{i<j} |z_i − z_j|^2 / n^n            (|Res(f,f')| = n^n prod_c |f(c)|)
                 ≤  R^{n(n−1)} n^n / n^n  =  R^{n(n−1)}       (Fekete: prod_{i<j}|z_i−z_j| ≤ R^{n(n−1)/2} n^{n/2})
```

and hence, for the geometric mean `Gcrit` of the `n−1` critical-value moduli,

```text
Gcrit := (prod_c |f(c)|)^(1/(n−1)) ≤ R^n ≤ 1.
```

Therefore the genuinely surviving sufficient inequality is

```text
V_E ≤ Gcrit ≤ R^n ≤ 1.                                      (GM)
```

Unlike the retracted identity, (GM) survives its exact degree-seven
counterexample: there `μ≈0.8158048441`, `Gcrit≈0.8169765323`, and direct
optimisation gives `V_E≈0.8158063`. A separate 168-configuration pressure pass
through degrees `3..12` also found no ratio `V_E/Gcrit>1`; the apparent worst
residual `4.8e-7` is the known finite inner-search error at the exact regular
triangle. This is evidence, not a proof. The point of the scale is that **the
number one enters only through Fekete's bound**, and equality occurs at the
regular polygon, exactly where the two-segment mechanism is sharp.

> **Conditional corollary.** Inequality (GM) implies Erdős #1041.

*Proof.* Fekete gives `Gcrit≤R^n`; (GM) gives an ellipse hub of level at most
`R^n`, and the minimum-enclosing-disk normalisation in Theorem 1 scales this to
level at most one and length at most two. The open-disk version is strict after
scaling by its enclosing radius. ∎

This is not a solution or a relabelling of the retracted statement: `V_E>μ` on
the exact witness. It is a strictly weaker upper bound than equality with `μ`,
but still stronger than the level-one conjecture, and its proof is open.

## 4b. The radial product identity, and why the centre hub still fails near Fekete

On the extremal stratum — all roots on the unit circle — `log|f|` is harmonic in the
disk and the radial spokes have an exact closed form. Writing `p_m = Σ_k z_k^m`,

> **Identity.** For `|z_k| = 1` and `t ∈ [0,1]`,
>
> ```text
> prod_{j=1}^{n} |f(t z_j)|  =  exp( − Σ_{m≥1} t^m |p_m|^2 / m )  ≤  1.
> ```

*Proof.* `Π_j |f(t z_j)| = Π_{j,k} |t z_j − z_k| = Π_{j,k} |1 − t z_j z̄_k|` since `|z_k| = 1`,
and `Σ_{j,k} log|1 − t z_j z̄_k| = −Σ_m (t^m/m) Re(p_m p̄_m)`. ∎

At `t = 1` this is the power-sum/reciprocal-adjoint identity already recorded as
`exact_results::reciprocal_adjoint_resultant_power_sum_identity`; the content here is
the **one-parameter family**, which says the geometric mean of the `n` radial values is
`≤ 1` at *every* radius, not only at the endpoint. Verified to `6.2e−15` relative at
`n = 3, 5, 8`, `t = 0.3, 0.7, 0.95`, at perturbation scale `0.3` — far from the polygon,
so the identity is not a near-extremal artefact.

It gives "for each `t`, some spoke is safe", which is weaker than the "some spoke, for
all `t`" the mechanism needs, and that gap is real. Differentiating at `t = 0` recovers
the exact necessary condition `Re(p̄_1 z_j) ≥ 0` of
[TwoSegmentContainmentReduction.md](TwoSegmentContainmentReduction.md) §3. That
condition is **necessary but not sufficient**: predicted and actual safe sets agree
`30/30` at `n = 3, 4` but only `15/30` at `n = 12` over angular perturbations of scale
`1e−3`.

**The centre hub is not stable at the Fekete configuration.** Adversarial angular
perturbation — roots kept exactly on the unit circle, so `R = 1` throughout — drives the
second-smallest radial maximum above one at `n = 5` (`1.0024`, `‖η‖_∞ = 0.170` rad) and
at `n = 6` (`1.00055`, `‖η‖_∞ = 0.0524` rad = **3.00°**). The degree-six witness, angles
`2πk/6 + η_k` with

```text
η = ( 0.00173207975211076, −0.01636641293505736,  0.01474617820591595,
      0.01950276945344509, −0.05244827523897744,  0.032833660762563 )
```

has radial maxima `1.000549, 1.000672, 1.000593, 1.000000, 1.000576, 1.011784`: exactly
**one** safe radius, with the runner-up outside by `5.5e−4`, three orders of magnitude
above float64 resolution here.

So `exact_results::two_safe_origin_spokes_counterexample` (a degree-five configuration
far from the polygon) is not the sharp form of that elimination. The centre hub fails
**within three degrees of the regular hexagon**, on the stratum where the problem is
tight. The free hub is not a convenience for awkward configurations; it is required in
the hard regime itself, which is why §3's identity is stated for a free hub in the
ellipse and not for the circumcentre.

## 5. The extremal, exactly

Write `Λ` for the cheapest feasible two-segment length,
`Λ = inf { |h−a|+|h−b| : [h,a] ∪ [h,b] ⊂ {|f| ≤ 1} }`.

> **Theorem 3.** For `f = z^n − λ` with `|λ| = 1` and `n ≥ 2`, `Λ = 2` exactly, attained
> at `h = 0`.

*Proof.* Rotate so `λ = 1`. For `z = ρe^{iθ}` with `ρ > 0`,

```text
|z^n − 1|^2 − 1  =  ρ^n ( ρ^n − 2 cos nθ ),
```

so `K := {|f| ≤ 1}` minus the origin is exactly `{ρ^n ≤ 2 cos nθ}`, which requires
`cos nθ > 0` and therefore lies in the `n` sectors `|θ − 2πk/n| < π/(2n)`. These have
half-angle `π/(2n)` and centres `2π/n` apart, so they are **pairwise disjoint**: `K ∖ {0}`
has exactly `n` components, one containing each root, and `0 ∈ K` because `|f(0)| = 1`.

Let `[h,a] ∪ [h,b]` ⊂ `K` with `a, b` distinct roots. It is connected and meets two
different components of `K ∖ {0}`, so it contains `0`. Say `0 ∈ [h,b]`; then
`|h−b| = |h| + 1` and `|h−a| ≥ |a| − |h| = 1 − |h|`, whence `|h−a| + |h−b| ≥ 2`. The
origin attains it: `|f(t ω^k)| = 1 − t^n ≤ 1` on each radius and `|0−a| + |0−b| = 2`. ∎

The proof's mechanism is visible on the **bisector** between two adjacent roots, where
`θ = π/n` gives `nθ = π` and

```text
|f(s e^{iπ/n})|  =  |−s^n − 1|  =  1 + s^n  >  1     for every s > 0,
```

so the entire open bisector ray is outside `K`. The petals meet only at the origin, and
that is the whole reason the mechanism costs exactly `2` here.

## 5b. The extremal is a cusp, and its exponent is the critical-point splitting

`Λ = 2` at `z^n − 1` is not a delicate ridge. Perturb the regular `n`-gon along a fixed
angular direction, `z_k = exp(i(2πk/n + ε d_k))` with `Σd_k = 0`, `‖d‖ = 1` — so the roots
stay on the unit circle and `R = 1` exactly throughout — and `Λ` falls away from `2` at a
**fractional** rate:

| `ε` | `1e−2` | `1e−3` | `1e−4` |
|---|---|---|---|
| `Λ` (`n = 4`) | `1.701422` | `1.863580` | `1.937389` |
| `2 − Λ` | `2.986e−1` | `1.364e−1` | `6.261e−2` |

Fitted exponents of `2 − Λ ~ C ε^α` over the smallest four of eight points spanning
`3e−1 … 1e−4`:

| `n` | fitted `α` | `1/(n−1)` | `1/n` |
|---|---|---|---|
| 4 | `0.3388` | `0.3333` | `0.2500` |
| 5 | `0.2618` | `0.2500` | `0.2000` |
| 6 | `0.2187` | `0.2000` | `0.1667` |

approaching `1/(n−1)` from above, as a finite-`ε` correction should.

**The exponent is not a fit, it is a mechanism.** Breaking the Fekete degeneracy splits
the `(n−1)`-fold critical point at the origin into a ring of radius

```text
rho  ~  (ε / n)^{1/(n−1)}
```

— the same scale `NearFeketeCuspLaw.md` derives for the near-field model, where the
critical points of `z^n − m + εh` solve `n z^{n−1} = −ε h'(z)`. At the extremal the
two-segment hub sits at the origin because that is where all the lobes meet; once the
critical points move, the hub has to follow them, and the length `|h−a| + |h−b|` changes
**linearly** in the hub displacement. So `2 − Λ` should be proportional to `rho`, not
merely of its order. It is:

| `ε` | `3e−1` | `1e−1` | `3e−2` | `1e−2` | `3e−3` | `1e−3` | `3e−4` | `1e−4` |
|---|---|---|---|---|---|---|---|---|
| `(2 − Λ)/rho`, `n = 4` | `2.049` | `2.159` | `2.204` | `2.200` | `2.182` | `2.166` | `2.152` | `2.142` |

constant to `±4%` across **three and a half decades**. An exponent fit can be produced by
accident; a constant ratio over that span cannot.

The ratio **converges** rather than being constant from the start, and it converges more
slowly as the degree rises — which is the same finite-`ε` correction the fitted `α` shows.
At `n = 5` it runs `2.198 … 2.344` over the whole range, at `n = 6` it runs `2.417` down
to `1.742` and then flattens (`1.743, 1.742, 1.747` at the last three points). So the
limiting constants are about `2.14`, `2.20`, `1.74` at `n = 4, 5, 6`: they are **not**
degree-independent, and the honest claim is convergence to a degree-dependent constant,
reached by `ε ≈ 1e−2` at `n = 4` and only by `ε ≈ 1e−3` at `n = 6`.

**What it buys.** The Fekete deficit closes much faster than the mechanism's slack. On
the same family `1 − μ ~ ε^{n/(n−1)} ≍ rho^n` (measured exponents `1.367, 1.347` at
`n = 4`, against `n/(n−1) = 1.333`), so

```text
(2 − Λ) / (R − μ^{1/n})  ≍  2.15 n rho^{1−n}  ≍  1/ε   →   ∞,
```

which at `n = 4, ε = 1e−4` is a factor of about `8e4`. So `negative_results` entry 1's
"no uniform length slack" — the phenomenon that kills every fixed-budget transfer
argument — **does not bite this mechanism near the extremal**: there the slack exceeds
the deficit it has to cover by a diverging factor. That is the opposite of the descent
route's situation, where the slack and the deficit are the same order and the coupling
between them is the open problem.

Two readings, and the second is the load-bearing one. First, the two-segment route and
the descent route share a cusp exponent because they share a cause — the splitting of
the degenerate critical point — so the cusp is a property of the Fekete degeneracy, not
of either mechanism. Second, sharing the exponent is not sharing the *situation*: the
descent route pays its slack against a deficit of the same order, and this one does not.

## 6. Adversarial extension past the recorded cap

[TwoSegmentContainmentReduction.md](TwoSegmentContainmentReduction.md) §5 caps its
search at degree nine. Adversarial hill-climbing on the same objective, roots capped at
modulus one, four restarts per degree (regular polygon, jittered polygon, two random),
150 iterations, verdicts re-scored with the exact degree-`2n` segment maximum:

| `n` | 10 | 12 | 16 | 20 |
|---|---|---|---|---|
| `sup V_E` | `1.0000000000` | `1.0000000000` | `1.0000000000` | `1.0000000000` |

Attained at the regular polygon at every degree and **never exceeded**. Jittering the
polygon strictly decreases the objective (`0.99807, 0.99809, 0.98898, 0.98283`), so the
Fekete configuration is a strict local maximiser at each of these degrees, which is what
§4 predicts. Random restarts land far below (`0.034` to `0.99`).

## 7. A new member of the instrument-defect class

At the extremal the mechanism's own margin falls below float64 resolution, and it does
so in the **unsafe** direction.

For `f = z^n − 1` and a hub `h` near the origin, `|f(h)| − 1 = Θ(|h|^n)`, because every
power sum `p_1, …, p_{n−1}` of the roots vanishes and the first surviving term of
`log|f(h)| = −Re Σ_m p̄_m h^m / m` is the one of order `n`. So for `|h| ≳ 10^{−16/n}`
an **infeasible** hub reads as feasible: at `n = 10` and `|h| = 0.02` the true excess is
`9.5e−17`, predicted scale `|h|^n = 1.0e−17`, and float64 returns `|f(h)| = 1.0000000000000002`.

Measured consequence: a float64 `Λ` search on `z^n − 1` reports `1.99994, 1.99897,
1.99655, 1.99354, 1.96371` at `n = 4, 5, 6, 8, 10` against the true value `2` of Theorem 3
— a `1.8%` error at `n = 10`, and every "shorter" path it finds is spurious. Dense
resampling does not catch it: the segments genuinely evaluate to `1.0000000000` in
float64 at 200 001 points.

This is the same class as `negative_results` entry 34, with a different cause. Entry 34's
members under-report **branch length**; this one under-reports **the level**, and its
cause is not quadrature or underflow but the vanishing of the low power sums at the
Fekete point. Two rules follow.

* Any two-segment or hub computation **on or near the extremal family** must be done in
  extended precision; float64 is adequate only where `p_1` is bounded away from zero,
  which is every generic configuration and none of the hard ones.
* The strictness in `1 + s^n > 1` of §5 is exact mathematics and is **not** numerically
  observable for `s^n < ε`; the receipt therefore asserts the closed form and the
  non-strict exclusion, and takes strictness from the algebra.

The trap reproduced itself **three times in one session on three unrelated probes** --
the `Lambda` search of §5, the receipt's own bisector-exclusion check, and the spoke
calibration of §3b, where `z^n - r^n` reported only `2` of `n` radial spokes as
contained when all `n` provably are, because at `t = 1 - 1e-3` the margin is
`|z|^n ~ 1e-24`. Three independent reproductions is why it is recorded as a class
member rather than as a bug.

## 8. What this does not settle

* The identity `V_E = μ` and its necessary condition `SPOKE>=1` are **false**,
  refuted exactly in degree seven by
  [TwoSegmentLevelIdentityRefutation.md](TwoSegmentLevelIdentityRefutation.md).
  The weaker geometric-mean inequality (GM) above is measured, not proved.
* A necessary condition for `≤`, not yet tested: at the minimum-critical hub `c*` the
  two-segment path at level `μ` must pass through `c*`, and both endpoints and the hub
  lie in the closed ellipse, which is convex — so `c*` lies in it too, i.e. the
  **merging** pair must satisfy `d_a + d_b ≤ 2` after normalising `R = 1`. E9/E10 supply
  this for the two **nearest** roots, not for the merging pair, and a first pass measured
  `(d_a + d_b) / (2μ^{1/n})` reaching `3.31` for the merging pair — so the nearest-pair
  bound does not transfer. That measurement is **not** trustworthy as stated: at
  `z^n − r^n` the minimum-critical hub is `(n−1)`-fold degenerate, where the two-branch
  quadratic model is the wrong local model (`negative_results` entry 24), and the
  calibration returned `0` at `n = 3` for exactly that reason. Testing `d_a + d_b ≤ 2`
  with a multiplicity-aware branch tracker is the sharpest available falsifier for §3.
* §5b's scaling law is measured along **one** angular direction per degree and at
  `n = 4, 5, 6` only. The exponent `1/(n−1)` has a mechanism behind it; the limiting
  constants (`2.14, 2.20, 1.74`) do not, they are degree-dependent, and no
  direction-uniform statement is attempted. The `n = 6` ratio only settles by
  `ε ≈ 1e−3`, so the convergence rate is itself untested at higher degree.
* Nothing here bears on the descent route, on `L(c*) ≤ 2R`, on the componentwise
  combined-charge lemma of [CriticalTreeLengthCharge.md](CriticalTreeLengthCharge.md),
  or on the near-Fekete cusp half of [NearFeketeCuspLaw.md](NearFeketeCuspLaw.md).
* Novelty is **not** claimed for `μ ≤ R^n` (entry 23 records the sandwich), for Fekete's
  bound, or for the properness/covering argument of Theorem 2, which is standard
  lemniscate topology. What is new here is the composition: that the mechanism's level is
  `μ`, that its threshold is therefore Fekete's, and the normalisation of Theorem 1.

**Erdős #1041 remains open.**

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_two_segment_level_identity.py --part all
```

Arms: `floor`, `identity`, `fekete`, `extremal`, `spoke`, `originhub`, `cusp`, `degeneracy`. Receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1041_two_segment_level_identity_receipt.json`.
