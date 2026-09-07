# Erdős 1041: the hard regime is one point, and the two-root component is one Blaschke product

Status: one coordinate change, one exact conformal normal form, two
unconditional length bounds, and one affine-invariant sharpening of the
standing obligation. 2026-08-24. **This does not prove Erdős #1041.** It
bounds `L(c*)` only when the merge component has room, and it says nothing
about the near-Fekete half, which
[ConeBoundMonotoneFunctional.md](ConeBoundMonotoneFunctional.md) and
[MonotoneTurningProof.md](MonotoneTurningProof.md) own.

## 0. What was open

[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) splits the problem on
the discriminant ratio `D` and says of the easier-looking side:

> * **`D` bounded away from 1.** Then `T* ≤ D^(1/(n−1))` is bounded away from
>   1, so the two cells of `{|f| < T*}` that merge at `c*` do so strictly below
>   level one, and the merged component has room between level `T*` and level
>   1. **Nothing here converts that room into a length bound yet.**

Section 4 below is that conversion. Sections 1–2 are about why the *other*
side was so hard to search, and section 5 is what the coordinates suggest the
obligation should have been.

## 1. Theorem N — the affine normalisation, and what it collapses

> **Theorem N.** Let `f` be monic of degree `n ≥ 2`, let `c` be a critical
> point with `f(c) ≠ 0`, let `lambda` be any `n`-th root of `f(c)`, and put
>
> ```text
> P(u) = f(c + lambda u) / f(c).
> ```
>
> (a) `P` is monic of degree `n`, `P(0) = 1`, `P'(0) = 0`.
>
> (b) `R_P = R_f/|lambda|`, `mu_P^{1/n} = mu_f^{1/n}/|lambda|`,
> `L_P(kappa) = L_f(c + lambda kappa)/|lambda|`. Hence `L/(2R)`,
> `L/(2 mu^{1/n})`, `Delta/R` and the hub set
> `A_F = {c : f'(c) = 0, |f(c)| <= R^n}` are all **invariant**.
>
> (c) Taking `c = c*` (so `mu_P = 1`), the residual freedom is exactly
> `(a_2, …, a_{n−1}) in C^{n−2}`, since the `u^1` and `u^0` coefficients are
> pinned to `0` and `1`.
>
> (d) **`P = u^n + 1` if and only if `f(z) = (z − c)^n + f(c)`.** So the whole
> equality family — every `z^n − r^n` for every `r in (0,1)`, under every
> rotation, translation and scaling — is the **single point `a = 0`**.

*Proof.* (a) `f(c + lambda u) = lambda^n prod_k (u − (a_k − c)/lambda)` and
`lambda^n = f(c)`, so `P = prod_k(u − b_k)` is monic with `P(0) = 1`;
`P'(0) = lambda f'(c)/f(c) = 0`. (b) is the chain rule plus the fact that a
similarity multiplies every length and every circumradius by `|lambda|`, while
critical values scale by `f(c)`, so `|P(kappa)| ≤ R_P^n` reads
`|f(·)| ≤ R_f^n`. (c) is (a). (d) `P = u^n + 1` says
`f(c + lambda u) = f(c)(u^n + 1)`; substituting `u = (z − c)/lambda` and using
`lambda^n = f(c)` gives `f(z) = (z − c)^n + f(c)`, and conversely. ∎

**What (d) collapses.** `HardRegimeIsNearFekete.md` lists four properties of
the hard set, each of which is a statement about root coordinates and each of
which (d) removes:

| in root coordinates | in `(a_2,…,a_{n−1})` |
|---|---|
| an "exponentially thin neighbourhood of a measure-zero configuration", a `1e-7`-thin shell about a rotated regular `n`-gon | a single point, `a = 0` |
| a cusp: splitting the multiplicity-`(n−1)` hub drops the objective by a **fractional power** of the perturbation, so a search at any fixed scale sits genuinely below the supremum | the cusp tip is a grid node; a search can stand **exactly on it** |
| the limit `r → 1⁻`, approached but never attained | no limit — every `r` is the same point |
| "at `eps ~ 1e-7` the quantities of interest have margins `~1e-5`, so double precision carries only about nine significant digits of headroom" | no small parameter, so full double precision |

The practical consequence is the one that matters. `negative_results` entry 19
records six occasions on which a hub statement was supported by adversarial
maximisation, came back with a supremum pinned just below its threshold, and
was later false; `HardRegimeIsNearFekete.md` explains those pins as basin
artifacts of a bulk search that "has essentially no chance of entering a
`1e-7`-thin shell". In these coordinates the shell is the origin, so the
question "did the search reach the hard set?" is answered by inspection.

**And it answers a recorded stop condition.** `CriticalTreeLengthCharge.md`
ends with: *"Passing to circumradius one without also transforming the level
threshold is another stop condition: admissibility is not purely affine
geometric data."* Theorem N transforms both — the scale factor is
`lambda^n = f(c)`, which is the level — and §5 replaces admissibility by an
affine-invariant condition that implies it.

## 2. The one thing that still bites, and it is removable

At `a = 0` the hub has multiplicity `n − 1`, and the float64 pipeline
under-reports `L`. Measured `minl_S` at `a = 0`, whose exact value is `1`:

| `n` | 3 | 4 | 5 | 6 | 8 | 10 | 12 |
|---|---|---|---|---|---|---|---|
| float64 | `0.999999995` | `0.999997069` | `0.999903899` | `0.999366204` | `0.994621289` | `0.984148532` | `0.961393531` |

This is `negative_results` entry 24 — "on `z^n − r^n` it returns `1.7989`
against the true `2r = 1.8` at degree six" — and my `n = 6` row reproduces it
(`0.999366` against `1.7989/1.8 = 0.99939`). Entry 24 records that the deficit
"does not shrink with the start offset" and draws the correct rule: **equality
families must be asserted from their ordinary proofs, not from the
integrator.** That rule stands.

What entry 24 does not record is that the deficit **does** shrink with
*precision*. Running the identical pipeline — root extraction on `P − t`,
nearest-point matching, straight chord into the hub — at 20 digits returns
`1.000000000000` at every degree tested. So the under-report is an artifact of
float64 root extraction at a coalescing fibre, not an intrinsic property of a
degenerate hub, and it is removable at a cost. Arm `PREC` of the receipt is
that comparison, and it fails if the deficit is ever negative (a tracker
inventing length), if it grows with precision, or if it does not reach zero.

**A new member of the branch-tracking defect class, and it runs backwards.**
The natural way to make a hub tracker accurate is to walk closer to the hub
before closing with the straight chord. That is wrong here. Writing the closing
depth as `-log10(1 - t/mu)`, the measured drift of the §1 invariants under a
similarity — which is exactly zero in exact arithmetic, so it is pure
instrument resolution — is

| closing depth | 4 | 6 | 8 | 10 | 12 | **14** |
|---|---|---|---|---|---|---|
| drift | `1.6e-9` | `1.6e-9` | `1.6e-9` | `1.6e-9` | `1.7e-9` | **`1.2e-7`** |

a factor of **78 lost in the last two decades**, because by depth 14 the two
branch points are separated by `~sqrt(eps)` and the closing chord is being
measured off pure noise. What makes it a defect rather than a tuning note is
that **the standard calibration cannot see it**: the quadratic returns
`|minl_S − 1| = 6e-14` at every depth from 4 to 14, because a quadratic's
branch is straight and the chord closes it exactly however late it is taken.
The receipt now runs at depth 10 and the `INV` arm carries the drift.

*A guess I made and my own receipt killed:* I first wrote that the deficit
obeys `eps_mach^{1/(n−1)}`, on the reasoning that a backward-stable root
extraction displaces a root of local multiplicity `m` by `eps^{1/m}`. The
float64 numbers fit that within a factor of three across `n = 3…12`, which is
exactly the kind of fit that should not be trusted: the high-precision arm
returns deficit `0`, so the law was fitted to a pipeline artifact rather than
to the conditioning it claimed to describe. Recorded because the fit was
convincing and the claim was wrong.

## 3. Theorem B — the two-root component is one Blaschke product with one real parameter

Let `c*` be a critical point with `|f(c*)| = mu = min_k |f(c_k)|`, and for
`t > mu` let `Omega_t` be the component of `{|f| < t}` containing `c*`. Let
`t_2 = sup{ t : Omega_t contains exactly two roots }`. The component structure
changes only at critical levels, so `t_2 > mu` whenever `c*` is simple and no
other critical point at level `mu` attaches a further root to the same
component. On the equality family `t_2 = mu` exactly, and everything in §4 is
vacuous there — which is the correct behaviour, since that is where the
obligation is tight.

> **Theorem B.** For every `t in (mu, t_2)`, with `a, b` the two roots of
> `Omega_t` and `q = sqrt(mu/t) in (0,1)`:
>
> **(B1)** `Omega_t` is simply connected and `f : Omega_t -> D_t` is proper of
> degree 2, with `c*` as its only critical point.
>
> **(B2)** There is a conformal `psi : D -> Omega_t` with `psi(0) = c*` and
>
> ```text
> f(psi(zeta)) = t e^{i alpha} (zeta^2 − q^2)/(1 − q^2 zeta^2).
> ```
>
> The two zeros are **antipodal**, and `q` is pinned by the level ratio alone.
>
> **(B3)** `psi(q) = a`, `psi(−q) = b`, and `psi([−q, q])` is exactly the
> descent arc `a -> c* -> b`. Since `[−q, q]` is a diameter of `D`:
>
> > **the descent arc is the hyperbolic geodesic of `Omega_t` joining `a` to
> > `b`, and `c*` is its hyperbolic midpoint — simultaneously for every
> > admissible level `t`.**
>
> **(B4)** `g_{Omega_t}(a,b) = log((1+q^2)/(2q))` and
> `g_{Omega_t}(c*,a) = g_{Omega_t}(c*,b) = log(1/q)`.
>
> **(B5)** `rad(Omega_t, a) = 2 t q /((1+q^2)|f'(a)|)` and
> `rad(Omega_t, c*) = sqrt(2 t (1−q^4)/|f''(c*)|)`.

*Proof.* **(B1)** A bounded component `U` of `{|f| > t}` would have `|f| = t`
on `∂U` and `|f| > t` inside, against the maximum principle; so `Omega_t` has
no holes. `|f| -> t` at `∂Omega_t` gives properness, and the degree is the
number of zeros inside, namely 2. Riemann–Hurwitz, `chi(Omega_t) = 1 = 2·1 − b`,
gives `b = 1`.

**(B2)** Let `psi` be a Riemann map with `psi(0) = c*`. Then `B := f∘psi/t` is
a proper degree-2 self-map of `D`, hence a Blaschke product with zeros
`zeta_1, zeta_2 in D`, and `B'(0) = 0`. From

```text
B'/B = 1/(zeta−zeta_1) + 1/(zeta−zeta_2)
        + conj(zeta_1)/(1−conj(zeta_1)zeta) + conj(zeta_2)/(1−conj(zeta_2)zeta)
```

at `zeta = 0`, `B'(0) = 0` reads

```text
(1/zeta_1 − conj(zeta_1)) + (1/zeta_2 − conj(zeta_2)) = 0.
```

Writing `zeta_j = r_j e^{i theta_j}`, the `j`-th term is
`(1/r_j − r_j) e^{−i theta_j}` with `1/r − r > 0` **strictly decreasing** on
`(0,1)`. Two such vectors cancel only if `e^{−i theta_2} = −e^{−i theta_1}`
and `r_1 = r_2`; hence `zeta_2 = −zeta_1`. Rotating the disk puts
`zeta_1 = q > 0`, giving the displayed form, and
`mu = |f(c*)| = t|B(0)| = t q^2`.

**(B3)** For real `s in [−q,q]`, `s^2 − q^2 ≤ 0` and `1 − q^2 s^2 > 0`, so
`arg f(psi(s)) ≡ alpha + pi` is constant while
`|f(psi(s))| = t(q^2 − s^2)/(1 − q^2 s^2)` decreases strictly from `mu` at
`s = 0` to `0` at `s = ±q`. That is precisely the pair of descending branches
at `c*`. A diameter of `D` is a hyperbolic geodesic with `0` as midpoint, and
the Green's function and the hyperbolic metric are conformal invariants.

**(B4)** `g_D(q,−q) = log(|1 − conj(q)(−q)|/|q−(−q)|) = log((1+q^2)/(2q))`, and
`g_D(0,±q) = log(1/q)`.

**(B5)** `B'(q) = e^{i alpha} 2q(1−q^4)/(1−q^4)^2` gives
`|psi'(q)| = 2tq/((1−q^4)|f'(a)|)`, and `rad = |psi'(q)|(1−q^2)`. For `c*`,
expand `f(psi(zeta)) − f(c*) = t e^{i alpha} zeta^2 (1−q^4)/(1−q^2zeta^2)`
against `(f''(c*)/2)(psi−c*)^2`. ∎

**What is not first here.** `CriticalTreeLengthCharge.md` §"Component
uniformization" already records the general statement: a level-one component
with `k` roots is simply connected, `f : Omega -> D` is proper of degree `k`,
`B = f∘phi` is a degree-`k` Blaschke product, and Riemann–Hurwitz gives `k−1`
critical points. Theorem B is the `k = 2` case **at an intermediate level**,
where three things happen that do not happen at level one: the Blaschke
product has a single real parameter `q = sqrt(mu/t)`; its zeros are forced
antipodal by the centred critical point; and the pullback of the descent arc
is a **diameter**, not a tree.

That last point is why this case escapes that file's own stop condition. It
says of the level-one trace estimate: *"A bound for arbitrary bounded univalent
`phi` would be too broad."* For a tree of unknown shape, yes. For a diameter
with both endpoints pinned at radius `q`, a univalent bound is the right
generality — which is §4.

## 4. Theorem R — room converts into length

> **Theorem R.** In the notation of Theorem B, with `d_a = |a − c*|`,
> `d_b = |b − c*|`,
>
> ```text
> (R1)   L(c*)  <=  (d_a + d_b) · ((1+q)/(1−q))^2
> (R2)   L(c*)  <=  2 diam(Omega_t) · log((1+q)/(1−q))  <=  8 t^{1/n} log((1+q)/(1−q))
> ```
>
> for every `t in (mu, t_2)`, hence for `q` as small as `sqrt(mu/t_2)`.

*Proof.* By (B3), `L(c*) = int_{−q}^{q} |psi'(s)| ds`. Koebe's distortion
theorem gives `|psi'(s)| ≤ |psi'(0)|(1+s)/(1−s)^3`, and
`int_0^q (1+s)(1−s)^{−3} ds = q/(1−q)^2`, so
`int_0^q |psi'| ≤ |psi'(0)| q/(1−q)^2`. Koebe's growth theorem gives
`d_a = |psi(q) − psi(0)| ≥ |psi'(0)| q/(1+q)^2`. Dividing and adding the
mirror half gives (R1). For (R2), the Koebe 1/4 theorem gives
`dist(psi(s), ∂Omega_t) ≥ (1/4)|psi'(s)|(1−s^2)`, and
`dist(z,∂Omega) ≤ diam(Omega)/2` because `D(z, dist) ⊂ Omega`; so
`|psi'(s)| ≤ 2 diam/(1−s^2)`, and
`int_{−q}^{q} ds/(1−s^2) = log((1+q)/(1−q))`. The final step is
`diam ≤ 4 cap({|f| ≤ t}) = 4t^{1/n}`, which is (D) and (B) of
[LemniscateCapacityBudget.md](LemniscateCapacityBudget.md). ∎

> **Corollary R.** Let `f` be monic with all roots in the open unit disk. If
> the two-root component of `c*` survives to a level `t ≤ 1` with
>
> ```text
> t / mu  >  coth^2(1/8)  =  64.68…,
> ```
>
> then `L(c*) < 2`, and **Erdős #1041 holds for that `f`** — the descent arc
> joins two roots, lies in `{|f| ≤ mu} ⊂ {|f| < 1}`, and is short.

*Proof.* `8 log((1+q)/(1−q)) < 2` iff `q < tanh(1/8)` iff `mu/t < tanh^2(1/8)`. ∎

**Reach, measured, and it is a slice rather than a half.** The room `t_2/mu`
is at its median barely above 1 — most configurations have no room at all,
because `t_2 = mu` exactly on the equality family and near it. Over 34 samples
per degree, half bulk and half drawn from the near-Fekete shell:

| `n` | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|
| median room `t_2/mu` | `1.213` | `1.029` | `1.123` | `1.016` | `1.176` |
| 90th percentile | `12.70` | `3.52` | `6.70` | `5.14` | `4.48` |
| max | `131.99` | `12.47` | `106.48` | `199.50` | `16.66` |
| fraction with room `> 64.7` | `0.029` | `0.000` | `0.059` | `0.029` | `0.000` |
| **fraction settled by (R1)–(R2)** | `0.147` | `0.147` | `0.235` | `0.176` | `0.265` |

The last row is the useful one: the R-free criterion of Corollary R fires
rarely, but (R1), which uses the actual chord `d_a + d_b` rather than the
worst-case `2R`, settles **15–27%** of sampled configurations outright. The
receipt's independent `THMR` arm agrees: 40 samples over degrees 3–7, **`0`
violations** of (R1)–(R2), **`13` settled outright (32.5%)**, worst
`L(c*)/bound = 0.826`.

The Koebe constants are the reason it is not more. On the same samples
`L(c*)/bound` never exceeds about `0.55`, so the bound is loose by a factor of
two or more even where it fires — Koebe distortion is sharp for the Koebe
function, whose image is a slit plane, and `Omega_t` is nothing like one. What
(R1)–(R2) establish is that the conversion **exists** and is elementary; the
constant is not the sharp one.

**Where the loss is not the issue.** The measurements also show
`L(c*) − (d_a + d_b)` running at `3e-4` to `2e-3` of the chord in the bulk:
the descent arc is very nearly straight there, and essentially all of the
obligation `L ≤ 2R` is carried by the chord budget `d_a + d_b ≤ 2R`, not by
curvature. The turning floor of `turning_floor_at_simple_saddle` is consistent
with this and explains it — it forces turning only when the angle `phi`
subtended at the hub is far from `pi`, and in the bulk the merge pair and the
saddle are nearly collinear. The equality family is exactly the opposite
corner, `phi = 2 pi/n`.

## 5. FEKETE-HUB MIN — an affine-invariant sharpening that survives entry 29

Put `A_F = { c : f'(c) = 0, |f(c)| ≤ R^n }`, the **Fekete-admissible** hubs.
Three facts, all immediate:

* `A_F ≠ ∅`. The resultant identity and Fekete give
  `mu^{n−1} ≤ prod_k|f(c_k)| = prod_{i<j}|z_i − z_j|^2/n^n ≤ R^{n(n−1)}`,
  i.e. `mu ≤ R^n`, so `c* in A_F`. (This is `HardRegimeIsNearFekete.md`'s own
  inequality.)
* `A_F` is affine-invariant, by Theorem N(b).
* For roots in the **open** unit disk, `R < 1`, so every hub of `A_F` is
  admissible for the target lemniscate — no separate admissibility qualifier
  is needed.

> **Conjecture (FEKETE-HUB MIN).**
> `min_{c in A_F} L(c) <= 2 mu^{1/n}`.

* **It implies Erdős #1041**, since `mu^{1/n} ≤ R < 1` and the minimising hub
  is admissible.
* **It is strictly stronger** than the standing obligation
  `min_{admissible c} L(c) ≤ 2R` of
  `admissible_branch_length_reformulation`, on both counts: `mu^{1/n} ≤ R`,
  and `A_F` is a subset of the admissible hubs.
* **It is exactly tight on the whole equality family and nowhere else.** On
  `f = (z−c)^n + v` we have `A_F = {c}`, `L(c) = 2R` and `mu^{1/n} = R`.
* **It survives `negative_results` entry 29.** Entry 29 refutes the *per-hub*
  form `L(c*) ≤ 2 mu^{1/n}` at degree four with ratio `1.004246913`, and
  records, as load-bearing caveats, that the two smallest critical values agree
  to `2.30e-9` relative, that **at the runner-up hub the ratio is `0.9608`**,
  and that "under a slightly wider tie-tolerant selector it would not stand".
  `A_F` is that tie-tolerant selector, and it is not fitted to the witness: it
  is the affine-invariant hub set, and its width `R^n/mu` is exactly the Fekete
  deficit. Entry 32 points the same way — 196 of 197 observed symmetric-bound
  violations sit at non-minimal hubs, and the minimum-critical hub has 1 in 480.

**The discriminator, on one configuration.** Entry 29's witness is not stored
in this directory, and two searches in **root** coordinates — one of them
tie-seeking, built specifically for this — both failed to rediscover anything
like it, converging to the symmetric extremal point instead. A search in the
normalised coordinates of §1 found a member of its family immediately. Pinned
in the receipt as arm `PIN`:

```text
P(u) = u^4 + a3 u^3 + a2 u^2 + 1,     P(0) = 1,  P'(0) = 0
a3 = -0.199341957743 - 0.409216378485i
a2 = -0.000225877943 + 0.000866621978i
```

| at this one configuration | value |
|---|---|
| per-hub strong form `L(c*)/(2 mu^{1/n})` | **`1.00329`** — refuted |
| FEKETE-HUB MIN `min_{A_F} L/(2 mu^{1/n})` | **`0.89683`** — survives |
| separation | `0.1065` |
| critical-value gap | `5.14e-10` (entry 29 records `2.30e-9`) |
| `|A_F|` | `3` — all three hubs are Fekete-admissible |

Stable across mesh sizes (`1.0032926` at 420 steps, `1.0032928` at 840) and
reproduced from an independent restart at `1.0032931` on the accurate tracker.
So the two statements are separated by `1e-1` on a single polynomial, not by a
tolerance — and the separation is in the direction entry 29 itself predicts,
since it records `0.9608` at *its* runner-up hub.

**Still not a proof.** A conjecture that survives one adversarial search is a
conjecture.

## 6. What the search in these coordinates says, and what it does not

Objective `minl_S = min_{A_F} L / (2 mu^{1/n})`, maximised over
`(a_2,…,a_{n−1})` by multi-scale hill climbing, seeded at `a = 0`, in its
immediate neighbourhood, and at random points out to radius `~1.2`.

| `n` | `sup minl_S` found | maximiser | reading |
|---|---|---|---|
| 3 | `0.9999999949` | `a = 0`, `R = 1.000000`, `rho/R = 1.000000` | the extremal point; residual `5e-9` is the §2 instrument floor |
| 4 | `0.9999970658` | `a = 0`, `R = 1.000000`, `rho/R = 1.000000` | same, floor `2.9e-6` |

At both degrees the search **converges to the extremal point itself** and
returns its exact calibration value. That is a qualitatively different reading
from the recorded pins: `negative_results` entry 19's warning is that a
supremum pinned just under a threshold is one basin, and the answer here is
that the basin **is** the extremal point, with the maximiser printed and
identifiable — `a = 0` to the digit.

**A sweep of the whole degree-four moduli space.** At `n = 4` the normalised
space is four real dimensions with no small parameter, so it can be swept
outright — which is structurally impossible in root coordinates. 42 000
quasi-random points over the ball of radius 3 in `(a_2, a_3)`, `0` failures:

```text
SUP = 0.9647877188      points with minl_S > 0.97 :  0
maximiser  a = (0.00626 + 0.04366i,  0.03101 - 0.03596i),   |a| = 0.0648
```

Two things are worth reading off. Nothing in 42 000 samples comes within `3.5%`
of the threshold. And the sweep's maximiser is, to within sampling statistics,
simply **its own closest approach to `a = 0`** — at that radial sampling
density the expected minimum `|a|` over 42 000 draws is `~0.065`, and the
maximiser sits at `0.0648`. The objective behaves like a function with an
isolated maximum at the extremal point and no competing structure anywhere in
the ball.

**And the instrument now has its licence.** The `PIN` arm of the receipt
exceeds `1` where the answer is known to (§5), which is exactly what entry 19
demands of any search that reports a survival. The two root-coordinate searches
that could not do this are recorded above; the coordinate change is what
supplied it.

## 7. What would change the picture

* A sharp replacement for the Koebe constants in Theorem R. The bound is loose
  by `≥ 2x` where it fires; the true arc is nearly straight. A distortion
  estimate that uses `f∘psi = tB` rather than mere univalence would be the
  object.
* Entry 29's **own** witness, stored as exact literals. §5 pins a member of its
  family, which is enough to license this instrument, but it is not entry 29's
  configuration and the two cannot be compared root by root. Storing the
  original would let every future search in this directory be validated against
  the one recorded refutation of the per-hub strong form rather than against a
  cousin of it.
* A statement about `t_2/mu` itself. Corollary R needs room; the near-Fekete
  half is exactly `t_2 = mu`. What is missing is any theorem forcing room when
  the configuration is far from Fekete — the two-sided version of
  `mu ≤ R^n`.

## Claim boundary

**Proved, by ordinary mathematics:** Theorem N (a)–(d); Theorem B (B1)–(B5),
including the antipodality of the Blaschke zeros and the identification of the
descent arc as a hyperbolic geodesic with `c*` as midpoint; Theorem R
(R1)–(R2) and Corollary R; the three facts about `A_F` in §5.

**Not first here:** the general Blaschke/Riemann–Hurwitz uniformisation of a
lemniscate component ([CriticalTreeLengthCharge.md](CriticalTreeLengthCharge.md));
`cap({|f| ≤ t}) = t^{1/n}`, `Area ≤ pi t^{2/n}`, `diam ≤ 4t^{1/n}`
([LemniscateCapacityBudget.md](LemniscateCapacityBudget.md) (A)–(D));
`mu ≤ R^n` and the `D`-split ([HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md));
the corrected obligation and the equality family
(`admissible_branch_length_reformulation`); the chord-deficit identity
(`chord_deficit_length_identity`); the turning floor
(`turning_floor_at_simple_saddle`). Koebe's growth, distortion and 1/4
theorems are classical.

**Measured, not proved:** every table in §2, §4, §5 and §6; the FEKETE-HUB MIN
conjecture of §5. The pinned witness of §5 is a float64 configuration verified
at two mesh sizes and reproduced from an independent restart; it is a
refutation of the per-hub form to the accuracy stated (`1.00329`, stable to
`2e-7`), not an exact certificate, and this directory has four recorded
retracted counterexamples of that shape — so it is used only as an instrument
licence and as a discriminator, never as an exact result.

**Retracted within this note:** the `eps^{1/(n−1)}` law for the degenerate-hub
under-report, §2.

**Not established: novelty.** The affine normalisation of a polynomial at a
critical point is standard; the degree-2 Blaschke normal form and the
antipodality of its zeros under a centred critical point should be assumed
classical until a priority search on finite Blaschke products and lemniscate
geometry says otherwise. What is claimed as new is only the *use*: that this
normalisation collapses this problem's hard set to a point, and that the
`k = 2` component model converts level room into a length bound.

**Erdős #1041 remains open.** Nothing here bounds `min_c L(c)` in general,
nothing here touches the near-Fekete half, and Corollary R settles a slice of
configurations, not a case of the theorem.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_affine_normalised_moduli.py --trials 60
```
