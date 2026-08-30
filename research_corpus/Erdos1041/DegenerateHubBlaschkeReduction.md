# Erdős 1041: the degenerate hub has an exact Blaschke normal form — and Conjecture P is false

Status: **one refutation with an explicit closed-form family, and one theorem
with its proof and its threshold table.** 2026-08-24. **Erdős #1041 remains
open** and nothing below claims otherwise.

Two independent results, both about the same gap.

1. **Conjecture P of [UnconditionalConstantFactorBound.md](UnconditionalConstantFactorBound.md) §10 is false.**
   Its constant `sqrt(2) varpi = 3.7081493546` is not an upper bound for the
   one-root lobe perimeter, and the quadratic is not the extremal. An
   elementary closed-form family reaches `1.5805` times the conjectured bound
   at `n = 26` and tends to `2 pi / (sqrt(2) varpi) = 1.6944`. Consequently
   **Theorem 3 of that note is not available at `beta = sqrt(2) varpi`**, and
   the residue it isolates has to be restated.
2. **A theorem that removes the silence on the degenerate stratum.**
   [BergmanSegmentLengthBound.md](BergmanSegmentLengthBound.md) §6 records that
   its machinery is "silent by construction on the extremal family `z^n - r^n`,
   because no level there ever gives a two-root component", and
   [BergmanGeodesicInvariance.md](BergmanGeodesicInvariance.md) removes that
   silence only for that one symmetric family, by hand, using its `n`-fold
   symmetry (Proposition S). §2–§4 below replace the symmetry by an averaging
   argument and prove the general statement: **at a critical point of
   multiplicity `m`, the merge component carries an exact `m`-fold cyclic
   Blaschke normal form, and (C) holds there as soon as an explicit threshold
   `Q(m)` is met.** `Q(2) = tanh 1` recovers Theorem E exactly; `Q(m)` rises to
   `1` like `1 - 4 e^{-m}`.

---

## 1. Conjecture P is false

> **Conjecture P** (as landed). Let `C` be a connected component of
> `{|f| <= sigma}` containing exactly one root of `f`. Then
> `H^1(dC) <= sqrt(2) varpi sigma^{1/n}`, with equality exactly for `f`
> quadratic at `sigma = mu`.

**Counterexample family.** Take

```text
f(z) = z^n - z = z (z^{n-1} - 1),        n >= 3,
```

whose roots are `0` and the `(n-1)`-th roots of unity. Its critical points
solve `n z^{n-1} = 1`, so they form a regular `(n-1)`-gon of radius
`|c| = n^{-1/(n-1)}`, all with the same critical-value modulus

```text
mu = |f(c)| = (n-1)/n * n^{-1/(n-1)} .
```

Below `mu` every component of `{|f| < sigma}` holds exactly one root (F5 of
[UnconditionalConstantFactorBound.md](UnconditionalConstantFactorBound.md)), so
for `sigma = mu(1-eps)` the component `C` around the root `0` is a legitimate
one-root component, and `rho = sigma^{1/n}`.

Measured at `sigma/mu = 0.9999`, by **two independent instruments**:

| `n` | 2 | 3 | 4 | 6 | 10 | 16 | 26 |
|---|---|---|---|---|---|---|---|
| `H^1(dC)/rho`, star/ray solver | `3.6961` | `3.7973` | `4.0432` | `4.4755` | `5.0333` | `5.4859` | `5.8622` |
| `H^1(dC)/rho`, `arg f` ODE tracer | — | `3.79671` | `4.04248` | `4.47451` | `5.03200` | `5.48447` | `5.86059` |
| ratio to `sqrt(2) varpi` | `0.9967` | **`1.0239`** | **`1.0902`** | **`1.2067`** | **`1.3570`** | **`1.4790`** | **`1.5805`** |

The two instruments share no code path: the first solves
`t^{2n} - 2 cos((n-1)phi) t^{n+1} + t^2 = sigma^2` for the smallest positive
root on each ray and integrates the resulting star-shaped boundary; the second
integrates `dz/dphi = i f/f'` — the exact `arg f = phi` parametrisation of
`{|f| = sigma}` — over `phi in [0, 2pi]`, whose closure error is a built-in
gate on having traced the *correct* component with winding one. They agree to
five digits at every degree.

**Instrument validation.** On the quadratic both return the exact Bernoulli
half-loop: `sqrt(2) varpi = Gamma(1/4)^2/(2 sqrt pi) = 3.7081493546`, reached
from below as `sigma -> mu` (`3.5790` at `0.99`, `3.6957` at `0.9999`). So the
refutation is not an artefact of a mis-measured extremal — the same code
reproduces Conjecture P's own equality case to four digits.

**The limit is `2 pi`, and the mechanism is elementary.** As `n -> oo`,
`|c| = n^{-1/(n-1)} -> 1` and, in the directions between the outer roots, the
boundary radius solves `t(1 + t^{n-1}) = sigma` with `t < 1`, so `t -> sigma -> 1`
as well. The lobe therefore converges to the closed unit disc while
`rho = mu^{1/n} -> 1`, giving

```text
H^1(dC)/rho  ->  2 pi = 6.2831853,      ratio to sqrt(2) varpi  ->  1.6944 .
```

**What this kills, and what it leaves.** Theorem 3 of
[UnconditionalConstantFactorBound.md](UnconditionalConstantFactorBound.md) is
stated conditionally on Conjecture P holding *with some constant `beta`*, and
that conditional form survives: what fails is the value `sqrt(2) varpi` and the
claim that the extremal is a quadratic. The corrected statement is a lower
bound plus an open question:

> **Question P'.** Is `sup H^1(dC)/cap(K_sigma)` over one-root components
> finite? The above shows it is at least `2 pi`, attained in the limit by
> `z^n - z`, not by a quadratic.

The earlier `120`-row sweep reported `max = 3.7081`, "attained only at
quadratics", over five families (uniform in the disc, on a circle, near-Fekete
shells, clustered, near-collinear). None of those families contains **one root
at the centre of a polygon formed by the others**, which is exactly the shape
that makes a one-root lobe fat relative to `cap`. That is the reportable
methodological point: the sweep's family list, not its estimator, was the
binding constraint. (A sibling session's adversarial climb had independently
broken the sharp form at degree three at `1.0127`; the family, the size `1.58`
and the limit `2 pi` are new here.)

**Instrument defect, fourth reproduction of the class at `negative_results`
34/41, new cause, hit twice in this session and both times biasing the same
way.** Locating the lobe boundary by walking outward from the root with a
*geometric* step and stopping at the first `t` with `|f| >= sigma` steps clean
over the crossing when the crossing window is narrow — at `sigma = mu(1-eps)`
that window has width `O(sqrt eps)` — and then lands on a **different lobe**.
In the first run this inflated every radius (reported `5.71` on a quadratic
whose true value is `3.708`); in the second it deflated the perimeter by a
factor of two (reported `2.05` at `n = 3` against the true `3.80`), because the
tracer started on the lobe of the wrong root and the closure gate still passed,
since that lobe is also a genuine one-root component. **General rule: a first
crossing of a non-monotone modulus must be found by a monotone scan, never by a
geometric or adaptive walk; and a closure gate cannot detect starting on the
wrong component.** Both instruments above use a monotone scan.

---

## 2. The normal form at a hub of multiplicity `m`

Throughout, `f` is monic of degree `n >= 2`, and a critical point `c` has
**multiplicity `m >= 2`** when `f - f(c)` vanishes to order exactly `m` at `c`.

> **Hypothesis (H).** `Delta` is a simply connected domain with
> `Delta subset D(0,t)`, `0 in Delta`, `v := f(c) in Delta`, and `Delta`
> contains no critical value of `f` restricted to the component of
> `{|f| < t}` containing `c`, other than `v`. Write
> `q := rho_Delta(0, v)` for the pseudohyperbolic distance in `Delta`, and
> `x := q^{1/m}`.

The simplest admissible choice is `Delta = D(0,s)` for any `s > |v|` below the
next critical-value modulus; then `q = |v|/s`.

> **Lemma 1 (cyclic Blaschke normal form).** Under (H), let `Omega` be the
> connected component of `f^{-1}(Delta)` containing `c`. Then `Omega` is
> simply connected, `f : Omega -> Delta` is proper of degree `m` branched only
> at `c`, and `Omega` contains exactly `m` roots of `f`, all simple. Moreover
> there is a conformal `psi : D -> Omega` with `psi(0) = c` and
>
> ```text
> sigma^{-1}( f(psi(zeta)) )  =  (zeta^m - x^m) / (1 - x^m zeta^m) ,
> ```
>
> where `sigma : D -> Delta` is the conformal map with `sigma(0) = 0`, after a
> rotation of `zeta` and of `sigma`. The `m` roots of `f` in `Omega` are
> `psi(x omega^j)`, `omega = e^{2 pi i/m}`, `j = 0, ..., m-1`; in particular
> they are equidistant from `c` in the hyperbolic metric of `Omega`, at
> pseudohyperbolic distance exactly `x = q^{1/m}`.

*Proof.* `f : Omega -> Delta` is proper (the preimage of a compact subset of
`Delta` is compact in `Omega`), hence a branched cover, of some degree `d`.

**The step that needs an argument, and where it is:** (H) says only that `v` is
the only critical *value* in `Delta`; it does not say that `c` is the only
critical *point* over `v`. It is: the unbranched cover
`Omega \ f^{-1}(v) -> Delta \ {v}` of a punctured disc has monodromy generated
by a single permutation, whose cycle lengths are the local degrees over `v`;
connectedness makes that generator transitive, hence a single full cycle, hence
there is exactly one point of `Omega` over `v` and its local degree is `d`. A
concurrent session in this directory supplied that step in full, with its finite
algebraic core Lean-checked, in
[DegenerateHubUniqueBranchRepair.md](DegenerateHubUniqueBranchRepair.md) and
[DegenerateHubMonodromyKernel.lean](DegenerateHubMonodromyKernel.lean); the
statement is used here, not reproved. So the only branch point is `c`, of local
degree `m`, and `d = m` follows either from that cycle length directly or from
the count below. Riemann–Hurwitz gives
`chi(Omega) = d - (m-1)`. `Omega` is a planar domain so `chi(Omega) <= 1`,
whence `d <= m`; and `d >= m` because `c` alone has `m` preimage sheets. So
`d = m` and `chi(Omega) = 1`: `Omega` is simply connected, and the `d = m`
preimages of `0 in Delta` are `m` simple roots of `f`.

Now transport by uniformisers `psi : D -> Omega`, `sigma : D -> Delta`, with
`psi(0) = c` and `sigma(0) = 0`. Then `B := sigma^{-1} o f o psi : D -> D` is
proper of degree `m`, i.e. a Blaschke product, branched only over `B(0)`. Hence
`D \ B^{-1}(B(0)) -> D \ {B(0)}` is an **unbranched** degree-`m` covering of a
punctured disc; its monodromy group is generated by a single permutation, so it
acts transitively only if that permutation is an `m`-cycle. The total space is
connected, so the covering is the cyclic one, and its deck group is `Z/m`
acting on `D` by conformal automorphisms with the fixed point `0`, i.e. by
`zeta -> omega zeta` after a rotation. Therefore `B(omega zeta) = B(zeta)`, so
`B(zeta) = b(zeta^m)` with `b` a degree-one Blaschke product, that is a Möbius
automorphism of `D`. Writing `b(w) = e^{i alpha}(w - x^m)/(1 - x^m w)` and
absorbing `e^{i alpha}` into `sigma` gives the displayed form; the zeros of `B`
are `x omega^j`. Finally `|B(0)| = x^m` and, on the other hand,
`|B(0)| = |sigma^{-1}(f(c))| = |sigma^{-1}(v)| = rho_Delta(0,v) = q`, so
`x = q^{1/m}`. ∎

The `m`-fold symmetry is not an assumption on `f`. It is forced by the single
branch point, and it is exactly the structure that Proposition S of
[BergmanGeodesicInvariance.md](BergmanGeodesicInvariance.md) had to take from
the symmetry of `z^n - r^n`.

---

## 3. The min-area adjacent sector

> **Lemma 2.** With `psi` and the roots `a_j = psi(x omega^j)` of Lemma 1, let
> `S_j = psi({ zeta in D : arg zeta in ((2j-1) pi/m, (2j+1) pi/m) })` be the `m`
> open sectors cut by the rays bisecting consecutive roots, and `A_j = Area(S_j)`.
> Then `sum_j A_j = Area(Omega)`, and for some `j`
>
> ```text
> Area( Omega_j )  <=  2 Area(Omega) / m ,
> ```
>
> where `Omega_j` is the interior of `closure(S_j) union closure(S_{j+1})`.
> Each `Omega_j` is the `psi`-image of a disc sector of opening `4 pi/m`, is
> simply connected, and contains exactly the two roots `a_j`, `a_{j+1}`.

*Proof.* `psi` is a conformal bijection, so the `m` sectors are disjoint with
union `Omega` minus `m` radii, giving `sum_j A_j = Area(Omega)`. Cyclically,
`sum_{j=1}^{m} (A_j + A_{j+1}) = 2 Area(Omega)`, and a minimum over `m` terms
is at most their mean. ∎

That one line is the whole replacement for symmetry: no hypothesis on `f`
beyond (H) is used, and for `f = z^n - r^n` it returns the exact `2/n` that
Proposition S obtains from the `n`-fold symmetry.

---

## 4. The bound and its threshold

Recall Theorem C′ of [BergmanGeodesicInvariance.md](BergmanGeodesicInvariance.md):
for `Omega'` simply connected of finite area and `a != b` in `Omega'`, the
hyperbolic geodesic of `Omega'` from `a` to `b` has

```text
length^2  <=  ( Area(Omega') / pi ) * log( 1 / (1 - rho_{Omega'}(a,b)^2) ) .
```

> **Theorem 3.** Under (H), with `x = q^{1/m}` and `delta = 2 pi/m`, two roots
> of `f` in `Omega` are joined by a path **inside `Omega`** of length at most
> `min(B_full, B_sect)`, where
>
> ```text
> B_full^2  =  ( Area(Omega) / pi ) * log( |1 - x^2 e^{i delta}|^2 / (1 - x^2)^2 ) ,
> B_sect^2  =  ( 2 Area(Omega) / (m pi) ) * log( 1 / (1 - rho_m(x)^2) ) ,
> ```
>
> and `rho_m(x)` is the pseudohyperbolic distance, inside the disc sector of
> opening `4 pi/m`, between the two points of modulus `x` at angles `± pi/m`
> from its axis. For `m = 2` the two coincide.

*Proof.* `B_full`: apply Theorem C′ to `Omega` with the adjacent pair
`a_j, a_{j+1}`. By Lemma 1 and conformal invariance,
`rho_Omega(a_j, a_{j+1}) = rho_D(x, x e^{i delta})`, and

```text
1 - rho_D(x, x e^{i delta})^2
   = ( |1 - x^2 e^{i delta}|^2 - x^2 |1 - e^{i delta}|^2 ) / |1 - x^2 e^{i delta}|^2
   = (1 - x^2)^2 / |1 - x^2 e^{i delta}|^2 ,
```

since `(1 - 2x^2 cos delta + x^4) - x^2(2 - 2 cos delta) = (1-x^2)^2`.

`B_sect`: apply Theorem C′ to the subdomain `Omega_j` of Lemma 2 — legitimate
because Theorem C′ has no hypothesis tying its domain to `f` — using
`Area(Omega_j) <= 2 Area(Omega)/m` and `rho_{Omega_j}(a_j, a_{j+1}) = rho_m(x)`,
again by conformal invariance. Both geodesics lie in `Omega`. ∎

> **Corollary 4.** `Area(Omega) <= pi cap(Omega)^2 <= pi t^{2/n}`, so conjecture
> (C) holds for `Omega` — and **Erdős #1041 holds for `f` whenever `t <= 1`** —
> as soon as `q <= Q(m)`, where
>
> ```text
> Q(m) = max( Q_full(m), Q_sect(m) ) ,
> Q_full(m) = x^m  with  x  maximal subject to  |1-x^2 e^{i delta}|^2/(1-x^2)^2 <= e^4 ,
> Q_sect(m) = x^m  with  x  maximal subject to  1 - rho_m(x)^2 >= e^{-2m} .
> ```

Computed (50-digit-stable up to `m = 16`; `Q_sect` saturates in double
precision beyond that, exactly as Proposition S's row does):

| `m` | 2 | 3 | 4 | 5 | 6 | 8 | 10 | 12 | 16 |
|---|---|---|---|---|---|---|---|---|---|
| `Q_full` | `0.7615942` | `0.7018372` | `0.6799458` | `0.6696476` | `0.6640101` | `0.6583743` | `0.6557556` | `0.6543304` | `0.6529114` |
| `Q_sect` | `=Q_full` | `0.8190903` | `0.9293377` | `0.9734072` | `0.9901339` | `0.9986590` | `0.9998184` | `0.9999754` | `0.9999995` |
| `Q` | `0.7615942` | `0.8190903` | `0.9293377` | `0.9734072` | `0.9901339` | `0.9986590` | `0.9998184` | `0.9999754` | `0.9999995` |

Three exact facts pin this table.

* **`Q_full(2) = tanh 1 = 0.7615941559…`, exactly Theorem E.** At `m = 2`,
  `delta = pi` and the criterion is `((1+q)/(1-q))^2 <= e^4`, i.e.
  `t/|v| >= coth 1 = 1.3130352855`. So Theorem 3 *contains* Theorem E, and
  reproves it from the deck-group normal form rather than from `(B2)` of
  [AffineNormalisedModuli.md](AffineNormalisedModuli.md). That is the check
  that the derivation is not drifting.
* **`Q_full(m)` decreases monotonically to a closed form.** With `y = x^2`,
  the criterion reads `y delta^2 <= (e^4-1)(1-y)^2 + O((1-y)^3)`, so
  `1-y ~ delta/sqrt(e^4-1)` and

  ```text
  lim_{m->oo} Q_full(m) = exp( - pi / sqrt(e^4 - 1) ) = 0.6510842287 .
  ```

* **`Q_sect(m) = (1 - e^{-m})^4 (1 + o(1))`, hence `1 - Q(m) = O(e^{-m})`.**
  In the sector of opening `4 pi/m`, `1 - rho_m(x)^2 = eps^2 + O(eps^3)` with
  `eps = 1 - x^{m/4}` (the constant is exactly one, by the identity
  `32 a^2 = (a^2-1)^2` at `a = cot^2(pi/8)` recorded in Proposition S), so the
  criterion is `1 - q^{1/4} >= e^{-m}`. The measured `Q_sect` agrees with
  `(1-e^{-m})^4` to eight digits from `m = 4` on.

**Reach, stated plainly.** For a hub of multiplicity `m >= 3` the criterion
`q <= Q(m)` already beats the `mu <= 1/2` proviso of Corollary 2 of
[UnconditionalConstantFactorBound.md](UnconditionalConstantFactorBound.md) at
the first degenerate degree (`0.819 > 0.5`), and from `m = 6` it leaves only an
exponentially thin window. Applied to `f = z^n - r^n` at `t = 1` — where `0` is
the unique critical point, of multiplicity `m = n`, and `q = r^n` — it settles
Erdős #1041 for every `r` with `1 - r > c n^{-1} e^{-n}`, recovering the shape
of Proposition S's row from a general theorem instead of a closed-form
uniformiser.

### 4b. Cross-validation against the published closed form

The strongest check available: `BergmanGeodesicInvariance.md` §6 publishes a
"two basins" row for `f = z^n - r^n` at `t = 1`, computed **at 50 digits from
the explicit uniformiser** `Phi(z)^n = sigma(z^n)` of Proposition S — i.e. from
the `n`-fold symmetry of that one family. Theorem 3's sector form, which knows
nothing about that symmetry, must reproduce it, with `m = n`, `q = r^n`,
`x = q^{1/m} = r`, and `Area(Omega)` from the closed form
`Area = (1/2) int_0^{2pi} (r^n cos th + sqrt(1 - r^{2n} sin^2 th))^{2/n} dth`.

| `r` | `n` | `Area(Omega)` | `B_sect` (Theorem 3) | published | rel. err |
|---|---|---|---|---|---|
| `0.90` | 3 | `2.693925` | `1.7052` | `1.705` | `1.3e-4` |
| `0.90` | 4 | `2.840628` | `1.4294` | `1.429` | `2.5e-4` |
| `0.90` | 5 | `2.938687` | `1.2360` | `1.236` | `2.6e-6` |
| `0.90` | 6 | `3.002372` | `1.0902` | `1.090` | `1.4e-4` |
| `0.90` | 8 | `3.072464` | `0.8826` | `0.883` | `4.7e-4` |
| `0.90` | 10 | `3.105285` | `0.7410` | `0.741` | `6.4e-5` |
| `0.90` | 12 | `3.121744` | `0.6380` | `0.638` | `6.1e-5` |
| `0.99` | 3 | `2.058661` | `2.0666` | `2.067` | `2.2e-4` |
| `0.99` | 4 | `2.167603` | `1.7816` | `1.782` | `2.4e-4` |
| `0.99` | 5 | `2.295658` | `1.5996` | `1.600` | `2.3e-4` |
| `0.99` | 6 | `2.411854` | `1.4653` | `1.465` | `1.8e-4` |
| `0.99` | 8 | `2.592655` | `1.2698` | `1.270` | `1.9e-4` |
| `0.99` | 10 | `2.717871` | `1.1292` | `1.129` | `1.3e-4` |
| `0.99` | 12 | `2.806149` | `1.0212` | `1.021` | `1.6e-4` |

**Worst relative discrepancy `4.7e-4` over all fourteen rows**, which is the
published table's own rounding. Proposition S is therefore exactly the
`f = z^n - r^n` instance of Theorem 3, and Lemma 2 is the general replacement
for the symmetry step it uses.

Note what the table shows about the *area* input: at `r = 0.99`, `n = 3` the
bound is `2.0666`, only `4%` above the true geodesic `2r = 1.98`. The `a priori`
substitution `Area(Omega) <= pi t^{2/n}` used in Corollary 4 is therefore the
only loose step in the chain; with the actual area the criterion is far
stronger, and it is computable for any given `f`.

### 4c. A form usable without any conformal map

> **Corollary 5.** Let `f` be monic of degree `n >= 2` with all roots in the
> open unit disc and no repeated root. Let `mu_1 < mu_2` be the two smallest
> **distinct** critical-value moduli of `f` (`mu_2 = +oo` if `f'` has a single
> zero set), `m` the multiplicity of a critical point attaining `mu_1`,
> `t = min(1, mu_2)` and `q = mu_1/t`. If `q <= Q(m)` then Erdős #1041 holds
> for `f`.

*Proof.* Every critical point other than the chosen one has critical-value
modulus `>= mu_2 >= t`, hence lies outside `{|f| < t}`; so the component of
`{|f| < t}` containing `c` satisfies (H) with `Delta = D(0,t)` and
`rho_Delta(0, f(c)) = mu_1/t = q`. Apply Corollary 4; `t <= 1` puts the path
inside `{|f| < 1}` and its length is at most `2 t^{1/n} <= 2`, strictly when
`q < Q(m)`. ∎

**Reach, measured.** Corollary 5 on `900` configurations, six families,
degrees `3, 4, 5, 6, 8` (`30` each):

| family | `n=3` | 4 | 5 | 6 | 8 |
|---|---|---|---|---|---|
| uniform in the disc | `26/30` | `25/30` | `18/30` | `19/30` | `23/30` |
| on a circle | `24/30` | `23/30` | `26/30` | `29/30` | `25/30` |
| near-Fekete | `0/30` | `0/30` | `0/30` | `0/30` | `0/30` |
| clustered | `28/30` | `25/30` | `26/30` | `24/30` | `22/30` |
| near-collinear | `24/30` | `29/30` | `26/30` | `27/30` | `25/30` |
| centre + polygon | `0/30` | `0/30` | `0/30` | `0/30` | `0/30` |

`494/900` fired. Two families are vacuous and for different reasons, both
instructive. **Near-Fekete**: `mu_1/mu_2 -> 1`, the universal obstruction.
**Centre + polygon**: the `n-1` hubs are simple but their critical values all
have the *same modulus*, so `mu_2 = mu_1` and Corollary 5's disc `Delta` is
unavailable — this is a **critical-value tie**, not a near-Fekete failure, and
it is exactly the case the general `Delta` of hypothesis (H) is for: the other
critical values there are separated in *argument*, so a slit `Delta` has
`rho_Delta(0,v)` bounded away from `1`. (That `Delta` is not evaluated here;
`#1041` is trivially true on that family by the straight spoke `[0, a_j]`, so it
is not a hard case, only a vacuous one for the simple criterion.)

For comparison, Theorem V of `BergmanGeodesicInvariance.md` §6b fires on
`112/150` of its own six-family sweep with the *actual* component area, and
also dies on near-Fekete. Corollary 5 is not a strict improvement in raw reach;
what it adds is the degenerate stratum and an explicitly computable criterion
with no conformal map in it.

---

## 5. What this does not settle

* **It is a statement about the degenerate stratum.** Hypothesis (H) asks the
  merge component to have a *single* critical value. Generic `f` has `n-1`
  simple, distinct critical values, and then `m = 2` and Theorem 3 collapses to
  Theorem E. The gain is real but it is on a set of positive codimension —
  which is nonetheless exactly where the conjectured extremal family, and every
  witness on which the `k = 2` machinery was previously silent, actually lives.
* **It is not stable under perturbation.** A hub of multiplicity `m` splits
  into `m-1` simple hubs with critical values within `O(rho_crit^n)` of each
  other, and then any admissible `Delta` must exclude `m-2` points that sit at
  distance `O(rho_crit^n)` from `v`, forcing `rho_Delta(0,v) -> 1`. So
  Theorem 3 does **not** by itself quantify the neighbourhood that
  [BergmanGeodesicInvariance.md](BergmanGeodesicInvariance.md) §6 leaves
  unquantified. Recording this as a limit, not as a route.
* **One step is borrowed.** Lemma 1's unique-branch-point step is proved in
  [DegenerateHubUniqueBranchRepair.md](DegenerateHubUniqueBranchRepair.md) by a
  concurrent session, not here. The rest of Lemma 1, Lemma 2, Theorem 3 and
  Corollaries 4–5 are self-contained.
* **The near-Fekete shell is untouched**, as it is by every other criterion in
  this directory.
* `Q_sect` beyond `m = 16` is reported at double precision and saturates near
  `1 - 5e-8`; the true values continue to `1 - 4e^{-m}`. Not re-run at 50
  digits here.

### 5b. Where the wall is, quantified — and the two obstructions coincide

Everything below is closed form on the perturbed extremal family

```text
f(z) = z^n + eps e^{i phi} z - m0 ,        m0 = R^n ,
```

and is checked against `numpy` to `1.1e-16` by gate G6 of the probe.
`f' = 0` gives `z^{n-1} = -eps e^{i phi}/n`, so the hubs form a regular
`(n-1)`-gon of radius `rho_c = (eps/n)^{1/(n-1)}`; and
`f(c) = -m0 + (n-1) rho_c^n * (e^{i phi} c/rho_c)`, where the `n-1` numbers
`e^{i phi} c/rho_c` are the `(n-1)`-th roots of `-e^{i n phi}`. Hence:

> **The critical VALUES are the vertices of a regular `(n-1)`-gon of radius
> `s = (n-1) rho_c^n` centred at `-m0`, rotated by `phi`.**

Two consequences, and one that was not expected.

* **The level deficit is the `n`-th power of the cusp radius.** The smallest
  critical-value modulus is `mu_1 = |{-m0} + s eta_max|`, so
  `1 - mu_1/m0 ≍ (n-1) rho_c^n/m0`. The cusp law's small parameter is therefore
  the `n`-th **root** of the level deficit — which is why its margin
  `kappa_n rho_c` is so much larger than the deficit, and equally why its regime
  `rho_c <= rho_0` is `1 - mu_1/m0 <= (n-1) rho_0^n/m0`: **exponentially thin in
  the degree.** Measured at `rho_0 = 0.3`: `5.4e-2` at `n = 3`, `9.7e-3` at
  `n = 5`, `4.6e-4` at `n = 8`, `5.8e-6` at `n = 12`.

* **The two obstructions coincide.** At `phi = 0` — which
  [NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) §3 records as the direction
  **minimising `kappa_n`**, i.e. the worst direction for the cusp law — the gon
  is symmetric about the real axis, so **the two smallest critical-value moduli
  are an exactly equal conjugate pair**: `mu_1 = mu_2` at every `eps`
  (verified to `0.0e+00` at `n = 3,4,5,6,8`). Corollary 5, and Theorem E with
  it, are then vacuous for every `eps`, because there is no admissible disc
  `Delta`. The direction that is worst for the cusp law is exactly the
  critical-value-tie direction. Separation is maximal at `phi = pi/n`, where a
  vertex points at `+1`; even there `mu_1/mu_2` is only `0.933` (`n=3`) to
  `0.955` (`n=8`) at `eps = 0.2`, still far above `tanh 1 = 0.7616`.

* **The uncovered band widens with the degree.** With `phi = pi/n` (the best
  case for Corollary 5):

| `n` | 3 | 4 | 5 | 6 | 8 | 10 | 12 |
|---|---|---|---|---|---|---|---|
| `eps*` — least `eps` at which Corollary 5 fires | `0.498` | `0.459` | `0.491` | `0.535` | `0.618` | `0.684` | `0.734` |
| `eps` giving `rho_c = 0.3` (cusp side) | `0.27` | `0.108` | `0.0405` | `0.0146` | `1.75e-3` | `1.97e-4` | `2.13e-5` |

  At `n = 3` the two sides nearly touch, consistent with degree three being
  settled; by `n = 12` the band is `(2.1e-5, 0.734)` — essentially everything.
  **The cusp law's reach shrinks like `rho_0^{n-1}` while the capacity
  criteria's threshold stays of order one.** That is the obstruction, in one
  line.

*Claim boundary.* `rho_0` stands in for the cusp expansion's unquantified radius
of validity; it is not a proved threshold. The family is one two-parameter slice
(`eps`, `phi`), not every near-Fekete `f`. Offered as a map of where to aim.

---

## 6. A concyclic reduction, and the elementary inequality it turns on

The wall above is about hubs. There is a completely different and much more
elementary route when the roots are **concyclic**, and it is worth recording
because the measurement says it is nearly tight.

Let the roots lie on the circle of radius `R < 1` about the origin,
`a_j = R w_j` with `|w_j| = 1`, and let `g(u) = prod_k (u - w_j)`. Then
`|f(z)| = R^n |g(z/R)|`, and `|f(0)| = R^n < 1`, so **the origin always lies in
`{|f| < 1}`**. The spoke `[0, a_j]` has length `R`, so any two spokes give a
path between two roots of length exactly `2R < 2`. Everything therefore reduces
to containment:

> **Proposition 6.** With `S_j := max_{t in [0,1]} log prod_k |t w_j - w_k|`
> (so `S_j >= 0`, with `S_j = 0` exactly when `|g| <= 1` on the whole spoke),
> the segment `[0, a_j]` lies in `{|f| < 1}` if and only if
> `S_j < n log(1/R)`. Hence if the **second-smallest** `S_j`, written
> `Lambda(w)`, satisfies `Lambda(w) < n log(1/R)`, then Erdős #1041 holds for
> `f`, by the two straight spokes through the origin.

*Proof.* `log|f(t R w_j)| = n log R + log|g(t w_j)|`, and the spoke is
`{tRw_j : t in [0,1]}`. ∎

`Lambda = 0` for the `n`-th roots of unity, where `|g(tw_j)| = 1 - t^n <= 1` on
every spoke. `TwoSegmentLevelIdentity.md` records that **ONE-SPOKE is false** at
`n = 5` — `min_j S_j > 0` is possible — which is exactly why `Lambda > 0` at
`R = 1`. What was not recorded is **how big** `Lambda` gets, and that is the
whole content:

| `n` | 3 | 4 | 5 | 6 | 8 |
|---|---|---|---|---|---|
| `sup Lambda`, hill-climbed over three families | `9.77e-3` | `0` (not found) | `2.19e-3` | `1.00e-3` | `1.22e-3` |
| implied `1 - R` sufficient for #1041 | `3.3e-3` | — | `4.4e-4` | `1.7e-4` | `1.5e-4` |

The maximiser sits close to the equally spaced configuration (at `n = 3` the
witness is `angles/2pi = 0.00366, 0.299, 0.70834`), which is the expected shape:
`Lambda ≍ eta^{n/(n-1)}` for an angular perturbation `eta`, so it vanishes at
Fekete, grows, and then collapses again once the points cluster.

> **Question (TWO-SPOKE).** Is `sup Lambda` over all `n` and all configurations
> on the unit circle bounded by a small absolute constant? Measurement says
> `<= 0.01`; nothing here proves it.

An affirmative answer with constant `c` settles Erdős #1041 for **every**
concyclic configuration with `1 - R > c/n`, by two straight segments — a
completely elementary path, on the family that carries the conjectured
extremal. Note the complementarity with everything else in this directory: this
route is **strongest exactly where the capacity criteria are weakest**, at and
near Fekete, where `Lambda -> 0`.

*Claim boundary.* `sup Lambda` is a hill-climbed basin record over three
families, not a supremum — `negative_results` 19 applies in full. Proposition 6
is proved; the table is measurement; the Question is open.

## 7. Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_degenerate_hub_reduction.py
```

## 8. Claim boundary

Lemma 1, Lemma 2, Theorem 3 and Corollary 4 are proved above by ordinary
mathematics; no computation enters their proofs. The threshold table and the
two closed forms in §4 are numerical solutions of the explicit inequalities
they state. Proposition 6 is proved; the `Lambda` table and the `sup Lambda` row are
measurement, and are hill-climbed basin records, not suprema.
§1 is a refutation by explicit example: the family is closed form,
the two instruments are independent, and the estimator is validated against the
exact Bernoulli half-loop on Conjecture P's own equality case. Erdős #1041 is
open; no literature priority is claimed for anything above.
