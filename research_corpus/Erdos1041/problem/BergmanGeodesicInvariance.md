# Erdős 1041: the Bergman segment functional is a Möbius invariant, so the sharp bound is a *geodesic* bound

Status: one invariance lemma, one sharp theorem with its equality family, two
exact potential-theoretic identities, one explicit criterion, one exact
subdomain computation on the degenerate stratum, and a new member of the
instrument-defect class. 2026-08-24. **Erdős #1041 remains open** and nothing
below claims otherwise.

## 0. What was missing

[BergmanSegmentLengthBound.md](BergmanSegmentLengthBound.md) proves Lemma A for
a **diameter** of the disk, hence Theorem C only for a component holding
**exactly two** roots, where antipodality forces the descent arc to be the image
of a diameter. Its §3 names the obstruction:

> This has no hypothesis on the number of roots — but it is only useful when
> `d_hyp,Omega(a,b)` can be bounded, and for a `k`-root component that is
> exactly what is missing: writing `B` for the degree-`k` Blaschke product and
> `zeta_j` for its zeros, `prod_j rho(zeta_c, zeta_j) = |f(c)|/t` bounds the
> **smallest** pseudohyperbolic distance and says nothing about the second.

Its §6 records that the whole machinery is **silent by construction on the
extremal family** `z^n - r^n`, because no level there ever gives a two-root
component.

Three things happen here.

* The functional `Lambda(gamma)` behind Lemma A is **conformally invariant**, so
  the sharp constant transfers verbatim from the diameter to *every hyperbolic
  geodesic* (§1–2). Theorem C is the `k = 2` case.
* The missing pseudohyperbolic bound is supplied by an exact Green identity
  **centred at a root rather than at the critical point** (§3), which bounds the
  distance between two *roots*, not merely the distance from the hub. A Gram
  inequality sharpens the constant by a factor `sqrt(k)` (§4).
* Theorem C′ has **no hypothesis tying its domain to `f`**, so it may be applied
  to any simply connected subdomain of `{|f| < 1}` carrying two roots. The
  canonical `f`-determined choice is the union of two adjacent Newton basins,
  and on the extremal family that subdomain is **exactly a disk sector** in the
  uniformiser (§5) — so its bound is closed form, and it settles that family for
  every `r` up to `1 - Theta(n^{-1} e^{-2n})` (§6), where Theorem C settles
  nothing at all.

---

## 1. `Lambda` is a Möbius invariant

Write `K(z,w) = 1/(pi (1 - z conj(w))^2)` for the Bergman kernel of `D` and, for
a rectifiable `gamma subset D`,

```text
Lambda(gamma)  =  int_gamma int_gamma  |dz| |dz'| / ( pi |1 - conj(z') z|^2 ) .
```

`BergmanSegmentLengthBound.md` Lemma A/B gives, for `h in A^2(D)`,

```text
( int_gamma |h| |dz| )^2   <=   Lambda(gamma) * ||h||^2 ,          (A)
```

with equality on the diameter `[-q,q]` for `h = (1-q^2z^2)^{-1}`, and
`Lambda([-q,q]) = (2/pi) log((1+q^2)/(1-q^2))`.

> **Lemma A′.** For every `sigma in Aut(D)` and every rectifiable `gamma`,
> `Lambda(sigma(gamma)) = Lambda(gamma)`.

*Proof.* Let `sigma(z) = e^{i theta}(z-alpha)/(1-conj(alpha) z)`. Clearing
denominators,

```text
(1 - alpha conj(z'))(1 - conj(alpha) z) - (conj(z') - conj(alpha))(z - alpha)
      = (1 - |alpha|^2)(1 - conj(z') z) ,
```

so

```text
1 - conj(sigma(z')) sigma(z)
      = (1-|alpha|^2) (1 - conj(z') z) / ( (1 - alpha conj(z'))(1 - conj(alpha) z) ) .
```

Since `|sigma'(z)| = (1-|alpha|^2)/|1-conj(alpha)z|^2`, taking moduli squared
gives the **exact** identity

```text
|1 - conj(sigma(z')) sigma(z)|^2  =  |sigma'(z)| |sigma'(z')| |1 - conj(z') z|^2 ,
```

whose two Jacobian factors cancel against `|d sigma(z)| = |sigma'(z)||dz|` in
the numerator. ∎

> **Corollary A″.** If `gamma` is the hyperbolic geodesic of `D` joining two
> points at pseudohyperbolic distance `rho`, then
> `Lambda(gamma) = (1/pi) log( 1/(1-rho^2) )`.

*Proof.* A Möbius map carries `gamma` to the diameter `[-q,q]` with
`rho(-q,q) = 2q/(1+q^2) = rho`, hence `(1-q^2)/(1+q^2) = sqrt(1-rho^2)`, and
`(2/pi) log((1+q^2)/(1-q^2)) = (1/pi) log(1/(1-rho^2))`. ∎

So the closed form of Lemma A was never a statement about segments. It is the
statement that `Lambda` of a geodesic is `(1/pi) log(1/(1-rho^2))`; the diameter
is only the normalised representative of its Möbius class.

---

## 2. Theorem C′ — the sharp geodesic bound

> **Theorem C′.** Let `Omega subset C` be simply connected with finite area and
> let `a != b` in `Omega`. Let `gamma*` be the hyperbolic geodesic of `Omega`
> from `a` to `b` and `rho = rho_Omega(a,b)` the pseudohyperbolic distance. Then
>
> ```text
> length(gamma*)^2   <=   ( Area(Omega) / pi ) * log( 1 / (1 - rho^2) ) .
> ```
>
> Equality holds, for every `q in (0,1)`, for `Omega = psi_q(D)`,
> `psi_q(z) = (1/(2q)) log((1+qz)/(1-qz))`, `a = psi_q(-q)`, `b = psi_q(q)`.

*Proof.* Let `psi : D -> Omega` be conformal. Pseudohyperbolic distance and
hyperbolic geodesics are conformal invariants, so `gamma = psi^{-1}(gamma*)` is
the hyperbolic geodesic of `D` between two points at distance `rho`. Apply (A)
to `h = psi'`, with `||psi'||^2_{A^2} = Area(Omega)` and Corollary A″. For
equality: `psi_q` is univalent (its image sits in a half plane before the
logarithm), `psi_q' = (1-q^2z^2)^{-1}` is the extremal of Lemma A, and
`psi_q(-z) = -psi_q(z)` makes the diameter the hyperbolic geodesic. ∎

**Theorem C is the `k = 2` case, verbatim.** If `Omega` is a component of
`{|f| < t}` holding exactly two roots `a,b`, Riemann–Hurwitz gives one branch
point — the hub `c` — and `(B2)` of `AffineNormalisedModuli.md` puts the two
Blaschke zeros at `±q`, `q^2 = v/t`, `v = |f(c)|`. Then the geodesic **is** the
descent arc pair, `1-rho^2 = ((t-v)/(t+v))^2`, and Theorem C′ reads

```text
L(c)^2  <=  ( 2 Area(Omega) / pi ) * log( (t+v)/(t-v) ) .
```

The threshold `log(1/(1-rho^2)) <= 4` is `t/v >= coth(1) = 1.3130352854993313`,
Theorem E's constant, recovered exactly (arm `SPEC`).

**Checked numerically** (arms `MOEB`, `GEOD`, `SHARP`): `Lambda` is
Möbius-invariant to `1e-9` over random automorphisms at `q = 0.3, 0.7, 0.95`;
the two closed forms agree to `1e-15`; and Theorem C′ is attained to `3e-7` on
its equality family at `q = 0.3, 0.6, 0.9`.

---

## 3. The root-centred Green identity

> **Lemma G.** Let `f` be monic of degree `n`, `t > 0`, and `Omega` a connected
> component of `{|f| < t}` containing the roots `a_1, ..., a_k` of `f` counted
> with multiplicity. Then `Omega` is simply connected, `∂Omega subset {|f| = t}`,
> and for every `z in Omega`
>
> ```text
> sum_{j=1}^{k} g_Omega(z, a_j)  =  log( t / |f(z)| ) .
> ```

*Proof.* A bounded complementary component `H` would have `|f| = t` on `∂H`,
hence `|f| <= t` on `H` by the maximum principle, so `H` could not be a hole:
`Omega` is simply connected. Both sides are harmonic on `Omega minus {a_j}` with
the same logarithmic poles and extend continuously by zero to `∂Omega` (a
lemniscate component's boundary is a finite union of analytic arcs, so every
boundary point is regular). Their difference is harmonic, bounded, and zero on
the boundary. ∎

For simply connected `Omega`, `g_Omega(z,a) = log(1/rho_Omega(z,a))`. Expanding
Lemma G as `z -> a_i` for a **simple** root, with
`g_Omega(z,a_i) = -log|z-a_i| + log r_Omega(a_i) + o(1)` (`r_Omega` = conformal
radius) and `log(t/|f(z)|) = log t - log|f'(a_i)| - log|z-a_i| + o(1)`:

> **Corollary G′ (root-centred product identity).**
>
> ```text
> prod_{j != i}  rho_Omega(a_i, a_j)   =   r_Omega(a_i) |f'(a_i)| / t   =:  P_i  <  1 .
> ```

This is the object §3 of `BergmanSegmentLengthBound.md` asks for. The identity
recorded there, `prod_j rho(zeta_c, zeta_j) = |f(c)|/t`, is centred at the
**critical point** and controls only the hub's nearest root; a sum of `k`
nonnegative terms bounds one of them and says nothing about the second.
Corollary G′ is centred at a **root**, so it controls the distance between two
**roots**, which is what a geodesic between roots needs:

```text
min_{j != i} rho_Omega(a_i,a_j)  <=  P_i^{1/(k-1)} .
```

Checked to `1e-12` against the closed forms of §5 (arm `GREEN`).

> **Theorem F.** Let `Omega` be a component of `{|f| < t}` holding exactly
> `k >= 2` roots and let `a_i in Omega` be a simple root with `P_i^{2/(k-1)} < 1`.
> Then some other root `b in Omega` is joined to `a_i` **inside `Omega`** by a
> path of length at most
> `sqrt( (Area(Omega)/pi) * log( 1/(1 - P_i^{2/(k-1)}) ) )`.

> **Corollary F′.** If for some `t <= 1`, some component `Omega` of `{|f| < t}`
> and some simple root `a_i in Omega`,
> `(Area(Omega)/pi) log(1/(1-P_i^{2/(k-1)})) < 4`, then Erdős #1041 holds for `f`.

> **Theorem E′.** Under the same hypotheses, Conjecture (C) of
> [CapacityGeodesicConjecture.md](CapacityGeodesicConjecture.md) holds for
> `Omega` whenever `(Area(Omega)/pi) log(1/(1-P_i^{2/(k-1)})) <= 4 t^{2/n}`.
> At `k = 2` this is exactly `t >= coth(1) v`, i.e. Theorem E.

---

## 4. A Gram inequality for the conformal radii

`P_i` contains `r_Omega(a_i)`, so a usable form of Theorem F needs an upper
bound on the conformal radius. The reproducing kernel gives the classical
`r_Omega(a) <= sqrt(Area(Omega)/pi)`, sharp only when `Omega` is a disk centred
at `a` — and a merge component is nothing like one. Using all `k` roots at once
recovers a factor `sqrt(k)`.

Let `zeta_i = psi^{-1}(a_i)`, `k_zeta = K_zeta/||K_zeta||`. Then

```text
G_ij  =  < k_{zeta_j}, k_{zeta_i} >  =  (1-|zeta_i|^2)(1-|zeta_j|^2) / (1 - zeta_i conj(zeta_j))^2 ,
|G_ij| = 1 - rho_ij^2 ,      G_ii = 1 ,
c_i    =  < psi', k_{zeta_i} >  =  sqrt(pi) (1-|zeta_i|^2) psi'(zeta_i) ,   |c_i| = sqrt(pi) r_Omega(a_i) .
```

> **Lemma B′.** `Area(Omega) = ||psi'||^2 >= c* G^{-1} c`, and by Gershgorin
> (`G` Hermitian, unit diagonal),
>
> ```text
> Area(Omega)  >=  pi * sum_i r_Omega(a_i)^2 / (1 + S) ,
> S := max_i sum_{j != i} ( 1 - rho_ij^2 ) .
> ```
>
> Hence `min_i r_Omega(a_i) <= sqrt( Area(Omega) (1+S) / (pi k) )`.

Roots that are hyperbolically far apart make `S` small, which is exactly the
regime where the crude bound is worst. On `z^n - r^n` at level `t = 1`,
`r = 0.9`, `n = 6`: `S = 0.126`, so Lemma B′ gives `r_Omega <= 0.4235` against
the exact `0.2648` — a factor `1.60` — where `sqrt(Area/pi) = 0.9776` is a
factor `3.69` (arm `BESSEL`).

Even so, `P_i` computed through Lemma B′ exceeds `1` on the extremal family, so
**Theorem F's fully explicit form is not where the reach is**; §5–6 use the
domain instead.

---

## 5. The subdomain principle, and an exact two-basin computation

Theorem C′ has no hypothesis tying `Omega` to `f`. So for a fixed pair of roots
`a, b`, **every** simply connected `Omega' subset {|f| < 1}` containing them is
admissible, and the bound may be minimised over that family. This matters
because **`Area` can fall faster than the logarithm grows.**

The canonical `f`-determined choice is the union of two adjacent **Newton
basins**: inside `Omega` the descent flow `z' = -f/f'` decreases `|f|`, so it
partitions `Omega` into the basins of its roots; two basins that merge at a hub
share a separatrix, and the interior of the union of their closures is again
simply connected and contains the hub and the descent arc pair.

> **Proposition S.** For `f = z^n - r^n` and `t > r^n`, the uniformiser `Phi` of
> `Omega_t = {|z^n - r^n| < t}` satisfies `Phi(z)^n = sigma(z^n)` for the Möbius
> `sigma : D(r^n,t) -> D` with `sigma(0) = 0`, and `Phi(omega z) = omega Phi(z)`.
> The Newton basins are the sectors `|arg(z omega^{-k})| < pi/n`, so `Phi` carries
> the two-basin domain `Omega' = Omega_t cap {arg z in (-pi/n, 3pi/n)}` onto the
> **disk sector** `W = { |zeta| < 1, arg zeta in (-pi/n, 3pi/n) }`, with the two
> roots at `R_0` and `R_0 omega`, `R_0 = r t^{-1/n}`. Consequently
>
> ```text
> Area(Omega') = (2/n) Area(Omega_t)   exactly,
> rho_{Omega'}(a_0,a_1) = rho_W(R_0, R_0 omega) ,
> ```
>
> and `rho_W` is elementary: rotate, take the power `n/4` (sector angle `4pi/n`
> to `pi`, i.e. the upper half disk), then upper half disk to disk by
> `u = ((1+w)/(1-w))^2`, `c = (u-i)/(u+i)`.

*Proof.* `Phi(z)^n = sigma(z^n)` is conformal `Omega_t -> D` because `z |-> z^n`
is the `n`-fold cover of `D(r^n,t)` branched at `0 in D(r^n,t)`; near `0`,
`Phi(z) = (sigma'(0))^{1/n} z + ...`, which forces `Phi(omega z) = omega Phi(z)`.
Rotation-equivariance plus the reflection symmetry `Phi(conj z) = conj Phi(z)`
sends each ray `arg z = k pi/n` to `arg zeta = k pi/n`. That the sectors are the
Newton basins is the standard computation: on `arg z = pi/n`, `z^n` is negative
real, so `-f/f' = (|z|^n + r^n)/(n z^{n-1})` has argument `pi/n - pi` and is
tangent to that ray, which is therefore invariant. ∎

**Asymptotics, in closed form.** With `epsilon = 1 - R_0^{n/4}`, the two points
of `W` sit at `arg = pi/4, 3pi/4` in the upper half disk, so `a = cot^2(pi/8)
= 3 + 2 sqrt 2` and a direct expansion gives

```text
1 - rho_W^2  =  ( 32 a^2 / (a^2-1)^2 ) epsilon^2 + O(epsilon^3)  =  epsilon^2 + O(epsilon^3) ,
```

the constant being **exactly** one because `32 a^2 = 544 + 384 sqrt 2 = (a^2-1)^2`.
Hence, at `t = 1`,

```text
log( 1/(1-rho^2) )  =  2 log( 1/(1 - r^{n/4}) ) + O(1) ,
```

and the criterion `bound < 2` becomes, to leading order,

```text
1 - r   >   (4/n) exp( - n pi / A_n ) ,
A_n = 2^{2/n - 1} sqrt(pi) Gamma(1/n + 1/2) / Gamma(1/n + 1)  ->  pi/2 ,
```

i.e. the reach on the extremal family is `1 - r_max(n) = Theta( n^{-1} e^{-2n} )`.

---

## 6. Reach

Everything in this section for `z^n - r^n` is **closed form** (Proposition S
plus one smooth one-dimensional area quadrature), not a grid measurement.

`bound < 2` settles Erdős #1041 for that polynomial.

| `n` | 3 | 4 | 5 | 6 | 8 | 10 | 12 | 20 | 30 |
|---|---|---|---|---|---|---|---|---|---|
| bound, full component, `r = 0.9` | `1.903` | `1.860` | `1.801` | `1.736` | `1.610` | `1.494` | `1.391` | `1.078` | `0.827` |
| bound, two basins, `r = 0.9` | `1.705` | `1.429` | `1.236` | `1.090` | `0.883` | `0.741` | `0.638` | `0.408` | `0.282` |
| bound, two basins, `r = 0.99` | `2.067` | `1.782` | `1.600` | `1.465` | `1.270` | `1.129` | `1.021` | `0.754` | `0.580` |

and the cut-offs `1 - r_max(n)`:

| `n` | 3 | 4 | 5 | 6 | 8 | 9 | 10 | 12 | 16 |
|---|---|---|---|---|---|---|---|---|---|
| full component | `7.3e-2` | `6.7e-2` | `6.1e-2` | `5.4e-2` | `4.4e-2` | — | `3.7e-2` | `3.2e-2` | `2.4e-2` |
| two basins | `1.7e-2` | `1.2e-3` | `1.1e-4` | `1.1e-5` | `1.4e-7` | `1.7e-8` | `2.1e-9` | `3.2e-11` | `8.8e-15` |

The two-basin row is computed in `mpmath` at 50 digits (`rho_W` cancels badly in
double precision near `r = 1`; a float64 run reported spurious cut-offs at the
`1e-15` level from `n = 10` on). Successive ratios are `13.7, 11.1, 9.6, ...,
8.4, 8.2, 8.0`, converging to `e^2 = 7.389` times `n/(n+1)` — the law
`1 - r_max = Theta(n^{-1} e^{-2n})` of §5. Beyond `n = 16` the area quadrature
itself loses double precision and the row is not reported.

**What this is and is not.** `z^n - r^n` is settled in closed form by its own
two radii, so no row above is news about that polynomial. What is new is that
Theorem C′ has **non-empty hypotheses on the degenerate stratum at all**, where
Theorem C has none at any level, and that the criterion is an *open* condition
in the roots, so each firing row settles a neighbourhood of that configuration —
including perturbations for which the two radii are no longer contained. The
size of that neighbourhood is **not** quantified here, so no near-Fekete witness
is claimed.

**On the recorded hard witnesses, Theorem F is vacuous.** At the degree-6 and
degree-9 `QC = infinity` witnesses, the near-Fekete quintic, the degree-3
two-segment witness and `z^3 - (99/100)^3`, `P_i >= 1` at every level tested, so
the criterion says nothing. The one witness it settles is the degree-5
origin-spoke lab (`bound = 0.061` at `t = 0.30`, `k = 2`). Theorem C′ with the
**exact** `rho` is much stronger than Theorem F, but computing that `rho` for a
non-symmetric configuration needs a conformal map, and §7 records why the
obvious instrument cannot supply it.

---

## 6b. Theorem V — a partial proof of (COVER), the other priority-1 producer

The two new identities were built for the descent-arc producer, but together
they hit the **visibility-overlap** producer directly, and there they need no
subdomain and no conformal radius.

`VisibilityOverlapReduction` proves: for monic `g` with roots in the **closed**
unit disk and `mu = min_c |g(c)|`, if for some `lambda in [mu,1]` every point of
a compact connected `Gamma subset Omega_lambda` carrying two roots lies within
intrinsic distance `1` — paths allowed anywhere in `Omega_lambda` — of a root of
`Omega_lambda`, then two roots are joined by a path of length `<= 2` at level
`<= 1`, and the minimum-enclosing-disk normalisation turns that into Erdős
#1041. `research_packet.json` lists (COVER) as an open producer of priority 1
with the note that *no adversarial search against it has run*.

Take `Gamma` = the component of `{|g| <= mu}` containing `c*`. That set is
compact, connected, carries `k' >= 2` roots (the first-merge reduction of that
same file), and satisfies `|g| <= mu` on all of it — no descent arc, no
degenerate-hub caveat.

> **Theorem V.** With `Omega` the component of `{|g| < lambda}` containing `c*`
> and `k` the number of roots of `g` in `Omega` counted with multiplicity, if
>
> ```text
> ( Area(Omega) / pi ) * log( 1 / ( 1 - (mu/lambda)^{2/k} ) )   <=   1
> ```
>
> for some `lambda in (mu, 1]`, then (COVER) holds on `Gamma`, hence two roots of
> `g` are joined inside `Omega` by a path of length at most `2`, and Erdős #1041
> holds for the corresponding `f`.

*Proof.* `Gamma subset {|g| <= mu} subset {|g| < lambda}` is connected and meets
`Omega` at `c*`, so `Gamma subset Omega`. For `h in Gamma`, Lemma G gives
`prod_{j=1}^{k} rho_Omega(h, a_j) = |g(h)|/lambda <= mu/lambda`, so some root
satisfies `rho_Omega(h, a_j) <= (mu/lambda)^{1/k}`. Theorem C′ bounds the
hyperbolic geodesic from `h` to that root, inside `Omega`, by the left-hand side's
square root, which is at most `1`. So `h in S_j` and the `S_j` cover `Gamma`;
apply the lemma. ∎

Every ingredient is explicit: `mu` and `k` are exact, and `Area(Omega)` enters as
a numerator so a bracketed grid area read at its **dilated** end is
conservative. There is no conformal radius and no small Green's function, so §7
does not apply to this criterion.

**Measured.** 150 configurations over degrees `3,4,5,6,8`, level scanned over
15 values in `[0.30, 1]`, area read at its dilated (conservative) end:

| family | `n = 3` | 4 | 5 | 6 | 8 |
|---|---|---|---|---|---|
| uniform in the disk (14 each) | `13` | `14` | `14` | `14` | `14` |
| all roots on the unit circle (8 each) | `7` | `7` | `8` | `8` | `8` |
| near-Fekete, `eps` log-uniform in `[1e-5, 1e-1]` (8 each) | `0` | `1` | `1` | `1` | `2` |

**`112 / 150` proved.** The split is exactly the `D`-split: `69/70` uniform,
`38/40` boundary, `5/40` near-Fekete. On the recorded witnesses it proves
(COVER) for the degree-5 origin-spoke lab (`mu = 0.00477`, score `0.0009`) and
for clustered configurations, and fails on `deg3 two-segment` (`mu = 0.94593`,
score `2.26`), `deg6 QC = infinity` (`mu = 0.99995`, score `2.93`) and the
near-Fekete quintic (`mu = 1`, score `4.41`). Rows reported as "no admissible
level" have `mu = 1` after normalisation — the Fekete stratum, exactly the family
on which `VisibilityOverlapReduction` already proves (COVER) in closed form with
equality. Theorem V and that closed form are complementary, and the gap between
them is again the near-Fekete shell.

**This is the first non-trivial proved case of (COVER).** It does not settle the
producer, and it is a `D`-away-from-`1` result like everything else here.

## 7. Instrument-defect class: a sixth reproduction, with a new cause and a fix

`negative_results` entries 24, 34, 41 and `BergmanSegmentLengthBound.md` §6
record four instruments that under-report a quantity entering a bound as a
numerator, always flattering the conjecture. Here is a fifth location and a
sixth reproduction.

**The defect.** `rho_Omega(a,b) = exp(-g_Omega(a,b))`, and a grid Laplace solve
for `g` places Dirichlet data on cells just *outside* the mask, i.e. it solves
on a slightly larger domain, so `g` comes out too large, `rho` too small, and
the bound too small. In the regime that matters — a component pinched at a
near-degenerate hub, so `rho -> 1` and `g -> 0` — the `O(dx)` boundary error is
the same size as `g` itself. An unguarded run on the recorded witnesses reported

| witness | unguarded bound | guarded |
|---|---|---|
| near-Fekete quintic | `1.681` **"settled"** | `rho` indistinguishable from `1` |
| degree-6 `QC = infinity` | `1.515` **"settled"** | `rho` indistinguishable from `1` |
| degree-9 `QC = infinity` | `1.353` **"settled"** | `rho` indistinguishable from `1` |

Three false settlements, all in the direction of the conjecture, all at the
configurations the corpus calls hardest. The guard is a two-resolution
Richardson extrapolation with the verdict taken at `min(g) - 2 * spread`; it
turns all three into "the instrument cannot decide".

**The fix, and it is the reason Corollary G′ is worth having.** Do not measure
`g` when `g` is small. Corollary G′ replaces the product of the `rho_ij` by
`r_Omega(a_i) |f'(a_i)| / t`, and the conformal radius is `O(1)`, so the same
grid solve delivers it to `O(dx)` **relative** accuracy — and in the
**conservative** direction, since the slightly larger solved domain makes
`r_Omega` too large. Measured against the closed form of Proposition S the grid
`r_Omega` is above the exact value at every tested `(n,r,t)`, by `0.6%` to
`2.6%`, halving as `dx` halves (arm `ROBIN`).

**General rule, extending the class.** When a bound depends on a quantity only
through its logarithm near a degeneracy, do not sample the quantity — find an
identity that expresses it through a non-degenerate one. The two forms are the
same number; only one is measurable.

---

## 8. Claim boundary

**Proved, by ordinary mathematics:** Lemma A′ and its algebraic identity;
Theorem V and its use of the visibility-overlap lemma;
Corollary A″; Theorem C′ with its equality family and the univalence of the
extremal; that Theorem C and its `coth(1)` threshold are the `k = 2` case;
Lemma G; Corollary G′; Theorem F, Corollary F′, Theorem E′; Lemma B′ and its
Gershgorin corollary; Proposition S including the sector uniformisation, the
exact area ratio `2/n`, and the constant `32a^2 = (a^2-1)^2` at `a = 3+2sqrt2`.

**Not first here:** Lemma A and `Area = ||psi'||^2` are
[BergmanSegmentLengthBound.md](BergmanSegmentLengthBound.md); Theorem B and the
degree-two Blaschke normal form are
[AffineNormalisedModuli.md](AffineNormalisedModuli.md); Pólya's area bound is
[LemniscateCapacityBudget.md](LemniscateCapacityBudget.md); the Green's-function
representation of a lemniscate sublevel set, the conformal invariance of the
pseudohyperbolic metric, the Bergman reproducing kernel and the frame/Gram form
of Bessel's inequality are classical. **No novelty is claimed** for Lemma A′,
Theorem C′ or Lemma B′ until a priority search on Bergman-space and
conformal-metric literature says otherwise. What is new here is the *use*.

**Computed, not proved:** the numbers in §6 are exact formulas evaluated
numerically (one smooth periodic quadrature for the area, elementary maps for
`rho`); they are not grid measurements and carry no instrument bias. The
asymptotic law `1 - r_max = Theta(n^{-1} e^{-2n})` is a leading-order expansion,
not a two-sided bound with constants.

**Measured, with the guard of §7:** everything about non-symmetric
configurations. Three previously reported settlements are **retracted inside
this note** as instrument artifacts.

**Erdős #1041 remains open.** Theorem C′ enlarges the proved region and gives
the degenerate stratum a non-empty criterion for the first time, but it switches
off as `r -> 1` at every fixed degree — as it must, since `L = 2r -> 2` there —
and no argument here reaches the near-Fekete shell that
[NearFeketeCuspLaw.md](NearFeketeCuspLaw.md) owns.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_bergman_geodesic.py --part all
```

| arm | what fails it |
|---|---|
| `MOEB` | `Lambda(sigma(gamma)) != Lambda(gamma)` beyond `1e-7` relative, or the diameter closed form is missed |
| `GEOD` | `Lambda` of a geodesic misses `(1/pi) log(1/(1-rho^2))` |
| `SHARP` | Theorem C′ is not attained on `psi_q(D)` to `1e-5` |
| `SPEC` | the `k = 2` specialisation misses Theorem C, or the `coth(1)` edge |
| `GREEN` | `prod_{j!=i} rho = r_Omega(a_i)|f'(a_i)|/t` fails on the closed-form family, or `P_i >= 1` |
| `BESSEL` | the Gram/Gershgorin lower bound for `Area` fails, or `r_Omega` exceeds `sqrt(Area(1+S)/(pi k))` |
| `ROBIN` | the grid conformal radius falls **below** the exact value, or does not converge |
| `SECTOR` | the closed-form two-basin bound disagrees with the independent grid instrument by more than `2%`, is not below the full-component bound, or is not below `2` |
| `LEMMAG` | `prod_j rho_Omega(z,a_j) = |f(z)|/t` fails at a general interior point of the closed-form family |
| `EXTREMAL` | the closed-form reach table for `z^n - r^n` is not reproduced |
| `COVER` | Theorem V does not prove (COVER) at the degree-5 origin-spoke lab or a clustered quartic, does prove it at the degree-3 two-segment witness, or a `mu = 1` row is not the Fekete stratum |

Receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1041_bergman_geodesic_receipt.json`.
