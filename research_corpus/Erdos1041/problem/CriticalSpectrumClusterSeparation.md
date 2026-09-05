# The critical spectrum of the ancestor component: a third, unconditional separation inequality, and the exact reason it is non-binding

## Status

Two new ordinary theorems about finite Blaschke products (Theorem 1), their
unconditional instance on the ancestor component of
[ClusterSeparationLowCriticalClosure.md](ClusterSeparationLowCriticalClosure.md)
(Corollary 2), and an exact proof that neither moves that note's threshold
(Theorem 3, Theorem 4). Not Lean-checked, not independently reviewed. The
constant `9/25` is unchanged and Erdős 1041 remains open.

The pass also produced one measurement that is worth more than the theorems:
the abstract distance profile behind the arity floor `Lambda(k,a)` is **not
realisable by points of the hyperbolic disc**, by a factor of `1.83` at the
attractor arity. That is recorded in §6 as a proof lead with its own guard, not
as a result.

## 1. The unused ingredient

Fix the setting of `ClusterSeparationLowCriticalClosure.md`. Under failure, `c*`
is a least critical point, `Gamma` the union of two descending arcs from `c*`,
`C_t` the component of `{|f| < t}` containing `Gamma` for `t > mu`,
`x = log(t/mu)`, `a(x) = Area(C_t)/pi`, and `k = k(t) >= 2` the root count of
`C_t`. `C_t` is simply connected (`|f|` is subharmonic, so no component of the
complement is bounded), so a Riemann map `phi : D -> C_t` turns `f/t` into a
finite Blaschke product `B = (f/t) o phi` of degree `k` whose zeros
`b_1, ..., b_k` are the roots of `f` in `C_t`.

Riemann–Hurwitz gives `B` exactly `k-1` critical points in `D`, counted with
multiplicity, and they are the images under `phi^{-1}` of the critical points of
`f` in `C_t`. Because `mu` is the **global** minimum of `|f|` over the critical
points of `f`, every one of them satisfies

```text
|B(c)| = |f(phi(c))|/t >= mu/t = e^(-x) =: m.
```

No failure hypothesis is used. This is the ingredient neither the COVER floor
nor the pairwise-separation floor consumes.

## 2. Theorem 1 — critical spectrum controls the zero configuration

Write `rho(z,w) = |z-w|/|1 - conj(w) z|` for the pseudohyperbolic and
`d(z,w) = 2 artanh rho(z,w)` for the hyperbolic metric of `D`.

> **Theorem 1.** Let `B` be a finite Blaschke product of degree `k >= 2` with
> zeros `b_1, ..., b_k` in `D`, and suppose `|B(c)| >= m > 0` at every critical
> point `c` of `B` in `D`. Then
>
> ```text
> (1a)  rho(b_i, b_j) >= 2 sqrt(m)/(1+m),  i.e.  d(b_i,b_j) >= 4 artanh(sqrt m),
>       for every i != j;
> (1b)  prod_{l != j} rho(b_l, b_j) = (1-|b_j|^2)|B'(b_j)| >= m,  for every j.
> ```
>
> (1a) is an equality for `k = 2` and is approached at every `k`; (1b) is
> approached on the regular family `b_j = r omega^j` as `r -> 1`.

*Proof.* Since no critical point of `B` lies in the open set `{|B| < m}`, each
component of `{|B| < m}` is a proper map onto `mD` with no critical points,
hence a conformal bijection of degree one, hence contains exactly one zero.
Write `Omega_j` for the component containing `b_j`; the `Omega_j` are pairwise
disjoint.

*(1a).* Fix `i != j` and factor `B = phi_i phi_j R`, where
`phi_l(z) = (z-b_l)/(1-conj(b_l) z)` and `R` is the Blaschke product carrying
the remaining zeros, so `|R| <= 1` and `|B| <= |g|` with `g = phi_i phi_j`.
Hence `{|g| < m} subset {|B| < m}`. Normalise by an automorphism so that
`b_i = -p`, `b_j = p` with `p = tanh(d(b_i,b_j)/4) in (0,1)`; then
`g(z) = (z^2-p^2)/(1-p^2 z^2)` and `g'(z) = 2z(1-p^4)/(1-p^2z^2)^2`, so `g` has
the single critical point `0` with `|g(0)| = p^2`. If `p^2 < m` then `0` lies in
`{|g| < m}`; that set is a union of components each mapping properly onto `mD`
with total degree `2`, and a component free of critical points has degree one,
so a two-component splitting would put no critical point in the set. Therefore
`{|g| < m}` is connected, and `b_i, b_j` lie in one component of `{|B| < m}` —
contradicting disjointness of `Omega_i, Omega_j`. Hence `p^2 >= m`, i.e.
`d(b_i,b_j) >= 4 artanh(sqrt m)`. Converting, with `sigma = sqrt(1-rho^2)`,
`p^2 = (1-sigma)/(1+sigma)`, so `p^2 >= m` is exactly
`rho >= 2 sqrt m/(1+m)`.

*(1b).* `B` maps `Omega_j` conformally onto `mD` with `b_j |-> 0`. Let
`F : D -> Omega_j subset D` be the inverse of `z |-> B(z)/m`; `F(0) = b_j` and
`F` is a holomorphic self-map of `D`, so Schwarz–Pick gives
`|F'(0)| <= 1-|F(0)|^2`, i.e. `m/|B'(b_j)| <= 1-|b_j|^2`. The identity
`(1-|b_j|^2)|B'(b_j)| = prod_{l != j} rho(b_l,b_j)` is immediate from
`B = prod phi_l` and `phi_j'(b_j) = 1/(1-|b_j|^2)`. ∎

*Sharpness.* For `k = 2`, `m = p^2` exactly, so (1a) is an identity: the unique
critical value of a degree-two Blaschke product has modulus
`tanh^2(d(b_1,b_2)/4)`. For `k >= 3`, send `b_i, b_j` close together and the
others far away: `|R|` at the local critical point tends to `1` and (1a)
saturates. For (1b), take `b_j = r omega^j` with `omega = e^(2 pi i/k)`; then
`B(z) = (z^k - r^k)/(1 - r^k z^k)` has one critical point of multiplicity `k-1`
at the origin with `m = r^k`, and (1b) reads
`k r^(k-1)(1-r^2)/(1-r^(2k)) >= r^k`, i.e. `k(1-r^2) >= r(1-r^(2k))`, which is
an equality in the limit `r -> 1` at every `k`.

## 3. Corollary 2 — the third inequality on the ancestor component

> **Corollary 2.** Unconditionally, at every regular level `t > mu` with the
> notation of §1, and with `lam(d) = -log tanh(d/2) = 2 artanh(e^(-d))`
> (a strictly decreasing involution of `(0, infinity)`),
>
> ```text
> (2a)  d(b_i,b_j) >= d_crit(x) := 4 artanh(e^(-x/2)) = 2 lam(x/2)   for all i != j;
> (2b)  sum_{l != j} lam(d(b_l,b_j)) <= x                            for every j.
> ```

Both follow from Theorem 1 with `m = e^(-x)`; for (2a) note
`4 artanh(sqrt m) = 4 artanh(e^(-x/2))` and for (2b) take `-log` of (1b). The
bound is attained: `c*` itself lies in `C_t` with `|B(c*)| = m` exactly, so `m`
*is* the minimum critical modulus of `B`, and no better `m` is available.

(2a) has the same functional shape as the failure separation
`d_min(a) = 2 lam(tau(a)/2)`, `tau(a) = -log tanh(1/a)`, of the parent note,
with `tau(a)` replaced by `x`. Hence, `lam` being strictly decreasing,

```text
d_crit(x) > d_min(a)   <=>   x < tau(a)   <=>   a > 1/artanh(e^(-x)),
```

and since `a <= 1` the new floor can be the larger one only for
`x < tau(1) = -log tanh 1 = 0.272341...`.

## 4. Theorem 3 — the arity floor does not move

The landed mechanism's arity lower bound at a separation floor `d` is

```text
K(x,a,d) = max( 2,  min(kA, kB),  2x/delta(a) ),
kA = 1 + (x - delta(a)/2)/lam(d - d_low),   kB = x/lam(d/2),
d_low = lam(delta(a)/2),   delta(a) = -log(1 - e^(-1/a)),
```

used with `d = d_min(a)`.

> **Theorem 3.** For every `x > 0` and `a in (0,1]`,
> `K(x, a, max(d_min(a), d_crit(x))) = K(x, a, d_min(a))`.

*Proof.* If `d_min(a) >= d_crit(x)` there is nothing to prove. Otherwise
`x < tau(a)` by §3. Then, using that `lam` is an involution,

- at `d = d_crit(x) = 2 lam(x/2)`: `lam(d/2) = lam(lam(x/2)) = x/2`, so
  `kB = x/(x/2) = 2` and `min(kA,kB) <= 2`;
- at `d = d_min(a) = 2 lam(tau(a)/2)`: `lam(d/2) = tau(a)/2`, so
  `kB = 2x/tau(a) < 2` and `min(kA,kB) < 2`.

In both cases the middle term is dominated by the constant `2`, so
`K = max(2, 2x/delta(a))` for both floors. ∎

So the critical-spectrum pairwise floor is *pointwise* invisible to the
mechanism: exactly where it is the stronger separation statement, the branch of
the arity floor it feeds has already fallen below the trivial value `k >= 2`.
Consequently the comparison ODE, its certified hitting time `X_cert`, the
floating supremum `X_*`, and the constant `9/25` are unchanged.

The checker replays this twice. At 220 digits it evaluates the arity floor at
both separation floors over a `12000`-cell grid `x in (0, 6/5]`, `a in (0,1]`:
`729` cells have `d_crit(x) > d_min(a)`, the worst ratio `d_crit/d_min` there is
`2.2285`, and the arity floor changes by `0.0` in all `12000` cells. In double
precision the comparison ODE gives `X_* = 1.0143730` at step `1/100` and
`X_* = 0.9982629` at step `1/400`, identical with and without the new floor
(difference exactly `0.0`). The first of those reproduces the parent note's
certified `X_cert < 1.014374` to six digits, which is the replica's fidelity
receipt.

## 5. Theorem 4 — the sum form is implied by the failure separation

> **Theorem 4.** Under failure, `d(b_l,b_j) >= d_min(a)` for all pairs, so
> `sum_{l != j} lam(d(b_l,b_j)) <= (k-1) lam(d_min(a))`, and (2b) is implied —
> adds no constraint — whenever `(k-1) lam(d_min(a)) <= x`. That inequality
> holds at every point of the failure window `0 < x <= 11/10`, `0 < a <= 1` at
> which the arity floor is active.

*Proof.* Put `eps = e^(-d_min/2)`, so `lam(d_min/2) = 2 artanh(eps) >= 2 eps`
and `lam(d_min) = 2 artanh(eps^2) <= 2 eps^2/(1-eps^4) <=
lam(d_min/2)^2/(2(1-eps^4))`.

On the `kB` branch the floor is active at `k lam(d_min/2) = x`, so
`lam(d_min/2) = x/k` and `eps <= x/(2k) <= 11/40`, giving

```text
(k-1) lam(d_min) <= (k-1) (x/k)^2 / (2(1-eps^4)) <= x^2/(2k(1-eps^4)) <= 0.28 x.
```

On the `kA` branch the floor is active at `delta/2 + (k-1) lam(g) = x` with
`g = d_min - d_low > d_min/2` (because `tau(a) < delta(a)` forces
`d_low < d_min/2`), so `lam(d_min) <= lam(2g) <= lam(g)^2/(2(1-eps^4))` with
`lam(g) = (x - delta/2)/(k-1) <= x`, giving
`(k-1) lam(d_min) <= x^2/(2(k-1)(1-eps^4)) <= 0.56 x`. ∎

Measured on the extremal trajectory the ratio `(k-1) lam(d_min(a))/x` runs from
`0.0074` at `x = 0.151` to `0.0538` at `x = 0.908`: slack of a factor `19` to
`135`, never approaching `1`.

**The structural reason both forms fail.** Every consequence of the critical
spectrum in Theorem 1 is a statement that the roots are *far apart*. The failure
hypothesis is also a statement that the roots are far apart, and it is the
stronger one throughout the window. A separation floor can only tighten
`Lambda(k,a)`; it cannot supply the opposing pressure the mechanism lacks, which
is an upper bound on the ancestor area — the quantity `S` named at the end of
the parent note. The critical spectrum is not a source of `S`.

## 6. What the same pass found instead: the abstract profile is a phantom

`Lambda(k,a)` is the maximum of `sum_j lam(d_j)` over abstract distance profiles
subject to `lam(d_j) <= delta(a)/2` and the *triangle relaxation*
`d_i + d_j >= d_min(a)`. But `d_i + d_j = d(b_i,b_j)` holds only when `h` lies on
the geodesic through `b_i, b_j`, i.e. when the two are seen from `h` in opposite
directions, and `h` has only two opposite directions at a time. The `kB` branch
of `Lambda` saturates that equality on **every** pair and the `kA` branch on
every pair `(1,j)`, so for `k >= 3` both profiles are geometrically impossible
and the bound they give is strictly slack. The real quantity is

```text
Lambda_real(k,a) = max { sum_j lam(d(h,b_j)) : d(b_i,b_j) >= d_min(a),
                         lam(d(h,b_j)) <= delta(a)/2 },
```

the maximum over actual configurations of `k+1` points of `D`. Normalising
`h = 0`, `lam(d(0,b)) = -log|b|`, this is a clean hyperbolic packing problem.
Measured at `a = 1` (`d_min = 5.377073`, `d_low = 2.170077`,
`R0 = e^(-delta/2) = 0.795060`), by SLSQP from randomised multi-shell starts with
an explicit feasibility re-check on every returned point:

| `k` | `Lambda(k,1)` (abstract) | best ring | best found `Lambda_real` | ratio |
|---|---|---|---|---|
| 2 | 0.310338 | 0.272341 | 0.310338 | 1.000 |
| 4 | 0.544683 | 0.385742 | 0.430565 | 1.265 |
| 7 | 0.953195 | 0.414613 | 0.520778 | 1.830 |
| 10 | 1.361707 | 0.421967 | 0.575890 | 2.365 |
| 14 | 1.906390 | 0.425458 | 0.622837 | 3.061 |
| 20 | 2.723415 | 0.427321 | 0.671675 | 4.055 |
| 30 | 4.085122 | 0.428318 | 0.728296 | 5.609 |

Rows `2, 4, 7, 10, 14` are the checker's `--full` arm (seed `20260905`); rows
`20, 30` come from a wider sweep of the same optimiser and are not replayed by
the checker. The multistart is seeded, so each row is reproducible, but the
column is a search record, not a bound.

The attractor rides `k ≈ 7.2` and needs `sum_j lam(d_j) >= x ≈ 0.998`; the best
realisable value found at `k = 7` is `0.521`, and no configuration reaching
`0.998` was found up to `k = 30` (best `0.728`). Two elementary facts explain the
gap and are proofs, not measurements: two roots at the minimal admissible radius
`R0` have `rho <= 2 R0/(1+R0^2) = 0.974267 < tanh(d_min/2) = 0.990800`, so at
most one root may sit at the COVER-saturating radius; and on a hyperbolic circle
of radius `r` the number of `d_min`-separated points is `2 pi/Theta(r)` with
`cos Theta(r) = 1 - (cosh d_min - 1)/sinh^2 r`, whose product with `lam(r)`
saturates at `2 pi/sqrt(2(cosh d_min - 1)) = 0.4310` as `r -> infinity`.

> **Proof lead (angular budget).** Order the `b_j` by argument about `h` and let
> `theta_i` be the cyclic gaps, `sum_i theta_i = 2 pi`. Two points at hyperbolic
> radii `r, r'` and angle `theta` satisfy
> `cosh d = cosh r cosh r' - sinh r sinh r' cos theta`, so failure forces
> `theta_i >= Theta(d_i, d_{i+1})` with
> `cos Theta = (cosh d_i cosh d_{i+1} - cosh d_min)/(sinh d_i sinh d_{i+1})`.
> Hence, unconditionally under failure,
> `sum_i Theta(d_i, d_{i+1}) <= 2 pi` for the cyclic order. Maximising
> `sum_j lam(d_j)` under this budget in place of the triangle relaxation is a
> rigorous replacement for `Lambda(k,a)`, and it is the smallest open
> sub-statement this note produces.

CAVEAT, load-bearing, and it is the direction that flatters the lead:
`Lambda_real` is a *maximum*, so an optimiser that under-performs makes the gap
look larger than it is. The table's right column is therefore a **lower bound
for `Lambda_real` and an upper bound for the true improvement**, and no
threshold may be quoted from it. Only the angular-budget theorem above, once
solved, can be certified. This is negative_results entry 28's shape: report the
basin, not the record.

## 7. Task-4 question, answered

> Does a degree-seven Blaschke product exist whose six critical values all have
> modulus at least `e^(-X_*) ≈ 0.37` and whose zeros are pairwise at hyperbolic
> distance at least `d_min(1) = 4 artanh(sqrt(tanh 1)) = 5.377073`?

Yes, and the family is the regular one. `B(z) = (z^7 - r^7)/(1 - r^7 z^7)` has a
single critical point of multiplicity six at the origin with critical value
`-r^7`, and adjacent zeros at pseudohyperbolic distance
`rho(r) = 2 r sin(pi/7)/sqrt(1 - 2 r^2 cos(2 pi/7) + r^4)`, which is the minimum
over all pairs (`rho^2` is strictly increasing in the angular gap on `[0,pi]`).
Both conditions hold for every `r in [0.942490, 1)`; the critical-value floor
alone needs only `r >= 0.867093`. At `r = 99/100` the checker certifies both in
`Fraction` arithmetic, using the certified enclosure
`2 cos(2 pi/7) in [1.2469, 1.2470]` from `y^3+y^2-2y-1` and
`tanh 1 in [0.7615941, 0.7615942]`:

```text
rho^2 >= 0.999331057867 > 4m/(1+m)^2 = 0.998763656675   (Theorem 1a, non-vacuous)
rho^2 >= 0.999331057867 > tanh^2(d_min(1)/2) = 0.981684368795
m = (99/100)^7 = 0.932065347907 > 37/100 > e^(-X_*).
```

So there is **no realisability obstruction at the level of the two stated
conditions**, and the attractor is not killed there. The obstruction, if any,
lives in §6: the conditions that actually bite are the COVER radius `R0` and the
angular budget, not the critical spectrum.

## 8. Side finding — the arity floor is floored where it may be ceiled

`k` is an integer, and `check_erdos1041_cluster_separation_closure.py::_k_lower`
returns `max(2, floor_q(min(kA,kB)), floor_q(2x/delta))` where `floor_q` is a
`10^-12`-grid floor, i.e. a real-valued lower bound. Because `kA, kB` are built
from *upper* bounds on `delta, tau, lam(g)`, `min(kA,kB)` is a genuine lower
bound for the integer `k`, so `ceil` of it is equally valid and strictly
stronger. On the attractor `min(kA,kB) ≈ 7.67`, so the change is `7.67 -> 8`.
The floating replica measures `X_* : 0.998263 -> 0.955763`, i.e.
`mu : 0.368519 -> 0.384519`. That is a candidate improvement of the landed
constant from `9/25` to `19/50` at no mathematical cost. It is **not** claimed
here: it belongs to the owner of that certificate, and the rounding directions
inside `_k_lower` must be re-audited before `ceil` is applied. Recorded so it is
not lost.

## 9. Claim boundary

Theorems 1, 3, 4 and Corollary 2 are ordinary arguments, not Lean-checked and
not independently reviewed. Theorem 1 is the standard Schwarz–Pick and
sublevel-connectivity argument for Blaschke products and should be assumed
known; no priority is claimed. The threshold `9/25` of
`ClusterSeparationLowCriticalClosure.md` is unchanged, the regime
`9/25 < mu < 1` is untouched, and Erdős 1041 remains open. Everything in §6
after the two elementary facts is floating measurement and carries entry 28's
warning.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_critical_spectrum_separation.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_critical_spectrum_separation.py --full
```

One JSON line. The default form runs the exact arms (Theorem 1 on rational
witnesses, the §7 witness, the Theorem 3 scalar kernel) plus the floating ODE
replay; `--full` adds the `Lambda_real` optimisation of §6, which needs `scipy`
and takes a few minutes.
